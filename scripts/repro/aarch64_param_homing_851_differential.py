#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 44
"""#851 (RQ-57-A64PARAM) — aarch64 PARAM HOMING execution differential (RED-first).

Compiles `aarch64_param_homing_851.wat` with `synth compile -b aarch64`, then
executes each exported function's emitted A64 `.text` and diffs the result
against wasmtime ground truth.

Every exported function WRITES one of its own parameters. Before this increment
the aarch64 selector homed params only on the NON-LEAF path (v0.54 lane L3, so a
`bl` could not clobber them); a LEAF function's params lived in `x0..x7` and were
pushed onto the value stack BY REFERENCE, so `local.set`/`local.tee` on a param
index LOUD-DECLINED. With `--all-exports` that decline makes the whole compile
exit non-zero — the RED state. AFTER the fix every case matches wasmtime — GREEN.

Execution uses two independent oracles:
  1. unicorn (UC_ARCH_ARM64) — portable, runs on any host (the CI path).
  2. native MAP_JIT — on an arm64 host the SAME `.text` is mapped executable and
     called through ctypes, so the real silicon is the oracle. Skipped off-arm64.

The load-bearing cases are the ones a naive lowering passes but a correct one
must handle:
  - `get_set_get_param_no_alias` / `tee_param_no_alias` — the exact hazard the
    decline was protecting against: a param write must not clobber a value the
    value stack already holds. A by-reference model returns a CONSTANT (10 / 30)
    for every input instead of `old(p) + 5` / `old(p) + 20`.
  - `param_countdown_sum` — the canonical real shape: the loop counter IS the
    param, stored and reloaded across a back-edge inside a leaf frame.
  - `mixed_param_and_local` — the homed frame now covers index 0..N, so a
    non-param local's slot MOVED; its zero-init and offset must both survive.
  - `swap_two_params` — two param writes through a scratch local (an aliasing
    lowering collapses to 0).
  - `i64_param_write` / `i64_i32_param_write` — the 8-byte home slot must
    preserve the full width, and mixed-width params must not disturb offsets.
  - POISONED-upper-bits cases (`poison=True`) — homing stores/loads the whole
    `x` register, so an i32 param arriving with AAPCS64-unspecified garbage in
    its upper half must still read back as the right i32. unicorn writes the
    full 64-bit poisoned value; wasmtime sees only the i32.
  - `param_write_across_call` — the NON-LEAF shape that already compiled, kept
    as a regression guard on the widened homing predicate.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_param_homing_851_differential.py
"""
import ctypes
import mmap
import os
import platform
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM64, UC_MODE_ARM, Uc, UcError
from unicorn.arm64_const import (
    UC_ARM64_REG_LR,
    UC_ARM64_REG_SP,
    UC_ARM64_REG_W0,
    UC_ARM64_REG_X0,
    UC_ARM64_REG_X1,
    UC_ARM64_REG_X2,
)

WAT = Path(__file__).with_name("aarch64_param_homing_851.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET = 0x100000, 0x200000, 0x300000
X_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1

R_AARCH64_CALL26 = 283

# Garbage stuffed into the UPPER half of a 32-bit argument register. AAPCS64
# leaves those bits UNSPECIFIED for an i32 argument, and param homing now
# stores/loads the full `x` register, so every i32 consumer must keep taking the
# `w` view. A lowering that leaked the upper half would return a huge number.
POISON = 0xDEADBEEF << 32


# (fn, [arg widths], result width, [args], poison-upper-half-of-32-bit-args).
# Widths in bits; args are given as UNSIGNED bit patterns of that width.
CASES = [
    # THE aliasing case the decline was protecting against.
    ("get_set_get_param_no_alias", [32], 32, [7], False),
    ("get_set_get_param_no_alias", [32], 32, [0], False),
    ("get_set_get_param_no_alias", [32], 32, [0xFFFFFFFF], False),
    ("get_set_get_param_no_alias", [32], 32, [7], True),
    # local.tee on a param: on the stack AND durable.
    ("tee_param_no_alias", [32], 32, [3], False),
    ("tee_param_no_alias", [32], 32, [0xFFFFFFF0], False),
    ("tee_param_no_alias", [32], 32, [3], True),
    ("tee_param_result", [32], 32, [40], False),
    ("tee_param_result", [32], 32, [0], False),
    ("tee_param_result", [32], 32, [0xFFFFFFFF], False),
    # The param IS the loop counter (store/load across a back-edge).
    ("param_countdown_sum", [32], 32, [0], False),
    ("param_countdown_sum", [32], 32, [1], False),
    ("param_countdown_sum", [32], 32, [5], False),
    ("param_countdown_sum", [32], 32, [8], True),
    # Param written on BOTH arms of if/else (SP balance on every path).
    ("param_write_if_else", [32], 32, [0], False),
    ("param_write_if_else", [32], 32, [1], False),
    ("param_write_if_else", [32], 32, [0xFFFFFFFF], False),
    # Slot-offset arithmetic across three params.
    ("write_last_of_three", [32, 32, 32], 32, [3, 4, 0], False),
    ("write_last_of_three", [32, 32, 32], 32, [0xFFFF, 0x10, 999], False),
    ("write_last_of_three", [32, 32, 32], 32, [0xFFFFFFFF, 2, 7], False),
    ("write_last_of_three", [32, 32, 32], 32, [3, 4, 0], True),
    # Two param writes through a scratch local.
    ("swap_two_params", [32, 32], 32, [5, 9], False),
    ("swap_two_params", [32, 32], 32, [0, 0], False),
    ("swap_two_params", [32, 32], 32, [0x7FFFFFFF, 0x80000000], False),
    # A param write next to a zero-init non-param local whose slot MOVED.
    ("mixed_param_and_local", [32, 32], 32, [1, 2], False),
    ("mixed_param_and_local", [32, 32], 32, [0, 0], False),
    ("mixed_param_and_local", [32, 32], 32, [10, 20], True),
    # 64-bit home slot keeps the full width.
    ("i64_param_write", [64], 64, [0], False),
    ("i64_param_write", [64], 64, [0x0123456789ABCDEF], False),
    ("i64_param_write", [64], 64, [0xFFFFFFFFFFFFFFFF], False),
    # Mixed-width params: an i64 param written alongside an i32 param.
    ("i64_i32_param_write", [64, 32], 64, [0x0000000100000001, 3], False),
    ("i64_i32_param_write", [64, 32], 64, [0xFFFFFFFFFFFFFFFF, 2], False),
    ("i64_i32_param_write", [64, 32], 64, [7, 0xFFFFFFFF], False),
    # The #457 param-count INFERENCE miscompile: a CONDITIONALLY written param
    # was reclassified as a zero-init non-param local and compiled SILENTLY
    # WRONG (measured on c2f9d72: cond_write_param(0,42) → 0, wasmtime 42).
    ("cond_write_param", [32, 32], 32, [0, 42], False),
    ("cond_write_param", [32, 32], 32, [1, 42], False),
    ("cond_write_param", [32, 32], 32, [0, 0], False),
    ("cond_write_param", [32, 32], 32, [0, 0xFFFFFFFF], False),
    ("cond_write_param", [32, 32], 32, [0, 42], True),
    ("cond_write_param_loop", [32, 32, 32], 32, [0, 5, 7], False),
    ("cond_write_param_loop", [32, 32, 32], 32, [3, 5, 7], False),
    ("cond_write_param_loop", [32, 32, 32], 32, [1, 0, 9], False),
    # NON-LEAF regression guard (this shape already compiled before the fix).
    ("param_write_across_call", [32], 32, [5], False),
    ("param_write_across_call", [32], 32, [0], False),
    ("param_write_across_call", [32], 32, [0xFFFFFFFF], False),
]


def wasmtime_run(fn, args):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    return wasmtime.Instance(store, module, []).exports(store)[fn](store, *args)


def compile_aarch64(out):
    """Compile the module; returns True on success, False on the RED decline."""
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "aarch64", "--all-exports"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0 or "skipping" in r.stderr or "not yet supported" in r.stderr:
        print("compile declined/failed (RED state before param homing):")
        print("  " + (r.stderr.strip() or r.stdout.strip()).replace("\n", "\n  "))
        return False
    return True


def load(elf):
    """Return (relocated .text bytes, sh_addr, {symbol: address}).

    The module contains one direct `call`, so `.text` carries an
    R_AARCH64_CALL26 whose `bl` still reads `#0` (a branch-to-self infinite
    loop) until it is resolved. Every function is already concatenated at its
    final offset, so resolving means only filling in the displacement.
    """
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = bytearray(text.data()), text["sh_addr"]
    symtab = None
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            symtab = sec
            for sy in sec.iter_symbols():
                if sy.name:
                    syms[sy.name] = sy["st_value"] & ~1
    rela = f.get_section_by_name(".rela.text")
    nrel = 0
    if rela is not None:
        for rel in rela.iter_relocations():
            assert rel["r_info_type"] == R_AARCH64_CALL26, (
                f"unexpected reloc type {rel['r_info_type']} — this harness only "
                f"resolves R_AARCH64_CALL26"
            )
            site = rel["r_offset"] - base
            target = symtab.get_symbol(rel["r_info_sym"])["st_value"] - base
            disp = (target + rel["r_addend"] - site) // 4
            word = struct.unpack_from("<I", code, site)[0]
            # Keep the opcode bits (bl = 0x94000000), fill imm26.
            word = (word & 0xFC000000) | (disp & 0x03FFFFFF)
            struct.pack_into("<I", code, site, word)
            nrel += 1
    if nrel:
        print(f"resolved {nrel} R_AARCH64_CALL26 relocation(s)")
    return bytes(code), base, syms


def encode_arg(width, value, poison):
    """The 64-bit pattern to place in the argument register."""
    if width == 64:
        return value & M64
    v = value & M32
    return (POISON | v) if poison else v


def unicorn_run(code, base, faddr, arg_widths, result_width, args, poison):
    off = faddr - base
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    for r, w, v in zip(X_ARGS, arg_widths, args):
        mu.reg_write(r, encode_arg(w, v, poison))
    try:
        mu.emu_start(CODE + off, RET, count=4000)
    except UcError as e:
        return f"ERR:{e}"
    if result_width == 32:
        raw = mu.reg_read(UC_ARM64_REG_W0) & M32
        return struct.unpack("<i", struct.pack("<I", raw))[0]
    raw = mu.reg_read(UC_ARM64_REG_X0) & M64
    return struct.unpack("<q", struct.pack("<Q", raw))[0]


# --- native MAP_JIT oracle (arm64 host only) --------------------------------
#
# Map the whole relocated `.text` blob RWX (MAP_JIT on Darwin), then call each
# function at its symbol offset via a ctypes prototype. This runs the emitted
# bytes on the REAL CPU — the strongest possible oracle for the silicon we
# target. It cannot force POISONED upper argument bits (ctypes marshals a clean
# 32-bit value), so the poison probe is unicorn-only by construction.
_IS_ARM64 = platform.machine() in ("arm64", "aarch64")
_IS_DARWIN = sys.platform == "darwin"


class _NativeText:
    def __init__(self, code, base, syms):
        self.base = base
        self.syms = syms
        n = (len(code) + 0xFFF) & ~0xFFF
        if _IS_DARWIN:
            MAP_JIT = 0x800
            flags = mmap.MAP_PRIVATE | mmap.MAP_ANONYMOUS | MAP_JIT
            self.buf = mmap.mmap(-1, n, flags=flags,
                                 prot=mmap.PROT_READ | mmap.PROT_WRITE | mmap.PROT_EXEC)
            # W^X toggle: make writable, copy, then executable.
            ctypes.pythonapi.pthread_jit_write_protect_np.restype = None
            ctypes.pythonapi.pthread_jit_write_protect_np(0)
            self.buf.write(code)
            ctypes.pythonapi.pthread_jit_write_protect_np(1)
            libc = ctypes.CDLL(None)
            libc.sys_icache_invalidate(
                ctypes.c_void_p(ctypes.addressof(ctypes.c_char.from_buffer(self.buf))),
                ctypes.c_size_t(n))
        else:  # linux arm64
            self.buf = mmap.mmap(-1, n,
                                 prot=mmap.PROT_READ | mmap.PROT_WRITE | mmap.PROT_EXEC)
            self.buf.write(code)
        self.addr = ctypes.addressof(ctypes.c_char.from_buffer(self.buf))

    def call(self, fn, arg_widths, result_width, args):
        off = self.syms[fn] - self.base
        restype = ctypes.c_int64 if result_width == 64 else ctypes.c_int32
        argtypes = [ctypes.c_int64 if w == 64 else ctypes.c_int32 for w in arg_widths]
        proto = ctypes.CFUNCTYPE(restype, *argtypes)
        fptr = proto(self.addr + off)
        return fptr(*to_signed(arg_widths, args))


def to_signed(arg_widths, args):
    out = []
    for w, a in zip(arg_widths, args):
        if w == 64:
            out.append(struct.unpack("<q", struct.pack("<Q", a & M64))[0])
        else:
            out.append(struct.unpack("<i", struct.pack("<I", a & M32))[0])
    return out


def main():
    out = "/tmp/aarch64_param_homing_851.o"
    # A stale object from an earlier run reads as a fresh miscompile.
    if os.path.exists(out):
        os.remove(out)
    if not compile_aarch64(out):
        print("\nRESULT: RED — aarch64 declined writing a PARAMETER "
              "(expected BEFORE param homing; a FAIL after the fix lands)")
        sys.exit(1)
    code, base, syms = load(out)

    native = None
    if _IS_ARM64:
        try:
            native = _NativeText(code, base, syms)
            print("native MAP_JIT oracle: ENABLED (arm64 host)")
        except Exception as e:  # noqa: BLE001
            print(f"native MAP_JIT oracle: unavailable ({e}); unicorn only")
    else:
        print("native MAP_JIT oracle: skipped (non-arm64 host); unicorn only")

    fails = 0
    total = 0
    for fn, aws, rw, args, poison in CASES:
        total += 1
        if fn not in syms:
            print(f"BUG {fn}: symbol missing from .text (silently declined?)")
            fails += 1
            continue
        exp = wasmtime_run(fn, to_signed(aws, args))
        m = M32 if rw == 32 else M64
        uni = unicorn_run(code, base, syms[fn], aws, rw, args, poison)
        ok = isinstance(uni, int) and (uni & m) == (exp & m)
        tag = " [poisoned upper halves]" if poison else ""
        line = (f"{fn}{tuple(hex(a) for a in args)}{tag}: "
                f"wasmtime={exp} unicorn={uni}")
        # The native oracle marshals clean 32-bit args, so it cannot reproduce
        # the poison probe — run it only on the un-poisoned cases.
        if native is not None and not poison:
            nat = native.call(fn, aws, rw, args)
            ok = ok and (nat & m) == (exp & m)
            line += f" native={nat}"
        if not ok:
            fails += 1
            print("BUG " + line)
        else:
            print("ok  " + line)
    print(f"\n{total - fails}/{total} cases matched wasmtime")
    print("RESULT:", "PASS — aarch64 param homing matches wasmtime (#851)"
          if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
