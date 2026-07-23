#!/usr/bin/env python3
"""#851 — aarch64 NON-PARAM LOCALS execution differential (RED-first).

Compiles `aarch64_locals_851.wat` with `synth compile -b aarch64`, then executes
each exported function's emitted A64 `.text` and diffs the result against
wasmtime ground truth. Every function uses at least one non-param local, so
BEFORE #851 the compile itself FAILS (`local.get {i}: non-param locals not yet
supported`) — the RED state (`compile_aarch64` exits non-zero) — and AFTER #851
every case matches wasmtime — the GREEN state.

Execution uses two independent oracles:
  1. unicorn (UC_ARCH_ARM64) — portable, runs on any host (the CI path).
  2. native MAP_JIT — on an arm64 host the SAME `.text` is mapped executable and
     called through ctypes, so the real silicon is the oracle. Skipped off-arm64.

The load-bearing cases are the ones a naive lowering passes but a correct one
must handle:
  - `get_set_get_no_alias`  — local.get must COPY, not alias the home slot
    (a read-by-reference model returns 10 instead of 5).
  - `zero_init_read_first`  — a local read before any write must be 0.
  - `i64_local`             — 64-bit slot store/load preserves the full width.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_locals_851_differential.py
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

WAT = Path(__file__).with_name("aarch64_locals_851.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET = 0x100000, 0x200000, 0x300000
X_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1


# (fn, arg_width, result_width, [args...]). widths in bits.
CASES = [
    ("two_locals_sum", 32, 32, []),
    ("zero_init_read_first", 32, 32, [0]),
    ("zero_init_read_first", 32, 32, [42]),
    ("zero_init_read_first", 32, 32, [0xFFFFFFFF]),
    ("get_set_get_no_alias", 32, 32, []),
    ("tee_double", 32, 32, []),
    ("param_plus_local", 32, 32, [3, 4]),
    ("param_plus_local", 32, 32, [0xFFFF, 0x10]),
    ("param_plus_local", 32, 32, [0, 0]),
    ("i64_local", 64, 64, []),
    ("three_locals", 32, 32, []),
    ("reassign_local", 32, 32, [0]),
    ("reassign_local", 32, 32, [10]),
    ("reassign_local", 32, 32, [0x7FFFFFFF]),
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
        print("compile declined/failed (RED state before #851):")
        print("  " + (r.stderr.strip() or r.stdout.strip()).replace("\n", "\n  "))
        return False
    return True


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name:
                    syms[sy.name] = sy["st_value"] & ~1
    return code, base, syms


def unicorn_run(code, base, faddr, arg_width, result_width, args):
    off = faddr - base
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    mask = M32 if arg_width == 32 else M64
    for r, v in zip(X_ARGS, args):
        mu.reg_write(r, v & mask)
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
# Map the whole `.text` blob RWX (MAP_JIT on Darwin), then call each function at
# its symbol offset via a ctypes prototype. This runs the emitted bytes on the
# REAL CPU — the strongest possible oracle for the silicon we target.
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

    def call(self, fn, arg_width, result_width, args):
        off = self.syms[fn] - self.base
        restype = ctypes.c_int64 if result_width == 64 else ctypes.c_int32
        argtype = ctypes.c_int64 if arg_width == 64 else ctypes.c_int32
        proto = ctypes.CFUNCTYPE(restype, *([argtype] * len(args)))
        fptr = proto(self.addr + off)
        sgn = []
        for a in args:
            if arg_width == 64:
                sgn.append(struct.unpack("<q", struct.pack("<Q", a & M64))[0])
            else:
                sgn.append(struct.unpack("<i", struct.pack("<I", a & M32))[0])
        return fptr(*sgn)


def to_wasm_args(arg_width, args):
    if arg_width == 32:
        return [struct.unpack("<i", struct.pack("<I", a & M32))[0] for a in args]
    return [struct.unpack("<q", struct.pack("<Q", a & M64))[0] for a in args]


def main():
    out = "/tmp/aarch64_locals_851.o"
    if not compile_aarch64(out):
        print("\nRESULT: RED — aarch64 declined non-param locals "
              "(expected BEFORE #851; a FAIL after the fix lands)")
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
    for fn, aw, rw, args in CASES:
        total += 1
        if fn not in syms:
            print(f"BUG {fn}: symbol missing from .text")
            fails += 1
            continue
        exp = wasmtime_run(fn, to_wasm_args(aw, args))
        m = M32 if rw == 32 else M64
        uni = unicorn_run(code, base, syms[fn], aw, rw, args)
        ok = isinstance(uni, int) and (uni & m) == (exp & m)
        line = f"{fn}{tuple(hex(a) for a in args)}: wasmtime={exp} unicorn={uni}"
        if native is not None:
            nat = native.call(fn, aw, rw, args)
            ok = ok and (nat & m) == (exp & m)
            line += f" native={nat}"
        if not ok:
            fails += 1
            print("BUG " + line)
        else:
            print("ok  " + line)
    print(f"\n{total - fails}/{total} cases matched wasmtime")
    print("RESULT:", "PASS — aarch64 non-param locals match wasmtime (#851)"
          if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
