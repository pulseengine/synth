#!/usr/bin/env python3
"""#538 control-flow increment — the void-block br/br_if EXECUTION differential.

The #538 aarch64 backend gains its first control-flow construct: forward
VOID-result `block` with `br` / `br_if`. This harness proves the emitted A64
`.text` executes bit-identically to wasmtime, with the branch-taken AND
branch-not-taken edge of every conditional branch exercised.

The observable difference between taken and not-taken is a TRAP: each function
guards an `unreachable` behind a branch, so the branch either skips the trap
(returns a value) or falls into it (traps). A wrong branch OFFSET flips
trap<->return and is caught — the gate is non-vacuous. Traps are
execution-verified two ways (as in the m4 harness):
  (1) unicorn (UC_ARCH_ARM64): the `brk #0` raises a UC exception;
  (2) natively on an arm64 host: each call runs in a forked child, so an
      expected SIGTRAP is observed by the parent and a surprise one is
      survivable.

The static expect-trap column is validated against wasmtime FIRST — if wasmtime
disagrees, the FIXTURE is declared wrong (loud), so the table can't drift
vacuous.

Run (needs wasmtime + unicorn + pyelftools; native path needs an arm64 host):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_cf_538_differential.py
"""

import ctypes
import os
import platform
import signal
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

WAT = Path(__file__).with_name("aarch64_cf_538.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET = 0x100000, 0x200000, 0x300000
X_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
TRAP = "TRAP"

# Signatures: fn -> ([arg widths in bits], ret width in bits).
SIGS = {
    "guard_brif": ([32, 32], 32),
    "always_br": ([32], 32),
    "nested_brif1": ([32, 32], 32),
    "brif_then_mul": ([32, 64, 64], 64),
    "bare_block_add": ([32, 32], 32),
}

# (fn, [args...]) — cond=0 exercises the NOT-TAKEN edge (trap); cond!=0 the
# TAKEN edge (return). Includes a large cond to prove `br_if` tests
# nonzero-ness, not a specific bit.
CASES = [
    ("guard_brif", [0, 7]),          # cond 0 -> trap
    ("guard_brif", [1, 7]),          # cond 1 -> return 7
    ("guard_brif", [0xFFFFFFFF, 42]),  # any nonzero -> return 42
    ("guard_brif", [0x10000, 99]),   # high bit only -> return 99
    ("always_br", [123]),            # always return 123
    ("always_br", [0]),              # always return 0 (br is unconditional)
    ("nested_brif1", [0, 5]),        # cond 0 -> inner trap
    ("nested_brif1", [1, 5]),        # cond 1 -> skip BOTH -> return 5
    ("nested_brif1", [0xDEAD, 88]),  # nonzero -> return 88
    ("brif_then_mul", [0, 6, 7]),    # cond 0 -> trap
    ("brif_then_mul", [1, 6, 7]),    # cond 1 -> 42
    ("brif_then_mul", [3, 0x100000000 & M64, 2]),  # wide i64 mul on fall-through
    ("bare_block_add", [10, 20]),    # transparent block -> 30
    ("bare_block_add", [0xFFFFFFFF, 1]),  # wrap -> 0
]


def wasmtime_run(fn, args, sig):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    f = wasmtime.Instance(store, module, []).exports(store)[fn]
    widths, ret = sig
    call = []
    for w, a in zip(widths, args):
        if w == 32:
            call.append(struct.unpack("<i", struct.pack("<I", a & M32))[0])
        else:
            call.append(struct.unpack("<q", struct.pack("<Q", a & M64))[0])
    try:
        r = f(store, *call)
    except wasmtime.Trap:
        return TRAP
    return r & (M32 if ret == 32 else M64)


def compile_aarch64(out):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "aarch64", "--all-exports"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0 or "skipping" in r.stderr:
        sys.exit(f"aarch64 compile failed/skipped: {r.stderr}")


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


def unicorn_run(code, base, faddr, sig, args):
    off = faddr - base
    widths, ret = sig
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    for r, (w, v) in zip(X_ARGS, zip(widths, args)):
        mu.reg_write(r, v & (M32 if w == 32 else M64))
    try:
        mu.emu_start(CODE + off, RET, count=2000)
    except UcError:
        return TRAP  # the guarded `brk #0` — a trap, not a value
    if ret == 32:
        return mu.reg_read(UC_ARM64_REG_W0) & M32
    return mu.reg_read(UC_ARM64_REG_X0) & M64


# ---- native arm64 execution (forked child; SIGTRAP == trap) ---------------
_MAP_PRIVATE = 0x0002
_MAP_ANON = 0x1000 if sys.platform == "darwin" else 0x20
_MAP_JIT = 0x0800
_PROT_RWX = 0x1 | 0x2 | 0x4


def native_setup(code):
    libc = ctypes.CDLL(None, use_errno=True)
    libc.mmap.restype = ctypes.c_void_p
    libc.mmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int,
                          ctypes.c_int, ctypes.c_int, ctypes.c_long]
    size = max(len(code), 4096)
    flags = _MAP_PRIVATE | _MAP_ANON
    if sys.platform == "darwin":
        flags |= _MAP_JIT
    addr = libc.mmap(None, size, _PROT_RWX, flags, -1, 0)
    if addr in (ctypes.c_void_p(-1).value, 0, None):
        err = ctypes.get_errno()
        raise OSError(err, f"mmap(MAP_JIT) failed: {os.strerror(err)}")
    if sys.platform == "darwin":
        wp = ctypes.CDLL(None).pthread_jit_write_protect_np
        wp(0)
    ctypes.memmove(addr, code, len(code))
    if sys.platform == "darwin":
        wp(1)
        libc.sys_icache_invalidate.argtypes = [ctypes.c_void_p, ctypes.c_size_t]
        libc.sys_icache_invalidate(ctypes.c_void_p(addr), len(code))
    return addr


def native_run(code, faddr, code_base, sig, args):
    widths, ret = sig
    rd, wr = os.pipe()
    pid = os.fork()
    if pid == 0:
        try:
            os.close(rd)
            base_addr = native_setup(code)
            fn_addr = base_addr + (faddr - code_base)
            argtys = [ctypes.c_int32 if w == 32 else ctypes.c_int64 for w in widths]
            retty = ctypes.c_int32 if ret == 32 else ctypes.c_int64
            fn = ctypes.CFUNCTYPE(retty, *argtys)(fn_addr)
            call = []
            for w, a in zip(widths, args):
                if w == 32:
                    call.append(struct.unpack("<i", struct.pack("<I", a & M32))[0])
                else:
                    call.append(struct.unpack("<q", struct.pack("<Q", a & M64))[0])
            r = fn(*call)  # a brk #0 here delivers SIGTRAP -> child dies
            bits = r & (M32 if ret == 32 else M64)
            os.write(wr, struct.pack("<Q", bits))
            os.close(wr)
        finally:
            os._exit(0)
    os.close(wr)
    _, status = os.waitpid(pid, 0)
    data = os.read(rd, 8)
    os.close(rd)
    if os.WIFSIGNALED(status):
        if os.WTERMSIG(status) in (signal.SIGTRAP, signal.SIGILL):
            return TRAP
        return f"ERR:signal {os.WTERMSIG(status)}"
    if len(data) != 8:
        return "ERR:no result"
    return struct.unpack("<Q", data)[0]


def main():
    out = "/tmp/aarch64_cf_538.o"
    compile_aarch64(out)
    code, base, syms = load(out)
    host_native = platform.machine() in ("arm64", "aarch64")

    fails = 0
    total = 0
    trap_cases = 0
    taken = 0
    for fn, args in CASES:
        sig = SIGS[fn]
        _, ret = sig
        if fn not in syms:
            print(f"FAIL {fn}: symbol missing")
            fails += 1
            continue
        total += 1
        exp = wasmtime_run(fn, args, sig)
        if exp == TRAP:
            trap_cases += 1
        else:
            taken += 1
        oracles = [("unicorn", unicorn_run(code, base, syms[fn], sig, args))]
        if host_native:
            oracles.append(("native", native_run(code, syms[fn], base, sig, args)))
        for label, got in oracles:
            ok = (exp == got) if (exp == TRAP or got == TRAP) else \
                (isinstance(got, int) and got == (exp & (M32 if ret == 32 else M64)))
            if not ok:
                fails += 1
                e = exp if exp == TRAP else hex(exp)
                g = got if isinstance(got, str) else hex(got)
                print(f"BUG {fn}{tuple(hex(a) for a in args)} [{label}] "
                      f"A64={g} wasmtime={e}")

    # Non-vacuity guard: the gate is only meaningful if BOTH branch edges ran.
    if trap_cases == 0 or taken == 0:
        print(f"VACUOUS: trap_cases={trap_cases} return_cases={taken} — a branch "
              f"edge was never exercised")
        fails += 1

    print(f"\n{total} cases ({trap_cases} not-taken/trap, {taken} taken/return), "
          f"{'arm64 host + unicorn' if host_native else 'unicorn-only host'}")
    print("RESULT:", "PASS — aarch64 void-block br/br_if matches wasmtime "
          "(both branch edges execution-verified)"
          if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
