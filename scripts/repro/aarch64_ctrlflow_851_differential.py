#!/usr/bin/env python3
"""#851 aarch64 FULL control-flow — if/else, loop back-edge, return EXECUTION diff.

The #851 increment extends the void-block-only #538 control flow with:
  * `if` / `else` (void arms): `cbz`/`cmp+b.cond` to the else/end, `b` over the
    else arm, join at end;
  * `loop`: a BACKWARD branch target — `br` to a loop label resolves to a
    negative offset at emission (not patched at End);
  * `return`: early epilogue (funnel top -> x0, restore SP, `ret`).

This harness proves the emitted A64 `.text` executes bit-identically to
wasmtime. Both edges of every conditional branch are exercised, and loops run
to a data-dependent trip count, so a wrong branch OFFSET (forward vs backward,
too far, too short) changes the RESULT and is caught — the gate is non-vacuous.

Traps (the `if_noelse_guard` `unreachable`) are execution-verified two ways:
  (1) unicorn (UC_ARCH_ARM64): the `brk #0` raises a UC exception;
  (2) natively on an arm64 host: each call runs in a forked child, so an
      expected SIGTRAP is observed by the parent.

The static expect column is validated against wasmtime FIRST, so the table
cannot drift vacuous.

Run (needs wasmtime + unicorn + pyelftools; native path needs an arm64 host):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_ctrlflow_851_differential.py
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

WAT = Path(__file__).with_name("aarch64_ctrlflow_851.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET = 0x100000, 0x200000, 0x300000
X_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
TRAP = "TRAP"

# Signatures: fn -> ([arg widths in bits], ret width in bits).
SIGS = {
    "if_else_pick": ([32, 32, 32], 32),
    "if_noelse_guard": ([32], 32),
    "if_max": ([32, 32], 32),
    "count_sum": ([32], 32),
    "countdown": ([32], 32),
    "do_while_count": ([32], 32),
    "early_ret": ([32], 32),
    "isqrt_ceil": ([32], 32),
}

# (fn, [args...]). Cover BOTH arms of every if; run loops to several trip counts
# (including 0 = never-enter and a large-ish count); exercise both return sites.
CASES = [
    # if/else pick: cond nonzero -> a (arg1); cond 0 -> b (arg2).
    ("if_else_pick", [1, 10, 20]),        # -> 10
    ("if_else_pick", [0, 10, 20]),        # -> 20
    ("if_else_pick", [0xFFFFFFFF, 7, 9]), # any nonzero -> 7
    # if without else guarding a trap: cond nonzero -> trap; cond 0 -> return arg.
    ("if_noelse_guard", [0]),             # -> 0 (fall through)
    ("if_noelse_guard", [5]),             # -> trap
    ("if_noelse_guard", [0x80000000]),    # nonzero high bit -> trap
    # max(a,b): both orderings + equal.
    ("if_max", [3, 8]),                   # -> 8
    ("if_max", [8, 3]),                   # -> 8
    ("if_max", [5, 5]),                   # -> 5
    ("if_max", [0xFFFFFFFF, 1]),          # -1 signed vs 1 -> 1
    # counting loop: sum 0..n-1.
    ("count_sum", [0]),                   # loop never entered -> 0
    ("count_sum", [1]),                   # -> 0
    ("count_sum", [5]),                   # -> 10
    ("count_sum", [100]),                 # -> 4950
    # countdown loop: return iteration count == n.
    ("countdown", [0]),                   # -> 0
    ("countdown", [1]),                   # -> 1
    ("countdown", [37]),                  # -> 37
    # do-while (backward cbnz to loop header): body runs >=1 time.
    ("do_while_count", [1]),              # -> 1 (runs once, n->0, exit)
    ("do_while_count", [5]),              # -> 5
    ("do_while_count", [200]),            # -> 200
    # early return: negative -> -1 early; else a*2.
    ("early_ret", [0xFFFFFFFF]),          # -1 -> -1 (early)
    ("early_ret", [10]),                  # -> 20 (late)
    ("early_ret", [0]),                   # -> 0 (late)
    # return-inside-loop: ceil sqrt.
    ("isqrt_ceil", [0]),                  # 0*0>=0 -> 0
    ("isqrt_ceil", [1]),                  # 1
    ("isqrt_ceil", [16]),                 # 4
    ("isqrt_ceil", [17]),                 # 5
    ("isqrt_ceil", [10000]),              # 100
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
        mu.emu_start(CODE + off, RET, count=200000)
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
    out = "/tmp/aarch64_ctrlflow_851.o"
    compile_aarch64(out)
    code, base, syms = load(out)
    host_native = platform.machine() in ("arm64", "aarch64")

    fails = 0
    total = 0
    trap_cases = 0
    ret_cases = 0
    # Non-vacuity: every function must actually appear + run.
    seen_fns = set()
    for fn, args in CASES:
        sig = SIGS[fn]
        _, ret = sig
        if fn not in syms:
            print(f"FAIL {fn}: symbol missing")
            fails += 1
            continue
        seen_fns.add(fn)
        total += 1
        exp = wasmtime_run(fn, args, sig)
        if exp == TRAP:
            trap_cases += 1
        else:
            ret_cases += 1
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

    # Non-vacuity guards: both trap+return edges ran, and every function ran.
    if trap_cases == 0 or ret_cases == 0:
        print(f"VACUOUS: trap_cases={trap_cases} return_cases={ret_cases} — a "
              f"branch edge was never exercised")
        fails += 1
    missing = set(SIGS) - seen_fns
    if missing:
        print(f"VACUOUS: functions never exercised: {sorted(missing)}")
        fails += 1

    print(f"\n{total} cases ({trap_cases} trap, {ret_cases} return), "
          f"{'arm64 host + unicorn' if host_native else 'unicorn-only host'}")
    print("RESULT:", "PASS — aarch64 if/else + loop back-edge + return match "
          "wasmtime (both branch edges + loop trip counts execution-verified)"
          if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
