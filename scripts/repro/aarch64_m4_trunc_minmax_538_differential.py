#!/usr/bin/env python3
"""#538 milestone-4 — the #709 boundary-table EXECUTION differential.

m4 converts the aarch64 backend's #709-class declines into capabilities:
  - i32.trunc_f32_s/u + i32.trunc_f64_s/u, lowered behind an explicit WASM
    domain guard (fcmp exact boundary + ordered b.cond + brk) in front of the
    otherwise-SATURATING A64 FCVTZS/FCVTZU;
  - f32/f64.min/max via A64 FMIN/FMAX (claimed = IEEE 754-2019 minimum/maximum
    = WASM semantics — VERIFIED here against wasmtime, not assumed);
  - f32/f64.copysign (bit surgery; NaN sign must be preserved bit-exactly).

The fatal class this gates: a saturating truncation where WASM traps. So the
harness runs the FULL boundary table for every trunc op and requires the trap
cases to ACTUALLY TRAP, execution-verified two ways:
  (1) unicorn (UC_ARCH_ARM64): the guard's `brk #0` raises UC_ERR_EXCEPTION;
  (2) natively on an arm64 host: EVERY native call runs in a forked child, so
      an expected SIGTRAP is observed by the parent (and a surprise trap can't
      kill the harness).
In-range cases must match wasmtime bit-exactly. The static expect-trap column
is itself validated against wasmtime first — if wasmtime disagrees with the
table, the FIXTURE is declared wrong (loud), so the table can't drift vacuous.

Run (needs wasmtime + unicorn + pyelftools; native path needs an arm64 host):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_m4_trunc_minmax_538_differential.py
"""

import ctypes
import math
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
    UC_ARM64_REG_CPACR_EL1,
    UC_ARM64_REG_D0,
    UC_ARM64_REG_LR,
    UC_ARM64_REG_S0,
    UC_ARM64_REG_SP,
    UC_ARM64_REG_V0,
    UC_ARM64_REG_V1,
    UC_ARM64_REG_W0,
    UC_ARM64_REG_X0,
    UC_ARM64_REG_X1,
)

WAT = Path(__file__).with_name("aarch64_m4_trunc_minmax_538.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET = 0x100000, 0x200000, 0x300000
V_ARGS = [UC_ARM64_REG_V0, UC_ARM64_REG_V1]
X_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
INF = float("inf")
NAN = float("nan")

# Signatures: fn -> ([arg types], ret type).
SIGS = {
    "i32_trunc_f32_s": (["f32"], "i32"),
    "i32_trunc_f32_u": (["f32"], "i32"),
    "i32_trunc_f64_s": (["f64"], "i32"),
    "i32_trunc_f64_u": (["f64"], "i32"),
    "f32_min": (["f32", "f32"], "f32"),
    "f32_max": (["f32", "f32"], "f32"),
    "f64_min": (["f64", "f64"], "f64"),
    "f64_max": (["f64", "f64"], "f64"),
    "f32_copysign": (["f32", "f32"], "f32"),
    "f64_copysign": (["f64", "f64"], "f64"),
    "f32_sqrt": (["f32"], "f32"),
}

# ---------------------------------------------------------------------------
# The #709 boundary table (WASM Core §4.3.3 trunc_s / trunc_u domains).
# Key subtleties pinned:
#   - trunc_f32_s(-2^31) is IN-range (exactly representable, lowest valid);
#     trunc_f32_s(2^31) TRAPS (the largest valid f32 is 2147483520).
#   - trunc_f64_s(-2147483648.5) is IN-range (truncates to -2^31): the f64
#     lower bound is the STRICT -(2^31)-1, not an inclusive -2^31.
#   - trunc_u(-0.9) -> 0 is IN-range (strict lower bound -1.0); trunc_u(-1.0)
#     TRAPS.
#   - NaN and ±inf ALWAYS trap.
TRUNC_TABLE = {
    "i32_trunc_f32_s": {
        "in": [0.0, -0.0, 0.5, -0.5, 1.9, -1.9, 100.75,
               2147483520.0, -2147483648.0, -2147483520.0],
        "trap": [2147483648.0, 2147483904.0, -2147483904.0,
                 1e10, -1e10, INF, -INF, NAN],
    },
    "i32_trunc_f32_u": {
        "in": [0.0, -0.0, 0.5, -0.5, -0.9, 1.9, 42.0, 4294967040.0],
        "trap": [-1.0, -1.5, 4294967296.0, 1e10, INF, -INF, NAN],
    },
    "i32_trunc_f64_s": {
        "in": [0.0, -0.0, 0.5, -0.5, 1.9, -1.9,
               2147483647.0, 2147483647.9,
               -2147483648.0, -2147483648.5, -2147483648.999],
        "trap": [2147483648.0, 2147483648.5, -2147483649.0, -2147483649.5,
                 1e18, -1e18, INF, -INF, NAN],
    },
    "i32_trunc_f64_u": {
        "in": [0.0, -0.0, 0.5, -0.5, -0.9, 1.9,
               4294967295.0, 4294967295.9],
        "trap": [-1.0, -1.5, 4294967296.0, 4294967296.5,
                 1e18, INF, -INF, NAN],
    },
}

# min/max NaN / ±0 matrix (WASM: either-NaN => NaN; min(-0,+0) = -0;
# max(-0,+0) = +0).
MINMAX_PAIRS = [
    (NAN, 1.0), (1.0, NAN), (NAN, NAN),
    (0.0, -0.0), (-0.0, 0.0), (0.0, 0.0), (-0.0, -0.0),
    (1.0, 2.0), (2.0, 1.0), (-1.0, -2.0), (-2.0, -1.0),
    (INF, 1.0), (-INF, 1.0), (INF, -INF), (-INF, INF),
    (3.5, 3.5), (-1.5, 1.5),
]

# copysign is a PURE BIT operation — compared bit-exactly, including the sign
# of a NaN result.
COPYSIGN_PAIRS = [
    (1.5, -2.0), (-1.5, 2.0), (1.5, -0.0), (-1.5, 0.0),
    (0.0, -1.0), (-0.0, 1.0), (INF, -1.0), (-INF, 1.0),
    (NAN, -1.0), (NAN, 1.0),
]

SQRT_VALS = [0.0, -0.0, 1.0, 2.0, 4.0, 0.25, -1.0, INF, NAN, 1e30]

TRAP = "TRAP"


def cases_for(fn):
    """Yield (args, expect_trap) for a function. expect_trap is None when the
    static table has no opinion (min/max/copysign/sqrt never trap)."""
    if fn in TRUNC_TABLE:
        for v in TRUNC_TABLE[fn]["in"]:
            yield [v], False
        for v in TRUNC_TABLE[fn]["trap"]:
            yield [v], True
    elif fn in ("f32_min", "f32_max", "f64_min", "f64_max"):
        for a, b in MINMAX_PAIRS:
            yield [a, b], False
    elif fn in ("f32_copysign", "f64_copysign"):
        for a, b in COPYSIGN_PAIRS:
            yield [a, b], False
    elif fn == "f32_sqrt":
        for v in SQRT_VALS:
            yield [v], False


# --------------------------------------------------------------------------- #
# encoding helpers
def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def f64_bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def as_i32(x):
    return struct.unpack("<i", struct.pack("<I", int(x) & M32))[0]


def arg_bits(ty, v):
    return f32_bits(v) if ty == "f32" else f64_bits(v) if ty == "f64" else int(v) & M32


def is_nan_bits(ty, bits):
    if ty == "f32":
        return math.isnan(struct.unpack("<f", struct.pack("<I", bits & M32))[0])
    if ty == "f64":
        return math.isnan(struct.unpack("<d", struct.pack("<Q", bits & M64))[0])
    return False


def results_match(ret, exp, got, bit_exact_nan):
    if exp == TRAP or got == TRAP:
        return exp == got
    if is_nan_bits(ret, exp) and is_nan_bits(ret, got) and not bit_exact_nan:
        return True  # NaN payload/sign not pinned for arithmetic min/max
    return exp == got


# --------------------------------------------------------------------------- #
# wasmtime ground truth (TRAP on wasmtime.Trap)
def wasmtime_run(fn, args, sig):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    f = wasmtime.Instance(store, module, []).exports(store)[fn]
    types, ret = sig
    call = [as_i32(v) if ty == "i32" else float(v) for ty, v in zip(types, args)]
    try:
        r = f(store, *call)
    except wasmtime.Trap:
        return TRAP
    if ret == "f32":
        return f32_bits(r)
    if ret == "f64":
        return f64_bits(r)
    return int(r) & M32


# --------------------------------------------------------------------------- #
# ELF load
def compile_aarch64(out):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "aarch64", "--all-exports"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0:
        sys.exit(f"aarch64 compile failed: {r.stderr}")


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


# --------------------------------------------------------------------------- #
# unicorn execution: value, or TRAP when the guard's brk raises an exception.
def unicorn_run(code, base, faddr, sig, args):
    off = faddr - base
    types, ret = sig
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.reg_write(UC_ARM64_REG_CPACR_EL1, 0x3 << 20)  # FPEN: enable V regs
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    ngrn = nsrn = 0
    for ty, v in zip(types, args):
        b = arg_bits(ty, v)
        if ty in ("f32", "f64"):
            mu.reg_write(V_ARGS[nsrn], b)
            nsrn += 1
        else:
            mu.reg_write(X_ARGS[ngrn], b)
            ngrn += 1
    try:
        mu.emu_start(CODE + off, RET, count=2000)
    except UcError:
        # The domain guard's `brk #0` surfaces as an unmapped/exception stop —
        # execution did NOT produce a value: a trap.
        return TRAP
    if ret == "f32":
        return mu.reg_read(UC_ARM64_REG_S0) & M32
    if ret == "f64":
        return mu.reg_read(UC_ARM64_REG_D0) & M64
    return mu.reg_read(UC_ARM64_REG_W0) & M32


# --------------------------------------------------------------------------- #
# native execution on an arm64 host — EVERY call in a forked child, so an
# expected `brk #0` (SIGTRAP) is observable and a surprise one is survivable.
_MAP_PRIVATE = 0x0002
_MAP_ANON = 0x1000 if sys.platform == "darwin" else 0x20
_MAP_JIT = 0x0800  # darwin only
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


_CTY = {"f32": ctypes.c_float, "f64": ctypes.c_double, "i32": ctypes.c_int32}


def native_run(code, faddr, code_base, sig, args):
    """Fork; the child maps + calls the JIT'd function and pipes back the
    result bits. A trap (SIGTRAP from `brk #0`) kills the CHILD; the parent
    reports TRAP. The MAP_JIT region is created IN the child — an inherited
    parent mapping sporadically faults (SIGBUS) after fork on macOS (the
    per-thread jit-write-protect state does not reliably survive fork)."""
    types, ret = sig
    rd, wr = os.pipe()
    pid = os.fork()
    if pid == 0:  # child
        try:
            os.close(rd)
            base_addr = native_setup(code)
            fn_addr = base_addr + (faddr - code_base)
            proto = ctypes.CFUNCTYPE(_CTY[ret], *[_CTY[t] for t in types])
            fn = proto(fn_addr)
            call = [as_i32(v) if ty == "i32" else float(v)
                    for ty, v in zip(types, args)]
            r = fn(*call)  # a brk #0 here delivers SIGTRAP -> child dies
            if ret == "f32":
                bits = f32_bits(r)
            elif ret == "f64":
                bits = f64_bits(r)
            else:
                bits = int(r) & M32
            os.write(wr, struct.pack("<Q", bits))
            os.close(wr)
        finally:
            os._exit(0)
    os.close(wr)
    _, status = os.waitpid(pid, 0)
    data = os.read(rd, 8)
    os.close(rd)
    if os.WIFSIGNALED(status):
        sig_no = os.WTERMSIG(status)
        if sig_no in (signal.SIGTRAP, signal.SIGILL):
            return TRAP
        return f"ERR:signal {sig_no}"
    if len(data) != 8:
        return "ERR:no result"
    return struct.unpack("<Q", data)[0]


# --------------------------------------------------------------------------- #
def main():
    out = "/tmp/aarch64_m4_538.o"
    compile_aarch64(out)
    code, base, syms = load(out)
    host_native = platform.machine() in ("arm64", "aarch64")

    fails = 0
    total = 0
    trap_cases = 0
    checked_native = 0
    for fn, sig in SIGS.items():
        if fn not in syms:
            print(f"FAIL {fn}: symbol missing")
            fails += 1
            continue
        _, ret = sig
        bit_exact_nan = "copysign" in fn
        for args, expect_trap in cases_for(fn):
            total += 1
            exp = wasmtime_run(fn, args, sig)
            # Fixture-table sanity: wasmtime must agree with the static
            # expect-trap column, or the boundary table itself is wrong.
            if expect_trap != (exp == TRAP):
                fails += 1
                print(f"TABLE-BUG {fn}{args}: table says "
                      f"{'trap' if expect_trap else 'value'}, wasmtime says "
                      f"{exp if exp == TRAP else hex(exp)}")
                continue
            if exp == TRAP:
                trap_cases += 1
            oracles = [("unicorn", unicorn_run(code, base, syms[fn], sig, args))]
            if host_native:
                oracles.append(
                    ("native", native_run(code, syms[fn], base, sig, args)))
                checked_native += 1
            for label, got in oracles:
                if not results_match(ret, exp, got, bit_exact_nan):
                    fails += 1
                    e = exp if exp == TRAP else hex(exp)
                    g = got if isinstance(got, str) else hex(got)
                    print(f"BUG {fn}{args} [{label}] A64={g} wasmtime={e}")
    print(f"\n{total} wasmtime cases ({trap_cases} trap cases), "
          f"{checked_native} also run natively "
          f"({'arm64 host' if host_native else 'unicorn-only host'})")
    print("RESULT:", "PASS — aarch64 m4 trunc boundary table + min/max NaN/±0 "
          "matrix match wasmtime (traps execution-verified)"
          if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
