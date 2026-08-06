#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 662
"""v0.54 L2 (#851) — the aarch64 float-completion EXECUTION differential.

Closes the four classes the VCR-SEL-005 third-backend op-parity oracle listed as
`Err(reason)`:

  ROUNDING        f{32,64}.{ceil,floor,trunc,nearest}  -> FRINT{P,M,Z,N}
  I64_TO_FP       f{32,64}.convert_i64_{s,u}           -> SCVTF/UCVTF (x-form)
  TRAP_TRUNC_I64  i64.trunc_f{32,64}_{s,u}             -> DOMAIN-GUARDED FCVTZ
  FP_MEM          f{32,64}.{load,store}                -> LDR/STR s|d, bounds-checked

The fatal class this gates is TRAP_TRUNC_I64. A64 `FCVTZS`/`FCVTZU` are MORE
TOTAL than WASM: on NaN they return 0 and out of range they SATURATE to
INT64_MIN/MAX (or 0/UINT64_MAX), where WASM Core §4.3.3 requires a TRAP. So this
harness runs a FULL BOUNDARY TABLE per trapping op — both sides of ±2^63 / 2^64,
the largest float strictly inside each bound, the smallest strictly outside,
±0, ±inf and NaN — and requires the trap cases to ACTUALLY TRAP.

Two independent oracles, exactly as the m4 harness does:
  (1) unicorn (UC_ARCH_ARM64): the guard's `brk #0` surfaces as UC_ERR_EXCEPTION;
  (2) natively on an arm64 host, EVERY call in a forked child, so an expected
      SIGTRAP is observed by the parent and a surprise trap is survivable.
The FP_MEM functions need `x28` = linear-memory base, which a plain native call
cannot establish, so they run under unicorn only (where x28 is set explicitly) —
their OOB cases are trap-checked the same way.

The static expect-trap column is VALIDATED AGAINST WASMTIME FIRST: if wasmtime
disagrees with the table, the FIXTURE is declared wrong (loud), so the boundary
table cannot silently drift vacuous.

Rounding is compared bit-exactly, which is what makes the `nearest` claim real:
FRINTN is round-to-nearest-TIES-TO-EVEN. The halfway table (0.5, 1.5, 2.5, 3.5
and negatives) DISTINGUISHES it from FRINTA (ties-away) — under FRINTA, 0.5 and
2.5 would come back 1 and 3 and this harness would fail.

Run (needs wasmtime + unicorn + pyelftools; the native leg needs an arm64 host):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_float_completion_851_differential.py
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
    UC_ARM64_REG_X0,
    UC_ARM64_REG_X1,
    UC_ARM64_REG_X28,
)

WAT = Path(__file__).with_name("aarch64_float_completion_851.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET, LINMEM = 0x100000, 0x200000, 0x300000, 0x1000000
LINMEM_SIZE = 0x20000  # 128 KiB mapped; the module declares 1 page (64 KiB)
V_ARGS = [UC_ARM64_REG_V0, UC_ARM64_REG_V1]
X_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
INF = float("inf")
NAN = float("nan")
TRAP = "TRAP"

PAGE = 65536


def f32(x):
    """Round a Python float to the nearest f32 (so the table means what it says)."""
    return struct.unpack("<f", struct.pack("<f", x))[0]


def f32_next(x, toward):
    """The adjacent f32 in the direction of `toward` (exact neighbour stepping —
    `math.nextafter` walks the f64 grid, which is far too fine here).

    Uses the standard IEEE-754 total-order key: for a negative bit pattern the
    ordering is REVERSED, so the key is the bitwise complement; for a
    non-negative one it is the pattern with the sign bit set. That maps -inf to
    the smallest key and +inf to the largest, so stepping the key by ±1 walks
    to the true float neighbour across zero and across the sign boundary."""
    x = f32(x)
    b = struct.unpack("<I", struct.pack("<f", x))[0]
    key = (~b & M32) if (b & 0x80000000) else (b | 0x80000000)
    key = (key + (1 if toward > x else -1)) & M32
    b = (key & 0x7FFFFFFF) if (key & 0x80000000) else (~key & M32)
    return struct.unpack("<f", struct.pack("<I", b))[0]


# Signatures: fn -> ([arg types], ret type).
SIGS = {
    "f32_ceil": (["f32"], "f32"),
    "f32_floor": (["f32"], "f32"),
    "f32_trunc": (["f32"], "f32"),
    "f32_nearest": (["f32"], "f32"),
    "f64_ceil": (["f64"], "f64"),
    "f64_floor": (["f64"], "f64"),
    "f64_trunc": (["f64"], "f64"),
    "f64_nearest": (["f64"], "f64"),
    "f32_convert_i64_s": (["i64"], "f32"),
    "f32_convert_i64_u": (["i64"], "f32"),
    "f64_convert_i64_s": (["i64"], "f64"),
    "f64_convert_i64_u": (["i64"], "f64"),
    "i64_trunc_f32_s": (["f32"], "i64"),
    "i64_trunc_f32_u": (["f32"], "i64"),
    "i64_trunc_f64_s": (["f64"], "i64"),
    "i64_trunc_f64_u": (["f64"], "i64"),
    "f32_mem_rt": (["i32", "f32"], "f32"),
    "f64_mem_rt": (["i32", "f64"], "f64"),
    "f32_mem_off": (["i32", "f32"], "f32"),
}

# Functions that touch linear memory: unicorn-only (they need x28 on entry).
MEM_FNS = {"f32_mem_rt", "f64_mem_rt", "f32_mem_off"}

# --------------------------------------------------------------------------- #
# ROUNDING table. The halfway values are the load-bearing part: WASM `nearest`
# is roundTiesToEven, so 0.5 -> 0, 1.5 -> 2, 2.5 -> 2, 3.5 -> 4. A ties-AWAY
# implementation (A64 FRINTA) gives 1 and 3 for 0.5 / 2.5 and fails here.
# The large / infinite / NaN entries catch the other classic wrong lowering: a
# round-trip through a 32-bit integer (which SATURATES) instead of a real
# round-to-integral.
ROUND_VALS_F32 = [
    0.0, -0.0, 0.5, -0.5, 1.5, -1.5, 2.5, -2.5, 3.5, -3.5,
    0.4999999, -0.4999999, 1.0, -1.0, 1.1, -1.1, 1.9, -1.9,
    8388607.5,            # largest f32 halfway case (2^23 - 0.5)
    float(2 ** 23), float(2 ** 24), -float(2 ** 24),
    float(2 ** 31), -float(2 ** 31), float(2 ** 63), -float(2 ** 63),
    1e30, -1e30, INF, -INF, NAN,
]
ROUND_VALS_F64 = [
    0.0, -0.0, 0.5, -0.5, 1.5, -1.5, 2.5, -2.5, 3.5, -3.5,
    0.49999999999999994, -0.49999999999999994, 1.0, -1.0, 1.9, -1.9,
    4503599627370495.5,   # largest f64 halfway case (2^52 - 0.5)
    float(2 ** 52), float(2 ** 53), -float(2 ** 53),
    float(2 ** 31) + 0.5, -float(2 ** 31) - 0.5,
    float(2 ** 63), -float(2 ** 63), 1e300, -1e300, INF, -INF, NAN,
]

# --------------------------------------------------------------------------- #
# I64 -> FLOAT table. Above 2^24 (f32) / 2^53 (f64) the convert must ROUND, and
# WASM requires round-to-nearest-EVEN — the ties entries below pin it.
CONVERT_VALS = [
    0, 1, -1, 2, -2, 42, -42,
    2 ** 23, 2 ** 24, 2 ** 24 + 1, 2 ** 24 + 3,     # f32 rounding onset
    -(2 ** 24) - 1, -(2 ** 24) - 3,
    2 ** 52, 2 ** 53, 2 ** 53 + 1, 2 ** 53 + 3,     # f64 rounding onset
    -(2 ** 53) - 1, -(2 ** 53) - 3,
    2 ** 62, -(2 ** 62),
    2 ** 63 - 1, -(2 ** 63),                        # i64 extremes
    2 ** 63, 2 ** 64 - 1, 2 ** 64 - 1024,           # only meaningful unsigned
]

# --------------------------------------------------------------------------- #
# THE #709 i64 BOUNDARY TABLE (WASM Core §4.3.3 trunc_s / trunc_u domains).
#
# Signed:   valid iff -2^63 <= x < 2^63   (lower bound INCLUSIVE)
# Unsigned: valid iff  -1   <  x < 2^64   (lower bound STRICT: trunc_u(-0.5)=0)
#
# The entries that matter most, and why:
#   * -2^63 is EXACTLY representable in both f32 and f64 and is IN range — an
#     off-by-one strict lower bound would trap a legal INT64_MIN input.
#   * The next float BELOW -2^63 is out of range and must trap. In f32 that is
#     -2^63·(1+2^-23); in f64 it is -2^63-2048 (the f64 ULP at that magnitude is
#     2048, which is exactly why the f64 lower bound can be inclusive here while
#     the i32/f64 row needed a strict -(2^31)-1).
#   * +2^63 itself TRAPS for signed (it is one past the top) but is IN range for
#     unsigned; +2^64 traps for both.
#   * NaN and ±inf always trap.
F32_2_63 = f32(2.0 ** 63)
F32_2_64 = f32(2.0 ** 64)
F64_2_63 = 2.0 ** 63
F64_2_64 = 2.0 ** 64

TRUNC_TABLE = {
    "i64_trunc_f32_s": {
        "in": [0.0, -0.0, 0.5, -0.5, 1.9, -1.9, 100.75,
               f32_next(F32_2_63, 0.0),          # largest in-range f32
               -F32_2_63,                        # INT64_MIN, exactly representable
               f32(2 ** 62), f32(-(2 ** 62))],
        "trap": [F32_2_63,                       # +2^63 is OUT (exclusive)
                 f32_next(-F32_2_63, -INF),      # first f32 below -2^63
                 F32_2_64, -F32_2_64, 1e30, -1e30, INF, -INF, NAN],
    },
    "i64_trunc_f32_u": {
        "in": [0.0, -0.0, 0.5, -0.5, -0.9, 1.9, 42.0,
               F32_2_63,                         # in range unsigned
               f32_next(F32_2_64, 0.0),          # largest in-range f32
               f32(2 ** 24)],
        "trap": [-1.0, -1.5, F32_2_64, 1e30, -1e30, INF, -INF, NAN],
    },
    "i64_trunc_f64_s": {
        "in": [0.0, -0.0, 0.5, -0.5, 1.9, -1.9,
               math.nextafter(F64_2_63, 0.0),    # largest in-range f64
               -F64_2_63,                        # INT64_MIN, exactly representable
               float(2 ** 62), -float(2 ** 62),
               9007199254740993.0],
        "trap": [F64_2_63,
                 math.nextafter(-F64_2_63, -INF),  # -2^63 - 2048
                 F64_2_64, -F64_2_64, 1e300, -1e300, INF, -INF, NAN],
    },
    "i64_trunc_f64_u": {
        "in": [0.0, -0.0, 0.5, -0.5, -0.9, 1.9,
               F64_2_63,
               math.nextafter(F64_2_64, 0.0),    # largest in-range f64
               float(2 ** 53)],
        "trap": [-1.0, -1.5, F64_2_64, 1e300, -1e300, INF, -INF, NAN],
    },
}

# --------------------------------------------------------------------------- #
# FP_MEM table. 65532 is IN bounds for a 4-byte access and OUT for an 8-byte
# one on this one-page memory — the width-aware half of the #865 bound. The
# offset=16 variant must additionally fold 16 into the compile-time constant.
MEM_ADDRS = [0, 4, 8, 4096, PAGE - 8, PAGE - 4, PAGE - 1, PAGE, 0xFFFFFFFF]
MEM_VALS = [1.5, -1.5, 0.0, -0.0, INF, -INF, NAN, 3.14159265, 1e30]


def cases_for(fn):
    """Yield (args, expect_trap) for a function; expect_trap is False for the
    total ops (the table has no opinion there — but wasmtime still validates it)."""
    if fn in TRUNC_TABLE:
        for v in TRUNC_TABLE[fn]["in"]:
            yield [v], False
        for v in TRUNC_TABLE[fn]["trap"]:
            yield [v], True
    elif fn.endswith(("_ceil", "_floor", "_trunc", "_nearest")):
        vals = ROUND_VALS_F32 if fn.startswith("f32") else ROUND_VALS_F64
        for v in vals:
            yield [v], False
    elif "convert_i64" in fn:
        for v in CONVERT_VALS:
            yield [v], False
    elif fn in MEM_FNS:
        off = 16 if fn.endswith("_off") else 0
        size = 8 if fn.startswith("f64") else 4
        for a in MEM_ADDRS:
            for v in MEM_VALS:
                yield [a, v], (a + off + size) > PAGE
    else:
        raise AssertionError(f"no case generator for {fn}")


# --------------------------------------------------------------------------- #
# encoding helpers
def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def f64_bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def as_i32(x):
    return struct.unpack("<i", struct.pack("<I", int(x) & M32))[0]


def as_i64(x):
    return struct.unpack("<q", struct.pack("<Q", int(x) & M64))[0]


def arg_bits(ty, v):
    if ty == "f32":
        return f32_bits(v)
    if ty == "f64":
        return f64_bits(v)
    if ty == "i64":
        return int(v) & M64
    return int(v) & M32


def is_nan_bits(ty, bits):
    if ty == "f32":
        return math.isnan(struct.unpack("<f", struct.pack("<I", bits & M32))[0])
    if ty == "f64":
        return math.isnan(struct.unpack("<d", struct.pack("<Q", bits & M64))[0])
    return False


def results_match(ret, exp, got):
    """Bit-exact, EXCEPT that a NaN result compares NaN-aware: WASM §4.3.3
    leaves the sign and payload of a produced NaN non-deterministic. Every op
    here that can produce NaN does so by PASSING ONE THROUGH (rounding) or not
    at all, so this is the only concession — values, traps and ±0 signs are
    all compared bit-for-bit."""
    if exp == TRAP or got == TRAP:
        return exp == got
    if is_nan_bits(ret, exp) and is_nan_bits(ret, got):
        return True
    return exp == got


# --------------------------------------------------------------------------- #
# wasmtime ground truth (TRAP on wasmtime.Trap)
def wasmtime_run(engine, module, fn, args, sig):
    store = wasmtime.Store(engine)
    f = wasmtime.Instance(store, module, []).exports(store)[fn]
    types, ret = sig
    call = []
    for ty, v in zip(types, args):
        if ty == "i32":
            call.append(as_i32(v))
        elif ty == "i64":
            call.append(as_i64(v))
        else:
            call.append(float(v))
    try:
        r = f(store, *call)
    except wasmtime.Trap:
        return TRAP
    if ret == "f32":
        return f32_bits(r)
    if ret == "f64":
        return f64_bits(r)
    if ret == "i64":
        return int(r) & M64
    return int(r) & M32


# --------------------------------------------------------------------------- #
# ELF load
def compile_aarch64(out):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "aarch64", "--all-exports"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0:
        sys.exit(f"aarch64 compile failed: {r.stderr}")
    if "skipping function" in r.stderr:
        skipped = [ln for ln in r.stderr.splitlines() if "skipping function" in ln]
        sys.exit("aarch64 compile SKIPPED functions (the surface regressed):\n"
                 + "\n".join(skipped))


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
# unicorn execution: a value, or TRAP when a guard's brk raises an exception.
def unicorn_run(code, base, faddr, sig, args):
    off = faddr - base
    types, ret = sig
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.reg_write(UC_ARM64_REG_CPACR_EL1, 0x3 << 20)  # FPEN: enable V regs
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_map(LINMEM, LINMEM_SIZE)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    mu.reg_write(UC_ARM64_REG_X28, LINMEM)  # the linear-memory base convention
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
        mu.emu_start(CODE + off, RET, count=4000)
    except UcError:
        # A domain guard's / bounds check's `brk #0` stops execution without
        # producing a value: a trap.
        return TRAP
    if ret == "f32":
        return mu.reg_read(UC_ARM64_REG_S0) & M32
    if ret == "f64":
        return mu.reg_read(UC_ARM64_REG_D0) & M64
    if ret == "i64":
        return mu.reg_read(UC_ARM64_REG_X0) & M64
    return mu.reg_read(UC_ARM64_REG_X0) & M32


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


_CTY = {"f32": ctypes.c_float, "f64": ctypes.c_double,
        "i32": ctypes.c_int32, "i64": ctypes.c_int64}


def native_run(code, faddr, code_base, sig, args):
    """Fork; the child maps + calls the JIT'd function and pipes back the result
    bits. A trap (SIGTRAP from `brk #0`) kills the CHILD; the parent reports
    TRAP. The MAP_JIT region is created IN the child — an inherited parent
    mapping sporadically faults after fork on macOS."""
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
            call = []
            for ty, v in zip(types, args):
                if ty == "i32":
                    call.append(as_i32(v))
                elif ty == "i64":
                    call.append(as_i64(v))
                else:
                    call.append(float(v))
            r = fn(*call)  # a brk #0 here delivers SIGTRAP -> child dies
            if ret == "f32":
                bits = f32_bits(r)
            elif ret == "f64":
                bits = f64_bits(r)
            else:
                bits = int(r) & (M64 if ret == "i64" else M32)
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
    out = "/tmp/aarch64_float_completion_851.o"
    compile_aarch64(out)
    code, base, syms = load(out)
    host_native = platform.machine() in ("arm64", "aarch64")

    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))

    fails = 0
    total = 0
    trap_cases = 0
    checked_native = 0
    per_class = {"rounding": 0, "convert": 0, "trunc": 0, "mem": 0}

    for fn, sig in SIGS.items():
        if fn not in syms:
            print(f"FAIL {fn}: symbol missing from the aarch64 object — the op "
                  f"is NOT lowering (a parity-gate Ok(()) entry would be stale)")
            fails += 1
            continue
        _, ret = sig
        cls = ("trunc" if fn in TRUNC_TABLE else
               "mem" if fn in MEM_FNS else
               "convert" if "convert_i64" in fn else "rounding")
        for args, expect_trap in cases_for(fn):
            total += 1
            per_class[cls] += 1
            exp = wasmtime_run(engine, module, fn, args, sig)
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
            # The memory functions need x28 on entry, which a plain native call
            # cannot set — unicorn is their only oracle.
            if host_native and fn not in MEM_FNS:
                oracles.append(
                    ("native", native_run(code, syms[fn], base, sig, args)))
                checked_native += 1
            for label, got in oracles:
                if not results_match(ret, exp, got):
                    fails += 1
                    e = exp if exp == TRAP else hex(exp)
                    g = got if isinstance(got, str) else hex(got)
                    print(f"BUG {fn}{args} [{label}] A64={g} wasmtime={e}")

    # NON-VACUITY floor: each class must actually have been exercised, and the
    # trapping-truncation class must contain real trap cases (a table that
    # somehow lost its out-of-range rows would be worthless).
    if total < 300:
        print(f"FAIL: only {total} checks — the case table collapsed")
        fails += 1
    for cls, n in per_class.items():
        if n == 0:
            print(f"FAIL: class '{cls}' contributed 0 checks")
            fails += 1
    if trap_cases < 40:
        print(f"FAIL: only {trap_cases} trap cases — the #709 boundary table "
              f"is not exercising the out-of-range side")
        fails += 1

    print(f"\n{total} wasmtime cases ({trap_cases} trap cases), "
          f"{checked_native} also run natively "
          f"({'arm64 host' if host_native else 'unicorn-only host'})")
    print("  per class: " + ", ".join(f"{k}={v}" for k, v in per_class.items()))
    print("RESULT:", "PASS — aarch64 rounding (ties-to-even), i64->float "
          "converts, DOMAIN-GUARDED i64 truncations (boundary table, traps "
          "execution-verified) and bounds-checked FP memory all match wasmtime"
          if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
