#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 96276
"""#869 — the ARM 64-bit integer<->float conversion family EXECUTION
differential (cortex-m7dp, Thumb-2, unicorn) vs wasmtime.

Eight ops under test (gale's six + the #756 i64.trunc_f64 pair):

  f32.convert_i64_{s,u} / f64.convert_i64_{s,u}
      ARMv7E-M VFP has no 64-bit-integer VCVT, so the lowering assembles the
      value from two exact 32-bit conversions: a = (f64)hi * 2^32 (exact),
      b = (f64)lo (exact), s = a + b (ONE correct RNE rounding). The f32
      targets additionally carry a Fast2Sum residual + branch-free
      ROUND-TO-ODD fixup before the demote — a bare demote of s would
      DOUBLE-ROUND (the 0x8000008000000001 row below is the killer case).
      Converts are TOTAL: any trap on our side fails the run.

  i64.trunc_f32_{s,u} / i64.trunc_f64_{s,u}
      The TRAPPING truncations (WASM §4.3.3): NaN and out-of-i64-range MUST
      trap. The lowering is the #709-class i64 domain guard (compare + UDF)
      in front of the #782 saturating word-decompose — a bare decompose (or a
      bare AEABI __aeabi_f2lz call) would saturate instead of trapping: the
      "ARM more-total-than-WASM" silent-miscompile class
      (#633/#666/#709/#665/#642). Every trap row is EXECUTED here: wasmtime
      must trap AND the ARM side must stop at a UDF; a value where wasmtime
      traps (or vice versa) fails the run.

Also gated:
  * falcon's exact flags (-t cortex-m7dp --relocatable): all family exports
    must reach the symbol table (the #869 skip class, RED before the fix).
  * decline-honesty on the single-precision cortex-m4f: every family member
    runs on f64 machinery, so all eight must be LOUD-declined there (absent
    from the symbol table) — never undefined VCVT.F64 encodings on FPv4-SP.
  * >=10k fixed-seed random patterns per direction (bit-exact, trap-aware).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=<target>/debug/synth python scripts/repro/i64_float_conv_869_differential.py
"""

import os
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_D0,
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R11,
    UC_ARM_REG_S0,
    UC_ARM_REG_SP,
)

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn naming
    UC_ARM_REG_C1_C0_2 = None
    UC_ARM_REG_FPEXC = None

WAT = Path(__file__).with_name("i64_float_conv_869.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
MEMBASE = 0x20000000  # ARM32 R11/fp linear-memory base at reset (cortex_m.rs)

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
INF = float("inf")
NAN = float("nan")

# fn -> (arg type, result type)
CONVERTS = {
    "i64u_to_f32": ("i64u", "f32"),
    "i64s_to_f32": ("i64s", "f32"),
    "i64u_to_f64": ("i64u", "f64"),
    "i64s_to_f64": ("i64s", "f64"),
}
TRUNCS = {
    "f32_to_i64s": ("f32", "i64"),
    "f32_to_i64u": ("f32", "i64"),
    "f64_to_i64s": ("f64", "i64"),
    "f64_to_i64u": ("f64", "i64"),
}
FAMILY = {**CONVERTS, **TRUNCS}

# ---------------------------------------------------------------------------
# Convert boundary table: u64 bit patterns (the _s forms reinterpret them as
# two's-complement i64). Rows pin: zero/small exact values, hi==0 (the
# Fast2Sum a==0 edge), INT64/UINT64 extremes, round-to-nearest-even TIES at
# both f32 (24-bit) and f64 (53-bit) granularity — including the
# double-rounding killers where RN53-then-RN24 differs from direct RN24 — and
# plain mid-range patterns exercising the borrow/carry of the fixup.
CONVERT_PATTERNS = [
    0x0000000000000000,
    0x0000000000000001,
    0x0000000000000002,
    0x000000000000002A,
    0x00000000FFFFFFFF,  # hi == 0: the exact single-word path
    0x0000000100000000,  # lo == 0
    0x0000000100000001,
    0x0000001000000001,  # small hi, sticky in lo
    0x0000000001000001,  # 2^24 + 1: first f32 rounding (tie -> even)
    0x0000000001000003,
    0x0000000002000002,
    0x0000000002000006,
    0x0020000000000001,  # 2^53 + 1: first f64 rounding (tie -> even)
    0x0020000000000003,
    0x0040000000000004,
    0x123456789ABCDEF0,
    0x7FFFFFFFFFFFFFFF,  # INT64_MAX
    0x7FFFFFFFFFFFFC00,
    0x8000000000000000,  # INT64_MIN as _s; 2^63 as _u
    0x8000000000000001,
    0x8000000000000200,  # 2^63 + 512:  f64 tie -> even (down)
    0x8000000000000201,  # 2^63 + 513:  f64 rounds up
    0x8000000000000600,  # 2^63 + 3*512: f64 tie -> even (up)
    0x8000008000000000,  # 2^63 + 2^39: exact f32 tie -> even (down)
    0x8000008000000001,  # DOUBLE-ROUNDING KILLER: f64 hides the +1 sticky
    0x8000018000000001,  # odd-mantissa neighbor of the above
    0xFFFFFF7FFFFFFFFF,  # just below the top f32 tie
    0xFFFFFF8000000000,  # top f32 tie (rounds to 2^64, even)
    0xFFFFFF8000000001,  # KILLER at the very top: must round UP to 2^64
    0xFFFFFFFFFFFFF800,
    0xFFFFFFFFFFFFFBFF,
    0xFFFFFFFFFFFFFC00,  # top f64 tie
    0xFFFFFFFFFFFFFC01,
    0xFFFFFFFFFFFFFFFF,  # UINT64_MAX / -1
    0xFFFFFFFF00000000,
    0xC000000000000000,
    0x8000000180000001,
]

# Trunc boundary table per source type: every i64-range edge on BOTH sides,
# NaN/±inf, the exact 2^63 / -2^63 / 2^64 boundaries, fraction rows, and the
# unsigned (-1, 0) truncate-to-zero window. wasmtime decides trap-vs-value;
# the ARM side must agree row by row.
TRUNC_VALUES = {
    "f32": [
        0.0, -0.0, 0.5, -0.5, 0.9, -0.9, 1.5, -1.5, 42.0, -42.0, 100.75,
        -0.99609375,             # in (-1,0): _u truncates to 0 (no trap)
        2147483648.0, -2147483648.0, 4294967296.0,
        1e10, -1e10, 3e18, -3e18,
        9223371487098961920.0,   # largest f32 < 2^63: _s in-range max
        9223372036854775808.0,   # 2^63 exactly: _s TRAPS
        -9223372036854775808.0,  # -2^63 exactly: _s in-range minimum
        -9223373136366403584.0,  # first f32 below -2^63: _s TRAPS
        18446742974197923840.0,  # largest f32 < 2^64: _u in-range max
        18446744073709551616.0,  # 2^64 exactly: _u TRAPS
        -1.0,                    # _u TRAPS (strict lower bound)
        -1.5, 1e30, -1e30, INF, -INF, NAN,
    ],
    "f64": [
        0.0, -0.0, 0.5, -0.5, 0.9, -0.9, 1.5, -1.5, 42.0, -42.0, 100.75,
        -0.9999999999999999,     # in (-1,0): _u truncates to 0 (no trap)
        2147483648.5, -2147483649.5, 4294967296.5,
        1e10, -1e10, 3e18, -3e18,
        9223372036854774784.0,   # largest f64 < 2^63: _s in-range max
        9223372036854775808.0,   # 2^63 exactly: _s TRAPS
        -9223372036854775808.0,  # -2^63 exactly: _s in-range minimum
        -9223372036854777856.0,  # first f64 below -2^63: _s TRAPS
        18446744073709549568.0,  # largest f64 < 2^64: _u in-range max
        18446744073709551616.0,  # 2^64 exactly: _u TRAPS
        -1.0,                    # _u TRAPS (strict lower bound)
        -1.5, 1e300, -1e300, INF, -INF, NAN,
    ],
}

FUZZ_PER_DIR = int(os.environ.get("I64_FLOAT_FUZZ", "12000"))


def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def f64_bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def to_signed(b):
    return b - (1 << 64) if b >= (1 << 63) else b


# ---------------------------------------------------------------------------
def wasmtime_instance():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    return store, wasmtime.Instance(store, module, []).exports(store)


def compile_or_die(out, extra, what):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, *extra]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0:
        sys.exit(f"{what} compile failed: {r.stderr}")
    return r.stderr + r.stdout


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":  # #489: symtab, not disasm text
            for sy in sec.iter_symbols():
                if sy.name:
                    syms[sy.name] = sy["st_value"]
    return code, base, syms


# ---------------------------------------------------------------------------
# ARM32 Thumb-2 unicorn execution. AAPCS-VFP: i64 args in R0:R1, f32/f64 args
# in S0/D0; f32/f64 results in S0/D0, i64 results in R0:R1 (reading only R0
# would blind every hi-word bug). Returns ('ok', bits) / ('trap-udf', info) /
# ('fault', info).
def arm32_run(text, base, addr, aty, rty, arg_bits_val):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    map_base = base & ~0xFFF
    size = ((len(text) + (base - map_base)) + 0xFFF) & ~0xFFF
    uc.mem_map(map_base, max(size, 0x1000))
    uc.mem_write(base, text)
    uc.mem_map(0x30000, 0x10000)  # stack
    uc.mem_map(MEMBASE, 0x10000)  # linear-memory window (R11 base)
    uc.reg_write(UC_ARM_REG_SP, 0x38000)
    uc.reg_write(UC_ARM_REG_R11, MEMBASE)
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)  # CPACR CP10/CP11
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)  # FPEXC.EN
    if aty in ("i64u", "i64s"):
        uc.reg_write(UC_ARM_REG_R0, arg_bits_val & M32)
        uc.reg_write(UC_ARM_REG_R1, (arg_bits_val >> 32) & M32)
    elif aty == "f32":
        uc.reg_write(UC_ARM_REG_S0, arg_bits_val)
    else:
        uc.reg_write(UC_ARM_REG_D0, arg_bits_val)
    ret = 0x38000
    uc.reg_write(UC_ARM_REG_LR, ret | 1)
    try:
        uc.emu_start(addr | 1, ret & ~1, count=2000)
    except UcError as e:
        pc = uc.reg_read(UC_ARM_REG_PC)
        kind = "fault"
        if base <= pc < base + len(text):
            hw = struct.unpack("<H", text[pc - base: pc - base + 2])[0]
            if hw & 0xFF00 == 0xDE00:  # Thumb UDF
                kind = "trap-udf"
        return (kind, f"{e} at pc={pc:#x}")
    if rty == "f32":
        return ("ok", uc.reg_read(UC_ARM_REG_S0) & M32)
    if rty == "f64":
        return ("ok", uc.reg_read(UC_ARM_REG_D0) & M64)
    lo = uc.reg_read(UC_ARM_REG_R0) & M32
    hi = uc.reg_read(UC_ARM_REG_R1) & M32
    return ("ok", lo | (hi << 32))


# ---------------------------------------------------------------------------
def wasmtime_convert(store, wexp, fn, aty, rty, pattern):
    """Expected result BITS for a (total) convert — a wasmtime trap here is a
    harness bug, not a data point."""
    arg = to_signed(pattern)  # wasmtime's i64 params are two's-complement
    try:
        r = wexp[fn](store, arg)
    except wasmtime.Trap:
        sys.exit(f"TABLE-BUG: wasmtime TRAPPED on {fn}({pattern:#x}) — "
                 f"convert_i64 is total")
    return f32_bits(r) if rty == "f32" else f64_bits(r)


def wasmtime_trunc(store, wexp, fn, v):
    """('trap', None) or ('ok', u64 bits) from wasmtime for a TRAPPING trunc."""
    try:
        r = wexp[fn](store, float(v))
    except wasmtime.Trap:
        return ("trap", None)
    return ("ok", int(r) & M64)


def check_convert(store, wexp, text, base, syms, fn, pattern, fails, what):
    aty, rty = CONVERTS[fn]
    want = wasmtime_convert(store, wexp, fn, aty, rty, pattern)
    kind, got = arm32_run(text, base, syms[fn], aty, rty, pattern)
    if kind != "ok":
        print(f"BUG [{what}] {fn}({pattern:#x}) -> {kind}: {got} — converts "
              f"are TOTAL (wasmtime bits {want:#x})")
        return fails + 1
    if got != want:
        print(f"BUG [{what}] {fn}({pattern:#x}) = {got:#x} != wasmtime "
              f"{want:#x} (round-to-nearest-even violation)")
        return fails + 1
    return fails


def check_trunc(store, wexp, text, base, syms, fn, v, fails, what):
    aty, _ = TRUNCS[fn]
    bits = f32_bits(v) if aty == "f32" else f64_bits(v)
    wkind, want = wasmtime_trunc(store, wexp, fn, v)
    kind, got = arm32_run(text, base, syms[fn], aty, "i64", bits)
    if wkind == "trap":
        if kind != "trap-udf":
            print(f"BUG [{what}] {fn}({v!r}): wasmtime TRAPS but ARM "
                  f"{'returned ' + hex(got) if kind == 'ok' else kind} — the "
                  f"#709-class silent-miscompile (missing domain guard)")
            return fails + 1
        return fails
    if kind != "ok":
        print(f"BUG [{what}] {fn}({v!r}) -> {kind}: {got} — wasmtime returns "
              f"{want:#x} (guard over-traps)")
        return fails + 1
    if got != want:
        print(f"BUG [{what}] {fn}({v!r}) = {got:#x} != wasmtime {want:#x}")
        return fails + 1
    return fails


# ---------------------------------------------------------------------------
def _rand_u64(rng):
    """u64 patterns biased toward tie-prone shapes: a short mantissa shifted
    high (exactly the round/sticky geometry of the 24- and 53-bit roundings)
    alongside uniform patterns and small/word-edge values."""
    r = rng.random()
    if r < 0.40:
        return rng.getrandbits(64)
    if r < 0.70:  # short significand << k, then poison low bits sometimes
        v = rng.getrandbits(rng.randint(20, 30)) << rng.randint(0, 40)
        if rng.random() < 0.5:
            v |= rng.getrandbits(rng.randint(1, 10))
        return v & M64
    if r < 0.85:  # dense high bits (top-of-range rounding, carry-out shapes)
        return (M64 ^ rng.getrandbits(rng.randint(1, 41))) & M64
    return rng.getrandbits(rng.randint(1, 64))


def _rand_f32_bits(rng):
    r = rng.random()
    if r < 0.5:
        return rng.getrandbits(32)
    if r < 0.85:  # exponents around the i64 boundary (2^62..2^65)
        exp = rng.randint(180, 195)
        return (rng.getrandbits(1) << 31) | (exp << 23) | rng.getrandbits(23)
    return (rng.getrandbits(1) << 31) | (0xFF << 23) | rng.getrandbits(23)


def _rand_f64_bits(rng):
    r = rng.random()
    if r < 0.5:
        return rng.getrandbits(64)
    if r < 0.85:
        exp = rng.randint(1084, 1091)  # 2^61..2^68
        return (rng.getrandbits(1) << 63) | (exp << 52) | rng.getrandbits(52)
    return (rng.getrandbits(1) << 63) | (0x7FF << 52) | rng.getrandbits(52)


# ---------------------------------------------------------------------------
def main():
    store, wexp = wasmtime_instance()
    fails = 0
    total = 0

    # ==== gale's exact flags: -t cortex-m7dp --relocatable =================
    # RED before #869: all eight family exports skipped. GREEN: all present
    # (plus the four 32-bit control rows that always lowered).
    compile_or_die("/tmp/i64_float_conv_869_reloc.o",
                   ["-b", "arm", "--target", "cortex-m7dp", "--relocatable"],
                   "ARM32 --relocatable (falcon flags)")
    _, _, reloc_syms = load("/tmp/i64_float_conv_869_reloc.o")
    for fn in [*FAMILY, "i32u_to_f32", "i32s_to_f32", "f32_to_i32s",
               "wrap_then_i32u"]:
        total += 1
        if fn not in reloc_syms:
            fails += 1
            print(f"FAIL [falcon-flags] {fn}: SKIPPED under -t cortex-m7dp "
                  f"--relocatable (the #869 skip class)")

    # ==== decline-honesty: single-precision m4f must LOUD-decline ==========
    # Every family member's lowering runs on f64 machinery (promote/decompose/
    # two-word build) — undefined encodings on FPv4-SP. Absent symbol = the
    # honest decline; present = the capability gate regressed.
    compile_or_die("/tmp/i64_float_conv_869_m4f.o",
                   ["-b", "arm", "--target", "cortex-m4f", "--all-exports", "--allow-skipped-exports"],
                   "ARM32 cortex-m4f")
    _, _, m4f_syms = load("/tmp/i64_float_conv_869_m4f.o")
    for fn in FAMILY:
        total += 1
        if fn in m4f_syms:
            fails += 1
            print(f"FAIL [m4f] {fn}: compiled on a single-precision target — "
                  f"expected a LOUD decline (f64 machinery on FPv4-SP)")

    # ==== execute the boundary tables (cortex-m7dp self-contained) =========
    compile_or_die("/tmp/i64_float_conv_869_arm.elf",
                   ["-b", "arm", "--target", "cortex-m7dp", "--all-exports", "--allow-skipped-exports"],
                   "ARM32 cortex-m7dp")
    text, base, syms = load("/tmp/i64_float_conv_869_arm.elf")
    for fn in FAMILY:
        if fn not in syms:
            sys.exit(f"FATAL [m7dp] {fn}: symbol missing from the execution "
                     f"build — cannot gate")

    for fn in CONVERTS:
        for pattern in CONVERT_PATTERNS:
            total += 1
            fails = check_convert(store, wexp, text, base, syms, fn, pattern,
                                  fails, "boundary")
    for fn, (aty, _) in TRUNCS.items():
        for v in TRUNC_VALUES[aty]:
            total += 1
            fails = check_trunc(store, wexp, text, base, syms, fn, v, fails,
                                "boundary")

    # ==== fixed-seed fuzz: converts (u64 patterns) and truncs (float bits) ==
    import random
    rng = random.Random(0x869F17E)
    for _ in range(FUZZ_PER_DIR):
        pattern = _rand_u64(rng)
        for fn in CONVERTS:
            total += 1
            f = fails
            fails = check_convert(store, wexp, text, base, syms, fn, pattern,
                                  fails, "fuzz")
            if fails > f and fails > 25:
                sys.exit(f"FAIL (aborted early at {fails} failures)")
    for src, gen in (("f32", _rand_f32_bits), ("f64", _rand_f64_bits)):
        fns = [fn for fn, (aty, _) in TRUNCS.items() if aty == src]
        for _ in range(FUZZ_PER_DIR):
            b = gen(rng)
            if src == "f32":
                v = struct.unpack("<f", struct.pack("<I", b))[0]
            else:
                v = struct.unpack("<d", struct.pack("<Q", b))[0]
            for fn in fns:
                total += 1
                f = fails
                fails = check_trunc(store, wexp, text, base, syms, fn, v,
                                    fails, "fuzz")
                if fails > f and fails > 25:
                    sys.exit(f"FAIL (aborted early at {fails} failures)")

    print(f"\n{total} checks (boundary + {FUZZ_PER_DIR}/direction fixed-seed "
          f"fuzz), trap rows executed on both sides")
    print("RESULT:", "PASS — i64<->float family matches wasmtime bit-exactly "
          "on cortex-m7dp (incl. executed NaN/±inf/2^63/-2^63/2^64 trap rows "
          "and the double-rounding killers); m4f loud-declines; falcon flags "
          "lower all exports" if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
