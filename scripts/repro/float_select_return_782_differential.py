#!/usr/bin/env python3
"""#782(b) — EXECUTION-validate float `select` + explicit float `return`.

The dominant decline class on the real falcon-flight-v1.123 fused core
(12/26 skipped functions, incl. run-stabilization) was
"GI-FPU-002: an integer operation popped an f32 (VFP) stack value". It is not
register pressure: untyped `select` over two f32/f64 values (falcon's clamp
idiom) and an explicit `return` of an f32 result both routed a VFP-resident
value into the integer pop, which loud-declined the whole function.

The fix lowers float `select` as a bit-pattern select through core registers
(VMOV reinterpret + the same flag-safe CMP + IT;MOV — bit-exact, select PICKS
a value and never computes one) and homes an explicit float return in S0/D0
exactly like the fall-through epilogue.

Also covered (found adversarially while clearing the float class): the WIDE
(i64) select hi-half SILENT miscompile — the narrow integer select moved only
the lo register, so `select` over i64 (or soft-float f64) values returned
val2's lo paired with val1's hi whenever cond == 0. `seli64` pins both halves
on cortex-m3 (soft-float) AND cortex-m7dp.

Differential, unicorn (cortex-m7dp) vs wasmtime:
  * sel32 / sel32b / clamp32 — strict BIT-exact compare (a select must
    preserve NaN payloads exactly; no NaN leniency).
  * sel64 / seli64           — strict bit-exact compare (both halves).
  * ret32 / ret64            — NaN-lenient (they contain an fadd), non-NaN
    bit-exact.
Honest capability gates pinned: on cortex-m3 (no FPU) the fns containing f32
arithmetic (sel32b/clamp32/ret32/ret64) honest-skip while the pure value-pick
fns (sel32/sel64/seli64) lower soft-float and execute correctly; on
cortex-m4f (single-precision) the f64 fns honest-skip, the f32 fns lower.

RED on origin/main: every function containing the float select / float
explicit return DECLINES (symbol missing) AND seli64 returns the wrong hi
half -> exit 1. GREEN after the fix.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=/path/to/synth python scripts/repro/float_select_return_782_differential.py
"""

import os
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc
from unicorn.arm_const import (
    UC_ARM_REG_D0,
    UC_ARM_REG_D1,
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R11,
    UC_ARM_REG_S0,
    UC_ARM_REG_S1,
    UC_ARM_REG_SP,
)

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn naming
    UC_ARM_REG_C1_C0_2 = None
    UC_ARM_REG_FPEXC = None

WAT = Path(__file__).with_name("float_select_return_782.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
MEMBASE = 0x20000000  # R11/fp linear-memory base at reset (cortex_m.rs)


def compile_elf(out, target):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
         "--target", target, "--all-exports"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    return r.returncode == 0, (r.stderr + r.stdout)


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    data, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":  # #489: symtab, not disasm text
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
    return data, base, syms


def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def bits_f32(b):
    return struct.unpack("<f", struct.pack("<I", b & 0xFFFFFFFF))[0]


def f64_bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def bits_f64(b):
    return struct.unpack("<d", struct.pack("<Q", b & 0xFFFFFFFFFFFFFFFF))[0]


def is_nan32(bits):
    b = bits & 0xFFFFFFFF
    return (b & 0x7F800000) == 0x7F800000 and (b & 0x007FFFFF) != 0


def is_nan64(bits):
    b = bits & 0xFFFFFFFFFFFFFFFF
    return (b & 0x7FF0000000000000) == 0x7FF0000000000000 and (
        b & 0x000FFFFFFFFFFFFF) != 0


def f32_bits_eq_lenient(got, want):
    """NaN==NaN regardless of payload (WASM Core 4.3.3 leaves arithmetic NaN
    results non-deterministic); every non-NaN result stays bit-exact."""
    if is_nan32(got) and is_nan32(want):
        return True
    return (got & 0xFFFFFFFF) == (want & 0xFFFFFFFF)


def f64_bits_eq_lenient(got, want):
    if is_nan64(got) and is_nan64(want):
        return True
    return (got & 0xFFFFFFFFFFFFFFFF) == (want & 0xFFFFFFFFFFFFFFFF)


def new_uc(text, text_base):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    try:
        from unicorn.arm_const import UC_CPU_ARM_MAX
        uc.ctl_set_cpu_model(UC_CPU_ARM_MAX)
    except (ImportError, AttributeError):
        pass
    map_base = text_base & ~0xFFF
    size = ((len(text) + (text_base - map_base)) + 0xFFF) & ~0xFFF
    uc.mem_map(map_base, max(size, 0x1000))
    uc.mem_write(text_base, text)
    uc.mem_map(0x30000, 0x10000)  # stack
    uc.mem_map(MEMBASE, 0x10000)  # linear-memory window (R11/fp base)
    uc.reg_write(UC_ARM_REG_SP, 0x38000)
    uc.reg_write(UC_ARM_REG_R11, MEMBASE)
    # Enable the FPU (off at reset): CPACR CP10/CP11 + FPEXC.EN.
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    return uc


def run(text, base, addr, r0=None, d0=None, d1=None, s0=None, s1=None):
    uc = new_uc(text, base)
    if r0 is not None:
        uc.reg_write(UC_ARM_REG_R0, r0 & 0xFFFFFFFF)
    if d0 is not None:
        uc.reg_write(UC_ARM_REG_D0, d0 & 0xFFFFFFFFFFFFFFFF)
    if d1 is not None:
        uc.reg_write(UC_ARM_REG_D1, d1 & 0xFFFFFFFFFFFFFFFF)
    if s0 is not None:
        uc.reg_write(UC_ARM_REG_S0, s0 & 0xFFFFFFFF)
    if s1 is not None:
        uc.reg_write(UC_ARM_REG_S1, s1 & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_LR, 0x38000 | 1)
    uc.emu_start(addr | 1, 0x38000, count=400)
    return uc


# f32 bit patterns exercising sign/NaN-payload/subnormal/inf edges. A select
# must reproduce the picked operand EXACTLY, so NaN payloads are fair game.
F32_EDGES = [
    0x00000000,  # +0.0
    0x80000000,  # -0.0
    0x3FC00000,  # 1.5
    0xBFC00000,  # -1.5
    0x7F800000,  # +inf
    0xFF800000,  # -inf
    0x7FC00001,  # +NaN with payload
    0xFFC00000,  # -NaN
    0x00000001,  # +subnormal tiny
    0x7F7FFFFF,  # +FLT_MAX
]

# Direct-f32-param values: only patterns that round-trip double<->float32
# exactly through the Python/wasmtime double boundary (no NaN payloads here;
# sel32b covers those via the i32-bits path).
F32_VALS = [0.0, -0.0, 1.5, -1.5, float("inf"), float("-inf"), 123.0, 0.25]

F64_VALS = [0.0, -0.0, 1.5, -1.5, float("inf"), float("-inf"), 1e300,
            2.2250738585072014e-308]

CONDS = [0, 1, 2, 0x80000000]


def run_seli64(text, base, addr, cond, a=0x2222222211111111, b=0x4444444433333333):
    """i64 select: a in r0:r1, b in r2:r3, cond on the caller stack (AAPCS
    5th argument word). Returns the r1:r0 result as one 64-bit value."""
    from unicorn.arm_const import UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3
    uc = new_uc(text, base)
    uc.reg_write(UC_ARM_REG_SP, 0x38000 - 8)
    uc.mem_write(0x38000 - 8, struct.pack("<I", cond & 0xFFFFFFFF))
    uc.reg_write(UC_ARM_REG_R0, a & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_R1, (a >> 32) & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_R2, b & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_R3, (b >> 32) & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_LR, 0x38000 | 1)
    uc.emu_start(addr | 1, 0x38000, count=400)
    from unicorn.arm_const import UC_ARM_REG_R1 as _R1
    return (uc.reg_read(_R1) << 32) | uc.reg_read(UC_ARM_REG_R0)


def main():
    elf = "/tmp/float_select_return_782_m7dp.elf"

    ok, log = compile_elf(elf, "cortex-m7dp")
    if not ok:
        print("RED: `synth compile -t cortex-m7dp` REJECTED the #782 fixture.")
        print(log.strip()[:900])
        sys.exit(1)

    text, base, syms = load(elf)
    store = wasmtime.Store(wasmtime.Engine())
    inst = wasmtime.Instance(
        store, wasmtime.Module(store.engine, WAT.read_bytes()), [])
    exp = inst.exports(store)

    fails = 0
    checked = 0

    def fail(msg):
        nonlocal fails
        fails += 1
        print("  MISMATCH " + msg)

    def need(name):
        if name not in syms:
            fail(f"symbol '{name}' MISSING — function was skipped, not lowered")
            return False
        return True

    def to_i32(v):
        return v - (1 << 32) if v >= 1 << 31 else v

    # ---- sel32: f32 params in S0/S1, cond in R0, result S0. STRICT bits. ----
    if need("sel32"):
        for a in F32_VALS:
            for b in F32_VALS[::-1]:
                for c in CONDS:
                    uc = run(text, base, syms["sel32"],
                             s0=f32_bits(a), s1=f32_bits(b), r0=c)
                    got = uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF
                    want = f32_bits(exp["sel32"](store, a, b, to_i32(c)))
                    checked += 1
                    if got != want:
                        fail(f"sel32({a}, {b}, {c:#x}) -> 0x{got:08x} != "
                             f"wasmtime 0x{want:08x}")
        print(f"[sel32] {len(F32_VALS)**2 * len(CONDS)} cases bit-exact OK"
              if fails == 0 else "[sel32] FAILURES above")

    # ---- sel32b: bit patterns through reinterpret — NaN payloads STRICT. ----
    pre = fails
    if need("sel32b"):
        from unicorn.arm_const import UC_ARM_REG_R1, UC_ARM_REG_R2
        for a in F32_EDGES:
            for b in F32_EDGES[::-1]:
                for c in (0, 1):
                    uc = new_uc(text, base)
                    uc.reg_write(UC_ARM_REG_R0, a)
                    uc.reg_write(UC_ARM_REG_R1, b)
                    uc.reg_write(UC_ARM_REG_R2, c)
                    uc.reg_write(UC_ARM_REG_LR, 0x38000 | 1)
                    uc.emu_start(syms["sel32b"] | 1, 0x38000, count=400)
                    got = uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
                    want = exp["sel32b"](store, to_i32(a), to_i32(b), c) \
                        & 0xFFFFFFFF
                    checked += 1
                    if got != want:
                        fail(f"sel32b(0x{a:08x}, 0x{b:08x}, {c}) -> "
                             f"0x{got:08x} != wasmtime 0x{want:08x}")
        if fails == pre:
            print(f"[sel32b] {len(F32_EDGES)**2 * 2} NaN-payload-strict cases OK")

    # ---- clamp32: run-stabilization's clamp shape. ----
    pre = fails
    if need("clamp32"):
        for a in F32_VALS + [0.05, 0.1, 0.2]:
            uc = run(text, base, syms["clamp32"], s0=f32_bits(a))
            got = uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF
            want = f32_bits(exp["clamp32"](store, a))
            checked += 1
            if got != want:
                fail(f"clamp32({a}) -> 0x{got:08x} != wasmtime 0x{want:08x}")
        if fails == pre:
            print(f"[clamp32] {len(F32_VALS) + 3} cases bit-exact OK")

    # ---- sel64: f64 params in D0/D1, cond R0, result D0. STRICT bits. ----
    pre = fails
    if need("sel64"):
        for a in F64_VALS:
            for b in F64_VALS[::-1]:
                for c in (0, 1, 2):
                    uc = run(text, base, syms["sel64"],
                             d0=f64_bits(a), d1=f64_bits(b), r0=c)
                    got = uc.reg_read(UC_ARM_REG_D0) & 0xFFFFFFFFFFFFFFFF
                    want = f64_bits(exp["sel64"](store, a, b, c))
                    checked += 1
                    if got != want:
                        fail(f"sel64({a}, {b}, {c}) -> 0x{got:016x} != "
                             f"wasmtime 0x{want:016x}")
        if fails == pre:
            print(f"[sel64] {len(F64_VALS)**2 * 3} cases bit-exact OK")

    # ---- ret32/ret64: explicit float return (NaN-lenient — contains fadd). --
    pre = fails
    if need("ret32"):
        for a in F32_VALS + [float("nan")]:
            for c in (0, 1):
                uc = run(text, base, syms["ret32"], s0=f32_bits(a), r0=c)
                got = uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF
                want = f32_bits(exp["ret32"](store, a, c))
                checked += 1
                if not f32_bits_eq_lenient(got, want):
                    fail(f"ret32({a}, {c}) -> 0x{got:08x} != "
                         f"wasmtime 0x{want:08x}")
        if fails == pre:
            print(f"[ret32] {(len(F32_VALS) + 1) * 2} cases OK")

    pre = fails
    if need("ret64"):
        for a in F64_VALS + [float("nan")]:
            for c in (0, 1):
                uc = run(text, base, syms["ret64"], d0=f64_bits(a), r0=c)
                got = uc.reg_read(UC_ARM_REG_D0) & 0xFFFFFFFFFFFFFFFF
                want = f64_bits(exp["ret64"](store, a, c))
                checked += 1
                if not f64_bits_eq_lenient(got, want):
                    fail(f"ret64({a}, {c}) -> 0x{got:016x} != "
                         f"wasmtime 0x{want:016x}")
        if fails == pre:
            print(f"[ret64] {(len(F64_VALS) + 1) * 2} cases OK")

    # ---- seli64 on m7dp: BOTH halves, both cond outcomes. STRICT. ----
    pre = fails
    if need("seli64"):
        for c in (0, 1, 7, 0x80000000):
            got = run_seli64(text, base, syms["seli64"], c)
            want = exp["seli64"](store, 0x2222222211111111,
                                 0x4444444433333333, to_i32(c)) \
                & 0xFFFFFFFFFFFFFFFF
            checked += 1
            if got != want:
                fail(f"seli64(cond={c:#x}) -> 0x{got:016x} != "
                     f"wasmtime 0x{want:016x} (hi-half drop?)")
        if fails == pre:
            print("[seli64/m7dp] both halves correct for all conds OK")

    # ---- m4f (single-precision): f32 fns compile, f64 fns honest-skip. ----
    elf_m4 = "/tmp/float_select_return_782_m4f.elf"
    ok_m4, _ = compile_elf(elf_m4, "cortex-m4f")
    if not ok_m4:
        fail("cortex-m4f compile failed outright — f32 fns must still lower")
    else:
        _, _, syms_m4 = load(elf_m4)
        for name in ("sel32", "sel32b", "clamp32", "ret32", "seli64"):
            if name not in syms_m4:
                fail(f"'{name}' missing on cortex-m4f — f32 select/return "
                     f"must lower on a single-precision FPU")
        for name in ("sel64", "ret64"):
            if name in syms_m4:
                fail(f"'{name}' EMITTED on cortex-m4f — f64 must honest-skip "
                     f"on a single-precision FPU, never silently lower")
        print("[m4f] f32 fns lower, f64 fns honest-skip OK")

    # ---- m3 (no FPU): f32-arithmetic fns honest-skip; the pure value-pick
    # fns lower SOFT-float; seli64 executes with both halves correct (the
    # pre-fix silent hi-half miscompile was live on every target). ----
    elf_m3 = "/tmp/float_select_return_782_m3.elf"
    ok_m3, _ = compile_elf(elf_m3, "cortex-m3")
    if not ok_m3:
        fail("cortex-m3 compile failed outright — integer/soft-float value-"
             "pick fns must still lower")
    else:
        text3, base3, syms_m3 = load(elf_m3)
        for name in ("sel32b", "clamp32", "ret32", "ret64"):
            if name in syms_m3:
                fail(f"'{name}' EMITTED on cortex-m3 — f32/f64 arithmetic "
                     f"must honest-skip on a no-FPU target")
        pre = fails
        if "seli64" not in syms_m3:
            fail("'seli64' missing on cortex-m3")
        else:
            for c in (0, 1, 7):
                got = run_seli64(text3, base3, syms_m3["seli64"], c)
                want = exp["seli64"](store, 0x2222222211111111,
                                     0x4444444433333333, c) \
                    & 0xFFFFFFFFFFFFFFFF
                checked += 1
                if got != want:
                    fail(f"seli64/m3(cond={c}) -> 0x{got:016x} != "
                         f"wasmtime 0x{want:016x} (hi-half drop?)")
        if fails == pre:
            print("[m3] f32 fns honest-skip; seli64 soft-float both halves OK")

    print(f"\n{checked} differential cases, {fails} failures")
    if fails:
        sys.exit(1)
    print("GREEN: float select + explicit float return execute bit-identically "
          "to wasmtime on cortex-m7dp; m3/m4f capability gates honest (#782b)")


if __name__ == "__main__":
    main()
