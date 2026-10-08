#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 40
"""#1069 (RQ-60-VFPPRESSURE increment 2) — EXECUTION-validate frame-homed
VFP locals on cortex-m7dp under falcon's exact flags
(`-t cortex-m7dp --relocatable`).

jess's discriminating measurement (fixture credit: jess): 60 simultaneously-
live f32 on the OPERAND STACK compile (#881 rescues them); 14 in HOMED LOCALS
do not — a home S-register is pinned for the function's extent and the #881
victim search skips homes. The fix frame-homes overflow locals from birth
(rung-only). This harness proves the emitted code is CORRECT, not merely
present:

  1. COMPILE — every export reaches an `nm -> T` symbol on
     `-t cortex-m7dp --relocatable` (live13 is the negative control);
  2. EXECUTE bit-identically to wasmtime (NaN==NaN per WASM Core §4.3.3)
     across representative values — a spill that reloads the wrong slot
     produces a plausible WRONG float, and every local's round-tripped value
     feeds the final product, so any slot mixup flips result bits:
       * live13 — negative control (base path, no rung);
       * live14/live16 — phase-1 S-file wall (attitude#tick / ekf#estimate);
       * live24 — grown-pool composition (>8 permanent slots);
       * live8d — the f64/D-file twin.

Run (needs wasmtime + unicorn + pyelftools + arm-none-eabi-ld):
  SYNTH=/path/to/synth python scripts/repro/vfp_local_pressure_1069_differential.py
"""

import os
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc
from unicorn.arm_const import (
    UC_ARM_REG_D0,
    UC_ARM_REG_LR,
    UC_ARM_REG_S0,
    UC_ARM_REG_SP,
)

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn naming
    UC_ARM_REG_C1_C0_2 = None
    UC_ARM_REG_FPEXC = None

WAT = Path(__file__).with_name("vfp_local_pressure_1069.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

F32_EXPORTS = ["live13", "live14", "live16", "live24"]
F64_EXPORTS = ["live8d"]
EXPORTS = F32_EXPORTS + F64_EXPORTS


def fail(msg):
    print(f"FAIL: {msg}")
    sys.exit(1)


def compile_relocatable(tmp):
    obj = str(Path(tmp) / "vfp1069.o")
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", obj,
         "-t", "cortex-m7dp", "--relocatable"],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        fail(f"compile failed:\n{r.stderr}\n{r.stdout}")
    combined = r.stderr + r.stdout
    if "skipping function" in combined:
        fail(f"a function was skipped (GI-FPU-002 regression):\n{combined}")
    return obj


def link(tmp, obj):
    ld = shutil.which("arm-none-eabi-ld")
    if ld is None:
        fail("arm-none-eabi-ld not found")
    out = str(Path(tmp) / "vfp1069.elf")
    r = subprocess.run(
        [ld, "-e", "live13", "-Ttext=0x0", obj, "-o", out],
        capture_output=True, text=True,
    )
    if r.returncode != 0 or r.stderr.strip():
        fail(f"link failed / diagnostics:\n{r.stderr}")
    return out


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


def f64_bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def is_nan32(b):
    b &= 0xFFFFFFFF
    return (b & 0x7F800000) == 0x7F800000 and (b & 0x007FFFFF) != 0


def is_nan64(b):
    b &= (1 << 64) - 1
    return (b & 0x7FF0000000000000) == 0x7FF0000000000000 and (
        b & 0x000FFFFFFFFFFFFF) != 0


def f32_bits_eq(got, want):
    if is_nan32(got) and is_nan32(want):
        return True  # WASM Core §4.3.3: NaN payload non-deterministic
    return (got & 0xFFFFFFFF) == (want & 0xFFFFFFFF)


def f64_bits_eq(got, want):
    if is_nan64(got) and is_nan64(want):
        return True
    return (got & ((1 << 64) - 1)) == (want & ((1 << 64) - 1))


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
    uc.reg_write(UC_ARM_REG_SP, 0x38000)
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    return uc


def run_f32(text, base, addr, s0):
    uc = new_uc(text, base)
    uc.reg_write(UC_ARM_REG_S0, s0 & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_LR, 0x38000 | 1)
    uc.emu_start(addr | 1, 0x38000, count=5000)
    return uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF


def run_f64(text, base, addr, d0):
    uc = new_uc(text, base)
    uc.reg_write(UC_ARM_REG_D0, d0 & ((1 << 64) - 1))
    uc.reg_write(UC_ARM_REG_LR, 0x38000 | 1)
    uc.emu_start(addr | 1, 0x38000, count=5000)
    return uc.reg_read(UC_ARM_REG_D0) & ((1 << 64) - 1)


# Products of 14+ scaled copies overflow to inf fast for |a| >= ~1; keep a
# spread that exercises normals, denormal underflow, zeros, infinities and
# NaN through the spilled paths (each local's round-tripped value feeds the
# product, so a wrong-slot reload flips result bits).
VALS = [0.0, -0.0, 1.0, -1.0, 0.5, -0.25, 1.5, 0.001, -3.14159265,
        1e-30, -1e30, float("inf"), float("-inf"), float("nan")]

# RQ-81-WIDEFILE4 (#1439): BOTH SIGNS ARE LOAD-BEARING, and until v0.81 nothing
# said so. The wide-file sign error (#1426) shows as `got ^ want == 0x8000_0000`
# with magnitudes BIT-IDENTICAL, so exactly one factor's sign is wrong and only
# an `abs` or a `neg` can do that. For a NEGATIVE input the two are
# indistinguishable -- abs(-x) and neg(-x) both give +x -- so the positive rows
# are the discriminator: a `neg` would corrupt them too, an `abs` leaves them
# alone. v0.78 recorded the failing set as exactly the six NEGATIVE values and
# no positive one, which identifies the operation as an ABS. That conclusion
# evaporates if someone trims this list to "the interesting cases", so the span
# is asserted rather than hoped for.
import struct as _struct  # noqa: E402  (bit-exact row pinning, below)

_POS = [v for v in VALS if v == v and v > 0 or (v == 0 and str(v)[0] != "-")]
_NEG = [v for v in VALS if v == v and (v < 0 or str(v)[0] == "-")]
assert len(_POS) >= 4 and len(_NEG) >= 4, (
    f"VALS must span BOTH signs with at least 4 each -- it is the abs-vs-neg "
    f"discriminator for #1439, not decoration. Got {len(_POS)} positive and "
    f"{len(_NEG)} negative")
# AND THE ROWS, NOT ONLY THE COUNTS. (v0.81 round-1 cold review, finding 11.)
# The count assertion above says the comment's reason more narrowly than the
# comment claims: replacing every FINITE negative with an infinity or a denormal
# keeps 4-and-4 and still passes, while deleting exactly the rows v0.78's failing
# set is made of. Measured by the reviewer:
# `[0.0, -0.0, inf, -inf, 1e-30, -1e-30, 1e30, -1e30]` passed.
#
# v0.78 recorded the failing set as EXACTLY these six, so these six are the
# evidence and are pinned by VALUE. A future lane may add rows; it may not remove
# one of these without re-deriving the abs-vs-neg conclusion that rests on them.
_FAILING_SET_1439 = (-0.0, -1.0, -0.25, -3.14159265, -1e30, float("-inf"))
# COMPARE BY BIT PATTERN, not by `==`. (v0.81 round-2 cold review, finding 4.)
# The first version of this guard used `v not in VALS`, and `-0.0 == 0.0` is True
# in IEEE-754 — so membership was satisfied by `+0.0` and deleting `-0.0` left
# BOTH assertions passing. `-0.0` is the SIGN-BIT row: the one value in the set
# whose entire content is the sign, on a defect that is a sign error. The row most
# central to the conclusion was the only one not actually pinned.
_bits = {_struct.pack("<f", _v) for _v in VALS}
_missing = [v for v in _FAILING_SET_1439 if _struct.pack("<f", v) not in _bits]
assert not _missing, (
    f"VALS is missing {_missing} -- v0.78's recorded failing set for #1439 is "
    f"exactly {_FAILING_SET_1439}, and the abs-vs-neg conclusion is derived from "
    f"those rows failing while every POSITIVE row passed. Removing one deletes "
    f"the evidence rather than the test")

# RQ-82-PINBYVALUE (#1439): AND THE NON-FINITE ROWS, WHICH NOTHING PINNED AT ALL.
# The two guards above cover the sign span and v0.78's failing set; MEASURED, both
# stayed green when `float("nan")` was deleted from VALS. That row is in the
# fixture for a stated reason -- the header comment above says NaN exercises the
# spilled paths, because each local's round-tripped value feeds the product, so a
# wrong-slot reload flips result bits -- and it was protected by nothing.
#
# It is the SAME FAMILY as the `-0.0` escape and the OPPOSITE failure mode.
# `-0.0` was pinned VACUOUSLY TRUE, because `-0.0 == 0.0`, so membership was
# satisfied by the wrong row. NaN cannot be pinned by membership AT ALL, because
# `nan != nan` makes `nan in [nan]` False -- a membership guard over it would be
# vacuously FALSE and would red on a correct fixture. `struct.pack` settles both:
# it compares the BITS, where `-0.0` and `+0.0` differ and `nan` equals itself.
# The infinities ride along; they are cheap and they are the other rows whose
# content is not a magnitude.
#
# Deliberately a SEPARATE set from _FAILING_SET_1439, which means exactly "the six
# values v0.78 recorded as failing". Adding rows to that tuple would falsify its
# own name and the conclusion drawn from it.
# AND THE POSITIVE ROWS, FOR THE SAME REASON ONE TIER OVER. The comment above
# states the conclusion's shape: "the positive rows are the discriminator -- a
# `neg` would corrupt them too, an `abs` leaves them alone". So the conclusion
# rests on BOTH halves: the six negatives failing AND no positive one failing.
# The negative half is pinned by bits; the positive half was pinned only by
# `len(_POS) >= 4` against SEVEN present, so MEASURED, any single positive row
# could be deleted in silence -- deleting `0.0`, `1.0`, `0.5`, `1.5`, `0.001` or
# `1e-30` reddened nothing. Half an argument pinned is the asymmetry this lane
# exists to remove, not a smaller version of it.
_POSITIVE_SPAN_1439 = (0.0, 1.0, 0.5, 1.5, 0.001, 1e-30)
_NONFINITE_1069 = (float("inf"), float("-inf"), float("nan"))
_missing_nonfinite = [v for v in _NONFINITE_1069
                      if _struct.pack("<f", v) not in _bits]
assert not _missing_nonfinite, (
    f"VALS is missing {_missing_nonfinite} -- the non-finite rows exercise the "
    f"spilled reload paths this differential exists to check, and a membership "
    f"guard could never have pinned the NaN one. Re-derive the coverage claim "
    f"before removing a row rather than trimming to 'the interesting cases'")
_missing_positive = [v for v in _POSITIVE_SPAN_1439
                     if _struct.pack("<f", v) not in _bits]
assert not _missing_positive, (
    f"VALS is missing {_missing_positive} -- the POSITIVE rows are the "
    f"abs-vs-neg discriminator for #1439 (an `abs` leaves them alone, a `neg` "
    f"would corrupt them), so they are evidence exactly as the negative rows "
    f"are. `len(_POS) >= 4` does not pin them: seven are present, so the floor "
    f"permits deleting three in silence")


def main():
    tmp = tempfile.mkdtemp(prefix="vfp1069_")
    obj = compile_relocatable(tmp)

    # Gate 1: every export is an emitted T symbol (see the #850 note in
    # vfp_spill_881_differential.py — pyelftools, never host nm).
    with open(obj, "rb") as fh:
        ef = ELFFile(fh)
        symtab = next((s for s in ef.iter_sections()
                       if s["sh_type"] == "SHT_SYMTAB"), None)
        if symtab is None:
            fail("relocatable object has no SHT_SYMTAB section")
        tsyms = set()
        for sym in symtab.iter_symbols():
            if not sym.name or sym["st_info"]["bind"] != "STB_GLOBAL":
                continue
            shndx = sym["st_shndx"]
            if shndx in ("SHN_UNDEF", "SHN_ABS", "SHN_COMMON"):
                continue
            if ef.get_section(shndx)["sh_flags"] & 0x4:  # SHF_EXECINSTR
                tsyms.add(sym.name)
    missing = [e for e in EXPORTS if e not in tsyms]
    if missing:
        fail(f"exports missing from nm -> T: {missing}")
    print(f"PASS: all {len(EXPORTS)} exports emitted (nm -> T) under "
          "-t cortex-m7dp --relocatable")

    # Gate 2: execution, bit-exact vs wasmtime.
    elf = link(tmp, obj)
    text, base, syms = load(elf)
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    store = wasmtime.Store(eng)
    inst = wasmtime.Instance(store, mod, [])
    exp = inst.exports(store)

    checked = 0
    for name in F32_EXPORTS:
        for a in VALS:
            want = f32_bits(exp[name](store, a))
            got = run_f32(text, base, syms[name], f32_bits(a))
            if not f32_bits_eq(got, want):
                fail(f"{name}({a}): got {got:#010x}, want {want:#010x}")
            checked += 1
    for name in F64_EXPORTS:
        for a in VALS:
            want = f64_bits(exp[name](store, a))
            got = run_f64(text, base, syms[name], f64_bits(a))
            if not f64_bits_eq(got, want):
                fail(f"{name}({a}): got {got:#018x}, want {want:#018x}")
            checked += 1

    print(f"PASS: {checked} emulations bit-identical to wasmtime "
          "(frame-homed VFP locals round-trip bit-exactly)")
    print("RESULT: PASS")


if __name__ == "__main__":
    main()
