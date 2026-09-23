#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 84
"""RQ-71-VFPALIAS (#881/#1069) — EXECUTION-validate a REDEFINED frame-homed
VFP local on cortex-m7dp under falcon's exact flags (`-t cortex-m7dp
--relocatable`).

WHY THIS HARNESS EXISTS, and why compiling is not enough.

`check_vfp_slot_aliasing` policed every `[sp,#off]` VFP access, including the
PERMANENT home the #1069 rung gives an overflow f32/f64 local. Under that rung
`local.set` IS the local's def and stores straight to the home, so a legal wasm
redefinition writes the home a second time with a different value — which the
single-value-per-slot rule reported as `VfpSpillSlotAliased`, refusing the
compile as "a compiler bug". Measured before the fix: f32 refused from 14
homed locals, f64 from 8 — exactly the pressure the #1069 rung exists to serve.

The fix NARROWS that check to exclude declared frame homes. A narrowing turns a
LOUD refusal into silence, so "it compiles now" is evidence about the validator,
not about the code. This harness supplies the missing half: the emitted code is
CORRECT, bit-for-bit, on the very shape that used to be refused.

  Gate 1  every export reaches an `nm -> T` symbol (pyelftools, never host nm).
  Gate 2  POTENCY. `redef_none` is `redef_diff` minus the redefinition, so if
          the compiled code ever read the STALE home the two would agree. They
          must differ on every finite input — otherwise gate 3 is vacuous and
          could not distinguish a correct home read from a stale one.
  Gate 3  EXECUTION, bit-identical to wasmtime (NaN == NaN per WASM Core
          §4.3.3) across a value spread. Every local's round-tripped value
          feeds the final product, so any wrong-slot read flips result bits.

The `redef_same` legs ride along as the third arm of the fixture's control set:
a re-store of the PROVABLY IDENTICAL value, which the check excused all along
via `src_word` + `src_version` and still must.
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

WAT = Path(__file__).with_name("vfp_home_redef_881.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

F32_EXPORTS = ["redef_none", "redef_diff", "redef_same"]
F64_EXPORTS = ["redef_none_d", "redef_diff_d", "redef_same_d"]
EXPORTS = F32_EXPORTS + F64_EXPORTS

# The potency pairs: (redefined leg, same-leg-without-the-redefinition).
POTENCY = [("redef_diff", "redef_none"), ("redef_diff_d", "redef_none_d")]


def fail(msg):
    print(f"FAIL: {msg}")
    sys.exit(1)


def compile_relocatable(tmp):
    obj = str(Path(tmp) / "vfpredef.o")
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", obj, "-t", "cortex-m7dp", "--relocatable"],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        fail(f"compile failed:\n{r.stderr}\n{r.stdout}")
    combined = r.stderr + r.stdout
    if "skipping function" in combined:
        # This is the pre-fix behaviour: VfpSpillSlotAliased on the redefined
        # home. Name it, so a regression reads as itself and not as a mystery.
        fail(f"a function was skipped (RQ-71-VFPALIAS regression):\n{combined}")
    return obj


def link(tmp, obj):
    ld = shutil.which("arm-none-eabi-ld")
    if ld is None:
        fail("arm-none-eabi-ld not found")
    out = str(Path(tmp) / "vfpredef.elf")
    r = subprocess.run(
        [ld, "-e", "redef_none", "-Ttext=0x0", obj, "-o", out],
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
    return (b & 0x7F800000) == 0x7F800000 and (b & 0x007FFFFF) != 0


def is_nan64(b):
    return (b & 0x7FF0000000000000) == 0x7FF0000000000000 and (
        b & 0x000FFFFFFFFFFFFF
    ) != 0


def f32_bits_eq(got, want):
    # WASM Core §4.3.3: NaN payloads are not observable, so NaN == NaN.
    if is_nan32(got) and is_nan32(want):
        return True
    return got == want


def f64_bits_eq(got, want):
    if is_nan64(got) and is_nan64(want):
        return True
    return got == want


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


# Products of 8-24 scaled copies overflow to inf fast for |a| >= ~1; keep a
# spread that exercises normals, denormal underflow, zeros, infinities and NaN
# through the homed paths.
VALS = [0.0, -0.0, 1.0, -1.0, 0.5, -0.25, 1.5, 0.001, -3.14159265,
        1e-30, -1e30, float("inf"), float("-inf"), float("nan")]

# Gate 2 needs inputs whose products are FINITE and NON-ZERO at BOTH widths:
# inf/nan/0 make the redefined and stale answers agree for reasons that have
# nothing to do with which slot was read, and a 24-term product underflows to
# 0.0 well before the input does (0.001 does, which is how this list was
# chosen — the potency gate rejected it).
FINITE_VALS = [0.5, -0.25, 0.1, 2.0]


def main():
    tmp = tempfile.mkdtemp(prefix="vfpredef_")
    obj = compile_relocatable(tmp)

    # Gate 1: every export is an emitted T symbol (#850: pyelftools, never nm).
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

    elf = link(tmp, obj)
    text, base, syms = load(elf)
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    store = wasmtime.Store(eng)
    inst = wasmtime.Instance(store, mod, [])
    exp = inst.exports(store)

    # Gate 2: POTENCY. A stale home read would make the redefined leg return
    # its non-redefined twin's answer, so gate 3 can only be meaningful if the
    # two genuinely differ.
    for redefined, stale in POTENCY:
        for a in FINITE_VALS:
            lo, hi = exp[redefined](store, a), exp[stale](store, a)
            if lo == hi:
                fail(f"potency: {redefined}({a}) == {stale}({a}) == {lo} — "
                     "reading the STALE home would be unobservable here, so "
                     "the execution gate below cannot discriminate")
    print(f"PASS: potency — {len(POTENCY) * len(FINITE_VALS)} pairs where a "
          "stale frame-home read is observable")

    # Gate 3: execution, bit-exact vs wasmtime.
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
          "(a REDEFINED frame-homed VFP local round-trips bit-exactly)")
    print("RESULT: PASS")


if __name__ == "__main__":
    main()
