#!/usr/bin/env python3
"""#881 (GI-FPU-002 + RA tail / VCR-RA-004) — EXECUTION-validate VFP
register-file spilling on cortex-m7dp under falcon's exact flags
(`-t cortex-m7dp --relocatable`).

The two exhaustion classes that block the falcon v1.128 cascade entry points
(`position/attitude#tick` = phase-1 S0..S15, `rate#tick`/`ekf#estimate` =
phase-2 D0..D7, plus the v0.52 #869 D-pressure-in-f32-only-code shape) are
reproduced by `vfp_spill_881.wat` and must now:

  1. COMPILE — every export reaches an `nm -> T` symbol (no GI-FPU-002 skip);
  2. EXECUTE bit-identically to wasmtime through the SPILLED paths:
       * deep_s      — 20 simultaneously-live f32 (S-file spill/reload)
       * deep_d      — 10 simultaneously-live f64 (D-file spill/reload)
       * deep_mix    — i64->f32 converts under a live 14-deep f32 stack
       * spill_call  — spilled f32 frame-resident ACROSS a bl + helper call
       * deep_local  — pinned f32 local homes are never victims
       * deep_select — the falcon clamp idiom (select) under pressure
       * deep_sd_mix — S/D aliasing churn (aligned-pair search while
                       fragmented by live f32s)

A function that emits but computes wrong is worse than one that declines:
results are compared BIT-EXACT (NaN==NaN per WASM Core §4.3.3).

The internal `bl` (spill_call -> helper) is resolved by linking the ET_REL
object with arm-none-eabi-ld; ANY unresolved/unexpected relocation hard-fails
the harness (the #757/#743 inverse-vacuity lesson: never skip-on-assumption).

Run (needs wasmtime + unicorn + pyelftools + arm-none-eabi-ld):
  SYNTH=/path/to/synth python scripts/repro/vfp_spill_881_differential.py
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
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_S0,
    UC_ARM_REG_S1,
    UC_ARM_REG_SP,
)

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn naming
    UC_ARM_REG_C1_C0_2 = None
    UC_ARM_REG_FPEXC = None

WAT = Path(__file__).with_name("vfp_spill_881.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

EXPORTS = [
    "deep_s", "deep_d", "deep_mix", "spill_call",
    "deep_local", "deep_select", "deep_sd_mix",
]


def fail(msg):
    print(f"FAIL: {msg}")
    sys.exit(1)


def compile_relocatable(tmp):
    obj = str(Path(tmp) / "vfp881.o")
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
    """Resolve the internal bl via a real link. Hard-fail on ANY ld
    diagnostic — an unresolved reloc silently skipped is a vacuous gate."""
    ld = shutil.which("arm-none-eabi-ld")
    if ld is None:
        fail("arm-none-eabi-ld not found (required to resolve the internal bl)")
    out = str(Path(tmp) / "vfp881.elf")
    r = subprocess.run(
        [ld, "-e", "deep_s", "-Ttext=0x0", obj, "-o", out],
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


def bits_f32(b):
    return struct.unpack("<f", struct.pack("<I", b & 0xFFFFFFFF))[0]


def is_nan32(bits):
    b = bits & 0xFFFFFFFF
    return (b & 0x7F800000) == 0x7F800000 and (b & 0x007FFFFF) != 0


def f32_bits_eq(got, want):
    if is_nan32(got) and is_nan32(want):
        return True  # WASM Core §4.3.3: NaN sign/payload non-deterministic
    return (got & 0xFFFFFFFF) == (want & 0xFFFFFFFF)


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
    # Enable the FPU (off at reset): CPACR CP10/CP11 + FPEXC.EN.
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    return uc


def run_f32(text, base, addr, s0=None, s1=None, r0=None, r1=None, r2=None,
            r3=None):
    """Execute a function returning f32 in S0 (AAPCS-VFP hard-float)."""
    uc = new_uc(text, base)
    for reg, val in ((UC_ARM_REG_S0, s0), (UC_ARM_REG_S1, s1)):
        if val is not None:
            uc.reg_write(reg, val & 0xFFFFFFFF)
    for reg, val in ((UC_ARM_REG_R0, r0), (UC_ARM_REG_R1, r1),
                     (UC_ARM_REG_R2, r2), (UC_ARM_REG_R3, r3)):
        if val is not None:
            uc.reg_write(reg, val & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_LR, 0x38000 | 1)
    # Deep spilled expressions execute a few hundred instructions; 5000 is a
    # loud upper bound (emu_start raises on runaway, never silent-passes).
    uc.emu_start(addr | 1, 0x38000, count=5000)
    return uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF


def wasm_instance():
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    store = wasmtime.Store(eng)
    inst = wasmtime.Instance(store, mod, [])
    return store, inst


F32_VALS = [0.0, -0.0, 1.0, -1.5, 3.14159265, 1e30, -1e-30, 65535.875,
            float("inf"), float("-inf"), float("nan"), 1.1754944e-38]
I64_VALS = [0, 1, -1, 0x7FFFFFFFFFFFFFFF, -0x8000000000000000,
            0xDEADBEEFCAFEBABE - (1 << 64), 1 << 32, (1 << 53) + 1, 12345]


def main():
    tmp = tempfile.mkdtemp(prefix="vfp881_")
    obj = compile_relocatable(tmp)

    # Gate 1: falcon flags — every export is an emitted T symbol.
    nm = subprocess.run(["arm-none-eabi-nm", obj], capture_output=True,
                        text=True)
    if nm.returncode != 0:
        fail("nm failed on the relocatable object")
    tsyms = {ln.split()[-1] for ln in nm.stdout.splitlines()
             if " T " in ln}
    missing = [e for e in EXPORTS if e not in tsyms]
    if missing:
        fail(f"exports missing from nm -> T: {missing}")
    print(f"PASS: all {len(EXPORTS)} exports emitted (nm -> T) under "
          "-t cortex-m7dp --relocatable")

    # Gate 2: execution, bit-exact vs wasmtime, on the LINKED image (the bl
    # inside spill_call is resolved by a real link, never skipped).
    elf = link(tmp, obj)
    text, base, syms = load(elf)
    store, inst = wasm_instance()
    exp = inst.exports(store)

    checked = 0
    # deep_s(a, b): S-file spilling.
    for a in F32_VALS:
        for b in (0.5, -2.25, 1e20):
            want = f32_bits(exp["deep_s"](store, a, b))
            got = run_f32(text, base, syms["deep_s"],
                          s0=f32_bits(a), s1=f32_bits(b))
            if not f32_bits_eq(got, want):
                fail(f"deep_s({a}, {b}): got {got:#010x} "
                     f"({bits_f32(got)}), want {want:#010x}")
            checked += 1

    # deep_d(): D-file spilling (constant fold — one row, but the whole
    # spilled path executes).
    want = f32_bits(exp["deep_d"](store))
    got = run_f32(text, base, syms["deep_d"])
    if not f32_bits_eq(got, want):
        fail(f"deep_d(): got {got:#010x}, want {want:#010x}")
    checked += 1

    # deep_mix(x, y): #869 i64->f32 under f32 pressure. AAPCS: x in r0:r1,
    # y in r2:r3 (lo:hi little-endian pairs).
    for x in I64_VALS:
        for y in (0, -1, 1 << 40):
            want = f32_bits(exp["deep_mix"](store, x, y))
            xu, yu = x & (2**64 - 1), y & (2**64 - 1)
            got = run_f32(text, base, syms["deep_mix"],
                          r0=xu & 0xFFFFFFFF, r1=xu >> 32,
                          r2=yu & 0xFFFFFFFF, r3=yu >> 32)
            if not f32_bits_eq(got, want):
                fail(f"deep_mix({x}, {y}): got {got:#010x}, want {want:#010x}")
            checked += 1

    # spill_call(a): spilled f32 across a bl.
    for a in F32_VALS:
        want = f32_bits(exp["spill_call"](store, a))
        got = run_f32(text, base, syms["spill_call"], s0=f32_bits(a))
        if not f32_bits_eq(got, want):
            fail(f"spill_call({a}): got {got:#010x}, want {want:#010x}")
        checked += 1

    # deep_local(a): pinned homes + spilling.
    for a in F32_VALS:
        want = f32_bits(exp["deep_local"](store, a))
        got = run_f32(text, base, syms["deep_local"], s0=f32_bits(a))
        if not f32_bits_eq(got, want):
            fail(f"deep_local({a}): got {got:#010x}, want {want:#010x}")
        checked += 1

    # deep_select(a, c): clamp idiom under pressure — BOTH select arms.
    for a in (1.5, -7.25, float("nan")):
        for c in (0, 1, 0x80000000):
            want = f32_bits(exp["deep_select"](store, a, c))
            got = run_f32(text, base, syms["deep_select"],
                          s0=f32_bits(a), r0=c)
            if not f32_bits_eq(got, want):
                fail(f"deep_select({a}, {c:#x}): got {got:#010x}, "
                     f"want {want:#010x}")
            checked += 1

    # deep_sd_mix(a): S/D aliasing churn.
    for a in F32_VALS:
        want = f32_bits(exp["deep_sd_mix"](store, a))
        got = run_f32(text, base, syms["deep_sd_mix"], s0=f32_bits(a))
        if not f32_bits_eq(got, want):
            fail(f"deep_sd_mix({a}): got {got:#010x}, want {want:#010x}")
        checked += 1

    print(f"PASS: {checked} execution rows bit-identical to wasmtime "
          "(unicorn, cortex-m7dp, spilled VFP paths)")


if __name__ == "__main__":
    main()
