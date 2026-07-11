#!/usr/bin/env python3
"""GI-FPU-002 (#619/#369) — EXECUTION-validate scalar f32 hard-float codegen.

synth has a working VFP encoder + selector VFP lowering, but the decoder dropped
every scalar float op, so `synth compile f32.wat -t cortex-m4f` HONESTLY REJECTED
f32 on every CLI path. Phase 1 wires decode -> the direct selector's VFP arms
(add/sub/mul/div, the six comparisons, i32.trunc_f32_s/u, f32.convert_i32_s/u,
f32.const, f32-param local.get) with AAPCS-VFP homing (args in S0..S15, result in
S0), gated on FPU presence (m0/m3 keep the honest reject).

This harness compiles the fixture for cortex-m4f, reads each function's address
from the ELF SYMTAB (#489 — never `synth disasm` text), runs it under unicorn
(UC_ARCH_ARM / Thumb) with the FPU ENABLED (CPACR CP10/CP11 + FPEXC.EN, since the
M4F FPU is off at reset), passing the f32 args in S0/S1 per hard-float, and
asserts the result is BIT-EXACT (`to_bits`, so signed-zero / NaN can't slip) to
wasmtime ground truth on FPU-boundary values.

RED / GREEN: on origin/main the compile step REJECTS (capability gap) -> this
script exits nonzero (RED, "compile rejected"). After phase 1 it compiles and
matches wasmtime -> exits 0 (GREEN). One harness, run against both trees.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=/path/to/synth python scripts/repro/f32_vfp_619_differential.py
Exits nonzero on any mismatch or on a compile rejection.
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
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_S0,
    UC_ARM_REG_S1,
    UC_ARM_REG_SP,
)

# Unicorn exposes CPACR as coprocessor reg C1_C0_2 and FPEXC for VFP enable.
try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # older unicorn naming
    UC_ARM_REG_C1_C0_2 = None
    UC_ARM_REG_FPEXC = None

WAT = Path(__file__).with_name("f32_vfp_619.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE_BASE = 0x1000
STACK_TOP = 0x40000
STACK_MEM = 0x30000

# FPU-boundary inputs: 0.0, 1.5, -2.25, a large magnitude, a denormal-ish tiny.
F32_PAIRS = [
    (0.0, 1.5),
    (1.5, 2.5),
    (-2.25, 4.0),
    (1.0e30, 3.0),
    (1.0e-40, 2.0),  # 1e-40 is subnormal in f32
    (-0.0, 0.0),
]
# i32 inputs for convert; f32 inputs for trunc (all in i32 range — an
# out-of-range trunc TRAPS in wasm, which is a control-flow property, not a
# value differential).
I32_INPUTS = [0, 1, -1, 7, -7, 2147483647, -2147483648, 100000]
TRUNC_INPUTS = [0.0, 1.9, -1.9, 2.5, -2.5, 123.75, -123.75, 2000000.5]

BINOP_F32 = ["fadd", "fsub", "fmul", "fdiv"]
CMP_F32 = ["flt", "fgt", "feq", "fne", "fle", "fge"]  # #712: all six, not just lt/gt
# The f32 comparisons compile to VCMP.F32 + VMRS APSR_nzcv, FPSCR + IT + MOV.
# HISTORY (#709): this harness ORIGINALLY skipped compare execution on the
# premise that "unicorn does not model the VMRS FPSCR->APSR transfer." That
# premise was FALSE — unicorn transfers the N/Z/C/V bits correctly — and the
# skip is exactly why a shipped compare bug went unnoticed: the encoder emitted
# a flag-setting `MOVS Rd,#0` AFTER the VMRS, clobbering the transferred flags,
# so every f32 comparison returned 0. The encoder now materializes the #0
# BEFORE the VCMP (byte reorder, sizes unchanged), and the compares are
# execution-differentiated here against wasmtime on FPU-boundary values.


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
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
    return data, base, syms


def f32_bits(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def bits_f32(b):
    return struct.unpack("<f", struct.pack("<I", b & 0xFFFFFFFF))[0]


def is_nan32(b):
    """True if the 32 bits are any IEEE-754 f32 NaN (exp all-ones, mantissa!=0)."""
    b &= 0xFFFFFFFF
    return (b & 0x7F800000) == 0x7F800000 and (b & 0x007FFFFF) != 0


def f32_bits_eq(got, want):
    """WASM leaves the sign+payload of a NaN result NON-DETERMINISTIC (§4.3.3
    NaN propagation) — a bit-exact compare of a NaN is over-specified and diverges
    by wasmtime version (e.g. f32.div(-0.0,0.0): ARM's DefaultNaN 0x7fc00000 vs
    wasmtime 0xffc00000, both valid qNaNs). So NaN==NaN regardless of bits; every
    non-NaN result stays bit-exact (signed zero / inf still can't slip)."""
    if is_nan32(got) and is_nan32(want):
        return True
    return (got & 0xFFFFFFFF) == (want & 0xFFFFFFFF)


def run_unicorn(text, text_base, addr, s0_bits=None, s1_bits=None, r0=None):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    map_base = text_base & ~0xFFF
    size = ((len(text) + (text_base - map_base)) + 0xFFF) & ~0xFFF
    uc.mem_map(map_base, max(size, 0x1000))
    uc.mem_write(text_base, text)
    uc.mem_map(STACK_MEM, 0x10000)
    uc.reg_write(UC_ARM_REG_SP, STACK_TOP)
    # Enable the FPU (M4F FPU is disabled at reset): CPACR CP10/CP11 + FPEXC.EN.
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    if s0_bits is not None:
        uc.reg_write(UC_ARM_REG_S0, s0_bits)
    if s1_bits is not None:
        uc.reg_write(UC_ARM_REG_S1, s1_bits)
    if r0 is not None:
        uc.reg_write(UC_ARM_REG_R0, r0 & 0xFFFFFFFF)
    ret = STACK_TOP | 1
    uc.reg_write(UC_ARM_REG_LR, ret)
    uc.emu_start(addr | 1, ret & ~1, count=200)
    return uc


def wasm_instance():
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    store = wasmtime.Store(eng)
    inst = wasmtime.Instance(store, mod, [])
    return store, inst


def main():
    elf = "/tmp/f32_vfp_619.elf"

    # Honest-reject check: f32 must be rejected on a no-FPU target (m3).
    ok_m3, _ = compile_elf("/tmp/f32_vfp_619_m3.elf", "cortex-m3")
    if ok_m3:
        sys.exit("FAIL: f32 must be REJECTED on cortex-m3 (no FPU), but compiled")

    ok, log = compile_elf(elf, "cortex-m4f")
    if not ok:
        print("RED: `synth compile -t cortex-m4f` REJECTED f32 (capability gap).")
        print(log.strip()[:400])
        sys.exit(1)

    text, base, syms = load(elf)
    store, inst = wasm_instance()

    fails = 0
    checked = 0

    def bit_result_f32(fn, uc):
        return uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF

    for fn in BINOP_F32:
        wf = inst.exports(store)[fn]
        for a, b in F32_PAIRS:
            uc = run_unicorn(text, base, syms[fn], s0_bits=f32_bits(a), s1_bits=f32_bits(b))
            got = uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF
            want = f32_bits(wf(store, a, b))
            checked += 1
            if not f32_bits_eq(got, want):
                fails += 1
                print(f"MISMATCH {fn}({a},{b}): synth 0x{got:08x} ({bits_f32(got)}) "
                      f"!= wasmtime 0x{want:08x} ({bits_f32(want)})")

    # #709: the f32 comparisons now execution-differentiate (the flag-clobber
    # bug is fixed). Result is an i32 (0/1) in R0.
    for fn in CMP_F32:
        wf = inst.exports(store)[fn]
        for a, b in F32_PAIRS:
            uc = run_unicorn(text, base, syms[fn], s0_bits=f32_bits(a), s1_bits=f32_bits(b))
            got = uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
            want = wf(store, a, b) & 0xFFFFFFFF
            checked += 1
            if got != want:
                fails += 1
                print(f"MISMATCH {fn}({a},{b}): synth {got} != wasmtime {want}")

    wf = inst.exports(store)["trunc_s"]
    for a in TRUNC_INPUTS:
        uc = run_unicorn(text, base, syms["trunc_s"], s0_bits=f32_bits(a))
        got = uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
        want = wf(store, a) & 0xFFFFFFFF
        checked += 1
        if got != want:
            fails += 1
            print(f"MISMATCH trunc_s({a}): synth 0x{got:08x} != wasmtime 0x{want:08x}")

    for fn in ("conv_s", "conv_u"):
        wf = inst.exports(store)[fn]
        for a in I32_INPUTS:
            uc = run_unicorn(text, base, syms[fn], r0=a)
            got = uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF
            want = f32_bits(wf(store, a))
            checked += 1
            if got != want:
                fails += 1
                print(f"MISMATCH {fn}({a}): synth 0x{got:08x} ({bits_f32(got)}) "
                      f"!= wasmtime 0x{want:08x} ({bits_f32(want)})")

    if fails:
        sys.exit(f"\nFAIL: {fails}/{checked} f32 results diverged from wasmtime")
    print(f"GREEN: {checked}/{checked} f32 results bit-exact vs wasmtime "
          f"(m3 honest-reject confirmed).")


if __name__ == "__main__":
    main()
