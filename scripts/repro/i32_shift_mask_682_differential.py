#!/usr/bin/env python3
"""#682 — thumb-2 i32 shifts must reduce the amount mod 32 (WASM §4.3.2).

ARMv7-M register-controlled shifts consume Rm[7:0] and yield 0 (LSL/LSR) or
the sign (ASR) for amounts >= 32; WASM requires `amount mod 32`. The bare
`LSL.W/LSR.W/ASR.W rd, rn, rm` lowering (present since before VCR-SEL inc-2,
faithfully inherited by the DSL rules whose model-side proof was vacuous —
ArmSemantics' LSL_reg used I32.shl's internal mod-32) silently miscompiled
every shift with amount >= 32. Fix: `AND R12, rm, #31` before the shift, on
both direct selectors and in the Rocq-proved rules (now non-vacuous under
either shift semantics). ROR is cyclic, so Rm[7:0] agrees with WASM — pinned
here as the unmasked exemption.

Table (gale's #682 repro + variable-amount and rotr rows, each cross-checked
against wasmtime ground truth under unicorn Thumb):

  shl32(1)             -> 1        <- RED on pre-fix synth (0)
  shl33(1)             -> 2        <- RED (0)
  shl300(1)            -> 4096     <- RED (0)
  shr300(0x80000000)   -> 0x80000  <- RED (0)
  sar300(0x40000000)   -> 0x40000  <- RED (0)
  shl_var(1, 33)       -> 2        <- RED (0)
  shr_var(-1, 40)      -> 0x00FFFFFF
  sar_var(0x80000000, 63) -> -1 (mod-32 amount = 31)
  rotr_var(0x00000001, 33) -> 0x80000000  (cyclic, correct pre-fix too)
  + in-range sanity rows (amounts < 32 unchanged)

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/i32_shift_mask_682_differential.py
Exits nonzero on any mismatch.
"""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("i32_shift_mask_682.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")

CASES = [
    ("shl32", (1,)),
    ("shl33", (1,)),
    ("shl300", (1,)),
    ("shr300", (0x80000000,)),
    ("sar300", (0x40000000,)),
    ("shl_var", (1, 33)),
    ("shl_var", (1, 300)),
    ("shr_var", (0xFFFFFFFF, 40)),
    ("sar_var", (0x80000000, 63)),
    ("rotr_var", (1, 33)),
    # in-range sanity: amounts < 32 must be untouched by the fix
    ("shl_var", (1, 4)),
    ("shr_var", (0x100, 4)),
    ("sar_var", (0x80000000, 4)),
    ("rotr_var", (0x10, 4)),
]

# Both direct-selector paths: --relocatable (select_with_stack) and the
# blind fixed-register path is covered by unit tests; the optimized default
# path already masked (bridge) — included as a regression pin.
VARIANTS = [
    ("relocatable", ["-t", "cortex-m3", "--relocatable"]),
    ("default", ["-t", "cortex-m3"]),
]


def compile_elf(out, extra):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, *extra, "--all-exports"],
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed ({extra}): {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"] - base
    return code, syms


def wasm_expected(func, args):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    sargs = [a - 2**32 if a >= 2**31 else a for a in args]
    return inst.exports(st)[func](st, *sargs) & 0xFFFFFFFF


def run_arm(code, off, args):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(0, 0x40000)
    mu.mem_write(0x1000, code)
    ret = 0x30000
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    for reg, val in zip((UC_ARM_REG_R0, UC_ARM_REG_R1), args):
        mu.reg_write(reg, val & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_SP, 0x3F000)
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    try:
        mu.emu_start((0x1000 + off) | 1, ret, timeout=5_000_000, count=10_000)
    except UcError as e:
        return f"UC_ERR:{e}"
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def main():
    fails = 0
    for vname, extra in VARIANTS:
        with tempfile.NamedTemporaryFile(suffix=".o") as tf:
            compile_elf(tf.name, extra)
            code, syms = load(tf.name)
            for func, args in CASES:
                want = wasm_expected(func, args)
                if func not in syms:
                    print(f"[{vname}] SYMBOL MISSING: {func}")
                    fails += 1
                    continue
                got = run_arm(code, syms[func], args)
                ok = got == want
                fails += 0 if ok else 1
                mark = "ok  " if ok else "FAIL"
                print(
                    f"[{vname}] {mark} {func}{args}: synth={got:#x} wasmtime={want:#x}"
                    if isinstance(got, int)
                    else f"[{vname}] {mark} {func}{args}: synth={got} wasmtime={want:#x}"
                )
    if fails:
        sys.exit(f"\n#682 differential: {fails} mismatches")
    print("\n#682 differential: all green (WASM mod-32 shift semantics hold)")


if __name__ == "__main__":
    main()
