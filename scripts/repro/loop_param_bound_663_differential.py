#!/usr/bin/env python3
"""#663 — thumb-2 parameter-bounded loop: live param bound clobbered by the
induction increment (loop exits after 1 iteration).

The direct selector's #193 param reservation computes each register-backed
param's LAST READ with a linear scan — but a loop back-edge re-executes every
read inside the Loop..End span, so a param whose (linearly) last read sits
inside a loop body lost its reservation before the loop finished. The
induction update `$i + 1` was then allocated into r0 (the live bound n):
`adds r0, r7, #1` — iteration 2's `cmp r2, r0` compares $i against $i+1 and
exits. Fix: extend the last-read horizon of any param read inside a
Loop..End span to the span's End (transitively, so nested loops extend to
the outermost enclosing loop).

Table (each row cross-checked against wasmtime ground truth under unicorn
Thumb; pre-fix synth returns 0 for every param-bounded row):

  sum_below(3, _)    -> 3       <- RED pre-fix (0)
  sum_below(10, _)   -> 45      <- RED pre-fix (0)  (gale's #663 table row)
  sum_below(100, _)  -> 4950    <- RED pre-fix (0)
  sum_below(1000, _) -> 499500  <- RED pre-fix (0)
  sum_stride(7, 5)   -> 35      (bound in r1, stride param also live)
  sum_nested(4, 3)   -> 12      (bound read only in the INNER loop)
  sum_const(_, _)    -> 45      (constant bound — correct pre-fix, pins
                                 the loop lowering itself)

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/loop_param_bound_663_differential.py
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

WAT = Path(__file__).with_name("loop_param_bound_663.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")

CASES = [
    ("sum_below", (3, 0)),
    ("sum_below", (10, 0)),
    ("sum_below", (100, 0)),
    ("sum_below", (1000, 0)),
    ("sum_below", (0, 0)),  # zero-trip loop
    ("sum_stride", (7, 5)),
    ("sum_nested", (4, 3)),
    ("sum_const", (0, 0)),
]

# Both direct-selector paths exercise the #193 reservation machinery.
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
        mu.emu_start((0x1000 + off) | 1, ret, timeout=5_000_000, count=100_000)
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
                print(f"[{vname}] {mark} {func}{args}: synth={got} wasmtime={want}")
    if fails:
        sys.exit(f"\n#663 differential: {fails} mismatches")
    print("\n#663 differential: all green (param bound survives the back-edge)")


if __name__ == "__main__":
    main()
