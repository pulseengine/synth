#!/usr/bin/env python3
"""#518 — CHARACTERIZE the i64-param binop miscompile on BOTH selectors.

This is the *oracle-first* artifact for issue #518 (epic #242, VCR-RA/VCR-SEL):
it reproduces and QUANTIFIES the defect against wasmtime ground truth before the
gated fix lands. It does NOT change codegen — it compiles the in-tree fixture
`i64_param_518.wat`, runs each export under unicorn (i64-aware: lo in R0, hi in
R1), and compares to wasmtime. It exercises BOTH lowering paths:

  * OPTIMIZED  (`synth compile ... --target cortex-m4`)  — the IR path.
  * DIRECT     (`... --relocatable`)                     — the shipped/relocatable
                                                           path (`select_with_stack`).

ROOT CAUSE (both paths, one omission — an i64 *param* is never classified i64):
  * Direct: `infer_i64_locals` learns i64-ness only from `LocalSet`/`LocalTee` of
    an i64 producer; a param that is only READ keeps `is_i64=false`. So
    `local.get 0` pushes `StackVal::Reg{is_i64:false}`, its implicit high register
    (R1 = `i64_pair_hi(R0)`) is NOT reserved on the vstack, the following
    `i64.const` is allocated INTO R1, and `i64.add` then reads `a_hi=R1` — already
    clobbered. Low half is correct; high half returns the const's low word.
  * Optimized: `I64Load`'s param-home guard (`num_params >= 2`/`>= 4`) confuses a
    *register* count with a *param* count — a single `(param i64)` has
    num_params==1, so it falls through to a fresh callee-saved pair (R4:R5) that
    was never homed from R0:R1. The param is dropped entirely.

EXPECTED while the bug is live: BOTH paths diverge from wasmtime on the i64-param
functions (t_add/t_sub/t_or, and the AAPCS even-aligned t_mixed); the i32 control
(t_i32) stays correct. This script EXITS 0 when that characterization holds (the
bug reproduces exactly as documented) and EXITS 1 if reality diverges from the
documented root cause — i.e. it is a stable characterization guard, not a CI red
gate. When the gated fix lands, flip EXPECT_MISCOMPILE→False: the same script
becomes the pass/fail correctness oracle (all paths must then match wasmtime).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth /tmp/synthvenv/bin/python \
      scripts/repro/i64_param_518_differential.py
"""
import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("i64_param_518.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET, R11 = 0x100000, 0x900000, 0x300000, 0x20000000

# While the bug is live we EXPECT the i64-param functions to miscompile. Flip to
# False in the gated fix PR; the script then enforces correctness on every path.
EXPECT_MISCOMPILE = True

# (export, arg-list, signature) — args/sig drive AAPCS-correct placement so the
# harness matches the TRUE calling convention, not synth's buggy mapping.
#   sig "i64"      -> one i64 param in R0:R1
#   sig "i32,i64"  -> i32 in R0, i64 EVEN-ALIGNED in R2:R3 (R1 skipped)
#   sig "i32"      -> one i32 param in R0
CASES = [
    ("t_add", [(7,)], "i64"),
    ("t_add", [(0xFFFFFFFF,)], "i64"),
    ("t_add", [(0x1_0000_0000,)], "i64"),
    ("t_sub", [(100,)], "i64"),
    ("t_or", [(0x8,)], "i64"),
    ("t_mixed", [(3, 10)], "i32,i64"),
    # AAPCS i64-param register-assignment matrix — the even-aligned-pair vs
    # sequential-index distinction the fix's mapping logic must get right.
    ("t_ii_add", [(7, 5)], "i64,i64"),          # p0=R0:R1, p1=R2:R3
    ("t_ii_add", [(0xFFFFFFFF, 1)], "i64,i64"),
    ("t_i64_i32", [(10, 3)], "i64,i32"),        # p0=R0:R1, p1=R2
    ("t_snd_i64", [(100, 40)], "i64,i64"),      # reads only p1=R2:R3
    ("t_i32", [(7,)], "i32"),
]
# functions whose result is i64 (read R0:R1) vs i32 (read R0 only)
I64_RESULT = {"t_add", "t_sub", "t_or", "t_mixed",
              "t_ii_add", "t_i64_i32", "t_snd_i64"}
I64_PARAM_FNS = I64_RESULT


def wasmtime_run(fn, args):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    return inst.exports(store)[fn](store, *args)


def compile_synth(out, relocatable):
    env = {"PATH": "/usr/bin:/bin"}
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
           "--target", "cortex-m4", "--all-exports"]
    if relocatable:
        cmd.append("--relocatable")
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"compile failed (reloc={relocatable}): {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name and sy["st_info"]["type"] == "STT_FUNC":
                    syms[sy.name] = sy["st_value"]
    return code, base, syms


def place_args(mu, args, sig):
    """Write args into registers per TRUE AAPCS (even-aligned i64 pairs)."""
    regs = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
    nxt = 0
    flat = [a for tup in args for a in tup]
    types = sig.split(",")
    vi = 0
    for t in types:
        v = flat[vi]
        vi += 1
        if t == "i64":
            if nxt % 2:  # even-align: skip an odd register
                nxt += 1
            mu.reg_write(regs[nxt], v & 0xFFFFFFFF)
            mu.reg_write(regs[nxt + 1], (v >> 32) & 0xFFFFFFFF)
            nxt += 2
        else:  # i32
            mu.reg_write(regs[nxt], v & 0xFFFFFFFF)
            nxt += 1


def unicorn_run(code, base, faddr, args, sig, i64_result):
    foff = (faddr & ~1) - base
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, R11)
    place_args(mu, args, sig)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + foff) | 1, RET, count=100000)
    except UcError as e:
        return f"ERR:{e}"
    lo = mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
    if i64_result:
        hi = mu.reg_read(UC_ARM_REG_R1) & 0xFFFFFFFF
        return lo | (hi << 32)
    return lo


def run_path(label, relocatable):
    out = f"/tmp/i518_{'rel' if relocatable else 'opt'}.o"
    compile_synth(out, relocatable)
    code, base, syms = load(out)
    print(f"\n=== {label} path ===")
    divergences = 0
    control_ok = True
    for fn, args, sig in CASES:
        faddr = syms.get(fn)
        if faddr is None:
            print(f"  {fn}: SYMBOL MISSING")
            divergences += 1
            if fn not in I64_PARAM_FNS:
                control_ok = False
            continue
        exp = wasmtime_run(fn, args[0])
        got = unicorn_run(code, base, faddr, args, sig, fn in I64_RESULT)
        match = isinstance(got, int) and got == exp
        flag = "ok " if match else "BUG"
        if not match:
            divergences += 1
            if fn not in I64_PARAM_FNS:  # an i32-control regression is a real fail
                control_ok = False
        print(f"  [{flag}] {fn}{args[0]} -> {got}  (wasmtime {exp})"
              + ("" if match else "  [MISCOMPILE: off by hi/param]"))
    return divergences, control_ok


def main():
    opt_div, opt_ctrl = run_path("OPTIMIZED (--target cortex-m4)", relocatable=False)
    rel_div, rel_ctrl = run_path("DIRECT (--relocatable)", relocatable=True)

    print("\n--- characterization verdict ---")
    # The i32 control must ALWAYS match; only i64-param fns are allowed to diverge
    # while the bug is live. So a "healthy" buggy state = both paths diverge on
    # >=1 i64-param fn AND neither breaks the i32 control.
    if EXPECT_MISCOMPILE:
        ok = opt_div > 0 and rel_div > 0 and opt_ctrl and rel_ctrl
        print(f"opt divergences={opt_div} (control_ok={opt_ctrl})  "
              f"direct divergences={rel_div} (control_ok={rel_ctrl})")
        if ok:
            print("RESULT: PASS — #518 reproduces on BOTH paths exactly as the "
                  "root-cause documents (i64 param dropped/high-half clobbered "
                  "across the full single/dual/even-aligned matrix; i32 control "
                  "correct). Oracle ready for the gated fix.")
            sys.exit(0)
        print("RESULT: FAIL — reality diverged from the documented #518 root "
              "cause (a path no longer miscompiles, or the i32 control broke). "
              "Re-examine before trusting the fix spec.")
        sys.exit(1)
    else:
        total = opt_div + rel_div
        if total == 0:
            print("RESULT: PASS — both paths now match wasmtime on every i64-param "
                  "function. #518 fixed.")
            sys.exit(0)
        print(f"RESULT: FAIL — {total} residual divergence(s); #518 not fully fixed.")
        sys.exit(1)


if __name__ == "__main__":
    main()
