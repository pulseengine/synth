#!/usr/bin/env python3
"""#518 cross-backend contrast — RISC-V LOUD-SKIPS the i64-param class (#242, #518).

Companion to `i64_param_518_differential.py` (which proves the ARM selectors
SILENTLY MISCOMPILE an i64 binop reading an i64 param). This oracle measures the
SAME fixture on the RISC-V backend and shows the SAME root cause (an i64 param is
never classified i64, so it reaches an i64 op as an i32 operand) manifests
DIFFERENTLY: the RV32 selector validates the operand-stack TYPE before lowering
the i64 op, hits `stack type mismatch ... expected i64, found i32`, and returns a
typed `Err` → the function is LOUD-SKIPPED (a `warning: skipping function …` plus
absence from the emitted symbol table), never emitted as wrong code.

This is the #378 never-guess contract (the ARM encoder's Ok-or-Err discipline,
#180/#185) acting as the honest-fail backstop that ARM's `select_with_stack`
LACKS for i64 params. The consequence for the VCR-SEL-005 cross-backend parity
ledger: on this class RV32 is INCOMPLETE (cannot yet compile i64-param functions)
but SOUND (no silent wrong-code); ARM is COMPLETE-but-UNSOUND (#518) until its
gated fix lands. A future regression that removed the RV32 stack-type guard would
flip a loud-skip into a silent miscompile — this oracle catches that.

What it asserts (analysis-only — compiles + inspects symtab/stderr, runs nothing):
  - every i64-PARAM function (t_add/t_sub/t_or/t_mixed/t_ii_add/t_i64_i32/
    t_snd_i64) is LOUD-SKIPPED: a `skipping function '<name>'` warning is emitted
    AND the name is absent from the .o symbol table.
  - the i32 control (t_i32) IS emitted (present in the symtab) — the i32 path is
    unaffected, so the skip is specific to the i64-param defect, not a blanket
    backend failure (non-vacuity).

Run (needs the riscv backend built in; default features include it):
  SYNTH=./target/debug/synth python scripts/repro/i64_param_518_riscv_loudskip.py
Exits 0 when the loud-skip contract holds exactly; 1 if any i64-param function was
silently emitted (a real RV32 regression) or the i32 control was skipped.
"""
import os
import subprocess
import sys
from pathlib import Path

from elftools.elf.elffile import ELFFile

WAT = Path(__file__).with_name("i64_param_518.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
OUT = "/tmp/i518_rv_loudskip.o"

I64_PARAM_FNS = [
    "t_add", "t_sub", "t_or", "t_mixed", "t_ii_add", "t_i64_i32", "t_snd_i64",
]
I32_CONTROL = "t_i32"


def compile_riscv():
    cmd = [SYNTH, "compile", str(WAT), "-o", OUT, "-b", "riscv",
           "--target", "riscv32imac", "--all-exports", "--relocatable"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0:
        sys.exit(f"riscv compile failed (expected success with skips): {r.stderr}")
    return r.stderr


def emitted_funcs():
    e = ELFFile(open(OUT, "rb"))
    return {
        s.name
        for sec in e.iter_sections()
        if sec.header.sh_type == "SHT_SYMTAB"
        for s in sec.iter_symbols()
        if s.name and s["st_info"]["type"] == "STT_FUNC"
    }


def main():
    stderr = compile_riscv()
    emitted = emitted_funcs()
    print("=== RV32 #518 loud-skip contract ===")
    fails = 0

    for fn in I64_PARAM_FNS:
        warned = f"skipping function '{fn}'" in stderr
        absent = fn not in emitted
        ok = warned and absent
        if not ok:
            fails += 1
        why = []
        if not warned:
            why.append("no skip warning")
        if not absent:
            why.append("SILENTLY EMITTED (regression!)")
        print(f"  [{'ok ' if ok else 'BUG'}] {fn}: loud-skipped"
              + ("" if ok else f"  [{', '.join(why)}]"))

    ctrl_ok = I32_CONTROL in emitted
    if not ctrl_ok:
        fails += 1
    print(f"  [{'ok ' if ctrl_ok else 'BUG'}] {I32_CONTROL}: i32 control emitted"
          + ("" if ctrl_ok else "  [skipped — backend broken, not #518-specific]"))

    print("\n--- verdict ---")
    if fails == 0:
        print("RESULT: PASS — RV32 loud-skips the #518 i64-param class (honest-fail "
              "backstop) while emitting the i32 control. Same root cause as ARM, "
              "but SOUND (no silent wrong-code) vs ARM's silent miscompile.")
        sys.exit(0)
    print(f"RESULT: FAIL — {fails} issue(s): an i64-param function was silently "
          "emitted (RV32 stack-type guard regressed → would miscompile), or the "
          "i32 control was lost.")
    sys.exit(1)


if __name__ == "__main__":
    main()
