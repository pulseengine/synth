#!/usr/bin/env python3
# ci-status: wired
# ci-checks: stdout /^litpool-345 declines: (\d+)$/ >= 1
"""RQ-71-ISLANDS (#345): pin the literal-pool range refusal, and pin that it is
still a REFUSAL rather than a miscompile.

THIS IS A DECLINE PIN, NOT A FIX. v0.71 did not ship constant islands; it
reproduced the class in-repo and measured why the fix is larger than it looks.
The pin exists so that:

  1. the class stays REPRODUCIBLE here, without cpetig's 50722-byte module,
     which is an issue attachment and not in this repository (the
     RQ-70-FALCONCORPUS lesson, applied before the fact rather than after);
  2. the refusal cannot silently become a MISCOMPILE. `imm12 > 0xFFF` is the
     only thing standing between an out-of-range pool word and a load from a
     wrong address, and it is one `if` in `arm_backend.rs`. If that check is
     ever loosened, this script goes red;
  3. WHEN ISLANDS LAND, THIS SCRIPT MUST FAIL. That is the point. The fixture
     will compile, `declines` will drop to 0, and whoever lands the fix is
     forced to come here, flip the expectation, and update RQ-71-ISLANDS
     rather than leaving a stale pin claiming a defect that is gone.

WHY THE FIX IS NOT A ONE-LINE PLACEMENT CHANGE, measured on this tree:

  - Branch displacements are PRE-COMPUTED UPSTREAM of the encoder, in final
    machine terms. `arm_encoder.rs` says so in its own words: "offset is
    already the halfword displacement: (target - branch - 4) / 2". Two ArmOp
    variants carry them (`BOffset`, `BCondOffset`).
  - There is NO post-encode branch relaxation or fixup pass:
    `grep -nE 'fn [a-z_]*(relax|fixup|patch)'` over `arm_backend.rs` and
    `arm_encoder.rs` finds only literal-pool patching.

So inserting an island mid-function silently corrupts every branch that spans
the insertion point, with nothing to repair it. That is worse than the "branch
into data" hazard the plan anticipated — it is a branch to the WRONG PLACE,
silently, which is the miscompile class VCR exists to prevent.

ONE ALTERNATIVE WAS CHECKED AND IS ALSO NOT SUFFICIENT. A pool at the function
START, branched over once, would be sound without any fixup pass: inserting N
bytes at offset 0 shifts every body instruction uniformly, so each intra-body
relative displacement is preserved exactly. But it needs the U=0 (backward)
LDR-literal form, of which synth emits ZERO today, and start-pool plus end-pool
still only serve accesses within 4 KB of either END. cpetig's function is 50722
bytes with accesses throughout, so it genuinely needs N islands, which needs the
fixup pass.
"""

import os
import re
import subprocess
import sys
import tempfile

SYNTH = os.environ.get("SYNTH_BIN", "./target/debug/synth")
HERE = os.path.dirname(os.path.abspath(__file__))
FIXTURE = os.path.join(HERE, "litpool_islands_345.wat")
# The exact refusal. Matched by SHAPE, not by the imm12 VALUE: that number moves
# with ordinary codegen drift and pinning it would make this script red for a
# reason that has nothing to do with the defect.
REFUSAL = re.compile(r"LdrSym literal pool out of range \(#345\): imm12=(\d+) > 4095")


def main():
    assert os.path.exists(FIXTURE), f"missing committed fixture {FIXTURE}"
    declines = 0
    with tempfile.TemporaryDirectory() as td:
        obj = os.path.join(td, "litpool.o")
        r = subprocess.run(
            [SYNTH, "compile", FIXTURE, "-o", obj,
             "--target", "cortex-m7", "--relocatable", "--all-exports",
             "--native-pointer-abi"],
            capture_output=True, text=True, timeout=180,
        )
        blob = r.stdout + r.stderr
        m = REFUSAL.search(blob)
        assert m, (
            "litpool-345: the fixture COMPILED (or failed differently) — if "
            "constant islands landed, that is the good news, and this pin must "
            "now be flipped and RQ-71-ISLANDS updated. Output:\n"
            + blob[:900]
        )
        imm12 = int(m.group(1))
        assert imm12 > 4095, f"refusal reports imm12={imm12}, which is IN range"
        declines += 1
        print(f"  OK litpool-345: refuses with imm12={imm12} > 4095 "
              f"(a REFUSAL, not a miscompile)")

        # POTENCY: the same fixture with a SHORT body must compile, so this
        # script is pinning the range and not merely that the fixture is
        # unbuildable for some unrelated reason.
        short = os.path.join(td, "short.wat")
        with open(FIXTURE) as f:
            text = f.read()
        head, sep, _ = text.partition("    local.get 2\n")
        assert sep, "fixture shape changed; cannot build the short control"
        with open(short, "w") as f:
            f.write(head + "    local.get 1)\n  (export \"big\" (func $big)))\n")
        r2 = subprocess.run(
            [SYNTH, "compile", short, "-o", os.path.join(td, "short.o"),
             "--target", "cortex-m7", "--relocatable", "--all-exports",
             "--native-pointer-abi"],
            capture_output=True, text=True, timeout=180,
        )
        assert r2.returncode == 0, (
            "POTENCY FAILED: the SHORT control must compile. If it does not, "
            "this script is pinning something other than the 4 KB range:\n"
            + (r2.stdout + r2.stderr)[:900]
        )
        print("  OK potency: the same shape with a short body COMPILES — "
              "the pin is the 4 KB range, not the fixture")

    print(f"litpool-345 declines: {declines}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except AssertionError as e:
        print(f"litpool-345 FAIL: {e}", file=sys.stderr)
        sys.exit(1)
