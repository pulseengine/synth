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

ISLANDS LANDED IN v0.72 (RQ-72-ISLANDS), AND THIS PIN WAS FLIPPED AS ITEM 3
INSTRUCTED. It went red on exactly that assertion, which is the design working
rather than a regression. What it pins now is NARROWER and still worth pinning:
the refusal itself, reached via the documented opt-out
`SYNTH_NO_LITPOOL_ISLANDS=1`. `emit_literal_pool` carries exactly ONE
`return Err` for this condition, so the off-leg and the on-leg reach the SAME
check — pinning it here keeps `imm12 > 0xFFF` from being loosened into a
wrong-address load, which was always reason (2) and is untouched by islands.

The ACCEPT side is owned by `litpool_islands_345_differential.py`, which also
proves byte-identity across the 165 corpus modules that need no island and
executes the islanded fixture against wasmtime.

WHY THE FIX IS NOT A ONE-LINE PLACEMENT CHANGE, measured on this tree:

  - Branch displacements are PRE-COMPUTED UPSTREAM of the encoder, in final
    machine terms. `arm_encoder.rs` says so in its own words: "offset is
    already the halfword displacement: (target - branch - 4) / 2". Two ArmOp
    variants carry them (`BOffset`, `BCondOffset`).
  - There is NO post-encode branch relaxation or fixup pass:
    `resolve_label_branches` (arm_backend.rs:2333, called at 1468/1590) IS such
    a pass, with a size fixed point, and it DOES run on the direct/--relocatable
    path. Corrected by the v0.71 cold review, which also showed the grep this
    text previously cited prints NOTHING AT ALL (rc=1) and so proved nothing.
    What has no post-encode fixup is the OPTIMIZED path's inline
    `BOffset`/`BCondOffset`, which carry no label and are left untouched.

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
        # ISLANDS OFF: this pin is about the REFUSAL, which is now reachable
        # only with the opt-out. Same `return Err`, same arithmetic.
        env = dict(os.environ)
        env["SYNTH_NO_LITPOOL_ISLANDS"] = "1"
        r = subprocess.run(
            [SYNTH, "compile", FIXTURE, "-o", obj,
             "--target", "cortex-m7", "--relocatable", "--all-exports",
             "--native-pointer-abi"],
            capture_output=True, text=True, timeout=180, env=env,
        )
        blob = r.stdout + r.stderr
        m = REFUSAL.search(blob)
        assert m, (
            "litpool-345: the fixture COMPILED (or failed differently) WITH "
            "SYNTH_NO_LITPOOL_ISLANDS=1 — the opt-out is unwired, so the "
            "islands differential's two legs are the same path and its "
            "byte-identity result is vacuous. Output:\n"
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
            capture_output=True, text=True, timeout=180, env=env,
        )
        # `env=env` above is load-bearing and was MISSING until the v0.72
        # gate-potency cold review. Without it the control ran with islands
        # ON — the configuration in which EVERYTHING compiles, including the
        # long fixture — so it could not discriminate and the assertion below
        # was true for the wrong reason. Measured four ways:
        #   short + islands ON  rc=0     short + islands OFF rc=0
        #   long  + islands ON  rc=0     long  + islands OFF rc=1 (the pin)
        # Only the islands-OFF row separates short from long, so only that
        # row is a control.
        assert r2.returncode == 0, (
            "POTENCY FAILED: the SHORT control must compile with islands "
            "DISABLED. If it does not, this script is pinning something "
            "other than the 4 KB range:\n"
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
