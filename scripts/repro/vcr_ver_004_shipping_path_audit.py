#!/usr/bin/env python3
"""VCR-VER-004 — the ABI observable contract on the SHIPPING allocator (#242).

The sibling script `vcr_ver_004_instrument_independence.py` proves the new
instrument catches v0.53's mutation on the flag-off graph-colouring spike. That
spike is not what users compile with. THIS script asks the same question of the
DEFAULT path — `liveness::reallocate_function_post_exhaust`, the allocator every
`synth compile` runs — and turns the answer into an enforced floor.

For every function in the ARM repro corpus (`--relocatable`, the label-form path
the checker can analyze) it collects `SYNTH_ABI_CONTRACT_AUDIT=1`'s per-function
verdict and asserts:

  (A) ZERO `Violated`. This is the real gate. A violation here means the SHIPPING
      allocator moved a value out of an AAPCS result register — the exact class
      v0.53's mutation produced and both dataflow validators missed. It is also
      the FALSE-REJECTION alarm: the shipping allocator is known-good on this
      corpus (frozen anchors + every execution differential), so a `Violated`
      is far more likely to be a bug in the INSTRUMENT than in the compiler.
      Either way it must not pass silently.
  (B) a floor on `Holds`. Coverage is the honest weak point of a checker that
      declines on calls and unmodeled ops, so it is PINNED: if a change makes the
      instrument see less of the shipping path, that regression is visible rather
      than absorbed. The floor is set below the measured value, not at it, so
      normal corpus churn does not create noise.

The audit hook is REPORT-ONLY inside the compiler, deliberately. Making it gate
the default path would mean hard-erroring a user's compile on a checker whose
false-positive rate is only measured, not proven — the honest sequence is
measure first, flip on evidence. This script is that measurement, held to a
floor.

Measured at the time of writing (v0.54, 617 corpus functions, --relocatable):
    Holds 376 · NotAttempted 241 · Violated 0
    declines: unmodeled-op 159, call 62, indirect-call 11, numeric-offset-branch 9

Proven RED-FIRST, by real exit code, in both directions:
  * a stub `SYNTH` that emits a `Violated` line -> exit 1, naming the fixture;
  * a stub that emits nothing at all            -> exit 1 on the vacuity
    assertion ("the audit hook produced NO verdicts"), so a stale binary or an
    un-wired hook cannot make this job pass while gating nothing;
  * the real binary                             -> exit 0.

Run:  SYNTH=./target/debug/synth python3 scripts/repro/vcr_ver_004_shipping_path_audit.py
Exits nonzero on any Violated, or if Holds falls below the floor.
"""

import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
REPRO = REPO / "scripts/repro"
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

# Set below the measured 376 so ordinary corpus churn is not noise, but close
# enough that losing a whole construct class (a `reg_effect` arm, the label-form
# CFG, the return-sink recognition) trips it.
HOLDS_FLOOR = 340

VERDICT = re.compile(r"\[abi-contract-audit\] (Holds|Violated|NotAttempted)(.*)")
REASON = re.compile(r'reason: "([a-z-]+)"')


def main():
    fixtures = sorted(
        [p for p in REPRO.glob("*.wat")] + [p for p in REPRO.glob("*.wasm")]
    )
    if not fixtures:
        print("FAIL no corpus fixtures found")
        return 1

    env = dict(os.environ, SYNTH_ABI_CONTRACT_AUDIT="1")
    verdicts = Counter()
    reasons = Counter()
    violations = []

    for f in fixtures:
        r = subprocess.run(
            [SYNTH, "compile", str(f), "--relocatable", "-o", os.devnull],
            cwd=REPO,
            capture_output=True,
            text=True,
            env=env,
        )
        for line in (r.stdout + r.stderr).splitlines():
            m = VERDICT.search(line)
            if not m:
                continue
            kind, rest = m.group(1), m.group(2)
            verdicts[kind] += 1
            if kind == "NotAttempted":
                rm = REASON.search(rest)
                reasons[rm.group(1) if rm else "?"] += 1
            elif kind == "Violated":
                violations.append(f"{f.name}: {line.strip()}")

    total = sum(verdicts.values())
    print(f"functions audited (--relocatable) : {total}")
    print(f"  Holds                           : {verdicts['Holds']}")
    print(f"  NotAttempted                    : {verdicts['NotAttempted']}")
    print(f"  Violated                        : {verdicts['Violated']}")
    if reasons:
        print("decline reasons:")
        for k, v in reasons.most_common():
            print(f"    {k:<28} {v}")

    problems = []
    if total == 0:
        problems.append(
            "the audit hook produced NO verdicts — SYNTH_ABI_CONTRACT_AUDIT is "
            "not wired, or the binary is stale. This run gated nothing."
        )
    if verdicts["Violated"]:
        for v in violations:
            print("FAIL VIOLATION " + v)
        problems.append(
            f"{verdicts['Violated']} ABI observable-contract VIOLATION(s) on the "
            "SHIPPING allocator"
        )
    if verdicts["Holds"] < HOLDS_FLOOR:
        problems.append(
            f"coverage regression: Holds={verdicts['Holds']} < floor {HOLDS_FLOOR} "
            "— the instrument now sees LESS of the shipping path"
        )

    print()
    print(
        f"VCR-VER-004-SHIPPING HOLDS={verdicts['Holds']} "
        f"VIOLATED={verdicts['Violated']} TOTAL={total} FLOOR={HOLDS_FLOOR}"
    )
    if problems:
        for p in problems:
            print("FAIL " + p)
        print("RESULT: FAIL")
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
