#!/usr/bin/env python3
"""RQ-87-RUNNERSHAPE4 (#1451) — is the no-show/cancel split derivable from the
job object?

THE ANSWER THIS FILE SHIPS IS "NOT ESTABLISHED", AND IT IS A REFUTATION OF THIS
LANE'S OWN FIRST ATTEMPT. That attempt concluded "non-derivable, PINNED". Three
things were wrong with it, each found by re-measuring rather than re-reading, and
all three are recorded here because a pin that asserts the wrong verdict
confidently is worse than no pin.

1. THE SAMPLE NUMBERS WERE WRONG, by a mechanism this repository has a memory
   about. The first passes used a helper that returned None on failure and a
   caller that did `(api(...) or {}).get("jobs", [])`, so a failed page became an
   EMPTY JOB LIST silently. Two passes over IMMUTABLE data disagreed — 49
   unserved, then 41 — which is the tell. Re-measured in one pass with retries
   and a raise on exhaustion: SIXTY-EIGHT cancelled jobs, SIXTY-SEVEN unserved.
   HTTP 502 on this endpoint was observed live. An API failure is not an empty
   population.

2. A CANDIDATE SEPARATOR WAS MEASURED AND THEN LEFT OUT OF THE FIELD SET. The
   job's own SPAN, `completed_at - started_at`, was computed in the very first
   probe and never carried into the comparison. Every cancelled-unserved job
   measured here spans 1246-14421 seconds, while the no-show this repository has
   on record is described in `ci.yml` as "600s, zero steps". If that 600 is the
   span, it sits BELOW the entire observed range of both other populations, and
   span separates. The original conclusion was reached with the one field most
   likely to carry the answer excluded.

3. THE COMPARISON HAS A THIRD ARM NOBODY COUNTED. Hunting a real no-show across
   52 recent runs turned up FOUR cancelled-and-unstarted jobs inside runs whose
   conclusion is FAILURE, not cancelled — a fail-fast cascade, which is neither a
   no-show nor a superseded-run cancel. A two-way "no-show vs cancel" framing
   cannot be completed because there are at least THREE causes of a cancelled
   unstarted job, and the question as posed does not name the third.

AND THE NO-SHOW ARM WAS NEVER MEASURED AT ALL. The first attempt's `NO_SHOW`
fixture was HAND-TYPED FROM PROSE and its docstring claimed it was "captured
from the live API", which was false. No real no-show job object was obtained in
this window, so the arm the whole question turns on is absent. That is the
honest reason this is NOT ESTABLISHED rather than either pinned or refuted.

WHAT IS GENUINELY SETTLED, and it is the one thing the refuting command asked:
a no-show is separable from an ORDINARY QUEUED job, trivially, by `status` and
`conclusion`. A queued job reads `queued`/null; any cancelled job reads
`completed`/`cancelled`. That half of the refuting command is REFUTED, and it is
retained here as the positive control.

TWO MEASURING TRAPS, asserted rather than described, because either would
manufacture a separator that is not there. An unserved job's `runner_name` is the
EMPTY STRING and not null — all 67 measured carry `''` — so a test spelled
`runner_name is None` reports a difference between identical jobs. And the
`started_at` predicate is a TOLERANCE ("within a second of run creation"): tested
as exact equality it reported a separator, and measured as the tolerance it is,
62 of 67 collide.

NOT a CI gate in its reporting form — the figures below are a window sample.
CI gates the SELF-TEST.
"""
import argparse
import sys

# ---------------------------------------------------------------------------
# MEASURED POPULATIONS. Each carries how it was obtained, because the first
# attempt's numbers were unreliable in a way only provenance would have caught.
# ---------------------------------------------------------------------------

# ARM A — cancelled-never-served: jobs in five superseded runs deliberately
# cancelled during v0.87's merge work. ONE pass, retries, raise on exhaustion.
ARM_A = {
    "runs": 5, "cancelled": 68, "unserved": 67,
    "per_run_cancelled": [18, 9, 5, 18, 18],
    "delta_min": 1, "delta_median": 1, "delta_max": 661, "delta_within_1s": 62,
    "span_min": 1246, "span_median": 2483, "span_max": 8681,
    "runner_names_seen": [""],
}

# ARM B — cancelled-and-unstarted inside a NON-cancelled run, over 60 recent
# runs of which 52 were readable (ONE api failure, so the population is
# INCOMPLETE and says so). All four sit in runs whose conclusion is FAILURE:
# a fail-fast cascade, the third cause.
ARM_B = {
    "runs_listed": 60, "runs_scanned": 52, "api_failures": 1, "candidates": 4,
    "enclosing_run_conclusions": ["failure"], "lone": 2, "in_pairs": 2,
    "deltas": [1, 1, 1, 1], "spans": [5554, 5796, 10369, 14421],
}

# ARM C — a live ORDINARY QUEUED job: PR #1543's `Clippy` on head
# 080a79100979e2d982025b8092ad4fc586d3ae29, while the self-hosted rust-cpu pool
# was starved (all 7 rust-cpu runners busy; the idle runners carried only
# `lean-mem`/`light`, so they could not serve it).
ARM_C = {"status": "queued", "conclusion": None, "steps": 0,
         "runner_name": "", "delta": 0}

# ARM D — the recorded no-show. NOT a measured job object: this is the figure
# `ci.yml` states in prose for the 2026-09-02 light-pool incident. It is kept
# separate from the arms above precisely because it is not a measurement.
ARM_D_RECORDED = {"source": "ci.yml prose, 2026-09-02 light-pool incident",
                  "span_or_duration_seconds": 600, "steps": 0,
                  "job_object_obtained": False}

# The fields a job object offers for this comparison. `span` is here because
# leaving it out is what made the first attempt's conclusion unsafe.
FIELDS = ("status", "conclusion", "steps", "runner_name", "delta_within_1s", "span")

CAUSES = {
    "no-show": "the runner never picked the job up; the job is cancelled to clear it",
    "superseded-run cancel": "the whole run was cancelled; its unstarted jobs are cancelled with it",
    "fail-fast cascade": "the run FAILED and its still-queued jobs were cancelled — ARM B, "
                         "four instances, which the two-way framing does not name",
}


def queued_vs_cancelled_separators() -> list[str]:
    """The settled half: what distinguishes a queued job from any cancelled one."""
    return ["status", "conclusion"]


def span_ranges_overlap() -> bool:
    """Does the recorded no-show's figure fall inside the measured spans?"""
    lo = min(ARM_A["span_min"], min(ARM_B["spans"]))
    return lo <= ARM_D_RECORDED["span_or_duration_seconds"]


def report() -> int:
    print("THE REFUTING COMMAND, and the lane's own first answer REFUTED.\n")
    print("ARM A  cancelled-never-served (5 superseded runs, deliberately cancelled):")
    print(f"  {ARM_A['cancelled']} cancelled, {ARM_A['unserved']} unserved, "
          f"per-run {ARM_A['per_run_cancelled']}")
    print(f"  delta  min={ARM_A['delta_min']} median={ARM_A['delta_median']} "
          f"max={ARM_A['delta_max']}  within-1s={ARM_A['delta_within_1s']}/{ARM_A['unserved']}")
    print(f"  span   min={ARM_A['span_min']} median={ARM_A['span_median']} "
          f"max={ARM_A['span_max']}")
    print(f"\nARM B  cancelled+unstarted in a NON-cancelled run "
          f"({ARM_B['runs_scanned']}/{ARM_B['runs_listed']} readable, "
          f"{ARM_B['api_failures']} api failure — INCOMPLETE):")
    print(f"  {ARM_B['candidates']} found, all in runs concluding "
          f"{ARM_B['enclosing_run_conclusions']}; lone={ARM_B['lone']}")
    print(f"  spans {ARM_B['spans']}  -> a THIRD cause: fail-fast cascade")
    print(f"\nARM C  live ordinary QUEUED job: {ARM_C}")
    print(f"\nARM D  the recorded no-show: {ARM_D_RECORDED['span_or_duration_seconds']}s, "
          f"from {ARM_D_RECORDED['source']}")
    print(f"       job object obtained: {ARM_D_RECORDED['job_object_obtained']}  <-- the arm "
          f"the question turns on was never measured")
    print(f"\nSETTLED: a no-show IS separable from an ordinary queued job, by "
          f"{queued_vs_cancelled_separators()}. That half is REFUTED.")
    print(f"NOT ESTABLISHED: the no-show vs cancelled-unserved split. The span field was "
          f"excluded from the first attempt and\n  the recorded 600s sits "
          f"{'INSIDE' if span_ranges_overlap() else 'BELOW'} the measured span range "
          f"[{min(ARM_A['span_min'], min(ARM_B['spans']))}..{max(ARM_A['span_max'], max(ARM_B['spans']))}].")
    print("\nTHE THREE CAUSES OF A CANCELLED UNSTARTED JOB:")
    for k, v in CAUSES.items():
        print(f"  {k:24s} {v}")
    return 0


def self_test() -> int:
    fails = 0

    def ok(cond: bool, what: str) -> None:
        nonlocal fails
        print(f"  {'ok  ' if cond else 'FAIL'} {what}")
        if not cond:
            fails += 1

    # THE POSITIVE CONTROL: the half that IS settled must stay settled.
    ok(queued_vs_cancelled_separators() == ["status", "conclusion"],
       "a queued job is separable from a cancelled one by status+conclusion — "
       "the refuted half, kept as the positive control")
    ok(ARM_C["status"] == "queued" and ARM_C["conclusion"] is None,
       "and the live queued arm is a real measurement carrying those values")

    # THE HONEST GAP, asserted so it cannot be quietly forgotten.
    ok(ARM_D_RECORDED["job_object_obtained"] is False,
       "the no-show arm is recorded as UNMEASURED, not as a fixture")

    # ARM A's internal consistency: the per-run counts must sum to the total, or
    # the silent-skip bug is back.
    ok(sum(ARM_A["per_run_cancelled"]) == ARM_A["cancelled"],
       f"ARM A's per-run counts sum to its total ({sum(ARM_A['per_run_cancelled'])}"
       f" == {ARM_A['cancelled']}) — the check the first attempt's numbers failed")
    ok(len(ARM_A["per_run_cancelled"]) == ARM_A["runs"],
       "and there is one per-run count per run, so no run was silently dropped")

    # The span field must be IN the comparison. This is the case that would have
    # caught the first attempt.
    ok("span" in FIELDS,
       "the SPAN field is in the field set — excluding it is what made the first "
       "attempt's conclusion unsafe")

    # The third cause must be named; a two-way framing is the actual defect.
    ok(len(CAUSES) >= 3, f"at least three causes of a cancelled unstarted job are named "
                         f"(got {len(CAUSES)})")
    ok("fail-fast cascade" in CAUSES,
       "including the fail-fast cascade, which ARM B found and the question did not name")

    # The two measuring traps.
    ok(ARM_A["runner_names_seen"] == [""],
       "every unserved job measured carries runner_name == '' (not null), so a "
       "None-spelled collision test would report a false separator")
    ok(ARM_A["delta_within_1s"] > ARM_A["unserved"] // 2,
       f"the started_at TOLERANCE collides in the sample "
       f"({ARM_A['delta_within_1s']}/{ARM_A['unserved']}), so it is not a separator — "
       f"tested as exact equality it wrongly looked like one")

    # ARM B's incompleteness must be carried, not rounded away.
    ok(ARM_B["api_failures"] > 0 and ARM_B["runs_scanned"] < ARM_B["runs_listed"],
       "ARM B records its own INCOMPLETENESS (an api failure and a short scan) "
       "rather than presenting a partial population as whole")
    return 0 if fails == 0 else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    return self_test() if a.self_test else report()


if __name__ == "__main__":
    sys.exit(main())
