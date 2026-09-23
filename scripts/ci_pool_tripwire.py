#!/usr/bin/env python3
"""RQ-72-CIPOOL (#1062 increment 3): a CEILING on how much of CI queues against
the GitHub-hosted `ubuntu-latest` quota, and a DEADLOCK GUARD on the required
contexts.

WHY A STRUCTURAL PIN AND NOT A QUEUE-DEPTH CHECK
------------------------------------------------
The obvious gate samples the live queue and fails when it is deep. That gate
would be red during a merge burst and green ten minutes later on an UNCHANGED
repository — a verdict that depends on when it ran. Measured at the v0.72 cut,
three samples 50 s apart on run 35888386080 all read `queued={}`; the v0.71
readings of the same pool read 55 and 57 queued. BOTH are real. The pool is not
saturated, it is BURST-SENSITIVE, and the thing that makes bursts hurt is
structural: what share of the job definitions point at one quota.

So this pins the SHARE OF JOB DEFINITIONS, which is a fact about `ci.yml`:
identical for every observer, stable between runs, and the actual cause.
(#1062's own history records the same correction — "sampled rather than read
off one instant" — after an earlier 7/7 point reading turned out to be a
merge-wave transient.)

MATCH THE LABEL EXACTLY, NEVER BY SUBSTRING
-------------------------------------------
A first pass at this counted `ubuntu` as a substring and reported 56/67. That
swept in `ubuntu-24.04-arm`, which is a DIFFERENT hosted pool with its own
queue, and inflated the number this lane exists to reduce — in the flattering
direction. The honest figure is 55/67. Exact-label matching is not a style
preference here; it is the difference between a true and a false number.

THE DEADLOCK GUARD
------------------
Retargeting a REQUIRED context is the one unsafe move: a required NAME that
never runs blocks every merge with no red to revert. So this also asserts that
every required context is still DEFINED and still has a `runs-on` — catching a
rename or a deletion before it can deadlock the branch, rather than after.
"""
import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
CI = ROOT / ".github" / "workflows" / "ci.yml"

# The ceiling. It is a CEILING and not an equality: a PR may add an
# `ubuntu-latest` job when it also moves others off, and a ratchet that
# punishes net progress is a ratchet people route around. Lower it in the same
# PR that earns the lower number — never raise it without a written reason
# here, which is the #911 rule applied to pool share.
#
#   v0.72 (RQ-72-CIPOOL): 55 -> 52. Measured on ff7a8dd1, then EARNED in
#   this same PR by moving three PURE-cargo, NON-required jobs to
#   [self-hosted, linux, x64, rust-cpu]: vcr-ra-003-alloc-validator-gate,
#   vcr-ra-003-rv32-alloc-validator-gate and
#   vcr-sel-005-cross-backend-op-parity-gate. Each uses only
#   checkout + rust-toolchain + cache, which is the shape `Clippy` (a
#   REQUIRED context) has run on this pool with since increment 2. The programme's earlier
#   readings were 56/65 (86.2%, #1062 increment 2) and 55/67 (82%) here — the
#   share is falling because v0.71's musl job and v0.72's litpool-islands job
#   were placed on the self-hosted pool rather than defaulting.
UBUNTU_LATEST_CEILING = 52

EXACT_LABEL = "ubuntu-latest"


def pool_of(runs_on):
    """The pool a `runs-on:` names. Self-hosted is a LABEL SET, everything else
    is a single string; neither is matched by substring."""
    if isinstance(runs_on, list):
        return "self-hosted" if "self-hosted" in runs_on else ",".join(runs_on)
    return str(runs_on)


def load_jobs():
    doc = yaml.safe_load(CI.read_text())
    return doc["jobs"]


# The required contexts, PINNED. Read from
# `repos/<repo>/branches/main/protection/required_status_checks/contexts`
# on 2026-09-23 and committed here on purpose:
#
#   1. The deadlock guard must run WITHOUT the network. The first version
#      called `gh` and skipped when it was unavailable — and no other job in
#      this workflow calls `gh`, so on the runner it skipped (or crashed)
#      every time. A guard that never executes is the "gate nobody asks"
#      defect RQ-72-ISSUEGATE is about, reproduced by the lane meant to fix
#      the pool.
#   2. A committed list is a CONTRACT. If branch protection changes, the
#      cross-check below says so instead of silently adopting the new set —
#      a required context appearing or vanishing is exactly the event worth
#      a visible diff.
REQUIRED_CONTEXTS = [
    "Format",
    "Clippy",
    "Test",
    "Z3 Verification",
    "Claim Check",
    "Version Pin Sweep",
    "Bazel Build & Proofs",
    "Kani Verification",
    "Rivet Validation",
]


def live_required_contexts(repo):
    """The API's view, or None when it cannot be read.

    `gh` may be absent from a runner entirely, in which case `subprocess.run`
    RAISES rather than returning non-zero — the first version of this function
    did not catch that and turned a missing tool into a failed required
    context."""
    try:
        out = subprocess.run(
            ["gh", "api",
             f"repos/{repo}/branches/main/protection/required_status_checks/contexts",
             "--jq", ".[]"],
            capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    return [l.strip() for l in out.stdout.splitlines() if l.strip()]


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default="pulseengine/synth")
    ap.add_argument("--offline", action="store_true",
                    help="skip the required-context deadlock guard (no network)")
    args = ap.parse_args()

    jobs = load_jobs()
    counts = Counter(pool_of(j.get("runs-on")) for j in jobs.values())
    total = sum(counts.values())
    ubl = counts.get(EXACT_LABEL, 0)

    print(f"ci-pool: {total} job definitions in ci.yml")
    for pool, n in counts.most_common():
        print(f"ci-pool:   {n:3d}  {pool}")
    pct = (100.0 * ubl / total) if total else 0.0
    print(f"ci-pool: {EXACT_LABEL} share = {ubl}/{total} = {pct:.0f}% "
          f"(ceiling {UBUNTU_LATEST_CEILING})")

    failures = []
    if ubl > UBUNTU_LATEST_CEILING:
        failures.append(
            f"CEILING: {ubl} job definitions target `{EXACT_LABEL}`, above the "
            f"pinned ceiling of {UBUNTU_LATEST_CEILING}. A new job defaulting to "
            f"the GitHub-hosted quota makes every other lane queue longer during "
            f"a merge burst. Put it on `[self-hosted, linux, x64, rust-cpu]` or "
            f"`light`, or lower something else in this PR and move the ceiling "
            f"with a written reason.")
    if ubl < UBUNTU_LATEST_CEILING:
        # A ratchet that lets a win be silently given back is not a ratchet.
        failures.append(
            f"RATCHET: {ubl} is BELOW the pinned ceiling {UBUNTU_LATEST_CEILING} "
            f"— lower `UBUNTU_LATEST_CEILING` to {ubl} in this PR so the win "
            f"cannot be given back without a visible diff (the claims.yaml "
            f"baseline rule, applied here).")

    # ---- the deadlock guard: ALWAYS runs, from the pinned contract ---------
    by_name = {}
    for key, j in jobs.items():
        by_name[j.get("name", key)] = j
        by_name.setdefault(key, j)
    on_hosted = 0
    for c in REQUIRED_CONTEXTS:
        j = by_name.get(c)
        if j is None:
            failures.append(
                f"DEADLOCK: required context `{c}` is not defined in ci.yml. "
                f"A required NAME that never runs blocks every merge, with no "
                f"red to revert — this is the one unsafe move in this lane. "
                f"If the context was deliberately renamed or retired, update "
                f"REQUIRED_CONTEXTS and the branch protection TOGETHER.")
            continue
        if not j.get("runs-on"):
            failures.append(f"DEADLOCK: required context `{c}` has no `runs-on:`.")
            continue
        # (v0.72 cold review, F3) A rename was caught; GATING THE JOB OFF was
        # not — and a required context that never REPORTS is the same deadlock
        # as one that does not exist, reached by a one-line `if:` instead of a
        # rename. Demonstrated: adding
        # `if: github.event_name == 'schedule'` to `Kani Verification` left
        # this guard at rc=0 with 0 failures. No required job carries an `if:`
        # today, so this is a latent class closed before it fires.
        if j.get("if") is not None:
            failures.append(
                f"DEADLOCK: required context `{c}` carries an `if:` "
                f"({j['if']!r}). A required NAME that is conditionally skipped "
                f"never reports, and a never-reporting required context blocks "
                f"every merge with no red to revert. Remove the condition, or "
                f"retire the context from branch protection FIRST.")
            continue
        if pool_of(j.get("runs-on")) == EXACT_LABEL:
            on_hosted += 1
    print(f"ci-pool: {len(REQUIRED_CONTEXTS)} required contexts (pinned), "
          f"{on_hosted} on {EXACT_LABEL}, "
          f"{len(REQUIRED_CONTEXTS) - on_hosted} elsewhere")

    # ---- and the API as a CROSS-CHECK, never as the source -----------------
    if not args.offline:
        live = live_required_contexts(args.repo)
        if live is None:
            print("ci-pool: live required-context list UNAVAILABLE (no gh, no "
                  "network, or no token) — the pinned contract above still ran; "
                  "only the drift cross-check is skipped")
        elif sorted(live) != sorted(REQUIRED_CONTEXTS):
            failures.append(
                f"CONTRACT DRIFT: branch protection requires {sorted(live)} but "
                f"REQUIRED_CONTEXTS pins {sorted(REQUIRED_CONTEXTS)}. A context "
                f"appearing or vanishing is worth a visible diff, not a silent "
                f"adoption — reconcile them in one PR.")
        else:
            print("ci-pool: pinned required contexts match branch protection")

    for f in failures:
        print(f"FAIL {f}")
    print(f"ci-pool: {len(failures)} failure(s)")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
