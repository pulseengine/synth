#!/usr/bin/env python3
"""Runner-redundancy gate (RQ-62-CLAIMCHECK, #1062).

THE INVARIANT: a REQUIRED status context must not target a runner-label set
satisfiable by fewer than two ONLINE runners.

PROVENANCE — a live incident, not a hypothetical. On 2026-09-02 the `light`
pool had EXACTLY ONE runner (pulseengine-ci-01-8) and it went offline. Two
required contexts (`Format`, `Version Pin Sweep`) were routed there, were
assigned to a dead machine, sat 600s, and failed having executed ZERO steps.
Branch protection needs a required context to PASS; a dead pool cannot
produce one, so NOTHING IN THE REPO COULD MERGE. Every measurement in #1062
before that day asked "is this pool IDLE?" — and idle and unavailable are
indistinguishable in a utilisation reading. This gate asks the question none
of them asked: HOW MANY ONLINE MACHINES CAN SATISFY THIS LABEL SET?

WHAT IT CHECKS
  1. Structural (no token needed): every pinned REQUIRED context resolves to
     a job in the workflows. A renamed required job never reports its
     context and DEADLOCKS all merges — the same terminal state the
     redundancy invariant guards against, caught at the other end.
     (v0.90, RQ-90-SPECEXEC #1636) Resolution is ci_pool_tripwire's own
     `resolve_required_contexts`, over EVERY file under .github/workflows/
     by default (`spec-suite execution (#1636)` lives in spec-suite.yml),
     and the contract is ci_pool_tripwire's REQUIRED_CONTEXTS +
     PENDING_REQUIRED_CONTEXTS — imported, not a second hand-kept copy.
     The same rules apply: a `${{ }}` name, a matrix job or a reusable-
     workflow caller does not resolve, the workflow must run on
     `pull_request` without a path filter, and two workflows defining one
     context is AMBIGUOUS.
  2. Redundancy: for every required context whose job targets self-hosted
     labels, count ONLINE runners whose label set satisfies the job's
     `runs-on` set (case-insensitive superset, GitHub's own matching rule).
     Fewer than MIN_ONLINE (2) is a FAILURE. GitHub-hosted labels
     (ubuntu-*/macos-*/windows-*) are skipped: that pool's failure mode is
     quota, not label thinness.

ANTI-VACUITY
  * An empty runner inventory is a FAILURE, never a pass — an API error must
    not read as "no thin pools".
  * Fewer self-hosted required contexts examined than --min-selfhosted
    (default 1) is a FAILURE — a parse drift that maps nothing must not
    green the gate (the #1012/#1064 "validator that never did the work"
    class).

RUNNER INVENTORY SOURCE
  --runners-json FILE   fixture inventory (unit tests: potency replays run
                        in CI without any token).
  live (default)        `gh api /orgs/<org>/actions/runners --paginate`.
                        NOTE: the workflow GITHUB_TOKEN CANNOT read org
                        runners (org-admin scope), so live mode is for an
                        authenticated human / the release ritual, not a CI
                        step. CI runs the fixture potency tests
                        (scripts/test_runner_redundancy_check.py) instead;
                        run live mode before retargeting any required
                        context and at the release tail.

RED-FIRST, live and cheap: `--require-label podman` (any deliberately thin
label) evaluates a hypothetical required context targeting
{self-hosted, <label>} against the live inventory and must refuse.

Exit 0 iff every check passes.  # ci: fixtures wired in the Claim Check job.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

import yaml

# The required contexts. (v0.90, RQ-90-SPECEXEC #1636) This file used to keep
# its OWN copy of the nine, which went stale the day protection gained a
# tenth: the structural mode below read ci.yml only and would have reported the
# new context as a deadlock. The contract now has ONE home —
# ci_pool_tripwire.REQUIRED_CONTEXTS, which merge_gate.py already imports and
# whose drift cross-check compares it with live branch protection — and the
# pending ones are guarded here exactly as there.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import ci_pool_tripwire as _T  # noqa: E402

REQUIRED_CONTEXTS = list(_T.REQUIRED_CONTEXTS) + [
    c for c in _T.PENDING_REQUIRED_CONTEXTS if c not in _T.REQUIRED_CONTEXTS]

MIN_ONLINE = 2

HOSTED_PREFIXES = ("ubuntu-", "macos-", "windows-")


def load_workflows(paths) -> dict:
    """{path: parsed doc}: every workflow file by default, else the given ones."""
    if not paths:
        return _T.load_workflows()
    return {str(p): (yaml.safe_load(Path(p).read_text()) or {}) for p in paths}


def resolve_jobs(workflows: dict):
    """(context -> runs-on label list (lowercased), [failure]) for the contract.

    Delegates to ci_pool_tripwire.resolve_required_contexts, so this gate and
    the tripwire cannot disagree about what a context resolves to."""
    resolved, failures = _T.resolve_required_contexts(REQUIRED_CONTEXTS, workflows)
    jobs = {}
    for ctx, (_path, job) in resolved.items():
        runs_on = job.get("runs-on", [])
        if isinstance(runs_on, str):
            runs_on = [runs_on]
        jobs[ctx] = [str(label).lower() for label in runs_on]
    return jobs, failures


def is_hosted(labels: list[str]) -> bool:
    return any(l.startswith(HOSTED_PREFIXES) for l in labels)


def live_runners(org: str) -> list[dict]:
    """Fetch the org runner inventory via gh (needs org-runner read auth)."""
    proc = subprocess.run(
        ["gh", "api", f"/orgs/{org}/actions/runners", "--paginate",
         "--jq", ".runners[]"],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        sys.exit(
            "runner-redundancy: FAILED to fetch live runner inventory "
            f"(gh exit {proc.returncode}): {proc.stderr.strip()}\n"
            "Live mode needs a token with org self-hosted-runner read; "
            "use --runners-json for fixture mode."
        )
    runners = []
    decoder = json.JSONDecoder()
    buf = proc.stdout.strip()
    idx = 0
    while idx < len(buf):
        obj, end = decoder.raw_decode(buf, idx)
        runners.append(obj)
        idx = end
        while idx < len(buf) and buf[idx] in " \n\r\t":
            idx += 1
    return runners


def online_satisfying(runners: list[dict], want: list[str]) -> list[str]:
    """Names of ONLINE runners whose label set covers `want` (case-insens.)."""
    want_set = {w.lower() for w in want}
    out = []
    for r in runners:
        if r.get("status") != "online":
            continue
        have = {str(l.get("name", "")).lower() for l in r.get("labels", [])}
        if want_set <= have:
            out.append(r.get("name", "?"))
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--workflow", type=Path, action="append", default=[],
                    help="workflow file to resolve contexts in (repeatable); "
                         "default: every file under .github/workflows/")
    ap.add_argument("--runners-json", type=Path, default=None,
                    help="fixture: JSON file with {'runners': [...]} or a list")
    ap.add_argument("--org", default="pulseengine")
    ap.add_argument("--min-online", type=int, default=MIN_ONLINE)
    ap.add_argument("--min-selfhosted", type=int, default=1,
                    help="FAIL if fewer self-hosted required contexts were "
                         "examined (anti-vacuity floor)")
    ap.add_argument("--require-label", action="append", default=[],
                    metavar="LABEL",
                    help="ALSO evaluate a hypothetical required context "
                         "targeting {self-hosted, LABEL} — the red-first "
                         "probe for a deliberately thin label")
    ap.add_argument("--structural-only", action="store_true",
                    help="run ONLY the no-token structural check (every "
                         "required context exists as a job name — the "
                         "rename/deadlock class); the fleet redundancy "
                         "check needs live inventory and is skipped. This "
                         "is the CI mode; it must never be mistaken for "
                         "the redundancy verdict.")
    args = ap.parse_args()

    where = ", ".join(map(str, args.workflow)) or ".github/workflows/*"
    if args.structural_only:
        jobs, res_failures = resolve_jobs(load_workflows(args.workflow))
        for f in res_failures:
            print(f"FAIL  {f} (resolved in {where}) — a context that never "
                  "reports DEADLOCKS all merges")
        print(f"runner-redundancy(structural): {len(REQUIRED_CONTEXTS)} "
              f"required contexts, {len(jobs)} "
              f"matched to jobs, {len(res_failures)} failures "
              "(fleet redundancy NOT checked in this mode — run live)")
        return 1 if res_failures else 0

    if args.runners_json is not None:
        raw = json.loads(args.runners_json.read_text())
        runners = raw["runners"] if isinstance(raw, dict) else raw
    else:
        runners = live_runners(args.org)

    if not runners:
        print("runner-redundancy: FAIL — runner inventory is EMPTY; an API "
              "error or empty fleet must not read as 'no thin pools'.")
        return 1

    jobs, res_failures = resolve_jobs(load_workflows(args.workflow))

    failures = 0
    examined_selfhosted = 0

    # 1. structural: every required context reports from a real job.
    for f in res_failures:
        print(f"FAIL  {f} (resolved in {where}) — a context that never "
              "reports DEADLOCKS all merges")
        failures += 1

    # 2. redundancy per required context.
    targets: list[tuple[str, list[str]]] = [
        (ctx, jobs[ctx]) for ctx in REQUIRED_CONTEXTS if ctx in jobs
    ]
    for label in args.require_label:
        targets.append((f"<probe {label}>", ["self-hosted", label.lower()]))

    for ctx, labels in targets:
        if not labels:
            print(f"FAIL  {ctx}: job has no runs-on labels at all")
            failures += 1
            continue
        if is_hosted(labels):
            print(f"skip  {ctx}: GitHub-hosted ({', '.join(labels)})")
            continue
        examined_selfhosted += 1
        sat = online_satisfying(runners, labels)
        verdict = "ok  " if len(sat) >= args.min_online else "FAIL"
        if len(sat) < args.min_online:
            failures += 1
        print(f"{verdict}  {ctx}: [{', '.join(labels)}] satisfiable by "
              f"{len(sat)} online runner(s) "
              f"({', '.join(sat) if sat else 'NONE'}); need >= "
              f"{args.min_online}")

    if examined_selfhosted < args.min_selfhosted:
        print(f"runner-redundancy: FAIL — only {examined_selfhosted} "
              f"self-hosted required context(s) examined, floor is "
              f"{args.min_selfhosted}; a gate that checked nothing must not "
              "pass")
        failures += 1

    print(f"runner-redundancy: {len(REQUIRED_CONTEXTS)} required contexts, "
          f"{examined_selfhosted} self-hosted label-sets checked over "
          f"{len(runners)} inventoried runners, {failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
