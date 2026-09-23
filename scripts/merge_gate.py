#!/usr/bin/env python3
"""RQ-72-RITUAL (#1269): the merge ritual's DECIDABLE half, as testable code.

WHY THIS EXISTS AT ALL
----------------------
The four-check merge ritual and the tag ritual gate every merge and every tag in
this repository, and until v0.72 they lived in a session scratchpad. Measured on
`87fb06d7`: `git grep -lIE 'merge --squash' -- scripts .github` returned NOTHING,
and `git grep -lIE 'CHECK3b|four-check|baseRefOid'` returned only artifact prose
and cold reviews. The scripts had already been lost once with a deleted volume
and rebuilt from memory — and the rebuild is what introduced the squash-subject
defect that reddened main during v0.71.

WHAT #1269 NAMED, AND WHY BOTH ARE HERE
---------------------------------------
(a) CHECK2 asserted `baseRefOid == origin/main`. That is the PR's recorded BASE
    BRANCH TIP, not the commit the branch forked from, so a branch cut from an
    old commit can carry a perfectly current `baseRefOid`. The check answered
    "is this PR pointed at today's main?" while every reader took it to mean
    "is this branch rebased onto today's main?". On #1268 it passed on a branch
    cut from the v0.66.0 tag, four dependabot commits behind.

(b) The step-8 attestation records `git diff <PR head> <merged commit>` and read
    0 for 45 consecutive merges, then 189 on #1268 — and the 189 was proven
    byte-identical to main's OWN advance. The metric answers "did the squash
    alter my content?" only when the branch is current; on a stale branch it
    silently becomes "how far did main move?", and the recorded number cannot
    tell you which question it answered.

Both are arithmetic over commit relationships, so both are unit-testable without
a network — which is the point. A committed script CI never runs is one more
hand-maintained artifact to drift; `--self-test` is what CI runs.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys

ADVISORY = ("codecov", "advisory")


def sh(*args: str) -> str:
    return subprocess.run(args, capture_output=True, text=True).stdout.strip()


def is_advisory(name: str) -> bool:
    n = (name or "").lower()
    return any(k in n for k in ADVISORY)


def branch_currency(head: str, base_ref: str = "origin/main"):
    """(#1269a) Is the BRANCH current, not merely POINTED at a current base?

    Returns (current, behind). `behind` is how many commits the base has that
    the head lacks; `current` is True only when that is zero, which is the
    question `baseRefOid` cannot answer."""
    behind_out = sh("git", "rev-list", "--count", f"{head}..{base_ref}")
    behind = int(behind_out or "0")
    anc = subprocess.run(["git", "merge-base", "--is-ancestor", base_ref, head],
                         capture_output=True)
    return (anc.returncode == 0 and behind == 0), behind


def squash_fidelity(pr_head: str, merged: str, base_at_merge: str):
    """(#1269b) Did the SQUASH alter my content — separated from main's advance.

    `git diff <head> <merged>` conflates the two. The disambiguation is the
    branch's own currency: when the branch was current, `base_at_merge` is an
    ancestor of the head and main contributed nothing, so a non-zero diff IS a
    squash infidelity. When it was stale, the diff contains main's advance and
    the number alone proves nothing — which is what it silently did for 45
    merges before #1268 made it visible.

    Returns (verdict, diff_lines, advance_lines)."""
    diff_lines = len(sh("git", "diff", pr_head, merged).splitlines())
    advance_lines = len(sh("git", "diff", base_at_merge, base_at_merge).splitlines())
    current, behind = branch_currency(pr_head, base_at_merge)
    if not current:
        return ("INDETERMINATE", diff_lines, behind)
    if diff_lines == 0:
        return ("FAITHFUL", 0, 0)
    return ("SQUASH ALTERED CONTENT", diff_lines, 0)


def gate(pr: str, repo: str, required: list[str]):
    """CHECK1/2/3/3b, with CHECK2 upgraded to the merge-base test."""
    d = json.loads(sh("gh", "pr", "view", pr, "--repo", repo,
                      "--json", "statusCheckRollup,baseRefOid,headRefOid"))
    roll = {(c.get("name") or c.get("context")):
            (c.get("conclusion") or c.get("state") or "PENDING")
            for c in d["statusCheckRollup"]}
    missing = [r for r in required if roll.get(r) != "SUCCESS"]
    red = [n for n, s in roll.items()
           if s in ("FAILURE", "ERROR") and not is_advisory(n)]
    pend = [n for n, s in roll.items() if s == "PENDING" and not is_advisory(n)]
    current, behind = branch_currency(d["headRefOid"])
    return {
        "CHECK1": (len(required) == 9 and not missing, missing),
        # #1269a: the BRANCH must be current. `baseRefOid` agreement is reported
        # beside it, deliberately NOT as the check — it is what was mistaken for
        # this one.
        "CHECK2": (current, {"behind": behind,
                             "baseRefOid_agrees":
                                 d["baseRefOid"].startswith(sh("git", "rev-parse",
                                                               "origin/main")[:8])}),
        "CHECK3": (not red, red),
        "CHECK3b": (not pend, pend),
    }


def self_test() -> int:
    """The arithmetic, offline and HERMETIC.

    An earlier version ran these against the AMBIENT repository — `HEAD`,
    `HEAD~1` — and passed locally while failing in CI, because a self-test that
    reads the repository's shape is not self-contained: a shallow checkout, or
    a `pull_request` merge commit, or a one-commit fixture gives different
    answers to the same assertion. Reproduced locally in a fresh single-commit
    repo, where `HEAD~1` does not exist and "one commit behind" measured 0.

    So it builds its own repository with a KNOWN shape. That is also what makes
    the assertions mean something: the scenarios are constructed, not whatever
    the working tree happened to look like.

    PROVEN POTENT by mutation, each against the failure mode it exists for:

        currency always returns CURRENT (#1269a's mode)   -> 2 assertions red
        fidelity never returns INDETERMINATE (#1269b's)   -> 1 assertion  red
        the advisory classifier matches nothing           -> 3 assertions red

    AND ONE THING IT DOES NOT COVER, stated rather than implied: dropping the
    `and behind == 0` clause from `branch_currency` changes nothing here,
    because in this fixture `base1` genuinely is not an ancestor of `feat`, so
    `merge-base --is-ancestor` already rejects it. That clause is redundancy
    for the case where the base IS an ancestor but the branch still lags —
    which this fixture does not construct. A reader should not take the
    mutation results above as covering it."""
    import os
    import tempfile

    fails = []

    def check(name, cond, detail=""):
        print(f"  {'ok  ' if cond else 'FAIL'} {name}"
              + (f" — {detail}" if not cond and detail else ""))
        if not cond:
            fails.append(name)

    # ---- the pure classifier, no repository needed -------------------------
    check("advisory: codecov is advisory", is_advisory("codecov/project"))
    check("advisory: a name containing 'advisory' is advisory",
          is_advisory("Rivet Federated Graph (advisory)"))
    check("advisory: a required context is NOT advisory", not is_advisory("Claim Check"))
    check("advisory: matching is case-insensitive", is_advisory("CODECOV/patch"))

    # ---- a fixture repo with a KNOWN shape ---------------------------------
    #
    #   base0 --- base1        <- "main" advanced by one commit
    #      \
    #       feat              <- branch cut from base0: STALE by one
    #
    cwd = os.getcwd()
    with tempfile.TemporaryDirectory() as td:
        def g(*a):
            return subprocess.run(["git", "-C", td, *a],
                                  capture_output=True, text=True).stdout.strip()
        g("init", "-q", "-b", "main")
        g("config", "user.email", "t@t"); g("config", "user.name", "t")
        g("commit", "-q", "--allow-empty", "-m", "base0")
        base0 = g("rev-parse", "HEAD")
        g("checkout", "-q", "-b", "feat")
        g("commit", "-q", "--allow-empty", "-m", "feat work")
        feat = g("rev-parse", "HEAD")
        g("checkout", "-q", "main")
        g("commit", "-q", "--allow-empty", "-m", "base1")
        base1 = g("rev-parse", "HEAD")
        # a branch cut from base1 — CURRENT
        g("checkout", "-q", "-b", "fresh")
        g("commit", "-q", "--allow-empty", "-m", "fresh work")
        fresh = g("rev-parse", "HEAD")

        os.chdir(td)
        try:
            cur, behind = branch_currency(fresh, base1)
            check("currency: a branch cut from the base is CURRENT",
                  cur and behind == 0, f"current={cur} behind={behind}")

            # #1269a — THE distinction. `feat` was cut from base0, so main has
            # one commit it lacks. The old CHECK2 could not see this, because a
            # PR on `feat` still records a current baseRefOid.
            cur2, behind2 = branch_currency(feat, base1)
            check("currency: a branch cut from an OLDER commit is STALE",
                  (not cur2) and behind2 == 1, f"current={cur2} behind={behind2}")

            # #1269b — a 0-line diff on a stale branch proves nothing.
            verdict, _d, _b = squash_fidelity(feat, feat, base1)
            check("fidelity: stale branch yields INDETERMINATE, not FAITHFUL",
                  verdict == "INDETERMINATE", f"verdict={verdict}")
            verdict2, d2, _ = squash_fidelity(fresh, fresh, base1)
            check("fidelity: current branch with a 0-line diff is FAITHFUL",
                  verdict2 == "FAITHFUL" and d2 == 0, f"verdict={verdict2} diff={d2}")
            check("fixture shape: base0 != base1 (the fixture really advanced)",
                  base0 != base1)
        finally:
            os.chdir(cwd)

    print(f"merge-gate-self-test: {len(fails)} failure(s)")
    return 1 if fails else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--pr")
    ap.add_argument("--repo", default="pulseengine/synth")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if not args.pr:
        ap.error("--pr is required unless --self-test")

    required = [l.strip() for l in sh(
        "gh", "api",
        f"repos/{args.repo}/branches/main/protection/required_status_checks/contexts",
        "--jq", ".[]").splitlines() if l.strip()]
    res = gate(args.pr, args.repo, required)
    ok = True
    for k, (passed, detail) in res.items():
        print(f"{k}={passed} {detail}")
        ok &= passed
    print("GATEOK" if ok else "GATEFAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
