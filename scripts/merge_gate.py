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
from pathlib import Path

ADVISORY = ("codecov", "advisory")


def sh(*args: str) -> str:
    return subprocess.run(args, capture_output=True, text=True).stdout.strip()


def is_advisory(name: str) -> bool:
    n = (name or "").lower()
    return any(k in n for k in ADVISORY)


# The required-context contract lives in ONE place. `ci_pool_tripwire` owns it
# (it is the module whose whole subject is the required set); importing it here
# is what stops a fifth copy from appearing. sys.path is extended because these
# scripts are invoked as files, not as a package.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from ci_pool_tripwire import REQUIRED_CONTEXTS  # noqa: E402


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

    Returns (verdict, diff_lines, behind) — where `behind` is a COMMIT
    count and is meaningful ONLY in the INDETERMINATE case; the two decided
    verdicts return 0 for it. An earlier docstring called the third value
    `advance_lines` and the code computed a diff of a commit against itself,
    which is always empty and was never returned. Named for what it is."""
    # (v0.73 cold review round 2, finding 4) `sh()` DISCARDS the return code,
    # so a `git diff` that fatals — "bad object", exactly what happens when the
    # squash commit is not in the local object store — yielded an empty string,
    # which read as 0 lines, which read as FAITHFUL. Demonstrated:
    # `git diff <fresh> <nonexistent-sha>` exits 128 and this returned
    # ("FAITHFUL", 0, 0). RQ-73-STEP8 claims the number exists WITHOUT a human
    # producing it, so a number produced by a failed command makes that claim
    # FALSE rather than merely untested.
    _proc = subprocess.run(["git", "diff", pr_head, merged],
                           capture_output=True, text=True)
    if _proc.returncode != 0:
        return ("DIFF UNAVAILABLE", -1, -1)
    diff_lines = len(_proc.stdout.strip().splitlines())
    current, behind = branch_currency(pr_head, base_at_merge)
    if not current:
        return ("INDETERMINATE", diff_lines, behind)
    if diff_lines == 0:
        return ("FAITHFUL", 0, 0)
    return ("SQUASH ALTERED CONTENT", diff_lines, 0)


def fidelity_exit(verdict: str) -> int:
    """verdict -> process exit code. (v0.74, RQ-74-GATEOFFLINE, #1269)

    Extracted from `main()` for the same reason `decide()` was extracted from
    `gate()`: it was the ONLY thing `merge_ritual.sh` consumes, and nothing
    could reach it offline. v0.73's round-2 gate review mutated
    `return 0 if verdict == "FAITHFUL" else 1` to `return 0` — deleting the
    mapping outright — and `--self-test` stayed GREEN, because `self_test()`
    never calls `main()`. That is round 1's F3 finding one level out: F3 gave
    the VERDICT a case and left the code that acts on it without one.

    Only FAITHFUL is a pass. INDETERMINATE is not: it means the branch was
    stale, so the diff contains main's advance and the number proves nothing.
    DIFF UNAVAILABLE is not either: it means `git diff` never ran.

    AND THE CALL SITE IS STILL UNTESTED (v0.74 cold review round 1). This
    function was extracted BECAUSE `merge_ritual.sh` consumes its exit code and
    nothing offline reached it — and the extraction gave the FUNCTION a case
    while leaving the CALL SITE without one. Mutating `return fidelity_exit(
    verdict)` to `return 0` in `main()` leaves `--self-test` green. The
    reviewer applied ten such mutations to `gate()` and `main()` — including
    forcing the whole rollup to SUCCESS, and `ok &= True` — and ALL TEN passed.
    `--self-test` reaches `decide()` and `fidelity_exit()` and nothing else.

    That is the same shape twice: v0.73 extracted `decide()` out of `gate()`,
    v0.74 extracted `fidelity_exit()` out of `main()`, and each moved the
    tested boundary one call outward without ever reaching the caller. A real
    fix drives `main()` itself against a recorded `gh` rollup; that is a v0.75
    candidate and is NOT claimed here.
    """
    return 0 if verdict == "FAITHFUL" else 1


def decide(roll: dict, required: list[str], current: bool, behind: int,
           base_agrees: bool):
    """The four checks, as a PURE function of the data (#1319).

    Split out from `gate()` so the decision can be driven OFFLINE. Until v0.73
    the whole thing went through `gh`, so CHECK1/2/3/3b were exercised only
    against the live API — v0.72's cold review injected nine mutants into this
    logic and FIVE survived `--self-test`, because the self-test could not reach
    it. A gate whose decision cannot be tested is a gate nobody has watched
    fail.
    """
    missing = [r for r in required if roll.get(r) != "SUCCESS"]
    red = [n for n, s in roll.items()
           if s in ("FAILURE", "ERROR") and not is_advisory(n)]
    pend = [n for n, s in roll.items() if s == "PENDING" and not is_advisory(n)]
    return {
        # (v0.72 cold review, F5) The literal `9` was a FOURTH hand-written
        # copy of a contract that already exists in
        # `ci_pool_tripwire.REQUIRED_CONTEXTS`. Demonstrated failure: with TEN
        # required contexts, ALL SUCCESS, this returned GATEFAIL and `missing`
        # was EMPTY — refusing a correct merge while naming nothing. The count
        # is now DERIVED from the pinned contract, which is the repo's own
        # "derive what you check against from the artifact you ship" rule
        # applied to the one place that had four copies of it.
        # (v0.73 RQ-73-GATETRUTH, #1319) BY NAME, not by count. v0.72 replaced
        # a hand-written `9` with `len(REQUIRED_CONTEXTS)` and called it
        # derived — but a COUNT is not a CONTRACT. Demonstrated failure, and it
        # is the one that matters: a rollup of nine contexts named `Bogus 0..8`,
        # all SUCCESS and none of them one of the nine REAL required names,
        # returned CHECK1=True and GATEOK. The gate would have merged on a
        # green wall of checks that gate nothing.
        #
        # The empty case is guarded separately because `set() == set()` is True
        # and `not missing` is True over an empty list: with the contract empty
        # this check passed while asserting NOTHING, which is the same shape one
        # level down.
        "CHECK1": (bool(REQUIRED_CONTEXTS)
                   and set(required) == set(REQUIRED_CONTEXTS)
                   and not missing,
                   {"missing": missing,
                    "not_in_contract": sorted(set(required) - set(REQUIRED_CONTEXTS)),
                    "absent_from_api": sorted(set(REQUIRED_CONTEXTS) - set(required)),
                    "contract_size": len(REQUIRED_CONTEXTS)}),
        # #1269a: the BRANCH must be current. `baseRefOid` agreement is reported
        # beside it, deliberately NOT as the check — it is what was mistaken for
        # this one.
        "CHECK2": (current, {"behind": behind,
                             "baseRefOid_agrees": base_agrees}),
        "CHECK3": (not red, red),
        "CHECK3b": (not pend, pend),
    }


def gate(pr: str, repo: str, required: list[str]):
    """Fetch the PR's live state and hand it to `decide`."""
    d = json.loads(sh("gh", "pr", "view", pr, "--repo", repo,
                      "--json", "statusCheckRollup,baseRefOid,headRefOid"))
    roll = {(c.get("name") or c.get("context")):
            (c.get("conclusion") or c.get("state") or "PENDING")
            for c in d["statusCheckRollup"]}
    current, behind = branch_currency(d["headRefOid"])
    base_agrees = d["baseRefOid"].startswith(sh("git", "rev-parse", "origin/main")[:8])
    return decide(roll, required, current, behind, base_agrees)


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

            # (v0.73 cold review, gate finding F3) The verdict that DETECTS the
            # defect #1269 ask 2 is about had no case at all: both calls above
            # pass `(x, x, base)`, so `diff_lines` is always 0 and the
            # SQUASH-ALTERED branch is unreachable from the fixture. Replacing
            # `if diff_lines == 0:` with `if True:` — deleting the detection
            # outright — left `--self-test` green. `merge_ritual.sh` calls this
            # after every merge, so the untested branch is the live one.
            g("checkout", "-q", "-b", "altered", base1)
            with open(os.path.join(td, "altered.txt"), "w") as fh:
                fh.write("content the squash did not preserve\n")
            g("add", "altered.txt")
            g("commit", "-q", "-m", "altered")
            altered = g("rev-parse", "HEAD")
            verdict3, d3, _ = squash_fidelity(fresh, altered, base1)
            check("fidelity: current branch with a NONZERO diff is SQUASH ALTERED",
                  verdict3 == "SQUASH ALTERED CONTENT" and d3 > 0,
                  f"verdict={verdict3} diff={d3}")
            check("fixture shape: base0 != base1 (the fixture really advanced)",
                  base0 != base1)
        finally:
            os.chdir(cwd)

    # ---- RQ-73-GATETRUTH (#1319): the decision, driven OFFLINE ------------
    # These are the demonstrations the artifact requires. Each names the exact
    # scenario v0.72's cold review executed, so the fix is verified in the
    # direction that FAILS and not only the one that passes.
    real = list(REQUIRED_CONTEXTS)
    green = {n: "SUCCESS" for n in real}

    r = decide(green, real, True, 0, True)
    check("CHECK1: the nine real contexts, all SUCCESS -> pass",
          r["CHECK1"][0], r["CHECK1"][1])

    # THE ONE THAT MATTERS. Nine contexts, all SUCCESS, none of them real.
    # Under the v0.72 count-based check this returned True and GATEOK.
    bogus_names = [f"Bogus {i}" for i in range(len(real))]
    bogus = {n: "SUCCESS" for n in bogus_names}
    r = decide(bogus, bogus_names, True, 0, True)
    check("CHECK1: nine BOGUS contexts, all SUCCESS -> REFUSED (was GATEOK)",
          not r["CHECK1"][0],
          f"detail={r['CHECK1'][1]}")

    # One real name swapped out: the count still matches, the contract does not.
    swapped = real[:-1] + ["Bogus tail"]
    r = decide({n: "SUCCESS" for n in swapped}, swapped, True, 0, True)
    check("CHECK1: one real context swapped for a fake -> REFUSED",
          not r["CHECK1"][0], f"detail={r['CHECK1'][1]}")

    # A real context missing from the API side, count short.
    short = real[:-1]
    r = decide({n: "SUCCESS" for n in short}, short, True, 0, True)
    check("CHECK1: a required context absent from the API -> REFUSED",
          not r["CHECK1"][0], f"detail={r['CHECK1'][1]}")

    # A context that NEVER REPORTED. (v0.74, RQ-74-GATEOFFLINE, #1269)
    #
    # Distinct from the case above, and nothing reached it. There, `required`
    # is short too, so the contract set-comparison fails and CHECK1 reds before
    # `missing` is ever consulted. Here the contract is INTACT and the ROLLUP is
    # empty — the shape where a required check was retargeted or renamed and now
    # never runs, which is the deadlock `ci_pool_tripwire`'s guard exists to
    # prevent and which no merge can ever clear.
    #
    # Demonstrated: mutating `roll.get(r)` to `roll.get(r, "SUCCESS")` — so an
    # ABSENT context reads as passing — left `--self-test` green and made
    # `decide({}, list(REQUIRED_CONTEXTS), True, 0, True)` return CHECK1=True on
    # an EMPTY rollup. The code was right; the test could not see it.
    r = decide({}, real, True, 0, True)
    check("CHECK1: the full contract with an EMPTY rollup -> REFUSED",
          not r["CHECK1"][0], f"detail={r['CHECK1'][1]}")

    r = decide({n: "SUCCESS" for n in real[:-1]}, real, True, 0, True)
    check("CHECK1: one required context never reported -> REFUSED",
          not r["CHECK1"][0], f"detail={r['CHECK1'][1]}")

    # THE EXIT MAPPING. (v0.74, RQ-74-GATEOFFLINE, #1269) `merge_ritual.sh`
    # consumes the exit code and nothing else, and until v0.74 no offline case
    # reached it — `return 0` passed the whole suite.
    check("fidelity exit: FAITHFUL -> 0",
          fidelity_exit("FAITHFUL") == 0, f"got {fidelity_exit('FAITHFUL')}")
    for bad in ("SQUASH ALTERED CONTENT", "INDETERMINATE", "DIFF UNAVAILABLE"):
        check(f"fidelity exit: {bad} -> non-zero",
              fidelity_exit(bad) != 0, f"got {fidelity_exit(bad)}")

    # THE EMPTY CONTRACT. `set() == set()` and `not []` are both True, so
    # without the explicit guard this passed while asserting nothing.
    _saved = list(REQUIRED_CONTEXTS)
    try:
        REQUIRED_CONTEXTS.clear()
        r = decide({}, [], True, 0, True)
        check("CHECK1: an EMPTY contract -> REFUSED (was a silent pass)",
              not r["CHECK1"][0], f"detail={r['CHECK1'][1]}")
    finally:
        REQUIRED_CONTEXTS.extend(_saved)
    check("fixture shape: the contract was restored after the empty-case test",
          list(REQUIRED_CONTEXTS) == _saved and len(REQUIRED_CONTEXTS) > 0)

    # CHECK3/3b still discriminate, and advisory names are still excluded.
    r = decide(dict(green, **{"Some Job": "FAILURE"}), real, True, 0, True)
    check("CHECK3: a non-advisory FAILURE -> REFUSED", not r["CHECK3"][0])
    r = decide(dict(green, **{"Rivet Federated Graph (advisory)": "FAILURE"}),
               real, True, 0, True)
    check("CHECK3: an ADVISORY failure does NOT refuse", r["CHECK3"][0])
    r = decide(dict(green, **{"Some Job": "PENDING"}), real, True, 0, True)
    check("CHECK3b: a non-advisory PENDING -> REFUSED", not r["CHECK3b"][0])

    print(f"merge-gate-self-test: {len(fails)} failure(s)")
    return 1 if fails else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--pr")
    ap.add_argument("--squash-fidelity", action="store_true",
                    help="post-merge: record whether the squash altered "
                         "content (#1269 ask 2). Requires --pr.")
    ap.add_argument("--repo", default="pulseengine/synth")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if not args.pr:
        ap.error("--pr is required unless --self-test")

    if args.squash_fidelity:
        d = json.loads(sh("gh", "pr", "view", args.pr, "--repo", args.repo,
                          "--json", "headRefOid,baseRefOid,mergeCommit,state"))
        if d["state"] != "MERGED":
            print(f"squash-fidelity: #{args.pr} is {d['state']}, not MERGED — "
                  f"nothing to attest")
            return 1
        # The branch is deleted by `--delete-branch`; the PULL ref is not.
        sh("git", "fetch", "-q", "origin", f"refs/pull/{args.pr}/head")
        head = d["headRefOid"]
        merged = d["mergeCommit"]["oid"]
        verdict, lines, behind = squash_fidelity(head, merged, d["baseRefOid"])
        print(f"squash-fidelity #{args.pr}: {verdict} "
              f"(diff_lines={lines}, behind={behind}, "
              f"head={head[:8]}, merged={merged[:8]})")
        # INDETERMINATE is not a pass. It means the branch was stale, so the
        # diff contains main's advance and the number proves nothing — the
        # condition that silently held for 45 merges before #1268.
        return fidelity_exit(verdict)

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
