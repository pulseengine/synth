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


class CommandFailed(Exception):
    """A subprocess this gate's verdict depends on did not succeed.

    RQ-81-SHEXIT (#1474). It is an EXCEPTION and not a return value on purpose:
    the old helper returned `""` on failure, which is indistinguishable from a
    command that succeeded with no output, and every caller then read that empty
    string as data. A raise cannot be ignored by accident.
    """


def sh(*args: str) -> str:
    """stdout of `args`, RAISING CommandFailed on a non-zero exit.

    RQ-81-SHEXIT (#1474). This used to be
    `subprocess.run(...).stdout.strip()` with no returncode read at all — the
    "checker succeeds about work it never did" class. The v0.73 cold review
    found it, fixed it in `squash_fidelity` ALONE (which calls subprocess
    directly and refuses on rc != 0, with a comment naming the incident), and
    left the other call sites. That is the twin-check shape: the narrowing was
    applied to the instance, not to the class.

    MEASURED before the fix, both failure modes on real commands:

      branch_currency("d"*40) -> behind == 0 although `git rev-list` exited 128
        with `fatal: Invalid revision range`. `behind` is the number the
        stale-base check is about, and the condition that held silently for 45
        merges before #1268.

      `d["baseRefOid"].startswith(sh("git","rev-parse","origin/main")[:8])`
        -> True UNCONDITIONALLY when rev-parse fails, because `""[:8]` is `""`
        and `str.startswith("")` is always True. A reported value that cannot
        be False.

    Use `sh_unchecked` only where a failure genuinely is not evidence, and say
    why at the call site.
    """
    r = subprocess.run(args, capture_output=True, text=True)
    if r.returncode != 0:
        raise CommandFailed(
            f"{' '.join(args)} -> exit {r.returncode}: "
            f"{(r.stderr or r.stdout).strip()[:200]}")
    return r.stdout.strip()


def sh_unchecked(*args: str) -> str:
    """stdout, exit code DELIBERATELY ignored.

    Exists so that tolerating a failure is a VISIBLE choice at the call site
    rather than the default for everything. Nothing uses it today; it is here so
    that the next person who needs it does not reach for the unchecked default.
    """
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
    # RQ-81-SHEXIT (#1474): this was `int(behind_out or "0")`, the SECOND HALF
    # of the same swallow — with a raising `sh()` the failure path no longer
    # reaches here, but `or "0"` would still turn "the command printed nothing"
    # into the reassuring number. `rev-list --count` prints a count on every
    # success, so empty output is not a zero count; it is an unanswered
    # question, and the gate says so rather than defaulting.
    if not behind_out.strip():
        raise CommandFailed(
            f"git rev-list --count {head}..{base_ref} succeeded but printed "
            f"NOTHING. A count is not optional output, so this is an unanswered "
            f"question and not a count of zero")
    behind = int(behind_out)
    # DELIBERATELY TOLERANT, and the only such site in this file: a non-zero
    # exit from `merge-base --is-ancestor` is its ANSWER ("not an ancestor"),
    # not a failure, so this one reads `returncode` instead of calling `sh`.
    # It is safe here only because the `rev-list` above names the same two refs
    # and has already raised on a ref git cannot resolve.
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

    THE CALL SITE IS NOW TESTED, and this paragraph used to deny it — a false
    statement about this tree, found by v0.77's round-1 gate review. What was
    true when it was written: this function was extracted BECAUSE
    `merge_ritual.sh` consumes its exit code and nothing offline reached it, and
    the extraction gave the FUNCTION a case while leaving the CALL SITE without
    one. Mutating `return fidelity_exit(verdict)` to `return 0` in `main()`
    still leaves `--self-test` green — that clause remains accurate. What is NO
    LONGER true is the conclusion drawn from it: v0.75 delivered
    `scripts/test_merge_gate_callsite.py`, it is CI-wired at `ci.yml:472` in the
    required `Claim Check` job, and it REDS on exactly that mutation with three
    failures. Read the state of a gap before describing it. The
    reviewer applied ten such mutations to `gate()` and `main()` — including
    forcing the whole rollup to SUCCESS, and `ok &= True` — and ALL TEN passed.
    `--self-test` does not reach `gate()` or `main()` AT ALL — which is the
    point. (An earlier wording said it "reaches `decide()` and `fidelity_exit()`
    and nothing else"; round 2 refuted that by walking the AST: it also drives
    `branch_currency`, `squash_fidelity` and `is_advisory`, whose potency this
    very docstring records.)

    That is the same shape twice: v0.73 extracted `decide()` out of `gate()`,
    v0.74 extracted `fidelity_exit()` out of `main()`, and each moved the
    tested boundary one call outward without ever reaching the caller. The real
    fix — driving `main()` itself against a recorded `gh` rollup — SHIPPED in
    v0.75 and is what closed this.

    THE SHAPE RECURRED ANYWAY, one level in: v0.77 added the `GateRefusal`
    branch to the already-covered `main()` and did not extend that driver, so
    the new branch shipped uncovered while every instrument stayed green. Round
    1 caught it and the driver now carries four refusal cases. Adding a branch
    to a tested function is not inheriting its coverage.
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


class GateRefusal(Exception):
    """The gate cannot JUDGE — distinct from judging and saying no.

    RQ-77-SUBJECT (#1418). A refusal exits 2 and never prints GATEOK, because a
    caller must be able to tell "the gate ran and the answer is no" from "the
    gate could not tell what it was being asked about". v0.76's RQ-76-CLOSUREMAIN
    drew the same distinction in `issue_closure_check` for the same reason.
    """


def subject_refusal(n_non_advisory: int, head: str, expect_head: str | None):
    """Is the gate about to judge the WRONG SUBJECT? Pure, so the self-test
    covers it with no network.

    RQ-77-SUBJECT (#1418). Two ways this gate could return a TRUE verdict about
    something other than the thing it was asked about, both measured in v0.76:

    1. AN EMPTY ROLLUP IS NOT A VERDICT. Right after a push, `gh pr view` can
       return zero checks. Every derived count is then 0 — no reds, nothing
       pending — and the arithmetic below is about the empty set. CHECK1 does
       catch this today by reporting all nine required contexts missing, so it
       has never merged anything wrongly; but "9 missing" reads as a verdict
       about the PR when it is really "nothing has registered yet", and relying
       on a downstream check to notice is the shape this release is named for.
       Observed live on #1407 at the v0.75 cut: "TERMINAL: 0 non-adv".

    2. A ROLLUP CAN BELONG TO THE PREVIOUS HEAD. After a force-push GitHub keeps
       serving the old head's checks — and the dangerous case is not an empty
       set but a COMPLETE GREEN one, which sails through any emptiness guard.
       Measured on #1410 in v0.76: the PR object still reported head 272e78b1
       with 72 green contexts while `check-runs` for the pushed SHA c84de062
       returned total_count 0.

       CHECK2 already catches the common form, and that is worth stating so this
       refusal is not oversold: a stale PRE-REBASE head LACKS main's advance, so
       `behind > 0` and CHECK2 reds. What it does NOT catch is an amend-shaped
       force-push where old and new heads share a merge-base — both are
       `behind == 0`, every check passes on the old head's CI, and `gh pr merge`
       merges the new content. `--expect-head` closes exactly that gap, and only
       when the caller supplies the SHA it pushed; absent it, this returns None
       and nothing changes.

    Returns a reason string, or None when the subject is sound.
    """
    if n_non_advisory == 0:
        return ("the rollup holds ZERO non-advisory checks. That is not a green "
                "PR, it is a PR whose checks have not registered — every count "
                "below would be about the empty set. Re-run once CI appears")
    # AN EXPECTATION THAT DERIVED TO NOTHING IS A REFUSAL, NOT A SKIPPED CHECK.
    # Added by v0.77's round-1 gate review. `expect_head is None` means the
    # caller did not ask — that stays a no-op, and a self-test assertion pins it.
    # But an EMPTY STRING means the caller DID ask and its derivation produced
    # nothing: `merge_ritual.sh` computes it with `EXPECT=$(git rev-parse
    # "origin/$HEADREF")` under `set -uo pipefail` WITHOUT `-e`, so a git that
    # fails at the repo level (the Xcode-license shape this environment has hit)
    # leaves EXPECT="" and execution continues. The old `if expect_head` then
    # silently disabled the subject check and printed GATEOK with no diagnostic
    # — a green about a subject nobody verified, which is this gate's own
    # subject. Whitespace is stripped because " " is the same empty derivation
    # wearing a character.
    # AND THE SAME RULE FOR THE OTHER INPUT. Round 2 found this guard asymmetric:
    # `expect_head.startswith(head)` is True for ANY empty `head`, so an empty
    # `headRefOid` still disabled the subject check silently. Lower risk than the
    # expectation side (it comes from the API, not a local `$( )` capture) but the
    # same class, and "a derived population of zero is a refusal" does not hold for
    # one of two inputs only.
    if not (head or "").strip():
        return ("the PR's head came back EMPTY, so there is no subject to judge "
                "against. That is a refusal, not a check to skip: every comparison "
                "below would be against the empty string, which any expectation "
                "prefix-matches")
    if expect_head is not None and not expect_head.strip():
        return ("this gate was asked about a head, but the expectation derived "
                "to the EMPTY STRING — so the subject check would be silently "
                "skipped and the verdict would be about an unverified head. "
                "That is a refusal, not a no-op: check how --expect-head was "
                "computed (a failed `git rev-parse` still exits into an empty "
                "capture)")
    if expect_head and not (head.startswith(expect_head)
                            or expect_head.startswith(head)):
        return (f"the PR's head is {head[:12]} but this gate was asked about "
                f"{expect_head[:12]}. After a force-push the rollup can still "
                f"serve the PREVIOUS head's complete green set, so a verdict "
                f"here would be true about the wrong commit")
    return None


def gate(pr: str, repo: str, required: list[str], expect_head: str | None = None):
    """Fetch the PR's live state and hand it to `decide`.

    The rollup and `headRefOid` come from ONE query on purpose: fetched
    separately they can skew, and the verdict would then be about a rollup and a
    head that were never simultaneously true.
    """
    d = json.loads(sh("gh", "pr", "view", pr, "--repo", repo,
                      "--json", "statusCheckRollup,baseRefOid,headRefOid"))
    roll = {(c.get("name") or c.get("context")):
            (c.get("conclusion") or c.get("state") or "PENDING")
            for c in d["statusCheckRollup"]}
    n_non_adv = sum(1 for k in roll if not is_advisory(k))
    why = subject_refusal(n_non_adv, d["headRefOid"], expect_head)
    if why:
        raise GateRefusal(why)
    current, behind = branch_currency(d["headRefOid"])
    # RQ-81-SHEXIT (#1474): was `.startswith(sh(...)[:8])`. With rev-parse
    # failing, `""[:8]` is `""` and `str.startswith("")` is ALWAYS True, so this
    # reported value could not be False. Both sides are full 40-char shas — gh
    # returns `baseRefOid` in full and `rev-parse` prints in full — so equality
    # is the honest comparison and there is nothing for an empty string to
    # satisfy. A failing rev-parse now raises instead of returning "".
    base_agrees = d["baseRefOid"] == sh("git", "rev-parse", "origin/main")
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

            # ---- RQ-81-SHEXIT (#1474): a FATAL git command must REFUSE ----
            #
            # The scenario the self-test could not reach: a git command this
            # gate's verdict depends on FAILS. Nothing here is mocked — `git
            # rev-list --count <nonexistent>..main` really exits 128 with
            # `fatal: Invalid revision range`, in this fixture, on this machine.
            #
            # RED-FIRST, measured against the PRE-FIX code at e995ac5c, in this
            # same fixture:
            #
            #   branch_currency(missing, base1) -> (False, 0)
            #
            # A VERDICT. Not an error — a tuple the caller reads as data, whose
            # `behind == 0` is the "not stale" answer, produced by a command
            # that computed nothing. The `current=False` came from
            # `merge-base --is-ancestor` (whose rc IS checked), so the two
            # halves disagreed about whether anything had been measured and only
            # the checked half said so. Had the ancestry call been the one to
            # fail, the pair would have read (True, 0): CURRENT and NOT BEHIND,
            # from two failed commands.
            missing = "d" * 40

            # FIRST, the HELPER'S OWN CONTRACT, asserted AT the helper.
            #
            # This assertion exists because of something measured while writing
            # the two below it: `branch_currency` now ALSO refuses on empty
            # output, so a `CommandFailed` out of `branch_currency` is no longer
            # attributable to `sh()` — either layer produces it. Two guards over
            # one input make a downstream assertion non-discriminating, which is
            # this release's own theme one level in. So the exit-code contract is
            # pinned where only `sh()` can satisfy it, with the paired control
            # directly beside it.
            helper_raised = None
            try:
                sh("git", "rev-list", "--count", f"{missing}..main")
            except CommandFailed as why:
                helper_raised = str(why)
            check("SHEXIT: sh() ITSELF raises on a non-zero exit (pre-fix: returned '')",
                  helper_raised is not None and "128" in helper_raised,
                  f"helper_raised={helper_raised!r}")

            raised = None
            try:
                verdict_from_a_failed_command = branch_currency(missing, base1)
            except CommandFailed as why:
                raised = str(why)
            check("SHEXIT: a FATAL git command REFUSES instead of returning a verdict",
                  raised is not None,
                  f"returned {verdict_from_a_failed_command!r} from a command that exited 128"
                  if raised is None else "")
            check("SHEXIT: the refusal CARRIES the exit code and git's own stderr",
                  raised is not None and "128" in raised and "fatal" in raised.lower(),
                  f"raised={raised!r}")

            # THE PAIRED CONTROL. Without it, the assertion above is satisfied
            # by an `sh()` that raises on EVERYTHING — including success — which
            # would red the gate on every real PR. So: the same helper, the same
            # fixture, a command that SUCCEEDS.
            check("SHEXIT control: sh() on a SUCCEEDING command still returns stdout",
                  sh("git", "rev-parse", "HEAD") == fresh
                  or sh("git", "rev-parse", "HEAD") == g("rev-parse", "HEAD"),
                  "a helper that raises on success is not a fix, it is an outage")
            # And the deliberate escape hatch is still an escape hatch: silent,
            # empty, no raise. Asserted so that `sh_unchecked` cannot quietly
            # become a second checked helper and leave the next author with no
            # tolerant option at all.
            check("SHEXIT control: sh_unchecked TOLERATES the same failure, silently",
                  sh_unchecked("git", "rev-list", "--count", f"{missing}..main") == "")
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

    # ---- RQ-77-SUBJECT (#1418): the gate must REFUSE a wrong subject -----
    #
    # These are pure and need no repository, which is the point: the failures
    # they guard are about WHICH rollup and WHICH head the verdict describes,
    # and that question is answerable without any network.
    check("SUBJECT: an EMPTY rollup REFUSES rather than reading as green",
          (subject_refusal(0, "aaaaaaaa", None) or "").startswith("the rollup holds ZERO"),
          str(subject_refusal(0, "aaaaaaaa", None)))
    check("SUBJECT: a populated rollup with no expectation does NOT refuse",
          subject_refusal(9, "aaaaaaaa", None) is None,
          str(subject_refusal(9, "aaaaaaaa", None)))
    check("SUBJECT: a head that is not the one asked about REFUSES",
          "was asked about" in (subject_refusal(72, "272e78b1c0de", "c84de062") or ""),
          str(subject_refusal(72, "272e78b1c0de", "c84de062")))
    check("SUBJECT: the head the caller asked about does NOT refuse",
          subject_refusal(72, "c84de062aaaa", "c84de062") is None,
          str(subject_refusal(72, "c84de062aaaa", "c84de062")))
    check("SUBJECT: a SHORT expectation matches a full head (prefix, either way)",
          subject_refusal(72, "c84de062", "c84de062aaaa") is None,
          str(subject_refusal(72, "c84de062", "c84de062aaaa")))
    # The dangerous shape is a FULL GREEN rollup belonging to the previous head.
    # Emptiness guards cannot see it, which is why the head check is separate
    # from the population check rather than folded into one predicate.
    check("SUBJECT: an EMPTY head REFUSES too (round 2: the guard was asymmetric)",
          subject_refusal(72, "", "abcdef1234") is not None)
    check("SUBJECT: a WHITESPACE head REFUSES",
          subject_refusal(72, "   ", "abcdef1234") is not None)
    check("SUBJECT: an EMPTY expectation REFUSES rather than skipping the check",
          subject_refusal(72, "a" * 40, "") is not None)
    check("SUBJECT: a WHITESPACE expectation REFUSES too",
          subject_refusal(72, "a" * 40, "   ") is not None)
    check("SUBJECT: expect_head=None is still a NO-OP (the caller did not ask)",
          subject_refusal(72, "a" * 40, None) is None)
    check("RQ-77-SUBJECT: a COMPLETE green rollup on the wrong head still REFUSES",
          subject_refusal(72, "oldoldold", "newnewnew") is not None,
          "a full population must not excuse a wrong subject")

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
    ap.add_argument("--expect-head", default=None,
                    help="RQ-77-SUBJECT (#1418): the head SHA this gate is "
                         "being asked about. A mismatch REFUSES (exit 2) "
                         "instead of judging the previous head's rollup.")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if not args.pr:
        ap.error("--pr is required unless --self-test")

    # (v0.81 round-1 cold review, finding 10.) THE TRY STARTS HERE, not at the
    # `gate()` call. RQ-81-SHEXIT made `sh()` raise, and three of its call sites
    # in this function sat OUTSIDE the handler: the two below and the
    # required-contexts read further down. Measured: `--pr 1 --repo
    # pulseengine/nonexistent-xyz-zz` produced an UNCAUGHT CommandFailed
    # traceback at **rc=1** with no `GATEREFUSED` printed.
    #
    # rc=1 is GATEFAIL's code — "the answer is no". So the fix changed the
    # failure's SHAPE without extending the classification, and a caller could
    # not tell "the answer is no" from "the gate could not tell", which is
    # exactly the distinction `GateRefusal`'s own docstring exists to preserve.
    # A legitimate non-zero verdict (`fidelity_exit`, GATEFAIL) is NOT a refusal
    # and still returns its own code: only the two exception types are converted.
    try:
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
        res = gate(args.pr, args.repo, required, args.expect_head)
    except (GateRefusal, CommandFailed) as why:
        # Exit 2, and NEVER GATEOK: `merge_ritual.sh` gates the merge on the
        # literal string GATEOK, so a refusal must not print it even by accident.
        print(f"GATEREFUSED {why}")
        return 2
    ok = True
    for k, (passed, detail) in res.items():
        print(f"{k}={passed} {detail}")
        ok &= passed
    print("GATEOK" if ok else "GATEFAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
