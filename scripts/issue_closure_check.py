#!/usr/bin/env python3
"""RQ-71-ISSUESCOPE (#1250): the issues a release CLOSES must equal the set its
artifacts AUTHORISE.

WHY THIS EXISTS. Closing issues at the tag was, until this script, an unchecked
manual step. Three things were measured before it was written:

  1. No existing artifact field separated the close-set from the keep-open set.
     Comparing the field key sets of v0.70's five "close" artifacts against both
     "keep-open" ones, no field is present in all of one and none of the other,
     in either direction. The only signal was prose.
  2. `issue_dispositions.md`, named at the v0.70 cut as where the decision
     lives, has NEVER existed — `git log --all --diff-filter=A` matches nothing.
  3. `scripts/` contained no tag-time issue closer at all.

So nothing connected "this artifact is implemented" to "this issue must NOT be
closed". v0.69 auto-closed an external reporter's LIVE blocker from the
substring `close #N` inside a DENIAL, and nothing would have caught it.

WHAT IT CHECKS, in both directions:

  * CLOSED BUT NOT AUTHORISED — an issue went closed that no delivered artifact
    entitles the release to close. This is the v0.69 accident.
  * HELD OPEN BUT CLOSED — an artifact explicitly declared `issue-scope:
    outlives` and the issue was closed anyway. The named defect of this lane.
  * AUTHORISED BUT NOT CLOSED — the release delivered the artifact and left its
    issue open. Not dangerous, but it is how a board stops meaning anything, so
    it is reported (and downgraded to a warning with --allow-unclosed, because
    a closure can legitimately lag a tag by minutes).

The authorised set is NOT re-derived here. It is imported from
`status_evidence_check.authorised_close_set`, the same function whose census
line prints on every CI run — two derivations of one set is exactly how the
closed set and the authorised set drift apart.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from status_evidence_check import (  # noqa: E402
    authorised_close_set,
    load_release_artifacts,
)

RELEASE_GLOB = "artifacts/release-v*/*.yaml"


def parse_version(release: str) -> tuple[int, int]:
    """'v0.71' -> (0, 71). Raises on anything else, deliberately: a silently
    unparsed release would scope the check to nothing and pass vacuously."""
    txt = release.strip().lstrip("vV")
    parts = txt.split(".")
    if len(parts) < 2:
        raise ValueError(f"unparseable release {release!r} — want vMAJOR.MINOR")
    return (int(parts[0]), int(parts[1]))


def closed_since(tag: str, repo: str) -> set[int]:
    """Issues closed at or after `tag`'s creation, via gh. Network; only used
    on the live path, never in the tests.

    RESOLVE THE TAG NAME DIRECTLY. The first version of this walked
    `git/refs/tags/<tag>` and fed `.object.sha` to `commits/<sha>`, which is
    WRONG for an ANNOTATED tag: `.object.sha` is then the TAG OBJECT's sha, not
    the commit's, and the API answers

        422 No commit found for SHA: f414f078...

    Every synth release tag is annotated and unsigned by policy, so that path
    could never have worked — and it would have failed first at the v0.71 tag,
    the release that shipped this checker. `repos/<repo>/commits/<tag-name>`
    makes GitHub do the dereference, in one call with nothing to get wrong.

    MEASURED against the shipped v0.70.0 tag: `git/refs/tags/v0.70.0` gives
    `object.type=tag`, and `commits/v0.70.0` returns 2026-09-22T21:33:30Z.

    AND THE WINDOW USED TO BE TRUNCATED TO A DAY (v0.74, found at the cut by
    running this gate rather than trusting it). The search qualifier was built
    as `closed:>={date[:10]}` — the tag's timestamp cut to `YYYY-MM-DD`, which
    GitHub reads as MIDNIGHT. So the window began up to 24 hours before the tag
    and swept in the PREVIOUS releases' closure waves.

    It was invisible while releases were more than a day apart, and v0.72,
    v0.73 and v0.74 all landed on 2026-09-24. MEASURED at the v0.74 cut against
    the live API, both halves on one tree:

        closed:>=2026-09-24            -> #1341, #1349, #1269, #1331   (4)
        closed:>=2026-09-24T15:02:41Z  ->               #1269, #1331   (2)

    where 15:02:41Z is v0.73.0's own commit. #1341 and #1349 closed at
    03:34Z — v0.72's wave — and the gate reported both as
    `CLOSED BUT NOT AUTHORISED: no delivered v0.74 artifact names it`, whose
    prescribed remedy is "reopen it". #1341 is an EXTERNAL reporter's issue,
    correctly closed by v0.72. The gate built to prevent the v0.69 wrong-closure
    shape was one step from causing a wrong REOPENING, for the same root reason
    it exists: a timestamp that was not read at the precision it was written.

    THIS IS NOW DRIVEN (v0.75, RQ-75-CLOSEWINDOW). The paragraph that stood here
    said "no offline test reaches it … a v0.75 candidate; it is NOT claimed
    here", and v0.75 delivered exactly that: `scripts/test_issue_closure_check.py`
    calls `closed_since` against a RECORDED `gh` response, with the pre-fix
    `date[:10]` truncation as the red-first case, and is CI-wired. A disclosure
    the release invalidated and left standing is as false as an overclaim, which
    is why this is corrected rather than deleted.

    ALSO NOW DRIVEN (v0.76, RQ-76-CLOSUREMAIN, #1404). The paragraph that stood
    here named `main()` and `open_issues_now()` as "STILL NOT DRIVEN … v0.76
    candidates", and v0.76 delivered both, so leaving it would break the rule
    stated just above. `main()`'s exit code is now asserted in three directions —
    0 for a clean judgement, 1 for a real failure, and 2 for a REFUSAL,
    distinguished on purpose so a caller can tell "ran and found nothing" from
    "could not run" — and an EMPTY live-open set is refused rather than believed.

    That paragraph also stated the failure mode more loosely than the code
    supports, which is the other half of what #1404 asked for. It said an empty
    set would make "every issue read as closed". Measured against `check()`, it
    SPLITS, and the split is worse than the uniform version:

      - the AUTHORISED direction goes VACUOUS AND SILENT — `if n in open_issues`
        is false for every n, so no `AUTHORISED BUT STILL OPEN` can fire, and the
        gate passes having checked nothing;
      - the HELD-OPEN direction goes RED FOR THE WRONG REASON, printing
        `HELD OPEN BUT ALREADY CLOSED`, whose text asserts the issue "is not
        open" — a falsehood about a live issue, and for #1318 a falsehood about
        an EXTERNAL reporter's open issue.

    THE REMAINING RESIDUAL, stated narrowly: the tests drive how `check()`
    CONSUMES live state (`open_issues` is passed as None, empty, and populated),
    but nothing calls `open_issues_now()` itself, so its three `return None`
    branches — OSError/SubprocessError, a non-zero return code, and a JSON parse
    failure — are untested. The hazard those branches guard is handled at the
    consumer; the branches themselves are not exercised, and that is not claimed
    here.
    """
    date = subprocess.run(
        ["gh", "api", f"repos/{repo}/commits/{tag}", "--jq", ".commit.committer.date"],
        capture_output=True, text=True, check=True).stdout.strip()
    # FULL ISO8601, never `date[:10]`: GitHub's search qualifiers accept a
    # second-granular timestamp, and a release cut on the same day as its
    # predecessor depends on it.
    out = subprocess.run(
        ["gh", "issue", "list", "--repo", repo, "--state", "closed",
         "--limit", "200", "--search", f"closed:>={date}",
         "--json", "number"],
        capture_output=True, text=True, check=True).stdout
    return {int(r["number"]) for r in json.loads(out)}


def open_issues_now(repo: str) -> set[int] | None:
    """Every OPEN issue number, or None when it cannot be read.

    RQ-72-ISSUEGATE (#1250) deliverable (e). The window (`closed_since`) answers
    "who closed this DURING the release", which is the right question for the
    closed-but-not-authorised direction. It is the WRONG question for the other
    two, and answering it there made the gate state a falsehood: at the v0.71
    tag it printed `AUTHORISED BUT NOT CLOSED: #1250` while `gh issue view 1250`
    said CLOSED — closed on 2026-09-17, simply BEFORE the tag. `--allow-unclosed`
    downgraded that to a warning, which hid the false sentence instead of
    correcting it."""
    try:
        out = subprocess.run(
            ["gh", "issue", "list", "--repo", repo, "--state", "open",
             "--limit", "500", "--json", "number"],
            capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    try:
        return {int(r["number"]) for r in json.loads(out.stdout)}
    except (ValueError, KeyError, TypeError):
        return None


def prior_attribution(artifacts, version: tuple[int, int]):
    """Issues that an EARLIER release's artifacts account for, and how.

    RQ-76-CLOSUREMAIN, found by RUNNING this gate at the v0.76 cut rather than
    trusting it. The release ritual closes issues AFTER the tag, because the tag
    is the evidence the closure comment cites. `closed_since` opens its window at
    the tag. So every release's own closure wave lands INSIDE THE NEXT RELEASE'S
    WINDOW, where `authorised_close_set(artifacts, version)` — scoped strictly to
    `version != only_version` — cannot see the artifact that authorised it.

    MEASURED at the v0.76 cut: v0.75.0's commit is 2026-09-25T06:52:31Z, and
    #1223 and #1391 closed at 07:27:31Z and 07:27:33Z — 35 minutes later, by
    v0.75's own ritual, named by RQ-75-PINDEBT3 / RQ-75-CLOSEWINDOW /
    RQ-75-PROBEINPUT. The gate reported both as `CLOSED BUT NOT AUTHORISED`,
    whose prescribed remedy is "Reopen it". That is the SECOND time this file
    was one step from causing a wrong REOPENING — the first was the v0.74
    day-truncated window, documented in `closed_since`. Both have the same
    shape: a timestamp compared against a model of when closures happen that no
    real release has ever matched.

    It did not fire before because it needs a preceding release that actually
    closed issues post-tag: v0.75's own window held exactly #1223 and #1391,
    which v0.75 itself authorised.

    LAUNDERING IS REFUSED, and this is the half that could make the gate WEAKER.
    A prior release that declared `issue-scope: outlives` said, explicitly, do
    not close this. Attribution must not convert that refusal into a permission,
    so held-open in a prior release is reported separately and stays a FAILURE.

    Scans every release STRICTLY BELOW `version`, not only the immediate
    predecessor: the window's lower bound is the tag passed on the command line,
    which the operator chooses, so "only the previous release can appear" is a
    property of one invocation and not of the function. Returns
    {issue: (release_tuple, "authorised" | "held-open", artifact_id)},
    keeping the HIGHEST such release when several name the same issue.
    """
    found: dict[int, tuple[tuple[int, int], str, str]] = {}
    versions = {v for _p, v, _i, _s, _f, _l, _r in artifacts
                if v is not None and v < version}
    for v in sorted(versions):
        auth, held = authorised_close_set(artifacts, v)
        for n, art in held.items():
            found[n] = (v, "held-open", art)
        for n, art in auth.items():
            found[n] = (v, "authorised", art)
    return found


def fmt_release(v: tuple[int, int]) -> str:
    return f"v{v[0]}.{v[1]}"


def check(root: Path, release: str, closed: set[int],
          allow_unclosed: bool = False, open_issues: set[int] | None = None):
    """Returns (failures, warnings, authorised, held_open).

    `closed` is the WINDOW — issues closed at or after the tag. `open_issues`,
    when given, is the live OPEN set and is what the authorised/held-open
    directions are judged against, because their question is about an issue's
    STATE and not about when it changed."""
    version = parse_version(release)
    artifacts, _bad = load_release_artifacts(root, RELEASE_GLOB)
    authorised, held_open = authorised_close_set(artifacts, version)
    prior = prior_attribution(artifacts, version)
    if not artifacts:
        return (["VACUOUS: zero release artifacts loaded"], [], {}, {})
    if not authorised and not held_open:
        return ([f"VACUOUS: no {release} artifact names an issue — the check "
                 f"would pass no matter what was closed"], [], {}, {})

    failures: list[str] = []
    warnings: list[str] = []
    for n in sorted(closed):
        if n in held_open:
            failures.append(
                f"HELD OPEN BUT CLOSED: #{n} — {held_open[n]} declares "
                f"`issue-scope: outlives`, so its issue asks a wider question "
                f"than the artifact delivered. Reopen it")
        elif n not in authorised and n in prior:
            pv, how, art = prior[n]
            if how == "held-open":
                failures.append(
                    f"HELD OPEN BY {fmt_release(pv)} BUT CLOSED: #{n} — "
                    f"{art} declares `issue-scope: outlives`, so "
                    f"{fmt_release(pv)} deliberately did NOT close it. A "
                    f"closure in this window is that refusal being overridden, "
                    f"not {fmt_release(pv)}'s own ritual. Reopen it")
            else:
                warnings.append(
                    f"ATTRIBUTED TO {fmt_release(pv)}: #{n} — closed after the "
                    f"{fmt_release(pv)} tag by that release's own ritual, and "
                    f"{art} names it. Not a {release} closure")
        elif n not in authorised:
            failures.append(
                f"CLOSED BUT NOT AUTHORISED: #{n} — no delivered {release} "
                f"artifact names it, and no earlier release accounts for it "
                f"either. This is the v0.69 shape (a `close #N` inside a PR "
                f"body closed an external reporter's live blocker). Reopen it, "
                f"or name it in the artifact that delivered it")
    for n in sorted(authorised):
        if open_issues is not None:
            # STATE, not window. An authorised issue that is closed — whenever
            # it closed — satisfies the obligation.
            if n in open_issues:
                msg = (f"AUTHORISED BUT STILL OPEN: #{n} — {authorised[n]} is "
                       f"delivered and entitles the release to close it, and "
                       f"the issue is OPEN right now")
                (warnings if allow_unclosed else failures).append(msg)
        elif n not in closed:
            msg = (f"AUTHORISED BUT NOT CLOSED IN THIS WINDOW: #{n} — "
                   f"{authorised[n]} is delivered and entitles the release to "
                   f"close it. NOTE: the live issue state was not available, so "
                   f"this says only that it did not close since the tag; it may "
                   f"already have been closed earlier")
            (warnings if allow_unclosed else failures).append(msg)

    # The mirror direction, which the window ALSO could not see: an issue
    # declared `issue-scope: outlives` must be OPEN. The window catches it only
    # if it was closed AFTER the tag; a closure BEFORE the tag was invisible.
    if open_issues is not None:
        for n in sorted(held_open):
            if n not in open_issues and n not in closed:
                failures.append(
                    f"HELD OPEN BUT ALREADY CLOSED: #{n} — {held_open[n]} "
                    f"declares `issue-scope: outlives`, but the issue is not "
                    f"open. It was closed OUTSIDE this release's window, which "
                    f"the closed-set alone cannot see")
    return failures, warnings, authorised, held_open


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--release", required=True, help="e.g. v0.71")
    ap.add_argument("--root", default=".", type=Path)
    ap.add_argument("--repo", default="pulseengine/synth")
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--closed", help="comma-separated issue numbers (offline)")
    g.add_argument("--since-tag", help="derive the closed set via gh, e.g. v0.70.0")
    ap.add_argument("--allow-unclosed", action="store_true",
                    help="report an authorised-but-open issue as a warning")
    ap.add_argument("--open",
                    help="comma-separated OPEN issue numbers (offline; the "
                         "authorised/held-open directions are judged against "
                         "this STATE, not against the closed window)")
    ap.add_argument("--no-state", action="store_true",
                    help="do not consult live issue state (window only)")
    args = ap.parse_args()

    if args.closed is not None:
        closed = {int(x) for x in args.closed.split(",") if x.strip()}
    else:
        closed = closed_since(args.since_tag, args.repo)

    # STATE beats the window for the authorised / held-open directions (e).
    # `--open` lets the tests drive it offline; otherwise ask the API, and if
    # that cannot be read, SAY the state was unavailable rather than silently
    # falling back to a sentence about the window that reads like one about the
    # issue.
    if args.open is not None:
        open_issues = {int(x) for x in args.open.split(",") if x.strip()}
    elif args.no_state:
        open_issues = None
    else:
        open_issues = open_issues_now(args.repo)
        if open_issues is None:
            print("issue-closure: live issue STATE unavailable — the "
                  "authorised/held-open directions fall back to the window, "
                  "which cannot distinguish 'never closed' from 'closed before "
                  "the tag'")

    failures, warnings, authorised, held_open = check(
        args.root, args.release, closed, args.allow_unclosed, open_issues)

    # RQ-76-CLOSUREMAIN (#1404): an EMPTY live-open set is not evidence.
    #
    # `open_issues_now` returns None on every failure it ANTICIPATES — OSError,
    # a non-zero rc, a parse failure — and the caller above falls back for
    # those. The unanticipated one is `gh` SUCCEEDING and returning `[]`: a
    # silent auth downgrade, a pagination change, a repo rename. That is not
    # None, so no fallback fires, and the two state-dependent directions then
    # behave differently and both wrongly:
    #
    #   * AUTHORISED goes vacuous and SILENT — `n in open_issues` is false for
    #     every n, so no "authorised but still open" is ever raised. The gate
    #     passes while checking nothing.
    #   * HELD-OPEN goes RED for the WRONG REASON — every held-open issue trips
    #     "HELD OPEN BUT ALREADY CLOSED", whose text asserts of a LIVE issue
    #     that it "is not open". A false statement about an external reporter's
    #     issue is worse than a missing check.
    #
    # So refuse rather than report either. Exit 2, not 1: this is "the gate
    # could not run", which a caller must be able to tell from "the gate ran
    # and found failures". Applied to `--open` too — the hazard is in the DATA,
    # not in where it came from.
    if open_issues is not None and not open_issues and (authorised or held_open):
        print(
            f"REFUSED: the live OPEN set is EMPTY while this release's "
            f"artifacts reference {len(authorised) + len(held_open)} issue(s) "
            f"({len(authorised)} authorised, {len(held_open)} held open). "
            f"Either every referenced issue really is closed — in which case "
            f"pass --no-state and judge on the window — or the state read is "
            f"broken. Reporting the authorised direction would be vacuous and "
            f"the held-open direction would assert that a live issue is not "
            f"open. Neither is evidence."
        )
        return 2

    for w in warnings:
        print(f"WARN {w}")
    for f in failures:
        print(f"FAIL {f}")
    print(f"issue-closure: {args.release} — {len(authorised)} authorised, "
          f"{len(held_open)} held open, {len(closed)} closed, "
          f"{len(failures)} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
