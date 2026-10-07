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


def tag_commit_date(tag: str, repo: str) -> str:
    """`tag`'s commit date, ISO8601. Split out so the window has two edges.

    RQ-81-R11CONFLICT (#1430). It resolves the TAG NAME directly for the reason
    documented in `closed_since`: every synth release tag is annotated, so
    `git/refs/tags/<tag>.object.sha` is the TAG OBJECT's sha and feeding it to
    `commits/<sha>` answers 422.
    """
    return subprocess.run(
        ["gh", "api", f"repos/{repo}/commits/{tag}", "--jq",
         ".commit.committer.date"],
        capture_output=True, text=True, check=True).stdout.strip()


def next_release_tag(tag: str, repo: str) -> str | None:
    """The release tag immediately ABOVE `tag`, or None if it is the newest.

    RQ-81-R11CONFLICT (#1430). Read from the REMOTE's tags, not a local list,
    because a stale `git fetch` would silently widen the window — and a window
    that is too wide is exactly the defect this is here to close.
    """
    out = subprocess.run(
        ["gh", "api", f"repos/{repo}/git/matching-refs/tags/v", "--jq",
         ".[].ref"], capture_output=True, text=True, check=True).stdout
    vs = []
    for line in out.splitlines():
        name = line.strip().removeprefix("refs/tags/")
        try:
            vs.append((tuple(int(x) for x in name.lstrip("v").split(".")), name))
        except ValueError:
            continue
    try:
        here = tuple(int(x) for x in tag.lstrip("v").split("."))
    except ValueError:
        return None
    above = sorted(v for v in vs if v[0] > here)
    return above[0][1] if above else None


def closed_since(tag: str, repo: str, until_tag: str | None = None) -> set[int]:
    """Issues closed in the window [`tag`, `until_tag`), via gh. Network; only
    used on the live path, never in the tests.

    THE WINDOW HAS AN UPPER EDGE NOW (RQ-81-R11CONFLICT, #1430), and the lack of
    one was the same defect `prior_attribution` patches at the LOWER edge — read
    that docstring first, because this is its mirror and the two belong together.

    `closed:>={date}` alone is unbounded above, so auditing a release that is
    already history sweeps in every LATER release's closure wave. MEASURED at the
    v0.81 cut: `--release v0.77.0 --since-tag v0.76.0` reported EIGHT
    `CLOSED BUT NOT AUTHORISED` failures whose prescribed remedy is "Reopen it".
    SEVEN of them — #1431, #1435, #1440, #1454, #1456, #1459, #1461 — are named
    by delivered artifacts in v0.78, v0.79 and v0.80 and were closed by THOSE
    releases' rituals. They were never v0.77's closures; the window had no reason
    to contain them.

    This is the THIRD time a window edge in this file was one step from a wrong
    REOPENING: the v0.74 day-truncated lower bound, the v0.76 post-tag wave, and
    this. Each one compared a timestamp against a model of when closures happen
    that no real release matched.

    IT CANNOT NARROW THE LIVE GATE, which is the property that matters because
    this is the gate the tag ritual runs. When auditing the release being CUT
    there is no tag above it, `next_release_tag` returns None, and the upper
    bound stays open — byte-identical behaviour to before. Verified by running
    the live invocation both ways.

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
    date = tag_commit_date(tag, repo)
    # FULL ISO8601, never `date[:10]`: GitHub's search qualifiers accept a
    # second-granular timestamp, and a release cut on the same day as its
    # predecessor depends on it. Same for the upper bound.
    qual = f"closed:>={date}"
    if until_tag:
        qual = f"closed:{date}..{tag_commit_date(until_tag, repo)}"
    out = subprocess.run(
        ["gh", "issue", "list", "--repo", repo, "--state", "closed",
         "--limit", "200", "--search", qual,
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


def later_attribution(artifacts, version: tuple[int, int]):
    """Issues that a LATER release's artifacts account for. (RQ-81-R11CONFLICT)

    The mirror of `prior_attribution`, and it exists because that function is
    STRICTLY BACKWARD-LOOKING — correct for the release being cut, where there
    is no "later", and wrong for every audit of history.

    MEASURED at the v0.81 cut, which is what makes this a defect and not a
    hypothetical: auditing v0.77.0 reports EIGHT `CLOSED BUT NOT AUTHORISED`
    failures, whose prescribed remedy is "Reopen it". Seven of the eight —
    #1431, #1435, #1440, #1454, #1456, #1459, #1461 — are named by artifacts in
    v0.78, v0.79 and v0.80, releases that legitimately delivered and closed
    them. Acting on that instruction would reopen seven correctly-closed issues.

    THIS FILE HAS NOW BEEN ONE STEP FROM A WRONG REOPENING THREE TIMES, each
    time because a timestamp or an ordering was compared against a model of when
    closures happen that no real release matched: the v0.74 day-truncated
    window, the v0.76 post-tag closure wave (see `prior_attribution`), and this.
    The shape is the same and the remedy is always the same — widen what the
    gate can see, never weaken what it concludes.

    IT CANNOT WEAKEN THE LIVE GATE, and the reason is structural rather than
    careful: when auditing the release being cut, NO artifact carries a version
    above it, so this returns {} and every verdict is unchanged. The function
    only has an effect on an audit of a release that is already history — which
    is the only situation in which it is consulted. Pinned by a test.

    LAUNDERING IS REFUSED IN THIS DIRECTION TOO. A later release declaring
    `issue-scope: outlives` said do not close this, and that refusal is returned
    as "held-open", which `check` makes a FAILURE rather than an excuse. Without
    it, "a later release mentions it" would become a way to override a
    deliberate hold.

    THE MOST RECENT DECISION GOVERNS, and getting this backwards is the bug this
    function shipped in its first draft — caught by running it, not by reading
    it. The draft let ANY later refusal outrank ANY later authorisation, on the
    reasoning that "a refusal must not be out-voted". MEASURED against real
    history, that is wrong: v0.78 declared `issue-scope: outlives` on #1440 and
    **v0.80 then DELIVERED it** (RQ-80-RITUAL3). Hold open, continue, deliver,
    close is the normal progression of a long-running issue, and the draft read
    it as v0.78's refusal being overridden — emitting "Reopen it" for a
    correctly-closed issue. That is the FOURTH near-reopening in this file, and
    it was produced by the fix for the third. So: iterate ASCENDING and let the
    highest release be the final writer, exactly as `prior_attribution` does.
    The two functions now differ in ONE CHARACTER — `>` where the other has `<`
    — which is a property a reviewer can check at a glance.

    Within a SINGLE release an authorisation wins over a hold-open, matching the
    backward direction. (`check` itself is stricter for the release being CUT,
    testing `held_open` first; that asymmetry is pre-existing and this lane does
    not change it.)

    Returns {issue: (release_tuple, "authorised" | "held-open", artifact_id)},
    keeping the HIGHEST such release when several name the same issue.
    """
    found: dict[int, tuple[tuple[int, int], str, str]] = {}
    versions = {v for _p, v, _i, _s, _f, _l, _r in artifacts
                if v is not None and v > version}
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
    later = later_attribution(artifacts, version)
    if not artifacts:
        return (["VACUOUS: zero release artifacts loaded"], [], {}, {})
    failures: list[str] = []
    warnings: list[str] = []

    # RQ-80-CLOSEGATE (#1454). An empty authorised-and-held-open set used to
    # RETURN HERE, before the loop below. The gate still went red -- this line is
    # itself a failure -- but every PER-ISSUE verdict was lost, and those are the
    # actionable half. `prior_attribution` is built from EVERY earlier release, so
    # the "a prior release held this open and someone closed it anyway" branch is
    # fully computable with nothing authorised in THIS release. Measured on the
    # v0.80 tree: closing #1318 (held open by v0.77 via RQ-77-FALCON2, and an
    # EXTERNAL reporter's issue) produced no mention of #1318 and no "Reopen it".
    # That is the v0.71/v0.73 shape, where the derived close set was empty and the
    # tag would have closed that same reporter's live blocker.
    #
    # So vacuity is now reported as a FINDING ABOUT THE AUTHORISED SET and the
    # loop runs regardless.
    if not authorised and not held_open:
        failures.append(
            f"VACUOUS AUTHORISED SET: no {release} artifact both names an issue "
            f"and claims completion, so nothing in this release authorises ANY "
            f"closure. The per-issue verdicts below are still derived -- from "
            f"earlier releases' attributions -- and must be acted on")
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
        elif n not in authorised and n in later:
            # RQ-81-R11CONFLICT (#1430): a LATER release accounts for it. Only
            # reachable when auditing history; empty for the release being cut.
            lv, how, art = later[n]
            if how == "held-open":
                failures.append(
                    f"HELD OPEN BY {fmt_release(lv)} BUT CLOSED: #{n} — {art} "
                    f"declares `issue-scope: outlives`, so {fmt_release(lv)} "
                    f"deliberately did NOT close it. A later release's refusal "
                    f"is still a refusal, and this closure overrides it. "
                    f"Reopen it")
            else:
                warnings.append(
                    f"ATTRIBUTED TO {fmt_release(lv)}: #{n} — accounted for by "
                    f"{art} in {fmt_release(lv)}, a release LATER than "
                    f"{release}. Not a {release} closure, and NOT something to "
                    f"reopen")
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
                # RQ-81-R11CONFLICT (#1430): the SAME forward blindness, one
                # level in. A hold-open is a statement about THIS release's
                # scope, not a promise for all time, so an issue a LATER release
                # went on to DELIVER is correctly closed and this is not a
                # finding. MEASURED: auditing v0.78.0, #1440 is declared
                # `outlives` by RQ-78-RITUAL and is closed — and
                # RQ-80-RITUAL3 delivered it two releases later. Without this
                # branch the gate demands a reopening of an issue whose work
                # shipped, which is the defect this lane exists to remove.
                lat = later.get(n)
                if lat and lat[1] == "authorised":
                    warnings.append(
                        f"HELD OPEN BY {release} BUT DELIVERED LATER: #{n} — "
                        f"{held_open[n]} declared `issue-scope: outlives`, and "
                        f"{lat[2]} in {fmt_release(lat[0])} went on to deliver "
                        f"it. The closure is that release's, correctly. Not "
                        f"something to reopen")
                    continue
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
    ap.add_argument("--until-tag",
                    help="bound the window ABOVE at this tag (RQ-81-R11CONFLICT, "
                         "#1430). Omitted, it is DERIVED as the release tag above "
                         "--release, which is None for the release being cut, so "
                         "the live invocation is unchanged. `--until-tag none` "
                         "forces the old unbounded window for archaeology")
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
        # RQ-81-R11CONFLICT (#1430): DERIVE the upper edge unless told otherwise.
        # For the release being cut there is no tag above it, so this is None and
        # the window is the same unbounded one every release before v0.81 used.
        until = args.until_tag
        if until is None:
            until = next_release_tag(args.release, args.repo)
        elif until.lower() == "none":
            until = None
        print(f"  window: [{args.since_tag}, {until or 'now'})")
        closed = closed_since(args.since_tag, args.repo, until)

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
