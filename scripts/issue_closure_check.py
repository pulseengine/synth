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
    """
    date = subprocess.run(
        ["gh", "api", f"repos/{repo}/commits/{tag}", "--jq", ".commit.committer.date"],
        capture_output=True, text=True, check=True).stdout.strip()
    out = subprocess.run(
        ["gh", "issue", "list", "--repo", repo, "--state", "closed",
         "--limit", "200", "--search", f"closed:>={date[:10]}",
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
        elif n not in authorised:
            failures.append(
                f"CLOSED BUT NOT AUTHORISED: #{n} — no delivered {release} "
                f"artifact names it. This is the v0.69 shape (a `close #N` "
                f"inside a PR body closed an external reporter's live "
                f"blocker). Reopen it, or name it in the artifact that "
                f"delivered it")
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
