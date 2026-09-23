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
    on the live path, never in the tests."""
    when = subprocess.run(
        ["gh", "api", f"repos/{repo}/git/refs/tags/{tag}", "--jq", ".object.sha"],
        capture_output=True, text=True, check=True).stdout.strip()
    date = subprocess.run(
        ["gh", "api", f"repos/{repo}/commits/{when}", "--jq", ".commit.committer.date"],
        capture_output=True, text=True, check=True).stdout.strip()
    out = subprocess.run(
        ["gh", "issue", "list", "--repo", repo, "--state", "closed",
         "--limit", "200", "--search", f"closed:>={date[:10]}",
         "--json", "number"],
        capture_output=True, text=True, check=True).stdout
    return {int(r["number"]) for r in json.loads(out)}


def check(root: Path, release: str, closed: set[int],
          allow_unclosed: bool = False):
    """Returns (failures, warnings, authorised, held_open)."""
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
        if n not in closed:
            msg = (f"AUTHORISED BUT NOT CLOSED: #{n} — {authorised[n]} is "
                   f"delivered and entitles the release to close it")
            (warnings if allow_unclosed else failures).append(msg)
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
                    help="report AUTHORISED BUT NOT CLOSED as a warning")
    args = ap.parse_args()

    if args.closed is not None:
        closed = {int(x) for x in args.closed.split(",") if x.strip()}
    else:
        closed = closed_since(args.since_tag, args.repo)

    failures, warnings, authorised, held_open = check(
        args.root, args.release, closed, args.allow_unclosed)
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
