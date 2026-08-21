#!/usr/bin/env python3
"""Classify a Dependabot version bump: auto-mergeable, or HELD? (#965)

WHY THIS EXISTS. Dependabot labels a bump by semver POSITION, but cargo's
compatibility rule is the LEFTMOST NONZERO component: for a 0.x crate the
minor is the de-facto major, and for a 0.0.x crate even the patch is. That
gap has bitten synth repeatedly — ordeal 0.9->0.12 auto-merged as "minor" and
hung Test+Z3 for days; `object` 0.39->0.40 (#938) was labelled minor and broke
16 call sites across three unrelated newtype surfaces. The hold used to be an
inline shell fragment in dependabot-auto-merge.yml that (a) could not be unit
tested and (b) FAILED OPEN when fetch-metadata returned an empty
previous-version (`case "" in 0.*)` does not match, so hold=false). This
script is the single classifier source, invoked by the workflow and driven by
scripts/test_dependabot_minor_hold.py in the required Claim Check job.

DECISION CONTRACT (fail-closed):
  decision=automerge  ONLY for a cargo-compatible upgrade — same leftmost
                      nonzero component, no prerelease on either side, a real
                      upgrade (new > prev). Classes: `patch`, `minor`.
  decision=hold       EVERYTHING else, including anything this script cannot
                      parse. Classes: `zerox-minor` (0.x minor changed),
                      `zerox-zero` (0.0.x — every bump is breaking),
                      `major`, `prerelease`, `downgrade`, `no-change`,
                      `unparseable`, `grouped-hold` (any member of a grouped
                      update holds).

The consumer (dependabot-auto-merge.yml) enables auto-merge ONLY on the exact
string `decision=automerge`; every other outcome — including this script
crashing, which leaves the output empty — lands on the hold path, which
actively DISABLES auto-merge and asserts it is off. Holding is a delay, never
a block: a held bump merges by hand once the FULL suite is green, including
the separate `--features z3-solver` path (required context "Z3 Verification").

Output (GITHUB_OUTPUT `key=value` lines, sanitized single-line text):
  decision=automerge|hold
  class=<one of the classes above>
  reason=<one human-readable sentence>

Stdlib only. Exit 0 whenever a decision was printed; exit 2 on CLI misuse.
"""

from __future__ import annotations

import argparse
import json
import re
import sys

# Version strings arrive from Dependabot metadata on a pull_request_target
# workflow — treat them as untrusted input. Sanitize anything echoed back so
# a hostile string cannot inject extra GITHUB_OUTPUT lines or control chars.
_UNSAFE_VERSION_CHARS = re.compile(r"[^A-Za-z0-9.+_\-]")
_LINE_BREAKS = re.compile(r"[\r\n]+")


def sanitize_version(s: str, limit: int = 64) -> str:
    return _UNSAFE_VERSION_CHARS.sub("", s or "")[:limit]


def parse_version(s: str):
    """Parse a version into (major, minor, patch, has_prerelease) or None.

    Lenient on shape (``0.39`` and ``v4`` are real Dependabot outputs: cargo
    manifests carry two-component reqs, github-actions tags carry ``v``
    prefixes; missing components read as 0), strict on content (any
    non-ASCII-numeric release component -> None -> the caller HOLDS). Build
    metadata (``+...``) is compatibility-irrelevant and stripped; a
    prerelease (``-...``) is flagged, never ignored.
    """
    s = (s or "").strip()
    if not s:
        return None
    if s[0] in ("v", "V"):
        s = s[1:]
    s = s.split("+", 1)[0]  # build metadata: ignored for compatibility
    prerelease = False
    if "-" in s:
        s, _ = s.split("-", 1)
        prerelease = True
    parts = s.split(".")
    if not parts or len(parts) > 3:
        return None
    nums = []
    for p in parts:
        # ASCII-digit-strict: `p.isdigit()` alone admits e.g. Unicode digits.
        if not p or not all("0" <= c <= "9" for c in p):
            return None
        nums.append(int(p, 10))
    while len(nums) < 3:
        nums.append(0)
    return nums[0], nums[1], nums[2], prerelease


def classify(prev: str, new: str):
    """Return (decision, class, reason) for a single PREV -> NEW bump."""
    shown = f"{sanitize_version(prev) or '<empty>'} -> {sanitize_version(new) or '<empty>'}"
    p = parse_version(prev)
    n = parse_version(new)
    if p is None or n is None:
        return (
            "hold",
            "unparseable",
            f"cannot parse {shown}; an unclassifiable bump fails CLOSED "
            "(the pre-#965 shell classifier failed OPEN on an empty previous-version)",
        )
    pmaj, pmin, ppat, ppre = p
    nmaj, nmin, npat, npre = n
    if ppre or npre:
        return (
            "hold",
            "prerelease",
            f"{shown} involves a prerelease; prerelease compatibility is undefined",
        )
    if (pmaj, pmin, ppat) == (nmaj, nmin, npat):
        return ("hold", "no-change", f"{shown} is not an upgrade")
    if (nmaj, nmin, npat) < (pmaj, pmin, ppat):
        return ("hold", "downgrade", f"{shown} is a downgrade, not an upgrade")
    if pmaj != nmaj:
        return ("hold", "major", f"{shown} changes the major component")
    if pmaj == 0 and pmin != nmin:
        return (
            "hold",
            "zerox-minor",
            f"{shown}: for a 0.x crate the MINOR is the de-facto major "
            "(ordeal 0.9->0.12; object 0.39->0.40 / #938)",
        )
    if pmaj == 0 and pmin == 0:
        return (
            "hold",
            "zerox-zero",
            f"{shown}: for a 0.0.x crate EVERY bump is breaking by cargo's "
            "compatibility rule",
        )
    if pmin != nmin:
        return ("automerge", "minor", f"{shown} is a compatible >=1.0 minor upgrade")
    return ("automerge", "patch", f"{shown} is a compatible patch upgrade")


def classify_all(prev: str, new: str, deps_json: str = ""):
    """Classify a whole PR: every member of a grouped update must be
    auto-mergeable, or the PR holds. Falls back to the single prev/new pair
    when the JSON is empty/absent; a PR with NO classifiable input holds
    (via classify's unparseable arm)."""
    pairs = []
    deps_json = (deps_json or "").strip()
    if deps_json:
        try:
            entries = json.loads(deps_json)
        except ValueError:
            return ("hold", "unparseable", "updated-dependencies-json did not parse")
        if not isinstance(entries, list):
            return ("hold", "unparseable", "updated-dependencies-json is not a list")
        for e in entries:
            if not isinstance(e, dict):
                return (
                    "hold",
                    "unparseable",
                    "updated-dependencies-json entry is not an object",
                )
            pairs.append((str(e.get("prevVersion", "")), str(e.get("newVersion", ""))))
    if not pairs:
        pairs = [(prev, new)]
    verdicts = [classify(p, n) for p, n in pairs]
    holds = [v for v in verdicts if v[0] != "automerge"]
    if holds:
        decision, cls, reason = holds[0]
        if len(pairs) > 1:
            return (
                "hold",
                "grouped-hold",
                f"{len(holds)}/{len(pairs)} grouped bumps hold; first: {reason}",
            )
        return (decision, cls, reason)
    if len(pairs) > 1:
        return (
            "automerge",
            verdicts[0][1],
            f"all {len(pairs)} grouped bumps are compatible upgrades",
        )
    return verdicts[0]


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "--prev", default="", help="previous version (fetch-metadata previous-version)"
    )
    ap.add_argument(
        "--new", dest="new_", default="", help="new version (fetch-metadata new-version)"
    )
    ap.add_argument(
        "--deps-json",
        default="",
        help="fetch-metadata updated-dependencies-json (grouped updates)",
    )
    args = ap.parse_args(argv)
    decision, cls, reason = classify_all(args.prev, args.new_, args.deps_json)
    print(f"decision={decision}")
    print(f"class={cls}")
    print(f"reason={_LINE_BREAKS.sub(' ', reason)[:300]}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
