#!/usr/bin/env python3
"""RQ-86-PROVENANCE2 (#1516) — a shipped record's METHOD, as checkable as its figures.

A cold-review record cites COMMITS and TOOL PATHS as its evidence. Until this
script nothing tested either: a reader following a citation could land on a
commit that is on no branch, or a tool that is in no commit.

MEASURED over the previous two records before writing this, which is why the two
halves are separate:

    record            hex tokens   non-ancestor commits   tool paths   absent
    v0.84 review          10                1                 4          0
    v0.85 review          14                2                14          0

So the ABSENT-TOOL half is clean today -- the earlier defect, two records citing
a derivation script that was in no commit on any branch, has since been fixed by
tracking the script -- while the ANCESTRY half is not. All three non-ancestors
are PRE-SQUASH BRANCH shas: this repo squash-merges, so a branch head never
becomes an ancestor of main and its content ships under a different sha. One of
the three is already flagged as a provenance caveat in its own record; the other
two are not, and a reader cannot verify them at all once the branch is deleted.

WHAT THIS CHECKS, and the default is deliberately the CURRENT record rather than
every record ever shipped. A rule that red on the three historical citations the
day it landed is one people route around (the RQ-74-STALEMSG trap, measured in
this repo). The obligation is FORWARD-ONLY: the record being written must cite
merged shas.

Usage:
    python3 scripts/review_record_provenance_check.py                 # newest record
    python3 scripts/review_record_provenance_check.py --record PATH
    python3 scripts/review_record_provenance_check.py --all           # report, never gate
    python3 scripts/review_record_provenance_check.py --self-test
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
REVIEWS = REPO_ROOT / "docs" / "reviews"

HEX = re.compile(r"\b([0-9a-f]{8,40})\b")
TOOLPATH = re.compile(r"\b(scripts/[\w/.-]+\.(?:py|sh|rs|md))\b")


def git(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *args], cwd=REPO_ROOT, capture_output=True, text=True)


def is_commit(sha: str) -> bool:
    return git("cat-file", "-e", f"{sha}^{{commit}}").returncode == 0


def is_ancestor(sha: str, ref: str) -> bool:
    return git("merge-base", "--is-ancestor", sha, ref).returncode == 0


def audit(path: Path, ref: str) -> tuple[list[str], list[str], int, int]:
    """(non-ancestor commits, absent tool paths, commits tested, paths tested)."""
    text = path.read_text()
    bad_sha: list[str] = []
    tested = 0
    for tok in sorted(set(HEX.findall(text))):
        # A hex token that is not a commit object is not a citation -- it is a
        # byte string, a register value or a digest. Counting those as failures
        # is how a check becomes one people disable.
        if not is_commit(tok):
            continue
        tested += 1
        if not is_ancestor(tok, ref):
            bad_sha.append(tok)
    bad_path = [p for p in sorted(set(TOOLPATH.findall(text)))
                if not (REPO_ROOT / p).exists()]
    n_paths = len(set(TOOLPATH.findall(text)))
    return bad_sha, bad_path, tested, n_paths


def newest_record() -> Path:
    recs = sorted(REVIEWS.glob("v0.*-cold-review.md"))
    if not recs:
        sys.exit("FAIL: no review record under docs/reviews/ -- refusing to audit nothing")
    return recs[-1]


def report(path: Path, ref: str, gate: bool) -> int:
    bad_sha, bad_path, n_sha, n_path = audit(path, ref)
    rel = path.relative_to(REPO_ROOT)
    print(f"record-provenance: {rel} — {n_sha} commit citation(s) tested against {ref}, "
          f"{len(bad_sha)} NOT an ancestor; {n_path} tool path(s), {len(bad_path)} absent")
    for s in bad_sha:
        sub = git("log", "-1", "--format=%s", s).stdout.strip()[:70]
        refs = git("branch", "-a", "--contains", s).stdout.strip()
        print(f"  NON-ANCESTOR {s[:12]}  on {'a branch' if refs else 'NO ref'}  {sub}")
    for p in bad_path:
        print(f"  ABSENT PATH  {p}")
    if gate and (bad_sha or bad_path):
        print("\nA citation a reader cannot follow is not evidence. Cite the MERGED "
              "sha (this repo squash-merges, so a branch head never becomes an "
              "ancestor), or state the mapping in the record.")
        return 1
    return 0


def self_test() -> int:
    """Both halves get a POSITIVE CONTROL, because a check that passes everything
    is indistinguishable from one that tests nothing."""
    fails = 0

    def ok(cond: bool, what: str) -> None:
        nonlocal fails
        print(f"  {'ok  ' if cond else 'FAIL'} {what}")
        if not cond:
            fails += 1

    ok(not is_ancestor("0" * 40, "HEAD"), "ANCESTRY control: an all-zero sha is NOT an ancestor")
    ok(is_ancestor("HEAD", "HEAD"), "ANCESTRY control: HEAD IS an ancestor of itself (not vacuous)")
    ok(not (REPO_ROOT / "scripts/definitely_absent_control.py").exists(),
       "EXISTENCE control: a known-absent path is reported absent")
    ok((REPO_ROOT / "scripts/claim_check.py").exists(),
       "EXISTENCE control: a known-present path is reported present (not vacuous)")
    ok(is_commit("HEAD"), "a real commit is recognised as a commit")
    ok(not is_commit("deadbeef" * 5), "a hex token that is no commit is NOT counted as a citation")
    # the extractors must actually extract
    ok(HEX.findall("see 74c5e0f9 for this") == ["74c5e0f9"], "the sha extractor matches a cited sha")
    ok(TOOLPATH.findall("via `scripts/claim_check.py`") == ["scripts/claim_check.py"],
       "the tool extractor matches a cited path")
    print(f"record-provenance-self-test: {fails} failure(s)")
    return 1 if fails else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--record", help="path to a review record (default: newest)")
    ap.add_argument("--ref", default="origin/main", help="ancestry reference")
    ap.add_argument("--all", action="store_true", help="report on every record; never gates")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        return self_test()
    if a.all:
        rc = 0
        for p in sorted(REVIEWS.glob("v0.*-cold-review.md")):
            report(p, a.ref, gate=False)
        return rc
    return report(Path(a.record) if a.record else newest_record(), a.ref, gate=True)


if __name__ == "__main__":
    sys.exit(main())
