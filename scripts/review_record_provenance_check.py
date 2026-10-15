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


def audit(path: Path, ref: str) -> tuple[list[str], list[str], int, int, list[str]]:
    """(non-ancestor commits, absent tool paths, commits tested, paths tested,
    hex tokens UNRESOLVABLE in this object store).

    RQ-87-PROVBLIND (#1540): the fifth element used to be a bare `continue`, and
    that silence was the whole defect. `cat-file -e` fails IDENTICALLY for a token
    that was never a commit (a digest, a register value, a byte string) and for a
    citation whose object this store has lost -- and this repository squash-merges
    and deletes branches, which is exactly what loses them. So the dropped tokens
    were a MIXTURE, and the half that matters is invisible by construction.

    MEASURED over all 25 shipped records, every figure with its venue named: the
    authoring checkout, which still holds the deleted branch heads, tests 243
    citations and flags 105; a fresh `git clone` of the REMOTE -- what CI checks
    out and what a reader following the record has -- tests 139 and flags 1. The
    flag count differs on 22 of the 25, agreeing only on the three that are zero
    in both. And the arithmetic is exact: 243 - 139 = 104 skipped, 105 - 1 = 104
    fewer flags, so EVERY token the fresh clone skipped was one the authoring
    checkout had flagged. The skip is not incidental to the measurement; it is the
    measurement, inverted.

    This bucket is therefore REPORTED and never failed on. It cannot be
    classified locally -- that is the point -- so the honest reading is the DELTA
    between two named venues, which is why `report()` prints the venue too."""
    text = path.read_text()
    bad_sha: list[str] = []
    unresolved: list[str] = []
    tested = 0
    for tok in sorted(set(HEX.findall(text))):
        # A hex token that is not a commit object is not a citation -- it is a
        # byte string, a register value or a digest. Counting those as failures
        # is how a check becomes one people disable. But it is no longer DROPPED:
        # an unfollowable citation lands here too, and a silent subtraction is
        # what let a record read clean in the venue where it had become
        # unfollowable.
        if not is_commit(tok):
            unresolved.append(tok)
            continue
        tested += 1
        if not is_ancestor(tok, ref):
            bad_sha.append(tok)
    bad_path = [p for p in sorted(set(TOOLPATH.findall(text)))
                if not (REPO_ROOT / p).exists()]
    n_paths = len(set(TOOLPATH.findall(text)))
    return bad_sha, bad_path, tested, n_paths, unresolved


def newest_record() -> Path:
    recs = sorted(REVIEWS.glob("v0.*-cold-review.md"))
    if not recs:
        sys.exit("FAIL: no review record under docs/reviews/ -- refusing to audit nothing")
    return recs[-1]


def venue() -> str:
    """Which OBJECT STORE answered, not just which ref — RQ-87-PROVBLIND (#1540).

    An ancestry figure without its venue is not a measurement: the same record
    reads 15 non-ancestors here and 0 in a fresh clone. The ref count is the
    cheapest honest proxy for "does this store still hold deleted branch heads",
    and it is DERIVED rather than asserted."""
    n = len(git("for-each-ref", "--format=%(refname)").stdout.strip().split("\n"))
    return f"{REPO_ROOT} ({n} local ref(s))"


def report(path: Path, ref: str, gate: bool) -> int:
    bad_sha, bad_path, n_sha, n_path, unresolved = audit(path, ref)
    rel = path.relative_to(REPO_ROOT)
    print(f"record-provenance-venue: {venue()}")
    print(f"record-provenance: {rel} — {n_sha} commit citation(s) tested against {ref}, "
          f"{len(bad_sha)} NOT an ancestor; {len(unresolved)} hex token(s) "
          f"UNRESOLVABLE in this store; {n_path} tool path(s), {len(bad_path)} absent")
    for s in bad_sha:
        sub = git("log", "-1", "--format=%s", s).stdout.strip()[:70]
        refs = git("branch", "-a", "--contains", s).stdout.strip()
        print(f"  NON-ANCESTOR {s[:12]}  on {'a branch' if refs else 'NO ref'}  {sub}")
    for p in bad_path:
        print(f"  ABSENT PATH  {p}")
    # Printed, not failed on. The bucket MIXES non-citations with citations this
    # store has lost, and nothing local can tell them apart -- so the length is
    # shown with each token, because a 64-character token is a digest and a
    # 7-to-12-character one is shaped like a sha.
    # No length classification: `HEX` bounds tokens to 8-40 chars, so every one
    # is sha-shaped by construction and a "digest-shaped" branch keyed on >= 40
    # would label a FULL GIT SHA a digest. An earlier version of this loop did
    # exactly that. The length is printed as data; the reading is the reader's,
    # and the decisive reading is the delta against another named venue.
    for s in unresolved:
        print(f"  UNRESOLVABLE {s:42s} {len(s)} hex chars — not a commit object "
              f"HERE; either never one, or a citation this store has lost")
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

    # RQ-87-PROVCRASH (#1539): the REPORT form, with a RELATIVE path — the form a
    # human runs, which nothing exercised. It raised ValueError from
    # `relative_to` on the raw argument. Both halves are asserted: the relative
    # path must work AND must resolve to the same record as the absolute one, so a
    # fix that merely swallowed the error would not pass.
    import subprocess as _sp
    newest = newest_record()
    rel = newest.relative_to(REPO_ROOT)
    runs = {}
    for label, arg in (("relative", str(rel)), ("absolute", str(newest))):
        r = _sp.run([sys.executable, str(Path(__file__).resolve()), "--record", arg],
                    capture_output=True, text=True, timeout=300, cwd=REPO_ROOT)
        runs[label] = r
        ok("Traceback" not in (r.stdout + r.stderr),
           f"REPORT form with a {label} path does not TRACEBACK")
    ok(runs["relative"].returncode == runs["absolute"].returncode,
       "...and both paths reach the same verdict "
       f"(rel={runs['relative'].returncode}, abs={runs['absolute'].returncode})")
    first = lambda r: next((l for l in r.stdout.split("\n")
                            if l.startswith("record-provenance:")), "")
    ok(first(runs["relative"]) == first(runs["absolute"]) != "",
       "...and both report the SAME record, non-vacuously")

    # RQ-87-PROVBLIND (#1540): the UNRESOLVABLE bucket. BOTH halves, because
    # either alone passes under a broken implementation -- a bucket that
    # swallowed everything would pass the first, and one that stayed empty would
    # pass the second. v0.86 shipped a case asserting one half of its own message
    # and it was green under exactly the state it forbade.
    import tempfile as _tf
    with _tf.TemporaryDirectory() as d:
        probe = Path(d) / "v0.00-cold-review.md"
        head = git("rev-parse", "HEAD").stdout.strip()
        # one token that IS a commit here, one 64-char digest that never is.
        # 16 hex chars: inside HEX's {8,40} AND word-bounded. A 64-character
        # digest is NOT -- `\b([0-9a-f]{8,40})\b` needs a boundary at both ends,
        # and a 40-char submatch of a 64-char run has a hex char after it, so the
        # first version of this probe was invisible to the pattern it tested.
        probe.write_text(f"cites {head} and token {'deadbeef' * 2}\n")
        bad_sha, _bp, n_sha, _np, unresolved = audit(probe, "HEAD")
        ok(n_sha == 1 and not bad_sha,
           "UNRESOLVABLE control: a real commit is TESTED, not bucketed")
        ok(unresolved == ["deadbeef" * 2],
           "UNRESOLVABLE control: ...and the unresolvable token IS reported, not dropped")
        ok(len(unresolved) == 1,
           "UNRESOLVABLE control: ...and the bucket did not swallow the real commit too")

    # The venue must be NAMED and DERIVED. An ancestry figure without its venue is
    # not a measurement: the same record reads 15 non-ancestors in the authoring
    # checkout and 0 in a fresh clone of the remote.
    v = venue()
    ok(str(REPO_ROOT) in v and "local ref(s)" in v,
       "VENUE control: the venue names the object store and its ref count")
    ok(not v.endswith("(0 local ref(s))"),
       "VENUE control: ...and the ref count is derived, not a stub zero")
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
    # RQ-87-PROVCRASH (#1539): RESOLVE the argument. `report()` calls
    # `path.relative_to(REPO_ROOT)`, which raises ValueError on a RELATIVE path —
    # a traceback, not a diagnostic. CI gates only `--self-test`, so the form a
    # human runs was the unexercised one, and v0.86's review worked around it
    # with an absolute path instead of reporting it: the unreported-workaround
    # anti-pattern. A self-test wired into CI says nothing about the report path
    # beside it.
    return report(Path(a.record).resolve() if a.record else newest_record(),
                  a.ref, gate=True)


if __name__ == "__main__":
    sys.exit(main())
