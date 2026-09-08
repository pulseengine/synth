#!/usr/bin/env python3
"""RQ-65-FLOORSHAPE (#1183) — churn of the two status-evidence population
counts, measured release by release with the checker's OWN instruments.

For every release tag v0.56.0 .. v0.64.0 plus HEAD:

  delivery  = id-first first-parent delivery commits reachable from the ref
              whose id is a release artifact in the tree AT THAT REF
              (the R4 scan, `ARTIFACT_ID` + `RELEASE_GLOB` as shipped today)
  programme = artifacts `check_programme` status-checks over the tree at
              that ref (`PROGRAMME_GLOB` + the strict loader as shipped today)

and, per release interval, how many first-parent commits MOVED each count —
which is how many ledger bumps an EQUALITY pin at HEAD would have cost. The
programme series is evaluated at every first-parent commit touching
artifacts/ (129 since v0.56.0), so a decrease anywhere inside an interval
would show; none did.

This is the measurement the anchor shape is justified by (see the ANCHOR_TAG
comment block in scripts/status_evidence_check.py and
scripts/repro/floorshape_1183_gate.md for the recorded run). Re-run it when
the shape is questioned; the checker re-derives the anchor itself on every
CI run, so nothing here is a pin.

    python3 scripts/floorshape_1183_churn.py [repo-root]
"""
import io
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 \
    else Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import status_evidence_check as sec  # noqa: E402

REFS = ["v0.56.0", "v0.56.1", "v0.56.2", "v0.57.0", "v0.58.0", "v0.59.0",
        "v0.60.0", "v0.61.0", "v0.62.0", "v0.63.0", "v0.64.0", "HEAD"]


def git(*args) -> bytes:
    r = subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True)
    if r.returncode != 0:
        raise SystemExit(f"git {' '.join(args)} failed: {r.stderr.decode()}")
    return r.stdout


def tree_at(ref: str, into: Path) -> None:
    blob = git("archive", "--format=tar", ref, "artifacts")
    with tarfile.open(fileobj=io.BytesIO(blob)) as tf:
        try:
            tf.extractall(into, filter="data")
        except TypeError:  # pragma: no cover - pre-3.12 tarfile
            tf.extractall(into)


def programme_at(ref: str):
    with tempfile.TemporaryDirectory() as td:
        tree_at(ref, Path(td))
        try:
            return sec.check_programme(Path(td), floor=0)[1]
        except sec.DuplicateKeyError:
            return None


def counts_at(ref: str):
    subjects = git("log", "--first-parent", "--format=%s",
                   ref).decode().splitlines()
    with tempfile.TemporaryDirectory() as td:
        tree_at(ref, Path(td))
        try:
            arts, _ = sec.load_release_artifacts(Path(td), sec.RELEASE_GLOB)
            by_id = {a[2] for a in arts}
            delivery = sum(
                1 for s in subjects
                if (m := sec.ARTIFACT_ID.match(s)) and m.group(1) in by_id)
        except sec.DuplicateKeyError:
            delivery = None
    return delivery, programme_at(ref), len(subjects)


def main() -> int:
    print(f"{'ref':9} {'fp-commits':>10} {'delivery':>9} {'programme':>10}")
    series = {}
    for ref in REFS:
        d, p, n = counts_at(ref)
        series[ref] = (d, p)
        print(f"{ref:9} {n:>10} {str(d):>9} {str(p):>10}")

    print("\nPer-interval moves (an equality pin at HEAD costs one bump per "
          "move):")
    print(f"{'interval':20} {'fp-commits':>10} {'delivery':>9} "
          f"{'programme':>10} {'dips':>5}")
    for a, b in zip(REFS, REFS[1:]):
        commits = git("log", "--first-parent", "--format=%H",
                      f"{a}..{b}").decode().split()
        subj = git("log", "--first-parent", "--format=%s",
                   f"{a}..{b}").decode().splitlines()
        # The delivery count moves by construction at every id-first subject.
        dmoves = sum(1 for s in subj if sec.ARTIFACT_ID.match(s))
        touching = git("log", "--first-parent", "--format=%H", f"{a}..{b}",
                       "--", "artifacts/").decode().split()
        touching.reverse()
        prev = series[a][1]
        pmoves = dips = 0
        for h in touching:
            cur = programme_at(h)
            if cur is None:
                continue
            if cur != prev:
                pmoves += 1
                dips += cur < prev
                prev = cur
        print(f"{a + '..' + b:20} {len(commits):>10} {dmoves:>9} "
              f"{pmoves:>10} {dips:>5}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
