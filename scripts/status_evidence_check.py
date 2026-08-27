#!/usr/bin/env python3
"""RQ-60-FLIPCOUPLE (#1064) — a release-artifact status must agree with the evidence on main.

The class this makes unrepresentable
--------------------------------------------------------------------------
v0.58 made release readiness a QUERY over rivet artifact statuses. A status
that disagrees with reality corrupts that query, and before this gate nothing
mechanically tied "the code landed" to "the artifact says so". Measured across
v0.59 and v0.60 — releases where the coordinator was EXPLICITLY watching for
the class — seven instances slipped anyway, in BOTH directions:

  Direction A (stale `proposed` over shipped code — the query UNDER-reports):
    RQ-59-TIERCENSUS    #1047 merged, no PR flipped it
    RQ-59-GLOBALINIT    #1058 merged, no PR flipped it
    RQ-59-PARTIALCENSUS #1051 merged and did not flip its OWN status
    RQ-60-CANARY        work shipped in v0.59.0 (#1061); artifact landed proposed
    RQ-60-A64IMPORT     #1071 merged, did not flip its own status
    RQ-60-VFPPRESSURE   #1073 merged, did not flip its own status

  Direction B (premature `implemented` over code that has not shipped what the
  artifact promises — the query OVER-reports):
    RQ-60-VFPPRESSURE   flipped on "#1073 merged" without meeting the
                        artifact's own definition of done (5-of-5 cascade
                        stages); reverted in #1074.

All seven were caught by a human querying after the fact; none by a mechanism.
Both directions are the SAME substitution: treating "the PR merged" as "the
artifact's stated outcome holds". Those are different claims, so this gate
makes each landing SAY WHICH ONE it is making, and checks what can be checked.

The mechanism — a composition, with each half's coverage stated
--------------------------------------------------------------------------
Two independent derivations over `artifacts/release-v*.yaml`:

(0) FILE VISIBILITY (R0). A release file that contributes ZERO artifacts
    under `artifacts:` is red — the #1064 class itself. At the moment of
    the three v0.59 misses the file was in the non-schema shape rivet's
    loader silently skipped, so the stale statuses inside it were
    UNFALSIFIABLE: the two defects hid each other. An invisible release
    file must be a red, never a quiet zero.

(1) DECLARED DONE-EVIDENCE (candidate shape 1, "derive what you check
    against"). Every artifact in a release file >= v0.60 must carry
    `fields.done-when`, a machine-evaluable signature of its own definition
    of done:

        done-when: "contains:<path>:<literal>"   file exists AND contains literal
        done-when: "file:<path>"                 path exists
        done-when: "manual: <reason>"            honestly no in-repo signature

    - R2 (over-report ceiling): a CLAIMING status (implemented/verified/
      accepted) whose evidence evaluates FALSE is red. A `manual:` predicate
      under a claiming status additionally requires `fields.verified-by`
      naming the basis (who/what verified it, where recorded) — the flip that
      motivated Direction B carried no basis at all, only "the PR merged".
    - R3 (under-report): a NON-claiming status whose evidence evaluates TRUE
      is red — the artifact's own done-signature exists on main while the
      status says otherwise. This is the only rule that catches work shipped
      under a DIFFERENT program id (RQ-60-CANARY landed as "VCR-TIER-001
      increment 1", so no commit ever named it).

(2) DELIVERY-COMMIT FLOOR (candidate shape 2's noticing direction, enforced
    per shape 3). This repo's measured convention is that a delivery commit's
    subject STARTS with the artifact id ("RQ-59-TIERCENSUS (#1021): ...") —
    28 of 28 delivery commits on main at authoring, zero plan/chore/salvage
    commits (those start "plan(", "chore(rivet):", "salvage(").

    - R4: a first-parent commit on HEAD whose subject starts with a known
      release-artifact id must be ACKNOWLEDGED by that artifact: either its
      status is CLAIMING, or the commit's PR number appears in
      `fields.landed` (the machine-readable statement "increment landed, the
      stated outcome does NOT yet hold" — exactly RQ-60-VFPPRESSURE after
      #1073). Silence — work landed, artifact says nothing — is red.
    - R1: an artifact in a release file >= v0.60 with no `done-when` is red,
      so a new artifact must choose its signature (or write down that it has
      none) in the PR that creates it.

What this does NOT cover, stated rather than silent:
  * Work that lands with NO artifact and a commit subject that names no
    artifact id is invisible to both halves (unknown-id delivery subjects are
    at least WARNED on). That is candidate shape 3's structural gap.
  * A `manual:` done-when under a non-claiming status cannot fire R3 — for
    those artifacts Direction A protection rests entirely on R4's subject
    convention, which a differently-titled delivery commit evades (a MISS,
    never a false red).
  * A FALSE `verified-by` basis passes. The gate forces the basis to be
    written where the reader of the release query can see it; it cannot
    judge it. That residual is exactly as manual as the artifact declared.

Anti-vacuity (the checker is a new defect surface; five releases running
found the defect in checking machinery):
  * Release files are parsed with a DUPLICATE-KEY-STRICT YAML loader —
    PyYAML's silent last-wins on duplicate keys is #1059, and this script
    must not validate with the parser that cannot see that defect. rivet
    remains the schema oracle; this loader only refuses to READ a file rivet
    would refuse.
  * A DELIVERY_FLOOR pins the minimum id-first delivery commits the history
    scan must find (28 at authoring). A shallow checkout, a broken regex, or
    a wrong `git log` invocation therefore reds instead of scanning nothing
    and passing. Only red BELOW the floor (the count grows with every
    delivery); raise it when it drifts far from live.
  * `scripts/test_status_evidence_check.py` replays all seven measured
    instances as committed fixtures, so the gate's ability to catch each is
    re-proven on every CI run, not asserted once at authoring.

Exit 0 iff no rule fires. Prints a `status-evidence:` summary line the CI
step greps as a second non-vacuity anchor.
"""

from __future__ import annotations

import argparse
import glob
import re
import subprocess
import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parent.parent

# Statuses that CLAIM the artifact's stated outcome holds. Everything else
# (draft/proposed/approved/...) claims it does not yet.
CLAIMING = {"implemented", "verified", "accepted"}

# `done-when` declarations are required from this release file on. Earlier
# files are shipped history: their statuses are frozen at implemented/verified
# and backfilling evidence for them would itself be a hand-written mirror.
DECLARE_SINCE = (0, 60)

# Non-vacuity floor on id-first delivery commits found in first-parent
# history. 28 measured on main at authoring (RQ-56-CITE .. RQ-60-VFPPRESSURE).
# A measured value BELOW this means the scan did LESS work than reality holds
# (shallow checkout, regex rot) — that is the defect; never lower it to pass.
DELIVERY_FLOOR = 28

ARTIFACT_ID = re.compile(r"^(RQ-\d+-[A-Z0-9]+)\b")
PR_NUMBER = re.compile(r"\(#(\d+)\)")
RELEASE_VERSION = re.compile(r"release-v(\d+)\.(\d+)")


class DuplicateKeyError(Exception):
    pass


class StrictLoader(yaml.SafeLoader):
    """SafeLoader that REFUSES duplicate mapping keys instead of last-wins."""


def _strict_mapping(loader: StrictLoader, node: yaml.Node, deep: bool = False):
    seen = set()
    for key_node, _ in node.value:
        key = loader.construct_object(key_node, deep=True)
        if key in seen:
            raise DuplicateKeyError(
                f"duplicate key {key!r} at line {key_node.start_mark.line + 1}"
            )
        seen.add(key)
    return yaml.SafeLoader.construct_mapping(loader, node, deep)


StrictLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _strict_mapping
)


def load_release_artifacts(root: Path, release_glob: str):
    """[(file, version-tuple, id, status, fields-dict)] for every release artifact."""
    out = []
    bad_files = []
    paths = sorted(glob.glob(str(root / release_glob)))
    for p in paths:
        path = Path(p)
        m = RELEASE_VERSION.search(path.name)
        version = (int(m.group(1)), int(m.group(2))) if m else (0, 0)
        doc = yaml.load(path.read_text(encoding="utf-8"), Loader=StrictLoader)
        if not isinstance(doc, dict):
            raise SystemExit(f"{path}: not a mapping — refusing to guess")
        arts = [
            a for a in (doc.get("artifacts") or [])
            if isinstance(a, dict) and "id" in a
        ]
        if not arts:
            # R0 — the #1064 class ITSELF: release-v0.59.yaml carried its
            # requirements under non-schema top-level keys, rivet's loader
            # skipped the WHOLE file, and every status inside became
            # unfalsifiable because the file was invisible. A release file
            # this checker cannot read is a RED, never a silent zero — the
            # same discipline as the rivet job's artifact-load floor, applied
            # per file (a floor over the sum can be masked by growth
            # elsewhere; a per-file emptiness check cannot).
            bad_files.append(
                f"R0 {path.name}: release file contributes ZERO artifacts "
                f"under `artifacts:` (top-level keys: "
                f"{', '.join(map(str, doc.keys()))}) — the #1064 invisible-"
                f"file shape; every status inside is unfalsifiable"
            )
            continue
        for art in arts:
            out.append(
                (
                    path,
                    version,
                    str(art["id"]),
                    str(art.get("status", "")),
                    art.get("fields") or {},
                )
            )
    return out, bad_files


def first_parent_subjects(root: Path) -> list[str]:
    r = subprocess.run(
        ["git", "-C", str(root), "log", "--first-parent", "--format=%s"],
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        raise SystemExit(f"git log failed: {r.stderr.strip()}")
    return r.stdout.splitlines()


def evaluate(done_when: str, root: Path):
    """-> (kind, holds_or_None). `manual:` evaluates to None (no signature)."""
    if done_when.startswith("contains:"):
        rest = done_when[len("contains:"):]
        path, sep, literal = rest.partition(":")
        if not sep or not literal:
            return ("malformed", None)
        f = root / path
        return ("contains", f.is_file() and literal in f.read_text(
            encoding="utf-8", errors="replace"))
    if done_when.startswith("file:"):
        return ("file", (root / done_when[len("file:"):].strip()).exists())
    if done_when.startswith("manual:"):
        reason = done_when[len("manual:"):].strip()
        return ("manual", None) if reason else ("malformed", None)
    return ("malformed", None)


def landed_prs(fields: dict) -> set[str]:
    return set(re.findall(r"#(\d+)", str(fields.get("landed", ""))))


def check(root: Path, release_glob: str, subjects: list[str],
          delivery_floor: int):
    failures: list[str] = []
    warnings: list[str] = []
    artifacts, bad_files = load_release_artifacts(root, release_glob)
    failures.extend(bad_files)
    by_id = {a[2]: a for a in artifacts}
    predicates_evaluated = 0

    # ---- Declared-evidence half (R1/R2/R3) --------------------------------
    for path, version, art_id, status, fields in artifacts:
        done_when = fields.get("done-when")
        if done_when is None:
            if version >= DECLARE_SINCE:
                failures.append(
                    f"R1 {art_id}: no `done-when` in {path.name} — declare the "
                    f"machine signature of done, or `manual: <reason>`"
                )
            continue
        kind, holds = evaluate(str(done_when), root)
        predicates_evaluated += 1
        if kind == "malformed":
            failures.append(
                f"R1 {art_id}: malformed `done-when` {done_when!r} — expected "
                f"contains:<path>:<literal> | file:<path> | manual: <reason>"
            )
            continue
        if status in CLAIMING:
            if kind == "manual":
                if not str(fields.get("verified-by", "")).strip():
                    failures.append(
                        f"R2 {art_id}: status `{status}` on a `manual:` "
                        f"done-when with no `verified-by` — 'the PR merged' is "
                        f"not 'the stated outcome holds'; write the basis down"
                    )
            elif not holds:
                failures.append(
                    f"R2 {art_id}: status `{status}` but done-when evidence "
                    f"is ABSENT on this tree ({done_when})"
                )
        else:
            if holds is True:
                failures.append(
                    f"R3 {art_id}: status `{status}` but its done-when "
                    f"evidence EXISTS on this tree ({done_when}) — the status "
                    f"under-reports shipped work"
                )

    # ---- Delivery-commit floor (R4) ---------------------------------------
    delivery_hits = 0
    flagged: set[tuple[str, str]] = set()
    for subject in subjects:
        m = ARTIFACT_ID.match(subject)
        if not m:
            continue
        art_id = m.group(1)
        if art_id not in by_id:
            warnings.append(
                f"WARN: delivery-shaped commit for unknown artifact {art_id}: "
                f"{subject!r} — work may have landed with no artifact at all"
            )
            continue
        delivery_hits += 1
        _, _, _, status, fields = by_id[art_id]
        if status in CLAIMING:
            continue
        prs = PR_NUMBER.findall(subject)
        pr = prs[-1] if prs else None
        if pr is not None and pr in landed_prs(fields):
            continue
        key = (art_id, pr or subject)
        if key in flagged:
            continue
        flagged.add(key)
        failures.append(
            f"R4 {art_id}: delivery commit on main ({subject.split(':')[0]}"
            f"{f' / PR #{pr}' if pr else ''}) but status is `{status}` and "
            f"`landed:` does not acknowledge it — flip the status or record "
            f"the increment"
        )

    # ---- Anti-vacuity ------------------------------------------------------
    if not artifacts:
        failures.append("VACUOUS: zero release artifacts loaded")
    if delivery_hits < delivery_floor:
        failures.append(
            f"VACUOUS: only {delivery_hits} delivery commits matched "
            f"(floor {delivery_floor}) — shallow checkout or scan rot; the "
            f"floor never comes down to pass"
        )

    return artifacts, predicates_evaluated, delivery_hits, warnings, failures


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", type=Path, default=REPO_ROOT,
                    help="repo root to check (default: this repo)")
    ap.add_argument("--release-glob", default="artifacts/release-v*.yaml")
    ap.add_argument("--subjects-file", type=Path, default=None,
                    help="newline-separated commit subjects (default: "
                         "`git log --first-parent --format=%%s` in --root)")
    ap.add_argument("--delivery-floor", type=int, default=DELIVERY_FLOOR,
                    help="min id-first delivery commits the scan must find "
                         "(replays against truncated history may lower it "
                         "EXPLICITLY; CI never does)")
    args = ap.parse_args()

    subjects = (
        args.subjects_file.read_text(encoding="utf-8").splitlines()
        if args.subjects_file
        else first_parent_subjects(args.root)
    )
    try:
        artifacts, preds, hits, warnings, failures = check(
            args.root, args.release_glob, subjects, args.delivery_floor
        )
    except DuplicateKeyError as e:
        print(f"FAIL: duplicate-key defect in a release file (#1059): {e}")
        return 1

    for w in warnings:
        print(w)
    for f in failures:
        print(f"FAIL {f}")
    files = len({a[0] for a in artifacts})
    print(
        f"status-evidence: {len(artifacts)} artifacts across {files} release "
        f"files, {hits} delivery commits matched, {preds} done-when "
        f"predicates evaluated, {len(failures)} failures"
    )
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
