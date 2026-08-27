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

(3) STRUCTURAL INTEGRITY (#1059 / RQ-60-ARTIFACTSPLIT). The v0.59 wave's
    hand-merged "keep both sides" conflict resolution spliced a new artifact
    INTO a sibling's mapping — between the sibling's `tags:` and its
    `links:`/`fields:` — so the sibling silently LOST its `derives-from`
    trace link and the new artifact inherited it. Both parse; the ids are
    unaffected; the trace graph is simply wrong, and the verification that
    checked it ("16 artifacts, no duplicates, YAML OK") was blind to it by
    construction. The duplicate-key half of that incident is already
    refused by the strict loader below; these rules catch the half that
    would have SHIPPED:

    - R5: every release artifact must carry its own non-empty `links:` (all
      release files — measured zero violations on shipped history), and,
      from v0.60 on, a non-empty `fields.issue`. An artifact whose links
      were absorbed by a splice has NO `links:` key of its own — that exact
      shape is now red.
    - R6: a release-artifact id declared more than once across the loaded
      release files is red. rivet reports this too, but this script's
      `by_id` map would otherwise silently last-wins — the same defect
      class the strict loader exists to refuse, one level up.
    - R0 (extended): from v0.61 the per-release write surface is a
      DIRECTORY, `artifacts/release-vX.YY/`, one file per requirement plus
      a comments-only `_release.yaml` for release metadata — parallel lanes
      then CREATE files instead of appending to one, so the merge-conflict
      class that produced the splice disappears at the source (#1059's
      chosen shape; rivet's generic-yaml source recurses into
      subdirectories — verified empirically on BOTH the required gate's
      pinned rivet 0.23.0 and 0.32.0). Under that layout every
      per-requirement file must contribute >= 1 artifact (a skipped file is
      the #1064 invisible shape, per file), and `_release.yaml` must parse
      to NOTHING but comments — a top-level key there is exactly the shape
      rivet skips silently, so it is red here before it can hide anything.

What this does NOT cover, stated rather than silent:
  * Work that lands with NO artifact and a commit subject that names no
    artifact id is invisible to both halves (unknown-id delivery subjects are
    at least WARNED on). That is candidate shape 3's structural gap.
  * A `manual:` done-when under a non-claiming status cannot fire R3 — for
    those artifacts Direction A protection rests entirely on R4's subject
    convention, which a differently-titled delivery commit evades (a MISS,
    never a false red).
  * R5 catches an artifact whose `links:` block was absorbed WHOLE. A splice
    that lands between `links:` and `fields:` steals only the fields — for
    those, coverage is R1 (the absorbed `done-when` is missing) plus the
    v0.60+ `issue:` requirement, i.e. >= v0.60 only. A splice INSIDE a
    mapping produces a duplicate key and is refused by the strict loader.
    A splice that swaps two artifacts' links without emptying either —
    conceivable, never observed — passes all of these; only rivet's
    per-type traceability rules or a human diff would see it.
  * The directory layout only removes the conflict surface for files under
    `artifacts/release-v*/`. A per-requirement file with a typo'd extension
    (`.yaml.txt`) is invisible to rivet AND to this script; the artifact-
    load floor in CI (which must be raised in the PR that adds artifacts)
    is what notices a file that never loaded.
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

# Release artifacts live in a flat per-release file (<= v0.60 history) OR,
# from v0.61, one file per requirement under artifacts/release-vX.YY/ with a
# comments-only _release.yaml (#1059 — parallel lanes create files instead of
# appending to one). Comma-separated; both layouts are always scanned.
RELEASE_GLOB = (
    "artifacts/release-v*.yaml,"
    "artifacts/release-v*/*.yaml,"
    "artifacts/release-v*/*.yml"
)

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
    """[(file, version, id, status, fields, links)] for every release artifact."""
    out = []
    bad_files = []
    paths = set()
    for pattern in release_glob.split(","):
        paths.update(glob.glob(str(root / pattern.strip())))
    for p in sorted(paths):
        path = Path(p)
        # The version comes from the path, not the basename: under the
        # per-requirement layout the file is release-v0.61/RQ-61-FOO.yaml and
        # only the directory carries the version. Basename-only matching
        # would classify every such artifact as (0, 0) and silently exempt
        # it from every >= v0.60 rule.
        #
        # Scoped to the path RELATIVE TO ROOT, never the absolute path: an
        # ANCESTOR directory of the checkout that happened to be named
        # `release-v0.99` would otherwise supply the first match and
        # mis-version every artifact beneath it — a checkout-location
        # dependency, i.e. the same class as reading an oracle's ground
        # truth from host-dependent text.
        rel = path.relative_to(root).as_posix() if path.is_relative_to(root) \
            else path.name
        m = RELEASE_VERSION.search(rel)
        version = (int(m.group(1)), int(m.group(2))) if m else (0, 0)
        doc = yaml.load(path.read_text(encoding="utf-8"), Loader=StrictLoader)
        if path.name == "_release.yaml":
            # Comments-only metadata file for the directory layout. Any
            # top-level key here is the #1064 shape waiting to happen:
            # rivet's generic-yaml loader skips a non-`artifacts:` file
            # SILENTLY, so content parked here would be invisible to the
            # graph while looking maintained. Red before it can hide.
            if doc is not None:
                bad_files.append(
                    f"R0 {path.parent.name}/{path.name}: _release.yaml must "
                    f"contain COMMENTS ONLY (top-level keys: "
                    f"{', '.join(map(str, doc.keys())) if isinstance(doc, dict) else type(doc).__name__}) "
                    f"— a keyed _release.yaml is skipped silently by rivet "
                    f"(#1064) and becomes a shared write surface again (#1059)"
                )
            continue
        if not isinstance(doc, dict):
            bad_files.append(
                f"R0 {path.name}: release file parses to "
                f"{type(doc).__name__}, not a mapping with `artifacts:` — "
                f"invisible to rivet (#1064)"
            )
            continue
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
                    art.get("links") or [],
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

    # ---- Structural integrity (R5/R6, #1059) ------------------------------
    seen_ids: dict[str, Path] = {}
    for path, version, art_id, status, fields, links in artifacts:
        if art_id in seen_ids:
            failures.append(
                f"R6 {art_id}: declared in BOTH {seen_ids[art_id].name} and "
                f"{path.name} — the later one silently wins every query"
            )
        else:
            seen_ids[art_id] = path
        if not links:
            failures.append(
                f"R5 {art_id}: no `links:` of its own in {path.name} — the "
                f"#1059 splice shape (a sibling absorbed them); every release "
                f"artifact must carry its own trace links"
            )
        if version >= DECLARE_SINCE and not str(fields.get("issue", "")).strip():
            failures.append(
                f"R5 {art_id}: no non-empty `fields.issue` in {path.name} — "
                f"required for release files >= v0.60 (#1059)"
            )

    # ---- Declared-evidence half (R1/R2/R3) --------------------------------
    for path, version, art_id, status, fields, _links in artifacts:
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
        _, _, _, status, fields, _links = by_id[art_id]
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
    ap.add_argument("--release-glob", default=RELEASE_GLOB,
                    help="comma-separated glob patterns for release files "
                         "(default covers the flat <= v0.60 files AND the "
                         "per-requirement release-v*/ directories)")
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
