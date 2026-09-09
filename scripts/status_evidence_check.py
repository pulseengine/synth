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
    - R4-issue (#1119 / RQ-61-R4BLIND): the same acknowledgment demand for a
      conventional-commit subject whose SCOPE is an issue reference --
      `fix(#1040): ...` resolves through `fields.issue` to the artifact
      holding that issue (the highest-release holder; a still-ambiguous
      issue WARNS, never guesses). The scope position IS the marker
      discipline: a `#N` in the DESCRIPTION is measured to name a cause,
      not a target (eefa19ef's `fix(oracle): #1104 shadowed ...` references
      the PR that INTRODUCED the defect -- resolving it would have
      misattributed the commit), so description-position references never
      become delivery claims. Scoped to the RELEASE WINDOW (first-parent
      commits since the previous minor's tag) because an issue can be
      re-worked across releases: `fix(#1085): ... (#1090)` was v0.60-era
      work on the issue RQ-61-EVIDENCE now holds, and matching frozen
      history against the current cycle's issue map would misattribute it.
    - R10 (#1119, the completeness floor R4 cannot be): every first-parent
      delivery-TYPED commit (feat/fix/perf/proof/test types; plan/chore/
      docs/salvage/investigate/track are process commits) in the release
      window must be ATTRIBUTABLE to some release artifact -- a known
      artifact id anywhere in the subject, a known `fields.issue` number
      anywhere in the subject, or the commit's PR number named in any
      artifact's `landed:`/`verified-by:`. Unattributable is red: work
      landed and every artifact is silent. This is what catches the
      measured eefa19ef instance -- a delivery whose subject names neither
      its artifact (RQ-61-ORACLEFLOOR) nor its issue (#1113) cannot be
      RESOLVED to one artifact, but it can be NOTICED, and the red forces a
      human to write the attribution (`landed:`) that resolution needs.
      Attribution deliberately errs toward green -- a mention suffices,
      because R10's demand is NON-SILENCE, not a status flip, so the
      passing-mention rule R4 protects is not violated. A window that
      cannot be derived (no git, no previous-minor tag) SKIPS LOUDLY, and
      the CI grep on the `status-evidence-window:` line turns that skip
      into a red.

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

(4) EVIDENCE SCOPING (RQ-61-EVIDENCE, #1085 — all three found by USING
    this gate during the v0.60 cut, not by reasoning about it):

    - R7 (evidence must belong to the release): RQ-60-CANARY was
      `implemented` in v0.60 on evidence that shipped in v0.59.0 — the
      canary gate merged at 08:50 (#1061), v0.59.0 was tagged at 15:19
      (the gate is an ANCESTOR of that tag; v0.59.0's notes credit it),
      and the v0.60 plan scoped it at 18:56, AFTER the tag. Every rule
      above passed, because each asks whether evidence EXISTS and none
      asks WHICH RELEASE it arrived in. So: for every contains:/file:
      done-when that currently HOLDS, the first-parent commit that
      INTRODUCED the signature (`git log -S<literal>` oldest for
      contains:, `--diff-filter=A` oldest for file:) must NOT be an
      ancestor of the previous minor's release tag — the HIGHEST
      vX.(Y-1).* tag, so "shipped in the previous minor's PATCH" is
      caught too (a main-line commit that is an ancestor of a patch tag
      predates the patch branch point, so the later-tagged-patch case
      cannot mis-attribute post-minor work). Escape hatch, per-case like
      the ratchet waivers: an explicit `fields.shipped-in: vX.Z`
      (version-shaped, reason written beside it) accepts the artifact as
      carrying traceability CLOSURE for work another release delivered —
      RQ-60-CANARY on main is the live green instance.

      Reliability, stated rather than silent: git archaeology needs full
      history and tags, and CI checkouts are often shallow. When the
      root is not a git repo, the checkout is SHALLOW, the previous-
      minor tag is invisible, or the signature holds only uncommitted,
      R7 LOUDLY SKIPS: an `R7-SKIP` warning per artifact, and the skip
      count printed in the machine-read summary line. The skip cannot
      become the quiet-pass shape in CI: the CI step's summary grep pins
      `(0 skipped)` and >= 1 archaeology check performed, and a shallow
      checkout already reds the release anchor (A1, #1183) before R7 is
      reached.

    - R8 (the `release:` field must equal the file's version): this
      script derives an artifact's release from its PATH; rivet's
      readiness query reads the FIELD; nothing asserted they agree. The
      harmful direction: an artifact in a pre-v0.60 file carrying
      `release: v0.60` is EXEMPT from every >= v0.60 rule here while
      rivet counts it in v0.60's scope — a silent version-gate bypass of
      R1/R5, red. The 6 measured benign mismatches (v0.56.1/v0.56.2
      artifacts in release-v0.57.yaml) are real PATCH-RELEASE artifacts
      parked in the next minor's file — a legitimate practice now STATED
      as the rule's one allowance: a field naming a PATCH of the file's
      previous minor (vX.(Y-1).Z, Z >= 1) is green, because a patch cut
      mid-cycle is written up in the file of the minor under
      development. Everything else — field ahead of the path, field
      behind it without a patch component, missing, unparseable — is
      red.

    - R9 (a `contains:` into crate SOURCE is weaker than the gate that
      exercises it): three of v0.60's eight artifacts pinned
      code-existence where their own description set a measured-or-
      executed bar (RQ-60-A64IMPORT: "the acceptance number is the
      deliverable", done-when = a symbol exists). A predicate that
      cannot fail on the failure the artifact defines for itself is not
      a predicate. Both live instances were corrected in #1090 — one
      re-pointed at its gate's non-vacuity floor, one moved to `manual:`
      + `verified-by`; this rule is what was missing. Under a CLAIMING
      status, a contains:/file: whose path is crate SOURCE — `crates/**`
      EXCLUDING `/tests/` components, because crate integration-test
      dirs are executed by the required Test job and are gate-shaped,
      exactly like scripts/, coq/ (kernel-checked by verify_proofs) and
      workflow files; measured on the tree, every honest signature
      already points at one of those — requires a written
      `fields.verified-by` saying why code-existence genuinely IS the
      outcome here. The better fix is re-pointing the signature at the
      gate, which is what both #1090 corrections did.

What this does NOT cover, stated rather than silent:
  * Work that lands with NO artifact used to be invisible to both halves.
    R10 closes that INSIDE the release window for delivery-typed
    conventional subjects; outside the window, for a subject with no
    recognized type prefix (`fix: x` with no scope, a bare sentence), and
    for process-typed subjects, the gap remains (unknown-id delivery
    subjects are at least WARNED on).
  * A `manual:` done-when under a non-claiming status cannot fire R3 — for
    those artifacts Direction A protection rests on R4's subject
    convention plus R4-issue's scope convention; a delivery commit using
    NEITHER is caught only as R10's weaker non-silence demand (a red that
    forces attribution, not a status flip).
  * R4-issue resolves an issue held by artifacts in SEVERAL releases to the
    highest-release holder, and WARNS instead of guessing when that is
    still ambiguous — an ambiguous-issue delivery commit therefore gets
    R10's attribution demand only.
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
    The same holds for `shipped-in` (R7): the gate checks its FORMAT and
    that it was written down; it does not re-derive which tag the named
    version corresponds to.
  * R7 checks only the "arrived too EARLY" direction (evidence already an
    ancestor of the previous release). Evidence landing AFTER the
    release's own tag — scoped to vX.Y, delivered in vX.Y+1 — is the
    other mis-scoping direction; it is what the release-notes review
    catches today, and R7 does not claim it.
  * R9 verifies the signature points at gate-shaped SURFACE (scripts/,
    tests, coq/, workflows — anything that is not crate source). Whether
    a scripts/ signature names a gate some CI job actually RUNS is
    oracle_wiring_check.py's surface, not this one's.

Anti-vacuity (the checker is a new defect surface; five releases running
found the defect in checking machinery):
  * Release files are parsed with a DUPLICATE-KEY-STRICT YAML loader —
    PyYAML's silent last-wins on duplicate keys is #1059, and this script
    must not validate with the parser that cannot see that defect. rivet
    remains the schema oracle; this loader only refuses to READ a file rivet
    would refuse.
  * The id-first delivery commits the history scan must find are pinned as
    an EQUALITY at the previous minor's release tag (A1, #1183 — see the
    ANCHOR_TAG comment block): a shallow checkout, a broken regex, or a
    wrong `git log` invocation reds instead of scanning nothing and passing,
    and the pin cannot lag because the anchor moves with the tag. The live
    count must be >= the anchor (A3), so the slack is one release's growth,
    never more. Before #1183 this was a hand-pinned lower bound that sat at
    28 against a live 67.
  * `scripts/test_status_evidence_check.py` replays all seven measured
    instances as committed fixtures, so the gate's ability to catch each is
    re-proven on every CI run, not asserted once at authoring.

(5) PROGRAMME-ARTIFACT STATUS LEGALITY (P0/P1/P2, #1133 /
    RQ-62-ROADMAPGATE) — see the comment block at PROGRAMME_GLOB. The VCR
    roadmap's 39 artifacts were outside every rule above by scope, and two
    carried no `status` key at all. P1 (status present) and P2 (status is a
    legal lifecycle value) apply to EVERY artifact-bearing yaml under
    artifacts/, release files included; P0 pins the roadmap file's own
    visibility; a P-VACUOUS floor pins the scan population. Deliberately
    NOT applied to the roadmap: R7/R8 (it has no `release:` by design until
    an item is scoped), R4/R10 (no release window exists), R1-R3/R9
    (programme items are long-lived records whose per-increment delivery is
    tracked by RQ-* release artifacts; backfilling 39 done-when signatures
    would be a hand-written mirror — the DECLARE_SINCE reasoning). Since
    #1183 the population is guarded per file (P3: every yaml under
    artifacts/ is one the glob scans; P4: it contributes >= 1 artifact) and
    the P-VACUOUS floor is derived from the release anchor (A3).

(7) RELEASE-ANCHORED NON-VACUITY (A0-A3, #1183 / RQ-65-FLOORSHAPE) — see
    the comment block at ANCHOR_TAG. The two population floors above were
    hand-pinned lower bounds that only ever lagged (28 against 67; 379
    against 408), and equality at HEAD was measured to cost a bump in
    essentially every delivery PR. What IS constant between releases — the
    delivery commits reachable from the previous minor's tag, the artifacts
    in the tree at that tag — is pinned as an equality and RE-DERIVED FROM
    GIT on every run (A1/A2); the live counts must not fall below it (A3);
    and the anchor must be the window's own previous tag, at most one minor
    behind (A0), so the once-per-release move is forced by the gate rather
    than remembered.

(6) UNSCOPED-ARTIFACT STALENESS (S1/S2, #1085 / RQ-64-SCOPEGAP) — see the
    comment block at STALENESS_ANCHOR. (5) widened the SCOPE to every
    artifact yaml but not the OBLIGATIONS: an artifact with no `release:`
    (293 of 400 at authoring, across 25 topic files) got a legal-status
    check and nothing else, and figures the repo DERIVES elsewhere were
    restated in those files as undated present-tense fact and rotted in
    place. The decision: an unscoped artifact is a RECORD — it cites a
    moving figure only AS HISTORY (dated in the same sentence) or names
    the derivation instead of the number. S1 enforces that for the
    repo-derived proof counts, S2 for any measured figure in a TITLE;
    a version-named topic file or a version-shaped `release:` is dated
    by construction; the citations scanned are pinned as an EQUALITY
    (S-DRIFT, red in both directions — RQ-63-FLOOREQ one surface over).

Exit 0 iff no rule fires. Prints `status-evidence:`, `programme-status:`,
`programme-staleness:` and `status-evidence-anchor:` summary lines the CI step greps as
non-vacuity anchors, and a
`status-evidence-window:` line pinning that the R4-issue/R10 window scan
actually ran (SKIPPED there fails the CI grep, so the loud skip cannot
become the quiet pass).
"""

from __future__ import annotations

import argparse
import io
import os
import tarfile
import tempfile
import glob
import json
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

# ---- Release-anchored non-vacuity (A-rules, #1183 / RQ-65-FLOORSHAPE) ------
#
# Two population counts guard this script against doing LESS work than
# reality holds: the id-first delivery commits R4 finds in first-parent
# history, and the artifacts the P-rules status-check. Until v0.65 each was a
# hand-pinned lower bound that only ever LAGGED: DELIVERY_FLOOR sat at 28
# against a live 67 (58 % slack — a first-parent checkout depth of 79 kept the
# gate green while dropping 39 of the 67 delivery commits and every one from
# v0.56-v0.61), PROGRAMME_FLOOR at 379 against 408.
#
# EQUALITY AT HEAD IS THE WRONG SHAPE FOR THESE TWO. RQ-63-FLOOREQ and
# RQ-64-SCOPEGAP chose equality for a count that moved 2 times in 7 release
# intervals. Measured v0.56.0 -> v0.64.0 -> HEAD with this script's own
# instruments (scripts/floorshape_1183_churn.py; transcript in
# scripts/repro/floorshape_1183_gate.md):
#
#   delivery   2, 2, 3, 3, 10, 26, 37, 53, 61, 64, 67, 67    65 moves / 11 intervals
#   programme  275, 287, 289, 290, 301, 322, 331, 367, 385, 391, 401, 408
#                                                             31 moves / 11 intervals
#
# An equality at HEAD costs a ledger bump in essentially every delivery PR —
# churn that buys nothing, on the repo's most merge-contended file, and a
# gate people cannot move honestly is a gate they route around.
#
# THE SHAPE: pin the part of each count that is CONSTANT between releases.
# Main history is immutable and a shipped release's artifacts are frozen, so
# "delivery commits reachable from the previous minor's tag" and "artifacts in
# the tree AT that tag" cannot change until the tag changes. Both are pinned
# as EQUALITIES, RE-DERIVED FROM GIT ON EVERY RUN against the anchor tag:
#
#   A1: id-first delivery commits reachable from ANCHOR_TAG == ANCHOR_DELIVERY.
#       Below = truncated history (a shallow checkout) or instrument rot (the
#       id regex or release glob finds less than it did); above = rewritten
#       history or an orphan commit that acquired an artifact. A repository
#       that declares itself SHALLOW is red outright — an equality that
#       happens to hold over a truncated ancestry is not evidence.
#   A2: artifacts the P-scan finds in `git archive ANCHOR_TAG artifacts` ==
#       ANCHOR_PROGRAMME, run through the SAME glob/loader/filter as the live
#       scan, so loader or glob rot shows as inequality on a tree that has
#       not changed.
#   A3: the live HEAD counts are >= the anchor (the pre-#1183 floors, now
#       DERIVED from the anchor instead of hand-pinned): slack is bounded to
#       exactly one release's growth — measured 0-16 delivery commits and
#       1-36 artifacts per interval — instead of unbounded.
#   P3/P4 (in check_programme): what a SUM floor structurally cannot see — a
#       single file going invisible — is caught per file: every yaml under
#       artifacts/ must be one the glob scans (P3) and must contribute >= 1
#       artifact (P4, R0 generalized past release files). Measured at
#       authoring: 89 of 89 visible, only the five comments-only
#       _release.yaml empty. Zero churn: adding a file moves no number.
#
# THE MOVE IS ONCE PER RELEASE AND FORCED, NOT REMEMBERED (A0): the anchor must
# be the previous minor's tag of the release being cut — the R4-issue/R10
# window's own derivation. One minor of lag is a WARNING that prints the
# three new lines to paste; two minors is red.
#
# WHEN TO MOVE IT — the PR that OPENS THE NEXT RELEASE WINDOW, not the post-tag
# attestation PR. This was measured, because the obvious reading is wrong in a
# way that reds `main` (coordinator, v0.65, in a scratch clone):
#
#   * TAGGING DOES NOT MOVE THE LAG. `lag` compares ANCHOR_TAG against the
#     release WINDOW's previous tag, not the newest tag. After `git tag -a
#     v0.65.0` the window is still v0.65 and its previous tag is still
#     v0.64.0, so the checker reports `lag 0` and exit 0. There is no
#     ANCHOR-LAG warning at the tag to act on.
#   * MOVING IT AT THE TAG IS RED, not merely early. With ANCHOR_TAG =
#     "v0.65.0" while the window is still v0.65:
#         FAIL A0 anchor v0.65.0: AHEAD of the window's previous tag v0.64.0
#              — an anchor cannot precede the release it anchors (#1183)
#     plus an A2 mismatch, because the tree at the new tag holds a different
#     artifact count than the pin recorded.
#
# So the anchor moves in the vX.(Y+1) PLANNING PR — the one that creates
# `artifacts/release-vX.(Y+1)/` — together with the re-derived
# ANCHOR_DELIVERY / ANCHOR_PROGRAMME and a PROGRAMME_DELETED_SINCE_ANCHOR
# reset. That is the first moment the window has advanced, which is exactly
# when the one-minor grace period starts. The values are this script's own derivation, so
# a wrong hand-copy fails A1/A2 in the same PR. claims.yaml pins the three
# lines verbatim (SYNTH-STATUS-EVIDENCE-ANCHOR-1183) so every move is a
# visible ledger diff, and pins that the `!=` checks stay wired.
ANCHOR_TAG = "v0.65.0"
ANCHOR_DELIVERY = 69
ANCHOR_PROGRAMME = 409
# A3-programme waiver channel, empty by construction: the programme count has
# never decreased at any of the 129 first-parent commits touching artifacts/
# since v0.56.0 (measured). A deliberate net deletion declares its size here
# WITH the reason beside it; a declaration the live count does not need is a
# DEAD waiver and red (the ratchet engine's rule). Reset to 0 when the anchor
# moves — the new tag's count absorbs it.
PROGRAMME_DELETED_SINCE_ANCHOR = 0

# A3 (delivery): the live first-parent scan must hold at least what the anchor
# tag held. Replays against truncated history may lower it EXPLICITLY on the
# command line; CI never does.
DELIVERY_FLOOR = ANCHOR_DELIVERY

# Release artifacts live in a flat per-release file (<= v0.60 history) OR,
# from v0.61, one file per requirement under artifacts/release-vX.YY/ with a
# comments-only _release.yaml (#1059 — parallel lanes create files instead of
# appending to one). Comma-separated; both layouts are always scanned.
RELEASE_GLOB = (
    "artifacts/release-v*.yaml,"
    "artifacts/release-v*/*.yaml,"
    "artifacts/release-v*/*.yml"
)

# ---- Programme-artifact status legality (P-rules, #1133) --------------------
#
# RQ-62-ROADMAPGATE: R0-R10 are scoped to RELEASE_GLOB, so
# artifacts/verified-codegen-roadmap.yaml — 39 VCR-* artifacts, the entire
# North Star programme — was subject to NONE of them, and two of its
# artifacts (VCR-WCET-001/002) carried no `status` key at all: visible to
# rivet's ARTIFACT_FLOOR count, invisible to every rule, and silently
# dropped by any consumer filtering on status.
#
# Deliberately NOT a glob widening: release rules assume obligations the
# roadmap does not have (R7/R8 need `release:` matching the filename — 38
# of 39 roadmap items carry none by design until scoped; R4/R10 need a
# release window the roadmap has none of). Pointing them at the roadmap
# would produce false reds. What DOES generalize — measured true today for
# every artifact yaml in the repo — is the minimum the issue names:
#
#   P1: every artifact has a non-empty `status` key.
#   P2: the status is a legal lifecycle value. rivet does not enforce an
#       enum (generic-yaml source; its docs mark `status` optional), so
#       this pin is the only mechanical guard against a typo'd status —
#       which on the release side would silently move an artifact OUT of
#       CLAIMING and weaken R2 to nothing.
#   P0: the roadmap file itself must load and contribute artifacts — the
#       #1064 invisible-file shape, applied to the one file whose whole
#       purpose is recording programme status (a rename or restructure
#       must red here, never quietly exempt 39 artifacts again).
#
# P1/P2 scan EVERY artifact-bearing yaml directly under artifacts/ plus the
# release-v*/ dirs (release files included: R0-R10 never checked status
# LEGALITY, only status/evidence agreement). Since #1183 an artifact-less
# yaml is P4-red rather than skipped (measured: none exists; artifacts/ is an
# artifact namespace and a silently skipped file is the #1064 shape), a yaml
# the glob cannot see is P3-red, and the P-VACUOUS floor on artifacts checked
# is DERIVED from the release anchor (A3, see ANCHOR_TAG) instead of
# hand-pinned.
LIFECYCLE = frozenset(
    {"draft", "proposed", "approved", "implemented", "verified", "accepted"}
)
PROGRAMME_FILE = "artifacts/verified-codegen-roadmap.yaml"
PROGRAMME_GLOB = (
    "artifacts/*.yaml,"
    "artifacts/*.yml,"
    "artifacts/release-v*/*.yaml,"
    "artifacts/release-v*/*.yml"
)
# A3 (programme): derived, not pinned — what the anchor tag's tree held, less
# any DECLARED deletion (#1183).
PROGRAMME_FLOOR = ANCHOR_PROGRAMME - PROGRAMME_DELETED_SINCE_ANCHOR

# ---- Unscoped-artifact staleness (S-rules, #1085 / RQ-64-SCOPEGAP) ---------
#
# RQ-62-ROADMAPGATE widened the SCOPE (P1/P2 reach every artifact yaml) but
# not the OBLIGATIONS: an artifact with no `release:` — 293 of the 400 at
# authoring, across 25 topic files: the stakeholder/system/technical
# requirements, architecture, the verification measures, the gale/zephyr/
# loom integration records, the VCR roadmap — is checked for a legal status
# and NOTHING else. Measured consequence: figures the repo DERIVES and
# ratchets elsewhere (claims.yaml -> artifacts/status.json) were restated in
# those files as undated present-tense fact and rotted in place. `VG-002`,
# `ARCH-004`, `SWVER-005`, `TR-005` still said "188 Qed / 52 Admitted"
# (2026-03-17 numbers; the kernel recount is 630 / 2), `VER-001`/`VER-002`
# "39"/"95 Qed", and `VCR-REACH-002`'s TITLE asserted "1.6% AArch64
# acceptance" as if current after v0.63 published a ladder measuring 20.2 %
# on the reachable corpus. (The artifact's other named instance, `VG-009`,
# is NOT one: its only "1.6" is the substring of "41.6 %", a line-coverage
# figure explicitly "measured at v0.54.0" — a grep hit, not a stale claim.)
#
# THE DECISION, recorded so it is not re-litigated: an unscoped artifact is
# a RECORD. It may cite a measured, moving figure only AS HISTORY — in a
# sentence that says WHEN (a release version, an issue/PR number, an ISO
# date) — or it names the derivation (`artifacts/status.json`'s field, the
# script that emits it) instead of the number. Never an undated literal
# that continues to move. Rejected, with the measurement that rejected it:
#   * `release: backlog` on every unscoped artifact — mislabels the
#     requirements base (BR-001 is the trace root, not backlog work) and
#     buys no rule: every R-rule presumes a release window or evidence
#     scoping these items have none of, so each would need an exemption —
#     the false-red shape RQ-62-ROADMAPGATE already refused.
#   * "topic files are narrative; strip every number" — 104 of the 293
#     carry a figure token and most are load-bearing: threshold/ABI
#     constants in requirements ("at least 80%", "64 KiB") and the measured
#     results that ARE a verification record's content ("13/13",
#     "338/338"). Stripping evidence to prevent staleness is backwards.
#   * "pinned" read as EQUALITY with the live derivation (the CLAUDE.md
#     count-eq discipline) — every citing topic artifact becomes one more
#     LIVE file that must move with the number. RQ-64-FLOORPROSE's
#     correction (#1178) measured where v0.63's largest merge cost actually
#     sat: on the two LIVE files of the emulation floor (ci.yml,
#     claims.yaml), all four lane rebases — never on a dated artifact
#     transcript. Equality here would grow exactly that set. A record
#     dates; a pin lives in claims.yaml once — and FLOORPROSE's surviving
#     rule ("say 'at v0.63' beside it") is S1 stated for one file.
#
#   S1: a citation of a REPO-DERIVED moving count — `N Qed`, `N Admitted` /
#       `N admits`, the shape every measured instance took — in an unscoped
#       artifact's description or any prose-valued `fields:` entry (TR-005's
#       `verification-criteria` and VER-001/002's `steps.coverage` were
#       measured instances) must sit in a sentence carrying a temporal
#       anchor. The failure names the live
#       value from status.json so the reader sees the drift, but the VERDICT
#       is dated-or-not, never equality (see the third rejection).
#   S2: an unscoped artifact's TITLE — the surface every listing and query
#       renders, always read as present tense — may not carry an undated
#       measured figure: a percentage, an N/M ratio, or a count of a
#       derived/measured unit (`52 VFP/float admits`, `77 modules`).
#   Dated by construction, hence exempt: an artifact whose `release:` is a
#   version, and every artifact in a topic file whose NAME carries one
#   (`sys-verification-v0.60.yaml` records what was true at v0.60 exactly
#   as a release-v*/ file does). Release-scoped files are R7/R8's surface.
#   S-DRIFT: the figure citations scanned are pinned as an EQUALITY
#   (STALENESS_CITATIONS): below is lost reach (pattern rot, a file
#   invisible), above is a citation that landed without its same-PR
#   bump. A lower bound cannot see declared drifting (RQ-63-FLOOREQ).
#
# What S-rules do NOT judge, stated rather than silent: whether a dated
# figure is the RIGHT history; whether the anchor genuinely dates the
# figure beside it (an incidental `#NNN` in the same sentence passes — the
# 3-digit minimum only keeps ARM immediates like `#3`/`#16` from dating a
# sentence); and percentages in DESCRIPTIONS — a threshold ("shall achieve
# at least 80%") and a measurement are not mechanically separable, and the
# six threshold percentages in the requirements base would be false reds.
# Those stay human-reviewed; the one measured description-level acceptance
# figure (VCR-REACH-002) was already dated by its issue.
STALENESS_ANCHOR = re.compile(
    r"\bv\d+\.\d+(?:\.\d+)?\b"     # a release version
    r"|#\d{3,}\b"                    # an issue / PR number
    r"|\b20\d\d-\d\d-\d\d\b"       # an ISO date
)
DERIVED_FIGURES = (
    # (label, artifacts/status.json key, prose pattern)
    ("Qed", "rocq_qed", re.compile(r"\b\d[\d,]*\s?Qed\b")),
    ("Admitted", "rocq_admitted",
     re.compile(r"\b\d[\d,]*\s?(?:Admitted|admits?)\b")),
)
TITLE_FIGURE = re.compile(
    r"\d+(?:[.,]\d+)?\s?%"
    r"|\b\d+\s?/\s?\d+\b"
    r"|\b\d[\d,]*(?:\s+\S+){0,3}\s+(?:Qed|Admitted|admits?|modules?)\b"
)
TOPIC_FILE_VERSION = re.compile(r"v\d+\.\d+")
SENTENCE_BREAK = re.compile(r"(?<=[.!?])\s+(?=[^a-z\s])")
# Figure citations the live scan must find — an EQUALITY, red in BOTH
# directions (RQ-63-FLOOREQ: a lower bound cannot see declared drifting).
# Below: the scan lost reach — pattern rot, a file invisible to it. Above:
# a citation landed without its same-PR bump. Measured churn v0.56.0 ->
# v0.63.0: 30, 30, 30, 31, 31, 31, 31, 32 — two moves in seven release
# intervals — so equality costs a one-line bump every few releases. Move
# it in the PR that moves it; claims.yaml pins this line verbatim
# (SYNTH-STATUS-EVIDENCE-STALENESS-CITATIONS-1085) so every movement is
# a visible ledger diff, and pins that the `!=` check itself stays wired.
STALENESS_CITATIONS = 34

ARTIFACT_ID = re.compile(r"^(RQ-\d+-[A-Z0-9]+)\b")
PR_NUMBER = re.compile(r"\(#(\d+)\)")

# R4-issue / R10 (#1119): conventional-commit subjects. Only the SCOPE
# position (`fix(#1040): ...`) counts as a delivery CLAIM for an issue —
# it is a deliberate authoring position, not a mention. `Revert "fix(...)"`
# does not match (anchored), and a scopeless `fix: x` is out of scope.
CONVENTIONAL = re.compile(r"^([a-z]+)\(([^)]*)\)!?: ")
SCOPE_ISSUE = re.compile(r"^#(\d+)$")
# R10: subject types that deliver code, measured over first-parent history;
# everything else (plan/chore/docs/salvage/investigate/track) is process.
DELIVERY_TYPES = frozenset({"feat", "fix", "perf", "proof", "test"})
ID_ANYWHERE = re.compile(r"\bRQ-\d+-[A-Z0-9]+\b")
ISSUE_ANYWHERE = re.compile(r"#(\d+)\b")
RELEASE_VERSION = re.compile(r"release-v(\d+)\.(\d+)")

# R8: the artifact's own `release:` field — the side rivet's readiness query
# reads. vX.Y or vX.Y.Z; anything else is red, not skipped.
FIELD_VERSION = re.compile(r"^v(\d+)\.(\d+)(?:\.(\d+))?$")

# R7 escape hatch: `shipped-in` must at least be version-shaped, so
# `shipped-in: "yes"` cannot buy the exemption.
SHIPPED_IN_VERSION = re.compile(r"^v\d+\.\d+(?:\.\d+)?$")

# R9: crate SOURCE — the code-existence surface. Paths under crates/ whose
# components include a `tests` dir are integration tests the required Test
# job executes, i.e. gate-shaped, and are deliberately NOT matched.
def is_crate_source(path: str) -> bool:
    parts = path.split("/")
    return parts[0] == "crates" and "tests" not in parts[1:]


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
                    art.get("release"),
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
    """-> (kind, holds_or_None, path, literal). `manual:` evaluates to None
    (no signature); path/literal are None where inapplicable."""
    if done_when.startswith("contains:"):
        rest = done_when[len("contains:"):]
        path, sep, literal = rest.partition(":")
        if not sep or not literal:
            return ("malformed", None, None, None)
        f = root / path
        holds = f.is_file() and literal in f.read_text(
            encoding="utf-8", errors="replace")
        return ("contains", holds, path, literal)
    if done_when.startswith("file:"):
        path = done_when[len("file:"):].strip()
        return ("file", (root / path).exists(), path, None)
    if done_when.startswith("manual:"):
        reason = done_when[len("manual:"):].strip()
        return ("manual", None, None, None) if reason \
            else ("malformed", None, None, None)
    return ("malformed", None, None, None)


# ---- R7 git archaeology (#1085) ------------------------------------------


def _git(root: Path, *args: str):
    r = subprocess.run(
        ["git", "-C", str(root), *args], capture_output=True, text=True
    )
    return r.returncode, r.stdout


def git_history_state(root: Path) -> str:
    """'ok' | 'no-git' | 'shallow' — whether R7 archaeology can be trusted."""
    rc, out = _git(root, "rev-parse", "--is-shallow-repository")
    if rc != 0:
        return "no-git"
    return "shallow" if out.strip() == "true" else "ok"


def previous_release_tag(root: Path, version: tuple) -> str | None:
    """Highest vX.(Y-1).* tag, so evidence shipped in the previous minor's
    PATCH releases is caught too. None when no such tag is visible."""
    x, y = version
    if y == 0:
        return None
    rc, out = _git(root, "tag", "-l", f"v{x}.{y - 1}.*")
    if rc != 0:
        return None
    tags = []
    for t in out.split():
        m = re.fullmatch(rf"v{x}\.{y - 1}\.(\d+)", t)
        if m:
            tags.append((int(m.group(1)), t))
    return max(tags)[1] if tags else None


def introducing_commit(root: Path, kind: str, path: str,
                       literal: str | None) -> str | None:
    """Oldest FIRST-PARENT commit that introduced the done-when signature —
    for contains: the pickaxe over the literal, for file: the commit that
    added the path. None when the signature holds only uncommitted."""
    if kind == "contains":
        rc, out = _git(root, "log", "--first-parent", "--format=%H",
                       f"-S{literal}", "--", path)
    else:
        rc, out = _git(root, "log", "--first-parent", "--diff-filter=A",
                       "--format=%H", "--", path)
    commits = out.split()
    return commits[-1] if rc == 0 and commits else None


def landed_prs(fields: dict) -> set[str]:
    return set(re.findall(r"#(\d+)", str(fields.get("landed", ""))))


def release_window_subjects(root: Path, version: tuple):
    """(tag, first-parent subjects since the previous minor's highest tag),
    or (None, None) when underivable — no git, no tag visible. The caller
    reports the skip LOUDLY; a silent empty window would be the #1064
    quiet-pass shape for R4-issue/R10."""
    if git_history_state(root) != "ok":
        return None, None
    tag = previous_release_tag(root, version)
    if tag is None:
        return None, None
    rc, out = _git(root, "log", "--first-parent", "--format=%s",
                   f"{tag}..HEAD")
    if rc != 0:
        return None, None
    return tag, out.splitlines()


def check_programme(root: Path, programme_glob: str = PROGRAMME_GLOB,
                    floor: int = PROGRAMME_FLOOR):
    """P-rules (#1133 / RQ-62-ROADMAPGATE): every artifact in every
    artifact-bearing yaml under artifacts/ has a legal lifecycle status,
    and the programme roadmap file itself is visible to the scan.

    -> (files_scanned, artifacts_checked, missing, illegal, failures).
    Raises DuplicateKeyError like the release scan (same strict loader,
    same #1059 refusal)."""
    failures: list[str] = []
    paths = set()
    for pattern in programme_glob.split(","):
        paths.update(glob.glob(str(root / pattern.strip())))
    # P3 (#1183): every yaml under artifacts/, at ANY depth, must be one the
    # glob scans. A layout change that parks files where the glob does not
    # look shrinks the population silently — a SUM floor cannot see one
    # file's loss behind growth elsewhere, a per-file rule can. Measured at
    # authoring: 89 of 89 visible.
    art_dir = root / "artifacts"
    visible = {os.path.normpath(p) for p in paths}
    walked = {
        os.path.normpath(str(p)) for p in art_dir.rglob("*")
        if p.is_file() and p.suffix in (".yaml", ".yml")
    } if art_dir.is_dir() else set()
    for p in sorted(walked - visible):
        rel = os.path.relpath(p, root)
        failures.append(
            f"P3 {rel}: yaml under artifacts/ that PROGRAMME_GLOB does not "
            f"scan — invisible to every P-rule; widen the glob or move the "
            f"file, never let the population shrink quietly (#1183)"
        )
    files_scanned = 0
    checked = 0
    missing = 0
    illegal = 0
    roadmap_artifacts = 0
    roadmap_seen = False
    for p in sorted(paths):
        path = Path(p)
        if path.name == "_release.yaml":
            # Comments-only by contract; its shape is R0's surface.
            continue
        rel = path.relative_to(root).as_posix() if path.is_relative_to(root) \
            else path.name
        is_roadmap = rel == PROGRAMME_FILE
        if is_roadmap:
            roadmap_seen = True
        doc = yaml.load(path.read_text(encoding="utf-8"), Loader=StrictLoader)
        arts = [
            a for a in ((doc.get("artifacts") or []) if isinstance(doc, dict)
                        else [])
            if isinstance(a, dict) and "id" in a
        ]
        if not arts:
            # The roadmap contributing zero is P0 below; a release file is
            # R0's surface (load_release_artifacts). Anything else under
            # artifacts/ that parses to zero artifacts is P4 (#1183): the
            # #1064 invisible-file shape, red rather than skipped —
            # measured, no such file exists, so the rule costs nothing and
            # the first one to appear is caught.
            if is_roadmap or RELEASE_VERSION.search(rel):
                continue
            keys = (", ".join(map(str, doc.keys())) if isinstance(doc, dict)
                    else type(doc).__name__)
            failures.append(
                f"P4 {rel}: yaml under artifacts/ contributes ZERO artifacts "
                f"under `artifacts:` (top-level: {keys}) — the #1064 "
                f"invisible-file shape; an artifact file is red before it can "
                f"hide, never skipped (#1183)"
            )
            continue
        files_scanned += 1
        if is_roadmap:
            roadmap_artifacts = len(arts)
        for art in arts:
            checked += 1
            art_id = str(art["id"])
            if "status" not in art or not str(art.get("status") or "").strip():
                missing += 1
                failures.append(
                    f"P1 {art_id}: no `status` in {rel} — a missing status "
                    f"is unrepresentable in the lifecycle; rivet still "
                    f"counts the artifact (ARTIFACT_FLOOR) while every "
                    f"status-filtering consumer silently drops it (#1133)"
                )
            elif str(art["status"]) not in LIFECYCLE:
                illegal += 1
                failures.append(
                    f"P2 {art_id}: status {str(art['status'])!r} in {rel} "
                    f"is not a legal lifecycle value "
                    f"({'|'.join(sorted(LIFECYCLE))}) — rivet does not "
                    f"enforce this enum, and on the release side a typo'd "
                    f"status silently exits CLAIMING and defuses R2 (#1133)"
                )
    if not roadmap_seen:
        failures.append(
            f"P0 {PROGRAMME_FILE}: programme roadmap file not found by the "
            f"scan — renamed or moved, the 39-artifact North Star programme "
            f"is invisible to every rule again (#1133)"
        )
    elif roadmap_artifacts == 0:
        failures.append(
            f"P0 {PROGRAMME_FILE}: contributes ZERO artifacts under "
            f"`artifacts:` — the #1064 invisible-file shape on the "
            f"programme's single source of truth (#1133)"
        )
    if checked < floor:
        failures.append(
            f"P-VACUOUS: only {checked} artifacts status-checked "
            f"(floor {floor}, derived from the {ANCHOR_TAG} anchor less "
            f"{PROGRAMME_DELETED_SINCE_ANCHOR} declared deletions) — files "
            f"invisible to the scan, or an undeclared deletion; the floor "
            f"never comes down to pass (#1183)"
        )
    return files_scanned, checked, missing, illegal, failures


# ---- Release-anchored non-vacuity (A-rules, #1183) ------------------------


def anchor_delivery_count(root: Path, by_id, tag: str) -> int | None:
    """Id-first FIRST-PARENT delivery commits reachable from `tag` whose id is
    a release artifact in the tree at HEAD — the R4 scan, bounded at the
    anchor. None when git cannot list the tag's ancestry (the tag is absent,
    or beyond a shallow boundary)."""
    rc, out = _git(root, "log", "--first-parent", "--format=%s", tag)
    if rc != 0:
        return None
    return sum(
        1 for s in out.splitlines()
        if (m := ARTIFACT_ID.match(s)) and m.group(1) in by_id
    )


def anchor_programme_count(root: Path, tag: str) -> int | None:
    """Artifacts the P-scan finds in the tree AT `tag` — `git archive` of its
    artifacts/, run through the SAME glob, loader and filter as the live scan
    so that instrument rot shows as an inequality on a tree that has not
    changed. None when the tag's tree cannot be read."""
    r = subprocess.run(
        ["git", "-C", str(root), "archive", "--format=tar", tag, "artifacts"],
        capture_output=True,
    )
    if r.returncode != 0:
        return None
    with tempfile.TemporaryDirectory() as td:
        with tarfile.open(fileobj=io.BytesIO(r.stdout)) as tf:
            try:
                tf.extractall(td, filter="data")
            except TypeError:  # pragma: no cover - pre-3.12 tarfile
                tf.extractall(td)
        try:
            return check_programme(Path(td), floor=0)[1]
        except DuplicateKeyError:
            return None


def check_anchor(root: Path, by_id, live_delivery: int, live_programme: int,
                 window_label: str | None, tag: str = ANCHOR_TAG,
                 delivery: int = ANCHOR_DELIVERY,
                 programme: int = ANCHOR_PROGRAMME,
                 deleted: int = PROGRAMME_DELETED_SINCE_ANCHOR):
    """A0-A3 (#1183 / RQ-65-FLOORSHAPE) — see the ANCHOR_TAG comment block.

    -> (derived_delivery, derived_programme, lag, warnings, failures).
    `window_label` is the previous minor's tag the R4-issue/R10 window
    derived (None = underivable). Derived counts are None when git could not
    produce them; `lag` is how many minors the anchor trails the window (None
    when that cannot be decided). Every underivable input is a FAILURE, never
    a skip: a floor that cannot be re-derived is the vacuous case itself."""
    warnings: list[str] = []
    failures: list[str] = []
    state = git_history_state(root)
    if state != "ok":
        failures.append(
            f"A1 anchor {tag}: history is {state.upper()} — `git rev-parse "
            f"--is-shallow-repository` says the ancestry is truncated (or "
            f"there is no git at all), so no count over it is evidence; "
            f"fetch-depth: 0 (#1183)"
        )
    d = anchor_delivery_count(root, by_id, tag) if state != "no-git" else None
    p = anchor_programme_count(root, tag) if state != "no-git" else None
    if d is None:
        failures.append(
            f"A1 anchor {tag}: `git log --first-parent {tag}` failed — the "
            f"tag is not reachable (not fetched, or beyond a shallow "
            f"boundary), so the delivery population cannot be re-derived "
            f"(#1183)"
        )
    elif d != delivery:
        side = "BELOW" if d < delivery else "ABOVE"
        why = ("truncated history or instrument rot (ARTIFACT_ID / "
               "RELEASE_GLOB finds less than it did)" if d < delivery else
               "rewritten history, or an orphan commit acquired an artifact")
        failures.append(
            f"A1 anchor {tag}: {d} id-first delivery commits reachable from "
            f"the tag != pinned ANCHOR_DELIVERY {delivery} ({side} by "
            f"{abs(d - delivery)}) — {why}. This count is a CONSTANT until "
            f"the anchor moves; do not re-pin it to pass (#1183)"
        )
    if p is None:
        failures.append(
            f"A2 anchor {tag}: `git archive {tag} artifacts` failed or the "
            f"tree would not load — the programme population at the tag "
            f"cannot be re-derived (#1183)"
        )
    elif p != programme:
        side = "BELOW" if p < programme else "ABOVE"
        failures.append(
            f"A2 anchor {tag}: {p} artifacts in the tree at the tag != "
            f"pinned ANCHOR_PROGRAMME {programme} ({side} by "
            f"{abs(p - programme)}) — the tag's tree cannot change, so the "
            f"INSTRUMENT changed: PROGRAMME_GLOB, the loader or the artifact "
            f"filter finds a different population than when the anchor was "
            f"recorded (#1183)"
        )
    # A0 — the anchor is the window's previous tag, at most one minor behind.
    lag = None
    m_a = re.fullmatch(r"v(\d+)\.(\d+)\.\d+", tag)
    m_w = re.fullmatch(r"v(\d+)\.(\d+)\.\d+", window_label or "")
    if m_a is None:
        failures.append(
            f"A0 anchor {tag!r}: ANCHOR_TAG must be a vX.Y.Z release tag "
            f"(#1183)"
        )
    elif m_w is None:
        failures.append(
            f"A0 anchor {tag}: the release window's previous tag is "
            f"underivable ({window_label!r}), so the anchor's currency cannot "
            f"be decided — no git, tags not fetched, or no release directory "
            f"(#1183)"
        )
    elif m_a.group(1) != m_w.group(1):
        failures.append(
            f"A0 anchor {tag}: a different MAJOR than the window's previous "
            f"tag {window_label}; re-anchor (#1183)"
        )
    else:
        lag = int(m_w.group(2)) - int(m_a.group(2))
        if lag < 0:
            failures.append(
                f"A0 anchor {tag}: AHEAD of the window's previous tag "
                f"{window_label} — an anchor cannot precede the release it "
                f"anchors (#1183)"
            )
        elif lag >= 2:
            failures.append(
                f"A0 anchor {tag}: {lag} minors behind the window's previous "
                f"tag {window_label} — the anchor moves once per release and "
                f"this one was skipped; re-pin at {window_label} (#1183)"
            )
        elif lag == 1:
            nd = anchor_delivery_count(root, by_id, window_label) \
                if state == "ok" else None
            np_ = anchor_programme_count(root, window_label) \
                if state == "ok" else None
            warnings.append(
                f"ANCHOR-LAG: {tag} is one minor behind the window's previous "
                f"tag {window_label}; move it in the PR that OPENS this window (measured: moving it earlier reds A0) — "
                f'ANCHOR_TAG = "{window_label}" / ANCHOR_DELIVERY = '
                f"{nd if nd is not None else '?'} / ANCHOR_PROGRAMME = "
                f"{np_ if np_ is not None else '?'} / "
                f"PROGRAMME_DELETED_SINCE_ANCHOR = 0 (two minors is red, #1183)"
            )
    # A3 — the waiver channel cannot be standing.
    if deleted < 0:
        failures.append(
            f"A3: PROGRAMME_DELETED_SINCE_ANCHOR = {deleted} is not a "
            f"deletion count (#1183)"
        )
    elif deleted > 0 and live_programme >= programme:
        failures.append(
            f"A3: DEAD waiver — PROGRAMME_DELETED_SINCE_ANCHOR = {deleted} "
            f"while the live scan holds {live_programme} >= anchor "
            f"{programme}; a declaration the count does not need is a "
            f"standing licence, delete it (#1183)"
        )
    if live_delivery < delivery:
        # The same fact check() reports as VACUOUS under the derived
        # DELIVERY_FLOOR; named here so the anchor line is self-contained.
        failures.append(
            f"A3: live delivery scan {live_delivery} < anchor {delivery} — "
            f"history the anchor tag reaches is missing from HEAD's, or a "
            f"shipped release artifact was deleted (#1183)"
        )
    return d, p, lag, warnings, failures


def _prose_fields(fields, prefix: str = "fields"):
    """Every string under `fields:` with its dotted key path — S1 scans
    prose wherever an artifact keeps it."""
    out = []
    if isinstance(fields, dict):
        for k, v in fields.items():
            out.extend(_prose_fields(v, f"{prefix}.{k}"))
    elif isinstance(fields, list):
        for i, v in enumerate(fields):
            out.extend(_prose_fields(v, f"{prefix}[{i}]"))
    elif isinstance(fields, str):
        out.append((prefix, fields))
    return out


def _sentences(text: str) -> list[str]:
    flat = re.sub(r"\s+", " ", text).strip()
    return [s for s in SENTENCE_BREAK.split(flat) if s]


def _live_status(root: Path) -> dict:
    """artifacts/status.json — the claim-check-derived numbers. Read for the
    failure MESSAGE only (so the reader sees the drift); absence is not a
    verdict either way."""
    try:
        doc = json.loads((root / "artifacts" / "status.json")
                         .read_text(encoding="utf-8"))
        return doc if isinstance(doc, dict) else {}
    except (OSError, ValueError):
        return {}


# ---- RQ-64-FLOORPROSE (#910): a LIVE pinned value may not be restated in
# release-artifact prose ------------------------------------------------------
#
# The emulation floor is enforced as an EQUALITY between exactly TWO files:
# `.github/workflows/ci.yml` (`--exact-emulation-floor N`) and `claims.yaml`
# (SYNTH-ORACLE-CHECK-FLOORS-910-CI, which pins the ci.yml string verbatim).
# Both move together in the PR that moves the floor, and RQ-63-FLOOREQ made that
# an equality so neither can drift.
#
# A THIRD copy in an artifact's prose is not in that lockstep and nothing checks
# it, so it rots the moment the floor moves — silently, behind a green gate.
# That is the #910 class one level out from the gate itself.
#
# THE RULE IS ABOUT THE *LIVE* VALUE, NOT THE DIGITS. A SUPERSEDED floor quoted
# as dated history is legitimate and must stay legible: RQ-63-FLOOREQ's
# `verified-by` transcribes a red-first run at 324845 and says in as many words
# "The figures below are AT v0.63 — a transcript of what was executed then, not
# a statement about the current floor." A transcript of a past run cannot go
# stale. Only a restatement of the number that is live RIGHT NOW can, because it
# silently becomes wrong the next time the floor legitimately moves.
#
# NON-VACUITY: if the live floor cannot be derived from ci.yml, or the artifact
# glob matches nothing, that is a FAILURE and not a quiet pass — a rule that
# cannot see its subject must say so (#1113 / RQ-63-FLOOREQ).
LIVE_FLOOR_RE = re.compile(r"--exact-emulation-floor\s+(\d+)")


def check_live_floor_prose(root: Path) -> tuple[int, str | None, int, list[str]]:
    """Return (artifacts_scanned, live_floor, restatements, failures)."""
    ci = root / ".github" / "workflows" / "ci.yml"
    if not ci.is_file():
        return (0, None, 0, [
            "floor-prose: .github/workflows/ci.yml is missing, so the live "
            "floor cannot be derived and this rule cannot run — a rule that "
            "cannot see its subject FAILS rather than passing quietly"
        ])
    m = LIVE_FLOOR_RE.search(ci.read_text(encoding="utf-8", errors="replace"))
    if not m:
        return (0, None, 0, [
            "floor-prose: no `--exact-emulation-floor N` found in ci.yml. "
            "Either the gate was removed (which RQ-63-FLOOREQ forbids) or its "
            "spelling changed and THIS rule went blind; both are failures"
        ])
    live = m.group(1)

    scanned, hits = 0, []
    for path in sorted(root.glob("artifacts/release-v*/*.yaml")):
        scanned += 1
        text = path.read_text(encoding="utf-8", errors="replace")
        for lineno, line in enumerate(text.splitlines(), 1):
            if live in line:
                hits.append(f"{path.relative_to(root)}:{lineno}")

    fails: list[str] = []
    if scanned == 0:
        fails.append(
            "floor-prose: the artifacts/release-v*/ glob matched NO files, so "
            "nothing was scanned. A zero-population scan is pattern rot, not a "
            "clean tree"
        )
    if hits:
        fails.append(
            f"floor-prose: the LIVE enforced floor {live} is restated as a "
            f"literal in release-artifact prose at {', '.join(hits)}. That copy "
            f"is NOT in the ci.yml <-> claims.yaml lockstep, so it rots the next "
            f"time the floor legitimately moves and nothing would notice. Cite "
            f"the DERIVATION (`oracle_wiring_check.py`'s reported total) or "
            f"quote a SUPERSEDED value with its release, the way "
            f"RQ-63-FLOOREQ's transcript does — never the live number."
        )
    return (scanned, live, len(hits), fails)


def check_unscoped(root: Path, programme_glob: str = PROGRAMME_GLOB,
                   expected: int | None = STALENESS_CITATIONS):
    """S-rules (#1085 / RQ-64-SCOPEGAP): an artifact with no release is a
    RECORD — a moving repo-derived count it cites must be dated in the same
    sentence (S1), and its title may not carry an undated measured figure
    (S2). Version-named topic files and version-shaped `release:` fields
    are dated by construction; release-v*/ files are R7/R8's surface.
    `expected` is the declared citation count (None: not checked — a
    fixture); the live scan must EQUAL it.

    -> (unscoped_artifacts, citations_scanned, undated, failures).
    Raises DuplicateKeyError like the other scans (same strict loader)."""
    failures: list[str] = []
    live = _live_status(root)
    paths = set()
    for pattern in programme_glob.split(","):
        paths.update(glob.glob(str(root / pattern.strip())))
    unscoped = 0
    citations = 0
    undated = 0
    for p in sorted(paths):
        path = Path(p)
        if path.name == "_release.yaml":
            continue
        rel = path.relative_to(root).as_posix() if path.is_relative_to(root) \
            else path.name
        if RELEASE_VERSION.search(rel):
            continue
        file_dated = bool(TOPIC_FILE_VERSION.search(path.name))
        doc = yaml.load(path.read_text(encoding="utf-8"), Loader=StrictLoader)
        arts = [
            a for a in ((doc.get("artifacts") or []) if isinstance(doc, dict)
                        else [])
            if isinstance(a, dict) and "id" in a
        ]
        for art in arts:
            if FIELD_VERSION.match(str(art.get("release") or "").strip()):
                continue
            unscoped += 1
            if file_dated:
                continue
            art_id = str(art["id"])
            # -- S2: the title.
            title = str(art.get("title") or "")
            for m in TITLE_FIGURE.finditer(title):
                citations += 1
                if not STALENESS_ANCHOR.search(title):
                    undated += 1
                    failures.append(
                        f"S2 {art_id}: title carries the measured figure "
                        f"`{m.group(0)}` with no date in {rel} — a title is "
                        f"the surface every listing renders and is always "
                        f"read as present tense; date it in the title "
                        f"(vX.Y / #NNN / YYYY-MM-DD) or move the figure into "
                        f"a dated sentence (#1085)"
                    )
                    break
            # -- S1: description + every prose-valued field.
            units = [("description", str(art.get("description") or ""))]
            units.extend(_prose_fields(art.get("fields")))
            for where, text in units:
                for sentence in _sentences(text):
                    anchored = None
                    for _label, key, pat in DERIVED_FIGURES:
                        for m in pat.finditer(sentence):
                            citations += 1
                            if anchored is None:
                                anchored = bool(
                                    STALENESS_ANCHOR.search(sentence))
                            if anchored:
                                continue
                            undated += 1
                            live_val = live.get(key)
                            drift = (
                                f"; the live derivation is {live_val} "
                                f"(artifacts/status.json `{key}`)"
                                if live_val is not None else ""
                            )
                            failures.append(
                                f"S1 {art_id}: undated `{m.group(0)}` in "
                                f"{rel} ({where}) — a moving, repo-derived "
                                f"count restated as present-tense fact"
                                f"{drift}; date it in the same sentence "
                                f"(vX.Y / #NNN / YYYY-MM-DD) or name the "
                                f"derivation instead of the number (#1085)"
                            )
    if expected is not None and citations != expected:
        if citations < expected:
            failures.append(
                f"S-DRIFT: {citations} figure citations scanned across "
                f"{unscoped} unscoped artifacts, BELOW the declared "
                f"{expected} — the scan lost reach (pattern rot, or a "
                f"file invisible to it); the declaration never comes down "
                f"to pass without the reason written beside it (#1085)"
            )
        else:
            failures.append(
                f"S-DRIFT: {citations} figure citations scanned across "
                f"{unscoped} unscoped artifacts, ABOVE the declared "
                f"{expected} — a citation landed without its same-PR bump "
                f"of STALENESS_CITATIONS; move the declaration in the PR "
                f"that moved the count (#1085)"
            )
    return unscoped, citations, undated, failures


def check(root: Path, release_glob: str, subjects: list[str],
          delivery_floor: int, window_subjects: list[str] | str | None = "derive"):
    """`window_subjects` — the first-parent subjects of the current RELEASE
    WINDOW (since the previous minor's tag), R4-issue's and R10's scan
    surface. "derive" (the default, what CI runs) derives it from git in
    `root`; an explicit list replays a fixture; None means underivable —
    the scan SKIPS LOUDLY and the summary line says so."""
    failures: list[str] = []
    warnings: list[str] = []
    artifacts, bad_files = load_release_artifacts(root, release_glob)
    failures.extend(bad_files)
    by_id = {a[2]: a for a in artifacts}
    predicates_evaluated = 0

    # ---- Structural integrity (R5/R6, #1059) ------------------------------
    seen_ids: dict[str, Path] = {}
    for path, version, art_id, status, fields, links, release_field in artifacts:
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

    # ---- Path/field release agreement (R8, #1085) -------------------------
    for path, version, art_id, status, fields, links, release_field in artifacts:
        m = FIELD_VERSION.match(str(release_field or "").strip())
        if not m:
            failures.append(
                f"R8 {art_id}: `release:` field {release_field!r} in "
                f"{path.name} is missing or not vX.Y[.Z] — rivet's readiness "
                f"query reads this field; it must be a version"
            )
            continue
        fv = (int(m.group(1)), int(m.group(2)))
        patch = m.group(3)
        if fv == version:
            continue
        if (patch is not None and int(patch) >= 1
                and fv == (version[0], version[1] - 1)):
            # The one STATED allowance: a PATCH release of the previous
            # minor, written up in the file of the minor under development
            # (the 6 measured v0.56.1/v0.56.2-in-release-v0.57.yaml cases).
            continue
        if fv > version:
            failures.append(
                f"R8 {art_id}: `release: {release_field}` parked in "
                f"{path.name} — this checker version-gates by PATH, so the "
                f"artifact is EXEMPT from every >= v0.60 rule while rivet "
                f"counts it in {release_field}'s scope: a silent version-"
                f"gate bypass, not a cosmetic mismatch"
            )
        else:
            failures.append(
                f"R8 {art_id}: `release: {release_field}` disagrees with "
                f"{path.name} and is not a patch of the previous minor — "
                f"the path (checker) and the field (rivet) name different "
                f"releases"
            )

    # ---- Declared-evidence half (R1/R2/R3 + R9 + R7) ----------------------
    r7_checked = 0
    r7_skipped = 0
    git_state: str | None = None  # probed lazily, once
    prev_tags: dict[tuple, str | None] = {}
    for path, version, art_id, status, fields, _links, _release in artifacts:
        done_when = fields.get("done-when")
        if done_when is None:
            if version >= DECLARE_SINCE:
                failures.append(
                    f"R1 {art_id}: no `done-when` in {path.name} — declare the "
                    f"machine signature of done, or `manual: <reason>`"
                )
            continue
        kind, holds, dw_path, dw_literal = evaluate(str(done_when), root)
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

        # R9 (#1085): under a CLAIMING status, a signature into crate SOURCE
        # only proves code exists — it cannot fail on the failure the
        # artifact defines for itself. Point it at the gate instead, or
        # write the basis for why code-existence IS the outcome.
        if (status in CLAIMING and kind in ("contains", "file")
                and is_crate_source(dw_path)
                and not str(fields.get("verified-by", "")).strip()):
            failures.append(
                f"R9 {art_id}: status `{status}` on a code-existence "
                f"done-when into crate source ({dw_path}) — a predicate that "
                f"cannot fail on the artifact's own definition of failure is "
                f"not a predicate (#1090); re-point it at the gate that "
                f"exercises the outcome, or write `verified-by` saying why "
                f"code-existence genuinely IS the outcome here"
            )

        # R7 (#1085): evidence must belong to the release. Only a signature
        # that HOLDS has an introduction to date; archaeology needs full git
        # history and tags, and every unverifiable case SKIPS LOUDLY (the CI
        # summary grep pins the skip count at zero).
        if kind in ("contains", "file") and holds is True:
            if git_state is None:
                git_state = git_history_state(root)
            if git_state != "ok":
                r7_skipped += 1
                warnings.append(
                    f"R7-SKIP {art_id}: {git_state} at {root} — evidence-"
                    f"release scoping NOT verified for {done_when!r}"
                )
                continue
            if version not in prev_tags:
                prev_tags[version] = previous_release_tag(root, version)
            prev_tag = prev_tags[version]
            if prev_tag is None:
                r7_skipped += 1
                warnings.append(
                    f"R7-SKIP {art_id}: no v{version[0]}.{version[1] - 1}.* "
                    f"tag visible (tags not fetched?) — evidence-release "
                    f"scoping NOT verified"
                )
                continue
            intro = introducing_commit(root, kind, dw_path, dw_literal)
            if intro is None:
                r7_skipped += 1
                warnings.append(
                    f"R7-SKIP {art_id}: signature holds on the tree but no "
                    f"first-parent commit introduces it (uncommitted work?) "
                    f"— evidence-release scoping NOT verified"
                )
                continue
            r7_checked += 1
            rc, _ = _git(root, "merge-base", "--is-ancestor", intro, prev_tag)
            if rc == 0:
                shipped = str(fields.get("shipped-in", "")).strip()
                if not shipped:
                    failures.append(
                        f"R7 {art_id}: done-when evidence was introduced by "
                        f"{intro[:9]}, an ANCESTOR of {prev_tag} — it shipped "
                        f"in a PREVIOUS release, so this artifact is "
                        f"mis-scoped; either move it or declare "
                        f"`shipped-in: <version>` with the reason written "
                        f"beside it (#1085)"
                    )
                elif not SHIPPED_IN_VERSION.match(shipped):
                    failures.append(
                        f"R7 {art_id}: `shipped-in: {shipped!r}` is not "
                        f"version-shaped (vX.Y[.Z]) — the escape hatch names "
                        f"WHICH release delivered the evidence"
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
        _, _, _, status, fields, _links, _release = by_id[art_id]
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

    # ---- Issue-anchored delivery claims (R4-issue) + attribution floor
    # ---- (R10) — both #1119, both scoped to the release window ------------
    if window_subjects == "derive":
        # #1152: the window belongs to the release BEING CUT, not to the
        # highest release DIRECTORY present. Every release here pre-scopes its
        # successor (that is how a deferral gets recorded instead of
        # vanishing), so taking the max blindly made `release-v0.63/` the
        # window's anchor while v0.62 was still uncut — its predecessor tag
        # v0.62.0 does not exist, the window became underivable, and R4-issue
        # and R10 STOPPED SCANNING during exactly the run-up to a tag.
        # Measured: hiding the pre-scoped directory restored
        # "1 delivery-shaped commits since v0.61.0"; restoring it re-skipped.
        #
        # So: walk release versions high-to-low and take the first whose
        # window actually derives. A pre-scoped future release no longer
        # perturbs it; the genuinely underivable cases the docstring names
        # (no git, no tag visible) still skip loudly, because none of the
        # candidates will derive either.
        candidates = sorted({a[1] for a in artifacts}, reverse=True)
        window_label, window_subjects = None, None
        for cand in candidates:
            if cand <= (0, 0):
                continue
            lbl, subj = release_window_subjects(root, cand)
            if lbl is not None:
                window_label, window_subjects = lbl, subj
                break
    else:
        window_label = "(replayed window)" if window_subjects is not None \
            else None

    # fields.issue -> holder artifacts (several releases may hold one issue).
    issue_holders: dict[str, list] = {}
    for a in artifacts:
        num = str((a[4] or {}).get("issue", "")).strip().lstrip("#")
        if num.isdigit():
            issue_holders.setdefault(num, []).append(a)
    # Every PR number any artifact's landed:/verified-by: prose names — the
    # R10 attribution surface that greens eefa19ef AFTER the #1120 flip
    # wrote `landed: PR #1112` down.
    acknowledged_prs: set[str] = set()
    for a in artifacts:
        for field in ("landed", "verified-by"):
            acknowledged_prs.update(
                re.findall(r"#(\d+)", str((a[4] or {}).get(field, ""))))

    issue_delivery_hits = 0
    window_delivery = 0
    window_attributed = 0
    if window_subjects is None:
        warnings.append(
            "WINDOW-SKIP: release window not derivable (no git, or the "
            "previous minor's tag is not visible) — R4-issue and R10 were "
            "NOT checked; the CI grep on `status-evidence-window:` turns "
            "this into a red")
    else:
        for subject in window_subjects:
            m = CONVENTIONAL.match(subject)
            if not m:
                continue
            # -- R4-issue: the SCOPE names an issue -> a delivery claim.
            sm = SCOPE_ISSUE.match(m.group(2))
            if sm and sm.group(1) in issue_holders:
                holders = issue_holders[sm.group(1)]
                best = max(h[1] for h in holders)
                best_holders = [h for h in holders if h[1] == best]
                if len(best_holders) > 1:
                    warnings.append(
                        f"WARN: issue-anchored delivery commit {subject!r} "
                        f"names issue #{sm.group(1)}, held by "
                        f"{', '.join(h[2] for h in best_holders)} — "
                        f"ambiguous, R4-issue will not guess (R10 "
                        f"attribution still applies)")
                else:
                    _, _, art_id, status, fields, _links, _release = \
                        best_holders[0]
                    issue_delivery_hits += 1
                    prs = PR_NUMBER.findall(subject)
                    pr = prs[-1] if prs else None
                    if (status not in CLAIMING
                            and not (pr is not None
                                     and pr in landed_prs(fields))):
                        key = (art_id, pr or subject)
                        if key not in flagged:
                            flagged.add(key)
                            failures.append(
                                f"R4 {art_id}: issue-anchored delivery "
                                f"commit on main "
                                f"({subject.split(':')[0]}: → issue "
                                f"#{sm.group(1)}"
                                f"{f' / PR #{pr}' if pr else ''}) but "
                                f"status is `{status}` and `landed:` does "
                                f"not acknowledge it — the #1119 blind "
                                f"spot; flip the status or record the "
                                f"increment"
                            )
            # -- R10: every delivery-typed commit must be attributable.
            if m.group(1) not in DELIVERY_TYPES:
                continue
            window_delivery += 1
            if (set(ID_ANYWHERE.findall(subject)) & set(by_id)
                    or set(ISSUE_ANYWHERE.findall(subject))
                    & set(issue_holders)):
                window_attributed += 1
                continue
            prs = PR_NUMBER.findall(subject)
            if prs and prs[-1] in acknowledged_prs:
                window_attributed += 1
                continue
            failures.append(
                f"R10: delivery-shaped commit in the release window is "
                f"attributable to NO release artifact: {subject!r} — no "
                f"known artifact id or issue number in the subject, and no "
                f"artifact's `landed:`/`verified-by:` names its PR (#1119: "
                f"work landed, every artifact silent). Name the artifact "
                f"in a `landed:` entry, or create the artifact this work "
                f"belongs to"
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

    return (artifacts, predicates_evaluated, delivery_hits, warnings,
            failures, r7_checked, r7_skipped,
            issue_delivery_hits, window_delivery, window_attributed,
            window_label)


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
    # A subjects FILE has no git window behind it: R4-issue/R10 then scan
    # the provided subjects as the window (a replay is by construction the
    # window under study). The in-repo run derives the real window.
    window = subjects if args.subjects_file else "derive"
    try:
        (artifacts, preds, hits, warnings, failures, r7_checked, r7_skipped,
         issue_hits, window_delivery, window_attributed, window_label) = \
            check(args.root, args.release_glob, subjects,
                  args.delivery_floor, window_subjects=window)
        (p_files, p_checked, p_missing, p_illegal, p_failures) = \
            check_programme(args.root)
        (s_unscoped, s_citations, s_undated, s_failures) = \
            check_unscoped(args.root)
        (fp_scanned, fp_live, fp_hits, fp_failures) = \
            check_live_floor_prose(args.root)
        # A-rules (#1183): the release anchor is a statement about THIS
        # repository's history; a subjects-file replay has none behind it.
        if args.subjects_file:
            a_delivery = a_programme = a_lag = None
            a_warnings, a_failures = [], []
            anchor_skipped = True
        else:
            (a_delivery, a_programme, a_lag, a_warnings, a_failures) = \
                check_anchor(args.root, {a[2] for a in artifacts}, hits,
                             p_checked, window_label)
            anchor_skipped = False
    except DuplicateKeyError as e:
        print(f"FAIL: duplicate-key defect in a release file (#1059): {e}")
        return 1
    failures = failures + p_failures + s_failures + fp_failures + a_failures
    warnings = warnings + a_warnings

    for w in warnings:
        print(w)
    for f in failures:
        print(f"FAIL {f}")
    files = len({a[0] for a in artifacts})
    print(
        f"status-evidence: {len(artifacts)} artifacts across {files} release "
        f"files, {hits} delivery commits matched, {preds} done-when "
        f"predicates evaluated, {r7_checked} release-scope archaeology "
        f"checks ({r7_skipped} skipped), {len(failures)} failures"
    )
    print(
        f"programme-status: {p_checked} artifacts across {p_files} artifact "
        f"files status-checked, {p_missing} missing status, {p_illegal} "
        f"illegal status"
    )
    print(
        f"programme-staleness: {s_unscoped} unscoped artifacts, "
        f"{s_citations} figure citations scanned, {s_undated} undated"
    )
    print(
        f"floor-prose: {fp_scanned} release artifacts scanned, live floor "
        f"{fp_live if fp_live is not None else 'UNDERIVABLE'} restated "
        f"{fp_hits} times"
    )
    if anchor_skipped:
        print("status-evidence-anchor: SKIPPED — subjects-file replay has no "
              "history to anchor (#1183)")
    else:
        print(
            f"status-evidence-anchor: {ANCHOR_TAG} — "
            f"{a_delivery if a_delivery is not None else 'UNDERIVABLE'} "
            f"delivery commits (pinned {ANCHOR_DELIVERY}), "
            f"{a_programme if a_programme is not None else 'UNDERIVABLE'} "
            f"artifacts (pinned {ANCHOR_PROGRAMME}), lag "
            f"{a_lag if a_lag is not None else 'UNDERIVABLE'}"
        )
    if window_label is None:
        print("status-evidence-window: SKIPPED — release window not "
              "derivable (#1119)")
    else:
        print(
            f"status-evidence-window: {window_delivery} delivery-shaped "
            f"commits since {window_label} — {window_attributed} attributed, "
            f"{issue_hits} issue-anchored delivery claims"
        )
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
