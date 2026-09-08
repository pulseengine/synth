#!/usr/bin/env python3
"""Unit tests for scripts/status_evidence_check.py (RQ-60-FLIPCOUPLE, #1064).

The gate that polices the statuses does not get to be the unchecked one —
six releases running found the defect in checking machinery, so this suite
does two things on every CI run:

1. THE SEVEN-INSTANCE REPLAY. Each of the seven measured misses that
   motivated the gate is reconstructed from the REAL repo state at the
   moment it happened — the artifact's actual status (read from
   `git show <merge>:artifacts/release-v*.yaml` at authoring and pinned
   here) and the actual delivery-commit subject on main — and the gate must
   flag it with the SPECIFIC rule that claims to cover it. A gate that
   would not have caught the measurement that motivated it has not
   addressed it.

   For the two instances whose catch depends on the `done-when` declaration
   this change introduces (RQ-60-CANARY / R3, RQ-60-VFPPRESSURE-B / R2),
   the fixture carries the declaration AS NOW WRITTEN in
   artifacts/release-v0.60.yaml over the historical status — i.e. the
   replay asks "would the mechanism, as landed, have flagged it", which is
   the honest question (had the mechanism existed, R1 would have forced the
   declaration into the PR that created the artifact).

2. GREEN CONTROLS. Every replay has a paired fixed state that must PASS,
   because a gate that reds on the fix too is noise, and noise gets routed
   around (#923).

3. THE #1059 SPLICE REPLAY (RQ-60-ARTIFACTSPLIT). Both defects the v0.59
   hand-merged conflict resolution actually produced are reconstructed
   byte-shape-for-byte-shape — the duplicate `issue:` key, and the new
   artifact spliced INTO a sibling's mapping so the sibling silently lost
   its `derives-from` trace link — and the gate must red on each (strict
   loader / R5). Plus controls for the per-requirement release-v*/
   directory layout that removes the conflict surface itself.

4. THE #1085 EVIDENCE-SCOPING RULES (RQ-61-EVIDENCE). Each of the three
   instances found by USING the gate during the v0.60 cut is replayed:
   R7 — RQ-60-CANARY's evidence committed BEFORE the previous release's
   tag (real git fixture, real tag, real ancestry), with the
   `shipped-in:` escape hatch as the green control, exactly as it stands
   on main; R8 — the six measured patch-park mismatches
   (v0.56.1/v0.56.2 in release-v0.57.yaml) as the STATED allowance, and
   the never-hit harmful direction (a pre-v0.60 file smuggling
   `release: v0.60` past every version-gated rule) as the red; R9 — the
   RQ-60-A64IMPORT shape (claiming status on a crates/** code-existence
   predicate) red, both #1090 correction forms green. R7's loud-skip
   contract (no git / no tag / uncommitted signature warns `R7-SKIP` and
   counts in the summary, never passes silently) is pinned here too.

5. THE #1119 R4-BLIND-SPOT REPLAY (RQ-61-R4BLIND). Both measured
   conventional-commit delivery subjects that R4's prefix anchor could not
   see are replayed verbatim — b4860e4e (`fix(#1040): ...`, resolved to
   RQ-61-A32RELOC through `fields.issue` in the SCOPE position → R4 red)
   and eefa19ef (`fix(oracle): #1104 ...`, whose subject names neither the
   artifact nor its issue #1113 and is caught by R10's window attribution
   floor instead) — plus the negative direction the artifact demands:
   an id MENTION (`fix(rivet): ... RQ-61-VCLOSURE's ...`, live commit
   0cb36bc7) is attribution, never a delivery claim; a DESCRIPTION-position
   issue reference never resolves; a revert does not match; ambiguity
   warns instead of guessing; and the underivable window skips loudly.

Run: python3 scripts/test_status_evidence_check.py
Mutation-verified at authoring (transcript in the RQ-60-FLIPCOUPLE PR):
disabling each of R1/R2/R3/R4 and the duplicate-key strictness kills at
least one test. Re-verified for RQ-60-ARTIFACTSPLIT: disabling each of
R5/R6, the _release.yaml comments-only rule, the per-file R0, and the
full-path version derivation kills at least one test. Re-verified for
RQ-61-EVIDENCE (#1085): disabling each of R7 (the ancestor check), R8
(both directions), R9, and the R7-SKIP warning kills at least one test.
Re-verified for RQ-61-R4BLIND (#1119): neutering the SCOPE_ISSUE matcher
kills the b4860e4e replay + the ambiguity control; emptying DELIVERY_TYPES
kills the eefa19ef replay.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
import warnings
from pathlib import Path

# TemporaryDirectory's implicit-cleanup warning is noise here: fixtures live
# until process exit by design (a test may hold several), and the dirs ARE
# cleaned. Nothing else is filtered.
warnings.filterwarnings("ignore", category=ResourceWarning)

sys.path.insert(0, str(Path(__file__).resolve().parent))

from status_evidence_check import (  # noqa: E402
    ANCHOR_DELIVERY,
    ANCHOR_PROGRAMME,
    ANCHOR_TAG,
    PROGRAMME_DELETED_SINCE_ANCHOR,
    PROGRAMME_FLOOR,
    RELEASE_GLOB,
    STALENESS_CITATIONS,
    RELEASE_VERSION,
    REPO_ROOT,
    DuplicateKeyError,
    StrictLoader,
    anchor_delivery_count,
    anchor_programme_count,
    check,
    check_anchor,
    check_live_floor_prose,
    check_programme,
    check_unscoped,
    first_parent_subjects,
    git_history_state,
    load_release_artifacts,
    release_window_subjects,
)
import status_evidence_check as sec  # noqa: E402
import yaml  # noqa: E402
import re  # noqa: E402
from unittest import mock  # noqa: E402

# --------------------------------------------------------------------------
# Real first-parent commit subjects from main (verbatim), one per measured
# Direction-A instance that had an id-first delivery commit.
# --------------------------------------------------------------------------
SUBJ_TIERCENSUS = (
    "RQ-59-TIERCENSUS (#1021): 52 of 80 proved rules sit above an encoder "
    "expansion — unguarded clobber set is {Popcnt/R11 (#1021, fix #1039 "
    "pending)} + {i64 shifts' amount clobber (#1048, NEW, "
    "execution-confirmed)} (#1047)"
)
SUBJ_GLOBALINIT = (
    "RQ-59-GLOBALINIT (#1052): ARM relocatable path REFUSES global "
    "initializers it does not materialize — the fourth silent drop, plus "
    "teeth for the harness that was green over it (#1058)"
)
SUBJ_PARTIALCENSUS = (
    "RQ-59-PARTIALCENSUS (#1017): census over the full decline set — 89% "
    "skip-only, but the median blocked module loses a quarter of its "
    "functions, not one (#1051)"
)
SUBJ_A64IMPORT = (
    "RQ-60-A64IMPORT (VCR-REACH-002 inc. 1): aarch64 import dispatch — "
    "SHN_UNDEF externals, the ARM #197 contract ported. Refs #1017, "
    "Refs #242 (#1071)"
)
SUBJ_VFPPRESSURE = (
    "RQ-60-VFPPRESSURE increment 1: AEABI-routed i64-f32 conversions on "
    "single-precision FPU targets - Refs #1069, Refs #869 (#1073)"
)
# Non-delivery subjects that must NOT trip the scan (measured convention:
# plan/chore/salvage commits never start with the artifact id).
SUBJ_NOISE = [
    "plan(v0.59): add RQ-59-POPCNT (#1021) and RQ-59-TIERCENSUS — a proof "
    "sitting above a defective expansion (#1030)",
    "chore(rivet): RQ-59-MEASURE and RQ-59-WCETI64 are implemented (#1027)",
    "salvage(#242): RQ-59-CRSWEEP dispositions — 10 stale, 1 CONFIRMED "
    "STILL REAL (CR-H7 / #1021) (#1031)",
]

# --------------------------------------------------------------------------
# #1119 (RQ-61-R4BLIND): the two measured conventional-commit delivery
# subjects R4's prefix anchor was blind to, verbatim from main, plus the
# live id-mention commit that must stay green.
# --------------------------------------------------------------------------
SUBJ_A32RELOC_1116 = (
    "fix(#1040): A32 BL sites carry R_ARM_CALL with a -8 addend — a real "
    "linker turned the pre-fix call into a plain branch to garbage (#1116)"
)
SUBJ_ORACLEFLOOR_1112 = (
    "fix(oracle): #1104 shadowed the aarch64 builder guard and left its "
    "oracle pinned to the superseded wording (#1112)"
)
SUBJ_UNRED_1118 = (
    "fix(rivet): un-red main's R4 — RQ-61-VCLOSURE's `landed:` named the "
    "ISSUE, not the PR (#1118)"
)


def art(art_id, status, fields=None, links=None, issue="#1064", release=None):
    """A schema-complete release artifact. R5 (#1059) demands links + issue
    of every real artifact, so the fixtures carry them by default; a test
    that exercises R5 itself passes links=[] or issue=None explicitly.
    `release` left None is stamped from the file's own version by
    Fixture.release(), so only R8's tests (#1085) pass it explicitly."""
    a = {"id": art_id, "type": "system-req", "title": "t", "status": status,
         "links": ([{"type": "derives-from", "target": "BR-001"}]
                   if links is None else links)}
    if release is not None:
        a["release"] = release
    f = dict(fields or {})
    if issue is not None:
        f.setdefault("issue", issue)
    if f:
        a["fields"] = f
    return a


class Fixture:
    """A temp repo root with release files, evidence files and subjects."""

    def __init__(self):
        self._td = tempfile.TemporaryDirectory()
        self.root = Path(self._td.name)
        (self.root / "artifacts").mkdir()

    def release(self, name, artifacts, stamp=True):
        """`name` may be a flat file (release-v0.60.yaml) or a path inside
        the per-requirement layout (release-v0.61/RQ-61-FOO.yaml). Unless
        stamp=False, artifacts without an explicit `release:` get the
        file's own version — matching every artifact on shipped history —
        so R8 (#1085) tests must opt out or pass release= explicitly."""
        p = self.root / "artifacts" / name
        p.parent.mkdir(parents=True, exist_ok=True)
        m = RELEASE_VERSION.search(name)
        if stamp and m:
            for a in artifacts:
                if isinstance(a, dict) and "release" not in a:
                    a["release"] = f"v{m.group(1)}.{m.group(2)}"
        p.write_text(yaml.safe_dump({"artifacts": artifacts}), encoding="utf-8")
        return p

    def raw(self, name, text):
        """A release file written VERBATIM — for the byte-shape replays
        (duplicate key, splice) that safe_dump could never produce."""
        p = self.root / "artifacts" / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        return p

    def evidence(self, rel, content):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
        return p

    def git(self, *args):
        """Run git in the fixture root — R7 (#1085) archaeology needs a
        real repo with real ancestry; identity/signing pinned inline so
        the fixture never touches the host's config."""
        subprocess.run(
            ["git", "-C", str(self.root), "-c", "user.name=fixture",
             "-c", "user.email=fixture@test", "-c", "commit.gpgsign=false",
             "-c", "tag.gpgsign=false", *args],
            check=True, capture_output=True,
        )

    def run(self, subjects, floor=0, window=None):
        """`window` is the release-window subject list for R4-issue/R10
        (#1119). Fixtures default to None — the loud-skip shape — so every
        pre-#1119 test is unaffected; window tests pass theirs explicitly."""
        return check(self.root, RELEASE_GLOB, subjects, floor,
                     window_subjects=window)


def fails(result):
    return result[4]


def has(result, needle):
    return any(needle in f for f in fails(result))


class ReplaySevenInstances(unittest.TestCase):
    """One test per measured miss. Status values are the REAL historical
    ones (verified against `git show` at authoring; commits named per case).
    """

    # -- Direction A: stale `proposed` over shipped code -------------------

    def test_1_tiercensus_1047(self):
        # d656fb8a merged #1047; release-v0.59.yaml still said `proposed`.
        #
        # STAGE 1 — the state as it actually was: the file carried its
        # requirements under the NON-SCHEMA top-level keys rivet silently
        # skipped (#1064: `metadata:`/`requirements:`, no `artifacts:`), so
        # the stale status inside was unfalsifiable. R0 reds on the file.
        fx = Fixture()
        p = fx.root / "artifacts" / "release-v0.59.yaml"
        p.write_text(
            "metadata:\n  release: v0.59\nrequirements:\n"
            "  - id: RQ-59-TIERCENSUS\n    status: proposed\n",
            encoding="utf-8",
        )
        r = fx.run([SUBJ_TIERCENSUS])
        self.assertTrue(has(r, "R0 release-v0.59.yaml"), fails(r))
        # STAGE 2 — with only the schema fix applied (#1065's `artifacts:`
        # key), the historical status becomes falsifiable and R4 fires.
        fx.release("release-v0.59.yaml", [art("RQ-59-TIERCENSUS", "proposed")])
        r = fx.run([SUBJ_TIERCENSUS])
        self.assertTrue(has(r, "R4 RQ-59-TIERCENSUS"), fails(r))
        # Green control: the (eventual, hand-made) flip passes.
        fx.release("release-v0.59.yaml", [art("RQ-59-TIERCENSUS", "implemented")])
        self.assertEqual(fails(fx.run([SUBJ_TIERCENSUS])), [])

    def test_2_globalinit_1058(self):
        # e1a7b57d merged #1058; status was `proposed`. (The file was in
        # the #1064 invisible shape here too — test_1 carries the two-stage
        # demonstration for the class; this pins the R4 half.)
        fx = Fixture()
        fx.release("release-v0.59.yaml", [art("RQ-59-GLOBALINIT", "proposed")])
        r = fx.run([SUBJ_GLOBALINIT])
        self.assertTrue(has(r, "R4 RQ-59-GLOBALINIT"), fails(r))

    def test_3_partialcensus_1051(self):
        # f1e2e7bc IS the artifact's own delivery PR and it did not flip
        # its own status — the same red, caught on the PR run itself.
        fx = Fixture()
        fx.release("release-v0.59.yaml", [art("RQ-59-PARTIALCENSUS", "proposed")])
        r = fx.run([SUBJ_PARTIALCENSUS])
        self.assertTrue(has(r, "R4 RQ-59-PARTIALCENSUS"), fails(r))

    def test_4_canary_no_commit_names_it(self):
        # The work shipped as "VCR-TIER-001 increment 1" (#1061), so NO
        # commit subject names RQ-60-CANARY and R4 is structurally blind —
        # this is the instance only the declared-evidence half can catch.
        # At 3267e0d3 the artifact said `proposed` while its own
        # done-signature (expansion_scratch_contract, landed in #1061) was
        # already on main.
        fx = Fixture()
        fx.evidence(
            "crates/synth-backend/src/arm_encoder.rs",
            "pub fn expansion_scratch_contract(op: &ArmOp) {}\n",
        )
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-CANARY", "proposed",
            {"done-when": "contains:crates/synth-backend/src/arm_encoder.rs:"
                          "expansion_scratch_contract"},
        )])
        r = fx.run(["VCR-TIER-001 increment 1: canary gate over pseudo-op "
                    "encoder expansions (#1061)"])
        self.assertTrue(has(r, "R3 RQ-60-CANARY"), fails(r))
        # Green control: the flip is consistent with the evidence. The
        # done-when here is the #1090 CORRECTED one (the gate's non-vacuity
        # floor) — the original `contains:crates/...:expansion_scratch_
        # contract` is exactly the code-existence shape R9 (#1085) now
        # reds under a claiming status, which R9CrateSource pins.
        fx.evidence("scripts/repro/expansion_canary_gate_1021.py",
                    "assert emulations >= 1200\n")
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-CANARY", "implemented",
            {"done-when": "contains:scripts/repro/"
                          "expansion_canary_gate_1021.py:emulations >= 1200"},
        )])
        self.assertEqual(fails(fx.run([]))[0:], [])

    def test_5_a64import_1071(self):
        # f8036ec1 merged #1071; status was `proposed`.
        fx = Fixture()
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-A64IMPORT", "proposed",
            {"done-when": "manual: replay fixture"},
        )])
        r = fx.run([SUBJ_A64IMPORT])
        self.assertTrue(has(r, "R4 RQ-60-A64IMPORT"), fails(r))

    def test_6_vfppressure_1073_landed_silently(self):
        # e6a3b27a merged #1073 (increment 1); the artifact said nothing.
        # The FIX here is not a status flip (the DoD is 5-of-5 cascade
        # stages, NOT met by increment 1) but the `landed:` acknowledgment —
        # the machine-readable "increment landed, outcome does not yet hold".
        manual = ("manual: 5-of-5 cascade stages export in jess's "
                  "fused-image run")
        fx = Fixture()
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-VFPPRESSURE", "proposed", {"done-when": manual},
        )])
        r = fx.run([SUBJ_VFPPRESSURE])
        self.assertTrue(has(r, "R4 RQ-60-VFPPRESSURE"), fails(r))
        # Green control: acknowledging the increment (today's main state).
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-VFPPRESSURE", "proposed",
            {"done-when": manual, "landed": "#1073"},
        )])
        self.assertEqual(fails(fx.run([SUBJ_VFPPRESSURE])), [])

    # -- Direction B: premature `implemented` ------------------------------

    def test_7_vfppressure_premature_implemented(self):
        # The reverted flip (#1074): status set to `implemented` on "the PR
        # merged", with the artifact's own DoD (external, jess-run) unmet
        # and NO written basis. A manual done-when under a claiming status
        # without `verified-by` is exactly that substitution.
        fx = Fixture()
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-VFPPRESSURE", "implemented",
            {"done-when": "manual: 5-of-5 cascade stages export",
             "landed": "#1073"},
        )])
        r = fx.run([SUBJ_VFPPRESSURE])
        self.assertTrue(has(r, "R2 RQ-60-VFPPRESSURE"), fails(r))
        # Green control: the same flip WITH a written basis passes the
        # mechanical check (the basis's truth is the stated manual residual).
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-VFPPRESSURE", "implemented",
            {"done-when": "manual: 5-of-5 cascade stages export",
             "landed": "#1073",
             "verified-by": "jess by-symbol run on the fused cascade, "
                            "recorded in #1069"},
        )])
        self.assertEqual(fails(fx.run([SUBJ_VFPPRESSURE])), [])


class RuleControls(unittest.TestCase):
    def test_r1_declaration_required_from_v060(self):
        fx = Fixture()
        fx.release("release-v0.60.yaml", [art("RQ-60-X", "proposed")])
        self.assertTrue(has(fx.run([]), "R1 RQ-60-X"))
        # ... but NOT for shipped history (< v0.60): backfilling evidence
        # for frozen releases would itself be a hand-written mirror.
        fx2 = Fixture()
        fx2.release("release-v0.59.yaml", [art("RQ-59-X", "implemented")])
        self.assertEqual(fails(fx2.run([])), [])

    def test_r1_malformed_predicate(self):
        fx = Fixture()
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-X", "proposed", {"done-when": "exists-somewhere"})])
        self.assertTrue(has(fx.run([]), "malformed"))
        fx2 = Fixture()
        fx2.release("release-v0.60.yaml", [art(
            "RQ-60-X", "proposed", {"done-when": "manual:"})])
        self.assertTrue(has(fx2.run([]), "malformed"))

    def test_r2_claiming_status_needs_present_evidence(self):
        fx = Fixture()
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-X", "implemented",
            {"done-when": "contains:src/gone.rs:needle"})])
        self.assertTrue(has(fx.run([]), "R2 RQ-60-X"))
        # file: predicate, green when present.
        fx.evidence("scripts/thing.py", "x\n")
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-X", "implemented", {"done-when": "file:scripts/thing.py"})])
        self.assertEqual(fails(fx.run([])), [])

    def test_r4_noise_subjects_do_not_trip(self):
        # plan/chore/salvage commits name artifacts without delivering.
        fx = Fixture()
        fx.release("release-v0.59.yaml", [
            art("RQ-59-POPCNT", "proposed"),
            art("RQ-59-MEASURE", "proposed"),
            art("RQ-59-CRSWEEP", "proposed"),
        ])
        self.assertEqual(fails(fx.run(SUBJ_NOISE)), [])

    def test_unknown_id_delivery_subject_warns(self):
        fx = Fixture()
        fx.release("release-v0.59.yaml", [art("RQ-59-X", "implemented")])
        r = fx.run(
            ["RQ-61-GHOST (#9999): work with no artifact (#9998)"])
        warnings, failures = r[3], r[4]
        self.assertEqual(failures, [])
        self.assertTrue(any("RQ-61-GHOST" in w for w in warnings), warnings)

    def test_vacuity_floor_reds_on_truncated_history(self):
        fx = Fixture()
        fx.release("release-v0.59.yaml", [art("RQ-59-X", "implemented")])
        self.assertTrue(has(fx.run([], floor=28), "VACUOUS"))

    def test_r0_empty_artifacts_list_is_red(self):
        # Even a well-shaped file with an empty list is a red, not a zero.
        fx = Fixture()
        fx.release("release-v0.61.yaml", [])
        # keep the population non-empty so R0 is the only failure mode shown
        fx.release("release-v0.59.yaml", [art("RQ-59-X", "implemented")])
        r = fx.run([])
        self.assertTrue(has(r, "R0 release-v0.61.yaml"), fails(r))

    def test_duplicate_key_refused(self):
        # #1059: PyYAML silently keeps the LAST value on a duplicate key —
        # the strict loader must refuse instead.
        with self.assertRaises(DuplicateKeyError):
            yaml.load("a: 1\na: 2\n", Loader=StrictLoader)


class Splice1059Replay(unittest.TestCase):
    """Both defects the v0.59 hand-merged conflict resolution ACTUALLY
    produced (RQ-60-ARTIFACTSPLIT, #1059), reconstructed in the byte shape
    the merge left behind. The verification that missed them reported
    '16 artifacts, no duplicates, YAML OK' — all three true."""

    def test_1059_defect2_duplicate_issue_key(self):
        # The "keep both sides" resolution left one mapping with the
        # `issue:` key twice. yaml.safe_load keeps the last silently.
        fx = Fixture()
        fx.raw("release-v0.59.yaml", (
            "artifacts:\n"
            "  - id: RQ-59-FRESHNESS\n"
            "    type: system-req\n"
            "    title: t\n"
            "    status: implemented\n"
            "    links:\n"
            "      - type: derives-from\n"
            "        target: BR-001\n"
            "    fields:\n"
            "      issue: \"#977\"\n"
            "      issue: \"#1028\"\n"
        ))
        with self.assertRaises(DuplicateKeyError):
            fx.run([])

    def test_1059_defect1_spliced_artifact_absorbs_sibling_links(self):
        # The new entry landed BETWEEN the sibling's `tags:` and its
        # `links:`/`fields:` — DATASEG's mapping ends at tags:, the spliced
        # artifact inherits the trace links. Both parse; ids unique; the
        # trace graph is wrong. This is the defect that would have SHIPPED.
        splice = (
            "artifacts:\n"
            "  - id: RQ-59-DATASEG\n"
            "    type: system-req\n"
            "    title: t\n"
            "    status: implemented\n"
            "    release: v0.59\n"
            "    tags: [backend]\n"
            "  - id: RQ-59-SPLICED\n"
            "    type: system-req\n"
            "    title: t\n"
            "    status: proposed\n"
            "    release: v0.59\n"
            "    links:\n"
            "      - type: derives-from\n"
            "        target: BR-001\n"
            "    fields:\n"
            "      issue: \"#1041\"\n"
        )
        fx = Fixture()
        fx.raw("release-v0.59.yaml", splice)
        r = fx.run([])
        self.assertTrue(has(r, "R5 RQ-59-DATASEG"), fails(r))
        # Green control: each artifact carrying its own links passes.
        fx.release("release-v0.59.yaml", [
            art("RQ-59-DATASEG", "implemented"),
            art("RQ-59-SPLICED", "proposed"),
        ])
        self.assertEqual(fails(fx.run([])), [])

    def test_r5_issue_required_from_v060_only(self):
        fx = Fixture()
        fx.release("release-v0.60.yaml",
                   [art("RQ-60-X", "proposed",
                        {"done-when": "manual: reason"}, issue=None)])
        self.assertTrue(has(fx.run([]), "R5 RQ-60-X"), fails(fx.run([])))
        # Shipped history is frozen — no issue backfill demanded.
        fx2 = Fixture()
        fx2.release("release-v0.59.yaml",
                    [art("RQ-59-X", "implemented", issue=None)])
        self.assertEqual(fails(fx2.run([])), [])

    def test_r6_duplicate_id_across_files(self):
        # Two lanes creating the SAME per-requirement file id — by_id would
        # otherwise silently last-wins, the #1059 class one level up.
        fx = Fixture()
        fx.release("release-v0.61/RQ-61-FOO.yaml",
                   [art("RQ-61-FOO", "proposed",
                        {"done-when": "manual: reason"})])
        fx.release("release-v0.60.yaml",
                   [art("RQ-61-FOO", "proposed",
                        {"done-when": "manual: reason"})])
        r = fx.run([])
        self.assertTrue(has(r, "R6 RQ-61-FOO"), fails(r))


class DirectoryLayout(unittest.TestCase):
    """The #1059 chosen shape: artifacts/release-vX.YY/ with one file per
    requirement and a comments-only _release.yaml. Verified against BOTH
    the required gate's pinned rivet 0.23.0 and 0.32.0 at authoring; these
    pin the checker's side of the contract."""

    def test_layout_green(self):
        fx = Fixture()
        fx.raw("release-v0.61/_release.yaml",
               "# release-v0.61 metadata — comments only (see #1064)\n")
        fx.release("release-v0.61/RQ-61-FOO.yaml",
                   [art("RQ-61-FOO", "proposed",
                        {"done-when": "manual: not yet decided"})])
        self.assertEqual(fails(fx.run([])), [])

    def test_layout_version_derived_from_directory(self):
        # release-v0.61/RQ-61-FOO.yaml carries the version only in the
        # DIRECTORY name. Basename-only matching would classify it (0, 0)
        # and silently exempt it from every >= v0.60 rule — R1 firing here
        # proves the version comes from the full path.
        fx = Fixture()
        fx.release("release-v0.61/RQ-61-FOO.yaml",
                   [art("RQ-61-FOO", "proposed")])
        r = fx.run([])
        self.assertTrue(has(r, "R1 RQ-61-FOO"), fails(r))

    def test_layout_per_file_r0(self):
        # A per-requirement file in the #1064 invisible shape (non-schema
        # top-level key) is red BY FILE — a lane's artifact cannot vanish
        # behind the rest of the directory loading fine.
        fx = Fixture()
        fx.release("release-v0.61/RQ-61-OK.yaml",
                   [art("RQ-61-OK", "proposed",
                        {"done-when": "manual: reason"})])
        fx.raw("release-v0.61/RQ-61-GONE.yaml",
               "requirements:\n  - id: RQ-61-GONE\n    status: proposed\n")
        r = fx.run([])
        self.assertTrue(has(r, "R0 RQ-61-GONE.yaml"), fails(r))

    def test_version_is_scoped_to_the_repo_root_not_the_absolute_path(self):
        # An ANCESTOR of the checkout named `release-v0.50` must not supply
        # the version for artifacts under `artifacts/release-v0.61/`. The
        # absolute path would match the ancestor FIRST (it appears earlier),
        # classify the artifact as pre-v0.60, and silently exempt it from
        # every >= v0.60 rule — a checkout-LOCATION dependency, invisible on
        # any CI runner whose workspace happens not to be named that way.
        # R1 firing here is the discriminator: 0.50 < DECLARE_SINCE, 0.61 >=.
        with tempfile.TemporaryDirectory() as outer:
            root = Path(outer) / "release-v0.50" / "checkout"
            (root / "artifacts").mkdir(parents=True)
            d = root / "artifacts" / "release-v0.61"
            d.mkdir()
            (d / "RQ-61-FOO.yaml").write_text(
                yaml.safe_dump({"artifacts": [art("RQ-61-FOO", "proposed")]}),
                encoding="utf-8")
            r = check(root, RELEASE_GLOB, [], 0)
            self.assertTrue(has(r, "R1 RQ-61-FOO"), fails(r))

    def test_release_yaml_must_be_comments_only(self):
        # A keyed _release.yaml is exactly the shape rivet skips SILENTLY
        # (#1064) — content parked there would be invisible to the graph
        # while looking maintained, and the file becomes a shared write
        # surface again. Red before it can hide anything.
        fx = Fixture()
        fx.release("release-v0.61/RQ-61-FOO.yaml",
                   [art("RQ-61-FOO", "proposed",
                        {"done-when": "manual: reason"})])
        fx.raw("release-v0.61/_release.yaml",
               "metadata:\n  release: v0.61\n  theme: t\n")
        r = fx.run([])
        self.assertTrue(has(r, "R0 release-v0.61/_release.yaml"), fails(r))
        # Green control: comments only.
        fx.raw("release-v0.61/_release.yaml",
               "#   release: v0.61\n#   theme: t\n")
        self.assertEqual(fails(fx.run([])), [])


CANARY_DONE_WHEN = "contains:scripts/repro/gate.py:emulations >= 1200"


class R4BlindSpot1119(unittest.TestCase):
    """#1119 (RQ-61-R4BLIND) — R4 was blind to conventional-commit delivery
    subjects; two v0.61 artifacts shipped and stayed `proposed` with the
    gate green. Replays both measured instances RED, and pins the negative
    direction (mention/revert/description-position/ambiguity) GREEN."""

    def _a32(self, status="proposed", extra=None):
        f = {"done-when": "manual: A32 BL sites emit R_ARM_CALL (28)"}
        if status in ("implemented", "verified", "accepted"):
            f["verified-by"] = "PR #1116, real-linker verified"
        f.update(extra or {})
        return art("RQ-61-A32RELOC", status, f, issue="#1040")

    def _oracle(self, status="proposed", extra=None):
        f = {"done-when": "manual: both oracles print a counted decline "
                          "floor"}
        if status in ("implemented", "verified", "accepted"):
            f["verified-by"] = "PR #1112, both members red-first"
        f.update(extra or {})
        return art("RQ-61-ORACLEFLOOR", status, f, issue="#1113")

    def _fx(self, arts):
        fx = Fixture()
        for a in arts:
            fx.release(f"release-v0.61/{a['id']}.yaml", [a])
        return fx

    # -- The two measured instances, red -----------------------------------

    def test_replay_b4860e4e_issue_in_scope_is_a_delivery_claim(self):
        # b4860e4e merged #1116; RQ-61-A32RELOC stayed `proposed` and the
        # old R4 (prefix anchor) reported 0 failures. The scope position
        # resolves through fields.issue.
        fx = self._fx([self._a32("proposed")])
        r = fx.run([], window=[SUBJ_A32RELOC_1116])
        self.assertTrue(has(r, "R4 RQ-61-A32RELOC"), fails(r))
        self.assertTrue(has(r, "issue-anchored"), fails(r))
        # Green control 1: the flip (#1120's shape).
        fx = self._fx([self._a32("implemented")])
        self.assertEqual(fails(fx.run([], window=[SUBJ_A32RELOC_1116])), [])
        # Green control 2: `landed:` acknowledges the PR without a flip —
        # the "increment landed, outcome does not yet hold" statement.
        fx = self._fx([self._a32("proposed", {"landed": "PR #1116"})])
        self.assertEqual(fails(fx.run([], window=[SUBJ_A32RELOC_1116])), [])

    def test_replay_eefa19ef_unattributable_delivery_is_red(self):
        # eefa19ef merged #1112. Its subject names NEITHER the artifact id
        # NOR the artifact's issue (#1113) — the `#1104` it does name is
        # the PR that INTRODUCED the defect, so no resolution rule can
        # attribute it. R10 notices the silence instead.
        fx = self._fx([self._oracle("proposed")])
        r = fx.run([], window=[SUBJ_ORACLEFLOOR_1112])
        self.assertTrue(has(r, "R10"), fails(r))
        self.assertTrue(has(r, "every artifact silent"), fails(r))
        # Green control: writing the attribution down (`landed: PR #1112`,
        # exactly what #1120 did) resolves it.
        fx = self._fx([self._oracle("proposed", {"landed": "PR #1112"})])
        self.assertEqual(
            fails(fx.run([], window=[SUBJ_ORACLEFLOOR_1112])), [])

    # -- The negative direction the artifact demands -----------------------

    def test_id_mention_is_attribution_not_a_delivery_claim(self):
        # Live commit 0cb36bc7: `fix(rivet)` MENTIONS RQ-61-VCLOSURE
        # mid-subject. It must neither red R10 (the mention attributes it)
        # nor demand acknowledgment from VCLOSURE (a mention is not a
        # delivery claim — the passing-mention rule R4 protects).
        fx = Fixture()
        fx.release("release-v0.61/RQ-61-VCLOSURE.yaml", [art(
            "RQ-61-VCLOSURE", "proposed",
            {"done-when": "manual: coverage asserts",
             "landed": "PR #1115 — increment 1"}, issue="#1091")])
        self.assertEqual(fails(fx.run([], window=[SUBJ_UNRED_1118])), [])

    def test_description_position_issue_never_resolves_to_a_claim(self):
        # A `#N` in the DESCRIPTION (not the scope) must not become a
        # delivery claim even when N IS a known artifact issue — eefa19ef
        # proved that position names a cause. Attribution (R10) still
        # holds, so the commit is green without any acknowledgment.
        fx = self._fx([self._a32("proposed")])
        subj = ("fix(oracle): #1040 regressed the probe wording after the "
                "guard moved (#1130)")
        r = fx.run([], window=[subj])
        self.assertEqual(fails(r), [])

    def test_revert_subject_is_not_delivery_shaped(self):
        fx = self._fx([self._a32("proposed")])
        subj = ('Revert "fix(#1040): A32 BL sites carry R_ARM_CALL" (#1131)')
        self.assertEqual(fails(fx.run([], window=[subj])), [])

    def test_ambiguous_issue_warns_never_guesses(self):
        # Two same-release artifacts holding one issue: R4-issue must not
        # pick one. It warns; R10 attribution still applies (green).
        fx = self._fx([
            self._a32("proposed"),
            art("RQ-61-OTHER", "proposed",
                {"done-when": "manual: x"}, issue="#1040"),
        ])
        r = fx.run([], window=[SUBJ_A32RELOC_1116])
        self.assertEqual(fails(r), [])
        self.assertTrue(any("ambiguous" in w for w in r[3]), r[3])

    def test_process_typed_subjects_are_exempt(self):
        # chore/plan/docs are process commits — never delivery-shaped.
        fx = self._fx([self._a32("proposed")])
        window = [
            "chore(deps): bump scry-sai-core from 3.2.4 to 3.2.7 (#1109)",
            "plan(v0.61): scope the release (6 artifacts) (#1094)",
            "chore(rivet): flip RQ-61-A32RELOC to implemented (#1120)",
        ]
        self.assertEqual(fails(fx.run([], window=window)), [])

    def test_window_skip_is_loud(self):
        # None = underivable window (no git / no previous-minor tag): both
        # rules skip with a WINDOW-SKIP warning, never silently.
        fx = self._fx([self._a32("proposed")])
        r = fx.run([], window=None)
        self.assertEqual(fails(r), [])
        self.assertTrue(any("WINDOW-SKIP" in w for w in r[3]), r[3])

    def test_landed_pr_attribution_survives_history(self):
        # After the #1120 flip, eefa19ef stays attributable FOREVER via
        # ORACLEFLOOR's landed naming PR #1112 — the red is not permanent.
        fx = self._fx([self._oracle("implemented",
                                    {"landed": "PR #1112 — complete"})])
        self.assertEqual(
            fails(fx.run([], window=[SUBJ_ORACLEFLOOR_1112])), [])


class R7EvidenceRelease(unittest.TestCase):
    """#1085 R7 — evidence must belong to the release. The replay is the
    RQ-60-CANARY shape: the gate merged at 08:50, v0.59.0 was tagged at
    15:19 (the evidence is an ANCESTOR of the tag), and the v0.60 plan
    scoped it at 18:56 — every existence rule passed throughout."""

    def _repo(self):
        """A git fixture whose evidence commit PRE-dates the v0.59.0 tag."""
        fx = Fixture()
        fx.git("init", "-q", "-b", "main")
        fx.evidence("scripts/repro/gate.py", "emulations >= 1200\n")
        fx.git("add", "-A")
        fx.git("commit", "-q", "-m",
               "VCR-TIER-001 increment 1: canary gate (#1061)")
        fx.git("tag", "v0.59.0")
        return fx

    def _canary(self, fx, extra_fields=None, status="implemented"):
        f = {"done-when": CANARY_DONE_WHEN}
        f.update(extra_fields or {})
        fx.release("release-v0.60.yaml", [art("RQ-60-CANARY", status, f)])

    def test_replay_canary_evidence_predates_previous_tag(self):
        fx = self._repo()
        self._canary(fx)
        r = fx.run([])
        self.assertTrue(has(r, "R7 RQ-60-CANARY"), fails(r))
        self.assertTrue(has(r, "ANCESTOR of v0.59.0"), fails(r))
        # ... and it is the ONLY failure: the fixture reds on R7, not
        # incidentally on some other rule.
        self.assertEqual([f for f in fails(r) if not f.startswith("R7 ")], [])

    def test_shipped_in_escape_hatch_accepts(self):
        # The green fixture demanded by #1085: RQ-60-CANARY as it stands on
        # main, `shipped-in: "v0.59.0"` written down (#1090).
        fx = self._repo()
        self._canary(fx, {"shipped-in": "v0.59.0"})
        self.assertEqual(fails(fx.run([])), [])

    def test_shipped_in_must_be_version_shaped(self):
        # `shipped-in: earlier` must not buy the exemption — the escape
        # hatch names WHICH release delivered the evidence.
        fx = self._repo()
        self._canary(fx, {"shipped-in": "earlier"})
        r = fx.run([])
        self.assertTrue(has(r, "R7 RQ-60-CANARY"), fails(r))
        self.assertTrue(has(r, "not version-shaped"), fails(r))

    def test_evidence_after_previous_tag_is_green(self):
        # The normal case: evidence committed AFTER v0.59.0 belongs to
        # v0.60 and passes with an archaeology check RECORDED (not skipped).
        fx = Fixture()
        fx.git("init", "-q", "-b", "main")
        fx.evidence("README.md", "seed\n")
        fx.git("add", "-A")
        fx.git("commit", "-q", "-m", "seed")
        fx.git("tag", "v0.59.0")
        fx.evidence("scripts/repro/gate.py", "emulations >= 1200\n")
        fx.git("add", "-A")
        fx.git("commit", "-q", "-m",
               "VCR-TIER-001 increment 1: canary gate (#1061)")
        self._canary(fx)
        r = fx.run([])
        self.assertEqual(fails(r), [])
        r7_checked, r7_skipped = r[5], r[6]
        self.assertEqual((r7_checked, r7_skipped), (1, 0))

    def test_patch_tag_of_previous_minor_is_archaeologized_too(self):
        # Evidence that shipped in v0.59.1 (tagged from the same line) is
        # still a PREVIOUS release's evidence — the highest vX.(Y-1).* tag
        # is the reference, not only .0.
        fx = self._repo()
        fx.evidence("scripts/repro/patch_fix.py", "patched\n")
        fx.git("add", "-A")
        fx.git("commit", "-q", "-m", "hotfix: patch fix (#1099)")
        fx.git("tag", "v0.59.1")
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-PARKED", "implemented",
            {"done-when": "contains:scripts/repro/patch_fix.py:patched"})])
        r = fx.run([])
        self.assertTrue(has(r, "R7 RQ-60-PARKED"), fails(r))
        self.assertTrue(has(r, "ANCESTOR of v0.59.1"), fails(r))

    # -- The loud-skip contract: R7 that cannot run must never pass quietly.

    def test_no_git_skips_loudly(self):
        fx = Fixture()  # a bare temp dir — no repo, no history
        fx.evidence("scripts/repro/gate.py", "emulations >= 1200\n")
        self._canary(fx)
        r = fx.run([])
        self.assertEqual(fails(r), [])
        warnings_ = r[3]
        self.assertTrue(
            any(w.startswith("R7-SKIP RQ-60-CANARY") for w in warnings_),
            warnings_)
        r7_checked, r7_skipped = r[5], r[6]
        self.assertEqual((r7_checked, r7_skipped), (0, 1))

    def test_missing_previous_tag_skips_loudly(self):
        fx = Fixture()
        fx.git("init", "-q", "-b", "main")
        fx.evidence("scripts/repro/gate.py", "emulations >= 1200\n")
        fx.git("add", "-A")
        fx.git("commit", "-q", "-m", "gate")
        self._canary(fx)  # no v0.59.* tag anywhere
        r = fx.run([])
        self.assertEqual(fails(r), [])
        self.assertTrue(any("R7-SKIP" in w and "tag" in w for w in r[3]), r[3])

    def test_uncommitted_signature_skips_loudly(self):
        fx = self._repo()
        fx.evidence("scripts/repro/other.py", "uncommitted needle\n")
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-DIRTY", "implemented",
            {"done-when": "contains:scripts/repro/other.py:uncommitted needle"}
        )])
        r = fx.run([])
        self.assertEqual(fails(r), [])
        self.assertTrue(
            any("R7-SKIP RQ-60-DIRTY" in w for w in r[3]), r[3])


class R8ReleaseField(unittest.TestCase):
    """#1085 R8 — the `release:` field (rivet's side) must agree with the
    file's version (this checker's side)."""

    def test_harmful_direction_version_gate_bypass(self):
        # The direction nobody has hit: `release: v0.60` parked in a
        # pre-v0.60 file. Before R8 this passed EVERY rule (no done-when
        # demanded, path < v0.60) while rivet counted it in v0.60's scope.
        fx = Fixture()
        fx.release("release-v0.59.yaml",
                   [art("RQ-59-SNEAK", "implemented", release="v0.60")])
        r = fx.run([])
        self.assertTrue(has(r, "R8 RQ-59-SNEAK"), fails(r))
        self.assertTrue(has(r, "bypass"), fails(r))
        # ... and R8 is the ONLY thing that sees it (that is the point).
        self.assertEqual([f for f in fails(r) if not f.startswith("R8 ")], [])

    def test_patch_park_allowance_replays_the_six(self):
        # The 6 measured mismatches: real patch-release artifacts of the
        # PREVIOUS minor parked in the next minor's file — the practice is
        # now STATED as the rule's one allowance, so both shapes are green.
        fx = Fixture()
        fx.release("release-v0.57.yaml", [
            art("RQ-561-ZEROMEM", "implemented", release="v0.56.1"),
            art("RQ-57-SENTINEL", "implemented", release="v0.56.2"),
        ])
        self.assertEqual(fails(fx.run([])), [])

    def test_previous_minor_without_patch_is_red(self):
        # `release: v0.56` (the MINOR, not a patch of it) in the v0.57 file
        # is not the parked-patch practice — it is a plain disagreement.
        fx = Fixture()
        fx.release("release-v0.57.yaml",
                   [art("RQ-57-X", "implemented", release="v0.56")])
        r = fx.run([])
        self.assertTrue(has(r, "R8 RQ-57-X"), fails(r))

    def test_missing_field_is_red(self):
        fx = Fixture()
        fx.release("release-v0.59.yaml",
                   [art("RQ-59-X", "implemented")], stamp=False)
        r = fx.run([])
        self.assertTrue(has(r, "R8 RQ-59-X"), fails(r))
        self.assertTrue(has(r, "missing or not vX.Y"), fails(r))

    def test_unparseable_field_is_red(self):
        fx = Fixture()
        fx.release("release-v0.59.yaml",
                   [art("RQ-59-X", "implemented", release="0.59-final")])
        self.assertTrue(has(fx.run([]), "R8 RQ-59-X"))

    def test_matching_field_green_incl_own_patch(self):
        # vX.Y in release-vX.Y.yaml, and vX.Y.Z in its OWN minor's file,
        # both agree.
        fx = Fixture()
        fx.release("release-v0.57.yaml", [
            art("RQ-57-A", "implemented", release="v0.57"),
            art("RQ-57-B", "implemented", release="v0.57.1"),
        ])
        self.assertEqual(fails(fx.run([])), [])


class R9CrateSource(unittest.TestCase):
    """#1085 R9 — under a claiming status, a code-existence predicate into
    crate source cannot fail on the failure the artifact defines for
    itself. The specimen is RQ-60-A64IMPORT ('the acceptance number is the
    deliverable') pinned on `contains:crates/.../elf.rs:undefined_externals`;
    both live instances were corrected in #1090 — this is the rule."""

    A64 = ("contains:crates/synth-backend-aarch64/src/elf.rs:"
           "undefined_externals")

    def _with_code(self, fx):
        fx.evidence("crates/synth-backend-aarch64/src/elf.rs",
                    "fn undefined_externals() {}\n")

    def test_replay_a64import_code_existence_is_red(self):
        fx = Fixture()
        self._with_code(fx)
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-A64IMPORT", "implemented", {"done-when": self.A64})])
        r = fx.run([])
        self.assertTrue(has(r, "R9 RQ-60-A64IMPORT"), fails(r))
        # The code EXISTS (R2 satisfied) — R9 is the only failure, i.e. the
        # fixture reds on the rule under test, not incidentally.
        self.assertEqual([f for f in fails(r) if not f.startswith("R9 ")], [])

    def test_verified_by_escape_hatch_accepts(self):
        # #1090 correction form 2: written basis for why code-existence is
        # genuinely the outcome here.
        fx = Fixture()
        self._with_code(fx)
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-A64IMPORT", "implemented",
            {"done-when": self.A64,
             "verified-by": "census re-run: aarch64 13 -> 101 of 805, "
                            "recorded in #1071"})])
        self.assertEqual(fails(fx.run([])), [])

    def test_repointing_at_the_gate_accepts(self):
        # #1090 correction form 1: the signature names the GATE (here a
        # crate integration test the required Test job executes) instead of
        # the code path.
        fx = Fixture()
        fx.evidence("crates/synth-backend-aarch64/tests/a64_import_gate.rs",
                    "fn undefined_externals_census_floor() {}\n")
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-A64IMPORT", "implemented",
            {"done-when": "contains:crates/synth-backend-aarch64/tests/"
                          "a64_import_gate.rs:undefined_externals_census_floor"
             })])
        self.assertEqual(fails(fx.run([])), [])

    def test_non_claiming_status_not_gated(self):
        # R9 fires on the CLAIM, not the plan: a proposed artifact may pin
        # a crates/ signature it intends to strengthen before flipping.
        fx = Fixture()
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-A64IMPORT", "proposed", {"done-when": self.A64})])
        self.assertEqual(fails(fx.run([])), [])


class ProgrammeStatus1133(unittest.TestCase):
    """P-rules (#1133 / RQ-62-ROADMAPGATE): the VCR roadmap's 39 artifacts
    were outside every R-rule by scope, and VCR-WCET-001/002 carried no
    `status` key at all. Replays the measured corpus of two, the negative
    direction the artifact demands (no false reds on by-design absent
    `release:` or on legitimately proposed/approved items), and the P0/floor
    visibility contract. Mutation-verified at authoring: deleting the P1
    branch kills the corpus replay; deleting P2 kills the illegal-status
    tests; deleting P0 kills both visibility tests; zeroing the floor
    argument path kills the floor test."""

    ROADMAP = "verified-codegen-roadmap.yaml"

    @staticmethod
    def p_fails(result):
        return result[4]

    def p_has(self, result, needle):
        return any(needle in f for f in self.p_fails(result))

    def roadmap(self, fx, artifacts):
        fx.raw(self.ROADMAP, yaml.safe_dump({"artifacts": artifacts}))

    def test_replay_vcr_wcet_missing_status_is_red(self):
        # The measured corpus: two roadmap artifacts with NO status key,
        # beside a healthy sibling. Both must fire; the sibling must not.
        fx = Fixture()
        self.roadmap(fx, [
            {"id": "VCR-WCET-001", "type": "sys-verification", "title": "t",
             "links": [{"type": "verifies", "target": "VCR-001"}]},
            {"id": "VCR-WCET-002", "type": "sys-verification", "title": "t",
             "links": [{"type": "verifies", "target": "VCR-001"}]},
            {"id": "VCR-001", "type": "system-req", "title": "t",
             "status": "proposed",
             "links": [{"type": "derives-from", "target": "SR-001"}]},
        ])
        r = check_programme(fx.root, floor=0)
        self.assertTrue(self.p_has(r, "P1 VCR-WCET-001"), self.p_fails(r))
        self.assertTrue(self.p_has(r, "P1 VCR-WCET-002"), self.p_fails(r))
        self.assertEqual(len(self.p_fails(r)), 2, self.p_fails(r))

    def test_null_and_empty_status_are_p1(self):
        # `status:` (None) and `status: ""` are the same defect as a
        # missing key: unrepresentable in the lifecycle.
        fx = Fixture()
        self.roadmap(fx, [
            {"id": "VCR-A", "type": "sw-req", "title": "t", "status": None,
             "links": []},
            {"id": "VCR-B", "type": "sw-req", "title": "t", "status": "",
             "links": []},
        ])
        r = check_programme(fx.root, floor=0)
        self.assertTrue(self.p_has(r, "P1 VCR-A"), self.p_fails(r))
        self.assertTrue(self.p_has(r, "P1 VCR-B"), self.p_fails(r))

    def test_illegal_status_is_p2(self):
        # A typo'd status is worse than untidy: on the release side it
        # silently exits CLAIMING and defuses R2.
        fx = Fixture()
        self.roadmap(fx, [
            {"id": "VCR-A", "type": "sw-req", "title": "t",
             "status": "implmented", "links": []},
        ])
        r = check_programme(fx.root, floor=0)
        self.assertTrue(self.p_has(r, "P2 VCR-A"), self.p_fails(r))

    def test_no_false_reds_on_programme_shape(self):
        # The negative direction #1133 demands: legitimately proposed/
        # approved programme items with NO `release:` key (38 of 39 on
        # main), an explicit `release: null`, and the one historical
        # `release: v0.24.0` must all pass — the release-scoped rules
        # (R7/R8/R4/R10) are deliberately NOT applied here.
        fx = Fixture()
        self.roadmap(fx, [
            {"id": "VCR-A", "type": "system-req", "title": "t",
             "status": "proposed", "links": []},
            {"id": "VCR-B", "type": "system-req", "title": "t",
             "status": "approved", "release": None, "links": []},
            {"id": "VCR-RA-001", "type": "system-req", "title": "t",
             "status": "verified", "release": "v0.24.0", "links": []},
        ])
        self.assertEqual(self.p_fails(check_programme(fx.root, floor=0)), [])

    def test_roadmap_file_missing_is_p0(self):
        # A rename/move must red, never quietly exempt the programme again.
        fx = Fixture()
        fx.raw("some-other-artifacts.yaml", yaml.safe_dump({"artifacts": [
            {"id": "X-1", "type": "sw-req", "title": "t",
             "status": "draft", "links": []}]}))
        r = check_programme(fx.root, floor=0)
        self.assertTrue(self.p_has(r, "not found by the scan"),
                        self.p_fails(r))

    def test_roadmap_zero_artifacts_is_p0(self):
        # The #1064 invisible shape on the programme's own file: parses,
        # but under non-schema keys — rivet would skip it silently.
        fx = Fixture()
        fx.raw(self.ROADMAP, "requirements:\n  - id: VCR-001\n")
        r = check_programme(fx.root, floor=0)
        self.assertTrue(self.p_has(r, "contributes ZERO artifacts"),
                        self.p_fails(r))

    def test_release_files_are_status_checked_too(self):
        # R0-R10 never checked status LEGALITY; P2 covering release files
        # closes the typo'd-CLAIMING hole there as well.
        fx = Fixture()
        self.roadmap(fx, [
            {"id": "VCR-001", "type": "system-req", "title": "t",
             "status": "proposed", "links": []}])
        fx.release("release-v0.62/RQ-62-FOO.yaml",
                   [art("RQ-62-FOO", "implmented",
                        {"done-when": "manual: reason",
                         "verified-by": "basis"})])
        r = check_programme(fx.root, floor=0)
        self.assertTrue(self.p_has(r, "P2 RQ-62-FOO"), self.p_fails(r))

    def test_floor_reds_below(self):
        # Non-vacuity: a scan that finds fewer artifacts than the pinned
        # floor did LESS work than reality holds — red, never a quiet pass.
        fx = Fixture()
        self.roadmap(fx, [
            {"id": "VCR-001", "type": "system-req", "title": "t",
             "status": "proposed", "links": []}])
        r = check_programme(fx.root, floor=10)
        self.assertTrue(self.p_has(r, "P-VACUOUS"), self.p_fails(r))

    def test_live_repo_is_green_and_meets_the_floor(self):
        # The live anchor: the real repo passes with the DEFAULT floor,
        # and the floor is DERIVED from the release anchor (#1183), never
        # hand-pinned — checked >= PROGRAMME_FLOOR must hold on the tree
        # this test ships with, and the slack is one release's growth.
        files, checked, missing, illegal, failures = check_programme(REPO_ROOT)
        self.assertEqual(failures, [])
        self.assertGreaterEqual(checked, PROGRAMME_FLOOR)
        self.assertEqual(PROGRAMME_FLOOR,
                         ANCHOR_PROGRAMME - PROGRAMME_DELETED_SINCE_ANCHOR)
        self.assertEqual((missing, illegal), (0, 0))


class ProgrammeVisibility1183(unittest.TestCase):
    """P3/P4 (#1183 / RQ-65-FLOORSHAPE): what a SUM floor structurally cannot
    see — one file going invisible behind growth elsewhere — is caught per
    file. P3: every yaml under artifacts/ at any depth is one the glob
    scans. P4: every scanned yaml contributes >= 1 artifact (R0 generalized
    past release files). Measured at authoring: 89 of 89 visible, only the
    comments-only _release.yaml files empty, so the rules cost nothing today
    and the first violation is caught. Mutation-verified: deleting the P3
    walk kills the subdir test; deleting the P4 branch kills the
    artifact-less tests; the exemptions each have a control."""

    ROADMAP = "verified-codegen-roadmap.yaml"

    def roadmap(self, fx):
        fx.raw(self.ROADMAP, yaml.safe_dump({"artifacts": [
            {"id": "VCR-001", "type": "system-req", "title": "t",
             "status": "proposed", "links": []}]}))

    @staticmethod
    def p_fails(result):
        return result[4]

    def test_yaml_in_unscanned_subdir_is_p3(self):
        fx = Fixture()
        self.roadmap(fx)
        fx.raw("stpa/hazards.yaml", yaml.safe_dump({"artifacts": [
            {"id": "H-1", "type": "hazard", "title": "t", "status": "draft",
             "links": []}]}))
        fails = self.p_fails(check_programme(fx.root, floor=0))
        self.assertTrue(any(f.startswith("P3 artifacts/stpa/hazards.yaml")
                            for f in fails), fails)

    def test_artifactless_topic_yaml_is_p4(self):
        # A keyed yaml with no `artifacts:` and an EMPTY yaml: both are the
        # #1064 shape (rivet skips them silently); both red, never skipped.
        fx = Fixture()
        self.roadmap(fx)
        fx.raw("notes.yaml", "notes:\n  - free text\n")
        fx.raw("empty.yml", "")
        fails = self.p_fails(check_programme(fx.root, floor=0))
        self.assertTrue(any(f.startswith("P4 artifacts/notes.yaml")
                            for f in fails), fails)
        self.assertTrue(any(f.startswith("P4 artifacts/empty.yml")
                            for f in fails), fails)

    def test_exemptions_do_not_double_report(self):
        # _release.yaml is comments-only by contract (R0's surface), the
        # roadmap's emptiness is P0, and a release file's emptiness is R0:
        # none of them is ALSO a P4.
        fx = Fixture()
        fx.raw(self.ROADMAP, "requirements:\n  - id: VCR-001\n")
        fx.raw("release-v0.65/_release.yaml", "# comments only\n")
        fx.raw("release-v0.65/RQ-65-X.yaml", "requirements:\n  - id: X\n")
        fails = self.p_fails(check_programme(fx.root, floor=0))
        self.assertFalse(any(f.startswith("P4") for f in fails), fails)
        self.assertTrue(any(f.startswith("P0") for f in fails), fails)

    def test_live_repo_has_no_invisible_or_empty_yaml(self):
        fails = self.p_fails(check_programme(REPO_ROOT))
        self.assertFalse([f for f in fails if f[:2] in ("P3", "P4")], fails)


class AnchorFixture(Fixture):
    """A real git repo shaped like main around a release tag (#1183): two
    artifacts delivered id-first BEFORE v0.64.0, one after, in the
    per-requirement layout so the R4-issue/R10 window derives v0.64.0 as the
    previous tag. Anchor truth at v0.64.0: 2 delivery commits, 3 artifacts
    (roadmap + two release artifacts); live at HEAD: 3 and 4."""

    ROADMAP = "verified-codegen-roadmap.yaml"

    def build(self):
        self.git("init", "-q", "-b", "main")
        self.raw(self.ROADMAP, yaml.safe_dump({"artifacts": [
            {"id": "VCR-001", "type": "system-req", "title": "t",
             "status": "proposed", "links": []}]}))
        self.raw("release-v0.64/_release.yaml", "# comments only\n")
        self.release("release-v0.64/RQ-64-A.yaml",
                     [art("RQ-64-A", "implemented")])
        self.release("release-v0.64/RQ-64-B.yaml",
                     [art("RQ-64-B", "implemented")])
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "plan(v0.64): scope")
        self.git("commit", "-q", "--allow-empty", "-m", "RQ-64-A (#1): a")
        self.git("commit", "-q", "--allow-empty", "-m", "RQ-64-B (#2): b")
        self.git("tag", "v0.64.0")
        self.release("release-v0.65/RQ-65-C.yaml",
                     [art("RQ-65-C", "proposed")])
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "plan(v0.65): scope")
        self.git("commit", "-q", "--allow-empty", "-m", "chore: noise")
        self.git("commit", "-q", "--allow-empty", "-m", "RQ-65-C (#3): c")
        return self

    def clone(self, depth=None):
        """`git clone [--depth N]` of the fixture — the SAME operation a
        shallow CI checkout performs, not a hand-truncated subjects list."""
        td = tempfile.TemporaryDirectory()
        self._clones = getattr(self, "_clones", []) + [td]
        dst = Path(td.name) / "clone"
        subprocess.run(
            ["git", "clone", "-q", *(["--depth", str(depth)] if depth else []),
             f"file://{self.root}", str(dst)],
            check=True, capture_output=True,
        )
        return dst


def anchor(root, live_delivery=3, live_programme=4, window="v0.64.0", **kw):
    arts, _ = load_release_artifacts(root, RELEASE_GLOB)
    by_id = {a[2] for a in arts}
    kw.setdefault("tag", "v0.64.0")
    kw.setdefault("delivery", 2)
    kw.setdefault("programme", 3)
    return check_anchor(root, by_id, live_delivery, live_programme, window,
                        **kw)


def a_fails(result):
    return result[4]


def a_has(result, needle):
    return any(needle in f for f in a_fails(result))


class AnchorRule1183(unittest.TestCase):
    """A0-A3 (#1183 / RQ-65-FLOORSHAPE): the delivery and programme
    populations are pinned as EQUALITIES at the previous minor's tag and
    re-derived from git on every run. The shallow direction is exercised by
    an actual `git clone --depth` of the fixture (the CI failure shape), at
    three depths: tag unreachable, tag reachable but ancestry truncated,
    and ancestry complete but still declared shallow. Both pin directions,
    instrument rot (id regex, release glob), anchor currency (lag 0/1/2,
    ahead, major, underivable), the waiver channel, and the live repo.
    Mutation-verified at authoring — see the artifact's verified-by."""

    def test_full_history_is_green_and_exact(self):
        fx = AnchorFixture().build()
        d, p, lag, warns, fails = anchor(fx.root)
        self.assertEqual(fails, [])
        self.assertEqual(warns, [])
        self.assertEqual((d, p, lag), (2, 3, 0))

    def test_full_clone_is_green(self):
        # The control for the shallow clones: the same clone operation
        # without --depth reproduces the exact anchor.
        fx = AnchorFixture().build()
        d, p, lag, warns, fails = anchor(fx.clone())
        self.assertEqual(fails, [], fails)
        self.assertEqual((d, p), (2, 3))

    def test_shallow_clone_tag_unreachable_is_red(self):
        # --depth 2: the tag is beyond the boundary. Both derivations fail
        # LOUDLY; nothing skips.
        fx = AnchorFixture().build()
        r = anchor(fx.clone(depth=2))
        self.assertIsNone(r[0])
        self.assertIsNone(r[1])
        self.assertTrue(a_has(r, "history is SHALLOW"), a_fails(r))
        self.assertTrue(a_has(r, "A1 anchor v0.64.0: `git log"), a_fails(r))
        self.assertTrue(a_has(r, "A2 anchor v0.64.0: `git archive"),
                        a_fails(r))

    def test_shallow_clone_truncated_ancestry_is_red(self):
        # --depth 4: the tag IS reachable, `git log v0.64.0` silently
        # returns 1 of the 2 delivery commits — the canonical loss. A1 reds
        # BELOW; A2 does NOT (a tree is complete however shallow the
        # ancestry — the programme anchor is shallow-insensitive by design).
        fx = AnchorFixture().build()
        r = anchor(fx.clone(depth=4))
        self.assertEqual(r[0], 1)
        self.assertEqual(r[1], 3)
        self.assertTrue(a_has(r, "1 id-first delivery commits reachable"),
                        a_fails(r))
        self.assertTrue(a_has(r, "BELOW by 1"), a_fails(r))
        self.assertFalse(a_has(r, "A2"), a_fails(r))

    def test_shallow_clone_with_equal_count_is_still_red(self):
        # --depth 5: the count happens to EQUAL the pin over a truncated
        # ancestry. An equality that holds by luck over a repository that
        # declares itself shallow is not evidence — red on the declaration.
        fx = AnchorFixture().build()
        r = anchor(fx.clone(depth=5))
        self.assertEqual(r[0], 2)
        self.assertTrue(a_has(r, "history is SHALLOW"), a_fails(r))
        self.assertFalse(a_has(r, "!= pinned"), a_fails(r))

    def test_pin_below_and_above_are_both_red(self):
        # RQ-63-FLOOREQ's discipline: --exact at N-1 and N+1 each red.
        fx = AnchorFixture().build()
        self.assertTrue(a_has(anchor(fx.root, delivery=1), "ABOVE by 1"))
        self.assertTrue(a_has(anchor(fx.root, delivery=3), "BELOW by 1"))
        self.assertTrue(a_has(anchor(fx.root, programme=2),
                              "A2 anchor v0.64.0: 3 artifacts"))
        self.assertTrue(a_has(anchor(fx.root, programme=2), "ABOVE by 1"))
        self.assertTrue(a_has(anchor(fx.root, programme=4), "BELOW by 1"))

    def test_id_regex_rot_is_red(self):
        # The instrument narrows (a future id format the regex misses):
        # the tag's ancestry has not changed, the count has — A1 BELOW.
        fx = AnchorFixture().build()
        with mock.patch.object(sec, "ARTIFACT_ID",
                               re.compile(r"^(RQ-99-[A-Z0-9]+)\b")):
            r = anchor(fx.root)
        self.assertEqual(r[0], 0)
        self.assertTrue(a_has(r, "A1 anchor v0.64.0: 0 id-first"), a_fails(r))

    def test_release_glob_rot_is_red(self):
        # The programme glob loses the release-v*/ layout: the tag's tree
        # has not changed, the scan finds 1 of 3 — A2 BELOW. A sum floor at
        # HEAD with one release of slack could not see this.
        fx = AnchorFixture().build()
        real = sec.glob.glob

        def rotted(pat, **kw):
            return [] if "release-v" in pat else real(pat, **kw)

        with mock.patch.object(sec.glob, "glob", side_effect=rotted):
            r = anchor(fx.root)
        self.assertEqual(r[1], 1)
        self.assertTrue(a_has(r, "A2 anchor v0.64.0: 1 artifacts"), a_fails(r))
        self.assertTrue(a_has(r, "BELOW by 2"), a_fails(r))

    def test_lag_one_warns_with_the_values_to_paste(self):
        # The next minor is tagged; the anchor trails by one. Not red: the
        # post-tag PR moves it, and the warning carries the three derived
        # lines so the move is a paste, not a measurement.
        fx = AnchorFixture().build()
        fx.git("tag", "v0.65.0")
        d, p, lag, warns, fails = anchor(fx.root, window="v0.65.0")
        self.assertEqual(fails, [], fails)
        self.assertEqual(lag, 1)
        self.assertEqual(len(warns), 1, warns)
        self.assertIn('ANCHOR_TAG = "v0.65.0"', warns[0])
        self.assertIn("ANCHOR_DELIVERY = 3", warns[0])
        self.assertIn("ANCHOR_PROGRAMME = 4", warns[0])

    def test_lag_two_is_red(self):
        fx = AnchorFixture().build()
        r = anchor(fx.root, window="v0.66.0")
        self.assertEqual(r[2], 2)
        self.assertTrue(a_has(r, "2 minors behind"), a_fails(r))

    def test_anchor_ahead_major_and_underivable_are_red(self):
        fx = AnchorFixture().build()
        self.assertTrue(a_has(anchor(fx.root, window="v0.63.0"), "AHEAD"))
        self.assertTrue(a_has(anchor(fx.root, window="v1.0.0"), "MAJOR"))
        self.assertTrue(a_has(anchor(fx.root, window=None), "underivable"))
        self.assertTrue(a_has(anchor(fx.root, tag="v0.64"),
                              "must be a vX.Y.Z"))

    def test_waiver_channel_cannot_stand(self):
        # A declared deletion the live count does not need is a standing
        # licence (the ratchet engine's dead-waiver rule); a negative one is
        # not a count. A NEEDED declaration is not judged here (P-VACUOUS
        # is check_programme's).
        fx = AnchorFixture().build()
        self.assertTrue(a_has(anchor(fx.root, deleted=1), "DEAD waiver"))
        self.assertTrue(a_has(anchor(fx.root, deleted=-1),
                              "not a deletion count"))
        self.assertFalse(a_has(anchor(fx.root, deleted=1, live_programme=2),
                               "A3"))

    def test_live_delivery_below_anchor_is_red(self):
        fx = AnchorFixture().build()
        self.assertTrue(a_has(anchor(fx.root, live_delivery=1),
                              "A3: live delivery scan 1 < anchor 2"))

    def test_no_git_is_red_not_skipped(self):
        fx = Fixture()
        fx.release("release-v0.64/RQ-64-A.yaml",
                   [art("RQ-64-A", "implemented")])
        r = anchor(fx.root)
        self.assertTrue(a_has(r, "history is NO-GIT"), a_fails(r))
        self.assertIsNone(r[0])

    def test_live_repo_anchor_is_exact_and_current(self):
        # The pinned constants EQUAL this repository's own derivation at
        # ANCHOR_TAG (no slack in either direction), and the anchor is the
        # window's previous tag or at most one minor behind it.
        self.assertEqual(git_history_state(REPO_ROOT), "ok",
                         "the live anchor needs full history and tags")
        arts, _ = load_release_artifacts(REPO_ROOT, RELEASE_GLOB)
        by_id = {a[2] for a in arts}
        self.assertEqual(anchor_delivery_count(REPO_ROOT, by_id, ANCHOR_TAG),
                         ANCHOR_DELIVERY)
        self.assertEqual(anchor_programme_count(REPO_ROOT, ANCHOR_TAG),
                         ANCHOR_PROGRAMME)
        live_delivery = sum(
            1 for s in first_parent_subjects(REPO_ROOT)
            if (m := sec.ARTIFACT_ID.match(s)) and m.group(1) in by_id)
        live_programme = check_programme(REPO_ROOT, floor=0)[1]
        window = None
        for cand in sorted({a[1] for a in arts}, reverse=True):
            if cand > (0, 0):
                window = release_window_subjects(REPO_ROOT, cand)[0]
                if window is not None:
                    break
        d, p, lag, warns, fails = check_anchor(
            REPO_ROOT, by_id, live_delivery, live_programme, window)
        self.assertEqual(fails, [], fails)
        self.assertIn(lag, (0, 1), (window, lag))
        self.assertGreater(ANCHOR_DELIVERY, 0)
        self.assertGreater(ANCHOR_PROGRAMME, 0)


class UnscopedStaleness1085(unittest.TestCase):
    """S-rules (#1085 / RQ-64-SCOPEGAP): an artifact with no `release:` is a
    RECORD — a moving repo-derived count it cites must be dated in the same
    sentence (S1), and its title may not carry an undated measured figure
    (S2). Replays the measured corpus (VCR-REACH-002's title and VG-002's
    "188 Qed / 52 Admitted"), the negative direction (dated sentences in
    every anchor form, version-named topic files, a version-shaped
    `release:`, release-scoped files, threshold percentages in
    descriptions), the field-prose surface (TR-005, VER-001/002), the
    per-sentence framing that VCR-X86-001's shape needs, and the declared
    citation count as an EQUALITY (RQ-63-FLOOREQ one surface over).
    Mutation-verified at authoring: deleting the S2 branch kills the title
    replay; deleting S1 kills the VG-002 replay and the fields test;
    dropping the sentence split kills the adjacent-sentence test; disabling
    the equality check, or weakening it to `<`, kills the equality test."""

    ROADMAP = "verified-codegen-roadmap.yaml"

    @staticmethod
    def s_fails(result):
        return result[3]

    def s_has(self, result, needle):
        return any(needle in f for f in self.s_fails(result))

    @staticmethod
    def topic(fx, name, artifacts):
        fx.raw(name, yaml.safe_dump({"artifacts": artifacts}))

    @staticmethod
    def art(art_id, title, description="", fields=None, **extra):
        a = {"id": art_id, "type": "sw-req", "status": "proposed",
             "title": title, "description": description, "links": []}
        if fields is not None:
            a["fields"] = fields
        a.update(extra)
        return a

    def test_replay_vcr_reach_002_title_figure_is_red(self):
        # The reported instance: a percentage in a TITLE with no date, over
        # a description whose own figure IS dated by its issue — so S2 is
        # the only rule that can see it, and it must.
        fx = Fixture()
        self.topic(fx, self.ROADMAP, [self.art(
            "VCR-REACH-002",
            "Reach is part of correctness — 1.6% AArch64 acceptance on real "
            "modules",
            "Measured on 805 REAL-WORLD wasm modules (#1017): ARM 531/805 "
            "(66 %), AArch64 13 (1.6 %).")])
        r = check_unscoped(fx.root, expected=None)
        self.assertTrue(self.s_has(r, "S2 VCR-REACH-002"), self.s_fails(r))
        self.assertTrue(self.s_has(r, "`1.6%`"), self.s_fails(r))
        self.assertEqual(len(self.s_fails(r)), 1, self.s_fails(r))

    def test_replay_vg_002_undated_derived_counts_are_red(self):
        # The class the survey found beside it: proof counts asserted as
        # present-tense fact in 2026-03 and never touched (kernel recount
        # at authoring 630 / 2). One red per citation; nothing else fires.
        fx = Fixture()
        self.topic(fx, "verification-gaps.yaml", [self.art(
            "VG-002", "Rocq proofs — float admits outstanding",
            "The Rocq proof suite has 188 Qed and 52 Admitted theorems. All "
            "52 admits are in VFP floating-point semantics.")])
        r = check_unscoped(fx.root, expected=None)
        fails = self.s_fails(r)
        self.assertTrue(self.s_has(r, "S1 VG-002: undated `188 Qed`"), fails)
        self.assertTrue(self.s_has(r, "S1 VG-002: undated `52 Admitted`"),
                        fails)
        self.assertTrue(self.s_has(r, "S1 VG-002: undated `52 admits`"), fails)
        self.assertEqual(len(fails), 3, fails)
        self.assertEqual((r[0], r[1], r[2]), (1, 3, 3))

    def test_failure_names_the_live_derivation_but_does_not_judge_by_it(self):
        # The message shows the drift from status.json; the VERDICT is
        # dated-or-not — an undated count EQUAL to the live value is still
        # red (the lockstep-copy rejection).
        fx = Fixture()
        fx.evidence("artifacts/status.json",
                    '{"rocq_qed": 630, "rocq_admitted": 2}')
        self.topic(fx, self.ROADMAP, [
            self.art("A", "t", "The suite has 188 Qed."),
            self.art("B", "t", "The suite has 630 Qed."),
        ])
        r = check_unscoped(fx.root, expected=None)
        self.assertTrue(self.s_has(r, "the live derivation is 630 "
                                      "(artifacts/status.json `rocq_qed`)"),
                        self.s_fails(r))
        self.assertTrue(self.s_has(r, "S1 B: undated `630 Qed`"),
                        self.s_fails(r))
        self.assertEqual(len(self.s_fails(r)), 2, self.s_fails(r))

    def test_dated_sentence_is_green_in_every_anchor_form(self):
        # VG-009's shape (a version), an increment log (a PR number), a
        # measurement note (an ISO date) — all history, none red.
        fx = Fixture()
        self.topic(fx, self.ROADMAP, [
            self.art("A", "t", "Consequence, measured at v0.54.0: backend.rs "
                               "41.6 %, and 188 Qed then."),
            self.art("B", "t", "Increment 1 landed (#1155): 7 Qed / 0 "
                               "Admitted, byte-identical."),
            self.art("C", "t", "FIRST MEASUREMENT (2026-06-20, built green): "
                               "7 Qed / 0 Admitted."),
        ])
        r = check_unscoped(fx.root, expected=None)
        self.assertEqual(self.s_fails(r), [])
        self.assertEqual(r[1], 5)  # every citation was scanned, none undated

    def test_anchor_must_share_the_sentence(self):
        # VCR-X86-001's shape: the paragraph is dated three sentences up and
        # an incidental version sits one sentence down; the count's OWN
        # sentence says nothing about when. Framing is per sentence.
        fx = Fixture()
        self.topic(fx, self.ROADMAP, [self.art(
            "VCR-X86-001", "t",
            "Measured 2026-09-06 at v0.62.0. THE PROOF SUITE IS ARM-SPECIFIC. "
            "630 Qed across ArmSemantics.v and the generated theorems. That "
            "is the failure the v0.58 correction names.")])
        r = check_unscoped(fx.root, expected=None)
        self.assertTrue(self.s_has(r, "S1 VCR-X86-001: undated `630 Qed`"),
                        self.s_fails(r))

    def test_arm_immediates_do_not_date_a_sentence(self):
        # `#3` / `#16` are ARM immediates in this repo's prose, not issue
        # numbers; the 3-digit minimum keeps them from anchoring anything.
        fx = Fixture()
        self.topic(fx, self.ROADMAP, [self.art(
            "A", "t", "One dead `movw #3` remains beside the 188 Qed.")])
        r = check_unscoped(fx.root, expected=None)
        self.assertTrue(self.s_has(r, "S1 A: undated `188 Qed`"),
                        self.s_fails(r))

    def test_title_figures_ratio_percent_and_count(self):
        # VER060-008's shape (a ratio dated in the title) is green; the
        # same title undated is red; VG-002's own title — the count within
        # three words of its unit — is red.
        fx = Fixture()
        self.topic(fx, self.ROADMAP, [
            self.art("A", "Fused cascade — 5/5 stages export (#1069, "
                          "2026-08-27)"),
            self.art("B", "Fused cascade — 5/5 stages export"),
            self.art("C", "Rocq proofs — 52 VFP/float admits outstanding"),
            self.art("D", "Reach — 77 modules blocked on call discipline"),
            self.art("E", "Plain title, no figure at all"),
        ])
        r = check_unscoped(fx.root, expected=None)
        fails = self.s_fails(r)
        self.assertFalse(self.s_has(r, "S2 A"), fails)
        self.assertTrue(self.s_has(r, "S2 B: title carries the measured "
                                      "figure `5/5`"), fails)
        self.assertTrue(self.s_has(r, "`52 VFP/float admits`"), fails)
        self.assertTrue(self.s_has(r, "`77 modules`"), fails)
        self.assertFalse(self.s_has(r, "S2 E"), fails)
        self.assertEqual(len(fails), 3, fails)

    def test_threshold_percent_in_description_is_not_judged(self):
        # NFR-001 / BR-002's shape: a requirement threshold is not a
        # measurement, and a threshold and a measurement are not
        # mechanically separable — so S-rules do not judge description-
        # level percentages at all (stated residual, human-reviewed).
        fx = Fixture()
        self.topic(fx, "nonfunctional-requirements.yaml", [self.art(
            "NFR-001", "Performance",
            "Synth shall achieve at least 80% of native performance and code "
            "size less than 120% of native.")])
        r = check_unscoped(fx.root, expected=None)
        self.assertEqual(self.s_fails(r), [])
        self.assertEqual(r[1], 0)

    def test_prose_fields_are_scanned_with_their_key_path(self):
        # TR-005's and VER-001/002's shape:
        # the count lives in a field, flat or nested, not the description.
        fx = Fixture()
        self.topic(fx, "technical-requirements.yaml", [
            self.art("TR-005", "t", "Synth shall integrate Rocq.", fields={
                "verification-criteria": "Rocq proofs compile without errors "
                                         "(188 Qed); proptest suites pass."}),
            self.art("VER-002", "t", "Existence proofs.", fields={
                "steps": {"coverage": "95 Qed — see coq/STATUS.md"}}),
            self.art("OK", "t", "Fine.", fields={
                "steps": {"coverage": "T2 tier (95 Qed when written, "
                                      "2026-03-17)"}}),
        ])
        r = check_unscoped(fx.root, expected=None)
        fails = self.s_fails(r)
        self.assertTrue(self.s_has(r, "S1 TR-005: undated `188 Qed` in "
                                      "artifacts/technical-requirements.yaml "
                                      "(fields.verification-criteria)"), fails)
        self.assertTrue(self.s_has(r, "S1 VER-002: undated `95 Qed`"), fails)
        self.assertTrue(self.s_has(r, "(fields.steps.coverage)"), fails)
        self.assertFalse(self.s_has(r, "S1 OK"), fails)
        self.assertEqual(len(fails), 2, fails)

    def test_dated_by_construction_is_exempt(self):
        # A version-named topic file (sys-verification-v0.60.yaml records
        # what was true at v0.60), a version-shaped `release:` field, and a
        # release-scoped file (R7/R8's surface) are outside S-rules — and
        # only the genuinely unscoped artifact is counted as such.
        fx = Fixture()
        self.topic(fx, "sys-verification-v0.60.yaml", [self.art(
            "VER060-002", "BrIf discharged", "Kernel recount 630 Qed / 2 "
            "Admitted at delivery.")])
        self.topic(fx, self.ROADMAP, [
            self.art("VCR-RA-001", "t", "Verified with 188 Qed.",
                     release="v0.24.0"),
            self.art("VCR-A", "t", "Proposed, no figures.", release=None),
        ])
        # stamp=False: NO `release:` field, so only the PATH can exempt it —
        # a release-scoped file is R7/R8's surface even when its field is
        # missing (that is R8's red, not a second S-rule red).
        fx.release("release-v0.60/RQ-60-A64IMPORT.yaml", [
            {"id": "RQ-60-A64IMPORT", "type": "system-req",
             "status": "implemented",
             "title": "AArch64 accepts 1.6% of real modules — import dispatch "
                      "is the top blocker",
             "description": "Measured on 805 modules: 13 (1.6 %).",
             "links": [{"type": "derives-from", "target": "BR-001"}],
             "fields": {"issue": "#1017",
                        "done-when": "manual: reason",
                        "verified-by": "basis"}}], stamp=False)
        r = check_unscoped(fx.root, expected=None)
        self.assertEqual(self.s_fails(r), [])
        # VER060-002 is unscoped-but-dated (counted, not scanned); VCR-A is
        # unscoped; VCR-RA-001 and the release artifact are not unscoped.
        self.assertEqual(r[0], 2)

    def test_declared_count_is_an_equality(self):
        # RQ-63-FLOOREQ one surface over: BELOW is lost reach (pattern rot),
        # ABOVE is a citation that landed without its bump, EQUAL is green.
        # A lower bound would pass the second direction silently — which is
        # what the first version of this rule did (floor 34, review #1182).
        fx = Fixture()
        self.topic(fx, self.ROADMAP, [self.art(
            "A", "t", "Increment 1 landed (#1155): 7 Qed / 0 Admitted.")])
        below = check_unscoped(fx.root, expected=3)
        above = check_unscoped(fx.root, expected=1)
        equal = check_unscoped(fx.root, expected=2)
        self.assertTrue(self.s_has(below, "S-DRIFT")
                        and self.s_has(below, "BELOW the declared 3"),
                        self.s_fails(below))
        self.assertTrue(self.s_has(above, "S-DRIFT")
                        and self.s_has(above, "ABOVE the declared 1"),
                        self.s_fails(above))
        self.assertEqual(self.s_fails(equal), [])
        self.assertEqual(equal[1], 2)

    def test_live_repo_is_green_and_meets_the_floor(self):
        # The live anchor: the real repo passes with the DEFAULT declared
        # count, which EQUALS the live scan (no slack in either direction),
        # and the corrected corpus has zero undated.
        unscoped, citations, undated, failures = check_unscoped(REPO_ROOT)
        self.assertEqual(failures, [])
        self.assertEqual(citations, STALENESS_CITATIONS)
        self.assertGreater(STALENESS_CITATIONS, 0)
        self.assertEqual(undated, 0)
        self.assertGreater(unscoped, 200)


class FloorProseRule(unittest.TestCase):
    """RQ-64-FLOORPROSE (#910) — check_live_floor_prose.

    Added after v0.64's cold review observed the rule shipped with ZERO unit
    tests: its three-direction red-first was a one-time manual transcript, and a
    transcript is not a test. The rule's own subject is "a live pinned value
    that nothing checks", so shipping it unchecked was the defect it describes.
    """

    def _tree(self, floor="324847", prose="hi"):
        td = tempfile.TemporaryDirectory()
        self.addCleanup(td.cleanup)
        root = Path(td.name)
        wf = root / ".github" / "workflows"
        wf.mkdir(parents=True)
        (wf / "ci.yml").write_text(
            "jobs:\n  x:\n    steps:\n      - run: |\n"
            f"          python3 scripts/oracle_wiring_check.py --exact-emulation-floor {floor}\n"
        )
        d = root / "artifacts" / "release-v0.64"
        d.mkdir(parents=True)
        (d / "RQ-64-X.yaml").write_text(
            f"artifacts:\n  - id: RQ-64-X\n    description: {prose}\n"
        )
        return root

    def test_clean_tree_passes(self):
        scanned, live, hits, fails = check_live_floor_prose(self._tree())
        self.assertEqual((live, hits, fails), ("324847", 0, []))
        self.assertEqual(scanned, 1)

    def test_restated_live_floor_fails_and_names_the_file(self):
        root = self._tree(prose="the floor is 324847 today")
        _, _, hits, fails = check_live_floor_prose(root)
        self.assertEqual(hits, 1)
        self.assertTrue(fails, "a restated LIVE floor must fail")
        self.assertIn("RQ-64-X.yaml", fails[0])

    def test_superseded_floor_does_not_fire(self):
        """A DIFFERENT value is dated history and cannot rot — the distinction
        the corrected premise in #1178 turns on."""
        root = self._tree(prose="at v0.63 the floor was 324845")
        _, _, hits, fails = check_live_floor_prose(root)
        self.assertEqual((hits, fails), (0, []))

    def test_blinded_rule_fails_rather_than_reporting_clean(self):
        """Rename the gate flag and the rule cannot derive its subject. It must
        FAIL, never report a clean tree (#1113 non-vacuity)."""
        root = self._tree()
        ci = root / ".github" / "workflows" / "ci.yml"
        ci.write_text(ci.read_text().replace("--exact-emulation-floor",
                                             "--min-emulation-floor"))
        _, live, _, fails = check_live_floor_prose(root)
        self.assertIsNone(live)
        self.assertTrue(fails, "a blinded rule must fail")

    def test_zero_population_fails(self):
        """An empty artifact glob is pattern rot, not a clean tree."""
        td = tempfile.TemporaryDirectory()
        self.addCleanup(td.cleanup)
        root = Path(td.name)
        wf = root / ".github" / "workflows"
        wf.mkdir(parents=True)
        (wf / "ci.yml").write_text("x: --exact-emulation-floor 1234\n")
        scanned, _, _, fails = check_live_floor_prose(root)
        self.assertEqual(scanned, 0)
        self.assertTrue(fails, "a zero-population scan must fail")


if __name__ == "__main__":
    unittest.main(verbosity=2)
