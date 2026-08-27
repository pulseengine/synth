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

Run: python3 scripts/test_status_evidence_check.py
Mutation-verified at authoring (transcript in the RQ-60-FLIPCOUPLE PR):
disabling each of R1/R2/R3/R4 and the duplicate-key strictness kills at
least one test.
"""

from __future__ import annotations

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
    DuplicateKeyError,
    StrictLoader,
    check,
)
import yaml  # noqa: E402

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


def art(art_id, status, fields=None):
    a = {"id": art_id, "type": "system-req", "title": "t", "status": status,
         "release": "v0.60"}
    if fields:
        a["fields"] = fields
    return a


class Fixture:
    """A temp repo root with release files, evidence files and subjects."""

    def __init__(self):
        self._td = tempfile.TemporaryDirectory()
        self.root = Path(self._td.name)
        (self.root / "artifacts").mkdir()

    def release(self, name, artifacts):
        p = self.root / "artifacts" / name
        p.write_text(yaml.safe_dump({"artifacts": artifacts}), encoding="utf-8")
        return p

    def evidence(self, rel, content):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
        return p

    def run(self, subjects, floor=0):
        return check(self.root, "artifacts/release-v*.yaml", subjects, floor)


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
        # Green control: the flip is consistent with the evidence.
        fx.release("release-v0.60.yaml", [art(
            "RQ-60-CANARY", "implemented",
            {"done-when": "contains:crates/synth-backend/src/arm_encoder.rs:"
                          "expansion_scratch_contract"},
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
        _, _, _, warnings, failures = fx.run(
            ["RQ-61-GHOST (#9999): work with no artifact (#9998)"])
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


if __name__ == "__main__":
    unittest.main(verbosity=2)
