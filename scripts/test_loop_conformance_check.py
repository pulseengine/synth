#!/usr/bin/env python3
"""Unit tests for loop_conformance_check.py (RQ-62-LOOPCONFORM, #1136).

The gate that certifies "this release ran the feature loop" is the mechanism
the standing release authorization now rests on, so it does not get to be the
unchecked checker (the v0.55-v0.61 recurring finding). Every derivation branch
is driven here on FIXTURES — no git refs, no network, no gh. The two release
shapes replayed at the end are reconstructions of the real corpora the gate
was proven against (transcripts in scripts/repro/loop_conformance_1136_gate.md):

  * the v0.61.0 shape  -> CONFORMS (steps 3-8 all derivable and green)
  * the v0.57.0 shape  -> DOES-NOT-CONFORM (no done-when regime, no
    status_evidence gate, mcdc gate without the BRANCH_POPULATION pin) —
    note v0.57.0 does NOT "predate the witness gate entirely" (RQ-57-MCDC
    shipped in it and its check-run succeeded on the tag commit); what it
    predates is the pin and the evidenced-status regime, and the gate must
    red on exactly that, with attribution
  * the v0.56.2 shape  -> DOES-NOT-CONFORM (predates the witness gate
    entirely: no mcdc_gate.py, no run)

Plus the verdict's own non-vacuity: a run that derived nothing must not pass
on attestations alone.

Stdlib unittest only:  python3 scripts/test_loop_conformance_check.py
"""

import pathlib
import sys
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import loop_conformance_check as lcc  # noqa: E402


def artifact(aid, tags=(), issue="", done_when="ok"):
    fields = {}
    if issue:
        fields["issue"] = issue
    if done_when is not None:
        fields["done-when"] = done_when
    return {"id": aid, "tags": list(tags), "fields": fields, "status": "proposed"}


def mk_check(version="v0.61.0", mode="retro", sha="d" * 40):
    c = lcc.Check.__new__(lcc.Check)
    c.version = version
    c.bare_version = version[1:]
    maj, mnr, _ = version[1:].split(".")
    c.majmin = (int(maj), int(mnr))
    c.rid = f"v{maj}.{mnr}"
    c.repo = "pulseengine/synth"
    c.findings = []
    c.mode = mode
    c.ref = version if mode == "retro" else "HEAD"
    c.sha = sha
    return c


class PureHelpers(unittest.TestCase):
    def test_filed_decision_matched_by_shape(self):
        docs = [("f.yaml", {"artifacts": [artifact("RQ-62-ARCHMODEL",
                 tags=["architecture", "aadl", "spar", "feature-loop"], issue="#1136")]})]
        d = lcc.find_filed_steps12_decision(docs)
        self.assertIsNotNone(d)
        self.assertEqual(d["id"], "RQ-62-ARCHMODEL")
        self.assertEqual(d["issue"], "#1136")

    def test_filed_decision_spar_alone_suffices(self):
        docs = [("f.yaml", {"artifacts": [artifact("X", tags=["spar", "feature-loop"], issue="#1")]})]
        self.assertIsNotNone(lcc.find_filed_steps12_decision(docs))

    def test_filed_decision_rejects_missing_issue(self):
        docs = [("f.yaml", {"artifacts": [artifact("X", tags=["aadl", "feature-loop"], issue="")]})]
        self.assertIsNone(lcc.find_filed_steps12_decision(docs))

    def test_filed_decision_rejects_feature_loop_without_arch_tag(self):
        # RQ-62-LOOPCONFORM itself is feature-loop-tagged; it must NOT count
        # as the steps-1-2 decision.
        docs = [("f.yaml", {"artifacts": [artifact(
            "RQ-62-LOOPCONFORM", tags=["release-process", "feature-loop"], issue="#1136")]})]
        self.assertIsNone(lcc.find_filed_steps12_decision(docs))

    def test_done_when_census(self):
        docs = [
            ("a.yaml", {"artifacts": [artifact("A"), artifact("B", done_when=None)]}),
            ("b.yaml", None),  # comments-only file parses to None
        ]
        total, missing = lcc.artifacts_missing_done_when(docs)
        self.assertEqual(total, 2)
        self.assertEqual(missing, ["B"])

    def test_done_when_blank_counts_missing(self):
        docs = [("a.yaml", {"artifacts": [artifact("A", done_when="  ")]})]
        self.assertEqual(lcc.artifacts_missing_done_when(docs)[1], ["A"])

    def test_ci_emulation_floor(self):
        self.assertEqual(lcc.ci_emulation_floor("x\n --min-emulation-floor 322754 \\\n"), 322754)
        self.assertEqual(lcc.ci_emulation_floor("oracle_wiring_check.py --json out"), 0)

    def test_signing_tag_trigger(self):
        wf = 'name: Signing E2E\non:\n  push:\n    tags:\n      - "v*"\n    branches: [main]\n'
        self.assertTrue(lcc.signing_workflow_tag_triggered(wf))
        self.assertTrue(lcc.signing_workflow_tag_triggered("on:\n  push:\n    tags: [ 'v*' ]\n"))
        self.assertFalse(lcc.signing_workflow_tag_triggered("on:\n  push:\n    branches: [main]\n"))

    def test_review_record_shas(self):
        shas = lcc.review_record_shas("reviewed commit d4f935c1c892 pre-tag; also 12a01a32")
        self.assertIn("d4f935c1c892", shas)
        self.assertIn("12a01a32", shas)
        self.assertEqual(lcc.review_record_shas("no shas here, v0.62 only"), [])


class VerdictAggregation(unittest.TestCase):
    def all_green(self, c):
        for step, _ in lcc.STEP_NAMES:
            c.add(step, "x", lcc.DERIVED_PASS, "fixture")

    def test_all_derived_green_conforms(self):
        c = mk_check()
        self.all_green(c)
        v = c.verdict()
        self.assertTrue(v["conforms"])
        self.assertEqual(v["derived_slots"], 7)
        self.assertEqual(v["failures"], 0)

    def test_one_fail_reds(self):
        c = mk_check()
        self.all_green(c)
        c.add("5", "mcdc gate", lcc.DERIVED_FAIL, "no pin")
        v = c.verdict()
        self.assertFalse(v["conforms"])
        # A failing sub-check disqualifies its slot from the derived count.
        self.assertEqual(v["derived_slots"], 6)

    def test_not_derived_reds(self):
        c = mk_check()
        self.all_green(c)
        c.add("6", "signing", lcc.NOT_DERIVED, "API unavailable")
        self.assertFalse(c.verdict()["conforms"])

    def test_attestations_alone_are_vacuous_not_conforming(self):
        # THE non-vacuity red: zero failures, nothing derived -> refused.
        c = mk_check()
        for step, _ in lcc.STEP_NAMES:
            c.add(step, "x", lcc.ATTESTED, "someone said so")
        v = c.verdict()
        self.assertEqual(v["failures"], 0)
        self.assertTrue(v["vacuous"])
        self.assertFalse(v["conforms"])

    def test_na_statuses_do_not_fail_but_do_not_count_derived(self):
        c = mk_check()
        self.all_green(c)
        c.findings = [f for f in c.findings if f[0] != "1-2"]
        c.add("1-2", "filed decision", lcc.NA_FILED, "RQ-62-ARCHMODEL (#1136)")
        v = c.verdict()
        self.assertTrue(v["conforms"])
        self.assertEqual(v["derived_slots"], 6)

    def test_render_summary_line(self):
        c = mk_check()
        self.all_green(c)
        out = lcc.render(c.verdict())
        self.assertIn("verdict=CONFORMS", out)
        self.assertIn("slots=7", out)


class Step7Regime(unittest.TestCase):
    def test_missing_record_fails_from_v062(self):
        c = mk_check("v0.62.0")
        with mock.patch.object(lcc, "tree_ls", return_value=[]):
            c.step_7()
        (_, _, status, detail) = c.findings[0]
        self.assertEqual(status, lcc.DERIVED_FAIL)
        self.assertIn("docs/reviews/v0.62-cold-review.md", detail)

    def test_missing_record_attested_before_v062(self):
        c = mk_check("v0.61.0")
        with mock.patch.object(lcc, "tree_ls", return_value=[]):
            c.step_7()
        self.assertEqual(c.findings[0][2], lcc.ATTESTED)

    def test_record_without_ancestor_sha_fails(self):
        c = mk_check("v0.62.0")
        with mock.patch.object(lcc, "tree_ls", return_value=["docs/reviews/v0.62-cold-review.md"]), \
             mock.patch.object(lcc, "tree_read", return_value="findings only, no commit named"), \
             mock.patch.object(lcc, "git", return_value=(1, "")):
            c.step_7()
        self.assertEqual(c.findings[0][2], lcc.DERIVED_FAIL)

    def test_record_naming_ancestor_derives(self):
        c = mk_check("v0.62.0", sha="a" * 40)
        with mock.patch.object(lcc, "tree_ls", return_value=["docs/reviews/v0.62-cold-review.md"]), \
             mock.patch.object(lcc, "tree_read", return_value="reviewed bbbbbbbbbbbb, ok"), \
             mock.patch.object(lcc, "git", return_value=(0, "b" * 40)):
            c.step_7()
        self.assertEqual(c.findings[0][2], lcc.DERIVED_PASS)


def fake_tree(files):
    """tree_read/tree_has over a {path: text} dict."""
    def _read(ref, path):
        return files.get(path)

    def _has(ref, path):
        return path in files

    return _read, _has


CI_MODERN = (
    "jobs:\n  claim:\n    steps:\n"
    "      - run: python3 scripts/status_evidence_check.py\n"
    "      - run: python3 scripts/oracle_wiring_check.py --min-emulation-floor 322754\n"
    "      - run: python3 scripts/mcdc_gate.py target/mcdc\n"
)
CI_V057 = (
    "jobs:\n  claim:\n    steps:\n"
    "      - run: python3 scripts/oracle_wiring_check.py --min-emulation-floor 295726\n"
    "      - run: python3 scripts/mcdc_gate.py target/mcdc\n"
)
CI_V056 = (
    "jobs:\n  claim:\n    steps:\n"
    "      - run: python3 scripts/oracle_wiring_check.py --min-emulation-floor 295726\n"
)


class ReleaseShapeReplay(unittest.TestCase):
    """The two corpora, reconstructed as fixtures so the red stays committed."""

    def run_steps_3_4_5(self, c, files, docs, check_run="success"):
        read, has = fake_tree(files)
        with mock.patch.object(lcc, "tree_read", side_effect=read), \
             mock.patch.object(lcc, "tree_has", side_effect=has), \
             mock.patch.object(lcc.Check, "load_release_docs", return_value=docs), \
             mock.patch.object(lcc.Check, "check_run_conclusion", return_value=check_run):
            c.step_3()
            c.step_4()
            c.step_5()

    def test_v061_shape_steps_3_4_5_green(self):
        c = mk_check("v0.61.0")
        files = {
            ".github/workflows/ci.yml": CI_MODERN,
            "scripts/status_evidence_check.py": "#",
            "scripts/oracle_wiring_check.py": "#",
            "scripts/mcdc_gate.py": "BRANCH_POPULATION = {}",
        }
        docs = [("artifacts/release-v0.61/RQ-61-X.yaml", {"artifacts": [artifact("RQ-61-X")]})]
        self.run_steps_3_4_5(c, files, docs)
        self.assertEqual([f for f in c.findings if f[2] in lcc.FAILING], [])

    def test_v057_shape_fails_with_attribution(self):
        c = mk_check("v0.57.0")
        files = {
            ".github/workflows/ci.yml": CI_V057,
            "scripts/oracle_wiring_check.py": "#",
            # gate exists, RUNS green, but has no BRANCH_POPULATION pin — the
            # v0.57 truth: it does NOT predate the witness gate, only the pin.
            "scripts/mcdc_gate.py": "def score(): pass",
        }
        docs = [("artifacts/release-v0.57.yaml",
                 {"artifacts": [artifact("RQ-57-A", done_when=None)]})]
        self.run_steps_3_4_5(c, files, docs, check_run="success")
        fails = {(f[0], f[1]) for f in c.findings if f[2] in lcc.FAILING}
        self.assertIn(("3", "done-when regime"), fails)
        self.assertIn(("3", "status-evidence gate"), fails)
        self.assertIn(("5", "mcdc gate"), fails)
        # and the failure text carries the pin attribution, not a vague "old"
        pin_fail = [f for f in c.findings if f[1] == "mcdc gate"][0]
        self.assertIn("BRANCH_POPULATION", pin_fail[3])

    def test_v056_shape_fails_witness_entirely(self):
        c = mk_check("v0.56.2")
        files = {
            ".github/workflows/ci.yml": CI_V056,
            "scripts/oracle_wiring_check.py": "#",
        }
        docs = [("artifacts/release-v0.56.yaml",
                 {"artifacts": [artifact("RQ-56-A", done_when=None)]})]
        self.run_steps_3_4_5(c, files, docs, check_run="absent")
        fails = {(f[0], f[1]) for f in c.findings if f[2] in lcc.FAILING}
        self.assertIn(("5", "mcdc gate"), fails)
        self.assertIn(("5", "mcdc ran on commit"), fails)

    def test_zero_artifact_release_is_red(self):
        # The #1064 invisible shape: a release whose artifact files parse to
        # nothing must red step 3, never quietly contribute zero.
        c = mk_check("v0.59.0")
        files = {
            ".github/workflows/ci.yml": CI_MODERN,
            "scripts/status_evidence_check.py": "#",
            "scripts/oracle_wiring_check.py": "#",
            "scripts/mcdc_gate.py": "BRANCH_POPULATION = {}",
        }
        self.run_steps_3_4_5(c, files, [("artifacts/release-v0.59.yaml", None)])
        fails = {(f[0], f[1]) for f in c.findings if f[2] in lcc.FAILING}
        self.assertIn(("3", "artifact set"), fails)

    def test_api_unavailable_is_not_derived_not_pass(self):
        c = mk_check("v0.61.0")
        files = {
            ".github/workflows/ci.yml": CI_MODERN,
            "scripts/status_evidence_check.py": "#",
            "scripts/oracle_wiring_check.py": "#",
            "scripts/mcdc_gate.py": "BRANCH_POPULATION = {}",
        }
        docs = [("a.yaml", {"artifacts": [artifact("RQ-61-X")]})]
        self.run_steps_3_4_5(c, files, docs, check_run=None)
        self.assertTrue(any(f[2] == lcc.NOT_DERIVED for f in c.findings))
        self.assertFalse(c.verdict()["conforms"])


class Steps12Branches(unittest.TestCase):
    def test_aadl_model_derives(self):
        c = mk_check()
        with mock.patch.object(lcc, "git", return_value=(0, "spar/synth.aadl\n")):
            c.step_1_2()
        self.assertEqual(c.findings[0][2], lcc.DERIVED_PASS)

    def test_unfiled_na_is_red(self):
        c = mk_check()
        with mock.patch.object(lcc, "git", return_value=(0, "")), \
             mock.patch.object(lcc.Check, "load_checkout_docs", return_value=[]):
            c.step_1_2()
        self.assertEqual(c.findings[0][2], lcc.DERIVED_FAIL)
        self.assertIn("#1136", c.findings[0][3])

    def test_filed_na_cites_the_artifact(self):
        c = mk_check()
        docs = [("artifacts/release-v0.62/RQ-62-ARCHMODEL.yaml",
                 {"artifacts": [artifact("RQ-62-ARCHMODEL",
                  tags=["aadl", "spar", "feature-loop"], issue="#1136")]})]
        with mock.patch.object(lcc, "git", return_value=(0, "")), \
             mock.patch.object(lcc.Check, "load_checkout_docs", return_value=docs):
            c.step_1_2()
        self.assertEqual(c.findings[0][2], lcc.NA_FILED)
        self.assertIn("RQ-62-ARCHMODEL", c.findings[0][3])


class ReleaseIdentity(unittest.TestCase):
    def test_pretag_version_mismatch_is_red(self):
        c = mk_check("v0.62.0", mode="pretag")
        with mock.patch.object(lcc.Path, "read_text",
                               return_value='[workspace.package]\nversion = "0.61.0"\n'):
            c.check_release_identity()
        self.assertEqual(c.findings[0][2], lcc.DERIVED_FAIL)

    def test_pretag_version_match_passes(self):
        c = mk_check("v0.62.0", mode="pretag")
        with mock.patch.object(lcc.Path, "read_text",
                               return_value='[workspace.package]\nversion = "0.62.0"\n'):
            c.check_release_identity()
        self.assertEqual(c.findings[0][2], lcc.DERIVED_PASS)

    def test_retro_skips_identity(self):
        c = mk_check("v0.61.0", mode="retro")
        c.check_release_identity()
        self.assertEqual(c.findings, [])


if __name__ == "__main__":
    unittest.main(verbosity=2)
