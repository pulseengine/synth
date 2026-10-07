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

import os
import pathlib
import sys
import unittest

import yaml
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import loop_conformance_check as lcc  # noqa: E402


def artifact(aid, tags=(), issue="", done_when="ok", release=None, verified_by=None):
    """`verified_by` exists because RQ-81-SILENT made "reports an outcome" part
    of a green release shape. A fixture that models a GREEN release must now
    carry one of verified-by/disposition/landed; fixtures that model a FAILING
    shape may stay silent, and several deliberately do."""
    fields = {}
    if issue:
        fields["issue"] = issue
    if done_when is not None:
        fields["done-when"] = done_when
    if verified_by is not None:
        fields["verified-by"] = verified_by
    a = {"id": aid, "tags": list(tags), "fields": fields, "status": "proposed"}
    if release is not None:
        a["release"] = release
    return a


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

    # --- release scoping of the steps-1-2 slot (v0.65, #1136) -------------
    # A recurring N/A must be RE-FILED each release. Before this, the matcher
    # returned the first shape-match in scan order regardless of `release:`,
    # so on the real v0.65 tree it returned RQ-63-ARCHMODEL -- two releases
    # back -- and the filing could have lapsed with the slot staying green.

    ARCH_TAGS = ["spar", "feature-loop"]

    def _two_releases(self):
        return [
            ("old.yaml", {"artifacts": [artifact(
                "RQ-63-ARCHMODEL", tags=self.ARCH_TAGS, issue="#1136", release="v0.63")]}),
            ("new.yaml", {"artifacts": [artifact(
                "RQ-65-ARCHMODEL", tags=self.ARCH_TAGS, issue="#1136", release="v0.65")]}),
        ]

    def test_steps12_prefers_the_release_under_test(self):
        d = lcc.find_filed_steps12_decision(self._two_releases(), "v0.65")
        self.assertEqual(d["id"], "RQ-65-ARCHMODEL")
        self.assertFalse(d["stale"])

    def test_steps12_marks_an_earlier_releases_filing_stale(self):
        # Only v0.63 is filed; a v0.65 run must NOT be discharged by it.
        docs = self._two_releases()[:1]
        d = lcc.find_filed_steps12_decision(docs, "v0.65")
        self.assertEqual(d["id"], "RQ-63-ARCHMODEL")
        self.assertTrue(d["stale"], "a previous release's filing must not discharge this one")

    def test_steps12_scan_order_does_not_decide(self):
        # The stale one FIRST in scan order -- the exact shape of the live bug.
        docs = self._two_releases()
        d = lcc.find_filed_steps12_decision(docs, "v0.65")
        self.assertEqual(d["id"], "RQ-65-ARCHMODEL")

    def test_steps12_unscoped_call_is_unchanged(self):
        # Back-compat: no release argument keeps first-match behaviour.
        d = lcc.find_filed_steps12_decision(self._two_releases())
        self.assertEqual(d["id"], "RQ-63-ARCHMODEL")

    def test_steps12_missing_tag_makes_the_release_invisible(self):
        # RQ-65-ARCHMODEL shipped without `feature-loop` and was invisible.
        docs = [("new.yaml", {"artifacts": [artifact(
            "RQ-65-ARCHMODEL", tags=["spar", "recurring-na"], issue="#1136",
            release="v0.65")]})]
        self.assertIsNone(lcc.find_filed_steps12_decision(docs, "v0.65"))

    def test_release_scope_normalises_the_tag(self):
        self.assertEqual(lcc.release_scope("v0.65.0"), "v0.65")
        self.assertEqual(lcc.release_scope("0.65.1"), "v0.65")
        self.assertEqual(lcc.release_scope("v1.10.3"), "v1.10")

    def test_done_when_census(self):
        docs = [
            ("a.yaml", {"artifacts": [artifact("A"), artifact("B", done_when=None)]}),
            ("b.yaml", None),  # comments-only file parses to None
        ]
        total, missing, evaluable, manual = lcc.artifacts_missing_done_when(docs)
        self.assertEqual(total, 2)
        self.assertEqual(missing, ["B"])

    def test_done_when_declared_is_not_evaluated_1335(self):
        """RQ-70-DONEWHEN (#1335): the census must SPLIT declared from evaluable.

        `manual:` is a declaration nothing evaluates — status_evidence's R3 fires
        only on the mechanical forms. Counting presence made a release with zero
        machine-checked signatures print the same `N/N done-when` line as one
        with all of them, and v0.66/67/68/69 were each 100% `manual:`.
        """
        docs = [("a.yaml", {"artifacts": [
            artifact("M1", done_when="manual: someone looks at it"),
            artifact("M2", done_when="manual: and at this too"),
            artifact("C1", done_when="contains:scripts/x.py:NEEDLE"),
            artifact("F1", done_when="file:scripts/repro/thing.wat"),
        ]})]
        total, missing, evaluable, manual = lcc.artifacts_missing_done_when(docs)
        self.assertEqual((total, missing), (4, []))
        self.assertEqual(evaluable, 2, "contains:/file: are machine-evaluable")
        self.assertEqual(manual, 2, "manual: is declared only")

    def test_done_when_all_manual_is_zero_evaluable_1335(self):
        """The shape four releases running shipped: nothing mechanically checked."""
        docs = [("a.yaml", {"artifacts": [
            artifact(f"M{i}", done_when="manual: ...") for i in range(9)]})]
        total, _missing, evaluable, manual = lcc.artifacts_missing_done_when(docs)
        self.assertEqual((total, evaluable, manual), (9, 0, 9))

    def test_done_when_blank_counts_missing(self):
        docs = [("a.yaml", {"artifacts": [artifact("A", done_when="  ")]})]
        self.assertEqual(lcc.artifacts_missing_done_when(docs)[1], ["A"])

    def test_review_declared_commit_1161(self):
        """#1161: the DECLARED commit must win over any cited sha.

        The old harvest took every hex token and accepted the first that was
        an ancestor, so on v0.63 it reported a commit the record merely CITES
        (`e3a09ac2`) instead of the one it declares (`f810d2f5`)."""
        rec = (
            "# v0.63.0 cold review\n\n"
            "- **Commit reviewed:** `f810d2f5` (`release(...)`), PR #1175.\n"
            "- I rebuilt the pre-fix compiler at `858ff8d0` to reproduce it.\n"
            "- Gates re-run at `e3a09ac2`.\n"
        )
        self.assertEqual(lcc.review_declared_commit(rec), "f810d2f5")
        # the cited shas are still harvested, but never preferred
        harvested = lcc.review_record_shas(rec)
        self.assertIn("858ff8d0", harvested)
        self.assertIn("e3a09ac2", harvested)
        # a record with no declaration falls back rather than inventing one
        self.assertIsNone(
            lcc.review_declared_commit("no declaration here, just `858ff8d0`"))
        # tolerate the formatting variants a human record uses
        for variant in ("**Commit reviewed:** `abc1234`",
                        "- Commit reviewed: `abc1234`",
                        "  **Commit reviewed** `abc1234`"):
            self.assertEqual(lcc.review_declared_commit(variant), "abc1234",
                             f"variant not parsed: {variant!r}")

    def test_ci_emulation_floor(self):
        # RQ-63-FLOOREQ: BOTH spellings must be recognised. A derivation coupled
        # to the older one reports the STRONGER gate as absent — which is what
        # happened when --exact- landed, and is why this test now pins both.
        self.assertEqual(
            lcc.ci_emulation_floor("x\n --min-emulation-floor 322754 \\\n"),
            (322754, "min"))
        self.assertEqual(
            lcc.ci_emulation_floor("x\n --exact-emulation-floor 324845 \\\n"),
            (324845, "exact"))
        # when both appear, the stronger form is reported
        self.assertEqual(
            lcc.ci_emulation_floor(
                " --min-emulation-floor 1 \\\n --exact-emulation-floor 2 \\\n"),
            (2, "exact"))
        self.assertEqual(
            lcc.ci_emulation_floor("oracle_wiring_check.py --json out"), (0, ""))

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
        # RQ-81-SILENT: a GREEN shape now has to report an outcome. This fixture
        # was accurate under the old rules and became incomplete when the rule
        # tightened — the fixture changed, not the rule.
        docs = [("artifacts/release-v0.61/RQ-61-X.yaml",
                 {"artifacts": [artifact("RQ-61-X", verified_by="DELIVERED. fixture")]})]
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
        # mk_check() runs at v0.61.0, so the discharging artifact must be
        # scoped to v0.61. Before release scoping this fixture carried no
        # `release:` at all and passed anyway -- which was the bug.
        c = mk_check()
        docs = [("artifacts/release-v0.61/RQ-61-ARCHMODEL.yaml",
                 {"artifacts": [artifact("RQ-61-ARCHMODEL",
                  tags=["aadl", "spar", "feature-loop"], issue="#1136",
                  release="v0.61")]})]
        with mock.patch.object(lcc, "git", return_value=(0, "")), \
             mock.patch.object(lcc.Check, "load_checkout_docs", return_value=docs):
            c.step_1_2()
        self.assertEqual(c.findings[0][2], lcc.NA_FILED)
        self.assertIn("RQ-61-ARCHMODEL", c.findings[0][3])

    def test_previous_releases_filing_does_not_discharge_this_one(self):
        # The live v0.65 shape: only an OLDER release's artifact exists.
        c = mk_check()  # v0.61.0
        docs = [("artifacts/release-v0.59/RQ-59-ARCHMODEL.yaml",
                 {"artifacts": [artifact("RQ-59-ARCHMODEL",
                  tags=["aadl", "spar", "feature-loop"], issue="#1136",
                  release="v0.59")]})]
        with mock.patch.object(lcc, "git", return_value=(0, "")), \
             mock.patch.object(lcc.Check, "load_checkout_docs", return_value=docs):
            c.step_1_2()
        self.assertEqual(c.findings[0][2], lcc.DERIVED_FAIL)
        self.assertIn("RQ-59-ARCHMODEL", c.findings[0][3])
        self.assertIn("v0.61", c.findings[0][3])

    def test_unreleased_artifact_does_not_discharge(self):
        # An artifact with no `release:` is programme-scoped, not this
        # release's filing.
        c = mk_check()
        docs = [("artifacts/x.yaml",
                 {"artifacts": [artifact("RQ-X", tags=["spar", "feature-loop"],
                  issue="#1136")]})]
        with mock.patch.object(lcc, "git", return_value=(0, "")), \
             mock.patch.object(lcc.Check, "load_checkout_docs", return_value=docs):
            c.step_1_2()
        self.assertEqual(c.findings[0][2], lcc.DERIVED_FAIL)


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


class Step7PriorReleaseBar(unittest.TestCase):
    """RQ-80-STEP7 (#1456). Step 7 used to compute an ancestry test and return
    DERIVED_PASS on BOTH branches, so the effective bar was "the declared object
    exists" and a record naming a PREVIOUS release's commit passed. The
    replacement bar: the declared sha must not be an ancestor of (or equal to)
    the previous release tag.

    The shas are DERIVED FROM TAGS rather than hardcoded, so the test does not
    rot when history is rewritten, and it SKIPS LOUDLY on a shallow clone rather
    than passing vacuously.
    """

    def _sha(self, rev):
        rc, out = lcc.git("rev-parse", "--verify", "-q", f"{rev}^{{commit}}")
        return out.strip() if rc == 0 else None

    def _verdict(self, declared):
        c = mk_check("v0.80.0", mode="pretag", sha=self._sha("HEAD"))
        rec = f"# r\n\n**Commit reviewed:** `{declared}`\n"
        with mock.patch.object(lcc, "tree_ls",
                               return_value=["docs/reviews/v0.80-cold-review.md"]), \
             mock.patch.object(lcc, "tree_read", return_value=rec):
            c.step_7()
        seven = [f for f in c.findings if f[0] == "7"]
        self.assertTrue(seven, "step 7 recorded no finding at all")
        return seven[0][2]

    def test_a_previous_releases_commit_is_red(self):
        for tag in ("v0.79.0", "v0.78.0"):
            sha = self._sha(tag)
            if sha is None:
                self.skipTest(f"{tag} not present (shallow clone) — the bar "
                              f"cannot be exercised, and a pass here would be "
                              f"vacuous")
            with self.subTest(tag=tag):
                self.assertIn(self._verdict(sha), lcc.FAILING,
                              f"a record declaring {tag}'s commit must RED")

    def test_a_head_not_in_the_previous_release_passes(self):
        head = self._sha("HEAD")
        prev = self._sha("v0.79.0")
        if head is None or prev is None:
            self.skipTest("HEAD or v0.79.0 unresolvable; skipping loudly")
        rc, _ = lcc.git("merge-base", "--is-ancestor", head, prev)
        if rc == 0:
            self.skipTest("HEAD is an ancestor of v0.79.0, so it is not a "
                          "legitimate v0.80 declaration on this checkout")
        self.assertEqual(self._verdict(head), lcc.DERIVED_PASS)

    def test_missing_previous_tag_is_attested_not_passed(self):
        """A release with no visible predecessor must SKIP LOUDLY. v9.0.0 has
        minor 0, which `previous_release_tag` answers None for by construction."""
        c = mk_check("v9.0.0", mode="pretag", sha=self._sha("HEAD"))
        rec = "# r\n\n**Commit reviewed:** `" + (self._sha("HEAD") or "d" * 40) + "`\n"
        with mock.patch.object(lcc, "tree_ls",
                               return_value=["docs/reviews/v9.0-cold-review.md"]), \
             mock.patch.object(lcc, "tree_read", return_value=rec):
            c.step_7()
        seven = [f for f in c.findings if f[0] == "7"]
        self.assertTrue(seven)
        self.assertEqual(seven[0][2], lcc.ATTESTED)
        self.assertIn("no", seven[0][3].lower())


class Step3EmptyValuedOutcomeKey(unittest.TestCase):
    """v0.81 round-1 cold review, findings 2 and 3.

    Both are the release's OWN theme turned on the release's own rules: a case
    that is out of the population reads as compliant.
    """

    def _docs(self, *fieldsets):
        return [("p.yaml", {"artifacts": [
            {"id": f"RQ-X-{i}", "fields": f} for i, f in enumerate(fieldsets)]})]

    def test_an_empty_valued_landed_key_is_SILENT(self):
        # PRE-FIX this returned (1, []) — the key was PRESENT, so the artifact
        # counted as reporting an outcome. R11 needs a NON-EMPTY value, so a
        # present-but-blank key was invisible to BOTH rules.
        total, silent = lcc.artifacts_reporting_nothing(self._docs({"landed": ""}))
        self.assertEqual((total, silent), (1, ["RQ-X-0"]))

    def test_a_VALUELESS_landed_key_is_SILENT(self):
        # A bare `landed:` in YAML parses to None, and `str(None)` is the
        # four-character string "None" — non-empty and truthy. That is R11's own
        # idiom, and copying it here would have swapped one hole for another.
        total, silent = lcc.artifacts_reporting_nothing(self._docs({"landed": None}))
        self.assertEqual((total, silent), (1, ["RQ-X-0"]))

    def test_blank_disposition_and_blank_verified_by_are_SILENT_too(self):
        # The twin check: a fix applied to one of three keys and not the others
        # is the shape this programme has had to correct repeatedly.
        for key in ("disposition", "verified-by", "landed"):
            with self.subTest(key=key):
                _t, silent = lcc.artifacts_reporting_nothing(self._docs({key: "   "}))
                self.assertEqual(silent, ["RQ-X-0"], f"blank {key} must be silent")

    def test_CONTROL_a_real_value_still_reports_an_outcome(self):
        # Without this, the four above are satisfied by a rule that calls
        # EVERYTHING silent, which would red every delivered release.
        for key, val in (("landed", "#1480"), ("disposition", "refuted"),
                         ("verified-by", "DELIVERED. ...")):
            with self.subTest(key=key):
                _t, silent = lcc.artifacts_reporting_nothing(self._docs({key: val}))
                self.assertEqual(silent, [], f"{key}={val!r} must NOT be silent")

    def test_CONTROL_the_live_tree_has_no_silent_artifact(self):
        # The fix must not red the release it ships in.
        import glob
        import yaml
        docs = []
        for f in sorted(glob.glob("artifacts/release-v0.81/*.yaml")):
            with open(f) as fh:
                docs.append((f, yaml.safe_load(fh)))
        if not docs:
            self.skipTest("no v0.81 artifacts at this path — cannot exercise")
        total, silent = lcc.artifacts_reporting_nothing(docs)
        self.assertEqual(silent, [], f"live v0.81 has silent artifacts: {silent}")
        self.assertGreaterEqual(total, 11, "population too small to trust")


class Step3ReportedOutcome(unittest.TestCase):
    """RQ-81-SILENT (#1458 + #1476). OUT OF POPULATION IS INDISTINGUISHABLE FROM
    COMPLIANT: an artifact recording NO outcome is invisible to every rule that
    reads `verified-by`/`disposition`/`landed`, and R11 cannot see it because its
    branch requires a non-empty `landed:`.

    The red-first evidence is REAL HISTORY, not a planted fixture: at 5ad2662f
    (main immediately before the v0.80 record PR) two `must` artifacts were silent
    with every structured gate green; at 6950aa99 they are not. Both are asserted
    below and the test SKIPS LOUDLY if the commits are unreachable rather than
    passing vacuously.
    """

    def _docs_at(self, ref, rid):
        rc, _ = lcc.git("rev-parse", "--verify", "-q", f"{ref}^{{commit}}")
        if rc != 0:
            return None
        docs = []
        for path in lcc.tree_ls(ref, f"artifacts/release-{rid}/"):
            name = os.path.basename(path)
            if name in ("_release.yaml", "_release.yml"):
                continue
            if not name.endswith((".yaml", ".yml")):
                continue
            docs.append((path, yaml.safe_load(lcc.tree_read(ref, path) or "")))
        return docs

    def test_the_pure_helper_names_the_silent_ids(self):
        docs = [
            ("a.yaml", {"artifacts": [{"id": "RQ-X-SPEAKS",
                                       "fields": {"verified-by": "DELIVERED. x"}}]}),
            ("b.yaml", {"artifacts": [{"id": "RQ-X-DISPOSED",
                                       "fields": {"disposition": "deferred"}}]}),
            ("c.yaml", {"artifacts": [{"id": "RQ-X-LANDED",
                                       "fields": {"landed": "#1"}}]}),
            ("d.yaml", {"artifacts": [{"id": "RQ-X-SILENT",
                                       "fields": {"issue": "#9", "priority": "must"}}]}),
        ]
        total, silent = lcc.artifacts_reporting_nothing(docs)
        self.assertEqual(total, 4)
        self.assertEqual(silent, ["RQ-X-SILENT"],
                         "any ONE of verified-by/disposition/landed counts as "
                         "reporting; only the artifact with none of them is silent")

    def test_an_artifact_with_no_fields_key_at_all_is_silent(self):
        total, silent = lcc.artifacts_reporting_nothing(
            [("a.yaml", {"artifacts": [{"id": "RQ-X-NOFIELDS"}]})])
        self.assertEqual((total, silent), (1, ["RQ-X-NOFIELDS"]),
                         "a missing `fields` map must not crash and must not "
                         "read as compliant")

    def test_empty_population_is_not_a_pass(self):
        total, silent = lcc.artifacts_reporting_nothing([])
        self.assertEqual((total, silent), (0, []))
        # step_3 refuses total == 0 ABOVE this slot (the #1064 zero-artifact
        # shape), which is what stops a DERIVED_PASS here being vacuous. This
        # asserts the helper reports the zero rather than inventing a pass.

    def test_red_first_on_real_history_5ad2662f(self):
        docs = self._docs_at("5ad2662f", "v0.80")
        if docs is None:
            self.skipTest("5ad2662f unreachable (shallow clone) — the red-first "
                          "anchor cannot be asserted, skipping LOUDLY rather "
                          "than passing")
        total, silent = lcc.artifacts_reporting_nothing(docs)
        self.assertEqual(total, 11)
        self.assertEqual(sorted(silent), ["RQ-80-PAGESIZE2", "RQ-80-WIDEFILE3"],
                         "the two `must` artifacts that reached the v0.80 "
                         "candidate silent while every structured gate was green")

    def test_green_after_the_record_landed_6950aa99(self):
        docs = self._docs_at("6950aa99", "v0.80")
        if docs is None:
            self.skipTest("6950aa99 unreachable (shallow clone) — skipping LOUDLY")
        total, silent = lcc.artifacts_reporting_nothing(docs)
        self.assertEqual((total, silent), (11, []),
                         "the record PR gave both artifacts a disposition and a "
                         "verified-by, so the rule must go green on the same tree "
                         "it reds one commit earlier")


class Step8NpmLive(unittest.TestCase):
    """RQ-80-NPM (#1460). Step 8 asked only about `scripts/publish.rs` — the CARGO
    surface — so npm publication had no assertion anywhere and the package went
    ten releases behind while reports truthfully said three release workflows
    succeeded. `Release NPM` is a FOURTH, and it failed its auth preflight every
    time.

    These stub the HTTP layer so the tests do not depend on the live registry: a
    network-dependent gate test is a gate that goes quiet when the network does.
    """

    def _run(self, pkg_json, status, version="v0.80.0", mode="retro"):
        c = mk_check(version, mode=mode)
        reads = {"npm/package.json": pkg_json, "scripts/publish.rs": ""}
        with mock.patch.object(lcc, "tree_read",
                               side_effect=lambda ref, p: reads.get(p, "")), \
             mock.patch.object(lcc, "tree_has", return_value=True), \
             mock.patch.object(lcc, "http_status", return_value=status), \
             mock.patch.object(lcc, "changelog_structure_verdict",
                               return_value=(lcc.ATTESTED, "stubbed")), \
             mock.patch.object(c, "check_run_conclusion", return_value="success"):
            c.step_8()
        got = [f for f in c.findings if f[1] == "npm live"]
        self.assertTrue(got, "step 8 recorded no `npm live` finding at all")
        return got[0]

    PKG = '{"name": "@pulseengine/synth", "version": "0.80.0"}'

    def test_missing_from_the_registry_is_red(self):
        self.assertEqual(self._run(self.PKG, 404)[2], lcc.DERIVED_FAIL)

    def test_present_in_the_registry_passes(self):
        self.assertEqual(self._run(self.PKG, 200)[2], lcc.DERIVED_PASS)

    def test_unreachable_registry_is_not_derived_rather_than_green(self):
        """An unreachable registry must not read as published."""
        self.assertEqual(self._run(self.PKG, 0)[2], lcc.NOT_DERIVED)

    def test_an_unbumped_manifest_is_red_even_if_that_version_is_live(self):
        """The old version resolving is exactly how an unbumped manifest would
        look green. Name and version are DERIVED from the ref's own manifest."""
        stale = '{"name": "@pulseengine/synth", "version": "0.79.0"}'
        f = self._run(stale, 200)
        self.assertEqual(f[2], lcc.DERIVED_FAIL)
        self.assertIn("not bumped", f[3])

    def test_absent_manifest_is_not_derived(self):
        self.assertEqual(self._run("", 200)[2], lcc.NOT_DERIVED)

    def test_unparseable_manifest_is_not_derived(self):
        self.assertEqual(self._run("{not json", 200)[2], lcc.NOT_DERIVED)

    def test_pretag_is_na_by_moment_not_a_false_red(self):
        """Demanding publication BEFORE the tag would invent evidence."""
        self.assertEqual(self._run(self.PKG, 404, mode="pretag")[2], lcc.NA_MOMENT)

    def test_it_runs_even_when_the_crates_check_would_bail(self):
        """Placed BEFORE the crates block, which returns early on an unparseable
        CRATES_TO_PUBLISH — otherwise npm would go silent exactly when something
        else had already gone wrong."""
        c = mk_check("v0.80.0", mode="retro")
        reads = {"npm/package.json": self.PKG, "scripts/publish.rs": ""}
        with mock.patch.object(lcc, "tree_read",
                               side_effect=lambda ref, p: reads.get(p, "")), \
             mock.patch.object(lcc, "tree_has", return_value=True), \
             mock.patch.object(lcc, "http_status", return_value=404), \
             mock.patch.object(lcc, "changelog_structure_verdict",
                               return_value=(lcc.ATTESTED, "stubbed")), \
             mock.patch.object(c, "check_run_conclusion", return_value="success"):
            c.step_8()
        labels = {f[1]: f[2] for f in c.findings}
        # the crates block really did bail (empty publish.rs -> unparseable list)
        self.assertEqual(labels.get("crates live"), lcc.NOT_DERIVED,
                         "the premise of this test is that crates bails here")
        # ...and npm was still recorded, which is the property under test
        self.assertEqual(labels.get("npm live"), lcc.DERIVED_FAIL)


if __name__ == "__main__":
    unittest.main(verbosity=2)
