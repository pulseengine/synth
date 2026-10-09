#!/usr/bin/env python3
"""Tests for scripts/verdict_prose_check.py (RQ-80-SENTENCE, #1461).

The script's own `--self-test` proves the RULE is potent. These test the SCRIPT:
the refusal on an empty population, the #1430 carve-out, and that a grammatical
accident in the leading position is not read as a verdict.
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verdict_prose_check as V  # noqa: E402


def art(status, verified_by, disposition=None):
    fields = {"verified-by": verified_by}
    if disposition:
        fields["disposition"] = disposition
    return {"id": "RQ-00-X", "status": status, "fields": fields}


class LeadingVerdict(unittest.TestCase):
    def test_complete_verdict_beside_non_claiming_status_is_bad(self):
        tok, bad, why = V.classify(art("proposed", "LANDED. it shipped"))
        self.assertEqual(tok, "LANDED")
        self.assertTrue(bad)
        self.assertIn("proposed", why)

    def test_complete_verdict_beside_non_delivery_disposition_is_bad(self):
        """The 28196ec7 shape: R11 ACCEPTS proposed+partial+landed as
        self-consistent, so this is coverage R11 cannot provide."""
        _tok, bad, why = V.classify(
            art("proposed", "LANDED. it shipped", disposition="partial"))
        self.assertTrue(bad)

    def test_incomplete_verdict_beside_claiming_status_is_bad(self):
        _tok, bad, _why = V.classify(art("implemented", "PENDING. not yet"))
        self.assertTrue(bad)

    def test_agreement_passes_both_ways(self):
        self.assertFalse(V.classify(art("implemented", "DELIVERED. done"))[1])
        self.assertFalse(V.classify(art("proposed", "PARTIAL. half"))[1])

    def test_refuted_beside_claiming_is_the_1430_carve_out(self):
        """Delivering a refutation IS delivery, and R11 FORBIDS
        `disposition: refuted` beside a claiming status — so no legal field can
        express it. Without the carve-out this reds RQ-77-PROSEBLIND, whose
        prose is right and whose fields cannot be."""
        _tok, bad, _why = V.classify(art("implemented", "REFUTED, and here is why"))
        self.assertFalse(bad)

    def test_not_delivered_is_a_phrase_not_the_bare_word(self):
        self.assertEqual(V.leading_verdict("NOT DELIVERED. nothing moved"),
                         "NOT DELIVERED")
        # `NOT` alone must not be read as a verdict: it can lead the OPPOSITE one.
        self.assertIsNone(V.leading_verdict("NOT a regression — delivered in full"))

    def test_grammatical_accidents_are_not_verdicts(self):
        # Both of these really do lead a `verified-by:` in this tree.
        self.assertIsNone(V.leading_verdict("FULL 243-MODULE CORPUS measured on ..."))
        self.assertIsNone(V.leading_verdict("DONE-WHEN BRANCH B, taken deliberately"))

    def test_no_all_caps_lead_is_out_of_population(self):
        self.assertIsNone(V.classify(art("implemented", "The work shipped.")))


class UnclassifiedLead(unittest.TestCase):
    """RQ-81-SILENT (#1476). `leading_verdict` returns None for TWO different
    situations — "not a verdict about the work" and "a verdict word no set
    knows" — and that conflation is the hole: an escape is indistinguishable
    from a legitimate opening. `unclassified_lead` separates them.
    """

    def test_the_four_measured_escapes_are_caught(self):
        for vb, want in (
            ("NOT LANDED. nothing in this lane moved at all", "NOT LANDED"),
            ("DONE. shipped and measured", "DONE"),
            ("NOT-DELIVERED. the hyphen makes it one unlisted token", "NOT-DELIVERED"),
            ("CLOSED. the work is finished and merged", "CLOSED"),
        ):
            with self.subTest(vb=vb):
                self.assertEqual(V.unclassified_lead(vb), want)

    def test_not_landed_is_the_sharpest_case(self):
        """Excluding a bare leading `NOT` means NOT + any COMPLETE word is
        unclassified. That consequence was documented nowhere, and it is the
        inverse of the contradiction the gate was built for."""
        self.assertIsNone(V.leading_verdict("NOT LANDED. nothing moved"),
                          "leading_verdict cannot see it — that is the defect")
        self.assertEqual(V.unclassified_lead("NOT LANDED. nothing moved"),
                         "NOT LANDED", "unclassified_lead must name it")

    def test_a_classified_verdict_is_not_an_escape(self):
        for vb in ("DELIVERED. x", "PARTIAL. x", "NOT DELIVERED. x", "REFUTED. x"):
            with self.subTest(vb=vb):
                self.assertIsNone(V.unclassified_lead(vb))

    def test_a_declared_non_verdict_is_not_an_escape(self):
        for vb in ("THE census says", "MEASURED over 26 runs", "ORACLE landed",
                   "CLASSIFICATION rather than a count", "TRIAGE of the window",
                   "RULE as written", "ADDED a slot", "BYTE IDENTITY holds",
                   "EVERY ATTRIBUTION checked"):
            with self.subTest(vb=vb):
                self.assertIsNone(V.unclassified_lead(vb),
                                  "members of NOT_A_VERDICT are DELIBERATE "
                                  "exclusions, not escapes")

    def test_prose_that_is_not_all_caps_is_not_verdict_shaped(self):
        self.assertIsNone(V.unclassified_lead("The census says nothing"))
        self.assertIsNone(V.unclassified_lead(""))

    def test_not_a_verdict_is_now_LOAD_BEARING(self):
        """Before `unclassified_lead` the set was INERT: every member was already
        outside COMPLETE u INCOMPLETE, so its branch was followed by a path that
        returned None anyway, and deleting it changed no verdict. Here removing a
        member turns a declared non-verdict into a reported escape, which is the
        effect the set was always documented as having."""
        self.assertIsNone(V.unclassified_lead("THE census says"))
        saved = set(V.NOT_A_VERDICT)
        try:
            V.NOT_A_VERDICT.discard("THE")
            self.assertEqual(V.unclassified_lead("THE census says"), "THE",
                             "with THE removed the same prose becomes an escape "
                             "— so the set has an effect")
        finally:
            V.NOT_A_VERDICT.clear()
            V.NOT_A_VERDICT.update(saved)
        self.assertIsNone(V.unclassified_lead("THE census says"),
                          "and the set was restored")

    def test_the_live_tree_has_no_escapes(self):
        """The gate must be GREEN on real history, or it is a gate nobody can
        move honestly (RQ-74-STALEMSG). The six live unclassified openings were
        added to NOT_A_VERDICT as MEASURED exclusions for exactly this reason."""
        esc = [a["id"] for _f, a in V.artifacts(".")
               if isinstance((a.get("fields") or {}).get("verified-by"), str)
               and V.unclassified_lead(a["fields"]["verified-by"])]
        self.assertEqual(esc, [], f"unclassified leads on the live tree: {esc}")


class PopulationRefusal(unittest.TestCase):
    def test_zero_population_refuses_rather_than_passing(self):
        """A DERIVED POPULATION OF ZERO IS A REFUSAL, NOT A PASS. Point the
        script at a tree with no artifacts and it must exit 2, not 0."""
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "artifacts").mkdir()
            argv = sys.argv
            sys.argv = ["verdict_prose_check.py", "--root", d]
            try:
                rc = V.main()
            finally:
                sys.argv = argv
        self.assertEqual(rc, 2)


class SelfTestIsWired(unittest.TestCase):
    def test_self_test_passes_on_this_tree(self):
        """If the self-test cannot run here, the potency evidence is absent and
        the verdict run alone would be a gate nobody has watched fire."""
        self.assertEqual(V.self_test("."), 0)


class SentenceScopeHazard1476(unittest.TestCase):
    """RQ-82-FIRSTTOKEN (#1476): sentence scope was measured and REFUSED, and the
    refusal needs a GUARD, not just a comment. The hazard is specific: a wider
    rule that scans the opening sentence for a verdict word INVERTS negation,
    because the only negated phrase in the vocabulary is `NOT DELIVERED` — so
    `NOT LANDED` yields the COMPLETE word `LANDED`. These tests fire the moment
    someone widens the rule without handling that."""

    NEGATED = ("NOT LANDED yet", "NOT SHIPPED in this release", "NOT VERIFIED",
               "NOT COMPLETE", "no work was SHIPPED")

    def test_a_negated_verdict_is_NEVER_classified_as_COMPLETE(self):
        """The invariant the refusal rests on. Today each returns None (out of
        population, and `unclassified_lead` names it). A naive widening would
        return LANDED / SHIPPED / VERIFIED / COMPLETE here — all in COMPLETE —
        and this assertion is what stops that shipping silently."""
        for vb in self.NEGATED:
            with self.subTest(prose=vb):
                self.assertNotIn(V.leading_verdict(vb), V.COMPLETE,
                                 "a negated verdict read as COMPLETE inverts the "
                                 "artifact's own statement about itself")

    def test_the_only_negated_phrase_in_the_vocabulary_is_NOT_DELIVERED(self):
        """The REASON the inversion exists, pinned so it is not rediscovered: if
        a future lane adds `NOT LANDED` et al. to INCOMPLETE, the inversion risk
        changes shape and the refusal above must be re-derived."""
        negated = {x for x in V.INCOMPLETE if x.startswith("NOT ")}
        self.assertEqual(negated, {"NOT DELIVERED"},
                         "the negated vocabulary moved; re-run the #1476 "
                         "measurement before widening the rule's scope")

    def test_the_generic_opener_hole_is_still_OPEN_and_that_is_recorded(self):
        """Honesty guard. This lane did NOT close #1476; it priced the fix. If a
        later change closes the hole, this test fires and the artifact's verdict
        must be updated rather than left claiming a refusal that no longer holds."""
        for vb in ("RULE DELIVERED in full", "EVERY ask SHIPPED",
                   "THE work is DELIVERED"):
            with self.subTest(prose=vb):
                self.assertIsNone(V.leading_verdict(vb))
                self.assertIsNone(V.unclassified_lead(vb),
                                  "still outside BOTH populations — the #1476 hole")


class EscapeIsEnforcedByThisModule(unittest.TestCase):
    """RQ-84-FIRSTTOKEN3 (#1476). `unclassified_lead` NAMED the hole, but
    `classify` never called it — so the module that DEFINES the escape did not
    refuse on it. Enforcement lived only in `loop_conformance_check` step 3,
    which is scoped to the release being cut and therefore ran over an EMPTY
    population at plan time: 14 artifacts scanned, none carrying a
    `verified-by`, reported NOT-DERIVED. Measured at the v0.84 base before
    wiring: ZERO escapes over a population of 216, so this reds nothing that
    exists today.
    """

    def test_an_escape_is_IN_the_population_and_BAD(self):
        got = V.classify(art("implemented", "NOT LANDED. nothing in this lane moved"))
        self.assertIsNotNone(got, "an escape must NOT be out of population")
        tok, bad, why = got
        self.assertEqual(tok, "NOT LANDED")
        self.assertTrue(bad)
        self.assertIn("1476", why, "the message must name the issue to act on")

    def test_every_measured_escape_is_caught_whatever_the_status(self):
        for vb in ("NOT LANDED. nothing moved", "DONE. shipped and measured",
                   "NOT-DELIVERED. the hyphen makes it one unlisted token",
                   "CLOSED. the work is finished"):
            for status in ("proposed", "implemented", "verified", "accepted"):
                with self.subTest(vb=vb, status=status):
                    got = V.classify(art(status, vb))
                    self.assertIsNotNone(got)
                    self.assertTrue(got[1])

    def test_CONTROL_a_declared_non_verdict_stays_OUT_of_population(self):
        """The paired control: without this, the wiring would be a blanket
        catch rather than an escape detector. `NOT_A_VERDICT` members and
        non-all-caps prose must still leave the population."""
        for vb in ("MEASURED over 26 runs", "THE census says",
                   "ORACLE landed", "The work shipped."):
            with self.subTest(vb=vb):
                self.assertIsNone(V.classify(art("implemented", vb)))


if __name__ == "__main__":
    unittest.main(verbosity=2)
