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


if __name__ == "__main__":
    unittest.main(verbosity=2)
