#!/usr/bin/env python3
"""Unit tests for the pure parts of scripts/mutation_survey.py.

RQ-66-DELETE (#242): the `want_reach_wide` check is the pin that turned
v0.65's four DEAD deletion candidates into four guarded reachable sites. A
checker whose failure branch was never exercised is the v0.57 class ("the
checkers were the defects"), so the decision function is pure and driven
here from both sides: a silent witness must FAIL, a reach that merely widened
must PASS, and the two ways a config can be absent are told apart.

Run: python3 scripts/test_mutation_survey.py
"""
import importlib.util
import os
import pathlib
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# The module resolves its target dir at import; keep the test hermetic.
os.environ.setdefault("CARGO_TARGET_DIR", str(ROOT / "target"))
_spec = importlib.util.spec_from_file_location("mutation_survey", ROOT / "scripts/mutation_survey.py")
ms = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ms)


class ReachWideFailures(unittest.TestCase):
    WANT = {
        "m7dp-reloc": ["vfp_local_pressure_1069.wat", "vfp_spill_881.wat"],
        "graph-alloc-reloc": ["a32_i64_615.wat"],
    }

    def test_every_witness_still_reaching_passes(self):
        got = {
            "m7dp-reloc": ["vfp_local_pressure_1069.wat", "vfp_spill_881.wat"],
            "graph-alloc-reloc": ["a32_i64_615.wat"],
        }
        self.assertEqual(ms.reach_wide_failures(self.WANT, got), [])

    def test_reach_widening_is_not_a_failure(self):
        # SUBSET semantics: a new module reaching the site needs no ledger edit.
        got = {
            "m7dp-reloc": ["new_fixture.wat", "vfp_local_pressure_1069.wat", "vfp_spill_881.wat"],
            "graph-alloc-reloc": ["a32_i64_615.wat", "zzz.wat"],
            "graph-alloc-self": ["a32_i64_615.wat"],  # an unpinned config is ignored
        }
        self.assertEqual(ms.reach_wide_failures(self.WANT, got), [])

    def test_one_silent_witness_fails_by_name(self):
        got = {
            "m7dp-reloc": ["vfp_local_pressure_1069.wat"],  # vfp_spill_881 went silent
            "graph-alloc-reloc": ["a32_i64_615.wat"],
        }
        self.assertEqual(ms.reach_wide_failures(self.WANT, got), [("m7dp-reloc", "vfp_spill_881.wat")])

    def test_a_config_that_vanished_fails_every_witness_in_it(self):
        got = {"m7dp-reloc": ["vfp_local_pressure_1069.wat", "vfp_spill_881.wat"]}
        self.assertEqual(ms.reach_wide_failures(self.WANT, got), [("graph-alloc-reloc", "a32_i64_615.wat")])

    def test_no_evidence_at_all_fails_everything(self):
        # A deleted site or an unusable probe yields no reach_wide: every
        # pinned witness is silent, so the pin cannot pass vacuously.
        silent = ms.reach_wide_failures(self.WANT, None)
        self.assertEqual(len(silent), 3)
        self.assertEqual(silent, ms.reach_wide_failures(self.WANT, {}))

    def test_nothing_pinned_is_never_a_failure(self):
        self.assertEqual(ms.reach_wide_failures({}, {"m7dp-reloc": []}), [])
        self.assertEqual(ms.reach_wide_failures(None, None), [])


class ClassifyIdentical(unittest.TestCase):
    # The salvage of DEAD as a category: DEAD only when unreached everywhere.
    def test_corpus_reached_is_equivalent_whatever_wide_says(self):
        self.assertEqual(ms.classify_identical(True, None), ("EQUIVALENT", None))
        self.assertEqual(ms.classify_identical(True, {"m7dp-reloc": ["x.wat"]}), ("EQUIVALENT", None))

    def test_unreached_everywhere_is_dead(self):
        self.assertEqual(ms.classify_identical(False, {"m7dp-reloc": [], "graph-alloc-reloc": []}), ("DEAD", None))

    def test_reached_only_under_wide_is_unresolved_not_dead(self):
        # v0.65's four: unreached on the corpus, reached under REACH_CFGS.
        cls, note = ms.classify_identical(False, {"m7dp-reloc": ["vfp_spill_881.wat"], "m7dp-self": []})
        self.assertEqual(cls, "UNRESOLVED")
        self.assertIn("m7dp-reloc", note)
        self.assertIn("neither DEAD nor EQUIVALENT", note)

    def test_no_wide_probe_is_dead_with_a_caveat(self):
        cls, note = ms.classify_identical(False, None)
        self.assertEqual(cls, "DEAD")
        self.assertIn("CORPUS_CFGS only", note)


class ReachCfgsShape(unittest.TestCase):
    def test_reach_cfgs_are_disjoint_from_corpus_cfgs(self):
        # The ledger's baseline hashes are relative to CORPUS_CFGS; REACH_CFGS
        # must never silently become part of that population.
        self.assertFalse(set(ms.REACH_CFGS) & set(ms.CORPUS_CFGS))
        for cfg, (flags, env) in ms.REACH_CFGS.items():
            self.assertIn("--target", flags, cfg)
            self.assertIsInstance(env, dict, cfg)

    def test_reach_cfgs_cover_both_findings(self):
        # A hard-float target (the VFP retry ladder) AND the flag-on spike
        # (the graph-alloc arbiter): drop either and one finding goes unguarded.
        hard_float = [c for c, (f, _) in ms.REACH_CFGS.items() if f[f.index("--target") + 1] in ("cortex-m7dp", "cortex-m4f")]
        flag_on = [c for c, (_, e) in ms.REACH_CFGS.items() if e.get("SYNTH_GRAPH_ALLOC") == "1"]
        self.assertTrue(hard_float, "no hard-float configuration in REACH_CFGS")
        self.assertTrue(flag_on, "no SYNTH_GRAPH_ALLOC configuration in REACH_CFGS")


class MutantsCiGateArithmetic(unittest.TestCase):
    """#1243 — the CI summary gate's floors must be NUMBERS, not digit shapes.

    The old form asserted `subset=[4-9][0-9]*`, meaning "first digit is 4-9",
    so it accepted 4-9 and 40-99 and rejected 10-39. RQ-66-DELETE grew the
    pinned subset 7 -> 10 and the job failed while reporting a healthy result.
    The regression that matters is not "the regex was wrong" but "a floor
    reddened when the guarded quantity IMPROVED", so both directions are
    asserted here rather than only the one that broke.
    """

    def setUp(self):
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "ci_mutants_gate", pathlib.Path(__file__).with_name("ci_mutants_gate.py"))
        self.gate_mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.gate_mod)

    def test_selftest_cases_all_hold(self):
        for label, text, expect_pass in self.gate_mod.SELFTEST:
            with self.subTest(label):
                self.assertEqual(not self.gate_mod.gate(text), expect_pass, label)

    def test_the_exact_1243_output_passes(self):
        # The literal job output that the character-class regex rejected.
        text = ("MUTANTS-CI subset=10 controls=3 non-killed=7 failures=0\n"
                "MUTANTS-REACH-WIDE entries=4 reached=4 unreached=0\n")
        self.assertEqual(self.gate_mod.gate(text), [])

    def test_growth_past_nine_never_reddens(self):
        # The whole 10-39 band the old assertion refused, plus beyond it.
        for subset in (10, 17, 39, 40, 100):
            text = (f"MUTANTS-CI subset={subset} controls=3 non-killed=7 failures=0\n"
                    "MUTANTS-REACH-WIDE entries=4 reached=4 unreached=0\n")
            with self.subTest(subset=subset):
                self.assertEqual(self.gate_mod.gate(text), [])

    def test_shrinking_below_the_floor_still_reddens(self):
        # The gate must not have been loosened into vacuity by the fix.
        text = ("MUTANTS-CI subset=3 controls=1 non-killed=1 failures=0\n"
                "MUTANTS-REACH-WIDE entries=4 reached=4 unreached=0\n")
        complaints = self.gate_mod.gate(text)
        self.assertEqual(len(complaints), 3, complaints)


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], "-v"])
