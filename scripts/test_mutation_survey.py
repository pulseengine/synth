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


class ClassifyUnrunnable(unittest.TestCase):
    """RQ-66-POTENCY (#1189): scripts/mutation_survey.py used to score ANY
    non-zero oracle exit as a KILL. 147 of 196 ci.yml L1 steps invoke bare
    `python`, absent on the machine this was measured on, so a re-survey
    nearly published a fabricated 0 % survival (147 dead oracles read as 147
    working ones). `classify_unrunnable` is the decision that must now gate
    every suite step before it can be scored: UNRUNNABLE means the step never
    executed (refuse), everything else means it ran and is a different thing
    (a real red, or a real pass) that must not be treated the same way.
    Every non-None case here is captured verbatim from this machine, not
    invented — see the PR description for the exact commands run.
    """

    def test_green_is_never_unrunnable(self):
        self.assertIsNone(ms.classify_unrunnable(0, ""))
        self.assertIsNone(ms.classify_unrunnable(0, "anything at all, even scary-looking text\nImportError: x"))

    def test_exit_127_command_not_found_is_unrunnable(self):
        # Captured verbatim: `bash -c "python nonexistent_script.py"` on this
        # machine, where bare `python` does not exist.
        out = "bash: python: command not found\n"
        reason = ms.classify_unrunnable(127, out)
        self.assertIsNotNone(reason)
        self.assertIn("python", reason)

    def test_exit_127_with_no_recognizable_text_is_still_unrunnable(self):
        # The exit code alone is dispositive for 127/126 — a step must not
        # need to ALSO match a text pattern to be caught.
        self.assertIsNotNone(ms.classify_unrunnable(127, ""))
        self.assertIsNotNone(ms.classify_unrunnable(126, "permission denied, no useful text"))

    def test_module_not_found_is_unrunnable_even_at_exit_1(self):
        # Captured verbatim: `python3 -c "import nonexistent_package_xyz"`.
        out = (
            "Traceback (most recent call last):\n"
            '  File "<string>", line 1, in <module>\n'
            "    import nonexistent_package_xyz\n"
            "ModuleNotFoundError: No module named 'nonexistent_package_xyz'\n"
        )
        reason = ms.classify_unrunnable(1, out)
        self.assertIsNotNone(reason)
        self.assertIn("nonexistent_package_xyz", reason)

    def test_env_shebang_missing_interpreter_is_unrunnable(self):
        # Captured verbatim: a `#!/usr/bin/env pythonzzz` script executed
        # directly on this (BSD env) machine.
        out = "env: pythonzzz: No such file or directory\n"
        reason = ms.classify_unrunnable(127, out)
        self.assertIsNotNone(reason)
        self.assertIn("pythonzzz", reason)

    def test_a_real_assertion_failure_is_not_unrunnable(self):
        # The step EXECUTED (real traceback from real logic, not an import or
        # shell-dispatch failure) and found something wrong. This is the
        # fact_spec_div_494_differential.py shape named in the brief: red
        # locally on an unmutated tree while green in CI is a REAL result,
        # not an environment failure, and must not be refused away.
        out = (
            "Traceback (most recent call last):\n"
            '  File "scripts/repro/fact_spec_div_494_differential.py", line 210, in <module>\n'
            "    assert observed == expected, f'divergence: {observed} != {expected}'\n"
            "AssertionError: divergence: 17 != 12\n"
        )
        self.assertIsNone(ms.classify_unrunnable(1, out))

    def test_a_stale_grep_assertion_after_a_passing_oracle_is_not_unrunnable(self):
        # A LIVE example from CI (v0.66, same week this fix was written): the
        # "home-register write audit sweep" job pipes an oracle's output
        # through `tee` and then chains `grep -Eq` assertions under
        # `set -euo pipefail` (.github/workflows/ci.yml, job
        # `home-alias-audit-oracle`). The oracle itself printed PASS on every
        # line that matters; a DIFFERENT, stale `grep` further down the same
        # step (pinning an exact count that had since moved) is what made the
        # STEP exit 1. `##[error]Process completed with exit code 1` is
        # exactly the shape defect 1 exists to stop trusting blindly — except
        # here the step genuinely EXECUTED and its own oracle said PASS, so
        # this is the "ran, and is a different thing" side, not "could not
        # run": scoring THIS step as an unrunnable environment failure would
        # be as wrong as scoring it a legitimate kill. Either way it is not
        # UNRUNNABLE, which is the one thing this function decides.
        out = (
            "functions audited: 7191\n"
            "homes watched: 8100\n"
            "POTENCY: PASS (192 planted writes reported, 0 without the plant, "
            "over 3 fixtures x 4 legs)\n"
            "WIDTH-1226: closed (.wast homes == .wat homes, merge refuses, same module text on 4 legs)\n"
            "hits: 0 (known-open: 0 [none], unexplained: 0)\n"
            "RESULT: PASS\n"
        )
        self.assertIsNone(ms.classify_unrunnable(1, out))

    def test_a_deliberate_missing_fixture_filenotfound_is_not_unrunnable(self):
        # A script's OWN FileNotFoundError (Python's `[Errno 2]` shape, e.g.
        # asserting a decline path when a fixture is intentionally absent) is
        # NOT the same signal as the shell or the loader failing to find an
        # interpreter or package — conflating the two is exactly the
        # over-broad match this test guards against (the brief: "refusing so
        # broadly that the survey can never run anywhere is not" right).
        out = (
            "Traceback (most recent call last):\n"
            '  File "scripts/repro/some_differential.py", line 42, in <module>\n'
            "    open('scripts/repro/fixtures/missing_on_purpose.wat')\n"
            "FileNotFoundError: [Errno 2] No such file or directory: "
            "'scripts/repro/fixtures/missing_on_purpose.wat'\n"
        )
        self.assertIsNone(ms.classify_unrunnable(1, out))

    def test_a_generic_importerror_from_application_logic_is_not_unrunnable(self):
        # A script's own version-guard ("ImportError: wasmtime too old") is
        # application logic, not "the package is not installed" — only the
        # narrower ModuleNotFoundError shape is trusted as environment signal.
        out = "ImportError: wasmtime 20.0 required, found 5.0\n"
        self.assertIsNone(ms.classify_unrunnable(1, out))


class DrawFrame(unittest.TestCase):
    """RQ-66-POTENCY (#1189): `cmd_run` used to unconditionally overwrite
    `ledger["meta"]` with its own argparse defaults on every invocation —
    v0.65 shipped `per_region: 12` in the ledger for a sample actually drawn
    at 8, because a later `run` call (default --per-region 12) silently
    clobbered the recorded frame. `draw_frame` is the pure decision that must
    now gate every write: write once, refuse to rewrite silently.
    """

    def test_first_draw_on_an_empty_ledger_writes_the_frame(self):
        fields, ok, msg = ms.draw_frame({}, seed=1189, per_region=8, oversample=4)
        self.assertTrue(ok)
        self.assertIsNone(msg)
        self.assertEqual(fields, {"seed": 1189, "per_region": 8, "oversample": 4})

    def test_a_repeat_run_with_the_same_frame_is_a_true_no_op(self):
        existing = {"seed": 1189, "per_region": 8, "oversample": 4, "candidate_sites": {"R1-routing": 65}}
        fields, ok, msg = ms.draw_frame(existing, seed=1189, per_region=8, oversample=4)
        self.assertTrue(ok)
        self.assertIsNone(msg)
        # Nothing to write: not "write the same values again", literally empty.
        self.assertEqual(fields, {})

    def test_the_exact_1189_regression_is_refused_not_silently_applied(self):
        # The precise shape that shipped: a sample drawn at per_region=8,
        # then `run` invoked again with the argparse DEFAULT (12) instead of
        # the recorded value.
        existing = {"seed": 1189, "per_region": 8, "oversample": 4}
        fields, ok, msg = ms.draw_frame(existing, seed=1189, per_region=12, oversample=4)
        self.assertFalse(ok)
        self.assertIsNotNone(msg)
        self.assertIn("8", msg)
        self.assertIn("12", msg)
        # And critically: draw_frame itself never mutates its input.
        self.assertEqual(existing, {"seed": 1189, "per_region": 8, "oversample": 4})

    def test_a_different_seed_is_also_refused(self):
        existing = {"seed": 1189, "per_region": 8, "oversample": 4}
        fields, ok, msg = ms.draw_frame(existing, seed=42, per_region=8, oversample=4)
        self.assertFalse(ok)
        self.assertIn("42", msg)

    def test_candidate_sites_is_not_part_of_the_locked_frame(self):
        # candidate_sites is live tree-state context (drifts as the codebase
        # changes) and is refreshed by the caller every run on purpose; it
        # must not be compared here or a routine `run` on a moved tree would
        # be refused for a reason that has nothing to do with the sample.
        existing = {"seed": 1189, "per_region": 8, "oversample": 4,
                    "candidate_sites": {"R1-routing": 65}}
        fields, ok, msg = ms.draw_frame(existing, seed=1189, per_region=8, oversample=4)
        self.assertTrue(ok)
        self.assertEqual(fields, {})


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], "-v"])
