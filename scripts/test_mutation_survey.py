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


class L2IsCurrent(unittest.TestCase):
    """RQ-66-POTENCY (#1189): `preflight_suite` (used by `run`/`controls`,
    which resume a survey across many invocations against a tree that is not
    expected to move between them) trusts L2's validated-green status
    without re-executing `cargo test --workspace` on every call — but only
    when that trust is not misplaced. `l2_is_current` is the decision,
    driven here with an explicit `current_commit` so it needs no subprocess.
    """

    def test_validated_at_the_current_commit_is_trusted(self):
        ledger = {"suite": {"l2_baseline_seconds": 274.4, "l2_validated_at": "abc12345"}}
        self.assertTrue(ms.l2_is_current(ledger, current_commit="abc12345"))

    def test_a_moved_commit_since_l2_was_validated_is_not_trusted(self):
        # The exact shape `run`/`controls` must catch: baseline validated L2
        # at abc12345, the tree has since moved to def67890 (new commits,
        # possibly a regression) without anyone re-running `baseline`/`l2`.
        ledger = {"suite": {"l2_baseline_seconds": 274.4, "l2_validated_at": "abc12345"}}
        self.assertFalse(ms.l2_is_current(ledger, current_commit="def67890"))

    def test_l2_never_validated_is_not_trusted(self):
        # `baseline --skip-l2` and no `l2` run since: nothing to trust yet.
        ledger = {"suite": {}}
        self.assertFalse(ms.l2_is_current(ledger, current_commit="abc12345"))

    def test_a_pre_fix_ledger_with_no_validated_at_field_is_not_trusted(self):
        # The committed docs/status/mutation_survey.json shape: it has
        # l2_baseline_seconds (L2 WAS run at baseline time) but predates this
        # fix's l2_validated_at field. Must refuse rather than assume trust
        # from a field that was never written for the reason being fixed.
        ledger = {"suite": {"l2_baseline_seconds": 274.4}}
        self.assertFalse(ms.l2_is_current(ledger, current_commit="ad52535a"))


class RetiredLedgerValidation(unittest.TestCase):
    """RQ-76-MUTRETIRE (#1257), added by v0.76 round 1 Pass B (gate potency).

    WHY THIS EXISTS. `validate_retired` shipped with NOTHING executing it. Pass B
    corrupted the real ledger three ways at once and both CI-wired steps stayed
    green — this file (34 tests, zero references to `retired`) and
    `claim_check.py` at 75/75. It then gutted the validator to `return []` and
    `loop_conformance_check.py` still reported "8/8 done-when DECLARED", because
    the lane's done-when was `contains:scripts/mutation_survey.py:RQ-76-MUTRETIRE`
    and all three matches of that literal are COMMENTS. A gate whose subject is a
    comment cannot fail; that is the v0.69 ARCHMODEL class one directory over.

    So the validator is driven from both sides here, and the done-when now points
    at THIS file, where the string lands on executed code.
    """

    def _ledger(self, mutants=None, retired=None):
        return {"mutants": mutants or [{"id": "R1/REG/a.rs:1:1"}],
                "retired": retired or []}

    def test_a_complete_entry_on_a_clean_ledger_validates(self):
        led = self._ledger(retired=[{
            "id": "R2/BOUND/b.rs:9:9", "classification_when_drawn": "EQUIVALENT",
            "retired_at": "v0.76", "reason": "the mutated construct was deleted"}])
        self.assertEqual(ms.validate_retired(led), [])
        self.assertEqual(ms.drawn_counts(led), (2, 1, 1))

    def test_EVERY_required_field_is_reported_when_missing(self):
        """ROUND 2 WIDENED THIS. The first version dropped only `reason`, so all
        seven tests passed on a validator wrong in general: round 2 removed
        `classification_when_drawn`, `retired_at` and `id` from
        `RETIRED_REQUIRED` one at a time and the whole suite stayed green. The
        loop below is derived from the tuple itself, so a field DELETED from
        `RETIRED_REQUIRED` now reds here instead of silently losing coverage.
        """
        complete = {"id": "R2/BOUND/b.rs:9:9",
                    "classification_when_drawn": "EQUIVALENT",
                    "retired_at": "v0.76", "reason": "the construct was deleted"}
        self.assertEqual(sorted(ms.RETIRED_REQUIRED),
                         sorted(complete), "the fixture must cover the tuple exactly")
        for field in ms.RETIRED_REQUIRED:
            with self.subTest(missing=field):
                entry = {k: v for k, v in complete.items() if k != field}
                problems = ms.validate_retired(self._ledger(retired=[entry]))
                self.assertTrue(
                    any("missing" in x and field in x for x in problems),
                    f"dropping {field!r} was not reported: {problems}")

    def test_an_id_both_live_and_retired_is_reported(self):
        # Pass B's second corruption, and the one that corrupts the DENOMINATOR:
        # the same id counted in both columns double-counts the drawn sample.
        led = self._ledger(
            mutants=[{"id": "R2/BOUND/b.rs:9:9"}],
            retired=[{"id": "R2/BOUND/b.rs:9:9",
                      "classification_when_drawn": "EQUIVALENT",
                      "retired_at": "v0.76", "reason": "x"}])
        problems = ms.validate_retired(led)
        self.assertTrue(any("ALSO present in `mutants`" in x for x in problems),
                        problems)

    def test_the_same_id_listed_twice_is_reported(self):
        # Pass B's third corruption.
        e = {"id": "R2/BOUND/b.rs:9:9", "classification_when_drawn": "EQUIVALENT",
             "retired_at": "v0.76", "reason": "x"}
        problems = ms.validate_retired(self._ledger(retired=[dict(e), dict(e)]))
        self.assertTrue(any("listed twice" in x for x in problems), problems)

    def test_all_three_corruptions_at_once_are_each_reported(self):
        # Pass B applied them TOGETHER; one report must not mask the others.
        led = {
            "mutants": [{"id": "R3/REG/c.rs:3:3"}],
            "retired": [
                {"id": "R1/BOUND/a.rs:1:1",
                 "classification_when_drawn": "EQUIVALENT",
                 "retired_at": "v0.76"},                      # missing reason
                {"id": "R2/BOUND/b.rs:2:2",
                 "classification_when_drawn": "EQUIVALENT",
                 "retired_at": "v0.76", "reason": "x"},
                {"id": "R2/BOUND/b.rs:2:2",
                 "classification_when_drawn": "EQUIVALENT",
                 "retired_at": "v0.76", "reason": "x"},        # listed twice
                {"id": "R3/REG/c.rs:3:3",
                 "classification_when_drawn": "EQUIVALENT",
                 "retired_at": "v0.76", "reason": "x"},        # also live
            ]}
        problems = ms.validate_retired(led)
        self.assertTrue(any("missing" in x for x in problems), problems)
        self.assertTrue(any("listed twice" in x for x in problems), problems)
        self.assertTrue(any("ALSO present" in x for x in problems), problems)

    def test_the_REAL_shipped_ledger_validates_clean(self):
        # The control. If this ever reds, the ledger is malformed, not the test.
        led = ms.load_ledger(ROOT / "docs/status/mutation_survey.json")
        self.assertEqual(ms.validate_retired(led), [])
        drawn, live, ret = ms.drawn_counts(led)
        self.assertEqual(drawn, live + ret)

    def test_a_FICTIONAL_but_complete_entry_is_NOT_caught_and_that_is_recorded(self):
        """ACCEPTED LIMITATION, pinned so it is a known gap and not a surprise.

        Pass B's fourth case: an entry that is structurally perfect but refers to
        a site that never existed validates clean and silently RAISES `drawn`.
        `validate_retired` cannot catch it, and the reason is structural rather
        than an oversight: a retired id carries only a BASENAME (`a.rs:1:1`, not
        a path), and a site legitimately retired because a fix DELETED its file
        would have no file to resolve against — so "the file must exist" would
        red on exactly the case this list is for. Establishing that a retired
        site genuinely vanished needs the tree AS OF the retiring release, which
        the ledger does not record.

        This test asserts the CURRENT behaviour deliberately. If a later release
        teaches the validator to resolve retired ids, this test should FAIL and
        be replaced — that failure is the signal, not a regression. Named as a
        v0.77 follow-up rather than left implicit.
        """
        led = self._ledger(retired=[{
            "id": "R9-fictional/NOPE/does_not_exist.rs:1:1",
            "classification_when_drawn": "EQUIVALENT",
            "retired_at": "v99.99", "reason": "because I said so"}])
        self.assertEqual(ms.validate_retired(led), [])
        self.assertEqual(ms.drawn_counts(led), (2, 1, 1))


class ShadowTree(unittest.TestCase):
    """RQ-89-SWEEPMUTANT (#1611): a mutant is applied only to a shadow copy, so
    no kill — of the survey, or of the shell that started it — can leave one
    in the live tree. Driven without cargo: a fixture git repo is the live
    tree, a child python process applies the mutant with the real `Edit`."""

    SITE = {"id": "T/REG/lib.rs:2:0", "file": "crates/x/src/lib.rs", "start": 2, "end": 2,
            "before": "    Reg::R10", "after": "    Reg::R9"}
    LIB = "fn f() {\n    Reg::R10\n}\n"

    def setUp(self):
        import subprocess
        import tempfile
        self._td = tempfile.TemporaryDirectory()
        self.td = Path(self._td.name)
        self.live = self.td / "live"
        (self.live / "crates/x/src").mkdir(parents=True)
        (self.live / "crates/x/src/lib.rs").write_text(self.LIB)
        (self.live / "scripts").mkdir()
        (self.live / "scripts/tool.sh").write_text("#!/bin/sh\n")
        os.chmod(self.live / "scripts/tool.sh", 0o755)
        (self.live / ".gitignore").write_text("target\n*.log\n")
        (self.live / "target/debug").mkdir(parents=True)
        (self.live / "target/debug/synth").write_text("live binary")
        (self.live / "ignored.log").write_text("x")
        env = dict(os.environ, GIT_CONFIG_GLOBAL="/dev/null", GIT_CONFIG_SYSTEM="/dev/null")
        subprocess.run(["git", "init", "-q", str(self.live)], check=True, env=env)
        subprocess.run(["git", "-C", str(self.live), "add", "crates", ".gitignore"], check=True, env=env)
        # scripts/tool.sh stays UNTRACKED: a lane's uncommitted file is surveyed too
        self.src = self.td / "shadow/src"

    def tearDown(self):
        self._td.cleanup()

    def _child(self, body):
        """A python child that imports the real module and runs `body`."""
        script = self.td / "child.py"
        script.write_text(
            "import importlib.util, os, sys, time\n"
            f"spec = importlib.util.spec_from_file_location('ms', {str(ROOT / 'scripts/mutation_survey.py')!r})\n"
            "ms = importlib.util.module_from_spec(spec); spec.loader.exec_module(ms)\n"
            f"SITE = {self.SITE!r}\n"
            f"open({str(self.td / 'pid')!r}, 'w').write(str(os.getpid()))\n" + body)
        return script

    def _wait_for(self, pred, timeout=20.0):
        import time
        t0 = time.time()
        while time.time() - t0 < timeout:
            if pred():
                return True
            time.sleep(0.1)
        return False

    @staticmethod
    def _alive(pid):
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return False
        # a zombie still answers kill(0); ask ps for its state
        import subprocess
        st = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True).stdout.strip()
        return bool(st) and not st.startswith("Z")

    def test_sync_copies_the_tree_but_never_target_or_git(self):
        rewritten, removed = ms.sync_shadow(self.live, self.src)
        self.assertEqual((self.src / "crates/x/src/lib.rs").read_text(), self.LIB)
        self.assertTrue((self.src / "scripts/tool.sh").is_file(), "an untracked file is surveyed too")
        self.assertEqual((self.src / "scripts/tool.sh").stat().st_mode & 0o777, 0o755)
        self.assertFalse((self.src / "target").exists())
        self.assertFalse((self.src / ".git").exists())
        self.assertFalse((self.src / "ignored.log").exists())
        self.assertTrue((self.src / ms.SHADOW_MARKER).is_file())
        self.assertEqual((rewritten, removed), (3, 0))
        self.assertEqual(ms.sync_shadow(self.live, self.src), (0, 0), "an unchanged tree rewrites nothing")

    def test_sync_rewrites_a_left_mutant_with_a_fresh_mtime(self):
        ms.sync_shadow(self.live, self.src)
        lib = self.src / "crates/x/src/lib.rs"
        lib.write_text(self.LIB.replace("R10", "R9"))  # what a kill leaves in the shadow
        os.utime(lib, (1, 1))
        (self.src / "stray.txt").write_text("a step's transcript")
        self.assertEqual(ms.sync_shadow(self.live, self.src), (1, 1))
        self.assertEqual(lib.read_text(), self.LIB)
        # cargo decides freshness by mtime; a restored file older than the
        # mutant build would let it reuse the MUTANT binary
        self.assertGreater(lib.stat().st_mtime, 1e9)
        self.assertFalse((self.src / "stray.txt").exists())

    def test_edit_refuses_a_live_tree(self):
        with self.assertRaises(RuntimeError) as cm:
            with ms.Edit(self.SITE, "after", root=self.live):
                pass
        self.assertIn("REFUSING", str(cm.exception))
        self.assertEqual((self.live / "crates/x/src/lib.rs").read_text(), self.LIB)

    def test_edit_applies_and_restores_in_a_shadow(self):
        ms.sync_shadow(self.live, self.src)
        with ms.Edit(self.SITE, "after", root=self.src) as ed:
            self.assertIn("Reg::R9", (self.src / "crates/x/src/lib.rs").read_text())
            self.assertFalse(ed.restored())
        self.assertTrue(ed.restored())

    def test_sigkill_mid_mutant_leaves_the_live_tree_untouched(self):
        import signal
        import subprocess
        ms.sync_shadow(self.live, self.src)
        ready = self.td / "ready"
        child = self._child(
            f"with ms.Edit(SITE, 'after', root={str(self.src)!r}):\n"
            f"    open({str(ready)!r}, 'w').write('1')\n"
            "    time.sleep(120)\n")
        p = subprocess.Popen([sys.executable, str(child)])
        try:
            self.assertTrue(self._wait_for(ready.exists), "child never applied its mutant")
            self.assertIn("Reg::R9", (self.src / "crates/x/src/lib.rs").read_text())
            p.send_signal(signal.SIGKILL)  # no handler can run
            p.wait(10)
        finally:
            if p.poll() is None:
                p.kill()
        self.assertEqual((self.live / "crates/x/src/lib.rs").read_text(), self.LIB,
                         "the LIVE tree must never have held the mutant")
        self.assertIn("Reg::R9", (self.src / "crates/x/src/lib.rs").read_text(),
                      "SIGKILL leaves the mutant in the SHADOW (control: the kill was real)")
        self.assertEqual(ms.sync_shadow(self.live, self.src), (1, 0))
        self.assertEqual((self.src / "crates/x/src/lib.rs").read_text(), self.LIB)

    def test_a_dead_parent_stops_the_survey_and_unwinds_its_edit(self):
        """The sweep-timeout shape: SIGKILL lands on the WRAPPER shell, python
        is reparented. The watchdog must notice and unwind (restoring the
        shadow file) instead of running on as an orphan."""
        import signal
        import subprocess
        ms.sync_shadow(self.live, self.src)
        ready = self.td / "ready"
        child = self._child(
            "ms.install_lifecycle_guards(interval=0.2)\n"
            f"with ms.Edit(SITE, 'after', root={str(self.src)!r}):\n"
            f"    open({str(ready)!r}, 'w').write('1')\n"
            "    time.sleep(120)\n")
        # `| cat` forces bash to FORK python rather than exec it — the
        # `python3 scripts/mutation_survey.py ci | tee` shape of ci.yml
        w = subprocess.Popen(["bash", "-c", f"{sys.executable} {child} | cat"])
        pid = None
        try:
            self.assertTrue(self._wait_for(ready.exists), "child never applied its mutant")
            pid = int((self.td / "pid").read_text())
            self.assertNotEqual(pid, w.pid)
            w.send_signal(signal.SIGKILL)  # what subprocess.run(timeout=) does
            w.wait(10)
            self.assertTrue(self._wait_for(lambda: not self._alive(pid), timeout=15),
                            "the survey kept running after its parent died")
        finally:
            if pid and self._alive(pid):
                os.kill(pid, signal.SIGKILL)
        self.assertEqual((self.src / "crates/x/src/lib.rs").read_text(), self.LIB,
                         "the watchdog's SIGTERM must unwind the Edit")

    def test_main_routes_every_building_command_through_the_shadow(self):
        self.assertEqual(set(ms.SHADOWED_CMDS), {"baseline", "l2", "run", "controls", "ci", "reach"})


class MutantResidueCheck(unittest.TestCase):
    """RQ-89-SWEEPMUTANT (#1611): the commit-side guard."""

    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location("mrc", ROOT / "scripts/mutant_residue_check.py")
        cls.mrc = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.mrc)

    def test_whole_line_match_only(self):
        f = self.mrc.find_block
        self.assertEqual(f("a\n    if x >= 0 {\nb", "    if x >= 0 {"), [2])
        self.assertEqual(f("a\n    if x >= 0 {y\nb", "    if x >= 0 {"), [])
        self.assertEqual(f("a\nb\nc\nb\nc", "b\nc"), [2, 4])

    def test_catalogue_covers_mutants_and_controls_not_retired(self):
        led = {"mutants": [{"id": "m", "file": "a.rs", "after": "x"}],
               "controls": [{"id": "c", "file": "b.rs", "after": "y"}],
               "retired": [{"id": "r"}]}
        self.assertEqual([i for i, _, _ in self.mrc.catalogue(led)], ["m", "c"])

    def test_plants_are_chosen_by_structure_not_by_id(self):
        # #1602 re-anchored arm_backend.rs:1805:36 to :1807:36 and the
        # id-naming self-test raised KeyError in a REQUIRED job; renaming every
        # id must not change which sites are planted
        import json
        led = json.loads((ROOT / "docs/status/mutation_survey.json").read_text())
        plants, problems = self.mrc.select_plants(led, ROOT)
        self.assertEqual(problems, [])
        self.assertGreaterEqual(len(plants), 2)
        for i, m in enumerate(led["mutants"] + led["controls"]):
            m["id"] = ("CONTROL/" if m in led["controls"] else "") + f"renamed-{i:03d}"
        again, _ = self.mrc.select_plants(led, ROOT)
        self.assertEqual([(p["file"], p["before"]) for p in again],
                         [(p["file"], p["before"]) for p in plants])

    def test_an_unusable_catalogue_is_a_plain_rc2_not_a_traceback(self):
        plants, problems = self.mrc.select_plants({"mutants": [], "controls": []}, ROOT)
        self.assertEqual(plants, [])
        self.assertEqual(len(problems), 2)
        stale = {"mutants": [{"id": "x", "op": "REG", "file": "crates/nope.rs", "before": "a", "after": "b"}],
                 "controls": [{"id": "CONTROL/y", "file": "Cargo.toml", "before": "no such line", "after": "z"}]}
        self.assertEqual(len(self.mrc.select_plants(stale, ROOT)[1]), 2)

    def test_red_first_and_clean(self):
        import contextlib
        import io
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(self.mrc.self_test(), 0)


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], "-v"])
