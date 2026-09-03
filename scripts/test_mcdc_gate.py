#!/usr/bin/env python3
"""Unit tests for mcdc_gate.py's BRANCH_POPULATION check (witness#208 / #990).

WHY THIS FILE EXISTS. The #990 lane's own verdict was that the MC/DC red it
diagnosed lived in a CHECKER (witness's layout-sensitive decision
reconstruction) — the sixth release running in which the defect was in
checking machinery. BRANCH_POPULATION is a NEW checker introduced by that
finding, and the repo's standing rule (stated in claims.yaml for the
RQ-58-METRIC ratchet, enforced by scripts/test_claim_check.py) is that a new
checker ships WITH a committed potency test, not a demonstration someone ran
once in a PR. So every branch of the population check is driven here — the
reds each NAMING the function, the guard text that stands between the REPIN
block and someone pasting it to go green, and the greens, because a gate that
only ever fails is as useless as one that only ever passes.

The fixtures are SYNTHETIC (a manifest + report pair built in a temp dir);
witness itself never runs. The report side is generated consistently from the
same population map so its floors hold in every case — a mutated population is
therefore the ONLY thing that can red the gate, which is what makes each
test's failure attribution clean.

Stdlib `unittest` only.

    python3 scripts/test_mcdc_gate.py       (wired in the mcdc CI job)
"""

import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

import mcdc_gate  # noqa: E402
from mcdc_gate import (  # noqa: E402
    BRANCH_POPULATION,
    SCORED_PREFIXES,
    check_restatement_ledger,
)

GATE = SCRIPTS / "mcdc_gate.py"

# The guard sentence standing between the printed REPIN block and someone
# pasting it to go green — the population check's analogue of "do not lower a
# floor to go green". Asserted verbatim below so a refactor cannot silently
# drop it.
REPIN_GUARD = "witness#208, not a repin"

# Same rule for the drift path's RE-STATEMENT block (#1100): the paste-able
# ledger entry must arrive WITH the sentence that scopes when pasting it is
# legitimate.
RESTATE_GUARD = "explained loss is a real regression, not drift"

# And the ledger consistency check's own guard — also the claims.yaml
# SYNTH-MCDC-FLOOR-RESTATEMENT text anchor.
LEDGER_GUARD = "movement and evidence travel in the"


def write_fixture(
    run_dir: pathlib.Path,
    population: dict[str, int],
    gap: dict[str, int] | None = None,
) -> None:
    """Build a consistent (manifest, report) pair from a population map.

    Every function's branches are chunked into 2-condition decisions with all
    conditions `proved`, so with the real pins the report side clears every
    floor (176 conditions, ~90 fully-proved decisions, 0 dead) and only the
    population check can fail. `gap` demotes that many of a function's
    conditions to `gap` WITHOUT touching the manifest — the report-side-only
    perturbation of the #1100 drift class.
    """
    gap = dict(gap or {})
    branches = []
    next_id = 0
    per_fn_ids: dict[str, list[int]] = {}
    for fn, n in sorted(population.items()):
        ids = []
        for _ in range(n):
            branches.append({"id": next_id, "function_name": fn})
            ids.append(next_id)
            next_id += 1
        per_fn_ids[fn] = ids

    decisions = []
    for fn, ids in per_fn_ids.items():
        to_gap = gap.get(fn, 0)
        for k in range(0, len(ids), 2):
            chunk = ids[k : k + 2]
            conds = []
            for i, b in enumerate(chunk):
                status = "proved"
                if to_gap > 0:
                    status = "gap"
                    to_gap -= 1
                conds.append(
                    {
                        "index": i,
                        "branch_id": b,
                        "status": status,
                        "gap_closure": {},
                    }
                )
            decisions.append(
                {
                    "id": len(decisions),
                    "source_file": "synthetic.rs",
                    "source_line": 1,
                    "conditions": conds,
                }
            )

    (run_dir / "instrumented.wasm.witness.json").write_text(
        json.dumps({"attribution_source": "synthetic", "branches": branches})
    )
    (run_dir / "report.json").write_text(
        json.dumps(
            {
                "schema": "https://pulseengine.eu/witness-mcdc/v3",
                "witness_version": "synthetic",
                "decisions": decisions,
            }
        )
    )


def run_gate(
    population: dict[str, int], gap: dict[str, int] | None = None
) -> tuple[int, str]:
    with tempfile.TemporaryDirectory() as td:
        run_dir = pathlib.Path(td)
        write_fixture(run_dir, population, gap=gap)
        r = subprocess.run(
            [sys.executable, str(GATE), str(run_dir)],
            capture_output=True,
            text=True,
        )
        return r.returncode, r.stdout + r.stderr


# Enough report-side-only demotion to miss FLOOR_PROVED while every other
# floor still holds (176 total conditions; 122 gapped leaves 54 proved < 56,
# conditions 176 >= 130, dead 0 <= 50, decisions and full untouched enough).
DRIFT_GAP = {
    "synth_backend_riscv::alloc_validator::is_straight_line": 52,
    "synth_backend_riscv::alloc_validator::validate_final_allocation_rv32": 47,
    "synth_core::static_data_addr::validate_reloc_resolutions_spanned": 13,
    "synth_backend_riscv::backend::compile_function_with_opts": 10,
}


class PopulationGreen(unittest.TestCase):
    """The gate must be able to PASS — otherwise it is noise and gets disabled."""

    def test_exact_pins_pass(self):
        rc, out = run_gate(dict(BRANCH_POPULATION))
        self.assertEqual(rc, 0, out)
        self.assertIn("PASS: all MC/DC floors met", out)
        self.assertNotIn("BRANCH POPULATION", out)

    def test_unscored_function_noise_is_ignored(self):
        # witness#208 is ABOUT unrelated code moving the numbers; branches in
        # functions outside SCORED_PREFIXES must not trip the population
        # check, or every dep bump reds the gate for the wrong reason.
        pop = dict(BRANCH_POPULATION)
        pop["core::fmt::Formatter::pad_integral"] = 7
        rc, out = run_gate(pop)
        self.assertEqual(rc, 0, out)
        self.assertNotIn("BRANCH POPULATION", out)


class PopulationRed(unittest.TestCase):
    """Each mismatch reds the gate AND names the function — presence of a
    check is not potency (#910); these are the negative controls, committed."""

    def test_dropped_branch_reds_naming_the_function(self):
        # THE deletion case — the reason the check exists: a condition deleted
        # from a gated predicate drops its function's instrument-side count.
        pop = dict(BRANCH_POPULATION)
        fn = "synth_core::static_data_addr::validate_served_image"
        pop[fn] -= 1
        rc, out = run_gate(pop)
        self.assertEqual(rc, 1, out)
        self.assertIn(f"branch population moved: {fn} = 4 (pinned 5)", out)
        self.assertIn(f"FAIL: branch population moved: {fn}", out)

    def test_grown_branch_reds_naming_the_function(self):
        # An ADDED condition is also a diff someone must look at (it needs
        # rows) — EXACT pins, not floors, in claims.yaml's value-must-EQUAL
        # spirit.
        pop = dict(BRANCH_POPULATION)
        fn = "synth_core::wasm_op::count_params_heuristic"
        pop[fn] += 1
        rc, out = run_gate(pop)
        self.assertEqual(rc, 1, out)
        self.assertIn(f"branch population moved: {fn} = 6 (pinned 5)", out)

    def test_unpinned_scored_function_reds(self):
        # A new function under a scored prefix has conditions nobody pinned or
        # wrote rows for — it must be surfaced, not silently half-scored.
        pop = dict(BRANCH_POPULATION)
        fn = "synth_core::static_data_addr::brand_new_check"
        self.assertTrue(fn.startswith(SCORED_PREFIXES))  # fixture sanity
        pop[fn] = 3
        rc, out = run_gate(pop)
        self.assertEqual(rc, 1, out)
        self.assertIn(f"UNPINNED scored function in manifest: {fn} (3 branches)", out)

    def test_mismatch_emits_repin_block_with_guard_text(self):
        # The REPIN block must arrive WITH its guard sentence. Without it the
        # block is a paste-to-green affordance — exactly what "do not lower a
        # floor to go green" exists to prevent on the floors.
        pop = dict(BRANCH_POPULATION)
        pop["synth_backend_riscv::alloc_validator::is_ret"] -= 1
        rc, out = run_gate(pop)
        self.assertEqual(rc, 1, out)
        self.assertIn("REPIN block", out)
        self.assertIn(REPIN_GUARD, out)
        # The block itself must be paste-able over BRANCH_POPULATION: it lists
        # the MEASURED population in the pin table's own syntax.
        self.assertIn('    "synth_backend_riscv::alloc_validator::is_ret": 3,', out)


class FailureModeClassification(unittest.TestCase):
    """#1100 / RQ-61-MCDCFLOOR: the two failure modes must be DISTINGUISHED in
    output and exit code, and neither may read as the other. A classifier
    nobody has seen fire on both branches is not a classifier — these are the
    committed negative controls for both branches."""

    def test_population_mismatch_is_the_real_alarm_exit_1(self):
        # MODE 1: an instrument-side branch disappears -> exit 1, the
        # branch-deletion headline, and NO re-statement offered.
        pop = dict(BRANCH_POPULATION)
        pop["synth_core::static_data_addr::validate_served_image"] -= 1
        rc, out = run_gate(pop)
        self.assertEqual(rc, 1, out)
        self.assertIn("FAIL[branch-population]", out)
        self.assertIn("THE REAL ALARM", out)
        self.assertNotIn("FAIL[reconstruction-drift]", out)
        self.assertNotIn("RE-STATEMENT block", out)

    def test_report_side_only_drift_is_exit_2_and_not_the_alarm(self):
        # MODE 2: the manifest matches every pin EXACTLY; only the report's
        # proved count drops (the #1096 shape) -> exit 2, the drift headline,
        # per-function attribution, the auditable RE-STATEMENT block — and
        # NOT the branch-deletion alarm.
        rc, out = run_gate(dict(BRANCH_POPULATION), gap=DRIFT_GAP)
        self.assertEqual(rc, 2, out)
        self.assertIn("FAIL[reconstruction-drift]", out)
        self.assertIn("matched EVERY pin exactly", out)
        self.assertNotIn("FAIL[branch-population]", out)
        self.assertNotIn("THE REAL ALARM", out)
        # attribution: the drifted function is NAMED, with its unmoved
        # instrument population beside it, so the re-statement is mechanical
        self.assertIn(
            "synth_backend_riscv::alloc_validator::is_straight_line", out
        )
        self.assertIn("[instrument population pinned-equal: 52]", out)
        # the paste-able ledger entry arrives WITH its guard sentence and
        # WITH the population evidence pre-filled
        self.assertIn("RE-STATEMENT block", out)
        self.assertIn(RESTATE_GUARD, out)
        self.assertIn("BRANCH_POPULATION exact-match on this run", out)

    def test_population_mismatch_dominates_mixed_failure(self):
        # BOTH at once: the population alarm must win (exit 1) and the gate
        # must NOT offer a re-statement — with the population moved, the
        # floor miss may be a real coverage loss.
        pop = dict(BRANCH_POPULATION)
        pop["synth_backend_riscv::alloc_validator::is_ret"] -= 1
        rc, out = run_gate(pop, gap=DRIFT_GAP)
        self.assertEqual(rc, 1, out)
        self.assertIn("FAIL[branch-population]", out)
        self.assertIn("FAIL (secondary, may be a consequence)", out)
        self.assertNotIn("FAIL[reconstruction-drift]", out)
        self.assertNotIn("RE-STATEMENT block", out)

    def test_green_shape_drift_is_advisory_not_red(self):
        # Floors met + populations pinned-equal + report shape differing from
        # the REPORT_SHAPE baseline (this synthetic shape always does) must
        # stay GREEN with an advisory note — failing here would red every
        # unrelated-code PR, the exact recurrence #1100 documents.
        rc, out = run_gate(dict(BRANCH_POPULATION))
        self.assertEqual(rc, 0, out)
        self.assertIn("PASS: all MC/DC floors met", out)
        self.assertIn("note: report-shape drift", out)
        self.assertIn("ADVISORY", out)


class RestatementLedger(unittest.TestCase):
    """The floors cannot move without an evidence-carrying RESTATEMENTS
    append — enforced, not folklore. Checked at the function level AND
    through the wired gate (a check that exists but is never called is the
    #910 class)."""

    def _restore(self, **attrs):
        saved = {k: getattr(mcdc_gate, k) for k in attrs}
        for k, v in attrs.items():
            setattr(mcdc_gate, k, v)
        self.addCleanup(lambda: [setattr(mcdc_gate, k, v) for k, v in saved.items()])

    def test_shipped_ledger_is_consistent(self):
        self.assertEqual(check_restatement_ledger(), [])

    def test_floor_moved_without_append_is_caught(self):
        self._restore(FLOOR_PROVED=mcdc_gate.FLOOR_PROVED - 1)
        problems = check_restatement_ledger()
        self.assertTrue(problems, "a moved floor with no ledger append passed")
        self.assertTrue(any(LEDGER_GUARD in p for p in problems), problems)

    def test_loosening_append_requires_drift_decomposition(self):
        entry = dict(mcdc_gate.RESTATEMENTS[-1])
        entry = {
            **entry,
            "floors": {**entry["floors"], "proved": entry["floors"]["proved"] - 1},
            "drift": "",
        }
        self._restore(
            RESTATEMENTS=mcdc_gate.RESTATEMENTS + (entry,),
            FLOOR_PROVED=entry["floors"]["proved"],
        )
        problems = check_restatement_ledger()
        self.assertTrue(
            any("drift" in p and "decomposition" in p for p in problems), problems
        )

    def test_empty_population_evidence_is_caught(self):
        entry = {**mcdc_gate.RESTATEMENTS[-1], "population_evidence": "  "}
        self._restore(RESTATEMENTS=mcdc_gate.RESTATEMENTS[:-1] + (entry,))
        problems = check_restatement_ledger()
        self.assertTrue(
            any("population_evidence" in p for p in problems), problems
        )

    def test_gate_refuses_to_run_on_inconsistent_ledger(self):
        # WIRING potency: run a COPY of the gate whose FLOOR_PROVED was
        # edited without a ledger append. It must exit 1 with the
        # restatement-ledger failure BEFORE scoring anything — the run dir is
        # deliberately empty, so reaching load() would crash differently.
        src = GATE.read_text()
        needle = f"FLOOR_PROVED = {mcdc_gate.FLOOR_PROVED}\n"
        self.assertIn(needle, src)  # count the needle before mutating (#v056)
        mutated = src.replace(needle, f"FLOOR_PROVED = {mcdc_gate.FLOOR_PROVED - 1}\n")
        self.assertNotEqual(mutated, src)
        with tempfile.TemporaryDirectory() as td:
            gate_copy = pathlib.Path(td) / "mcdc_gate.py"
            gate_copy.write_text(mutated)
            empty = pathlib.Path(td) / "empty"
            empty.mkdir()
            r = subprocess.run(
                [sys.executable, str(gate_copy), str(empty)],
                capture_output=True,
                text=True,
            )
        out = r.stdout + r.stderr
        self.assertEqual(r.returncode, 1, out)
        self.assertIn("FAIL[restatement-ledger]", out)
        self.assertIn(LEDGER_GUARD, out)


if __name__ == "__main__":
    unittest.main(verbosity=2)
