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

from mcdc_gate import BRANCH_POPULATION, SCORED_PREFIXES  # noqa: E402

GATE = SCRIPTS / "mcdc_gate.py"

# The guard sentence standing between the printed REPIN block and someone
# pasting it to go green — the population check's analogue of "do not lower a
# floor to go green". Asserted verbatim below so a refactor cannot silently
# drop it.
REPIN_GUARD = "witness#208, not a repin"


def write_fixture(run_dir: pathlib.Path, population: dict[str, int]) -> None:
    """Build a consistent (manifest, report) pair from a population map.

    Every function's branches are chunked into 2-condition decisions with all
    conditions `proved`, so with the real pins the report side clears every
    floor (175 conditions, ~90 fully-proved decisions, 0 dead) and only the
    population check can fail.
    """
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
        for k in range(0, len(ids), 2):
            chunk = ids[k : k + 2]
            decisions.append(
                {
                    "id": len(decisions),
                    "source_file": "synthetic.rs",
                    "source_line": 1,
                    "conditions": [
                        {"index": i, "branch_id": b, "status": "proved"}
                        for i, b in enumerate(chunk)
                    ],
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


def run_gate(population: dict[str, int]) -> tuple[int, str]:
    with tempfile.TemporaryDirectory() as td:
        run_dir = pathlib.Path(td)
        write_fixture(run_dir, population)
        r = subprocess.run(
            [sys.executable, str(GATE), str(run_dir)],
            capture_output=True,
            text=True,
        )
        return r.returncode, r.stdout + r.stderr


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


if __name__ == "__main__":
    unittest.main(verbosity=2)
