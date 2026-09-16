#!/usr/bin/env python3
"""Potency tests for scripts/determinism_check.py (#1291).

A determinism gate that has only ever passed is indistinguishable from one
that cannot fail. So: the same binary on both sides must PASS, and the same
binary with one byte-changing lever planted on the second side must FAIL.
SYNTH_RANGE_REALLOC=0 is used because the v0.68 lever census measured it moving
84 outputs on a 60-module sample — the largest effect of the 14 found.
"""
import pathlib
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
SYNTH = ROOT / "target" / "debug" / "synth"
CHECK = ROOT / "scripts" / "determinism_check.py"


@unittest.skipUnless(SYNTH.exists(), "needs ./target/debug/synth — build synth-cli first (skip is not a pass)")
class DeterminismGatePotency(unittest.TestCase):
    def run_check(self, *extra):
        return subprocess.run([sys.executable, str(CHECK), str(SYNTH), str(SYNTH), *extra],
                              capture_output=True, text=True, timeout=1800)

    def test_identical_builds_pass(self):
        r = self.run_check()
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("PASS", r.stdout)

    def test_a_planted_lever_is_caught(self):
        r = self.run_check("--plant", "SYNTH_RANGE_REALLOC=0")
        self.assertEqual(r.returncode, 1, "the gate did not notice a planted byte-changing lever:\n" + r.stdout)
        self.assertIn("OBJECT bytes differ", r.stdout)

    def test_comparing_nothing_is_a_failure(self):
        r = self.run_check("--min-pairs", "1000000")
        self.assertEqual(r.returncode, 1, r.stdout)


if __name__ == "__main__":
    unittest.main(verbosity=2)
