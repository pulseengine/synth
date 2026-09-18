#!/usr/bin/env python3
"""Unit tests for scripts/release_notes_from_rivet.py (RQ-70-RIVETNOTES, #1337).

The load-bearing test is `test_pin_is_not_below_ci`: the generator's own
`PINNED_RIVET` is RE-DERIVED from ci.yml rather than trusted, so the two cannot
drift apart. That drift is the whole failure this lane exists to prevent — a
generator that accepts a rivet CI considers stale would emit a confidently clean
answer from a tool that never resolved the graph (rivet 0.32 reports "0 broken
cross-refs" where 0.37 reports "cross-refs NOT CHECKED").
"""

from __future__ import annotations

import importlib.util
import re
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("rnfr", ROOT / "scripts" / "release_notes_from_rivet.py")
rnfr = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(rnfr)


class Pin(unittest.TestCase):
    def test_pin_is_not_below_ci(self):
        """The generator must never accept a rivet older than the one CI installs.

        DERIVED from ci.yml, not restated: a hand-copied version is exactly the
        second-source-of-truth this repo keeps finding rotted behind a green gate.
        """
        ci = (ROOT / ".github" / "workflows" / "ci.yml").read_text()
        pins = re.findall(r"Install rivet \(pinned v(\d+)\.(\d+)\.(\d+)\)", ci)
        self.assertTrue(pins, "no `Install rivet (pinned vX.Y.Z)` step found in ci.yml")
        for p in pins:
            ci_ver = tuple(int(x) for x in p)
            self.assertGreaterEqual(
                rnfr.PINNED_RIVET,
                ci_ver,
                f"PINNED_RIVET {rnfr.PINNED_RIVET} is BELOW ci.yml's {ci_ver} — the "
                f"generator would accept a rivet CI considers stale, which is how a "
                f"never-resolved graph reads as clean",
            )

    def test_version_regex_reads_the_real_format(self):
        """rivet prints `rivet 0.37.0 (sha branch date)`; the parser must take the semver."""
        m = rnfr.VERSION_RE.match("rivet 0.37.0 (6f9ef82c master 2026-09-18) [1 untracked]")
        self.assertIsNotNone(m)
        self.assertEqual(tuple(int(g) for g in m.groups()), (0, 37, 0))

    def test_version_regex_rejects_a_non_version(self):
        self.assertIsNone(rnfr.VERSION_RE.match("command not found"))


class Sources(unittest.TestCase):
    def test_source_roots_are_read_from_rivet_yaml(self):
        """The extract is bounded by rivet.yaml, so a source moving is a loud
        extract failure rather than a silently narrower diff."""
        roots = rnfr.source_roots(ROOT)
        self.assertIn("artifacts", roots)
        self.assertGreaterEqual(len(roots), 2, "rivet.yaml declares more than one source")

    def test_source_roots_refuses_a_config_with_no_sources(self):
        with tempfile.TemporaryDirectory() as td:
            (Path(td) / "rivet.yaml").write_text("docs:\n  - docs\n")
            with self.assertRaises(SystemExit):
                rnfr.source_roots(Path(td))


class Parsing(unittest.TestCase):
    def test_diagnostic_line_is_parsed(self):
        m = rnfr.DIAG_RE.match("0 new errors, 0 resolved errors, 21 new warnings, 0 resolved warnings")
        self.assertIsNotNone(m)
        self.assertEqual([int(g) for g in m.groups()], [0, 0, 21, 0])

    def test_diagnostic_line_singular_forms(self):
        """rivet singularizes at 1; a parser that only knows the plural silently
        reports 'no diagnostic summary' on exactly the release that has one."""
        m = rnfr.DIAG_RE.match("1 new error, 0 resolved errors, 1 new warning, 0 resolved warnings")
        self.assertIsNotNone(m)
        self.assertEqual([int(g) for g in m.groups()], [1, 0, 1, 0])

    def test_added_line_yields_id_and_title(self):
        m = rnfr.ADDED_RE.match("+ RQ-70-NPA  `--native-pointer-abi` cannot lower static-data f32")
        self.assertIsNotNone(m)
        self.assertEqual(m.group(1), "RQ-70-NPA")
        self.assertTrue(m.group(2).startswith("`--native-pointer-abi`"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
