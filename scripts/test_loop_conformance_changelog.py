#!/usr/bin/env python3
"""Potency tests for the RQ-67-NOTESGATE (#1259) changelog-structure slot.

A NEW checker ships with its own committed potency tests — the same rule
scripts/test_claim_check.py and scripts/test_mcdc_gate.py already follow. A
gate that cannot be shown to FAIL is indistinguishable from no gate, and this
one exists precisely because the release notes had no gate at all.

THE RED-FIRST HERE IS FREE, WHICH IS WHY IT IS WORTH HAVING. Two commits that
already exist in this repository straddle the defect:

    0cfcc160  the v0.66 tag CANDIDATE — `## [Unreleased]` on top of 115 lines,
              because the release PR APPENDED `## [0.66.0]` below the existing
              heading instead of RENAMING it. Two of that release's own
              artifacts stayed filed as unreleased, and the defect survived the
              release PR, a clean-room review that edited INSIDE that very
              block, and 67 green CI checks.
    2e1a8287  the v0.66 TAG — `## [0.66.0]` on top, no [Unreleased] heading.

No fixture had to be invented. When git history is unavailable the two
history-backed tests SKIP rather than pass vacuously — a checker that reports
success about work it never did is the #1012/#1064 class.
"""

from __future__ import annotations

import subprocess
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from loop_conformance_check import (  # noqa: E402
    DERIVED_FAIL,
    DERIVED_PASS,
    changelog_structure_verdict,
)

ROOT = Path(__file__).resolve().parent.parent


def at(ref: str) -> str | None:
    r = subprocess.run(
        ["git", "-C", str(ROOT), "show", f"{ref}:CHANGELOG.md"],
        capture_output=True,
        text=True,
    )
    return r.stdout if r.returncode == 0 else None


class RealCommits(unittest.TestCase):
    def test_v066_tag_candidate_is_red(self):
        text = at("0cfcc160")
        if text is None:
            self.skipTest("0cfcc160 not present (shallow clone) — not a pass")
        status, detail = changelog_structure_verdict(text, "0.66.0")
        self.assertEqual(status, DERIVED_FAIL, detail)
        self.assertIn("Unreleased", detail)
        self.assertIn("#1259", detail)

    def test_v066_tag_is_green(self):
        text = at("2e1a8287")
        if text is None:
            self.skipTest("2e1a8287 not present (shallow clone) — not a pass")
        status, detail = changelog_structure_verdict(text, "0.66.0")
        self.assertEqual(status, DERIVED_PASS, detail)
        self.assertIn("[0.66.0]", detail)


class Synthetic(unittest.TestCase):
    """The shapes the two real commits do not cover."""

    def test_empty_unreleased_heading_is_not_itself_the_defect(self):
        # An empty leftover heading files nothing as unreleased. It still
        # fails, but via the TOPMOST rule and with that reason — the
        # distinction matters because the fix differs.
        text = "# Changelog\n\n## [Unreleased]\n\n## [0.67.0] - 2026-09-16\n\n- a\n"
        status, detail = changelog_structure_verdict(text, "0.67.0")
        self.assertEqual(status, DERIVED_FAIL, detail)
        self.assertIn("topmost", detail)

    def test_wrong_release_on_top_is_red(self):
        text = "# Changelog\n\n## [0.66.0] - 2026-09-10\n\n- old\n"
        status, detail = changelog_structure_verdict(text, "0.67.0")
        self.assertEqual(status, DERIVED_FAIL, detail)
        self.assertIn("do not describe this release", detail)

    def test_correct_top_section_is_green(self):
        text = "# Changelog\n\n## [0.67.0] - 2026-09-16\n\n- a\n\n## [0.66.0] - 2026-09-10\n\n- b\n"
        status, detail = changelog_structure_verdict(text, "0.67.0")
        self.assertEqual(status, DERIVED_PASS, detail)

    def test_missing_file_is_red_not_silently_green(self):
        status, detail = changelog_structure_verdict(None, "0.67.0")
        self.assertEqual(status, DERIVED_FAIL, detail)

    def test_no_headings_is_red_not_silently_green(self):
        status, detail = changelog_structure_verdict("# Changelog\n\nprose only\n", "0.67.0")
        self.assertEqual(status, DERIVED_FAIL, detail)


if __name__ == "__main__":
    unittest.main(verbosity=2)
