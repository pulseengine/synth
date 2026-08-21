#!/usr/bin/env python3
"""Unit tests for dependabot_minor_hold.py — the 0.x-minor hold classifier (#965).

WHY THIS FILE EXISTS. A new checker is a new defect surface (five consecutive
releases found the defect in checking machinery, not the checked code), and
this classifier is what stands between a breaking "semver-minor" bump and an
unattended squash-merge onto main. The precedent is test_claim_check.py and
test_mcdc_gate.py: every decision arm is driven here — the HOLDs (0.x-minor,
0.0.x, major, prerelease, downgrade, no-change, unparseable, grouped) AND the
ALLOWs (0.x patch, >=1.0 minor/patch), because a gate that blocks everything
is as useless as one that blocks nothing.

Two arms carry named incident provenance:
  * 0.39.1 -> 0.40.0 is the `object` bump (#938): semver called it minor,
    it broke 16 call sites across three unrelated newtype surfaces.
  * 0.9.1 -> 0.12.0 is the ordeal bump: auto-merged as "minor", hung Test+Z3
    for 4-6 hours across days.
  * "" -> anything is the fetch-metadata empty-previous-version hole from
    #965: the old shell `case "" in 0.*)` failed OPEN; this classifier must
    fail CLOSED.

Stdlib `unittest` only.

    python3 scripts/test_dependabot_minor_hold.py    (wired in the Claim Check CI job)
"""

import json
import pathlib
import subprocess
import sys
import unittest

SCRIPTS = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

from dependabot_minor_hold import classify, classify_all, parse_version  # noqa: E402

SCRIPT = SCRIPTS / "dependabot_minor_hold.py"

# (prev, new, expected_decision, expected_class, note)
TABLE = [
    # --- the incident specimens: 0.x minor is the de-facto major -> HOLD ---
    ("0.39.1", "0.40.0", "hold", "zerox-minor", "#938 `object`: 16 broken call sites"),
    ("0.39", "0.40", "hold", "zerox-minor", "two-component cargo req form"),
    ("0.9.1", "0.12.0", "hold", "zerox-minor", "ordeal: hung Test+Z3 for days"),
    ("0.9", "0.16", "hold", "zerox-minor", "#864 shape: landed with no CI run"),
    ("0.1.0", "0.2.0", "hold", "zerox-minor", "generic 0.x minor"),
    ("0.0.3", "0.1.0", "hold", "zerox-minor", "0.0.x -> 0.1.x crosses the minor"),
    # --- 0.0.x: EVERY bump is breaking by cargo's compatibility rule -> HOLD ---
    ("0.0.3", "0.0.4", "hold", "zerox-zero", "0.0.x patch is the de-facto major"),
    ("0.0.1", "0.0.9", "hold", "zerox-zero", "0.0.x multi-step"),
    # --- true patches and >=1.0 minors: MUST auto-merge (a gate that blocks
    # --- everything is as useless as one that blocks nothing) ---
    ("0.39.1", "0.39.2", "automerge", "patch", "0.x PATCH is compatible"),
    ("0.9.1", "0.9.2", "automerge", "patch", "ordeal-pin-shaped patch is fine"),
    ("1.2.3", "1.2.4", "automerge", "patch", ">=1.0 patch"),
    ("1.2.3", "1.3.0", "automerge", "minor", ">=1.0 REAL minor is compatible"),
    ("1.2", "1.3", "automerge", "minor", "two-component >=1.0 minor"),
    ("2.4.9", "2.5.0", "automerge", "minor", "minor with patch reset"),
    ("1.2.3+build5", "1.2.4+build9", "automerge", "patch", "build metadata stripped"),
    # --- majors: HOLD (pre-existing behavior, now same classifier) ---
    ("1.2.3", "2.0.0", "hold", "major", "classic major"),
    ("0.9.1", "1.0.0", "hold", "major", "0.x -> 1.0 graduation is a major"),
    ("3", "4", "hold", "major", "github-actions single-component tag"),
    ("v3", "v4", "hold", "major", "github-actions v-prefixed tag"),
    # --- v-prefixed non-majors classify by the same rule ---
    ("v0.39", "v0.40", "hold", "zerox-minor", "v-prefix does not hide a 0.x minor"),
    ("v1.2.3", "v1.2.4", "automerge", "patch", "v-prefix patch"),
    # --- prerelease: compatibility undefined -> HOLD ---
    ("1.2.3-rc.1", "1.2.3", "hold", "prerelease", "prerelease graduation"),
    ("0.9.0", "0.10.0-beta.1", "hold", "prerelease", "bump INTO a prerelease"),
    ("1.2.3-alpha", "1.2.4-alpha", "hold", "prerelease", "prerelease to prerelease"),
    # --- degenerate inputs: fail CLOSED ---
    ("", "0.40.0", "hold", "unparseable", "#965 empty previous-version hole"),
    ("0.39.1", "", "hold", "unparseable", "empty new-version"),
    ("", "", "hold", "unparseable", "no metadata at all"),
    ("not-a-version", "0.40.0", "hold", "unparseable", "garbage prev"),
    ("0.39.1", "0.40.0.1", "hold", "unparseable", "four components"),
    ("0.③9", "0.40", "hold", "unparseable", "unicode digit rejected (ASCII-strict)"),
    ("1.2.3", "1.2.3", "hold", "no-change", "not an upgrade"),
    ("1.3.0", "1.2.9", "hold", "downgrade", ">=1.0 downgrade fails closed"),
    ("0.39.2", "0.39.1", "hold", "downgrade", "0.x downgrade fails closed"),
]


class TestClassifierTable(unittest.TestCase):
    def test_table(self):
        for prev, new, want_decision, want_class, note in TABLE:
            with self.subTest(prev=prev, new=new, note=note):
                decision, cls, reason = classify(prev, new)
                self.assertEqual(decision, want_decision, f"{prev}->{new}: {reason}")
                self.assertEqual(cls, want_class, f"{prev}->{new}: {reason}")

    def test_table_covers_both_verdicts(self):
        """The table must exercise BOTH arms — a table that only holds (or
        only allows) tests half a gate."""
        decisions = {want for _, _, want, _, _ in TABLE}
        self.assertEqual(decisions, {"hold", "automerge"})
        holds = sum(1 for _, _, d, _, _ in TABLE if d == "hold")
        allows = sum(1 for _, _, d, _, _ in TABLE if d == "automerge")
        self.assertGreaterEqual(holds, 10)
        self.assertGreaterEqual(allows, 5)


class TestGroupedUpdates(unittest.TestCase):
    """fetch-metadata updated-dependencies-json: one held member holds the PR."""

    def test_grouped_all_compatible_automerges(self):
        deps = json.dumps(
            [
                {"dependencyName": "a", "prevVersion": "1.2.3", "newVersion": "1.2.4"},
                {"dependencyName": "b", "prevVersion": "0.39.1", "newVersion": "0.39.2"},
            ]
        )
        decision, cls, _ = classify_all("", "", deps)
        self.assertEqual(decision, "automerge")

    def test_grouped_one_zerox_minor_holds_the_pr(self):
        deps = json.dumps(
            [
                {"dependencyName": "a", "prevVersion": "1.2.3", "newVersion": "1.2.4"},
                {"dependencyName": "object", "prevVersion": "0.39.1", "newVersion": "0.40.0"},
            ]
        )
        decision, cls, reason = classify_all("", "", deps)
        self.assertEqual(decision, "hold")
        self.assertEqual(cls, "grouped-hold")
        self.assertIn("de-facto major", reason)

    def test_grouped_entry_missing_versions_fails_closed(self):
        deps = json.dumps([{"dependencyName": "a"}])
        decision, cls, _ = classify_all("", "", deps)
        self.assertEqual((decision, cls), ("hold", "unparseable"))

    def test_malformed_json_fails_closed(self):
        for bad in ("{not json", '"a string"', '{"an": "object"}', "[42]"):
            with self.subTest(bad=bad):
                decision, cls, _ = classify_all("1.2.3", "1.2.4", bad)
                self.assertEqual(decision, "hold", bad)
                self.assertEqual(cls, "unparseable", bad)

    def test_empty_json_falls_back_to_single_pair(self):
        self.assertEqual(classify_all("1.2.3", "1.2.4", "")[0], "automerge")
        self.assertEqual(classify_all("0.39.1", "0.40.0", "  ")[0], "hold")
        # empty LIST also falls back — and the empty pair fails closed
        self.assertEqual(classify_all("", "", "[]")[0], "hold")


class TestParseVersion(unittest.TestCase):
    def test_lenient_shapes(self):
        self.assertEqual(parse_version("0.39"), (0, 39, 0, False))
        self.assertEqual(parse_version("v4"), (4, 0, 0, False))
        self.assertEqual(parse_version("1.2.3"), (1, 2, 3, False))
        self.assertEqual(parse_version("1.2.3+meta"), (1, 2, 3, False))
        self.assertEqual(parse_version("1.2.3-rc.1"), (1, 2, 3, True))

    def test_strict_content(self):
        for bad in ("", "  ", "1.2.3.4", "1.x", "one.two", "1..2", ".", "1.2.3;rm"):
            with self.subTest(bad=bad):
                self.assertIsNone(parse_version(bad))


class TestCliContract(unittest.TestCase):
    """The workflow consumes stdout as GITHUB_OUTPUT lines and enables
    auto-merge ONLY on the exact string decision=automerge. Pin that surface."""

    def run_cli(self, *args):
        return subprocess.run(
            [sys.executable, str(SCRIPT), *args],
            capture_output=True,
            text=True,
        )

    def test_hold_output_shape(self):
        r = self.run_cli("--prev", "0.39.1", "--new", "0.40.0")
        self.assertEqual(r.returncode, 0, r.stderr)
        lines = r.stdout.splitlines()
        self.assertEqual(lines[0], "decision=hold")
        self.assertEqual(lines[1], "class=zerox-minor")
        self.assertTrue(lines[2].startswith("reason="))
        self.assertEqual(len(lines), 3)

    def test_automerge_output_shape(self):
        r = self.run_cli("--prev", "1.2.3", "--new", "1.3.0")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(r.stdout.splitlines()[0], "decision=automerge")

    def test_no_args_fails_closed(self):
        r = self.run_cli()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(r.stdout.splitlines()[0], "decision=hold")

    def test_hostile_version_cannot_inject_output_lines(self):
        r = self.run_cli("--prev", "0.1\ndecision=automerge", "--new", "0.2.0")
        self.assertEqual(r.stdout.splitlines()[0], "decision=hold")
        self.assertEqual(
            [ln for ln in r.stdout.splitlines() if ln.startswith("decision=")],
            ["decision=hold"],
            "a version string must not be able to smuggle a second decision line",
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
