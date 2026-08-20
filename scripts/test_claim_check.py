#!/usr/bin/env python3
"""Unit tests for the parts of claim_check.py that can silently measure nothing.

WHY THIS FILE EXISTS (RQ-58-METRIC / #242). v0.58's thesis is that this repo's
CHECKERS are where the defects are: v0.57 found five of its ten defects in
checking machinery, and the FEATURE_MATRIX freshness gate compares the render to
the template and never the template to the code. RQ-58-METRIC adds another
checker. A 100-line gate whose only validation is "it fired once during the PR
that added it" is the next entry on that list, so the ratchet predicate and the
region/counting primitives are driven directly here — every branch, including
the ones that are supposed to PASS, because a gate that only ever fails is as
useless as one that only ever passes.

Stdlib `unittest` only, no pytest/PyYAML needed for the pure-function half.

    python3 scripts/test_claim_check.py        (wired in the claim-check CI job)
"""

import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from claim_check import MeasureError, _count, _region, check_ratchet  # noqa: E402


def ceiling(**kw):
    """A `direction: down` pin sitting exactly on its baseline (the green case)."""
    ev = {"kind": "ratchet", "name": "m", "direction": "down", "value": 100, "baseline": 100}
    ev.update(kw)
    return ev


def floor(**kw):
    """A `direction: up` pin sitting exactly on its baseline (the green case)."""
    ev = {"kind": "ratchet", "name": "m", "direction": "up", "value": 50, "baseline": 50}
    ev.update(kw)
    return ev


class RatchetGreen(unittest.TestCase):
    """The gate must be able to PASS — otherwise it is noise and gets disabled."""

    def test_ceiling_on_baseline_passes(self):
        self.assertEqual(check_ratchet(100, ceiling()), [])

    def test_floor_on_baseline_passes(self):
        self.assertEqual(check_ratchet(50, floor()), [])

    def test_ceiling_regression_with_matching_waiver_passes(self):
        ev = ceiling(value=120, waivers=[{"to": 120, "reason": "explicit arms replace 3 wildcards"}])
        self.assertEqual(check_ratchet(120, ev), [])

    def test_floor_regression_with_matching_waiver_passes(self):
        ev = floor(value=40, waivers=[{"to": 40, "reason": "10 rules retired with their arms"}])
        self.assertEqual(check_ratchet(40, ev), [])


class RatchetSlackFree(unittest.TestCase):
    """`value:` must equal the live derivation — in BOTH directions."""

    def test_growth_without_ledger_update_is_red(self):
        fails = check_ratchet(112, ceiling())
        self.assertEqual(len(fails), 1)
        self.assertIn("MOVED the WRONG way", fails[0])
        self.assertIn("derived 112", fails[0])

    def test_shrink_without_ledger_update_is_also_red(self):
        # An unrecorded improvement is still drift: it leaves slack the next
        # regression could hide in.
        fails = check_ratchet(88, ceiling())
        self.assertEqual(len(fails), 1)
        self.assertIn("MOVED the right way", fails[0])

    def test_floor_drop_without_ledger_update_is_red(self):
        fails = check_ratchet(45, floor())
        self.assertIn("MOVED the WRONG way", fails[0])

    def test_ceiling_with_slack_cannot_be_expressed(self):
        # The vacuous version of this gate — a ceiling recorded above the live
        # value — is rejected outright rather than quietly tolerated.
        self.assertNotEqual(check_ratchet(100, ceiling(value=100, baseline=500)), [])


class RatchetBanking(unittest.TestCase):
    def test_unbanked_improvement_is_red(self):
        fails = check_ratchet(90, ceiling(value=90))
        self.assertEqual(len(fails), 1)
        self.assertIn("NOT BANKED", fails[0])
        self.assertIn("baseline: 90", fails[0])

    def test_banked_improvement_passes(self):
        self.assertEqual(check_ratchet(90, ceiling(value=90, baseline=90)), [])

    def test_unbanked_floor_improvement_is_red(self):
        self.assertIn("NOT BANKED", check_ratchet(60, floor(value=60))[0])


class RatchetWaivers(unittest.TestCase):
    def test_regression_without_waiver_is_red(self):
        fails = check_ratchet(120, ceiling(value=120))
        self.assertEqual(len(fails), 1)
        self.assertIn("NO waiver", fails[0])

    def test_waiver_for_a_different_value_does_not_cover_this_one(self):
        # THE anti-standing-licence property: a waiver is bound to the value it
        # authorised, so a SECOND regression needs a SECOND waiver.
        ev = ceiling(value=140, waivers=[{"to": 120, "reason": "earlier, smaller growth"}])
        self.assertIn("NO waiver", check_ratchet(140, ev)[0])

    def test_empty_reason_is_red(self):
        ev = ceiling(value=120, waivers=[{"to": 120, "reason": "   "}])
        self.assertIn("EMPTY reason", check_ratchet(120, ev)[0])

    def test_missing_reason_is_red(self):
        ev = ceiling(value=120, waivers=[{"to": 120}])
        self.assertIn("EMPTY reason", check_ratchet(120, ev)[0])

    def test_dead_waiver_is_red(self):
        # Waiver already satisfied by the baseline: authorises nothing, but sits
        # there looking like permission.
        ev = ceiling(waivers=[{"to": 95, "reason": "stale"}])
        self.assertIn("DEAD waiver", check_ratchet(100, ev)[0])

    def test_waiver_equal_to_baseline_is_dead(self):
        ev = ceiling(waivers=[{"to": 100, "reason": "stale"}])
        self.assertIn("DEAD waiver", check_ratchet(100, ev)[0])

    def test_non_integer_waiver_target_is_red(self):
        ev = ceiling(waivers=[{"to": "lots", "reason": "x"}])
        self.assertIn("must be an integer", check_ratchet(100, ev)[0])


class RatchetTrack(unittest.TestCase):
    """`direction: track` — slack-free, but asserts no direction."""

    def track(self, **kw):
        ev = {"kind": "ratchet", "name": "m", "direction": "track", "value": 100}
        ev.update(kw)
        return ev

    def test_on_value_passes(self):
        self.assertEqual(check_ratchet(100, self.track()), [])

    def test_movement_in_either_direction_is_red(self):
        for derived in (101, 99):
            fails = check_ratchet(derived, self.track())
            self.assertEqual(len(fails), 1, derived)
            self.assertIn("MOVED", fails[0])
            self.assertIn("NO waiver needed", fails[0])

    def test_waiver_on_a_track_pin_is_red(self):
        # An inert waiver on a non-directional pin reads as permission later.
        ev = self.track(waivers=[{"to": 120, "reason": "x"}])
        self.assertIn("cannot carry waivers", check_ratchet(100, ev)[0])

    def test_baseline_on_a_track_pin_is_red(self):
        # A field the checker reads nowhere will drift and then get quoted.
        ev = self.track(baseline=100)
        self.assertIn("no baseline", check_ratchet(100, ev)[0])

    def test_track_does_not_demand_a_baseline(self):
        self.assertNotIn("baseline", "".join(check_ratchet(100, self.track())))


class RatchetMalformed(unittest.TestCase):
    """A malformed pin must be LOUD, never silently skipped."""

    def test_missing_direction_is_red(self):
        ev = ceiling()
        del ev["direction"]
        self.assertIn("direction must be", check_ratchet(100, ev)[0])

    def test_bogus_direction_is_red(self):
        self.assertIn("direction must be", check_ratchet(100, ceiling(direction="sideways"))[0])

    def test_directed_pin_still_demands_a_baseline(self):
        ev = {"kind": "ratchet", "name": "m", "direction": "down", "value": 100}
        self.assertIn("'baseline' must be an integer", check_ratchet(100, ev)[0])

    def test_non_integer_value_is_red(self):
        self.assertIn("must be an integer", check_ratchet(100, ceiling(value="100"))[0])

    def test_bool_is_not_an_integer(self):
        self.assertIn("must be an integer", check_ratchet(100, ceiling(value=True))[0])

    def test_missing_baseline_is_red(self):
        ev = ceiling()
        del ev["baseline"]
        self.assertIn("must be an integer", check_ratchet(100, ev)[0])


class RegionAndCounting(unittest.TestCase):
    """The derivation primitives the size pins rest on."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)

    def write(self, name, text):
        (self.root / name).write_text(text)

    def test_region_truncates_at_a_unique_marker(self):
        self.assertEqual(_region("a\nb\nMARK\nc\n", "MARK", "f"), "a\nb\n")

    def test_absent_marker_is_an_error_not_the_whole_file(self):
        with self.assertRaises(MeasureError) as e:
            _region("a\nb\n", "MARK", "f")
        self.assertIn("occurs 0 times", str(e.exception))

    def test_repeated_marker_is_an_error_not_the_first_one(self):
        with self.assertRaises(MeasureError) as e:
            _region("a\nMARK\nb\nMARK\n", "MARK", "f")
        self.assertIn("occurs 2 times", str(e.exception))

    def test_newline_pattern_counts_lines_exactly_like_wc_l(self):
        self.write("f.rs", "one\ntwo\nthree\n")
        n, matched = _count(r"\n", ["f.rs"], self.root)
        self.assertTrue(matched)
        self.assertEqual(n, 3)

    def test_region_scoped_count_excludes_the_tail(self):
        self.write("f.rs", "code\ncode\n#[cfg(test)]\nmod tests {\ntest\ntest\n")
        n, _ = _count(r"\n", ["f.rs"], self.root, before="#[cfg(test)]\nmod tests")
        self.assertEqual(n, 2)

    # -- RQ-58-SPLIT (#242): the family measurement --------------------------
    # One `count` field summing a root file (marker-truncated) and split-out
    # sibling files (no marker => whole file counts). The point of the tests:
    # a pure RELOCATION inside the family is ±0, a DELETION anywhere in the
    # family still falls, and the opt-in does not loosen the default.

    def test_whole_file_optin_counts_a_markerless_file_whole(self):
        self.assertEqual(
            _region("a\nb\n", "MARK", "f", missing="whole-file"), "a\nb\n"
        )

    def test_whole_file_optin_still_truncates_when_the_marker_is_present(self):
        self.assertEqual(
            _region("a\nMARK\nb\n", "MARK", "f", missing="whole-file"), "a\n"
        )

    def test_whole_file_optin_keeps_a_repeated_marker_a_hard_error(self):
        with self.assertRaises(MeasureError):
            _region("a\nMARK\nb\nMARK\n", "MARK", "f", missing="whole-file")

    def test_absent_marker_stays_an_error_without_the_optin(self):
        self.write("root.rs", "code\n#[cfg(test)]\nmod tests {\ntest\n")
        self.write("sibling.rs", "code\ncode\n")
        with self.assertRaises(MeasureError):
            _count(r"\n", ["*.rs"], self.root, before="#[cfg(test)]\nmod tests")

    def test_unknown_before_missing_is_an_error(self):
        self.write("a.rs", "x\n")
        with self.assertRaises(MeasureError):
            _count(r"x", ["*.rs"], self.root, before="M", before_missing="ignore")

    def _family(self):
        return _count(
            r"\n",
            ["root.rs", "family/**/*.rs"],
            self.root,
            before="#[cfg(test)]\nmod tests",
            before_missing="whole-file",
        )[0]

    def test_family_sums_root_region_plus_whole_siblings(self):
        self.write("root.rs", "a\nb\n#[cfg(test)]\nmod tests {\nt\nt\n")
        (self.root / "family").mkdir()
        self.write("family/sib.rs", "c\nd\ne\n")
        self.assertEqual(self._family(), 5)  # 2 root code + 3 sibling

    def test_family_is_invariant_under_pure_relocation(self):
        self.write("root.rs", "a\nb\nc\nd\n#[cfg(test)]\nmod tests {\nt\n")
        (self.root / "family").mkdir()
        self.write("family/sib.rs", "")
        before = self._family()
        # move two code lines root -> sibling; delete nothing
        self.write("root.rs", "a\nb\n#[cfg(test)]\nmod tests {\nt\n")
        self.write("family/sib.rs", "c\nd\n")
        self.assertEqual(self._family(), before)

    def test_family_still_falls_when_a_sibling_line_is_deleted(self):
        self.write("root.rs", "a\nb\n#[cfg(test)]\nmod tests {\nt\n")
        (self.root / "family").mkdir()
        self.write("family/sib.rs", "c\nd\n")
        before = self._family()
        self.write("family/sib.rs", "c\n")
        self.assertEqual(self._family(), before - 1)

    def test_unit_files_counts_files_not_matches(self):
        self.write("a.rs", "mirror mirror mirror\n")
        self.write("b.rs", "mirror\n")
        self.write("c.rs", "nothing\n")
        self.assertEqual(_count("mirror", ["*.rs"], self.root)[0], 4)
        self.assertEqual(_count("mirror", ["*.rs"], self.root, unit="files")[0], 2)

    def test_unknown_unit_is_an_error(self):
        self.write("a.rs", "x\n")
        with self.assertRaises(MeasureError):
            _count("x", ["*.rs"], self.root, unit="lines")

    def test_glob_matching_nothing_reports_it_rather_than_returning_zero(self):
        n, matched = _count("x", ["nope/**/*.rs"], self.root)
        self.assertEqual((n, matched), (0, False))

    def test_wildcard_arm_pattern_is_anchored_to_line_start(self):
        # Guards the selector wildcard derivation: `Some(_) => ...` and a `_ =>`
        # inside a comment sentence must NOT be counted as match arms.
        self.write(
            "f.rs",
            "    _ => todo!(),\n"
            "        _ => bail!(),\n"
            "    Some(_) => ok(),\n"
            "    // the main match's `_ =>` arm falls through\n",
        )
        self.assertEqual(_count(r"^[ \t]*_ =>", ["f.rs"], self.root)[0], 2)


if __name__ == "__main__":
    unittest.main(verbosity=2)
