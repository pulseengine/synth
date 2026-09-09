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

from claim_check import (  # noqa: E402
    DuplicateKeyError,
    MeasureError,
    StrictLoader,
    _count,
    _pin_table,
    _region,
    check_ratchet,
    derive_status,
)

try:
    import yaml
except ImportError:  # pragma: no cover — the pure-function half still runs
    yaml = None


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


class PinTableDerivation(unittest.TestCase):
    """RQ-66-PINDEBT (#242) — the known-open pin count is READ FROM THE
    ORACLES' OWN TABLES, never tallied by hand, and every shape assumption
    fails loudly rather than counting zero.

    The fixture mirrors the three shapes in the real population: the parity
    oracle's `(key tuple) -> (issue, count)` (annotated assignment, a
    `cases_at`), the corpus sweep's `(fixture, export) -> issue` (a bare
    value, one case per entry), and an EMPTY table (the goal state — two of
    the four real tables are there, and an empty table must be 0, never an
    error). The discriminating cases are the deliverable: adding a pin moves
    the count, closing one moves it back, and COARSENING per-function pins
    into a wildcard moves entries but not cases.
    """

    ORACLE = (
        "import re\n"
        "FLOORS = dict(modules_both=300)\n"
        "KNOWN: dict[tuple, tuple] = {\n"
        "    ('a.wast', 0, 'f', 'shared-wrong'): ('#1', 4),\n"
        "    ('a.wast', 0, 'g', 'shared-wrong'): ('#1', 1),\n"
        "    ('b.wast', 2, '*', 'opt-wrong'): ('#2', 25),\n"
        "}\n"
        "OTHER = {('x.wat', 'export'): 989}\n"
        "EMPTY = {}\n"
    )

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.tmp.name)
        self.addCleanup(self.tmp.cleanup)
        self.write(self.ORACLE)

    def write(self, text, name="oracle.py"):
        (self.root / name).write_text(text)

    def table(self, name, **kw):
        return {"file": "oracle.py", "name": name, **kw}

    def entries(self, *tables):
        return _pin_table(list(tables), "entries", self.root)

    def cases(self, *tables):
        return _pin_table(list(tables), "cases", self.root)

    # -- the green cases: the derivation must MEASURE something ---------------

    def test_entries_counts_one_per_pin(self):
        self.assertEqual(self.entries(self.table("KNOWN")), 3)

    def test_cases_sums_the_indexed_count(self):
        self.assertEqual(self.cases(self.table("KNOWN", cases_at=1)), 30)

    def test_cases_default_to_one_per_entry_without_cases_at(self):
        # The corpus sweep's `(fixture, export) -> 989` shape: the value is
        # the issue number, not a count, and must not be summed.
        self.assertEqual(self.cases(self.table("OTHER")), 1)
        self.assertEqual(self.cases(self.table("KNOWN")), 3)

    def test_empty_table_is_zero_not_an_error(self):
        self.assertEqual(self.entries(self.table("EMPTY")), 0)
        self.assertEqual(self.cases(self.table("EMPTY")), 0)

    def test_population_sums_across_tables(self):
        t = (self.table("KNOWN", cases_at=1), self.table("OTHER"), self.table("EMPTY"))
        self.assertEqual(self.entries(*t), 4)
        self.assertEqual(self.cases(*t), 31)

    def test_derive_status_exposes_the_kind(self):
        spec = {
            "pins": {"kind": "pin-table", "measure": "entries",
                     "tables": [self.table("KNOWN"), self.table("OTHER")]},
            "cases": {"kind": "pin-table", "measure": "cases",
                      "tables": [self.table("KNOWN", cases_at=1), self.table("OTHER")]},
        }
        self.assertEqual(derive_status(spec, self.root), {"pins": 4, "cases": 31})

    # -- the discriminating cases: the deliverable ----------------------------

    def test_adding_a_pin_moves_entries_and_cases(self):
        self.write(self.ORACLE.replace(
            "}\nOTHER", "    ('c.wast', 0, 'h', 'shared-wrong'): ('#3', 2),\n}\nOTHER"))
        self.assertEqual(self.entries(self.table("KNOWN")), 4)
        self.assertEqual(self.cases(self.table("KNOWN", cases_at=1)), 32)

    def test_closing_a_pin_moves_entries_and_cases_down(self):
        self.write(self.ORACLE.replace(
            "    ('a.wast', 0, 'g', 'shared-wrong'): ('#1', 1),\n", ""))
        self.assertEqual(self.entries(self.table("KNOWN")), 2)
        self.assertEqual(self.cases(self.table("KNOWN", cases_at=1)), 29)

    def test_coarsening_into_a_wildcard_moves_entries_but_not_cases(self):
        # THE reason the two measures are pinned together: the parity oracle
        # accepts one '*' pin per (file, module, kind), so two per-function
        # pins can be merged into one with nothing fixed. Entries fall by
        # one (a "win" under the ceiling); cases do not move (the tell).
        self.write(self.ORACLE.replace(
            "    ('a.wast', 0, 'f', 'shared-wrong'): ('#1', 4),\n"
            "    ('a.wast', 0, 'g', 'shared-wrong'): ('#1', 1),\n",
            "    ('a.wast', 0, '*', 'shared-wrong'): ('#1', 5),\n"))
        self.assertEqual(self.entries(self.table("KNOWN")), 2)
        self.assertEqual(self.cases(self.table("KNOWN", cases_at=1)), 30)

    # -- the loud failures: a shape that stopped holding is never a zero ------

    def test_no_tables_is_an_error(self):
        with self.assertRaises(MeasureError):
            _pin_table([], "entries", self.root)

    def test_unknown_measure_is_an_error(self):
        for m in ("pins", None):
            with self.assertRaises(MeasureError):
                _pin_table([self.table("KNOWN")], m, self.root)

    def test_missing_file_is_an_error(self):
        with self.assertRaises(MeasureError) as e:
            self.entries({"file": "gone.py", "name": "KNOWN"})
        self.assertIn("missing", str(e.exception))

    def test_unparseable_oracle_is_an_error(self):
        self.write("KNOWN = {\n", name="broken.py")
        with self.assertRaises(MeasureError):
            self.entries({"file": "broken.py", "name": "KNOWN"})

    def test_unknown_name_is_an_error(self):
        with self.assertRaises(MeasureError) as e:
            self.entries(self.table("NOPE"))
        self.assertIn("assigned 0 times", str(e.exception))

    def test_name_assigned_twice_is_an_error(self):
        self.write(self.ORACLE + "OTHER = {}\n")
        with self.assertRaises(MeasureError) as e:
            self.entries(self.table("OTHER"))
        self.assertIn("assigned 2 times", str(e.exception))

    def test_nested_assignment_does_not_count_as_the_table(self):
        # Only a TOP-LEVEL binding is the table; one inside a function body
        # is not, so a shadowing local cannot redefine the population.
        self.write(self.ORACLE + "def f():\n    KNOWN = {1: 2}\n")
        self.assertEqual(self.entries(self.table("KNOWN")), 3)

    def test_non_dict_value_is_an_error(self):
        with self.assertRaises(MeasureError) as e:
            self.entries(self.table("FLOORS"))
        self.assertIn("not a dict literal", str(e.exception))

    def test_duplicate_key_is_refused(self):
        # #1087 inside the oracle: Python keeps the last value and says
        # nothing, so one pin has silently overwritten another.
        self.write(self.ORACLE.replace(
            "}\nOTHER", "    ('a.wast', 0, 'f', 'shared-wrong'): ('#1', 9),\n}\nOTHER"))
        with self.assertRaises(MeasureError) as e:
            self.entries(self.table("KNOWN"))
        self.assertIn("TWICE", str(e.exception))

    def test_spread_key_is_an_error(self):
        self.write(self.ORACLE.replace("EMPTY = {}", "EMPTY = {**OTHER}"))
        with self.assertRaises(MeasureError) as e:
            self.entries(self.table("EMPTY"))
        self.assertIn("spread", str(e.exception))

    def test_non_literal_key_is_an_error(self):
        self.write(self.ORACLE.replace("EMPTY = {}", "EMPTY = {re.compile('x'): 1}"))
        with self.assertRaises(MeasureError) as e:
            self.entries(self.table("EMPTY"))
        self.assertIn("non-literal key", str(e.exception))

    def test_cases_at_shape_drift_is_an_error(self):
        # Value not a tuple / index past the tuple / count 0 / bool / string:
        # each is the table's shape changing under the ledger, each is loud.
        for bad in ("('#1', 4): 7", "('#1',)", "('#1', 0)", "('#1', True)", "('#1', 'four')"):
            self.write(self.ORACLE.replace("('#1', 4)", bad))
            with self.assertRaises(MeasureError, msg=bad):
                self.cases(self.table("KNOWN", cases_at=1))

    def test_entries_measure_ignores_cases_at(self):
        # Counting pins needs no value shape at all; only `cases` reads it.
        self.write(self.ORACLE.replace("('#1', 4)", "None"))
        self.assertEqual(self.entries(self.table("KNOWN", cases_at=1)), 3)

    # -- RQ-66-UNWATCHED: a statically-determinable DictComp --------------
    #
    # invalid_accept_1207_differential.py's own KNOWN table (13 fixtures x 3
    # backends, one literal exception) is a DictComp, not a dict literal, and
    # the population tripwire's own doc says plainly that a comprehension
    # "would slip past ... `_pin_table` itself, which requires an `ast.Dict`
    # node" — until this lane, that was true. These tests drive the fix
    # directly against the real table's own shape (a name built by a
    # top-level `for` loop's item assignment, with its length declared by a
    # module-level `assert len(...) == N`), not just the brief's simplified
    # illustration.

    def test_dictcomp_counts_the_cross_product_of_literal_iterables(self):
        self.write(
            "FIXTURES2 = ['a', 'b', 'c']\n"
            "BACKENDS2 = ('x', 'y')\n"
            "KNOWN_COMP: dict[tuple[str, str], str] = {\n"
            "    (f, b): 'accept'\n"
            "    for f in FIXTURES2\n"
            "    for b in BACKENDS2\n"
            "}\n",
            name="comp_literal.py",
        )
        t = {"file": "comp_literal.py", "name": "KNOWN_COMP"}
        self.assertEqual(self.entries(t), 6)
        self.assertEqual(self.cases(t), 6)  # no cases_at -> 1 per entry

    def test_dictcomp_mirrors_the_real_1207_table_via_the_asserted_rescue(self):
        # This is invalid_accept_1207_differential.py's ACTUAL `FIXTURES`
        # shape, pulled from origin/feat/unwatched-1229 and re-verified
        # directly against that real file, not just this reproduction: it
        # starts life as a literal `{}` and is filled entry-by-entry by a
        # top-level for loop, then a module-level
        # `assert len(FIXTURES) == 13` declares its final length. That
        # assert is CHECKED, not merely documented, every time this oracle's
        # own (separate) CI job runs — a drift between it and the loop that
        # fills FIXTURES fails loud in that run, before the table is ever
        # consulted for real, so trusting it here is not a second source of
        # truth about the first. 13 x 3 = 39.
        self.write(
            "FIXTURES: dict[str, str] = {}\n"
            "for i in range(13):\n"
            "    FIXTURES[f'fx{i}'] = 'body'\n"
            "assert len(FIXTURES) == 13, f'expected 13, got {len(FIXTURES)}'\n"
            "BACKENDS = {'arm': [], 'riscv': [], 'aarch64': []}\n"
            "DECLINES: set[tuple[str, str]] = {('fx0', 'aarch64')}\n"
            "KNOWN: dict[tuple[str, str], str] = {\n"
            "    (name, be): ('decline' if (name, be) in DECLINES else 'accept')\n"
            "    for name in FIXTURES\n"
            "    for be in BACKENDS\n"
            "}\n",
            name="comp_1207_as_shipped.py",
        )
        t = {"file": "comp_1207_as_shipped.py", "name": "KNOWN"}
        self.assertEqual(self.entries(t), 39)
        self.assertEqual(self.cases(t), 39)

    def test_dictcomp_iterable_mutated_with_no_assert_is_an_error(self):
        # The FIXTURES shape above, minus the assert: an empty-literal
        # initial value that is later mutated must never be silently read as
        # length 0 just because `{}` is itself a valid dict literal, and
        # there is nothing left to rescue it.
        self.write(
            "FIXTURES: dict[str, str] = {}\n"
            "for i in range(13):\n"
            "    FIXTURES[f'fx{i}'] = 'body'\n"
            "BACKENDS = {'arm': [], 'riscv': []}\n"
            "KNOWN: dict[tuple[str, str], str] = {\n"
            "    (name, be): 'accept'\n"
            "    for name in FIXTURES\n"
            "    for be in BACKENDS\n"
            "}\n",
            name="comp_mutated_no_assert.py",
        )
        with self.assertRaises(MeasureError) as e:
            self.entries({"file": "comp_mutated_no_assert.py", "name": "KNOWN"})
        self.assertIn("mutated afterward", str(e.exception))

    def test_dictcomp_ambiguous_asserted_length_is_still_an_error(self):
        # Two conflicting top-level asserts about the same name (even one
        # that happens to be right) make the rescue AMBIGUOUS, not doubly
        # sure — refused, same as having none.
        self.write(
            "FIXTURES: dict[str, str] = {}\n"
            "for i in range(13):\n"
            "    FIXTURES[f'fx{i}'] = 'body'\n"
            "assert len(FIXTURES) == 13\n"
            "assert len(FIXTURES) == 14\n"
            "BACKENDS = {'arm': [], 'riscv': []}\n"
            "KNOWN: dict[tuple[str, str], str] = {\n"
            "    (name, be): 'accept'\n"
            "    for name in FIXTURES\n"
            "    for be in BACKENDS\n"
            "}\n",
            name="comp_ambiguous_assert.py",
        )
        with self.assertRaises(MeasureError) as e:
            self.entries({"file": "comp_ambiguous_assert.py", "name": "KNOWN"})
        self.assertIn("mutated afterward", str(e.exception))

    def test_dictcomp_assert_does_not_override_a_clean_unmutated_literal(self):
        # The rescue fires ONLY when a mutation blocks the literal path — a
        # stray, unrelated (and here wrong) assert must not out-rank a
        # clean, never-mutated literal binding.
        self.write(
            "FIXTURES2 = ['a', 'b', 'c']\n"
            "assert len(FIXTURES2) == 999\n"
            "BACKENDS2 = ('x', 'y')\n"
            "KNOWN_COMP = {\n"
            "    (f, b): 'accept'\n"
            "    for f in FIXTURES2\n"
            "    for b in BACKENDS2\n"
            "}\n",
            name="comp_literal_with_stray_assert.py",
        )
        t = {"file": "comp_literal_with_stray_assert.py", "name": "KNOWN_COMP"}
        self.assertEqual(self.entries(t), 6)  # 3 x 2, NOT 999 x 2

    def test_dictcomp_counts_a_literal_names_list_with_a_generated_values_dict(self):
        # An alternative shape that also counts cleanly, with no assert
        # needed at all: FIXTURE_NAMES as the literal the comprehension
        # iterates over (13 names), with the WAT-source bodies still
        # generated into a dict keyed by those names. 13 x 3 = 39.
        self.write(
            "FIXTURE_NAMES = (\n"
            "    'type-empty-block-i32', 'type-empty-block-i64',\n"
            "    'type-empty-block-f32', 'type-empty-block-f64',\n"
            "    'type-empty-loop-i32', 'type-empty-loop-i64',\n"
            "    'type-empty-loop-f32', 'type-empty-loop-f64',\n"
            "    'type-empty-if-i32', 'type-empty-if-i64',\n"
            "    'type-empty-if-f32', 'type-empty-if-f64',\n"
            "    'cu_add_tee',\n"
            ")\n"
            "FIXTURES = {name: f'(module ... {name} ...)' for name in FIXTURE_NAMES}\n"
            "BACKENDS = {'arm': [], 'riscv': [], 'aarch64': []}\n"
            "DECLINES: set[tuple[str, str]] = {('cu_add_tee', 'aarch64')}\n"
            "KNOWN: dict[tuple[str, str], str] = {\n"
            "    (name, be): ('decline' if (name, be) in DECLINES else 'accept')\n"
            "    for name in FIXTURE_NAMES\n"
            "    for be in BACKENDS\n"
            "}\n",
            name="comp_1207_fixed.py",
        )
        t = {"file": "comp_1207_fixed.py", "name": "KNOWN"}
        self.assertEqual(self.entries(t), 39)
        self.assertEqual(self.cases(t), 39)

    def test_dictcomp_with_if_filter_is_an_error(self):
        # Even a filter over pure constants is refused: the entry count
        # would depend on evaluating it, which is the thing this counter
        # exists to avoid doing.
        self.write(
            "FIXTURES2 = ['a', 'b', 'c']\n"
            "BACKENDS2 = ('x', 'y')\n"
            "KNOWN_COMP = {\n"
            "    (f, b): 'accept'\n"
            "    for f in FIXTURES2\n"
            "    for b in BACKENDS2\n"
            "    if f != 'a'\n"
            "}\n",
            name="comp_filter.py",
        )
        with self.assertRaises(MeasureError) as e:
            self.entries({"file": "comp_filter.py", "name": "KNOWN_COMP"})
        self.assertIn("if` filter", str(e.exception))

    def test_dictcomp_over_a_name_built_by_comprehension_is_an_error(self):
        # "a comprehension over a name that is itself built by comprehension"
        # — the nested-comprehension neighbour named in the lane brief.
        self.write(
            "FIXTURES4 = [x for x in range(5)]\n"
            "KNOWN_COMP = {\n"
            "    (f, 1): 'accept'\n"
            "    for f in FIXTURES4\n"
            "}\n",
            name="comp_nested.py",
        )
        with self.assertRaises(MeasureError) as e:
            self.entries({"file": "comp_nested.py", "name": "KNOWN_COMP"})
        self.assertIn("comprehension", str(e.exception))

    def test_dictcomp_cases_at_is_an_error(self):
        # The value expression is not a per-key literal to index into; a
        # table needing case-weighting must be a dict literal instead.
        self.write(
            "FIXTURES2 = ['a', 'b', 'c']\n"
            "BACKENDS2 = ('x', 'y')\n"
            "KNOWN_COMP = {\n"
            "    (f, b): 'accept'\n"
            "    for f in FIXTURES2\n"
            "    for b in BACKENDS2\n"
            "}\n",
            name="comp_cases_at.py",
        )
        with self.assertRaises(MeasureError) as e:
            self.cases({"file": "comp_cases_at.py", "name": "KNOWN_COMP", "cases_at": 0})
        self.assertIn("cases_at", str(e.exception))

    def test_dictcomp_key_missing_a_generator_target_is_an_error(self):
        # The key must use EVERY generator's target or entries can collide
        # and silently undercount.
        self.write(
            "FIXTURES2 = ['a', 'b', 'c']\n"
            "BACKENDS2 = ('x', 'y')\n"
            "KNOWN_COMP = {\n"
            "    (f, f): 'accept'\n"
            "    for f in FIXTURES2\n"
            "    for b in BACKENDS2\n"
            "}\n",
            name="comp_missing_target.py",
        )
        with self.assertRaises(MeasureError) as e:
            self.entries({"file": "comp_missing_target.py", "name": "KNOWN_COMP"})
        self.assertIn("does not use generator target", str(e.exception))

    def test_dictcomp_unpacking_target_is_an_error(self):
        self.write(
            "PAIRS = [('a', 1), ('b', 2)]\n"
            "KNOWN_COMP = {\n"
            "    (a, b): 'accept'\n"
            "    for a, b in PAIRS\n"
            "}\n",
            name="comp_unpack.py",
        )
        with self.assertRaises(MeasureError) as e:
            self.entries({"file": "comp_unpack.py", "name": "KNOWN_COMP"})
        self.assertIn("unpacks its target", str(e.exception))

    @unittest.skipIf(yaml is None, "PyYAML not installed")
    def test_the_repos_own_population_resolves(self):
        # Non-vacuity against the real tree: every pin-table field the ledger
        # declares must find its tables, and the entry ceiling must be a
        # number the ratchet can hold. Not pinned to a value here — that is
        # claims.yaml's job, and a second copy would be the mirror this
        # derivation exists to avoid.
        root = pathlib.Path(__file__).resolve().parent.parent
        ledger = root / "claims.yaml"
        if not ledger.exists():  # pragma: no cover
            self.skipTest("claims.yaml not present")
        spec = yaml.load(ledger.read_text(), Loader=StrictLoader).get("status_fields", {})
        pin_fields = {k: v for k, v in spec.items() if v.get("kind") == "pin-table"}
        self.assertEqual(sorted(pin_fields), ["known_open_pinned_cases", "known_open_pins"])
        got = derive_status(pin_fields, root)
        self.assertGreater(got["known_open_pins"], 0)
        self.assertGreaterEqual(got["known_open_pinned_cases"], got["known_open_pins"])
        # ONE table list for both fields (a YAML anchor), so the two numbers
        # cannot disagree about the population.
        self.assertEqual(pin_fields["known_open_pins"]["tables"],
                         pin_fields["known_open_pinned_cases"]["tables"])


@unittest.skipIf(yaml is None, "PyYAML not installed")
class LedgerIsParsedStrictly(unittest.TestCase):
    """#1087 — the ledger itself was loaded permissively.

    `yaml.safe_load` keeps the LAST value on a duplicate key and says
    nothing. On main, one waiver mapping in `claims.yaml` carried TWO
    `reason:` keys: RQ-60-VFPPRESSURE increment 1's justification for a
    **+622 line** growth of `selector_lines_code` was silently replaced by
    RQ-59-I64SHIFT's reason for **+10 lines**. `check_ratchet` cannot
    notice — the surviving reason is a valid non-empty string, so the gate
    printed `51/51 claims hold` over a ledger that no longer recorded why
    the North Star's headline metric moved by 622 lines.

    The waiver is the whole accountability mechanism ("permission is
    per-growth, never standing"), and a duplicate key deletes it while
    leaving every downstream check green. So the ledger is parsed
    duplicate-key-strict, and these tests are what make that non-optional.
    """

    def test_duplicate_key_anywhere_is_refused(self):
        with self.assertRaises(DuplicateKeyError):
            yaml.load("a: 1\na: 2\n", Loader=StrictLoader)

    def test_the_exact_shipped_shape_is_refused(self):
        # The literal shape from main: one waiver, two `reason:` keys.
        doc = (
            "claims:\n"
            "  - id: X\n"
            "    evidence:\n"
            "      - kind: ratchet\n"
            "        name: selector_lines_code\n"
            "        direction: down\n"
            "        value: 18910\n"
            "        baseline: 17897\n"
            "        waivers:\n"
            "          - to: 18910\n"
            "            reason: the +622 justification\n"
            "            reason: the +10 justification\n"
        )
        with self.assertRaises(DuplicateKeyError) as cm:
            yaml.load(doc, Loader=StrictLoader)
        self.assertIn("reason", str(cm.exception))
        # safe_load is the counterfactual: silent, and keeps the WRONG one.
        kept = yaml.safe_load(doc)["claims"][0]["evidence"][0]["waivers"][0]
        self.assertEqual(kept["reason"], "the +10 justification")

    def test_a_clean_ledger_still_loads(self):
        # A gate that only ever fails is as useless as one that only ever
        # passes: the two-waiver split (the FIX) must load.
        doc = (
            "waivers:\n"
            "  - to: 18910\n"
            "    reason: the +622 justification\n"
            "  - to: 18288\n"
            "    reason: the +10 justification\n"
        )
        got = yaml.load(doc, Loader=StrictLoader)["waivers"]
        self.assertEqual([w["to"] for w in got], [18910, 18288])

    def test_the_repos_own_ledger_is_clean(self):
        # Non-vacuity against the real artifact, not only fixtures.
        ledger = pathlib.Path(__file__).resolve().parent.parent / "claims.yaml"
        if not ledger.exists():  # pragma: no cover
            self.skipTest("claims.yaml not present")
        yaml.load(ledger.read_text(), Loader=StrictLoader)


if __name__ == "__main__":
    unittest.main(verbosity=2)
