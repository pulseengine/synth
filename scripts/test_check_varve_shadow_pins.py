#!/usr/bin/env python3
"""Unit tests for scripts/check_varve_shadow_pins.py (RQ-66-VARVE, #1236).

Fixtures are REAL captured `varve verify` output, not synthesized text:

- FIXTURE_CI_RUN1 / FIXTURE_CI_RUN2 / FIXTURE_CI_RUN3: the exact stdout from
  three real CI runs on pulseengine/synth PR #1244 (`rivet-federated` job) —
  runners `pulseengine-ci-01-9`, `-01-12` and `-01-11` — all three reporting
  exactly one shadowed tool: `rivet`.
- FIXTURE_CI_RUN4_CLEAN: the exact stdout from a FOURTH real CI run, runner
  `pulseengine-ci-01-6` — completely clean, no shadow at all. This is the
  fixture that falsified the second design (an exact-match pin that
  required the shadow to be PRESENT): the same repo, the same pin, the
  same commit, a DIFFERENT runner — clean. Proof the observable is
  runner-state, not a repo property, and must not be gated on presence.
- FIXTURE_LOCAL_MULTI: real local `varve verify` output on the authoring
  machine, which (unlike the CI runners sampled) has FIVE ambient tools
  installed via cargo — used as the "a NEW, unpinned tool showed up" case.
- FIXTURE_DIFFERENT_PATH_SAME_TOOL: SYNTHETIC (not observed) — same tool
  name (`rivet`) as the pinned hazard, shadowed via a path shape the pin
  does NOT describe, for the "different hazard, same name" case.

Run: python3 scripts/test_check_varve_shadow_pins.py
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_varve_shadow_pins import (  # noqa: E402
    KNOWN_OPEN,
    check,
    shadowed_pairs_from_verify_output,
    shadowed_tools_from_verify_output,
)

FIXTURE_CI_RUN1 = """\
layer 2026.09.2 sha256:67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025 verified: signature OK, 12 tool(s) match their signed digests
error: the layer verifies, but 1 of its tool(s) are not what your PATH runs (REQ-SHADOW-001):

`rivet` on your PATH is /var/lib/runners/runner9/.cargo/bin/rivet, not the pinned /var/lib/runners/runner9/.varve/realms/a8ca9eb8fec663e6/core/sha256-67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025/bin/rivet.
Your shell will run the first one; varve dispatches the second, so `varve which` and `varve run` disagree with what you get by typing `rivet`.
Fix: run `varve shim install` and put the shim directory FIRST on PATH (`. "$VARVE_ROOT/env"`, default ~/.varve/env), or remove the earlier entry.
"""

FIXTURE_CI_RUN2 = """\
layer 2026.09.2 sha256:67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025 verified: signature OK, 12 tool(s) match their signed digests
error: the layer verifies, but 1 of its tool(s) are not what your PATH runs (REQ-SHADOW-001):

`rivet` on your PATH is /var/lib/runners/runner12/.cargo/bin/rivet, not the pinned /var/lib/runners/runner12/.varve/realms/a8ca9eb8fec663e6/core/sha256-67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025/bin/rivet.
Your shell will run the first one; varve dispatches the second, so `varve which` and `varve run` disagree with what you get by typing `rivet`.
Fix: run `varve shim install` and put the shim directory FIRST on PATH (`. "$VARVE_ROOT/env"`, default ~/.varve/env), or remove the earlier entry.
"""

FIXTURE_CI_RUN3 = """\
layer 2026.09.2 sha256:67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025 verified: signature OK, 12 tool(s) match their signed digests
error: the layer verifies, but 1 of its tool(s) are not what your PATH runs (REQ-SHADOW-001):

`rivet` on your PATH is /var/lib/runners/runner11/.cargo/bin/rivet, not the pinned /var/lib/runners/runner11/.varve/realms/a8ca9eb8fec663e6/core/sha256-67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025/bin/rivet.
Your shell will run the first one; varve dispatches the second, so `varve which` and `varve run` disagree with what you get by typing `rivet`.
Fix: run `varve shim install` and put the shim directory FIRST on PATH (`. "$VARVE_ROOT/env"`, default ~/.varve/env), or remove the earlier entry.
"""

# Real, captured from job 102615600973 (run 34395957454), runner
# pulseengine-ci-01-6, on the SAME commit/pin as runs 1-3 above. Completely
# clean — this is the fixture that falsified exact-match-on-presence.
FIXTURE_CI_RUN4_CLEAN = (
    "layer 2026.09.2 sha256:67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025"
    " verified: signature OK, 12 tool(s) match their signed digests\n"
)

FIXTURE_LOCAL_MULTI = """\
layer 2026.09.2 sha256:67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025 verified: signature OK, 12 tool(s) match their signed digests
error: the layer verifies, but 5 of its tool(s) are not what your PATH runs (REQ-SHADOW-001):

`loom` on your PATH is /Users/r/.cargo/bin/loom, not the pinned /Users/r/.varve/realms/a8ca9eb8fec663e6/core/sha256-67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025/bin/loom.
Your shell will run the first one; varve dispatches the second, so `varve which` and `varve run` disagree with what you get by typing `loom`.
Fix: run `varve shim install` and put the shim directory FIRST on PATH (`. "$VARVE_ROOT/env"`, default ~/.varve/env), or remove the earlier entry.

`meld` on your PATH is /Users/r/.cargo/bin/meld, not the pinned /Users/r/.varve/realms/a8ca9eb8fec663e6/core/sha256-67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025/bin/meld.
Your shell will run the first one; varve dispatches the second, so `varve which` and `varve run` disagree with what you get by typing `meld`.
Fix: run `varve shim install` and put the shim directory FIRST on PATH (`. "$VARVE_ROOT/env"`, default ~/.varve/env), or remove the earlier entry.

`rivet` on your PATH is /Users/r/.cargo/bin/rivet, not the pinned /Users/r/.varve/realms/a8ca9eb8fec663e6/core/sha256-67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025/bin/rivet.
Your shell will run the first one; varve dispatches the second, so `varve which` and `varve run` disagree with what you get by typing `rivet`.
Fix: run `varve shim install` and put the shim directory FIRST on PATH (`. "$VARVE_ROOT/env"`, default ~/.varve/env), or remove the earlier entry.

`spar` on your PATH is /Users/r/.cargo/bin/spar, not the pinned /Users/r/.varve/realms/a8ca9eb8fec663e6/core/sha256-67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025/bin/spar.
Your shell will run the first one; varve dispatches the second, so `varve which` and `varve run` disagree with what you get by typing `spar`.
Fix: run `varve shim install` and put the shim directory FIRST on PATH (`. "$VARVE_ROOT/env"`, default ~/.varve/env), or remove the earlier entry.

`synth` on your PATH is /Users/r/.cargo/bin/synth, not the pinned /Users/r/.varve/realms/a8ca9eb8fec663e6/core/sha256-67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025/bin/synth.
Your shell will run the first one; varve dispatches the second, so `varve which` and `varve run` disagree with what you get by typing `synth`.
Fix: run `varve shim install` and put the shim directory FIRST on PATH (`. "$VARVE_ROOT/env"`, default ~/.varve/env), or remove the earlier entry.
"""

# SYNTHETIC — not an observed run. Same tool name (`rivet`) as the pinned
# hazard, but shadowed via a path shape the pin does NOT describe (a
# Homebrew keg instead of a plain `cargo install`'s default bin dir). This
# is the "different hazard wearing the same name" case the pin's scope
# (tool name + path shape, not tool name alone) exists to catch — real
# fixtures for it don't exist yet because it hasn't happened.
FIXTURE_DIFFERENT_PATH_SAME_TOOL = """\
layer 2026.09.2 sha256:67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025 verified: signature OK, 12 tool(s) match their signed digests
error: the layer verifies, but 1 of its tool(s) are not what your PATH runs (REQ-SHADOW-001):

`rivet` on your PATH is /opt/homebrew/bin/rivet, not the pinned /var/lib/runners/runner9/.varve/realms/a8ca9eb8fec663e6/core/sha256-67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025/bin/rivet.
Your shell will run the first one; varve dispatches the second, so `varve which` and `varve run` disagree with what you get by typing `rivet`.
Fix: run `varve shim install` and put the shim directory FIRST on PATH (`. "$VARVE_ROOT/env"`, default ~/.varve/env), or remove the earlier entry.
"""


class ExtractShadowedTools(unittest.TestCase):
    def test_run1_extracts_rivet_only(self):
        self.assertEqual(shadowed_tools_from_verify_output(FIXTURE_CI_RUN1), {"rivet"})

    def test_run2_extracts_rivet_only(self):
        self.assertEqual(shadowed_tools_from_verify_output(FIXTURE_CI_RUN2), {"rivet"})

    def test_run3_extracts_rivet_only(self):
        self.assertEqual(shadowed_tools_from_verify_output(FIXTURE_CI_RUN3), {"rivet"})

    def test_run4_clean_extracts_nothing(self):
        self.assertEqual(shadowed_tools_from_verify_output(FIXTURE_CI_RUN4_CLEAN), set())

    def test_local_multi_extracts_all_five(self):
        self.assertEqual(
            shadowed_tools_from_verify_output(FIXTURE_LOCAL_MULTI),
            {"loom", "meld", "rivet", "spar", "synth"},
        )

    def test_pairs_capture_the_ambient_path_not_just_the_name(self):
        self.assertEqual(
            shadowed_pairs_from_verify_output(FIXTURE_CI_RUN1),
            [("rivet", "/var/lib/runners/runner9/.cargo/bin/rivet")],
        )
        self.assertEqual(
            shadowed_pairs_from_verify_output(FIXTURE_DIFFERENT_PATH_SAME_TOOL),
            [("rivet", "/opt/homebrew/bin/rivet")],
        )


class AllFourRealRunsReplayGreen(unittest.TestCase):
    """The pin REPORTS the already-known, runner-state-driven observation —
    it does not gate on whether it is present. All four real CI runs (three
    shadowed, one clean, four different runners, same commit) must be
    green: presence or absence of the KNOWN hazard is not, by itself,
    new information."""

    def test_run1_shadowed_is_green(self):
        ok, messages = check(FIXTURE_CI_RUN1)
        self.assertTrue(ok, messages)

    def test_run2_shadowed_is_green(self):
        ok, messages = check(FIXTURE_CI_RUN2)
        self.assertTrue(ok, messages)

    def test_run3_shadowed_is_green(self):
        ok, messages = check(FIXTURE_CI_RUN3)
        self.assertTrue(ok, messages)

    def test_run4_clean_is_ALSO_green(self):
        # THE test that would have failed the second design. A clean run on
        # a fourth runner is not "the hazard was fixed" (unfalsifiable from
        # one run) and not "the pin is wrong" — it is exactly what
        # runner-state variance predicts, and must not redden the job.
        ok, messages = check(FIXTURE_CI_RUN4_CLEAN)
        self.assertTrue(ok, messages)

    def test_absence_is_reported_not_silently_dropped(self):
        # Not gated, but not silent either — still worth a human reading
        # the log seeing it was checked and found absent this run.
        ok, messages = check(FIXTURE_CI_RUN4_CLEAN)
        joined = "\n".join(messages)
        self.assertIn("rivet", joined)
        self.assertIn("NOT shadowed", joined)


class GateOnlyOnGenuinelyNewInformation(unittest.TestCase):
    def test_new_unpinned_tools_are_red(self):
        # loom/meld/spar/synth are NOT in KNOWN_OPEN (only rivet is) — this
        # is NOT explained by runner-state variance of the KNOWN hazard, so
        # it must fail, loudly naming each new tool.
        ok, messages = check(FIXTURE_LOCAL_MULTI)
        self.assertFalse(ok)
        joined = "\n".join(messages)
        for tool in ("loom", "meld", "spar", "synth"):
            self.assertIn(tool, joined, f"expected {tool!r} named in: {joined}")
        # rivet IS pinned and matches its known shape, so it must not be
        # reported as a new hazard.
        self.assertNotIn("NEW PATH shadow found, not in KNOWN_OPEN: `rivet`", joined)

    def test_same_tool_different_path_is_red(self):
        ok, messages = check(FIXTURE_DIFFERENT_PATH_SAME_TOOL)
        self.assertFalse(ok)
        joined = "\n".join(messages)
        self.assertIn("DIFFERENT hazard", joined)
        self.assertIn("/opt/homebrew/bin/rivet", joined)

    def test_same_tool_different_path_is_not_conflated_with_new_tool(self):
        ok, messages = check(FIXTURE_DIFFERENT_PATH_SAME_TOOL)
        joined = "\n".join(messages)
        self.assertNotIn("NEW PATH shadow found, not in KNOWN_OPEN: `rivet`", joined)

    def test_malformed_input_is_red_not_silently_green(self):
        ok, messages = check("not varve output at all\n")
        self.assertFalse(ok)


class KnownOpenShape(unittest.TestCase):
    """Shape assumptions IF this table is ever registered with RQ-66-PINDEBT's
    `_pin_table` derivation — NOT done: this hazard is non-deterministic
    runner state, not a reproducible code defect, so it is deliberately
    excluded from `known_open_pins`'s population (see module docstring)."""

    def test_is_a_plain_dict_of_str_to_tuple(self):
        self.assertIsInstance(KNOWN_OPEN, dict)
        for k, v in KNOWN_OPEN.items():
            self.assertIsInstance(k, str)
            self.assertIsInstance(v, tuple)
            self.assertEqual(len(v), 3)  # (issue, note, ambient_path_pattern)

    def test_no_duplicate_keys_by_construction(self):
        self.assertEqual(len(KNOWN_OPEN), len(set(KNOWN_OPEN)))


if __name__ == "__main__":
    unittest.main()
