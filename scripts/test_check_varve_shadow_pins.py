#!/usr/bin/env python3
"""Unit tests for scripts/check_varve_shadow_pins.py (RQ-66-VARVE, #1236).

Fixtures are REAL captured `varve verify` output, not synthesized text:

- FIXTURE_CI_RUN1 / FIXTURE_CI_RUN2: the exact stdout from the two real CI
  runs on pulseengine/synth PR #1244 (`rivet-federated` job), pulled from
  the job logs via `gh api .../logs` — `pulseengine-ci-01-9` and
  `pulseengine-ci-01-12` respectively, both reporting exactly one shadowed
  tool: `rivet`.
- FIXTURE_LOCAL_MULTI: real local `varve verify` output on the authoring
  machine, which (unlike the CI runners) has FIVE ambient tools installed
  via cargo — used as the "a NEW, unpinned tool showed up" case, since the
  pin only carries `rivet`.
- FIXTURE_CLEAN: real `varve verify` output captured locally with PATH
  reduced to `/usr/bin:/bin` (no ambient tools at all) — used as the "the
  pinned hazard was fixed" (resolved) case.

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

FIXTURE_CLEAN = (
    "layer 2026.09.2 sha256:67d585476be898dcd6c7f0e31fb8abe9c6548f708b3cb44804ad61cc5d999025"
    " verified: signature OK, 12 tool(s) match their signed digests\n"
)

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

    def test_local_multi_extracts_all_five(self):
        self.assertEqual(
            shadowed_tools_from_verify_output(FIXTURE_LOCAL_MULTI),
            {"loom", "meld", "rivet", "spar", "synth"},
        )

    def test_clean_extracts_nothing(self):
        self.assertEqual(shadowed_tools_from_verify_output(FIXTURE_CLEAN), set())

    def test_pairs_capture_the_ambient_path_not_just_the_name(self):
        # The whole point of widening the pin past tool-name-only: the path
        # must actually be extractable, not silently dropped.
        self.assertEqual(
            shadowed_pairs_from_verify_output(FIXTURE_CI_RUN1),
            [("rivet", "/var/lib/runners/runner9/.cargo/bin/rivet")],
        )
        self.assertEqual(
            shadowed_pairs_from_verify_output(FIXTURE_DIFFERENT_PATH_SAME_TOOL),
            [("rivet", "/opt/homebrew/bin/rivet")],
        )


class PinTableGreenOnExactMatch(unittest.TestCase):
    """The two REAL CI runs this pin was authored from must both be green."""

    def test_ci_run1_is_green(self):
        ok, messages = check(FIXTURE_CI_RUN1)
        self.assertTrue(ok, messages)
        self.assertIn("rivet", messages[0])

    def test_ci_run2_is_green(self):
        ok, messages = check(FIXTURE_CI_RUN2)
        self.assertTrue(ok, messages)


class PinTableRedOnDrift(unittest.TestCase):
    def test_new_unpinned_tools_are_red(self):
        # loom/meld/spar/synth are NOT in KNOWN_OPEN (only rivet is) — this
        # must fail, loudly naming each new tool.
        ok, messages = check(FIXTURE_LOCAL_MULTI)
        self.assertFalse(ok)
        joined = "\n".join(messages)
        for tool in ("loom", "meld", "spar", "synth"):
            self.assertIn(tool, joined, f"expected {tool!r} named in: {joined}")
        # rivet IS pinned, so it must not be reported as a new hazard.
        self.assertNotIn("NEW PATH shadow found, not in KNOWN_OPEN: `rivet`", joined)

    def test_resolved_pin_is_red_not_silently_accepted(self):
        # A clean verify means the pinned `rivet` shadow is GONE — that is
        # an improvement, and it must still be RED until KNOWN_OPEN is
        # edited, not silently accepted as a win (the #911 / ratchet rule).
        ok, messages = check(FIXTURE_CLEAN)
        self.assertFalse(ok)
        joined = "\n".join(messages)
        self.assertIn("rivet", joined)
        self.assertIn("IMPROVEMENT", joined)

    def test_malformed_input_is_red_not_silently_green(self):
        ok, messages = check("not varve output at all\n")
        self.assertFalse(ok)


class PinTableScopedToPathShapeNotNameAlone(unittest.TestCase):
    """The pin is (tool, ambient-path SHAPE), not tool name alone — a `rivet`
    shadowed via an unrelated path is a DIFFERENT hazard under the same
    name and must be caught, not silently absorbed by the pin."""

    def test_same_tool_different_path_is_red(self):
        ok, messages = check(FIXTURE_DIFFERENT_PATH_SAME_TOOL)
        self.assertFalse(ok)
        joined = "\n".join(messages)
        self.assertIn("DIFFERENT hazard", joined)
        self.assertIn("/opt/homebrew/bin/rivet", joined)

    def test_same_tool_different_path_is_not_reported_as_new_or_resolved(self):
        # It is neither "a brand-new tool name" nor "the pinned hazard
        # vanished" — it needs its OWN distinct message, not a conflation.
        ok, messages = check(FIXTURE_DIFFERENT_PATH_SAME_TOOL)
        joined = "\n".join(messages)
        self.assertNotIn("NEW PATH shadow found, not in KNOWN_OPEN: `rivet`", joined)
        self.assertNotIn("IMPROVEMENT", joined)


class KnownOpenShape(unittest.TestCase):
    """Shape assumptions RQ-66-PINDEBT's `_pin_table` derivation will rely on
    once this table is registered in claims.yaml (#1242, not yet merged as of
    this branch's base — see the module docstring)."""

    def test_is_a_plain_dict_of_str_to_tuple(self):
        self.assertIsInstance(KNOWN_OPEN, dict)
        for k, v in KNOWN_OPEN.items():
            self.assertIsInstance(k, str)
            self.assertIsInstance(v, tuple)
            self.assertEqual(len(v), 3)  # (issue, note, ambient_path_pattern)

    def test_no_duplicate_keys_by_construction(self):
        # A Python dict literal cannot carry a duplicate key at all (the
        # later one silently wins at parse time) — this test exists so a
        # future refactor that builds KNOWN_OPEN programmatically doesn't
        # reintroduce the #1087 duplicate-key class RQ-66-PINDEBT's
        # `_pin_table` refuses outright.
        self.assertEqual(len(KNOWN_OPEN), len(set(KNOWN_OPEN)))


if __name__ == "__main__":
    unittest.main()
