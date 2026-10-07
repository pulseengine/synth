#!/usr/bin/env python3
"""Tests for scripts/check_version_pins.py — RQ-81-PINSWEEP (#1457).

THIS GATE IS REQUIRED AT EVERY MERGE AND HAD NO TEST. It is 194 lines of
hand-rolled parsing standing between a desynced pin and a tag, with two
recorded incidents behind it (#145 sank the v0.7.0 tag; #924 found a
Cargo.lock holding ZERO entries at the new version AFTER a bump), and
nothing ever showed it could fail.

The two blind spots below were MEASURED on the v0.80 tree with paired
controls before this file existed, and both are LATENT there rather than
live — which is exactly when they are cheap to close:

  inline `{ path = "..", version = ".." }` left stale  -> rc=1  (seen)
  [dependencies.X] block form left stale               -> rc=0  (BLIND)
  `members` on ONE line + every lock entry wrong       -> rc=0  (BLIND)
  the SAME lock damage with `members` multi-line       -> rc=1  (so the
      lock check works and the members parse is what disables it)

A derived population of zero is a refusal, not a pass: with `members`
unparseable the member list is empty and `check_cargo_lock` iterates
nothing, so the gate prints OK over a wholly stale lockfile.
"""
import os
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
GATE = HERE / "check_version_pins.py"

WS = """\
[workspace]
members = [
    "crates/alpha",
    "crates/beta",
]

[workspace.package]
version = "{ver}"
"""

LOCK = """\
version = 4

[[package]]
name = "alpha"
version = "{alpha}"

[[package]]
name = "beta"
version = "{beta}"
"""

MODULE_BAZEL = 'module(\n    name = "t",\n    version = "{ver}",\n)\n'
NPM = '{{\n  "name": "@t/t",\n  "version": "{ver}"\n}}\n'


def tree(root, *, ws=None, lock=None, alpha_dep=None, module=None, npm=None, ver="0.80.0"):
    """A minimal workspace the gate can run against. Every surface defaults to
    CONSISTENT, so a single argument isolates one blind spot at a time."""
    root = Path(root)
    (root / "scripts").mkdir(parents=True, exist_ok=True)
    (root / "scripts" / "check_version_pins.py").write_text(GATE.read_text())
    (root / "Cargo.toml").write_text(ws if ws is not None else WS.format(ver=ver))
    (root / "Cargo.lock").write_text(
        lock if lock is not None else LOCK.format(alpha=ver, beta=ver))
    (root / "MODULE.bazel").write_text((module or MODULE_BAZEL).format(ver=ver))
    (root / "npm").mkdir(exist_ok=True)
    (root / "npm" / "package.json").write_text((npm or NPM).format(ver=ver))
    for name in ("alpha", "beta"):
        d = root / "crates" / name
        d.mkdir(parents=True, exist_ok=True)
        if name == "alpha" and alpha_dep is not None:
            body = alpha_dep
        else:
            body = '[dependencies]\nbeta = { path = "../beta", version = "%s" }\n' % ver
        d.joinpath("Cargo.toml").write_text(
            f'[package]\nname = "{name}"\n\n' + (body if name == "alpha" else ""))
    return root


def run(root):
    r = subprocess.run([sys.executable, "scripts/check_version_pins.py"],
                       cwd=root, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


class PositiveControls(unittest.TestCase):
    """The harness must be able to produce a GREEN and a RED, or nothing it
    reports about the blind spots means anything."""

    def test_a_consistent_tree_is_green(self):
        with tempfile.TemporaryDirectory() as d:
            rc, out = run(tree(d))
            self.assertEqual(rc, 0, out)

    def test_a_stale_INLINE_pin_is_caught(self):
        with tempfile.TemporaryDirectory() as d:
            root = tree(d, alpha_dep='[dependencies]\nbeta = { path = "../beta", version = "0.79.0" }\n')
            rc, out = run(root)
            self.assertEqual(rc, 1, out)
            self.assertIn("0.79.0", out)


class BlindSpotSplitLinePin(unittest.TestCase):
    """#1457 blind spot 1: the gate requires `path` and `version` on ONE line."""

    def test_a_stale_block_form_pin_is_caught(self):
        with tempfile.TemporaryDirectory() as d:
            root = tree(d, alpha_dep=textwrap.dedent('''\
                [dependencies.beta]
                path = "../beta"
                version = "0.79.0"
                '''))
            rc, out = run(root)
            self.assertEqual(
                rc, 1,
                "a [dependencies.X] block pinned at the OLD version must red; "
                "the line-based scan cannot see it and prints OK:\n" + out)


class BlindSpotSingleLineMembers(unittest.TestCase):
    """#1457 blind spot 2: `members` on one line yields ZERO members, so
    check_cargo_lock iterates nothing and a wholly stale lock passes."""

    ONE_LINE_WS = (
        '[workspace]\nmembers = ["crates/alpha", "crates/beta"]\n\n'
        '[workspace.package]\nversion = "0.80.0"\n'
    )

    def test_single_line_members_still_sees_a_stale_lock(self):
        with tempfile.TemporaryDirectory() as d:
            root = tree(d, ws=self.ONE_LINE_WS,
                        lock=LOCK.format(alpha="0.1.0", beta="0.1.0"))
            rc, out = run(root)
            self.assertEqual(
                rc, 1,
                "every workspace member locked at 0.1.0 must red even when "
                "`members` is written on one line — a derived population of "
                "zero is a refusal, not a pass:\n" + out)

    def test_the_same_lock_damage_reds_with_multi_line_members(self):
        """The paired control: this is what proves the LOCK check works and the
        MEMBERS parse is what disables it."""
        with tempfile.TemporaryDirectory() as d:
            root = tree(d, lock=LOCK.format(alpha="0.1.0", beta="0.1.0"))
            rc, out = run(root)
            self.assertEqual(rc, 1, out)

    def test_an_empty_member_set_is_refused(self):
        with tempfile.TemporaryDirectory() as d:
            root = tree(d, ws='[workspace]\nmembers = []\n\n'
                               '[workspace.package]\nversion = "0.80.0"\n')
            rc, out = run(root)
            self.assertEqual(
                rc, 1,
                "zero members means the lock half asserts NOTHING; the gate "
                "must refuse rather than print OK:\n" + out)


if __name__ == "__main__":
    unittest.main(verbosity=2)
