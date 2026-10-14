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
import os
import re
import subprocess
import sys
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


class Refusals(unittest.TestCase):
    """The two refusals the artifact calls 'demonstrated live'.

    Demonstrated once, by hand, is not pinned: both live in `main()` behind a
    subprocess call to rivet, which is precisely why neither had a test. A
    refusal nothing exercises is the same shape as the gates this release
    measured and fixed — it works until the day it silently does not.

    Both tests drive the REAL `main()` in a subprocess against a FAKE rivet and
    a throwaway git repo, so they depend on no tag, no network, and no
    `fetch-depth` setting in whatever CI job runs them.
    """

    def _fake_rivet(self, td: Path, version: str, diff_json: str) -> Path:
        fake = td / "fake-rivet"
        fake.write_text(
            "#!/bin/sh\n"
            'if [ "$1" = "--version" ]; then echo "rivet %s"; exit 0; fi\n'
            'if [ "$1" = "diff" ]; then\n'
            '  for a in "$@"; do if [ "$a" = "json" ]; then printf \'%s\'; exit 0; fi; done\n'
            "  exit 0\n"
            "fi\n"
            "exit 0\n" % (version, diff_json)
        )
        fake.chmod(0o755)
        return fake

    def _repo(self, td: Path) -> Path:
        """A minimal repo with a tag, so `git archive` succeeds on its own."""
        root = td / "repo"
        (root / "artifacts").mkdir(parents=True)
        (root / "artifacts" / "x.yaml").write_text("artifacts: []\n")
        (root / "rivet.yaml").write_text("sources:\n  - path: artifacts\n")
        # Fixture-local config only: this repo is created and destroyed inside
        # the test. It is not a synth commit and never leaves the temp dir.
        #
        # The ambient config is neutralised WHOLESALE, not one setting at a
        # time. Handling `commit.gpgsign` alone left `core.hooksPath` and
        # `init.templateDir` inherited, so a developer whose global config
        # points at a hooks framework with a failing `pre-commit` gets three
        # spurious errors here — a red that is about their machine, not about
        # the generator. Loud rather than silent, but still wrong.
        env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t",
                   GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t",
                   GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_SYSTEM=os.devnull,
                   GIT_CONFIG_NOSYSTEM="1")
        for cmd in (["init", "-q", "-b", "main"], ["add", "-A"],
                    ["-c", "commit.gpgsign=false", "commit", "-qm", "base"],
                    ["tag", "v0.0.1"]):
            subprocess.run(["git", *cmd], cwd=root, check=True, env=env,
                           capture_output=True)
        return root

    def _run(self, root: Path, rivet: Path) -> subprocess.CompletedProcess:
        return subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "release_notes_from_rivet.py"),
             "--base", "v0.0.1", "--root", str(root), "--rivet", str(rivet)],
            capture_output=True, text=True,
        )

    def _recording_rivet(self, td: Path, version: str, diff_json: str) -> tuple[Path, Path]:
        """A fake rivet that RECORDS the --head it was given, and that head's
        contents, at call time.

        Recorded at call time on purpose: the generator builds its extracts in a
        TemporaryDirectory, so by the time a test could look the directory is
        gone. A test that inspected it afterwards would pass vacuously.
        """
        log = td / "rivet-head.log"
        fake = td / "recording-rivet"
        fake.write_text(
            "#!/bin/sh\n"
            'if [ "$1" = "--version" ]; then echo "rivet %s"; exit 0; fi\n'
            'if [ "$1" = "diff" ]; then\n'
            "  h=''\n"
            '  while [ $# -gt 0 ]; do\n'
            '    if [ "$1" = "--head" ]; then h="$2"; fi\n'
            "    shift\n"
            "  done\n"
            '  { echo "HEAD=$h"; (cd "$h" 2>/dev/null && find . -maxdepth 2 | sort); } >> %s\n'
            "  printf '%s'\n"
            "  exit 0\n"
            "fi\n"
            "exit 0\n" % (version, log, diff_json)
        )
        fake.chmod(0o755)
        return fake, log

    def test_the_head_extract_is_bounded_like_the_base(self):
        """RQ-86-NOTESPOP3 (#1259): the HEAD side must be bounded to the source
        roots, exactly as the base side is -- and that is what makes the
        anti-vacuity guard reachable.

        THE DEFECT THIS PINS, measured before the fix: the base is a
        `git archive` of the configured source roots, so it can never contain
        `.rivet/repos/` -- the federated sibling checkouts. Diffing it against
        the whole working tree reported every FOREIGN artifact as "added": 3219
        added against v0.85.0 where only 18 were this repo's. With `--base HEAD`,
        where NOTHING of this repo's own is added, the synced checkout still
        reported 3201 added and exited 0; the same breakage in a checkout without
        the cache exited 1. The guard was potent ONLY where the generator never
        runs.

        So this asserts the property rather than the count: the path handed to
        `rivet diff --head` is NOT the repo root, and what it contains is the
        source roots WITHOUT the sibling cache.
        """
        with tempfile.TemporaryDirectory() as d:
            td = Path(d)
            fake, log = self._recording_rivet(
                td, "0.37.0", '{"added": ["RQ-86-X"], "removed": []}'
            )
            root = self._repo(td)
            # a FOREIGN artifact, outside the configured source roots -- the
            # shape `.rivet/repos/<sibling>` takes in a synced checkout
            foreign = root / ".rivet" / "repos" / "sibling" / "artifacts"
            foreign.mkdir(parents=True)
            (foreign / "f.yaml").write_text("artifacts: []\n")

            r = self._run(root, fake)
            self.assertEqual(r.returncode, 0, r.stderr)
            recorded = log.read_text()
            self.assertIn("HEAD=", recorded, "the fake was never asked to diff")

            heads = [l[5:] for l in recorded.splitlines() if l.startswith("HEAD=")]
            self.assertTrue(heads, "no --head was passed")
            for h in heads:
                self.assertNotEqual(
                    Path(h).resolve(), root.resolve(),
                    "the head side is the RAW REPO ROOT -- the sibling cache is "
                    "back in the diff and the guard is unreachable again",
                )
            self.assertIn("./artifacts", recorded, "the source roots must be present")
            self.assertNotIn(
                "./.rivet", recorded,
                "the sibling cache reached the head extract -- foreign artifacts "
                "will read as 'added' and the anti-vacuity guard goes inert",
            )

    def test_a_rivet_older_than_the_pin_is_refused(self):
        """0.36.0 < the 0.37.0 pin must REFUSE, and say why an old rivet lies.

        The fake reports a NON-EMPTY diff on purpose. With `"{}"` the process
        still exits non-zero when the version refusal is removed — via the
        zero-added refusal — so the returncode assertion carried no weight and
        all the potency sat in the message. A non-empty diff makes both
        assertions load-bearing: without the version check this run would
        SUCCEED.
        """
        with tempfile.TemporaryDirectory() as d:
            td = Path(d)
            fake = self._fake_rivet(td, "0.36.0", '{"added": ["RQ-70-X"], "removed": []}')
            r = self._run(self._repo(td), fake)
            self.assertNotEqual(r.returncode, 0, "a stale rivet must be refused")
            self.assertIn("older than the CI pin", r.stderr)

    def test_zero_added_artifacts_is_refused_as_a_broken_derivation(self):
        """An empty diff is a broken derivation, never a quiet release."""
        with tempfile.TemporaryDirectory() as d:
            td = Path(d)
            fake = self._fake_rivet(td, "0.37.0", '{"added": [], "removed": []}')
            r = self._run(self._repo(td), fake)
            self.assertNotEqual(r.returncode, 0, "zero added must be refused")
            self.assertIn("ZERO added artifacts", r.stderr)

    def test_the_fake_rivet_lets_a_NON_empty_diff_through(self):
        """Negative control: the two refusals above must be the REFUSALS firing,

        not the harness failing to reach them. Same fixture, same fake rivet,
        one added artifact — the generator must now exit 0.
        """
        with tempfile.TemporaryDirectory() as d:
            td = Path(d)
            fake = self._fake_rivet(td, "0.37.0", '{"added": ["RQ-70-X"], "removed": []}')
            r = self._run(self._repo(td), fake)
            self.assertEqual(r.returncode, 0, f"harness cannot reach main(): {r.stderr[:400]}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
