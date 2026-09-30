#!/usr/bin/env python3
"""Unit tests for scripts/oracle_run.py.

RQ-77-STDERR (#1419). This driver runs **206 oracles** in CI and had NO tests at
all, and was not wired into `ci.yml`. The specific defect it shipped with: an
oracle that refuses via `sys.exit("REFUSE: ...")` had its REASON discarded.

WHY THE REASON WAS LOST, stated exactly, because the issue first named the wrong
subject. `oracle_run` runs oracles **in-process** via `runpy` — there is no
subprocess and no stderr redirection anywhere in the file, so "it discards
stderr" was wrong and fixing that would have changed nothing. What happened is
that `sys.exit(str)` puts the STRING in `SystemExit.code`, and the handler
coerced a non-int to `1` without printing it. Under a plain interpreter CPython
prints a non-int exit code itself; here the driver catches `SystemExit` first, so
it never gets the chance.

The exit code always propagated, so this was never a false pass. What CI lost was
"why", which the oracle had already computed — the log showed only
"VACUOUS ... measured 0".

DERIVED, not asserted: 188 of the 206 oracles this driver runs refuse via
`sys.exit(<non-int>)`. The count is reproducible with an `ast` walk over the
`scripts/repro/*.py` paths that appear after `oracle_run.py` in `ci.yml`, JOINING
`\`-continuation lines first — 18 invocations use them, and reading only same-line
paths gives a narrower 170 of 188, which is what this file published until v0.77's
round-1 cold review caught it. A plain grep for `sys.exit(` over `scripts/**/*.py`
gives 244 files / 660 sites, a true count of the WRONG population — most of those
scripts never run under this driver. Both distinctions are the v0.77 theme applied
to this file's own numbers.

WHAT THESE SEVEN TESTS DO AND DO NOT PROVE, stated because the docstring used to
present them all as the red-first case. FOUR of them — the int exit code, the
clean exit, `sys.exit()` with no argument, and falling off the end — assert
`assertNotIn("ORACLE-REFUSED", out)`, which is trivially satisfied when the
feature is ABSENT: run against the parent commit they PASS. They are legitimate
no-false-positive guards, and they are not evidence of the fix. THREE discriminate:
the two that assert the reason reaches the captured buffer, and the cwd/argv one.

Run: python3 scripts/test_oracle_run.py
"""
import importlib.util
import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
_spec = importlib.util.spec_from_file_location(
    "oracle_run", ROOT / "scripts/oracle_run.py")
orun = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(orun)


class RefusalReasonReachesTheLog(unittest.TestCase):
    """The red-first case: a string exit code must be PRINTED, not just coerced."""

    def _script(self, body):
        d = tempfile.mkdtemp()
        p = pathlib.Path(d) / "probe_oracle.py"
        p.write_text(body)
        return str(p)

    def test_a_string_exit_code_is_printed_into_the_captured_output(self):
        # RED before the fix: `out` held only "working" and the reason vanished.
        s = self._script(
            "import sys\n"
            "print('working')\n"
            "sys.exit('REFUSE: parsed to ZERO anchors — this check would be vacuous')\n")
        code, _counters, out = orun.run_oracle(s, [])
        self.assertEqual(code, 1, "a string exit code must still mean failure")
        self.assertIn("REFUSE: parsed to ZERO anchors", out,
                      "RQ-77-STDERR: the refusal REASON must reach the captured "
                      "output, not only the exit code")
        self.assertIn("ORACLE-REFUSED", out)
        self.assertIn("probe_oracle.py", out,
                      "the message must name WHICH oracle refused")

    def test_the_reason_is_in_the_CAPTURED_buffer_not_merely_the_terminal(self):
        # `evaluate()` and the JSON record both read the returned string, so a
        # message printed after stdout is restored would be invisible to them
        # while still looking right in a terminal. Assert on the return value.
        s = self._script("import sys\nsys.exit('REFUSE: distinctive-marker-42')\n")
        _code, _counters, out = orun.run_oracle(s, [])
        self.assertIn("distinctive-marker-42", out)

    def test_an_integer_exit_code_is_unchanged_and_prints_nothing_extra(self):
        s = self._script("import sys\nprint('ran')\nsys.exit(3)\n")
        code, _counters, out = orun.run_oracle(s, [])
        self.assertEqual(code, 3)
        self.assertNotIn("ORACLE-REFUSED", out,
                        "an int exit code is not a refusal message")

    def test_a_clean_exit_is_unchanged(self):
        s = self._script("print('all good')\n")
        code, _counters, out = orun.run_oracle(s, [])
        self.assertEqual(code, 0)
        self.assertIn("all good", out)
        self.assertNotIn("ORACLE-REFUSED", out)

    def test_sys_exit_None_is_success_and_prints_nothing_extra(self):
        # `sys.exit()` with no argument is exit 0 — it must not be mistaken for
        # a refusal just because it is not an int.
        s = self._script("import sys\nprint('done')\nsys.exit()\n")
        code, _counters, out = orun.run_oracle(s, [])
        self.assertEqual(code, 0)
        self.assertNotIn("ORACLE-REFUSED", out)

    def test_a_nonzero_exit_via_falling_off_the_end_is_success(self):
        s = self._script("x = 1 + 1\n")
        code, _counters, _out = orun.run_oracle(s, [])
        self.assertEqual(code, 0)


class DriverRestoresInterpreterState(unittest.TestCase):
    """Guarding what the file's own comments say it had to learn the hard way."""

    def _script(self, body):
        d = tempfile.mkdtemp()
        p = pathlib.Path(d) / "probe_state.py"
        p.write_text(body)
        return str(p)

    def test_cwd_argv_and_path_survive_a_chdiring_oracle_that_refuses(self):
        import os
        before_cwd, before_argv, before_path = os.getcwd(), sys.argv[:], sys.path[:]
        s = self._script(
            "import os, sys, tempfile\n"
            "os.chdir(tempfile.mkdtemp())\n"
            "sys.argv.append('mutated')\n"
            "sys.exit('REFUSE: after moving the cwd')\n")
        code, _c, out = orun.run_oracle(s, [])
        self.assertEqual(code, 1)
        self.assertIn("REFUSE: after moving the cwd", out)
        self.assertEqual(os.getcwd(), before_cwd, "cwd must be restored")
        self.assertEqual(sys.argv, before_argv, "argv must be restored")
        self.assertEqual(sys.path, before_path, "sys.path must be restored")


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], "-v"])
