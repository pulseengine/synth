#!/usr/bin/env python3
"""Unit tests for scripts/oracle_wiring_check.py `--floor-base` (RQ-91-EMUFLOOR, #910).

The per-oracle emulation-floor comparison replaced a SUMMED floor pinned in
ci.yml. The pin's one remaining job was to make a shrink cost a visible second
edit; it cost every oracle PR an edit to the same line instead, and it was blind
to a compensating move. These tests are the controls the replacement must pass,
each against a throwaway git repository built from the REAL gate script:

  NEGATIVE (must be red):  a floor shrinks · an oracle is deleted · an oracle is
      unwired (step removed; step removed AND header flipped) · a mode change ·
      a compensating move (-10/+10, which the summed pin could not see) · a
      wrong-number waiver · a stale waiver · a tombstone for a live script · an
      unresolvable base · a base with no wired emulations oracle.
  POSITIVE (must stay green): no change · a raised floor · a new oracle · an
      exact-match waiver · a tombstone · and two PRs, each adding an oracle on
      the same base, merged in EITHER order with no conflict and green after
      each merge — paired with the same two PRs under the old summed pin, which
      conflict on the pinned line.

The fixture repos commit with `commit.gpgsign=false`: they are discarded temp
repositories with no key, never a commit of this project.
"""

import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = pathlib.Path(__file__).resolve().parent
GIT_ID = ["-c", "user.name=fixture", "-c", "user.email=fixture@invalid",
          "-c", "commit.gpgsign=false", "-c", "init.defaultBranch=main"]


def oracle(floor, status="wired", mode="emulations", extra=""):
    if status == "wired":
        st = "# ci-status: wired"
    else:
        st = "# ci-status: unwired — no step runs it yet, kept for later"
    head = f"# ci-checks: {mode} >= {floor}" if mode != "none" else (
        "# ci-checks: none — nothing here can be bound to a count")
    return f"#!/usr/bin/env python3\n{st}\n{head}\n{extra}print('ok')\n"


def workflow(jobs):
    """jobs: {job: [script basenames]} -> ci.yml text, one step per script."""
    out = ["name: CI", "on: [push]", "jobs:"]
    for job, names in jobs.items():
        out += [f"  {job}:", "    runs-on: ubuntu-latest", "    steps:",
                "      - run: echo start"]
        for n in names:
            out.append(f"      - run: python3 scripts/oracle_run.py scripts/repro/{n}")
    return "\n".join(out) + "\n"


class Repo:
    def __init__(self, tc):
        td = tempfile.TemporaryDirectory()
        tc.addCleanup(td.cleanup)
        self.root = pathlib.Path(td.name)
        (self.root / "scripts" / "repro").mkdir(parents=True)
        (self.root / ".github" / "workflows").mkdir(parents=True)
        for f in ("oracle_wiring_check.py", "oracle_run.py"):
            shutil.copy(HERE / f, self.root / "scripts" / f)
        self.git("init", "-q")

    def git(self, *args, check=True):
        r = subprocess.run(["git", *GIT_ID, "-C", str(self.root), *args],
                           capture_output=True, text=True)
        if check and r.returncode != 0:
            raise AssertionError(f"git {args}: {r.stdout}{r.stderr}")
        return r

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)

    def rm(self, rel):
        (self.root / rel).unlink()

    def commit(self, msg="c"):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", msg)
        return self.git("rev-parse", "HEAD").stdout.strip()

    def gate(self, base):
        out = self.root / "summary.json"
        r = subprocess.run(
            [sys.executable, str(self.root / "scripts" / "oracle_wiring_check.py"),
             "--json", str(out), "--floor-base", base],
            capture_output=True, text=True)
        summary = json.loads(out.read_text())["summary"] if out.exists() else {}
        if out.exists():
            out.unlink()
        return r.returncode, r.stdout + r.stderr, summary


def base_repo(tc):
    """Three wired emulations oracles in two jobs, one compiles-mode oracle."""
    r = Repo(tc)
    r.write("scripts/repro/a.py", oracle(100))
    r.write("scripts/repro/b.py", oracle(50))
    r.write("scripts/repro/c.py", oracle(7))
    r.write("scripts/repro/k.py", oracle(3, mode="compiles"))
    r.write(".github/workflows/ci.yml",
            workflow({"ja": ["a.py", "k.py"], "jb": ["b.py", "c.py"]}))
    sha = r.commit("base")
    return r, sha


def set_floor(r, name, old, new):
    p = r.root / "scripts" / "repro" / name
    t = p.read_text()
    needle = f"# ci-checks: emulations >= {old}\n"
    assert t.count(needle) == 1, (name, needle)
    p.write_text(t.replace(needle, f"# ci-checks: emulations >= {new}\n"))


class Negative(unittest.TestCase):
    def assertRed(self, res, needle):
        rc, out, _ = res
        self.assertEqual(rc, 1, out)
        self.assertIn(needle, out)

    def test_floor_shrinks(self):
        r, base = base_repo(self)
        set_floor(r, "b.py", 50, 49)
        self.assertRed(r.gate(base), "b.py: emulation floor SHRANK")

    def test_oracle_deleted_with_its_step(self):
        """The dangling-reference check cannot see this: the step went too."""
        r, base = base_repo(self)
        r.rm("scripts/repro/c.py")
        r.write(".github/workflows/ci.yml",
                workflow({"ja": ["a.py", "k.py"], "jb": ["b.py"]}))
        self.assertRed(r.gate(base), "c.py: emulation floor SHRANK")

    def test_unwired_step_removed(self):
        r, base = base_repo(self)
        r.write(".github/workflows/ci.yml",
                workflow({"ja": ["a.py", "k.py"], "jb": ["b.py"]}))
        self.assertRed(r.gate(base), "c.py: declares `wired` but NO workflow STEP runs it")

    def test_unwired_step_removed_and_header_flipped(self):
        r, base = base_repo(self)
        r.write("scripts/repro/c.py", oracle(7, status="unwired"))
        r.write(".github/workflows/ci.yml",
                workflow({"ja": ["a.py", "k.py"], "jb": ["b.py"]}))
        self.assertRed(r.gate(base), "c.py: emulation floor SHRANK")

    def test_mode_change(self):
        r, base = base_repo(self)
        r.write("scripts/repro/a.py", oracle(100, mode="compiles"))
        self.assertRed(r.gate(base), "a.py: emulation floor SHRANK")

    def test_compensating_move_is_red_where_the_sum_was_blind(self):
        """-10 on one oracle, +10 on another. The summed total is UNCHANGED —
        the quantity the retired `--exact-emulation-floor` pin compared — and
        the per-oracle gate is red. Measured on the real tree too: rc 0 under
        the pin on eab66646, red under `--floor-base eab66646`."""
        r, base = base_repo(self)
        _, _, before = r.gate(base)
        set_floor(r, "a.py", 100, 90)
        set_floor(r, "b.py", 50, 60)
        rc, out, after = r.gate(base)
        self.assertEqual(before["emulation_floor"], after["emulation_floor"],
                         "the paired half: the sum must be unchanged")
        self.assertRed((rc, out, after), "a.py: emulation floor SHRANK")

    def test_wrong_number_waiver(self):
        r, base = base_repo(self)
        set_floor(r, "b.py", 50, 40)
        t = (r.root / "scripts/repro/b.py").read_text().replace(
            "print", "# ci-checks-shrink: emulations 50 -> 45 — a leg is retired by #1\nprint")
        r.write("scripts/repro/b.py", t)
        rc, out, _ = r.gate(base)
        self.assertEqual(rc, 1, out)
        self.assertIn("STALE", out)
        self.assertIn("b.py: emulation floor SHRANK", out)

    def test_stale_waiver_after_the_floor_moves_again(self):
        r, _ = base_repo(self)
        set_floor(r, "b.py", 50, 40)
        t = (r.root / "scripts/repro/b.py").read_text().replace(
            "print", "# ci-checks-shrink: emulations 50 -> 40 — a leg is retired by #1\nprint")
        r.write("scripts/repro/b.py", t)
        waived = r.commit("shrink, waived")
        set_floor(r, "b.py", 40, 44)
        self.assertRed(r.gate(waived), "b.py: STALE `ci-checks-shrink")

    def test_short_reason_waiver(self):
        r, base = base_repo(self)
        set_floor(r, "b.py", 50, 40)
        t = (r.root / "scripts/repro/b.py").read_text().replace(
            "print", "# ci-checks-shrink: emulations 50 -> 40 — tbd\nprint")
        r.write("scripts/repro/b.py", t)
        self.assertRed(r.gate(base), "needs a REAL reason")

    def test_tombstone_for_a_live_script(self):
        r, base = base_repo(self)
        r.write("scripts/repro/retired/c.py.retired",
                "# ci-checks-shrink: emulations 7 -> 0 — superseded by a.py's leg\n")
        self.assertRed(r.gate(base), "tombstone for scripts/repro/c.py, which EXISTS")

    def test_unresolvable_base(self):
        r, _ = base_repo(self)
        self.assertRed(r.gate("0" * 40), "cannot resolve")

    def test_base_with_no_wired_emulations_oracle(self):
        """An empty base would make every oracle an addition: vacuous green."""
        r = Repo(self)
        r.write("scripts/repro/k.py", oracle(3, mode="compiles"))
        r.write(".github/workflows/ci.yml", workflow({"ja": ["k.py"]}))
        base = r.commit("base")
        r.write("scripts/repro/a.py", oracle(100))
        r.write(".github/workflows/ci.yml", workflow({"ja": ["k.py", "a.py"]}))
        self.assertRed(r.gate(base), "VACUOUS")


class Positive(unittest.TestCase):
    def assertGreen(self, res):
        rc, out, _ = res
        self.assertEqual(rc, 0, out)

    def test_no_change(self):
        r, base = base_repo(self)
        rc, out, s = r.gate(base)
        self.assertEqual(rc, 0, out)
        self.assertEqual(s["floor_base_compared"], 3)
        self.assertEqual((s["floor_base_raised"], s["floor_base_waived"],
                          s["floor_base_added"]), (0, 0, 0))
        self.assertEqual(s["emulation_floor"], 157)

    def test_raised_floor_needs_no_other_edit(self):
        r, base = base_repo(self)
        set_floor(r, "c.py", 7, 9)
        rc, out, s = r.gate(base)
        self.assertEqual(rc, 0, out)
        self.assertEqual(s["floor_base_raised"], 1)

    def test_exact_waiver(self):
        r, base = base_repo(self)
        set_floor(r, "b.py", 50, 40)
        t = (r.root / "scripts/repro/b.py").read_text().replace(
            "print", "# ci-checks-shrink: emulations 50 -> 40 — a leg is retired by #1\nprint")
        r.write("scripts/repro/b.py", t)
        rc, out, s = r.gate(base)
        self.assertEqual(rc, 0, out)
        self.assertEqual(s["floor_base_waived"], 1)
        # ... and once merged, the waiver is history: still green against
        # the waived commit while the floor stays where it names.
        waived = r.commit("shrink, waived")
        self.assertGreen(r.gate(waived))

    def test_unwire_with_waiver(self):
        r, base = base_repo(self)
        r.write("scripts/repro/c.py", oracle(7, status="unwired", extra=(
            "# ci-checks-shrink: emulations 7 -> 0 — its toolchain left CI\n")))
        r.write(".github/workflows/ci.yml",
                workflow({"ja": ["a.py", "k.py"], "jb": ["b.py"]}))
        self.assertGreen(r.gate(base))

    def test_deletion_with_tombstone(self):
        r, base = base_repo(self)
        r.rm("scripts/repro/c.py")
        r.write("scripts/repro/retired/c.py.retired",
                "# ci-checks-shrink: emulations 7 -> 0 — superseded by a.py's leg\n")
        r.write(".github/workflows/ci.yml",
                workflow({"ja": ["a.py", "k.py"], "jb": ["b.py"]}))
        rc, out, s = r.gate(base)
        self.assertEqual(rc, 0, out)
        self.assertEqual(s["floor_base_waived"], 1)


class MeasuredBelowDeclared(unittest.TestCase):
    """The fourth negative control. This half was never the floor pin's job:
    scripts/oracle_run.py fails the STEP when an oracle executes less than it
    declares, and scripts/oracle_evidence.py fails the JOB on any below-floor
    record. Shown here so retiring the pin is seen not to touch it."""

    def test_oracle_run_reds_an_oracle_that_emulates_less_than_it_declares(self):
        td = tempfile.TemporaryDirectory()
        self.addCleanup(td.cleanup)
        o = pathlib.Path(td.name) / "lazy.py"
        o.write_text(oracle(5))  # declares emulations >= 5, emulates nothing
        r = subprocess.run([sys.executable, str(HERE / "oracle_run.py"), str(o)],
                           capture_output=True, text=True, cwd=td.name,
                           env=dict(os.environ, ORACLE_EVIDENCE_JSONL=str(
                               pathlib.Path(td.name) / "ledger.jsonl")))
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("VACUOUS", r.stderr)
        self.assertIn("measured 0", r.stderr)
        ev = subprocess.run([sys.executable, str(HERE / "oracle_evidence.py"),
                             str(pathlib.Path(td.name) / "ledger.jsonl"),
                             "--min-oracles", "1"],
                            capture_output=True, text=True)
        self.assertEqual(ev.returncode, 1, ev.stdout + ev.stderr)
        self.assertIn("below floor", ev.stderr)


class TwoPRs(unittest.TestCase):
    """The done-when's positive control: two oracle PRs in one window."""

    def _branches(self, r, base, pinned=False):
        def pin(total):
            if pinned:
                r.write("scripts/floor.txt", f"--exact-emulation-floor {total}\n")
        pin(157)
        if pinned:
            base = r.commit("pin")
        r.git("checkout", "-q", "-b", "pr-x", base)
        r.write("scripts/repro/x.py", oracle(11))
        r.write(".github/workflows/ci.yml",
                workflow({"ja": ["a.py", "k.py", "x.py"], "jb": ["b.py", "c.py"]}))
        pin(168)
        r.commit("add x")
        r.git("checkout", "-q", "-b", "pr-y", base)
        r.write("scripts/repro/y.py", oracle(13))
        r.write(".github/workflows/ci.yml",
                workflow({"ja": ["a.py", "k.py"], "jb": ["b.py", "c.py", "y.py"]}))
        pin(170)
        r.commit("add y")
        return base

    def test_two_oracle_prs_merge_in_either_order_green_after_each(self):
        r, base = base_repo(self)
        self._branches(r, base)
        for pr in ("pr-x", "pr-y"):
            r.git("checkout", "-q", pr)
            self.assertEqual(r.gate(base)[0], 0, f"{pr} against its base")
        trees = []
        for first, second in (("pr-x", "pr-y"), ("pr-y", "pr-x")):
            r.git("checkout", "-q", "-B", f"main-{first}", base)
            for pr in (first, second):
                m = r.git("merge", "-q", "--no-ff", "--no-edit", pr, check=False)
                self.assertEqual(m.returncode, 0, f"{first} then {second}: "
                                 f"{pr} did not merge cleanly: {m.stdout}{m.stderr}")
                rc, out, s = r.gate("HEAD^1")
                self.assertEqual(rc, 0, f"after merging {pr}: {out}")
            self.assertEqual(s["emulation_floor"], 157 + 11 + 13)
            self.assertEqual(s["floor_base_added"], 1)
            trees.append(r.git("rev-parse", "HEAD^{tree}").stdout.strip())
        self.assertEqual(trees[0], trees[1], "both orders reach the same tree")

    def test_paired_the_same_two_prs_conflict_under_a_summed_pin(self):
        r, base = base_repo(self)
        base = self._branches(r, base, pinned=True)
        r.git("checkout", "-q", "-B", "main-pinned", base)
        self.assertEqual(r.git("merge", "-q", "--no-edit", "pr-x", check=False).returncode, 0)
        m = r.git("merge", "-q", "--no-edit", "pr-y", check=False)
        self.assertNotEqual(m.returncode, 0, "the pinned line must conflict")
        self.assertIn("scripts/floor.txt", r.git("diff", "--name-only",
                                                 "--diff-filter=U").stdout)
        r.git("merge", "--abort")


if __name__ == "__main__":
    unittest.main()
