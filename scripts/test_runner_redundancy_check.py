#!/usr/bin/env python3
"""Potency tests for runner_redundancy_check.py (RQ-62-CLAIMCHECK, #1062).

WHY THIS FILE EXISTS. Six releases running found the defect in checking
machinery, not the checked code, and this checker guards a terminal failure
mode: on 2026-09-02 a single-runner `light` pool went offline and NOTHING IN
THE REPO COULD MERGE (two required contexts assigned to a dead machine, 600s,
zero steps executed). The gate must therefore be provably able to go red.
Precedent: test_claim_check.py, test_status_evidence_check.py.

Every fixture below replays the invariant against a synthetic workflow +
runner inventory, including the ways the gate could go INERT:
  * the 2026-09-02 instance itself — one-runner pool, and the same pool with
    its lone runner offline (0 online: idle and unavailable must both refuse);
  * 2 registered / 1 online (status matters, not registration);
  * a renamed required job (the deadlock class — context never reports);
  * an EMPTY runner inventory (an API error must not read as healthy);
  * zero self-hosted contexts examined below the floor (parse-drift vacuity);
  * case-insensitive label matching (runner labels are `Linux`/`X64`,
    runs-on is lowercase — a case-sensitive compare would refuse EVERY pool
    or, worse, a substring compare could accept the wrong one);
  * green control — the gate must also PASS, because a gate that blocks
    everything is as useless as one that blocks nothing.

Stdlib `unittest` only; runs in CI without any token (fixture mode).

    python3 scripts/test_runner_redundancy_check.py    (wired in the Claim Check CI job)
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = pathlib.Path(__file__).resolve().parent
SCRIPT = SCRIPTS / "runner_redundancy_check.py"

# `on:` is load-bearing since v0.90: resolution is ci_pool_tripwire's, which
# refuses a context whose workflow does not run on `pull_request`.
WORKFLOW_TWO_REQUIRED = """
name: CI
on: [push, pull_request]
jobs:
  fmt:
    name: Format
    runs-on: [self-hosted, linux, x64, light]
    steps: [{run: "true"}]
  clip:
    name: Clippy
    runs-on: [self-hosted, linux, x64, rust-cpu]
    steps: [{run: "true"}]
  test:
    name: Test
    runs-on: ubuntu-latest
    steps: [{run: "true"}]
  z3:
    name: Z3 Verification
    runs-on: ubuntu-latest
    steps: [{run: "true"}]
  cc:
    name: Claim Check
    runs-on: ubuntu-latest
    steps: [{run: "true"}]
  vps:
    name: Version Pin Sweep
    runs-on: [self-hosted, linux, x64, light]
    steps: [{run: "true"}]
  bazel:
    name: Bazel Build & Proofs
    runs-on: ubuntu-latest
    steps: [{run: "true"}]
  kani:
    name: Kani Verification
    runs-on: ubuntu-latest
    steps: [{run: "true"}]
  rivet:
    name: Rivet Validation
    runs-on: [self-hosted, linux, x64, rust-cpu]
    steps: [{run: "true"}]
"""

# v0.90 (RQ-90-SPECEXEC, #1636): the tenth required context lives in a SECOND
# workflow file, as it does in the repo (spec-suite.yml).
WORKFLOW_SPEC = """
name: Spec Suite
on:
  push:
    branches: [main]
  pull_request:
    branches: [main]
jobs:
  spec-suite-execution:
    name: spec-suite execution (#1636)
    runs-on: ubuntu-latest
    steps: [{run: "true"}]
"""


def write_workflows(td: str, ci_text: str, spec_text: str | None = WORKFLOW_SPEC):
    """The --workflow arguments for a ci.yml (+ optional spec-suite.yml)."""
    wf = pathlib.Path(td) / "ci.yml"
    wf.write_text(ci_text)
    args = ["--workflow", str(wf)]
    if spec_text is not None:
        sp = pathlib.Path(td) / "spec-suite.yml"
        sp.write_text(spec_text)
        args += ["--workflow", str(sp)]
    return args


def runner(name: str, status: str, labels: list[str]) -> dict:
    return {"name": name, "status": status, "busy": False,
            "labels": [{"name": l} for l in labels]}


# Runner labels use GitHub's real capitalisation on purpose — the matcher
# must be case-insensitive like GitHub's own.
LABELS_LIGHT = ["self-hosted", "Linux", "X64", "hetzner", "light"]
LABELS_RUST = ["self-hosted", "Linux", "X64", "hetzner", "rust-cpu"]

HEALTHY_FLEET = [
    runner("l1", "online", LABELS_LIGHT),
    runner("l2", "online", LABELS_LIGHT),
    runner("r1", "online", LABELS_RUST),
    runner("r2", "online", LABELS_RUST),
]


class RedundancyGate(unittest.TestCase):
    def run_gate(self, workflow: str, runners: list[dict],
                 extra: list[str] | None = None):
        with tempfile.TemporaryDirectory() as td:
            wfargs = write_workflows(td, workflow)
            rj = pathlib.Path(td) / "runners.json"
            rj.write_text(json.dumps({"runners": runners}))
            return subprocess.run(
                [sys.executable, str(SCRIPT)] + wfargs
                + ["--runners-json", str(rj)] + (extra or []),
                capture_output=True, text=True,
            )

    def test_green_control(self):
        p = self.run_gate(WORKFLOW_TWO_REQUIRED, HEALTHY_FLEET)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("0 failures", p.stdout)

    def test_2026_09_02_single_runner_pool_refused(self):
        # The incident shape at rest: `light` satisfiable by exactly one
        # ONLINE runner. Idle. The gate must refuse anyway.
        fleet = [
            runner("light-only", "online", LABELS_LIGHT),
            runner("r1", "online", LABELS_RUST),
            runner("r2", "online", LABELS_RUST),
        ]
        p = self.run_gate(WORKFLOW_TWO_REQUIRED, fleet)
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("FAIL  Format", p.stdout)
        self.assertIn("FAIL  Version Pin Sweep", p.stdout)

    def test_2026_09_02_lone_runner_offline_refused(self):
        # The incident live: the lone light runner OFFLINE — 0 online.
        fleet = [
            runner("light-only", "offline", LABELS_LIGHT),
            runner("r1", "online", LABELS_RUST),
            runner("r2", "online", LABELS_RUST),
        ]
        p = self.run_gate(WORKFLOW_TWO_REQUIRED, fleet)
        self.assertEqual(p.returncode, 1)
        self.assertIn("0 online runner(s) (NONE)", p.stdout)

    def test_registered_is_not_online(self):
        # 2 registered, 1 online: registration must not count.
        fleet = HEALTHY_FLEET[:1] + [runner("l2", "offline", LABELS_LIGHT)] \
            + HEALTHY_FLEET[2:]
        p = self.run_gate(WORKFLOW_TWO_REQUIRED, fleet)
        self.assertEqual(p.returncode, 1)
        self.assertIn("FAIL  Format", p.stdout)

    def test_renamed_required_job_is_the_deadlock_class(self):
        wf = WORKFLOW_TWO_REQUIRED.replace("name: Format",
                                           "name: Formatting")
        p = self.run_gate(wf, HEALTHY_FLEET)
        self.assertEqual(p.returncode, 1)
        self.assertIn("DEADLOCK: required context `Format`", p.stdout)
        self.assertIn("DEADLOCKS", p.stdout)

    def test_empty_inventory_refused(self):
        p = self.run_gate(WORKFLOW_TWO_REQUIRED, [])
        self.assertEqual(p.returncode, 1)
        self.assertIn("EMPTY", p.stdout)

    def test_vacuity_floor_nothing_examined(self):
        # Every required job hosted -> 0 self-hosted examined < floor 1.
        wf = WORKFLOW_TWO_REQUIRED.replace(
            "runs-on: [self-hosted, linux, x64, light]",
            "runs-on: ubuntu-latest").replace(
            "runs-on: [self-hosted, linux, x64, rust-cpu]",
            "runs-on: ubuntu-latest")
        p = self.run_gate(wf, HEALTHY_FLEET)
        self.assertEqual(p.returncode, 1)
        self.assertIn("checked nothing must not pass", p.stdout)

    def test_case_insensitive_label_match(self):
        # Same fleet, but the pass must come from matching Linux/X64 against
        # linux/x64 — assert the ok lines name the runners.
        p = self.run_gate(WORKFLOW_TWO_REQUIRED, HEALTHY_FLEET)
        self.assertEqual(p.returncode, 0)
        self.assertIn("ok    Format", p.stdout)
        self.assertIn("l1, l2", p.stdout)

    def test_thin_label_probe_refused(self):
        # The red-first probe: a deliberately thin label must refuse even
        # when every real required context is healthy.
        fleet = HEALTHY_FLEET + [
            runner("p1", "online", ["self-hosted", "Linux", "podman"])]
        p = self.run_gate(WORKFLOW_TWO_REQUIRED, fleet,
                          extra=["--require-label", "podman"])
        self.assertEqual(p.returncode, 1)
        self.assertIn("FAIL  <probe podman>", p.stdout)

    def test_structural_only_catches_rename_without_inventory(self):
        # The CI mode: no runner inventory at all, rename still refused.
        wf_text = WORKFLOW_TWO_REQUIRED.replace("name: Format",
                                                "name: Formatting")
        with tempfile.TemporaryDirectory() as td:
            p = subprocess.run(
                [sys.executable, str(SCRIPT)] + write_workflows(td, wf_text)
                + ["--structural-only"],
                capture_output=True, text=True)
        self.assertEqual(p.returncode, 1)
        self.assertIn("DEADLOCK: required context `Format`", p.stdout)
        self.assertIn("DEADLOCKS", p.stdout)

    def test_structural_only_green_control(self):
        with tempfile.TemporaryDirectory() as td:
            p = subprocess.run(
                [sys.executable, str(SCRIPT)]
                + write_workflows(td, WORKFLOW_TWO_REQUIRED)
                + ["--structural-only"],
                capture_output=True, text=True)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("10 required contexts, 10 matched to jobs, 0 failures",
                      p.stdout)

    # ---- v0.90 (RQ-90-SPECEXEC, #1636) ------------------------------------
    def test_structural_only_context_in_no_workflow_deadlocks(self):
        # NEGATIVE CONTROL: the tenth context resolved nowhere — ci.yml alone,
        # which is exactly what the pre-v0.90 structural mode read.
        with tempfile.TemporaryDirectory() as td:
            p = subprocess.run(
                [sys.executable, str(SCRIPT)]
                + write_workflows(td, WORKFLOW_TWO_REQUIRED, spec_text=None)
                + ["--structural-only"],
                capture_output=True, text=True)
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("DEADLOCK: required context `spec-suite execution (#1636)` "
                      "is not defined in any workflow", p.stdout)

    def test_structural_only_matrix_spelling_does_not_resolve(self):
        # The same name behind a matrix reports `name (a, b)`, not the name.
        spec = WORKFLOW_SPEC.replace(
            "    runs-on: ubuntu-latest\n",
            "    runs-on: ubuntu-latest\n    strategy: {matrix: {leg: [m4, m7]}}\n")
        self.assertNotEqual(spec, WORKFLOW_SPEC)
        with tempfile.TemporaryDirectory() as td:
            p = subprocess.run(
                [sys.executable, str(SCRIPT)]
                + write_workflows(td, WORKFLOW_TWO_REQUIRED, spec_text=spec)
                + ["--structural-only"],
                capture_output=True, text=True)
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)
        self.assertIn("spec-suite execution (#1636)", p.stdout)

    def test_contract_is_ci_pool_tripwires_not_a_copy(self):
        sys.path.insert(0, str(SCRIPTS))
        import ci_pool_tripwire as T
        import runner_redundancy_check as R
        want = list(T.REQUIRED_CONTEXTS) + [
            c for c in T.PENDING_REQUIRED_CONTEXTS if c not in T.REQUIRED_CONTEXTS]
        self.assertEqual(R.REQUIRED_CONTEXTS, want)
        self.assertIn("spec-suite execution (#1636)", R.REQUIRED_CONTEXTS)

    def test_probe_on_thick_label_passes(self):
        p = self.run_gate(WORKFLOW_TWO_REQUIRED, HEALTHY_FLEET,
                          extra=["--require-label", "light"])
        self.assertEqual(p.returncode, 0)
        self.assertIn("ok    <probe light>", p.stdout)


if __name__ == "__main__":
    unittest.main(verbosity=2)
