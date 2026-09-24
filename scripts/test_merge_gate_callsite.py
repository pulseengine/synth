#!/usr/bin/env python3
"""RQ-75-CALLSITE (#1269): drive `gate()` and `main()` — the functions CI
actually runs — against RECORDED process output.

WHY THIS FILE EXISTS. `merge_gate.py --self-test` builds a real git repository
and exercises the arithmetic: `decide`, `branch_currency`, `squash_fidelity`,
`fidelity_exit`, `is_advisory`. Twenty-five checks, all genuine. It never calls
`gate()` or `main()`.

v0.74's round-1 gate review measured the consequence directly: TEN mutations
applied to `gate()` and `main()` — including forcing the whole status rollup to
SUCCESS, replacing `ok &= passed` with `ok &= True`, and returning 0 instead of
`fidelity_exit(verdict)` — and ALL TEN passed `--self-test`. The merge ritual
consumes `main()`'s exit code. Nothing tested it.

AND IT IS A CLASS, NOT AN INSTANCE. v0.73 extracted `decide()` out of `gate()`
BECAUSE the ritual consumes the decision, gave `decide()` a test, and left
`gate()` untested. v0.74 extracted `fidelity_exit()` out of `main()` for the
identical stated reason, gave it a test, and left `main()` untested. Each
release moved the tested boundary one call outward and moved the gap with it.
Extracting an eleventh function would be the same move a third time, so this
file drives the ENTRY POINTS instead.

THE SEAM IS `subprocess.run`, NOT `sh`. Patching `sh` would miss the two calls
that bypass it — `git merge-base --is-ancestor` in `branch_currency` (line ~70)
and `git diff` in `squash_fidelity` (line ~98) — and would silently keep
missing any third one added later. `subprocess.run` is the single chokepoint
through which this module touches anything outside itself.

AN UNRECORDED CALL IS A HARD FAILURE, never a default. A recorder that returns
empty output for an argv it does not know would let a scenario under-specify
itself and still go green — which is the vacuity this programme keeps finding in
its own instruments. `_Recorder` raises instead, and one test asserts that it
does.

PROVEN POTENT BY MUTATION — the ten that v0.74 measured as surviving. Each was
applied to `merge_gate.py`, VERIFIED PRESENT ON DISK before anything was
measured, then both instruments were run and restored:

    mutation                                          --self-test   this file
    main: fidelity exit code discarded                green         RED
    main: rollup accumulator forced true (ok &= True) green         RED
    main: gate result never reaches the exit code     green         RED
    main: non-MERGED PR no longer refused             green         RED
    main: required contexts replaced by []            green         RED
    gate: every rollup entry forced to SUCCESS        green         RED
    gate: branch currency forced current              green         RED
    gate: base agreement forced true                  green         RED
    gate: decide called with an empty required list   green         RED
    gate: PENDING rendered as SUCCESS                 green         RED

10 of 10 CAUGHT, 0 survived, 0 inert — and all ten leave `--self-test` GREEN,
which is the measurement that justifies this file rather than an eleventh
extraction.

ONE ASSERTION HERE WAS ITSELF FALSE WHEN FIRST WRITTEN, and is recorded because
this programme keeps finding its corrections are where the next wrong sentence
goes. It asserted that a `baseRefOid` disagreeing with `origin/main` REFUSES.
`decide()`'s own comment refutes that: agreement is reported beside CHECK2 and
deliberately NOT gated, because agreement is exactly what was mistaken for
branch currency in #1269a. The assertion now pins the real contract in both
directions, so a change that starts gating on it — or drops it from the report —
goes red.

WHAT THIS STILL DOES NOT COVER, disclosed rather than left to be rediscovered:
the recorded strings are hand-written, so they assert what THIS file believes
`gh` and `git` emit, not what they actually emit. A `gh` schema change would
leave every test here green and the real gate broken. Closing that needs a
recording captured from a live call and refreshed, which is a v0.76 candidate
and is NOT claimed here.
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import types

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import merge_gate  # noqa: E402

REPO = "pulseengine/synth"
PR = "1400"
HEAD = "aaaaaaaa11112222333344445555666677778888"
BASE = "bbbbbbbb11112222333344445555666677778888"
MERGED = "cccccccc11112222333344445555666677778888"

REQUIRED = [
    "Format", "Clippy", "Test", "Z3 Verification", "Claim Check",
    "Version Pin Sweep", "Bazel Build & Proofs", "Kani Verification",
    "Rivet Validation",
]


class UnrecordedCall(AssertionError):
    """Raised when the code under test reaches for something not recorded."""


class _Recorder:
    """Replaces `subprocess.run`. Answers ONLY what it was given."""

    def __init__(self, table: dict[tuple, tuple[int, str]]):
        self.table = table
        self.calls: list[tuple] = []

    def __call__(self, args, **kw):
        key = tuple(args)
        self.calls.append(key)
        if key not in self.table:
            raise UnrecordedCall(
                f"unrecorded subprocess call: {key!r}\n"
                f"recorded keys:\n  " + "\n  ".join(repr(k) for k in self.table)
            )
        rc, out = self.table[key]
        return subprocess.CompletedProcess(args=list(args), returncode=rc,
                                           stdout=out, stderr="")


def rollup(**overrides) -> list[dict]:
    """A status rollup with every required context SUCCESS, then overrides."""
    checks = [{"name": n, "conclusion": "SUCCESS"} for n in REQUIRED]
    for c in checks:
        if c["name"] in overrides:
            c["conclusion"] = overrides[c["name"]]
    for name, concl in overrides.items():
        if name not in REQUIRED:
            checks.append({"name": name, "conclusion": concl})
    return checks


def gate_table(checks, base_oid=BASE, behind="0", ancestor_rc=0,
               origin_main=None) -> dict:
    """The exact process calls `gate()` makes, and nothing else."""
    origin_main = origin_main if origin_main is not None else base_oid
    view = {"statusCheckRollup": checks, "baseRefOid": base_oid,
            "headRefOid": HEAD}
    return {
        ("gh", "pr", "view", PR, "--repo", REPO, "--json",
         "statusCheckRollup,baseRefOid,headRefOid"): (0, json.dumps(view)),
        ("git", "rev-list", "--count", f"{HEAD}..origin/main"): (0, behind),
        ("git", "merge-base", "--is-ancestor", "origin/main", HEAD): (ancestor_rc, ""),
        ("git", "rev-parse", "origin/main"): (0, origin_main),
    }


def main_table(checks, **kw) -> dict:
    """gate()'s calls plus the required-contexts fetch `main()` performs."""
    t = gate_table(checks, **kw)
    t[("gh", "api",
       f"repos/{REPO}/branches/main/protection/required_status_checks/contexts",
       "--jq", ".[]")] = (0, "\n".join(REQUIRED))
    return t


def fidelity_table(state="MERGED", diff_rc=0, diff_out="", behind="0",
                   ancestor_rc=0) -> dict:
    view = {"headRefOid": HEAD, "baseRefOid": BASE,
            "mergeCommit": {"oid": MERGED}, "state": state}
    return {
        ("gh", "pr", "view", PR, "--repo", REPO, "--json",
         "headRefOid,baseRefOid,mergeCommit,state"): (0, json.dumps(view)),
        ("git", "fetch", "-q", "origin", f"refs/pull/{PR}/head"): (0, ""),
        ("git", "diff", HEAD, MERGED): (diff_rc, diff_out),
        ("git", "rev-list", "--count", f"{HEAD}..{BASE}"): (0, behind),
        ("git", "merge-base", "--is-ancestor", BASE, HEAD): (ancestor_rc, ""),
    }


# --------------------------------------------------------------------------


def run_gate(table) -> dict:
    rec = _Recorder(table)
    orig, merge_gate.subprocess = merge_gate.subprocess, types.SimpleNamespace(run=rec)
    try:
        return merge_gate.gate(PR, REPO, REQUIRED)
    finally:
        merge_gate.subprocess = orig


def run_main(argv: list[str], table) -> tuple[int, str]:
    rec = _Recorder(table)
    orig_sub, merge_gate.subprocess = merge_gate.subprocess, types.SimpleNamespace(run=rec)
    orig_argv, sys.argv = sys.argv, ["merge_gate.py", *argv]
    import io
    import contextlib
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            rc = merge_gate.main()
        return rc, buf.getvalue()
    finally:
        merge_gate.subprocess = orig_sub
        sys.argv = orig_argv


def main() -> int:
    fails: list[str] = []

    def check(name, cond, detail=""):
        if cond:
            print(f"  ok   {name}")
        else:
            print(f"  FAIL {name} {detail}")
            fails.append(name)

    # ---- gate(): the decision, driven end to end --------------------------
    res = run_gate(gate_table(rollup()))
    check("gate: all-green PR passes every check",
          all(p for p, _ in res.values()), res)

    res = run_gate(gate_table(rollup(Clippy="FAILURE")))
    check("gate: a REQUIRED red refuses",
          not all(p for p, _ in res.values()))

    res = run_gate(gate_table(rollup(Test="PENDING")))
    check("gate: a REQUIRED pending refuses (CHECK3b)",
          not all(p for p, _ in res.values()))

    # A required context absent from the rollup is the deadlock shape: it is
    # not red, it simply never reports.
    partial = [c for c in rollup() if c["name"] != "Kani Verification"]
    res = run_gate(gate_table(partial))
    check("gate: a required context MISSING from the rollup refuses",
          not all(p for p, _ in res.values()))

    res = run_gate(gate_table(rollup(), behind="3", ancestor_rc=1))
    check("gate: a BEHIND branch refuses (CHECK2)",
          not all(p for p, _ in res.values()))

    # `baseRefOid` agreement is REPORTED, deliberately NOT gated — that is
    # #1269a's whole finding: agreement with `origin/main` is what people
    # mistook for branch currency, and a branch can agree while being stale.
    # This assertion pinned the OPPOSITE when first written, and `decide`'s own
    # comment refuted it. Kept as the positive statement of the contract, so a
    # future change that either starts gating on it, or drops it from the
    # report, goes red.
    res = run_gate(gate_table(rollup(), origin_main="deadbeef" + "0" * 32))
    check("gate: baseRefOid disagreement is REPORTED, not gated",
          all(p for p, _ in res.values())
          and res["CHECK2"][1]["baseRefOid_agrees"] is False, res)

    res = run_gate(gate_table(rollup()))
    check("gate: baseRefOid agreement is reported True when it agrees",
          res["CHECK2"][1]["baseRefOid_agrees"] is True, res)

    # The advisory carve-out is the one that must NOT block.
    res = run_gate(gate_table(rollup(**{"codecov/patch": "FAILURE"})))
    check("gate: an ADVISORY red still passes",
          all(p for p, _ in res.values()), res)

    res = run_gate(gate_table(rollup(**{"Rivet Federated Graph (advisory)": "FAILURE"})))
    check("gate: the advisory federated-graph red still passes",
          all(p for p, _ in res.values()), res)

    # ---- main(): the EXIT CODE the merge ritual consumes ------------------
    rc, out = run_main(["--pr", PR], main_table(rollup()))
    check("main: green PR -> rc 0 and GATEOK", rc == 0 and "GATEOK" in out,
          f"rc={rc} out={out!r}")

    rc, out = run_main(["--pr", PR], main_table(rollup(Clippy="FAILURE")))
    check("main: required red -> rc 1 and GATEFAIL",
          rc == 1 and "GATEFAIL" in out, f"rc={rc} out={out!r}")

    rc, out = run_main(["--pr", PR], main_table(rollup(Test="PENDING")))
    check("main: required pending -> rc 1", rc == 1, f"rc={rc}")

    # ---- main --squash-fidelity: the other exit code ----------------------
    rc, out = run_main(["--pr", PR, "--squash-fidelity"], fidelity_table())
    check("main: FAITHFUL squash -> rc 0",
          rc == 0 and "FAITHFUL" in out, f"rc={rc} out={out!r}")

    rc, out = run_main(["--pr", PR, "--squash-fidelity"],
                       fidelity_table(diff_out="+ a\n- b"))
    check("main: SQUASH ALTERED CONTENT -> non-zero",
          rc != 0 and "ALTERED" in out, f"rc={rc} out={out!r}")

    # INDETERMINATE is not a pass — the v0.74 disclosure's whole point.
    rc, out = run_main(["--pr", PR, "--squash-fidelity"],
                       fidelity_table(behind="4", ancestor_rc=1))
    check("main: INDETERMINATE -> non-zero",
          rc != 0 and "INDETERMINATE" in out, f"rc={rc} out={out!r}")

    rc, out = run_main(["--pr", PR, "--squash-fidelity"],
                       fidelity_table(diff_rc=128))
    check("main: DIFF UNAVAILABLE -> non-zero",
          rc != 0 and "DIFF UNAVAILABLE" in out, f"rc={rc} out={out!r}")

    rc, out = run_main(["--pr", PR, "--squash-fidelity"],
                       fidelity_table(state="OPEN"))
    check("main: squash-fidelity on a non-MERGED PR -> rc 1",
          rc == 1, f"rc={rc} out={out!r}")

    # ---- the recorder itself must be loud, or every test above is vacuous --
    try:
        short = gate_table(rollup())
        del short[("git", "rev-parse", "origin/main")]
        run_gate(short)
        check("recorder: an UNRECORDED call raises", False,
              "it returned instead of raising")
    except UnrecordedCall:
        check("recorder: an UNRECORDED call raises", True)

    print(f"\nmerge-gate-callsite: {len(fails)} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
