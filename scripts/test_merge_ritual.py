#!/usr/bin/env python3
# ci-status: wired — runs in the required `claim-check` job.
"""The FIRST test for `scripts/merge_ritual.sh` (#1440).

WHY IT DID NOT HAVE ONE, and why that mattered. The ritual is the script every
merge goes through: four checks, the merge inside its own `&&` chain, a squash
simulation. It had NO test, NO CI reference and NO shellcheck anywhere in the
tree — so every property it relies on was held in place by nothing but the file
not being edited. Three separate releases have already had to repair it
(RQ-72-RITUAL created it, RQ-73-STEP8 added the squash-fidelity call,
RQ-77-SUBJECT fixed a wait loop that counted checks with an EMPTY conclusion and
an exit code read through a `| tee`).

WHAT A TEST OF A SHELL SCRIPT CAN AND CANNOT PROVE, stated because the
difference is the whole honesty of this file. The ritual's real behaviour needs a
LIVE PR, a live branch-protection API and a live merge; none of that is
reproducible here, and a test that stubbed all of it would be testing the stub.
So this file does two DIFFERENT things and never conflates them:

  * PART 1 — EXECUTION. The wait loop's timeout is tested by EXTRACTING THE
    SHIPPED LOOP TEXT from `merge_ritual.sh` and RUNNING IT against a stub `gh`.
    The lines under test are the lines that ship; nothing is mirrored. This is a
    real execution test of a real control path.

  * PART 2 — STRUCTURE. The remaining invariants are asserted STATICALLY, and
    each one is proven non-vacuous by REMOVING the property from a COPY and
    checking the assertion then fails. A static assertion cannot prove the
    ritual behaves correctly; it proves the property has not silently
    disappeared, which is exactly the failure these three releases hit.

Run:  python3 scripts/test_merge_ritual.py
"""
from __future__ import annotations

import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
RITUAL = ROOT / "scripts" / "merge_ritual.sh"

fails: list[str] = []
ran: list[str] = []


def ok(name: str, cond: bool) -> None:
    ran.append(name)
    print(f"  {'ok  ' if cond else 'FAIL'} {name}")
    if not cond:
        fails.append(name)


def extract_wait_loop(text: str) -> str:
    """The SHIPPED `while :; do … done` block, verbatim.

    Sliced from the source rather than re-typed: a re-typed loop would be a
    hand-written mirror of a shipped thing, which is the defect class this repo's
    North Star names. If the slice fails, that is a REFUSAL — an empty loop would
    "pass" every execution test below while testing nothing.
    """
    start = text.index("while :; do")
    depth = 0
    i = start
    for m in re.finditer(r"\b(do|done)\b", text[start:]):
        if m.group(1) == "do":
            depth += 1
        else:
            depth -= 1
            if depth == 0:
                i = start + m.end()
                break
    else:
        raise AssertionError("REFUSE: no matching `done` for the wait loop")
    loop = text[start:i]
    assert "sleep 60" in loop, "REFUSE: the sliced block is not the polling loop"
    return loop


def run_loop(loop: str, max_wait: str, pending: str,
             present: str = "9") -> tuple[int, str]:
    """Execute the SHIPPED loop with a stub `gh`.

    `present` is the first field the loop's own jq produces (how many non-advisory
    checks EXIST) and `pending` the second (how many have no conclusion yet), so
    the stub can drive both halves of the loop's break condition independently.

    `present` exists because without it the population FLOOR could not be tested
    at all: v0.78's round-2 review found the floor assertion passing under every
    mutation of the property it named, since the harness could only ever produce
    two outcomes and the predicate accepted both. A parameter that cannot vary
    cannot discriminate.
    """
    with tempfile.TemporaryDirectory() as d:
        bindir = pathlib.Path(d) / "bin"
        bindir.mkdir()
        gh = bindir / "gh"
        # A REAL TAB between the fields: the loop reads them with `read -r N P`, and
        # a literal backslash-t would make `[ "$N" -ge "$FLOOR" ]` error with
        # "integer expression expected" and never settle — the loop would then
        # "time out" for a reason that has nothing to do with the property tested.
        gh.write_text(f'#!/bin/bash\necho "{present}\t{pending}"\n')
        gh.chmod(0o755)
        script = pathlib.Path(d) / "loop.sh"
        script.write_text(
            "set -uo pipefail\n"
            f'export PATH="{bindir}:$PATH"\n'
            'PR=1; REPO=x/y; FLOOR=9\n'
            f'MAX_WAIT_MIN={max_wait}\nWAITED=0\n'
            + loop
            + '\necho "LOOP-EXITED-NORMALLY"\n'
        )
        p = subprocess.run(["bash", str(script)], capture_output=True, text=True,
                           timeout=120)
        return p.returncode, p.stdout + p.stderr


def main() -> int:
    text = RITUAL.read_text()
    loop = extract_wait_loop(text)
    ok("the shipped wait loop is locatable and is the polling loop "
       "(a failed slice REFUSES rather than testing an empty string)",
       "sleep 60" in loop and "while :; do" in loop)

    # ---------------------------------------------------------- PART 1: EXECUTION
    # THE DEFECT (#1440): the loop was `while :; do … sleep 60; done` with no
    # bound, so its failure mode was a HANG — no verdict, nothing to read.
    rc, out = run_loop(loop, max_wait="1", pending="3")
    ok("RQ-78-RITUAL: the SHIPPED wait loop TIMES OUT instead of hanging when "
       "checks never settle (executed, not grepped)",
       rc != 0 and "TIMEOUT" in out)
    ok("RQ-78-RITUAL: and the timeout is a REFUSAL (exit 2 = could not judge), "
       "never a fall-through to a verdict",
       rc == 2 and "LOOP-EXITED-NORMALLY" not in out)
    ok("RQ-78-RITUAL: the timeout says it is NOT a verdict about the PR — an "
       "operator must not read it as 'not mergeable'",
       "NOT a verdict" in out)
    # POSITIVE CONTROL: with nothing pending the same loop must EXIT NORMALLY.
    # Without this, "it exits 2" would be consistent with a loop that can never
    # succeed, and the timeout test would prove nothing about the happy path.
    rc_ok, out_ok = run_loop(loop, max_wait="5", pending="0")
    ok("POSITIVE CONTROL: the same shipped loop exits NORMALLY when the "
       "population is met and nothing is pending",
       rc_ok == 0 and "LOOP-EXITED-NORMALLY" in out_ok)
    # THE POPULATION FLOOR, tested by varying the POPULATION. Nothing pending, but
    # only 3 of the 9 required checks present: "nothing is pending" is also true of
    # a PR whose checks have not registered, which is the #1407 defect the floor
    # exists to catch. It must NOT settle.
    #
    # This assertion replaces one that was VACUOUS and was caught by v0.78's round-2
    # review: it passed `loop.replace("FLOOR", "FLOOR")` — a no-op — and its
    # predicate `rc == 0 or "TIMEOUT" in out` accepted BOTH outcomes the harness can
    # produce, so it held under a break condition replaced by `false`, under the
    # floor removed entirely, and under an unsatisfiable floor. Its own name
    # conceded it ("which is what the positive control above just showed"). A
    # predicate that accepts every outcome is not an assertion.
    # THE FLOOR ASSERTION AND THE POSITIVE CONTROL ARE A PAIR, and neither alone
    # discriminates every mutation — measured, not assumed:
    #   floor removed (`-ge 0`)        -> THIS assertion fails, positive control passes
    #   break condition -> `false`     -> this passes, POSITIVE CONTROL fails
    #   floor unsatisfiable (`-ge 999`)-> this passes, POSITIVE CONTROL fails
    #   timeout removed                -> the loop HANGS; the harness's own
    #                                     subprocess timeout raises after 120s
    # So the set is potent where no single member is. Claiming this assertion
    # catches all four would be the over-claim round 2 caught in its predecessor.
    rc_lo, out_lo = run_loop(loop, max_wait="1", pending="0", present="3")
    ok("RQ-78-RITUAL: population BELOW the floor does NOT settle even with nothing "
       "pending — 'no checks pending' is also true before CI registers (#1407)",
       rc_lo == 2 and "TIMEOUT" in out_lo
       and "LOOP-EXITED-NORMALLY" not in out_lo)

    # ---------------------------------------------------------- PART 2: STRUCTURE
    # Each assertion below is paired with a MUTATION proving it is not vacuous.
    def strip_comments(s: str) -> str:
        """Comment lines removed. The first draft of this test searched the whole
        file for `gh pr merge` and matched a COMMENT at line 25 ("`gh pr merge
        --squash` uses the PR title…"), which has no `&&` — so it reported the
        shipped merge as unchained while the real statement 20 lines further down
        is correctly chained. A true statement about the wrong subject, inside the
        test written to catch that class."""
        return "\n".join(l for l in s.splitlines()
                          if not l.lstrip().startswith("#"))

    def prop_merge_inside_chain(s: str) -> bool:
        # The merge must sit inside an `&&` chain, never on its own line after an
        # `echo OK || echo FAIL` — that shape pushes past a red gate.
        code = strip_comments(s)
        m = re.search(r"gh pr merge[^\n]*", code)
        if not m:
            return False
        line_start = code.rfind("\n", 0, m.start()) + 1
        return "&&" in code[line_start:m.end()]

    def prop_reads_gate_rc(s: str) -> bool:
        # merge_gate's rc must be read from the process, NOT through a pipe:
        # a pipeline's exit code is the last command's.
        return "GATERC=$?" in s and not re.search(r"merge_gate\.py[^\n]*\|\s*tee", s)

    def prop_greps_gateok(s: str) -> bool:
        return "GATEOK" in s

    def prop_floor_derived(s: str) -> bool:
        # The wait floor must come from branch protection, not a hardcoded number.
        return "required_status_checks/contexts" in s

    def prop_bounded(s: str) -> bool:
        return "MAX_WAIT_MIN" in s and "WAITED" in s

    props = [
        ("the merge statement sits INSIDE an && chain", prop_merge_inside_chain,
         ("&& gh pr merge", "; gh pr merge")),
        ("merge_gate's exit code is read from the PROCESS, not through a pipe",
         prop_reads_gate_rc, ("GATERC=$?", "GATERC=0")),
        ("the ritual greps for the literal GATEOK", prop_greps_gateok,
         ("GATEOK", "GATE_OK_RENAMED")),
        ("the wait FLOOR is derived from branch protection, not hardcoded",
         prop_floor_derived, ("required_status_checks/contexts", "hardcoded")),
        ("the wait loop is BOUNDED", prop_bounded,
         ("MAX_WAIT_MIN", "UNBOUNDED_AGAIN")),
    ]
    for name, fn, (old, new) in props:
        holds = fn(text)
        # replace_all, NOT the first occurrence. The first draft used
        # `.replace(old, new, 1)` and two mutants were then REJECTED BY NOTHING:
        # an `in`-style predicate still found a later copy of the token, so the
        # assertion looked non-vacuous while proving nothing. Caught only because
        # this loop requires the mutant to FAIL.
        mutated = text.replace(old, new)
        # THE MUTATION MUST HAVE APPLIED. A replace that matched nothing leaves
        # the text identical and the "mutant fails" check would then be a lie.
        applied = mutated != text
        broken = not fn(mutated)
        ok(f"{name} — holds, and the assertion is NON-VACUOUS "
           f"(mutation applied={applied}, mutant rejected={broken})",
           holds and applied and broken)

    print(f"merge-ritual-tests: {len(ran)} assertions, {len(fails)} failure(s)")
    MIN = 11
    if len(ran) < MIN:
        print(f"REFUSE: only {len(ran)} assertions ran, floor is {MIN} — "
              f"assertions were removed or the body stopped early.")
        return 1
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
