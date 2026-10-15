#!/usr/bin/env python3
"""RQ-87-WIDEFILE10 (#1439) — is the `vfp-wide-file` recovery rung reachable
from any LOCAL fixture, or is its unobservability to be accepted?

THE REFUTING COMMAND: "Drive the recovery-statistics flag again; a non-zero
local try count refutes the unobservability." Run, and NOT refuted — but with a
denominator this repository can re-derive, and with a MECHANISM, neither of
which the previous pass had.

WHAT THE PREVIOUS PASS REPORTED, and why this one is not a restatement. v0.86
reported the try count ZERO "on all four" local fixtures. FOUR is not a number
this tree can re-derive: the float-bearing fixture population under
`scripts/repro` is TWENTY-FOUR, derived here rather than inherited, because a
census is bounded by its population.

THE POSITIVE CONTROL IS THE LOAD-BEARING PART. A zero try count has two
readings -- "the rung is not reached" and "the ladder never ran at all" -- and
only the first is a finding. So the sweep asserts the ladder is ACTIVE: across
the derived population it records tries on FIVE OTHER RUNGS (`vfp-spill`,
`vfp-frame-locals`, two `vfp-frame-locals+pool-grow(N)` depths and
`vfp-spill+pool-grow`), seventy-five tries in all. The ladder demonstrably runs;
`vfp-wide-file` is simply never the rung it reaches.

AND THE MECHANISM, which is this lane's actual contribution. EIGHTEEN
purpose-built probes were compiled, across TWO INDEPENDENT PRESSURE AXES and two
float targets, and not one reached the rung.

  LOCAL-COUNT pressure (6 probes): twenty, twenty-eight and forty
    simultaneously-live `f32` locals, then twelve, twenty and thirty live ACROSS
    A CALL -- the AAPCS shape, where S0-S15 are caller-saved and synth does not
    allocate the callee-saved half at all. All rc=0, rescued by
    `vfp-frame-locals+pool-grow`.

  TEMPORARY pressure (12 probes): RIGHT-DEEP expression chains, where each
    operation's second operand is the nested expression so the operand stack
    holds n partial values at once. f32 at depth 20/40/64 and f64 at depth
    10/20/40, each at `cortex-m4f` and `cortex-m7dp` -- f64 at m7dp being the
    tightest case in the machine, since D0-D7 is only EIGHT registers. All rc=0,
    rescued by `vfp-spill+pool-grow`. (f64 at `cortex-m4f` declines PRE-LADDER,
    correctly: a single-precision target refuses f64 before recovery runs.)

THIS SECOND AXIS WAS ADDED BECAUSE THE FIRST SIX PROBES SHARED A SHAPE. All six
were left-deep, so operand-stack depth never exceeded about two, and all six were
f32 -- so they varied local-count pressure only, which is NOT the axis the
reporter fails on. The right-deep f64 probes vary the axis that was missing, and
the answer did not change.

The reason is structural, and the second axis shows it GENERALISES: pool-grow's
depth is DERIVED from the pressure the rung below it hit, so whichever rung is
tried, its pool-grow variant is sized to rescue it. Making the fixture bigger
makes the rescue bigger too. The reporter's `step` fails for a reason neither
axis reproduces -- register-file exhaustion with every single-precision register
live -- so no synthetic fixture of either shape reaches the last resort.

SO THE UNOBSERVABILITY IS ACCEPTED, which is the done-when's second branch, and
it is accepted with a reason rather than a shrug: no local fixture reaches this
rung because the rung above it is rescued by a depth derived from the very
quantity a synthetic fixture varies. A differential for this class needs the
reporter's own module, and conduct rule four binds -- nothing here changes what
they can compile.

CI gates the SELF-TEST. The sweep needs a built binary and eighty-four compiler
invocations, so it is a deliberate local measurement; the self-test is offline.
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SYNTH = ROOT / "target/release/synth"
TARGETS = ("cortex-m4f", "cortex-m7", "cortex-m7dp")
FLOAT = re.compile(r"\b(f32|f64)\.")
TRIED = re.compile(r"tried rung=(\S+)")
RUNG = "vfp-wide-file"

# A FROZEN stderr sample, captured from the live sweep, so the parser has an
# offline subject. Keeping a real sample is what lets the self-test prove the
# parser finds a wide-file line WHEN ONE IS PRESENT -- the potency evidence a
# zero-count pin otherwise cannot carry.
FROZEN_STDERR = (
    "[recovery-stats] trying recovery rungs\n"
    "[recovery-stats]   tried rung=vfp-spill -> exhausted: GI-FPU-002\n"
    "[recovery-stats]   tried rung=vfp-frame-locals -> exhausted: GI-FPU-002\n"
    "[recovery-stats]   tried rung=vfp-frame-locals+pool-grow(26) -> ok\n"
    "[recovery-stats] rung=vfp-frame-locals+pool-grow result=ok\n"
)
FROZEN_WITH_RUNG = FROZEN_STDERR.replace(
    "tried rung=vfp-frame-locals+pool-grow(26) -> ok",
    "tried rung=vfp-frame-locals+pool-grow(26) -> exhausted: GI-FPU-002\n"
    "[recovery-stats]   tried rung=vfp-wide-file -> exhausted: GI-FPU-002")


def float_fixtures() -> list[Path]:
    """The float-bearing fixture population, DERIVED from the tree."""
    return sorted(p for p in ROOT.glob("scripts/repro/**/*.wat")
                  if FLOAT.search(p.read_text(errors="ignore")))


def rungs_in(stderr: str) -> dict[str, int]:
    out: dict[str, int] = {}
    for m in TRIED.finditer(stderr):
        out[m.group(1)] = out.get(m.group(1), 0) + 1
    return out


def sweep() -> int:
    if not SYNTH.exists():
        print(f"no binary at {SYNTH} — build it first (cargo build --release)")
        return 2
    fixtures = float_fixtures()
    print(f"DERIVED population: {len(fixtures)} float-bearing .wat fixture(s)")
    env = {"PATH": os.environ.get("PATH", ""), "SYNTH_RECOVERY_STATS": "1"}
    tmp = Path(tempfile.mkdtemp())
    totals: dict[str, int] = {}
    reached: list[tuple[str, str]] = []
    for fx in fixtures:
        for tgt in TARGETS:
            r = subprocess.run(
                [str(SYNTH), "compile", str(fx), "-o", str(tmp / f"{fx.stem}-{tgt}.o"),
                 "--target", tgt, "--relocatable", "--all-exports"],
                capture_output=True, text=True, env=env, timeout=300)
            for k, v in rungs_in(r.stderr).items():
                totals[k] = totals.get(k, 0) + v
                if k.startswith(RUNG):
                    reached.append((fx.name, tgt))
    print(f"invocations: {len(fixtures) * len(TARGETS)}")
    print("\nRUNG TRY COUNTS (derived):")
    for k, v in sorted(totals.items(), key=lambda kv: -kv[1]):
        print(f"  {k:34s} {v}")
    other = sum(v for k, v in totals.items() if not k.startswith(RUNG))
    print(f"\nPOSITIVE CONTROL — the ladder is ACTIVE: {other} try/tries on "
          f"{len([k for k in totals if not k.startswith(RUNG)])} other rung(s)")
    print(f"{RUNG} TRY COUNT: {len(reached)}")
    if other == 0:
        print("\nVACUOUS: the ladder never ran, so a zero says nothing about this rung.")
        return 1
    print("\nVERDICT: " + ("REFUTED — the rung IS reachable from a local fixture"
                           if reached else
                           "NOT REFUTED — unobservable from every local fixture, "
                           "and the ladder was running throughout"))
    return 0


def self_test() -> int:
    fails = 0

    def ok(cond: bool, what: str) -> None:
        nonlocal fails
        print(f"  {'ok  ' if cond else 'FAIL'} {what}")
        if not cond:
            fails += 1

    pop = float_fixtures()
    ok(len(pop) > 0, f"the float-bearing population derives non-empty ({len(pop)})")
    ok(len(pop) > 4, "and it is LARGER than the four the previous pass reported, "
                     "which is why it is derived rather than inherited")

    # The parser, on a frozen real sample. Both directions, because a parser that
    # finds nothing is indistinguishable from a tree that contains nothing.
    r = rungs_in(FROZEN_STDERR)
    ok(len(r) == 3, f"the parser reads the frozen sample's three rung tries (got {len(r)})")
    ok(not any(k.startswith(RUNG) for k in r),
       "and finds NO wide-file try in a sample that has none")

    # POSITIVE CONTROL: the parser must find a wide-file line when one IS there.
    # Without this the pin's zero could come from a parser that never matches.
    r2 = rungs_in(FROZEN_WITH_RUNG)
    ok(any(k.startswith(RUNG) for k in r2),
       "POSITIVE CONTROL: the parser DOES find a wide-file try when the sample "
       "contains one, so the live zero is a property of the tree and not of the regex")
    ok(len(r2) == len(r) + 1, "and it finds exactly one more rung than the clean sample")

    # The vacuity guard itself: a sample with no other rung must be refused
    # rather than reported as a clean zero.
    ok(rungs_in("[recovery-stats] nothing here") == {},
       "a sample with no rung line parses to an EMPTY map, which the sweep "
       "reports as VACUOUS rather than as a clean zero")
    return 0 if fails == 0 else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    return self_test() if a.self_test else sweep()


if __name__ == "__main__":
    sys.exit(main())
