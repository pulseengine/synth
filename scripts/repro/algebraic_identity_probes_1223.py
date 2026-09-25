#!/usr/bin/env python3
# ci-status: wired
# ci-checks: stdout /^algebraic-identity-probes: ([0-9]+) \(shape,input\) probe\(s\) executed$/ >= 30
"""RQ-74-PINDEBT2 (#1223): the five algebraic-identity shapes, EXECUTED.

WHY THIS EXISTS, and why it is committed rather than kept in a scratchpad.
`crates/synth-opt` has five arms that used to mark an instruction DEAD without
defining `dest`: `0 + x`, `x + 0`, `x - 0`, `1 * x`, `x * 1`. Killing the
instruction leaves `dest` undefined while consumers still read it, so they get
whatever the allocator left in that register. v0.74 repaired all five to emit
`Opcode::Copy`.

The lane's sweep — "only 2 of the 5 are observably wrong" — rested on five probe
modules that existed only in a scratchpad. v0.74's round-1 cold review rebuilt
the pre-fix compiler independently and measured FOUR of five wrong. Two
measurements of the same quantity disagreed and NEITHER was reproducible,
in a repository whose stated rule is "derive what you check against from the
artifact you ship". So the probes ship here, and the number is whatever this
prints.

WHAT IT CHECKS. Each shape is compiled on the OPTIMIZED path (`--target
cortex-m4`, self-contained — the IR passes do not run on `--relocatable`) and
EXECUTED through the same unicorn harness the home-alias differential uses,
against wasmtime as the oracle. A mismatch is a silent wrong answer: exit 0, no
decline, a wrong value.

WHAT IT DOES NOT CLAIM. These five shapes are not the whole class. The arms fire
on any constant-0/constant-1 operand the IR produces, and this probes the
shapes a human wrote down. The population line below is the count of shapes
executed, not a coverage claim.
"""
import importlib.util
import os
import pathlib
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SYNTH = os.environ.get("SYNTH_BIN", str(ROOT / "target/debug/synth"))
FLAGS = ["--target", "cortex-m4", "--all-exports"]

# name -> (wat body, the shape in source terms)
# THE SHAPES ARE BARE, and round 2 of the v0.74 cold review is why. They were
# each wrapped in `(i32.add <shape> (local.get 0))`, and THAT WRAPPER MASKED
# THREE OF THE FIVE ARMS: with `x - 0` reverted to the defect, the wrapped shape
# returns wasmtime's 14 and the bare shape returns 0 against wasmtime's 7. So
# the oracle was 2/5 potent for its own stated population — it named five arms
# and could only red on two.
#
# This also settles a disagreement round 1 got backwards. Round 1 measured
# "2 of 5 wrong pre-fix" with the wrapped shapes, a reviewer measured 4 of 5
# with bare ones, and round 1 adjudicated in favour of ITS OWN WEAKER PROBES and
# recorded the other figure as unreproducible. Bare shapes reproduce it exactly.
# RQ-75-PROBEINPUT (#1223), v0.75 — EACH SHAPE IS PROBED AT SEVERAL INPUTS.
# v0.74 probed every shape at exactly ONE value (7). An identity can be
# coincidentally correct at a single input, and for THESE identities the
# coincidence is not exotic — it is the value the buggy fold returns:
#
#   (x - x) + x  folded to the constant 0  agrees with the truth at x = 0
#   x + 0 / 0 + x  same
#   x - 0          same
#   1 * x / x * 1  folded to the constant 1 agrees with the truth at x = 1
#
# So "0 of 5 wrong" measured at x=7 was a true statement about one point, and
# the set below deliberately CONTAINS the hiding values (0 and 1) alongside
# values that expose — because a probe set that quietly omitted them would look
# stronger while proving less about the arms it names.
#
# The anti-vacuity assertion is not "6 values": it is that wasmtime's OWN
# answers vary across the set for every shape. If the reference is constant over
# the probed inputs, a compiler returning a constant cannot be caught, however
# many inputs are tried. Derived per shape, never declared.
ARGVALS = (0, 1, 2, 7, 0x7FFFFFFF, 0xFFFFFFFF)

# PER-ARM POTENCY RE-MEASURED WITH THE WIDER SET, and the answer is the one this
# lane did not want: STILL 4 OF 5. Each of the five algebraic arms in
# `synth-opt` was reverted to `inst.is_dead = true` INDIVIDUALLY, the compiler
# rebuilt, and the probes re-run:
#
#     arm          verdict
#     A  0 + x     CAUGHT   (1 of 5 shapes wrong)
#     B  x + 0     CAUGHT
#     C  x - 0     CAUGHT
#     D  1 * x     MISSED   <- unchanged from v0.74's one-input measurement
#     E  x * 1     CAUGHT
#
# So widening the inputs strengthens this oracle against a VALUE coincidence and
# does NOT unmask arm D. Saying "6 inputs instead of 1" as if it were an
# improvement in coverage would have been false.
#
# WHY, established rather than assumed. Arm D is NOT unreachable: reverting it
# CHANGES the emitted bytes (`.text` sha 31f013a6 -> 426b248f on `mul1_l`), so
# the arm fires. The program still returns wasmtime's answer at all six inputs
# because the value survives in the register the result is read from — the
# masking is in REGISTER ALLOCATION, not in the input. Two higher-pressure
# shapes were tried to break that incidental placement (a deferred local read,
# and a second live value across the use) and BOTH still returned correct
# answers at all six inputs.
#
# So arm D's coverage rests on the unit test `test_algebraic_one_mul`, NOT on
# this oracle, and that is stated here rather than left to be inferred from a
# "0 of 5" line. Unmasking it needs a byte-level invariant or a shape that
# forces `dest` to be read from a register the allocator cannot coincidentally
# satisfy; that is a v0.76 candidate and is NOT claimed.

SHAPES = {
    "addzero_r": ("(i32.add (i32.sub (local.get 0) (local.get 0)) (local.get 0))",
                  "(x - x) + x   -> exercises `0 + x`"),
    "addzero_l": ("(i32.add (local.get 0) (i32.sub (local.get 0) (local.get 0)))",
                  "x + (x - x)   -> exercises `x + 0`"),
    "subzero":   ("(i32.sub (local.get 0) (i32.const 0))",
                  "x - 0         -> exercises `x - 0`"),
    "mul1_l":    ("(i32.mul (i32.const 1) (local.get 0))",
                  "1 * x         -> exercises `1 * x`"),
    "mul1_r":    ("(i32.mul (local.get 0) (i32.const 1))",
                  "x * 1         -> exercises `x * 1`"),
}


def _harness():
    """Reuse the home-alias differential's ARM emulator rather than writing a
    fourth one. A second harness is a second thing to be wrong."""
    p = HERE / "home_alias_class_1189_differential.py"
    spec = importlib.util.spec_from_file_location("ha1189", p)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def main() -> int:
    if not os.path.isfile(SYNTH):
        print(f"FAIL: {SYNTH} not built")
        return 1
    try:
        import wasmtime
    except ImportError:
        print("FAIL: wasmtime is required — it is the oracle, not a convenience")
        return 1
    ha = _harness()
    ran, probes, wrong = 0, 0, []
    print(f"{'shape':11s}{'inputs':>10s}{'verdict':>10s}   discrimination")
    with tempfile.TemporaryDirectory() as td:
        for name, (body, desc) in SHAPES.items():
            wat = os.path.join(td, f"{name}.wat")
            with open(wat, "w") as fh:
                fh.write('(module\n  (func (export "f") (param i32) (result i32)\n'
                         f"    {body}))\n")
            obj = os.path.join(td, f"{name}.o")
            r = subprocess.run([SYNTH, "compile", wat, "-o", obj, *FLAGS],
                               capture_output=True, text=True)
            if r.returncode != 0 or not os.path.isfile(obj):
                print(f"  {name:11s}{'-':>10s}{'DECLINED':>10s}   "
                      f"unexpected: these shapes must compile")
                wrong.append(f"{name}: declined")
                continue
            eng = wasmtime.Engine()
            mod = wasmtime.Module(eng, open(wat).read())
            expected = {}
            for a in ARGVALS:
                st = wasmtime.Store(eng)
                inst = wasmtime.Instance(st, mod, [])
                expected[a] = inst.exports(st)["f"](st, a) & 0xFFFFFFFF
            # The reference must DISCRIMINATE, or nothing below can catch a
            # constant-returning fold. Derived from wasmtime's own answers.
            if len(set(expected.values())) < 2:
                wrong.append(
                    f"{name}: VACUITY — wasmtime returns the same value "
                    f"{sorted(set(expected.values()))} for all {len(ARGVALS)} "
                    f"probed inputs, so a fold to a constant is invisible here")
                continue
            loaded = ha.load_object(open(obj, "rb").read(), "arm-self")
            # SIGNATURE: (param widths, return width) — round 2 found this was
            # ("i32", ["i32"]), which is the convention inverted. `_pack_args32`
            # compares each width to 32, so every argument took the 64-bit PAIR
            # branch and clobbered R1's canary: the seed that exists to make an
            # undefined-register read visible was destroyed on every probe.
            bad_here = []
            for a in ARGVALS:
                exp = expected[a]
                got = ha.run_leg("arm-self", loaded, "f", ([32], 32), (a,))
                if isinstance(got, tuple):
                    got = got[0]
                got = got & 0xFFFFFFFF if isinstance(got, int) else got
                probes += 1
                if got != exp:
                    bad_here.append(f"f({a}) = {got}, wasmtime {exp}")
            ran += 1
            if bad_here:
                wrong.append(f"{name} ({desc}): " + "; ".join(bad_here))
            print(f"  {name:11s}{len(ARGVALS):>10d}"
                  f"{('ok' if not bad_here else 'WRONG'):>10}   "
                  f"{len(set(expected.values()))} distinct reference answer(s)")
    print()
    print(f"algebraic-identity-probes: {ran} shape(s) executed")
    print(f"algebraic-identity-probes: {probes} (shape,input) probe(s) executed")
    print(f"silent wrong answers: {len(wrong)} of {ran}")
    for w in wrong:
        print(f"  REFUSE: {w}")
    if ran == 0:
        print("RESULT: FAIL — nothing executed; a gate that checked nothing")
        return 1
    if wrong:
        print("RESULT: FAIL — an algebraic identity dropped its surviving use")
        return 1
    print(f"RESULT: PASS — all {ran} identity shapes return wasmtime's answer "
          f"at every one of {len(ARGVALS)} inputs")
    return 0


if __name__ == "__main__":
    sys.exit(main())
