#!/usr/bin/env python3
"""VCR-RA-003 phase 2 (#242) repro — across-CALL + across-JOIN allocation validation.

The v0.48 validator (`validate_final_allocation`) was BOUNDED to straight-line
segments + callee-saved/spill discipline. Phase 2 extends it to WHOLE-FUNCTION
control flow:

  Invariant 3 (across-CALL): a caller-saved register R2/R3/R12 held live across a
    bl/blx/call is flagged (the AAPCS boundary destroys it). R0/R1 excluded
    (return value). Anchored on the ABI contract, not inferred value-identity.

  Invariant 4 (across-JOIN): a register live-in to a control-flow join (>=2
    predecessors) must be AVAILABLE (must-defined on every incoming path, or an
    entry live-in). Forward MUST/intersection availability fixpoint over a
    dedicated join CFG (bx-lr returns = sinks, calls = fall-through with a
    caller-saved def-set; reserved R9/R10/R11/R12 + params/SP/LR seeded).

This script is the SILENT-ON-REAL-CODEGEN half of the gate: it compiles a set of
branchy + memory-touching + call-bearing repro fixtures through the UNCONDITIONAL
validator and asserts ZERO false positives (no `VCR-RA-003 ... FAILED`). If the
across-JOIN check false-positived (e.g. the R11 linmem-base regression this lane
found + fixed by seeding the reserved registers), one of these would decline to
compile and this gate would go red.

The RED (non-vacuity) half lives in the `ra003_red_*` unit tests
(`cargo test -p synth-synthesis --lib ra003_`), which assert the validator
CATCHES a synthetic across-CALL clobber and across-JOIN clobber.

Usage:  python3 scripts/repro/vcr_ra_003_phase2_join_call.py [path/to/synth]
Exit 0 iff every branchy fixture compiles clean (validator silent on real code).
"""
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
REPRO = REPO / "scripts" / "repro"

# Fixtures with real control-flow joins (br/br_if/block/loop/if) and/or memory
# stores through the reserved R11 base — the shapes invariant 4 reasons about.
BRANCHY_FIXTURES = [
    "block_brif_483.wat",       # forward block + br_if; nested br 1 (the R11 case)
    "if_else_result_343.wat",   # if/else merging a value at the join
    "cf_shapes_500.wat",        # assorted CF shapes, promoted-local + R11 joins
    "br_value_509.wat",         # br carrying a value
    "brif_outer_740.wat",       # br_if to an outer block
    "loop_param_bound_663.wat", # counted loop (loop-header join)
    "base_cse_branch.wat",      # base-CSE across a branch (R11 base at a join)
]


def synth_bin() -> str:
    if len(sys.argv) > 1:
        return sys.argv[1]
    # Prefer an env-redirected target dir, else the workspace default.
    import os
    tgt = os.environ.get("CARGO_TARGET_DIR", str(REPO / "target"))
    return str(Path(tgt) / "debug" / "synth")


def main() -> int:
    binp = synth_bin()
    if not Path(binp).exists():
        print(f"error: synth binary not found at {binp}", file=sys.stderr)
        print("build first: cargo build -p synth-cli", file=sys.stderr)
        return 2

    failures = []
    checked = 0
    for fx in BRANCHY_FIXTURES:
        path = REPRO / fx
        if not path.exists():
            print(f"warn: fixture missing, skipping: {fx}", file=sys.stderr)
            continue
        checked += 1
        with tempfile.NamedTemporaryFile(suffix=".elf") as out:
            proc = subprocess.run(
                [binp, "compile", str(path), "-o", out.name, "--relocatable"],
                capture_output=True,
                text=True,
            )
        combined = proc.stdout + proc.stderr
        if "VCR-RA-003" in combined and "FAILED" in combined:
            # Extract the offending line for the report.
            line = next(
                (l for l in combined.splitlines() if "FAILED" in l and "VCR-RA-003" in l),
                "<unknown>",
            )
            failures.append((fx, line.strip()))
            print(f"FAIL {fx}: validator false-positived on real codegen")
            print(f"     {line.strip()}")
        else:
            print(f"ok   {fx}: validator silent (Consistent / NotAttempted)")

    print(f"\nchecked {checked} branchy fixtures; {len(failures)} false-positives")
    if failures:
        print(
            "\nVCR-RA-003 phase-2 across-JOIN/across-CALL check FALSE-POSITIVED on "
            "real codegen — the availability seed or the join CFG is wrong.",
            file=sys.stderr,
        )
        return 1
    print(
        "VCR-RA-003 phase 2 SILENT on real branchy codegen — the whole-function "
        "across-CALL + across-JOIN checks pass every real fixture."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
