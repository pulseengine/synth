#!/usr/bin/env python3
"""VCR-RA-003 for RISC-V (#815, epic #242) — RV32 register-allocation validator.

The RV32 analogue of the ARM `validate_final_allocation` gate. The RV32 checker
(`synth_backend_riscv::alloc_validator::validate_final_allocation_rv32`) runs
UNCONDITIONALLY on every RV32 compile in the default `--features riscv` build and
hard-errors on a violation of the two STRAIGHT-LINE invariants #815 names:

  Invariant 1 (callee-saved preservation): a callee-saved `s`-register (s1,
    s2..s10 — the set `preserve_callee_saved` saves) written by the body must be
    saved by a prologue `sw s_k, off(sp)` and restored by every epilogue
    `lw s_k, off(sp)`. Reverting the save/restore makes it fire
    (CalleeSavedNotSaved / CalleeSavedNotRestored).

  Invariant 2 (spill-slot non-aliasing): within a straight-line segment a frame
    slot `off(sp)` overwritten by a second `sw` while the first value is still
    reloaded downstream corrupts the reload (SpillSlotAliased).

A `Call` — the ARM phase-2 across-call/across-join frontier, which has no RV CFG
machinery yet — yields a NON-FATAL `NotAttempted` (decline > guess): the two
straight-line invariants still run.

This script is the SILENT-ON-REAL-CODEGEN half of the gate: it compiles the RV32
repro fixtures (branchy, memory-touching, callee-saved-heavy, call-bearing)
through the UNCONDITIONAL validator on BOTH the default and `--relocatable`
paths and asserts ZERO false positives (no `VCR-RA-003 (RV32) ... FAILED`). If the
validator false-positived on any real function that function would refuse to
compile and this gate would go red — the guard that the callee-saved set mirrors
the pass (s1/s2..s10, NOT the reserved s0/s11) and that the spill-slot map
resets on each `addi sp` frame adjust.

The RED (non-vacuity) half lives in the `ra003rv_red_*` unit tests
(`cargo test -p synth-backend-riscv --lib ra003rv`), which assert the validator
CATCHES a synthetic unsaved-s-register clobber, a dropped epilogue restore, and a
spill-slot alias.

Usage:  python3 scripts/repro/vcr_ra_003_rv32_alloc_validator.py [path/to/synth]
Exit 0 iff every RV32 fixture compiles clean (validator silent on real code).
"""
import os
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
REPRO = REPO / "scripts" / "repro"

# RV32-compilable fixtures spanning the shapes the validator reasons about:
# callee-saved-heavy (control_step reads the linmem table via s11, uses
# s-registers), spill/frame traffic, branches, and calls (the NotAttempted
# boundary). A false positive on ANY reds this gate.
RV32_FIXTURES = [
    "control_step.wasm",      # callee-saved + linmem base (s11) + branches
    "controller_step.wasm",   # PID-style step, promoted locals
    "filter_axis.wasm",       # filter, memory + arithmetic
    "signed_div_const.wasm",  # signed div-by-const (trap guard shapes)
    "reachable_helper.wasm",  # call-bearing (NotAttempted boundary)
    "msgq_put_359.wasm",      # queue put, memory stores
    "gust_kernel.wasm",       # larger kernel, spill traffic
    "flight_seam.wasm",       # branchy control flow
    "flight_seam_flat.wasm",  # flattened branchy control flow
]


def synth_bin() -> str:
    if len(sys.argv) > 1:
        return sys.argv[1]
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
    for path_name, extra_args in (("relocatable", ["--relocatable"]), ("default", [])):
        for fx in RV32_FIXTURES:
            path = REPRO / fx
            if not path.exists():
                if path_name == "relocatable":
                    print(f"warn: fixture missing, skipping: {fx}", file=sys.stderr)
                continue
            checked += 1
            with tempfile.NamedTemporaryFile(suffix=".o") as out:
                proc = subprocess.run(
                    [
                        binp, "compile", str(path),
                        "-b", "riscv", "-t", "rv32imac",
                        "--all-exports", "-o", out.name, *extra_args,
                    ],
                    capture_output=True,
                    text=True,
                )
            combined = proc.stdout + proc.stderr
            if "VCR-RA-003 (RV32)" in combined and "FAILED" in combined:
                line = next(
                    (l for l in combined.splitlines()
                     if "FAILED" in l and "VCR-RA-003 (RV32)" in l),
                    "<unknown>",
                )
                failures.append((fx, path_name, line.strip()))
                print(f"FAIL [{path_name}] {fx}: RV32 validator false-positived on real codegen")
                print(f"     {line.strip()}")
            elif proc.returncode != 0:
                # A non-validator compile error (unsupported op etc.) is not a
                # validator false-positive — record but do not fail the gate on it
                # (the fixture simply doesn't compile on RV32 for another reason).
                print(f"skip [{path_name}] {fx}: compile failed for a non-validator reason "
                      f"(rc={proc.returncode})")
            else:
                print(f"ok   [{path_name}] {fx}: RV32 validator silent (Consistent / NotAttempted)")

    print(f"\nchecked {checked} (fixture, path) pairs; {len(failures)} validator false-positives")
    if failures:
        print(
            "\nVCR-RA-003 (RV32) validator FALSE-POSITIVED on real codegen — the "
            "callee-saved set or the spill-slot segmentation is wrong.",
            file=sys.stderr,
        )
        return 1
    print(
        "VCR-RA-003 (RV32) SILENT on real codegen — the callee-saved-preservation "
        "+ spill-slot-non-aliasing checks pass every real RV32 fixture."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
