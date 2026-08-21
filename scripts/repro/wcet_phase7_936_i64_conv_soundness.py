#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 4
"""RQ-59-WCETI64 (#936 residual) soundness cross-check: the #936 audit's four
remaining real direct-selector emissions — `I32WrapI64`, `I64ExtendI32S`,
`I64ExtendI32U`, `I64Sub` — are now PRICED (bounded), not declined, in the
WCET cycle model. Compile four fixtures via `--relocatable` (#197: the ONLY
compile path that reaches these pseudo-ops as real `ArmOp`s), execute each
under unicorn (Thumb-2), and confirm:

  1. the functional result matches the WASM-semantics ground truth (a wrong
     ASR sign-fill, a dropped high-word clear — the #916 class — or a wrong
     low-word move would change it);
  2. bound_cycles >= executed machine instructions (every machine
     instruction costs >= 1 cycle) — the priced bound is a sound ceiling on
     the ACTUAL execution, not a guessed constant.

The fixture set is the measured RQ-59 step ledger:

  - `w`  (`i32.wrap_i64` leaf) and `narrow` (`i64.load` + `i64.add` +
    `i32.wrap_i64`, the #936 "narrow an i64 read to i32" OS shape) declined
    `unmodeled-op op=I32WrapI64` before this fix;
  - `es` (`i64.extend_i32_s` leaf) declined `unmodeled-op op=I64ExtendI32S`;
  - `eu` (`i64.extend_i32_u` leaf) is the CONTROL: it bounded BEFORE the fix
    (RQ-58-SELDSL's rule emits raw Mov/Movw primitives), so its pass here
    pins that pricing the pseudo did not disturb the already-bounded path.

`I64Sub` has no unicorn fixture ON PURPOSE: its only real emission today is
inside the f64 trunc-sat decompose, which does not even COMPILE on a sound
core (cortex-m4 has no double-precision FPU — measured: "no functions
compiled successfully"), so there is no reachable stream to execute. Its
price is pinned analytically in the `synth-backend` unit tests
(`i64_sub_is_bounded`: SUBS + SBC.W = 6 B -> 15 cycles).

The `narrow` seed is chosen so the i64.add CARRIES across the word boundary
(0xFFFFFFFE + 3 = 0x1_00000001 -> wrap = 1): a bound-only harness would pass
with a broken ADDS/ADC pair, this result does not.

This is the execution-side evidence the cargo gate cannot produce in-CI (no
unicorn dep there); the gate (`wcet_bound_gate.rs`) pins the same fixtures'
exact cycle literals (28 / 80 / 39 / 16 at authoring, debug build,
cortex-m4).

Usage:
    SYNTH=/path/to/synth python3 scripts/repro/wcet_phase7_936_i64_conv_soundness.py
Requires: pip install unicorn pyelftools
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from wcet_phase2_778_unicorn_soundness import load_elf, sidecar_entry  # noqa: E402
from wcet_phase6_936_i64_leaf_soundness import (  # noqa: E402
    MEM_BASE,
    compile_wat_relocatable,
    run_leaf,
)

WRAP_WAT = r"""
(module
  (memory 1)
  (func (export "w") (param i64) (result i32)
    local.get 0
    i32.wrap_i64))
"""

NARROW_WAT = r"""
(module
  (memory 1)
  (func (export "narrow") (param i32) (result i32)
    local.get 0 i64.load i64.const 3 i64.add i32.wrap_i64))
"""

EXT_S_WAT = r"""
(module
  (func (export "es") (param i32) (result i64)
    local.get 0
    i64.extend_i32_s))
"""

EXT_U_WAT = r"""
(module
  (func (export "eu") (param i32) (result i64)
    local.get 0
    i64.extend_i32_u))
"""


def check(name, wat, args, expect, mem_writes=(), expect_hi=None):
    open(f"{name}.wat", "w").write(wat)
    report = compile_wat_relocatable(f"{name}.wat", f"{name}.o")
    f = sidecar_entry(report, name)
    assert f["status"] == "bounded", f"{name}: expected bounded, got {f}"
    text, text_addr, syms = load_elf(f"{name}.o")
    r0, r1, n, _ = run_leaf(text, text_addr, syms[name], args=args,
                            mem_writes=mem_writes)
    assert r0 == expect, f"{name}: r0 = {r0:#x}, expected {expect:#x}"
    if expect_hi is not None:
        assert r1 == expect_hi, f"{name}: r1 = {r1:#x}, expected {expect_hi:#x}"
    bound = f["cycles"]
    assert bound >= n, f"{name}: UNSOUND — bound {bound} cycles < {n} executed insns"
    print(f"  OK {name}: r0={r0:#x} r1={r1:#x}, {n} insns <= bound {bound} cycles")


def main():
    d = os.environ.get("WCET_REPRO_DIR", "/tmp/wcet_phase7_936_repro")
    os.makedirs(d, exist_ok=True)
    os.chdir(d)

    print("== I32WrapI64: i32.wrap_i64 leaf (i64 param in r0:r1, low word out) ==")
    check("w", WRAP_WAT, (0x11223344, 0xAABBCCDD), 0x11223344)

    print("== I32WrapI64 behind priced i64 ops: the #936 narrow OS shape ==")
    print("   (seed 0xFFFFFFFE + 3 carries across the word boundary -> 1)")
    check(
        "narrow", NARROW_WAT, (16,), 0x00000001,
        mem_writes=[(MEM_BASE + 16, (0xFFFFFFFE).to_bytes(8, "little"))],
    )

    print("== I64ExtendI32S: sign-extend a NEGATIVE i32 (-5) ==")
    check("es", EXT_S_WAT, (0xFFFFFFFB,), 0xFFFFFFFB, expect_hi=0xFFFFFFFF)

    print("== I64ExtendI32U (control, bounded pre-fix): zero-extend sign-bit-set ==")
    check("eu", EXT_U_WAT, (0x80000001,), 0x80000001, expect_hi=0)

    print("\nALL PHASE-7 (RQ-59-WCETI64 / #936 residual) CONVERSION SOUNDNESS CHECKS PASSED")


if __name__ == "__main__":
    sys.exit(main())
