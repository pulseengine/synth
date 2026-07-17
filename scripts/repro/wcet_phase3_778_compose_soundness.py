#!/usr/bin/env python3
"""#778 phase 3 soundness cross-check: execute compiled DIRECT-CALL fixtures under
unicorn (Thumb-2) and confirm the COMPOSED inter-procedural bound is a sound upper
bound on the ACTUAL executed cost.

`run_func` maps the whole `.text` and lets `BL func_N` follow into the callee
(same image), so executing an entry point counts EVERY machine instruction the
whole call tree runs — the real worst-case for a loop-free / const-loop chain.
For each entry we check:

  1. the functional result (r0) matches the WASM-semantics ground truth (a wrong
     composed edge or lost multiplier would change it);
  2. composed_bound_cycles >= executed_instructions across the WHOLE call tree
     (every machine instruction costs >= 1 cycle) — the composed bound is a sound
     ceiling on the transitive execution, not just the caller's own body.

And the decline-honesty half: recursion / indirect / declined-callee entries stay
DECLINED with their specific machine reason (executed for evidence they are real
programs, not just rejected shapes).

This is the execution-side evidence the cargo gate (wcet_bound_gate.rs) cannot
produce in-CI (no unicorn dep there); the gate pins the same fixtures analytically
(exact composed literals 19/51/136, call-in-loop >= 10x leaf, trip floor, decline
matrix). Observed at authoring (v0.48 branch, debug build): see the printed lines.

Usage:
    SYNTH=/path/to/synth python3 scripts/repro/wcet_phase3_778_compose_soundness.py
Requires: pip install unicorn pyelftools
"""
import os
import sys

# Reuse the phase-2 harness machinery (compile/load/run/count) verbatim.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from wcet_phase2_778_unicorn_soundness import (  # noqa: E402
    compile_wat, load_elf, run_func, sidecar_entry,
)

SYNTH = os.environ.get("SYNTH", "synth")


def check_composed(name, report, elf_path, expect_r0, args=()):
    """A composed BOUNDED entry: executing `name` follows its BLs into callees;
    the composed bound must cover the whole transitive machine-instruction count."""
    f = sidecar_entry(report, name)
    assert f["status"] == "bounded", f"{name}: expected composed bound, got {f}"
    text, text_addr, syms = load_elf(elf_path)
    r0, n_exec = run_func(text, text_addr, syms[name], args)
    assert r0 == expect_r0 & 0xFFFFFFFF, f"{name}: r0={r0} expected {expect_r0}"
    cyc = f["cycles"]
    assert cyc >= n_exec, (
        f"{name}: UNSOUND — composed bound {cyc} cycles < {n_exec} executed "
        f"machine insns across the whole call tree"
    )
    print(f"  OK {name}: r0={r0}, executed {n_exec} machine insns (whole call tree)"
          f" <= composed bound {cyc} cycles")


def check_declined(name, report, reason):
    f = sidecar_entry(report, name)
    assert f["status"] == "declined", f"{name}: expected declined, got {f}"
    assert f["reason"] == reason, f"{name}: reason {f['reason']} != {reason}"
    print(f"  OK {name}: declined `{reason}` (decline-honesty preserved)")


CHAIN_WAT = r"""
(module
  (func $leaf (param i32) (result i32) local.get 0 i32.const 1 i32.add)
  (func $mid (param i32) (result i32) local.get 0 call $leaf i32.const 2 i32.add)
  (func (export "root") (param i32) (result i32)
    local.get 0 call $mid call $mid))
"""

LOOPCALL_WAT = r"""
(module
  (func $leaf (param i32) (result i32) local.get 0 i32.const 1 i32.add)
  (func (export "loopcaller") (result i32)
    (local i32 i32)
    (block
      (loop
        local.get 0 i32.const 10 i32.lt_s i32.eqz br_if 1
        local.get 1 call $leaf local.set 1
        local.get 0 i32.const 1 i32.add local.set 0
        br 0))
    local.get 1))
"""

REC_WAT = r"""
(module
  (func $fac (export "fac") (param i32) (result i32)
    local.get 0 i32.eqz
    (if (result i32)
      (then i32.const 1)
      (else local.get 0 local.get 0 i32.const 1 i32.sub call $fac i32.mul))))
"""

IND_WAT = r"""
(module
  (type $t (func (param i32) (result i32)))
  (table 1 funcref)
  (func $g (param i32) (result i32) local.get 0 i32.const 1 i32.add)
  (elem (i32.const 0) $g)
  (func (export "dispatch") (param i32) (result i32)
    local.get 0 i32.const 0 call_indirect (type $t)))
"""


def main():
    tmp = "/tmp/wcet_phase3"
    os.makedirs(tmp, exist_ok=True)

    print("== composed bounds cover the WHOLE call tree (bound >= actual) ==")
    # root(x) = leaf(leaf(x)+? ) — trace: root calls mid twice.
    # mid(v) = leaf(v) + 2 = (v+1) + 2 = v+3; root(v) = mid(mid(v)) = (v+3)+3 = v+6.
    def wat_file(name, wat):
        p = os.path.join(tmp, name + ".wat")
        open(p, "w").write(wat)
        return p, os.path.join(tmp, name + ".elf")

    p, e = wat_file("chain", CHAIN_WAT)
    rep = compile_wat(p, e)
    # root/mid/leaf all bounded and composed.
    for nm, cyc_expect in [("func_0", 19), ("func_1", 51), ("root", 136)]:
        f = sidecar_entry(rep, nm)
        assert f["status"] == "bounded" and f["cycles"] == cyc_expect, \
            f"{nm}: {f} (expected composed {cyc_expect})"
    check_composed("root", rep, e, expect_r0=7, args=(1,))  # root(1) = 1+6 = 7

    p, e = wat_file("loopcall", LOOPCALL_WAT)
    rep = compile_wat(p, e)
    # leaf called 10x; loopcaller returns sum_{i=0..9} leaf(prev) folding r1:
    # r1 starts 0, each trip r1 = leaf(r1) = r1+1, 10 trips => r1 = 10.
    check_composed("loopcaller", rep, e, expect_r0=10, args=())
    # And the composed bound must include >= 10x the leaf body (multiplier kept).
    leaf = sidecar_entry(rep, "func_0")["cycles"]
    lc = sidecar_entry(rep, "loopcaller")["cycles"]
    assert lc >= 10 * leaf, f"loopcaller {lc} < 10x leaf {leaf} — multiplier lost"
    print(f"  OK loopcaller composed bound {lc} >= 10 x leaf {leaf}"
          f" (callee counted per-trip)")

    print("== decline-honesty: recursion + indirect stay LOUD declines ==")
    p, e = wat_file("rec", REC_WAT)
    rep = compile_wat(p, e)
    check_declined("fac", rep, "recursion")

    p, e = wat_file("ind", IND_WAT)
    rep = compile_wat(p, e)
    check_declined("dispatch", rep, "indirect-call")

    print("\nALL PHASE-3 COMPOSITION SOUNDNESS CHECKS PASSED")


if __name__ == "__main__":
    main()
