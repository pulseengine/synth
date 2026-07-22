#!/usr/bin/env python3
"""#778 phase 5 masked-ceiling loop-bound soundness cross-check: execute a
compiled BOUNDED data-dependent loop under unicorn (Thumb-2) and confirm the
derived masked-ceiling bound is a sound upper bound on the ACTUAL executed cost
for the WORST-CASE runtime input over the whole masked domain.

The masked-ceiling accept shape bounds its loop counter against a DATA-DEPENDENT
value `x & K ∈ [0, K]` for ANY runtime input `x`. synth derives the worst-case
trip as the MAX over both endpoints of that interval (`rhs = K` and `rhs = 0`) —
an entry-independent ceiling — and consumes it only under a verified
`--wcet-hints` `loop_bounds` entry. We drive the input that MAXIMIZES the real
trip and check:

  1. functional result (r0) matches the WASM ground truth;
  2. bound_cycles >= total executed machine instructions (every machine insn
     costs >= 1 cycle) — the masked-ceiling bound is a sound ceiling;
  3. ENTRY-INDEPENDENCE: several inputs (including the OTHER endpoint) all run
     within the SAME bound — the count-up worst case is `x&K == K`, the
     count-DOWN worst case is `x&K == 0`, and the both-endpoints max covers both.

The load-bearing red half (the decline moved, not deleted):
  - an UNMASKED data-dependent loop (`i < param`) STAYS declined `loop` even
    WITH a hint (`hint-unverifiable-induction`) — the mask is the discriminator;
  - a too-low hint (< derived) is REJECTED `hint-below-derived-trip`;
  - unhinted, the masked loop STAYS declined `loop` (opt-in gate).

This is execution-side evidence the cargo gate (wcet_bound_gate.rs) cannot
produce in-CI (no unicorn dep there); the gate pins the same fixtures
analytically (derived trip, source mask-ceiling, bound >= trip x region, and the
reject matrix).

Usage:
    SYNTH=/path/to/synth python3 scripts/repro/wcet_phase5_778_masked_loop_soundness.py
Requires: pip install unicorn pyelftools
"""
import json
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from wcet_phase2_778_unicorn_soundness import (  # noqa: E402
    load_elf, run_func, sidecar_entry,
)

SYNTH = os.environ.get("SYNTH", "synth")
TMP = "/tmp/wcet_phase5"

# COUNT-UP masked bound: counter i from 0, exit when i < (param & 7) is false.
# Real trips = param & 7 (<= 7). Worst case param & 7 == 7 → 7 trips. Sum 0..i.
UP_WAT = r"""
(module
  (func (export "maskloop") (param i32) (result i32)
    (local i32 i32)
    (block
      (loop
        local.get 1 local.get 0 i32.const 7 i32.and i32.lt_s i32.eqz br_if 1
        local.get 2 local.get 1 i32.add local.set 2
        local.get 1 i32.const 1 i32.add local.set 1
        br 0))
    local.get 2))
"""

# COUNT-DOWN masked bound: counter starts at 10, decrements, exit when
# counter > (param & 7) is false. Real trips = 10 - (param & 7). WORST case is
# param & 7 == 0 → 10 trips. A NAIVE single-endpoint seed (rhs=7) would derive
# 3 → an UNSOUND bound below the real 10-iteration execution. The both-endpoints
# max derives 10.
DOWN_WAT = r"""
(module
  (func (export "cd") (param i32) (result i32)
    (local i32 i32)
    (local.set 1 (i32.const 10))
    (block
      (loop
        local.get 1 local.get 0 i32.const 7 i32.and i32.gt_s i32.eqz br_if 1
        local.get 2 i32.const 1 i32.add local.set 2
        local.get 1 i32.const 1 i32.sub local.set 1
        br 0))
    local.get 2))
"""

# UNMASKED data-dependent bound (`i < param`): the discriminator negative. No
# mask → no entry-independent ceiling → STAYS declined even with a hint.
UNMASKED_WAT = r"""
(module
  (func (export "spin") (param i32) (result i32)
    (local i32)
    (block
      (loop
        local.get 1 local.get 0 i32.lt_s i32.eqz br_if 1
        local.get 1 i32.const 1 i32.add local.set 1
        br 0))
    local.get 1))
"""


def wat_file(name, wat):
    p = os.path.join(TMP, name + ".wat")
    open(p, "w").write(wat)
    return p, os.path.join(TMP, name + ".elf")


def write_hints(name, fn, bounds):
    p = os.path.join(TMP, name + ".hints.json")
    json.dump({"schema": "synth-wcet-hints-v1",
               "functions": {fn: {"loop_bounds": bounds}}}, open(p, "w"))
    return p


def compile_wat(wat_path, elf_path, hints=None):
    cmd = [SYNTH, "compile", wat_path, "-o", elf_path, "-t", "cortex-m4", "--emit-wcet"]
    if hints:
        cmd += ["--wcet-hints", hints]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    assert r.returncode == 0, r.stderr
    return json.load(open(elf_path + ".wcet.json"))


def up_ref(param):
    m = param & 7
    return sum(range(m))  # 0+1+..+(m-1)


def down_ref(param):
    m = param & 7
    return max(0, 10 - m)  # counter 10 down to m, counting iterations


def loop_src(f):
    return f.get("loops", [{}])[0].get("source")


def main():
    os.makedirs(TMP, exist_ok=True)

    print("== count-UP masked ceiling: bound >= actual for worst-case input ==")
    p, e = wat_file("up", UP_WAT)
    hints = write_hints("up", "maskloop", [7])  # ceiling K = 7
    rep = compile_wat(p, e, hints=hints)
    f = sidecar_entry(rep, "maskloop")
    assert f["status"] == "bounded", f"maskloop: expected bounded, got {f}"
    assert loop_src(f) == "mask-ceiling", f"expected mask-ceiling source: {f}"
    assert f["loops"][0]["trip_count"] == 7, f"derived trip != 7: {f['loops']}"
    bound = f["cycles"]
    text, text_addr, syms = load_elf(e)
    # WORST case is param & 7 == 7 (max trips). Entry-independence: every input,
    # including the OTHER endpoint (param&7==0 → 0 trips), runs within the bound.
    for arg in (7, 0xFFFFFFFF, 0x7FFFFFFF, 0, 3, 8):
        r0, n = run_func(text, text_addr, syms["maskloop"], (arg,))
        assert r0 == up_ref(arg) & 0xFFFFFFFF, f"maskloop({arg:#x}): r0={r0} != {up_ref(arg)}"
        assert bound >= n, (
            f"maskloop({arg:#x}): UNSOUND — masked bound {bound} cyc < {n} executed insns")
        print(f"  OK maskloop({arg:#x})=r0 {r0}: {n} insns <= bound {bound} cyc")

    print("== count-DOWN masked ceiling: worst case is the OTHER endpoint (rhs=0) ==")
    p, e = wat_file("down", DOWN_WAT)
    hints = write_hints("down", "cd", [10])  # derived 10 (the rhs=0 endpoint)
    rep = compile_wat(p, e, hints=hints)
    f = sidecar_entry(rep, "cd")
    assert f["status"] == "bounded", f"cd: expected bounded, got {f}"
    assert loop_src(f) == "mask-ceiling", f
    assert f["loops"][0]["trip_count"] == 10, (
        f"UNSOUND single-endpoint: count-down trip must be 10 (rhs=0), got "
        f"{f['loops'][0]['trip_count']} — a naive rhs=7 seed would give 3")
    bound = f["cycles"]
    text, text_addr, syms = load_elf(e)
    for arg in (0, 8, 0xFFFFFFF8, 7, 0xFFFFFFFF, 3):
        r0, n = run_func(text, text_addr, syms["cd"], (arg,))
        assert r0 == down_ref(arg) & 0xFFFFFFFF, f"cd({arg:#x}): r0={r0} != {down_ref(arg)}"
        assert bound >= n, (
            f"cd({arg:#x}): UNSOUND — masked bound {bound} cyc < {n} executed insns "
            f"(count-down worst case is param&7==0 → 10 trips)")
        print(f"  OK cd({arg:#x})=r0 {r0}: {n} insns <= bound {bound} cyc")

    print("== decline-honesty: the decline MOVED, not deleted ==")
    # Unhinted masked loop STAYS declined `loop` (opt-in gate).
    p, e = wat_file("up", UP_WAT)
    rep = compile_wat(p, e, hints=None)
    f = sidecar_entry(rep, "maskloop")
    assert f["status"] == "declined" and f["reason"] == "loop", f
    print("  OK maskloop unhinted: declined `loop` (masked bound is opt-in)")

    # Too-low hint (< derived 7) REJECTED below-derived.
    hints = write_hints("up_low", "maskloop", [3])
    rep = compile_wat(p, e, hints=hints)
    f = sidecar_entry(rep, "maskloop")
    assert f["status"] == "declined" and f["reason"] == "loop", f
    reasons = [r["reason"] for r in f.get("hint_rejections", [])]
    assert "hint-below-derived-trip" in reasons, f
    print("  OK maskloop + too-low hint(3<7): declined `loop` + hint-below-derived-trip")

    # UNMASKED data-dependent loop STAYS declined even WITH a hint — the mask is
    # the discriminator (param is symbolic Top, never Masked).
    p, e = wat_file("unmasked", UNMASKED_WAT)
    hints = write_hints("unmasked", "spin", [100])
    rep = compile_wat(p, e, hints=hints)
    f = sidecar_entry(rep, "spin")
    assert f["status"] == "declined" and f["reason"] == "loop", \
        f"UNSOUND — unmasked `i < param` was BOUNDED (no entry-independent ceiling): {f}"
    reasons = [r["reason"] for r in f.get("hint_rejections", [])]
    assert "hint-unverifiable-induction" in reasons, f
    print("  OK spin (unmasked i<param) + hint: declined `loop` + "
          "hint-unverifiable-induction (mask is the discriminator)")

    print("\nALL PHASE-5 (#778) MASKED-CEILING LOOP SOUNDNESS CHECKS PASSED")


if __name__ == "__main__":
    main()
