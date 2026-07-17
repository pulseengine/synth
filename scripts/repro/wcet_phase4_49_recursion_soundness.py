#!/usr/bin/env python3
"""#778 phase 4 (#49) recursion-bound soundness cross-check: execute a compiled
BOUNDED self-recursion under unicorn (Thumb-2) and confirm the composed
recursion bound is a sound upper bound on the ACTUAL total executed cost across
EVERY recursive frame — for the WORST-CASE entry over the whole i32 input domain.

The masked-recursion accept shape (`md`) bounds its controlling value to
`m = param & 15 ∈ [0,15]` for ANY runtime input, so the derived maximum depth is
15 (entry-independent) and the composed bound folds 16 frames. We drive the
worst-case entry (param & 15 == 15, e.g. param = 15 or 0xFFFFFFFF) and check:

  1. functional result (r0) matches the WASM ground truth (a lost frame or wrong
     fold would change it);
  2. composed bound_cycles >= total executed machine instructions across ALL
     frames (every machine instruction costs >= 1 cycle) — the recursion bound is
     a sound ceiling on the whole call tree, not one frame.

And the decline-honesty half: the uncapped countdown (`count`) and the two-self-
call tree (`fib`) STAY declined `recursion` even WITH a depth hint (moved, never
deleted) — with the specific rejection reason.

This is execution-side evidence the cargo gate (wcet_bound_gate.rs) cannot
produce in-CI (no unicorn dep there); the gate pins the same fixtures
analytically (derived depth 15, frame_count 16, bound == 16 x own, wrong-hint /
tree-recursion / uncapped-countdown decline matrix).

Usage:
    SYNTH=/path/to/synth python3 scripts/repro/wcet_phase4_49_recursion_soundness.py
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
TMP = "/tmp/wcet_phase4"

# A masked-recursion accept fixture: m = param & 15 in [0,15]; recurse while m != 0
# passing (m-1); base returns 0. Depth <= 15 entry-independent, for ANY input.
MASKED_WAT = r"""
(module
  (func $md (export "md") (param i32) (result i32)
    local.get 0 i32.const 15 i32.and
    (if (result i32)
      (then
        local.get 0 i32.const 15 i32.and i32.const 1 i32.sub call $md i32.const 1 i32.add)
      (else i32.const 0))))
"""

# Uncapped countdown: base at param==0, arg param-1 (NO mask on the arg path). Runtime
# unbounded (negative entry diverges); must REJECT any depth hint.
COUNT_WAT = r"""
(module
  (func $count (export "count") (param i32) (result i32)
    local.get 0 i32.eqz
    (if (result i32)
      (then i32.const 0)
      (else local.get 0 i32.const 1 i32.sub call $count i32.const 1 i32.add))))
"""

# Tree recursion (two self-calls per frame) even with a mask: depth x per-frame
# under-counts exponentially — must REJECT (single-self-call gate).
FIB_WAT = r"""
(module
  (func $fib (export "fib") (param i32) (result i32)
    local.get 0 i32.const 15 i32.and i32.const 2 i32.lt_s
    (if (result i32)
      (then i32.const 1)
      (else
        local.get 0 i32.const 15 i32.and i32.const 1 i32.sub call $fib
        local.get 0 i32.const 15 i32.and i32.const 2 i32.sub call $fib
        i32.add))))
"""


def wat_file(name, wat):
    p = os.path.join(TMP, name + ".wat")
    open(p, "w").write(wat)
    return p, os.path.join(TMP, name + ".elf")


def write_hints(name, fn, depth):
    p = os.path.join(TMP, name + ".hints.json")
    json.dump({"schema": "synth-wcet-hints-v1",
               "functions": {fn: {"recursion_depth": depth}}}, open(p, "w"))
    return p


def compile_wat(wat_path, elf_path, hints=None, relocatable=False):
    cmd = [SYNTH, "compile", wat_path, "-o", elf_path, "-t", "cortex-m4", "--emit-wcet"]
    if relocatable:
        cmd.append("--relocatable")
    if hints:
        cmd += ["--wcet-hints", hints]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    assert r.returncode == 0, r.stderr
    return json.load(open(elf_path + ".wcet.json"))


def md_ref(n):
    """Ground-truth: md(n) counts down m=n&15 to 0, returning m (each frame +1)."""
    m = n & 15
    return m


def main():
    os.makedirs(TMP, exist_ok=True)

    print("== masked recursion: composed bound >= WHOLE call tree (bound >= actual) ==")
    p, e = wat_file("masked", MASKED_WAT)
    hints = write_hints("masked", "md", 15)
    # Self-contained image so the self-call BL is patched to the in-image target.
    rep = compile_wat(p, e, hints=hints, relocatable=False)
    f = sidecar_entry(rep, "md")
    assert f["status"] == "bounded", f"md: expected bounded, got {f}"
    assert f["recursion"]["max_depth"] == 15, f"derived depth != 15: {f['recursion']}"
    assert f["recursion"]["frame_count"] == 16, f["recursion"]
    bound = f["cycles"]

    text, text_addr, syms = load_elf(e)
    # WORST-CASE entry: param & 15 == 15 → maximal 15-deep recursion. Also check a
    # large/negative entry (0xFFFFFFFF) which & 15 == 15 — the entry-independence.
    for arg in (15, 0xFFFFFFFF, 0x7FFFFFFF):
        r0, n_exec = run_func(text, text_addr, syms["md"], (arg,))
        assert r0 == md_ref(arg) & 0xFFFFFFFF, \
            f"md({arg:#x}): r0={r0} expected {md_ref(arg)}"
        assert bound >= n_exec, (
            f"md({arg:#x}): UNSOUND — recursion bound {bound} cycles < {n_exec} "
            f"executed machine insns across all frames"
        )
        print(f"  OK md({arg:#x})=r0 {r0}: executed {n_exec} insns (all frames)"
              f" <= composed bound {bound} cycles")

    print("== decline-honesty: uncapped countdown + tree recursion STAY declined ==")
    p, e = wat_file("count", COUNT_WAT)
    hints = write_hints("count", "count", 100)
    rep = compile_wat(p, e, hints=hints, relocatable=True)
    f = sidecar_entry(rep, "count")
    assert f["status"] == "declined" and f["reason"] == "recursion", f
    reasons = [r["reason"] for r in f.get("hint_rejections", [])]
    assert "hint-unverifiable-recursion" in reasons, f
    print("  OK count: declined `recursion` + hint-unverifiable-recursion "
          "(uncapped runtime param — no entry-independent ceiling)")

    p, e = wat_file("fib", FIB_WAT)
    hints = write_hints("fib", "fib", 15)
    rep = compile_wat(p, e, hints=hints, relocatable=True)
    f = sidecar_entry(rep, "fib")
    assert f["status"] == "declined" and f["reason"] == "recursion", f
    reasons = [r["reason"] for r in f.get("hint_rejections", [])]
    assert "hint-unverifiable-recursion" in reasons, f
    print("  OK fib: declined `recursion` + hint-unverifiable-recursion "
          "(two self-calls/frame — depth x per-frame would under-count)")

    # Wrong (too-low) hint on the provable masked shape → rejected below-derived.
    p, e = wat_file("masked", MASKED_WAT)
    hints = write_hints("masked_low", "md", 3)
    rep = compile_wat(p, e, hints=hints, relocatable=True)
    f = sidecar_entry(rep, "md")
    assert f["status"] == "declined" and f["reason"] == "recursion", f
    reasons = [r["reason"] for r in f.get("hint_rejections", [])]
    assert "hint-below-derived-depth" in reasons, f
    print("  OK md + too-low hint(3<15): declined `recursion` + hint-below-derived-depth")

    print("\nALL PHASE-4 (#49) RECURSION SOUNDNESS CHECKS PASSED")


if __name__ == "__main__":
    main()
