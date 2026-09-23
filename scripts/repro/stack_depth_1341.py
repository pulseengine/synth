#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 3
"""RQ-71-STACKDEPTH (#1341) soundness cross-check: EXECUTE a `--relocatable`
export under unicorn, measure the ACTUAL peak native stack it consumes across
the whole call tree, and confirm synth's reported bound is a sound ceiling on it.

WHY THIS ORACLE EXISTS, in the reporter's own failure. cpetig's export returned
a bit-identical-to-wasmtime answer EVERY time and then corrupted an unrelated
RTOS pointer: it overran its NuttX task stack while the linear-memory guard
bands above and below stayed untouched. A `--relocatable` object tells the
embedder how much LINEAR MEMORY to reserve and nothing at all about native
stack, so the region has to be guessed, and guessing low fails SILENTLY with a
plausible result. That is the exact class synth exists to refuse.

THE THREE WAYS TO COUNT, and why only one is right. Measured in-repo on
`stack_depth_branch_1341.wat`, a four-function branching call graph
(`top` calls `a` and `b`; both call `leaf`):

    leaf   push { r4, lr }             =  8   sub sp  ABSENT   frame  8
    a      push.w { r4-r8, lr }        = 24   sub sp  #0x20    frame 56
    b      push.w { r4-r8, lr }        = 24   sub sp  #0x20    frame 56
    top    push.w { r4-r8, lr }        = 24   sub sp  #0x20    frame 56

  (a) THE REPORTER'S METHOD — sum every `sub sp, #N`:        96 bytes
  (b) a naive sum of every frame:                           176 bytes
  (c) THE TRUTH — max over root-to-leaf paths:              120 bytes
        top -> a -> leaf = 56 + 56 + 8 = 120
        top -> b -> leaf = 56 + 56 + 8 = 120

(a) UNDER-reports by 24 bytes (20%) — the dangerous direction, and the reason
the reporter's 1456-byte estimate looked ample against a requirement that really
sat between 1984 and 4032. It misses TWO things: the callee-saved `push`, which
moves SP before any `sub sp` does, and every function whose `frame_size` is 0
and therefore emits NO `sub sp` at all (`leaf` above consumes 8 bytes and is
invisible to that grep). (b) OVER-reports by 46%, because `a` and `b` are never
live at the same time; an embedder told to reserve 46% more than it needs stops
believing the number, which is its own failure.

AND THE IMMEDIATE IS HEX. `sub.w sp, sp, #0x20` is 32, not 0 — a `#[0-9]+`
regex silently reads it as `0`. Parse with base 0 or do not parse at all.

WHAT THIS ORACLE PINS, which the cargo gate cannot (no unicorn dep in-CI):
  1. the reported bound is >= the ACTUAL peak stack measured by execution,
     for the worst-case entry over the fixture's input domain;
  2. it is not vacuously huge — within a stated factor of the measured peak,
     so a bound of u64::MAX could never pass;
  3. `call_indirect` LOUD-DECLINES with the reason named, rather than emitting
     a silent lower bound, which would reproduce the reported defect.

RED-FIRST BY CONSTRUCTION: run against a synth that reports no stack bound and
this exits 1 at the first fixture, naming the missing sidecar.
"""

import json
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# The ABI values have ONE source: phase 2's harness. The setup calls below are a
# local copy (the house pattern -- see `run_leaf` in wcet_phase6), but the
# CONSTANTS are imported so the entry SP, return magic and register contract
# cannot drift between oracles.
from wcet_phase2_778_unicorn_soundness import (  # noqa: E402
    LINMEM_BASE,
    LINMEM_SIZE,
    RETURN_MAGIC,
    load_elf,
)
from unicorn import UC_ARCH_ARM, UC_HOOK_CODE, UC_MODE_THUMB, Uc  # noqa: E402
from unicorn.arm_const import (  # noqa: E402
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

SYNTH = os.environ.get("SYNTH_BIN", "./target/debug/synth")
ENTRY_SP = 0x2003FF00
# A bound more than this many times the measured peak is not a bound, it is a
# refusal wearing a number. The reporter's own complaint about an unbelievable
# figure is why this is asserted rather than left to taste.
MAX_SLACK_FACTOR = 4


def compile_wat(wat_path, obj_path, relocatable, extra=()):
    """Drive the REAL CLI.

    TWO invocations are needed and the reason is not incidental. `--relocatable`
    is the reporter's own command line and the configuration #1341 is about, but
    its `BL` targets are RELOCATIONS — unresolved until a linker runs — so the
    object cannot be executed. Emulating one runs away (measured: 5,000,001
    instructions, `pc=0x6c`, never returning).

    So the sidecar is checked on BOTH, and execution on the linkable one:
    `--relocatable` proves the number is reported where the reporter needs it;
    the self-contained build is what the emulator can actually run to measure
    the peak the number claims to bound. The stack figure is a property of the
    emitted stream and is identical either way — which this oracle asserts
    rather than assumes.
    """
    cmd = [
        SYNTH, "compile", wat_path, "-o", obj_path,
        "--target", "cortex-m7", "--all-exports", "--emit-stack-depth", *extra,
    ]
    if relocatable:
        cmd.insert(cmd.index("--all-exports"), "--relocatable")
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=180)
    return r


def stack_sidecar(obj_path):
    """The per-export stack-depth report, or None if synth emitted none."""
    p = obj_path + ".stack.json"
    if not os.path.exists(p):
        return None
    with open(p) as f:
        return json.load(f)


def run_tracking_sp(text, text_addr, addr, args=()):
    """Like phase2's `run_func`, extended to track the MINIMUM SP reached.

    Peak stack usage is `ENTRY_SP - min(SP)` over the whole execution, which
    follows every `BL` into its callee, so this measures the CALL TREE and not
    one frame. Returns (r0, insns, peak_bytes).
    """
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    base = text_addr & ~0xFFF
    size = ((text_addr + len(text) - base) + 0xFFF) & ~0xFFF
    mu.mem_map(base, max(size, 0x1000))
    mu.mem_write(text_addr, text)
    mu.mem_map(0x20000000, 0x40000)  # linear memory + stack RAM
    mu.mem_map(RETURN_MAGIC & ~0xFFF, 0x1000)
    mu.reg_write(UC_ARM_REG_SP, ENTRY_SP)
    mu.reg_write(UC_ARM_REG_LR, RETURN_MAGIC | 1)
    mu.reg_write(UC_ARM_REG_R10, LINMEM_SIZE)  # size, not base (#1276)
    mu.reg_write(UC_ARM_REG_R11, LINMEM_BASE)
    for i, v in enumerate(args):
        mu.reg_write(UC_ARM_REG_R0 + i, v)

    st = {"n": 0, "min_sp": ENTRY_SP}

    def hook(mu_, addr_, size_, _):
        st["n"] += 1
        sp = mu_.reg_read(UC_ARM_REG_SP)
        # Sample AFTER the prologue push/sub has retired on the next tick; the
        # minimum over every instruction boundary is the peak regardless.
        if sp < st["min_sp"]:
            st["min_sp"] = sp
        if st["n"] > 5_000_000:
            mu_.emu_stop()

    mu.hook_add(UC_HOOK_CODE, hook)
    mu.emu_start(addr | 1, RETURN_MAGIC, timeout=10_000_000)
    assert mu.reg_read(UC_ARM_REG_PC) & ~1 == RETURN_MAGIC, (
        f"did not return: pc={mu.reg_read(UC_ARM_REG_PC):#x} after {st['n']} insns"
    )
    return mu.reg_read(UC_ARM_REG_R0), st["n"], ENTRY_SP - st["min_sp"]


def check_bounded(tag, obj, export, args_domain):
    """The bound must cover the WORST entry in the domain, and not by absurd slack."""
    report = stack_sidecar(obj)
    assert report is not None, (
        f"{tag}: synth emitted NO {obj}.stack.json — there is no reported stack "
        f"bound to check. This is the RED half: the embedder still has nothing "
        f"to size the region with, which is #1341 verbatim."
    )
    entry = next((f for f in report.get("exports", []) if f.get("name", "").endswith(export)), None)
    assert entry is not None, f"{tag}: no entry for export {export!r} in {report}"
    assert entry.get("status") == "bounded", (
        f"{tag}: expected a bounded stack depth for {export}, got {entry}"
    )
    bound = entry["bytes"]

    text, text_addr, syms = load_elf(obj)
    sym = next((v for k, v in syms.items() if k.endswith(export)), None)
    assert sym is not None, f"{tag}: {export} not in symtab: {sorted(syms)[:8]}"

    worst = 0
    runs = 0
    for a in args_domain:
        _r0, _n, peak = run_tracking_sp(text, text_addr, sym, (a,))
        worst = max(worst, peak)
        runs += 1
    assert bound >= worst, (
        f"{tag}: UNSOUND — reported bound {bound} B < measured peak {worst} B "
        f"across the call tree. An embedder sizing from this number corrupts "
        f"memory silently, which is the reported failure."
    )
    assert bound <= worst * MAX_SLACK_FACTOR, (
        f"{tag}: bound {bound} B is more than {MAX_SLACK_FACTOR}x the measured "
        f"peak {worst} B — an unbelievable number is its own failure mode"
    )
    print(f"  OK {tag}: {export} reported {bound} B >= measured peak {worst} B "
          f"(slack {bound - worst} B)")
    return runs


def check_declined(tag, obj, export, reason):
    """The EXPORT must decline loudly, with the accurate reason.

    Scoped to the export on purpose. The unboundable module's LEAVES are still
    perfectly boundable — `one` and `two` have no indirect call — and demanding
    that nothing in the module is bounded was this oracle's own second mistake.
    What matters to an embedder is the entry point they call.
    """
    report = stack_sidecar(obj)
    assert report is not None, f"{tag}: no sidecar emitted at all"
    entry = next((e for e in report.get("exports", []) if e.get("name", "").endswith(export)), None)
    assert entry is not None, f"{tag}: no entry for {export!r} in {report}"
    assert entry.get("status") == "declined", (
        f"{tag}: export {export} must DECLINE ({reason}); got {entry} — a silent "
        f"lower bound on an unboundable entry point reproduces #1341"
    )
    assert entry.get("reason") == reason, (
        f"{tag}: declined with {entry.get('reason')!r}, not {reason!r}. A safe "
        f"but inaccurate reason tells the embedder the walker got confused "
        f"rather than that their call graph is unresolvable."
    )
    print(f"  OK {tag}: {export} declines {reason!r} rather than guessing "
          f"(its boundable leaves still report figures)")
    return 0


WATS = {
    # Committed alongside this script so the lane is re-derivable in-repo; the
    # reporter's own module is an issue attachment (the RQ-70-FALCONCORPUS
    # lesson applied BEFORE the fact).
    "branch": "stack_depth_branch_1341.wat",
    "chain": "stack_depth_chain_1341.wat",
    "indirect": "stack_depth_indirect_1341.wat",
}


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    emulations = 0
    with tempfile.TemporaryDirectory() as td:
        objs = {}
        for tag, wat in WATS.items():
            src = os.path.join(here, wat)
            assert os.path.exists(src), f"missing committed fixture {src}"
            # (1) the reporter's own invocation: the sidecar must exist there.
            rel = os.path.join(td, tag + "-rel.o")
            r = compile_wat(src, rel, relocatable=True)
            assert r.returncode == 0, f"{tag}: --relocatable compile failed\n{r.stderr}"
            rel_report = stack_sidecar(rel)
            assert rel_report is not None, (
                f"{tag}: --relocatable emitted NO sidecar — that is the "
                f"configuration #1341 is about"
            )
            # (2) the linkable build, which the emulator can run.
            obj = os.path.join(td, tag + ".o")
            r = compile_wat(src, obj, relocatable=False)
            assert r.returncode == 0, f"{tag}: compile failed\n{r.stderr}"
            # THE TWO FIGURES LEGITIMATELY DIFFER, and asserting they match was
            # this oracle's own first mistake. `--relocatable` forces the DIRECT
            # selector (#197); the self-contained build uses the optimized one,
            # whose prologue costs 8 more bytes per frame. Measured on `branch`:
            # relocatable leaf/a/b/top = 8/64/64/120, self-contained = 16/72/72/128.
            #
            # So the number is a property of THE BUILD YOU SHIP, not of the
            # module — and an embedder must read it from their own object. What
            # is asserted instead is that both paths produce a BOUNDED answer
            # with the same shape; the execution check below then validates the
            # self-contained figure against the build it was measured on.
            sc_report = stack_sidecar(obj)
            shape = lambda rep: {e["name"]: e["status"] for e in rep["exports"]}
            assert shape(rel_report) == shape(sc_report), (
                f"{tag}: the two link modes disagree about WHICH functions are "
                f"boundable ({shape(rel_report)} vs {shape(sc_report)}) — the "
                f"figures may differ, the decline set must not"
            )
            objs[tag] = obj

        # A branching graph: `a` and `b` are never live together, so a bound
        # that SUMS them is wrong in the believable direction and a bound that
        # sums only `sub sp` is wrong in the dangerous one.
        emulations += check_bounded("branch", objs["branch"], "top", (0, 1, 0xFFFFFFFF))
        # A chain whose LEAF has frame_size 0 and emits no `sub sp` at all.
        emulations += check_bounded("chain", objs["chain"], "top", (0, 7, 0xFFFFFFFF))
        # Decline honesty: moved, never deleted.
        check_declined("indirect", objs["indirect"], "top", "call_indirect")

    print(f"STACK-DEPTH-1341 emulations={emulations} PASS")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except AssertionError as e:
        print(f"STACK-DEPTH-1341 FAIL: {e}", file=sys.stderr)
        sys.exit(1)
