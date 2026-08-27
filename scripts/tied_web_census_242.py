#!/usr/bin/env python3
# NOTE on home: this lives in scripts/ (with claim_check.py and
# tier_census_1021.py — derivation/audit tooling over shipped artifacts), not
# scripts/repro/ (defect oracles; their `# ci-status: manual` ceiling is
# count-max 8 and AT 8). It is RQ-60-RACOST increment 1's measurement
# artifact, report-and-stop by scope: it attributes the graph-colouring
# allocator's `single-block` declines to their increment-1 sub-cause, so the
# tied-operand web merge has a re-derivable BEFORE/AFTER population instead of
# a remembered one. The enforcing correctness gates over the merge itself are
# the wired VCR-DEC-001 differentials + VCR-RA-003.
"""RQ-60-RACOST increment 1 (#242) — the `single-block` decline census.

The v0.60 artifact claims "49 of 71 single-block declines" are the
read-modify-write colour-mismatch shape (an RMW field's use-side and def-side
value ranges coloured independently, the mismatch caught after the fact by
`rewrite_op`).  That figure predates the change this lane makes, so this
script RE-DERIVES it from the shipped binary's own `SYNTH_GRAPH_ALLOC_STATS`
stream rather than asserting it.

Attribution works on stream adjacency, which is sound because the allocator is
sequential per function: increment 1 (the straight-line path) prints its
post-prescan sub-reason lines FIRST, then the joins path prints
`join colouring DECLINED: <reason>` for the same function.  A `single-block`
decline is therefore attributed to the increment-1 sub-block immediately
preceding it:

  rmw-colour-mismatch   the preceding `rewrite-refused complete set` listing
                        names at least one `/rmw-colour-mismatch` refusal
  no-rewrite-arm        listing present, but only `/no-rewrite-arm` causes
  <sub-reason>          any other named increment-1 sub-reason
                        (needs-spill, edge-recheck, trace-validator-reject/…)
  prescan               NO increment-1 line at all: the function failed the
                        prescan (non-straight-line / unmodeled op) and joins
                        refused it silently as single-block

One subtlety keeps the attribution honest: the SHIPPING segment-based
`reallocate_function` (run after a graph-alloc decline) prints
`rewrite-refused complete set` lines through the SAME apply_range_coloring
census, and those land in the stream AFTER the current function's join
verdict — i.e. inside the NEXT function's evidence window.  A GENUINE
increment-1 refusal is printed immediately before its own
`increment-1 declined: apply-colouring` line, so a refusal listing counts as
increment-1 evidence ONLY when the very next diagnostic line is that
apply-colouring sub-reason; anything else is shipping-path noise and is
dropped.

Usage:  python3 scripts/tied_web_census_242.py <synth-binary> [--json OUT]
Exit 0 unless a compile fails — this MEASURES, it does not judge.
"""

import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

REPRO = Path(__file__).resolve().parent / "repro"

# Same ambient-flag hygiene as vcr_dec_001_join_alloc_measure.py: clear every
# codegen lever so an exported SYNTH_* cannot skew a measurement.
CLEAR = [
    "SYNTH_NO_CMP_SELECT_FUSE", "SYNTH_NO_LOCAL_PROMOTE", "SYNTH_NO_IMM_SHIFT_FOLD",
    "SYNTH_NO_STACK_FWD", "SYNTH_SPILL_REALLOC", "SYNTH_CONST_CSE", "SYNTH_BASE_CSE",
    "SYNTH_DEAD_FRAME_ELIM", "SYNTH_UXTH_FOLD", "SYNTH_GRAPH_ALLOC", "SYNTH_GRAPH_ALLOC_FORCE",
    "SYNTH_SHIFT_MASK_ELIDE", "SYNTH_RANGE_REALLOC", "SYNTH_FACT_SPEC",
    "SYNTH_GRAPH_ALLOC_STATS", "SYNTH_GRAPH_ALLOC_DUMP",
]

INC1 = re.compile(r"^\[graph-alloc\] increment-1 declined: (.+)$")
REFUSED = re.compile(r"^\[graph-alloc\] rewrite-refused complete set: (.+)$")
JOIN = re.compile(r"^\[graph-alloc\] join colouring DECLINED: (.+)$")


def corpus():
    return sorted(
        [p for p in REPRO.glob("*.wat")] + [p for p in REPRO.glob("*.wasm")],
        key=lambda p: p.name,
    )


def compile_stats(synth, src, outdir, relocatable):
    env = {k: v for k, v in os.environ.items()}
    for k in CLEAR:
        env.pop(k, None)
    env["SYNTH_GRAPH_ALLOC"] = "1"
    env["SYNTH_GRAPH_ALLOC_STATS"] = "1"
    elf = Path(outdir) / (src.stem + ".elf")
    cmd = [synth, "compile", str(src), "-o", str(elf),
           "-b", "arm", "--target", "cortex-m4", "--all-exports"]
    if relocatable:
        cmd.append("--relocatable")
    return subprocess.run(cmd, capture_output=True, env=env, text=True)


def attribute(stderr):
    """Per-file: (Counter of join-decline reasons,
                  Counter of single-block attributions,
                  Counter of rmw op families seen in refusals)."""
    joins = Counter()
    single = Counter()
    rmw_ops = Counter()
    # The increment-1 evidence block accumulated since the last join verdict.
    inc1 = []          # sub-reason strings
    refused_rmw = []   # op families refused as /rmw-colour-mismatch
    refused_other = False
    # A refusal listing counts as increment-1 evidence ONLY if the immediately
    # following diagnostic line is `increment-1 declined: apply-colouring`
    # (see the module doc: the shipping pass prints the same listing).
    pending_rmw = []
    pending_other = False
    for line in stderr.splitlines():
        m = INC1.match(line)
        if m:
            reason = m.group(1)
            if reason == "apply-colouring":
                refused_rmw.extend(pending_rmw)
                refused_other = refused_other or pending_other
            pending_rmw, pending_other = [], False
            inc1.append(reason)
            continue
        m = REFUSED.match(line)
        if m:
            pending_rmw, pending_other = [], False
            for item in m.group(1).split(", "):
                name = item.split(" x")[0]
                fam, _, cause = name.partition("/")
                if cause == "rmw-colour-mismatch":
                    pending_rmw.append(fam)
                else:
                    pending_other = True
            continue
        # Any other line breaks refusal→apply-colouring adjacency.
        pending_rmw, pending_other = [], False
        m = JOIN.match(line)
        if m:
            reason = m.group(1)
            joins[reason] += 1
            if reason == "single-block":
                if refused_rmw:
                    single["rmw-colour-mismatch"] += 1
                    rmw_ops.update(refused_rmw)
                elif refused_other:
                    single["no-rewrite-arm"] += 1
                elif inc1:
                    single[inc1[-1]] += 1
                else:
                    single["prescan"] += 1
            inc1, refused_rmw, refused_other = [], [], False
    return joins, single, rmw_ops


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    synth = sys.argv[1]
    json_out = None
    if "--json" in sys.argv:
        json_out = sys.argv[sys.argv.index("--json") + 1]

    report = {}
    for relocatable in (True, False):
        path = "relocatable" if relocatable else "self-contained"
        joins_all, single_all, rmw_all = Counter(), Counter(), Counter()
        files = failures = 0
        with tempfile.TemporaryDirectory() as td:
            for src in corpus():
                r = compile_stats(synth, src, td, relocatable)
                if r.returncode != 0:
                    failures += 1
                    continue
                files += 1
                j, s, ops = attribute(r.stderr)
                joins_all.update(j)
                single_all.update(s)
                rmw_all.update(ops)
        n_single = sum(single_all.values())
        n_rmw = single_all.get("rmw-colour-mismatch", 0)
        print(f"\n== {path} ({files} files compiled, {failures} compile-failures) ==")
        print("join-decline histogram:")
        for k, v in joins_all.most_common():
            print(f"  {v:5d}  {k}")
        print(f"single-block attribution ({n_rmw} of {n_single} are rmw-colour-mismatch):")
        for k, v in single_all.most_common():
            print(f"  {v:5d}  {k}")
        if rmw_all:
            print("rmw-refused op families (instances, not functions):")
            for k, v in rmw_all.most_common():
                print(f"  {v:5d}  {k}")
        report[path] = {
            "files": files,
            "compile_failures": failures,
            "join_declines": dict(joins_all),
            "single_block_attribution": dict(single_all),
            "rmw_op_families": dict(rmw_all),
            "single_block_total": n_single,
            "single_block_rmw": n_rmw,
        }

    if json_out:
        Path(json_out).write_text(json.dumps(report, indent=2, sort_keys=True))
        print(f"\nwrote {json_out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
