#!/usr/bin/env python3
"""oracle_evidence — close out an oracle job with what it actually EXECUTED.

Per-step floors (scripts/oracle_run.py) answer "did this oracle run?". This
answers the job-level question #910 asks: **report the differential population
in its own unit instead of folding it into a coverage percentage.**

It reads the JSONL ledger the driver appended to during the job and

  * asserts every record passed AND the expected number of oracles reported —
    a step that vanished (deleted, commented out, short-circuited by an earlier
    `exit`) leaves the ledger short, and a short ledger is a red job, not a
    quietly smaller number;
  * writes the job's measured totals to `$GITHUB_STEP_SUMMARY`.

Reported PER UNIT, never as one figure: emulator entries, wasmtime reference
executions and compilations are three different things. Summing them would
manufacture exactly the kind of impressive-but-meaningless total this lane
exists to remove.

Exit: 0 = ledger complete and every oracle met its floor · 1 = otherwise.
"""

import argparse
import json
import os
import pathlib
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("ledger", help="the JSONL written via $ORACLE_EVIDENCE_JSONL")
    ap.add_argument(
        "--min-oracles",
        type=int,
        required=True,
        metavar="N",
        help="how many oracle records this job must have filed",
    )
    ap.add_argument("--job", default=os.environ.get("GITHUB_JOB", "oracle job"))
    args = ap.parse_args()

    p = pathlib.Path(args.ledger)
    if not p.exists():
        sys.exit(
            f"oracle_evidence: no ledger at {args.ledger} — the job ran NO "
            f"instrumented oracle. Either the steps are not routed through "
            f"scripts/oracle_run.py, or $ORACLE_EVIDENCE_JSONL is unset."
        )

    records = [json.loads(line) for line in p.read_text().splitlines() if line.strip()]
    if not records:
        sys.exit(f"oracle_evidence: ledger {args.ledger} is EMPTY — nothing ran.")

    fails = [r for r in records if not r.get("ok")]
    scripts = {r["script"] for r in records}
    tot_emu = sum(r.get("emulations", 0) for r in records)
    tot_wasm = sum(r.get("wasmtime_calls", 0) for r in records)
    tot_comp = sum(r.get("compiles", 0) for r in records)

    print(
        f"ORACLE-LEDGER job={args.job} oracles={len(scripts)} runs={len(records)} "
        f"emulations={tot_emu} wasmtime_calls={tot_wasm} compiles={tot_comp} "
        f"below_floor={len(fails)}"
    )

    step_summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if step_summary:
        with open(step_summary, "a") as fh:
            fh.write(f"### Differential evidence — `{args.job}` (#910)\n\n")
            fh.write("| unit | measured |\n|---|---|\n")
            fh.write(f"| oracles run | {len(scripts)} |\n")
            fh.write(f"| emulator entries | {tot_emu} |\n")
            fh.write(f"| wasmtime reference executions | {tot_wasm} |\n")
            fh.write(f"| compilations | {tot_comp} |\n\n")
            fh.write(
                "Three units, reported separately on purpose. None of this is "
                "visible to `Rust-test Line Coverage`: these oracles run the "
                "compiler as an uninstrumented subprocess, in this job, not "
                "under `cargo llvm-cov`.\n\n"
            )

    problems = []
    if len(scripts) < args.min_oracles:
        problems.append(
            f"ledger SHORT: {len(scripts)} distinct oracles reported, expected "
            f">= {args.min_oracles}. A step is missing, commented out, or the "
            f"job exited early — its gate is inert (#890)."
        )
    for r in fails:
        problems.append(
            f"{r['script']}: below floor — mode={r.get('mode')} "
            f"floor={r.get('floor')} measured={r.get('measured')} "
            f"exit={r.get('exit')}"
        )
    if problems:
        print()
        for f in problems:
            print(f"FAIL {f}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
