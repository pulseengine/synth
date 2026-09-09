#!/usr/bin/env python3
# ci-status: wired
# ci-checks: stdout /^functions audited: (\d+)$/ >= 4628
"""RQ-65-ALIASCLASS (#1189) — the home-register write audit, swept over the
local corpus on every ARM direct-selector leg.

THE QUESTION. `local.get` of a register-homed local pushes THE HOME REGISTER
uncopied onto the ARM direct selector's operand stack. #677, #989 and #1189
were three consumers that wrote it — each found as a silent wrong answer,
each fixed at its own site. This sweep asks the general question the three
fixes never did: over every module we have, on every leg the direct selector
serves, does ANY emitted instruction write a live local's home register
through a path other than that local's own `local.set`/`local.tee`?

HOW. `synth_synthesis::home_alias::audit` (Rust, exhaustive over all 222
`ArmOp` variants with no wildcard arm, unit-tested against a planted #1189
join write) runs inside `select_with_stack` when `SYNTH_HOME_ALIAS_AUDIT` is
set; a hit becomes a loud per-function decline carrying the needle
`#1189-class home-register write`, and `=verbose` prints one
`home-alias-audit:` line per audited function. This script compiles the
corpus with it armed and asserts:

  * ZERO UNEXPLAINED hits — every hit is printed with module, leg, op index
    and the exact instruction, and fails the run unless it is pinned in
    KNOWN_OPEN_HITS: a hit whose defect is FILED and OPEN, pinned EXACTLY
    (function, op, register, local, on every leg) so the fix must flip the
    pin and nothing else can hide behind it. Today's pinned hits are one
    defect, #1226 — the multi-module .wast merge hands a LATER module's
    function the representative module's param-width table, so an i64 param
    is homed as i32 and its pair overlaps the next param; the #1222 fix
    (which writes the pair's hi half) is what made it visible;
  * NON-VACUITY floors on the work done (#1113: a floor on green is not a
    floor on work): functions audited, homes watched, attributed
    instructions, modules compiled — each pinned at a value DERIVED from a
    run, so a corpus that silently shrinks or a hook that silently stops
    firing is red, not green.

LEGS. `select_with_stack` serves (a) every `--relocatable` compile (#197) and
(b) every self-contained function the optimized selector declines — so both
ARM paths are swept, on `cortex-m4` (soft-float: integer homes only) AND on
`cortex-m4f` (hard-float: f32 params homed in S-registers alias too, #619).

CORPUS. The pinned spec testsuite (257 top-level .wast, submodule commit
345367358f065375524498749470720d9cdd1418 — `--suite` must point at it;
missing or short is a hard failure, never 0/0), tests/wast, tests/wat,
tests/fixtures, scripts/repro/*.wat. Per module `--all-exports
--allow-skipped-exports`, so a per-function decline elsewhere in a module
never hides the functions that DID compile from the audit.

WHAT A CLEAN SWEEP MEANS, precisely: on this corpus, no consumer other than
the three already guarded writes a live home — the enumeration of consumers
is complete OVER THESE INPUTS. The per-opcode oracle
(`home_alias_class_1189_differential.py`) covers the consumer families the
corpus may not exercise with a home operand, and executes them.

Run:
  SYNTH=./target/debug/synth python3 scripts/repro/home_alias_audit_corpus_1189.py \
      --suite tests/spec-testsuite
"""

import argparse
import concurrent.futures
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

EXPECTED_SUITE_FILES = 257
NEEDLE = "#1189-class home-register write"
AUDIT_LINE = re.compile(
    r"^home-alias-audit: ops=(\d+) homes=(\d+) attributed=(\d+) "
    r"unattributed=(\d+) hits=(\d+)$"
)

LEGS = {
    "m4-reloc": ["--target", "cortex-m4", "--relocatable"],
    "m4-self": ["--target", "cortex-m4"],
    "m4f-reloc": ["--target", "cortex-m4f", "--relocatable"],
    "m4f-self": ["--target", "cortex-m4f"],
}

# Non-vacuity floors — DERIVED from a run on the pinned corpus (see the PR),
# re-derive with --print-floors when the corpus or the selector legitimately
# moves. Every one is a floor on WORK DONE, not on hits.
FLOORS = {
    "modules_compiled": 313,   # (module, leg) pairs that produced >=1 audited fn
    "functions_audited": 4628,
    "homes_watched": 2372,
    "attributed_instrs": 227150,
}

# Hits whose defect is FILED and OPEN, pinned EXACTLY — (module, function,
# op, written register, local) — and required on EVERY leg in LEGS. A hit
# outside this table is unexplained (red); a pinned hit that stops occurring
# means the fix landed (red until the pin is flipped in that PR).
KNOWN_OPEN_HITS = {
    # #1226: `(param $from i64) (param $to i64) (param $expected i32)` in a
    # later module of a multi-module .wast — `$to` homed at R1:R2, so the
    # #1222-correct `local.set $from` (writing R0:R1) lands on "local 1".
    ("memory_copy64.wast", "checkRange", "op 16 (LocalSet(0))", "R1", 1): "#1226",
    ("memory_fill64.wast", "checkRange", "op 16 (LocalSet(0))", "R1", 1): "#1226",
    ("memory_init64.wast", "checkRange", "op 16 (LocalSet(0))", "R1", 1): "#1226",
    ("memory_grow64.wast", "check-memory-zero", "op 18 (LocalSet(0))", "R1", 1): "#1226",
}
HIT_LINE = re.compile(
    r"skipping function '([^']+)'.*?(op \d+ \(.+?\)) instr \d+ `[^`]*` "
    r"writes ([A-Z0-9]+) = home of local (\d+)"
)


def corpus(suite: Path):
    files = sorted(suite.glob("*.wast"))
    if len(files) != EXPECTED_SUITE_FILES:
        print(f"FATAL: {suite} holds {len(files)} top-level .wast, want "
              f"{EXPECTED_SUITE_FILES} (submodule not checked out?)")
        sys.exit(1)
    files += sorted((ROOT / "tests" / "wast").glob("*.wast"))
    files += sorted((ROOT / "tests" / "wat").glob("*.wat"))
    files += sorted((ROOT / "tests" / "fixtures").rglob("*.wat"))
    files += sorted((ROOT / "scripts" / "repro").glob("*.wat"))
    return files


def run_one(module: Path, leg: str):
    with tempfile.TemporaryDirectory() as td:
        out = os.path.join(td, "m.o")
        env = {"PATH": "/usr/bin:/bin", "SYNTH_HOME_ALIAS_AUDIT": "verbose"}
        try:
            r = subprocess.run(
                [SYNTH, "compile", str(module), "-o", out, "--all-exports",
                 "--allow-skipped-exports", *LEGS[leg]],
                capture_output=True, text=True, env=env, timeout=600,
            )
        except subprocess.TimeoutExpired:
            return module, leg, None, [], "timeout"
        log = r.stderr + r.stdout
    stats = [0, 0, 0, 0]  # functions, homes, attributed, unattributed
    hits = []
    for line in log.splitlines():
        m = AUDIT_LINE.match(line.strip())
        if m:
            stats[0] += 1
            stats[1] += int(m.group(2))
            stats[2] += int(m.group(3))
            stats[3] += int(m.group(4))
            continue
        if NEEDLE in line:
            hits.append(line.strip())
    panic = "panicked at" in log or r.returncode == 101
    return module, leg, stats, hits, "panic" if panic else ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--suite", default=str(ROOT / "tests" / "spec-testsuite"))
    ap.add_argument("-j", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--print-floors", action="store_true",
                    help="print the measured totals in FLOORS form and exit 0")
    args = ap.parse_args()

    files = corpus(Path(args.suite))
    jobs = [(f, leg) for f in files for leg in LEGS]
    totals = {"modules_compiled": 0, "functions_audited": 0,
              "homes_watched": 0, "attributed_instrs": 0,
              "unattributed_instrs": 0}
    all_hits = []
    unexplained = []
    known_seen = {}  # (key, leg) -> count
    panics = []
    timeouts = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.j) as ex:
        for module, leg, stats, hits, err in ex.map(lambda j: run_one(*j), jobs):
            rel = module.relative_to(ROOT) if module.is_relative_to(ROOT) else module.name
            if err == "timeout":
                timeouts.append(f"{rel}/{leg}")
                continue
            if err == "panic":
                panics.append(f"{rel}/{leg}")
            if stats[0] > 0:
                totals["modules_compiled"] += 1
            totals["functions_audited"] += stats[0]
            totals["homes_watched"] += stats[1]
            totals["attributed_instrs"] += stats[2]
            totals["unattributed_instrs"] += stats[3]
            for h in hits:
                all_hits.append(f"{rel}/{leg}: {h}")
                m = HIT_LINE.search(h)
                key = (module.name, m.group(1), m.group(2), m.group(3), int(m.group(4))) if m else None
                if key in KNOWN_OPEN_HITS:
                    known_seen[(key, leg)] = known_seen.get((key, leg), 0) + 1
                else:
                    unexplained.append(f"{rel}/{leg}: {h}")

    for h in all_hits:
        tag = "HIT  " if h in unexplained else "known"
        print(f"  {tag} {h}")
    for p in panics:
        print(f"  PANIC {p}")
    for t in timeouts:
        print(f"  TIMEOUT {t}")

    expected_known = {(k, leg) for k in KNOWN_OPEN_HITS for leg in LEGS}
    missing_known = sorted(expected_known - set(known_seen), key=str)
    known_total = sum(known_seen.values())
    issues = sorted(set(KNOWN_OPEN_HITS.values()))

    print(f"modules compiled: {totals['modules_compiled']}")
    print(f"functions audited: {totals['functions_audited']}")
    print(f"homes watched: {totals['homes_watched']}")
    print(f"attributed instructions: {totals['attributed_instrs']} "
          f"(unattributed: {totals['unattributed_instrs']})")
    print(f"hits: {len(all_hits)} (known-open: {known_total} [{', '.join(issues)}], "
          f"unexplained: {len(unexplained)})")

    if args.print_floors:
        print("FLOORS = {")
        for k in FLOORS:
            print(f'    "{k}": {totals[k]},')
        print("}")
        return 0

    fails = 0
    for k, floor in FLOORS.items():
        if totals[k] < floor:
            print(f"VACUOUS: {k}={totals[k]} < floor {floor} — the sweep did "
                  f"less work than the pin; re-derive with --print-floors only "
                  f"if the corpus or the selector legitimately shrank")
            fails += 1
    if unexplained:
        print(f"FAIL: {len(unexplained)} UNEXPLAINED home-register write(s) — a "
              f"#1189-class consumer is emitting a write to a live local's home")
        fails += 1
    if missing_known:
        print(f"FAIL: {len(missing_known)} pinned known-open hit(s) did not occur — "
              f"a fix landed (flip the pin in that PR) or the corpus moved: "
              f"{missing_known[:4]}")
        fails += 1
    if known_total != len(expected_known):
        print(f"FAIL: known-open hits={known_total}, pinned {len(expected_known)} "
              f"(one per pinned function per leg)")
        fails += 1
    if panics or timeouts:
        print(f"FAIL: {len(panics)} panic(s), {len(timeouts)} timeout(s)")
        fails += 1
    if fails:
        print(f"RESULT: FAIL ({fails})")
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
