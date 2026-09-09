#!/usr/bin/env python3
# ci-status: wired
# ci-checks: stdout /^functions audited: (\d+)$/ >= 8317
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
`home-alias-audit:` line per audited function. Two writes are EXEMPT, each
proven ON THE STREAM (never from the op name): a write that IS, or runs
straight-line into, the inline epilogue `pop {…, pc}` (the epilogue restores
a promoted local's r4–r8 and returns in the same instruction), and a write
bracketed by the op's own save/restore of a VFP home through one frame slot
(the caller-save around a `bl`; calls carry the AAPCS VFP clobber s0–s15, so
a MISSING restore is a hit). Both were found as false positives of the first
FULL-corpus run (8 + 4 of its 12 hits) and fixed in the walk, not silenced
here. This script compiles the corpus with it armed and asserts:

  * ZERO UNEXPLAINED hits — every hit is printed with module, leg, op index
    and the exact instruction, and fails the run unless it is pinned in
    KNOWN_OPEN_HITS: a hit whose defect is FILED and OPEN, pinned EXACTLY
    (function, op, register, local, on every leg) so the fix must flip the
    pin and nothing else can hide behind it. Today the table is EMPTY. It
    carried #1226 (the multi-module .wast merge hands a LATER module's
    function the representative module's param-width table, so an i64 param
    is homed as i32 and its pair overlaps the next param — 4 spec functions
    x 4 legs) until the #1222 pair-write was gated on the DECLARED width:
    `declared_wide_params` reads the same stale table, so `local.set $from`
    writes only R0 there again and nothing lands on the mis-homed
    neighbour. That removed the HIT, not the miscompile — `checkRange` still
    compares `$to` at R1:R2 (bytes on the issue) — so #1226 stays OPEN and is
    simply no longer visible to this audit; no line here can see it;
  * NON-VACUITY floors on the work done (#1113: a floor on green is not a
    floor on work): functions audited, homes watched, attributed
    instructions, modules compiled — each pinned at a value DERIVED from a
    run, so a corpus that silently shrinks or a hook that silently stops
    firing is red, not green;
  * POTENCY, before the sweep: `hits: 0` over a corpus proves the sweep RAN,
    not that the DETECTOR FIRES. The `plant` probe (`home_alias::plant_probe`)
    plants one synthetic home write per function of three small fixtures and
    every one MUST decline with the needle at op 0 — pinned EXACTLY per
    (fixture, leg), and 0 without the plant (PLANT_EXPECTED);
  * the #1226 PIN: a mis-homing this audit cannot see as a write (it trusts
    the selector's home table) is pinned on the `homes=` count instead — the
    same module text as `.wast` vs `.wat` (WIDTH_1226_HOMES), red-first,
    flipped by the fix.

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

# scripts/repro/<this file> -> the repo root is THREE levels up. (First CI run:
# `parent.parent` resolved to `scripts/`, the suite path did not exist, and
# the sweep exited 1 having audited nothing — a local run from the repo root
# with an explicit --suite never saw it.)
ROOT = Path(__file__).resolve().parent.parent.parent
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

EXPECTED_SUITE_FILES = 257
NEEDLE = "#1189-class home-register write"
AUDIT_LINE = re.compile(
    r"^home-alias-audit: ops=(\d+) homes=(\d+) attributed=(\d+) "
    r"unattributed=(\d+) hits=(\d+)(?: planted=(\d+))?$"
)

LEGS = {
    "m4-reloc": ["--target", "cortex-m4", "--relocatable"],
    "m4-self": ["--target", "cortex-m4"],
    "m4f-reloc": ["--target", "cortex-m4f", "--relocatable"],
    "m4f-self": ["--target", "cortex-m4f"],
}

# Non-vacuity floors — DERIVED from a run on the pinned corpus WITH the suite
# submodule present (the 4628/2372/227150 first pinned here were a suite-only
# run: ROOT resolved one level too shallow, so tests/wast, tests/wat, fixtures
# and scripts/repro were never found). Re-derive with --print-floors when the
# corpus or the selector legitimately moves. Every one is a floor on WORK
# DONE, not on hits.
FLOORS = {
    "modules_compiled": 1045,  # (module, leg) pairs that produced >=1 audited fn
    "functions_audited": 8317,
    "homes_watched": 8776,
    "attributed_instrs": 261440,
}

# Hits whose defect is FILED and OPEN, pinned EXACTLY — (module, function,
# op, written register, local) — and required on EVERY leg in LEGS. A hit
# outside this table is unexplained (red); a pinned hit that stops occurring
# means the fix landed (red until the pin is flipped in that PR).
KNOWN_OPEN_HITS: dict = {
    # Empty since the #1222 declared-width gate. It held #1226's 4 x 4:
    #   ("memory_copy64.wast", "checkRange", "op 16 (LocalSet(0))", "R1", 1)
    #   ("memory_fill64.wast", "checkRange", "op 16 (LocalSet(0))", "R1", 1)
    #   ("memory_init64.wast", "checkRange", "op 16 (LocalSet(0))", "R1", 1)
    #   ("memory_grow64.wast", "check-memory-zero", "op 18 (LocalSet(0))", "R1", 1)
    # — `$to` homed at R1:R2, the #1222-correct `local.set $from` (R0:R1)
    # landing on "local 1". The gate now writes R0 only on that stale-width
    # shape, so the write that made #1226 visible is gone while the wrong
    # homing remains. A #1226 fix will not flip anything HERE; it is gated by
    # its own repro on the issue.
}
HIT_LINE = re.compile(
    r"skipping function '([^']+)'.*?(op \d+ \(.+?\)) instr \d+ `[^`]*` "
    r"writes ([A-Z0-9]+) = home of local (\d+)"
)

# ── POTENCY SELF-TEST + #1226 PIN — runs BEFORE the sweep, cheap ─────────────
#
# A `hits: 0` sweep proves the sweep RAN (the floors above) — not that the
# DETECTOR FIRES, and after the walk was relaxed to clear 12 false positives
# that is the property under suspicion. `SYNTH_HOME_ALIAS_AUDIT=verbose,plant`
# makes `home_alias::plant_probe` plant ONE synthetic write of a watched home
# at op 0 of every function that has a home still read later — on a COPY of
# the stream — so each such function MUST decline with the needle at `op 0`,
# through the very decline / needle / parse path this sweep relies on; and
# NO function may decline without the plant. Pinned EXACTLY per (fixture,
# leg) in BOTH directions: fewer declines -> the detector went quiet; more ->
# the walk over-reports again. The three fixtures cover the three home kinds:
# i32 params in r0-r3 (leaf), #390-promoted locals in r4-r8, f32 params and
# locals in S-registers (cortex-m4f). On the self-contained legs only the
# functions the optimized selector declines reach the direct selector, so
# their counts are smaller and may be 0 — the relocatable legs carry the
# potency for every fixture (asserted: no fixture may be 0 on every leg).
PLANT_FIXTURES = [
    "home_alias_class_1189_i32.wat",
    "home_alias_class_1189_promo.wat",
    "f32_ops_719.wat",
]
# (fixture, leg) -> functions that MUST decline under the plant (= the
# verbose lines with `planted=1`). DERIVED by --print-self-test; a fixture or
# walk change moves it here, visibly.
PLANT_EXPECTED = {
    ("home_alias_class_1189_i32.wat", "m4-reloc"): 58,
    ("home_alias_class_1189_i32.wat", "m4-self"): 7,
    ("home_alias_class_1189_i32.wat", "m4f-reloc"): 58,
    ("home_alias_class_1189_i32.wat", "m4f-self"): 7,
    ("home_alias_class_1189_promo.wat", "m4-reloc"): 11,
    ("home_alias_class_1189_promo.wat", "m4-self"): 9,
    ("home_alias_class_1189_promo.wat", "m4f-reloc"): 11,
    ("home_alias_class_1189_promo.wat", "m4f-self"): 9,
    ("f32_ops_719.wat", "m4-reloc"): 0,  # soft-float: no VFP home to plant into
    ("f32_ops_719.wat", "m4-self"): 0,
    ("f32_ops_719.wat", "m4f-reloc"): 11,
    ("f32_ops_719.wat", "m4f-self"): 11,
}

# #1226 — stated plainly. It is a mis-HOMING, not a home WRITE, and its real
# mechanism is wider than the issue first said: the synth-cli `.wast` driver
# path returns `Vec::new()` for EVERY declared-width table (func/type ret_i64,
# params_i64/_f32/_f64, the f32/f64 return masks — main.rs, each annotated
# "WAST fixture suite is i32-only"), so on ANY `.wast` — single-module too,
# not only a later module of a multi-module file — every i64/f32/f64 param or
# result whose width body inference cannot recover (`infer_i64_locals` learns
# from set/tee only) is homed as i32. Measured: the SAME module text compiled
# as `.wat` gives `second3` homes=4 and `mov r0, r2; mov r1, r3`; as a `.wast`
# (single or merged) homes=2 and `mov r0, r1`. This audit trusts the
# selector's home table BY CONSTRUCTION (it asks "does anything write a
# home?", not "is the home right?"), so it never saw #1226 itself — the 16
# hits it carried were a SYMPTOM (the #1222 pair-write, fired by body
# inference, landing in the neighbour's wrongly assigned R1) that the
# declared-width gate removed by changing the EMISSION on that shape, not the
# walk. The audit's coverage of home WRITES is unchanged; the walk is correct.
# What covers #1226 now is THIS pin, on the one thing the audit does report
# about homing — the `homes=` count: ONE fixture, three ways — (a) as shipped
# (two modules, the spec-suite shape), (b) its last module alone as a `.wast`,
# (c) the identical text as a `.wat` — must report `wast < wat` on every leg
# while the defect is open. A fix makes (b) == (c), this goes red, and the fix
# flips the pin (known-open -> closed) in its own PR. The fixture is `.wast`
# on purpose: `scripts/repro/*.wat` is executed against wasmtime by
# arm_corpus_sweep_973.py and this module is a KNOWN miscompile; the `.wat`
# control is derived from it at run time so the two can never drift.
WIDTH_1226_FIXTURE = "home_alias_width_1226.wast"
# leg -> (merged .wast total, single-module .wast total, .wat total) of
# `homes=`. DERIVED; the pin is `wast < wat` with these exact values.
WIDTH_1226_HOMES = {
    "m4-reloc": (7, 6, 8),
    "m4-self": (4, 4, 8),   # self-contained: `second3` (params read as i32) takes the optimized selector, no audit line
    "m4f-reloc": (7, 6, 8),
    "m4f-self": (4, 4, 8),
}


def corpus(suite: Path):
    files = sorted(suite.glob("*.wast"))
    if len(files) != EXPECTED_SUITE_FILES:
        print(f"FATAL: looked for the spec testsuite at {suite.resolve()} "
              f"(exists: {suite.is_dir()}) and found {len(files)} top-level "
              f".wast, want {EXPECTED_SUITE_FILES} — pass --suite, or check "
              f"that path; nothing was audited")
        sys.exit(1)
    files += sorted((ROOT / "tests" / "wast").glob("*.wast"))
    files += sorted((ROOT / "tests" / "wat").glob("*.wat"))
    files += sorted((ROOT / "tests" / "fixtures").rglob("*.wat"))
    files += sorted((ROOT / "scripts" / "repro").glob("*.wat"))
    return files


def run_one(module: Path, leg: str, mode: str = "verbose"):
    with tempfile.TemporaryDirectory() as td:
        out = os.path.join(td, "m.o")
        env = {"PATH": "/usr/bin:/bin", "SYNTH_HOME_ALIAS_AUDIT": mode}
        try:
            r = subprocess.run(
                [SYNTH, "compile", str(module), "-o", out, "--all-exports",
                 "--allow-skipped-exports", *LEGS[leg]],
                capture_output=True, text=True, env=env, timeout=600,
            )
        except subprocess.TimeoutExpired:
            return module, leg, None, [], "timeout"
        log = r.stderr + r.stdout
    stats = [0, 0, 0, 0, 0]  # functions, homes, attributed, unattributed, planted
    hits = []
    for line in log.splitlines():
        m = AUDIT_LINE.match(line.strip())
        if m:
            stats[0] += 1
            stats[1] += int(m.group(2))
            stats[2] += int(m.group(3))
            stats[3] += int(m.group(4))
            stats[4] += int(m.group(6) or 0)
            continue
        if NEEDLE in line:
            hits.append(line.strip())
    panic = "panicked at" in log or r.returncode == 101
    return module, leg, stats, hits, "panic" if panic else ""


def self_test(print_pins: bool) -> int:
    """Potency (plant) in both directions + the #1226 homes pin. Returns the
    number of failures; with `print_pins` prints the derived tables and
    returns 0."""
    fails = 0
    repro = ROOT / "scripts" / "repro"
    derived_plant = {}
    total_planted = 0
    for fx in PLANT_FIXTURES:
        per_fixture = 0
        for leg in LEGS:
            _, _, stats, hits, err = run_one(repro / fx, leg, "verbose,plant")
            planted = stats[4] if stats else -1
            declined = len(hits)
            bad_shape = [h for h in hits
                         if not HIT_LINE.search(h) or "op 0 (" not in h
                         or "planted probe" not in h]
            derived_plant[(fx, leg)] = planted
            expected = PLANT_EXPECTED.get((fx, leg))
            ok = (err == "" and not bad_shape and planted == declined
                  and (print_pins or expected == declined))
            print(f"potency: {fx}/{leg}: planted={planted} declined={declined} "
                  f"expected={'?' if expected is None else expected}"
                  f"{'' if not bad_shape else f' malformed={len(bad_shape)}'}"
                  f"{'' if not err else f' {err}'} {'ok' if ok else 'FAIL'}")
            if not ok:
                fails += 1
            per_fixture += declined
            total_planted += declined
            # The other direction: the same fixture, no plant, declines nothing.
            _, _, _, hits0, err0 = run_one(repro / fx, leg, "verbose")
            if hits0 or err0:
                print(f"potency: unplanted {fx}/{leg}: declined={len(hits0)} "
                      f"expected=0 {err0} FAIL")
                fails += 1
        if per_fixture == 0:
            print(f"potency: {fx}: 0 planted writes on EVERY leg — vacuous FAIL")
            fails += 1
    derived_width = {}
    src = "\n".join(l for l in (repro / WIDTH_1226_FIXTURE).read_text().splitlines()
                    if not l.lstrip().startswith(";;"))
    last_module = src[src.rindex("(module"):]
    with tempfile.TemporaryDirectory() as td:
        single_wast = Path(td) / "single.wast"
        single_wast.write_text(last_module)
        as_wat = Path(td) / "same.wat"
        as_wat.write_text(last_module)
        for leg in LEGS:
            totals = {}
            for kind, f in (("merged", repro / WIDTH_1226_FIXTURE),
                            ("wast", single_wast), ("wat", as_wat)):
                _, _, stats, hits, err = run_one(f, leg, "verbose")
                totals[kind] = stats[1] if stats else -1
                if hits or err:
                    print(f"width-1226: {kind}/{leg}: unexpected {len(hits)} hit(s) {err} FAIL")
                    fails += 1
            derived_width[leg] = (totals["merged"], totals["wast"], totals["wat"])
            pinned = WIDTH_1226_HOMES.get(leg)
            open_ = totals["wast"] < totals["wat"]
            ok = print_pins or (pinned == derived_width[leg] and open_)
            print(f"width-1226: {leg}: homes merged-wast={totals['merged']} "
                  f"single-wast={totals['wast']} same-text-wat={totals['wat']} "
                  f"pinned={pinned} "
                  f"{'known-open' if open_ else 'wast == wat -> a fix landed, flip the pin'} "
                  f"{'ok' if ok else 'FAIL'}")
            if not ok:
                fails += 1
    if print_pins:
        print("PLANT_EXPECTED = {")
        for (fx, leg), n in derived_plant.items():
            print(f'    ("{fx}", "{leg}"): {n},')
        print("}")
        print("WIDTH_1226_HOMES = {")
        for leg, pair in derived_width.items():
            print(f'    "{leg}": {pair},')
        print("}")
        return 0
    legs_open = sum(1 for leg in LEGS if derived_width[leg][1] < derived_width[leg][2])
    if fails:
        print(f"POTENCY: FAIL ({fails})")
    else:
        print(f"POTENCY: PASS ({total_planted} planted writes reported, 0 without "
              f"the plant, over {len(PLANT_FIXTURES)} fixtures x {len(LEGS)} legs)")
        print(f"WIDTH-1226: known-open (.wast homes < .wat homes for the same "
              f"module text on {legs_open} legs)")
    return fails


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--suite", default=str(ROOT / "tests" / "spec-testsuite"))
    ap.add_argument("-j", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--print-floors", action="store_true",
                    help="print the measured totals in FLOORS form and exit 0")
    ap.add_argument("--print-self-test", action="store_true",
                    help="print the derived PLANT_EXPECTED / WIDTH_1226_HOMES and exit 0")
    ap.add_argument("--self-test-only", action="store_true",
                    help="run only the potency self-test + #1226 pin")
    args = ap.parse_args()

    if args.print_self_test:
        return self_test(print_pins=True)
    self_fails = self_test(print_pins=False)
    if args.self_test_only:
        print("RESULT: PASS" if not self_fails else f"RESULT: FAIL ({self_fails})")
        return 1 if self_fails else 0

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
    print(f"hits: {len(all_hits)} (known-open: {known_total} [{', '.join(issues) or 'none'}], "
          f"unexplained: {len(unexplained)})")

    if args.print_floors:
        print("FLOORS = {")
        for k in FLOORS:
            print(f'    "{k}": {totals[k]},')
        print("}")
        return 0

    fails = 1 if self_fails else 0
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
