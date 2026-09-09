#!/usr/bin/env python3
"""spec_compile_census.py — the WASM spec-suite compile census, exact-pinned.

RQ-61-SPECCLAIM (#1095): README.md and FEATURE_MATRIX advertised a "CI-tracked
compile rate" over the official WebAssembly spec test suite while (a) no
workflow ran the suite and (b) no workflow checked out submodules, so
`tests/spec-testsuite` was EMPTY on every runner. This script is the number
the docs now cite, and `.github/workflows/spec-suite.yml` is the job that
produces it (with `submodules: recursive` on checkout — without that this
census measures an empty directory, which is exactly the vacuity this gate
exists to kill, so an empty/missing suite is a HARD FAILURE here, never 0/0).

WHAT IT MEASURES — a compile CENSUS, not a pass rate. Per CLAUDE.md's
compliance envelope, A DECLINE IS NOT A FAILURE: synth's loud-decline-over-
silent-miscompile stance means "refused with a machine reason" is a documented
outcome, and conflating it with a crash would manufacture exactly the
flattering/damning single number the envelope forbids. So every one of the
suite's top-level .wast files is compiled per backend with `--all-exports`
and classified into one of NINE buckets:

  ok             every exported function compiled; ELF emitted, exit 0
  partial        >=1 export compiled, the rest were per-function loud declines
                 (the #952 skipped-exports non-zero exit)
  all_declined   every EXPORT was a per-function loud decline — "no
                 functions compiled successfully (N skipped)", or (#1168, now
                 that reachable helpers are compiled too) only non-exported
                 helpers compiled and #952 reports "N of N requested exports
                 were skipped"
  module_decline whole-module loud refusal with a machine reason (start
                 function #1046; the aarch64 module-shape declines #851/#1013)
  no_module      the .wast contains no module to compile (assert-only file);
                 the harness cannot drive it
  no_exports     module(s) present but nothing exported (validation-only file)
  parse_fail     synth's WAST parser refuses the file (names.wast: the
                 deliberately-confusing U+202E identifier)
  panic          the compiler PANICKED — always a defect, never acceptable;
                 this pin is structurally forced to 0 below
  other_error    non-zero exit that matches none of the decline shapes — a NEW
                 unexpected failure class; pinned 0 so it is always RED

EXACT PINS, ratchet-style (RQ-58-METRIC): every bucket count must EQUAL the
pin — there is no "current + slack" floor to hide in, so ANY movement (a
regression OR an improvement) is a visible diff in this file in the PR that
caused it. The suite submodule is pinned by commit, and synth is
deterministic, so these counts are reproducible; when a selector/backend
change legitimately moves one, update the pin here AND the two doc rows that
cite these numbers (README.md "WebAssembly spec test suite" row,
scripts/templates/feature_matrix.md.tmpl "WASM spec test suite" row — the
SYNTH-SPEC-SUITE-CENSUS-* claims in claims.yaml bind them to this file, so
claim_check goes red if they drift apart).

Baseline measured 2026-09-01, re-measured 2026-09-06 after #1168 (the .wast
reachable-callgraph closure — see the note above PINS), and again 2026-09-09
after #1225 (RQ-65-MVPCORE: a single-module .wast now compiles on the
single-module path, and the multi-module merge refuses what it cannot
represent — see the second note above PINS), on the pinned suite commit
345367358f065375524498749470720d9cdd1418 (257 top-level .wast files; the
repo's subdirectories carry 27 more inside proposals/, deliberately out of
scope — the top level IS the merged spec, proposals are not).

WHICH PATH THIS MEASURES (#1225): the single-module path for a .wast carrying
one `(module ...)` — exactly the bytes the execution oracles compile
(`selector_parity_197_differential.py` writes every module to a `.wat`), gated
byte-for-byte by `scripts/repro/wast_single_module_path_identity_1225.py` in
the same workflow — and the multi-module MERGE for the rest, which refuses a
module carrying active data segments, accessed globals or a non-i32
signature. Before v0.65 every .wast took the merge, which handed the backends
empty data, empty globals (the Cortex-M startup never wrote R9) and i32-only
signatures, so an `ok` here could be an object that read an uninitialized
register or mis-homed an i64 parameter pair; the counts below are the
first measured on objects nothing was silently dropped from.

Usage:
  python3 scripts/spec_compile_census.py [--synth PATH] [--suite DIR]
                                         [--backend arm|riscv|aarch64] [-j N]

ci-status: wired — .github/workflows/spec-suite.yml runs this on every PR/push
"""

import argparse
import concurrent.futures
import os
import re
from collections import Counter
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Non-vacuity floor: the pinned suite commit carries exactly this many
# top-level .wast files. 0 (empty submodule) or a drifted count is RED.
EXPECTED_WAST_FILES = 257

BACKENDS = {
    "arm": ["--cortex-m"],
    "riscv": ["-b", "riscv"],
    "aarch64": ["-b", "aarch64"],
}

BUCKETS = [
    "ok", "partial", "all_declined", "module_decline",
    "no_module", "no_exports", "parse_fail", "panic", "other_error",
]

# The census pins. Update rules are in the module docstring; `panic` and
# `other_error` may NEVER be raised above 0 (enforced structurally below) —
# a panic is a compiler defect to fix, and other_error is an unclassified new
# failure class to triage, not a number to wave through.
# v0.63 / #1168 (RQ-63-WASTCLOSURE): the .wast path now applies the #235
# reachable-callgraph closure, so every number below is measured on objects
# that are COMPLETE (a retained function's callees are in the object) instead
# of the exports-only merge that shipped dangling `func_N` references at exit
# 0. Re-measured per file against the pre-fix binary; every move is one of:
#   * multi-module label collision -> module_decline (12 files on arm/rv32,
#     5 on aarch64: array, br_on_non_null, br_on_null, func, func_ptrs,
#     imports, linking, memory_trap, memory_trap64, simd_const, struct,
#     try_table): a retained direct call whose `func_N` label another merged
#     module's retained function ALSO defines — on the pre-fix binary that
#     call bound to whichever body was laid out last (a silently WRONG
#     object), now refused with the call named;
#   * skip-stack-guard-page: ok -> module_decline on arm/rv32: its one export
#     calls a helper the backend DECLINES (SUB imm > 0xFFF); pre-fix the helper
#     was never attempted and the "ok" object carried `U func_1` — the #1102
#     gate now fires on it;
#   * stack.wast on aarch64: partial -> module_decline: a now-retained callee
#     uses globals, and the .wast merge threads no globals image to the
#     aarch64 substrate (#851 refusal) — a pre-existing .wast-path gap made
#     visible, not created.
# None of the moves is a new decline class: every one is a refusal of an
# object that previously shipped wrong or unlinkable. The `partial`/
# `all_declined` split ALSO sharpened (see `classify`): an object holding only
# non-exported helpers is `all_declined`, so `AT_LEAST_ONE_EXPORT` keeps its
# name's meaning.
#
# v0.65 / #1225 (RQ-65-MVPCORE, #1017): the numbers moved AGAIN, in the honest
# direction, and for a reason of the same shape as #1168. A .wast with ONE
# module now compiles on the single-module path (what every execution oracle
# compiles), and the multi-module merge REFUSES a module carrying active data
# segments, accessed globals or an i64/f32/f64 parameter or result — the three
# shapes measured to be silently dropped or mis-typed by the merge (an `ok`
# object whose `global.get` dereferenced an R9 the startup never wrote; whose
# data bytes were absent; whose `i64.add` on two i64 params was lowered as
# `adds r3, r0, r1`). Re-measured per file against the pre-fix binary on all
# three backends (the per-file movement is in the PR); the moves are:
#   * multi-module files with those shapes: ok/partial -> module_decline
#     (`int_exprs`, `const` (402 f32/f64-result modules), `stack`,
#     `binary-leb128`, `memory`, `address`, `float_memory`, `global`,
#     `select`, `traps`, `unreached-valid`, `token`, every multi-memory twin
#     that carries data, ...) — objects that were wrong are now refused;
#   * single-module files gain: `nop`/`load` partial -> ok on arm (the merge's
#     default call_indirect guards had declined every dispatch); on aarch64
#     `f32`, `f32_bitwise`, `f32_cmp`, `f64_bitwise`, `f64_cmp`, `float_misc`,
#     `conversions` all_declined/partial -> ok (real signatures reach the
#     backend), and `block`, `br`, `br_if`, `br_table`, `call`, `if`, `load`,
#     `local_tee`, `loop`, `nop`, `return`, `left-to-right` module_decline ->
#     partial (the #851 "declares no globals" refusal was the merge's empty
#     globals table);
#   * the VCR-MEM-002 `multi-memory (#406)` decline family reaches this census
#     for the first time (a single-module twin now hands the backend its
#     second memory) — classified as `module_decline` by its tag;
#   * `no_exports` 16 -> 11: five files carrying data/globals in export-free
#     modules are refused by the merge before the "nothing exported" check.
# None of the moves is a lowering change: every one is a refusal of an object
# that shipped wrong, or the first real compile of an object the merge had
# mis-typed. The start-function invocation that landed alongside (#1017,
# Reset_Handler BLs the start function on the self-contained image) moves NO
# file here — start.wast/annotations.wast/binary.wast are multi-module and
# start0.wast is a multi-memory twin — which is exactly the file-vs-module
# gap RQ-65-MVPCORE was told to measure rather than predict; the module-level
# gain is the parity oracle's `start-function modules ... both-accepted`
# line (2 modules, 10 assertions).
# RE-MEASURED after RQ-66-BOTHWRONG (#1210). `refuse_memory64_module`
# (crates/synth-cli/src/main.rs, #1209) now refuses every `(memory i64 ...)`
# module outright, on all three backends. Exhaustively diffed file-by-file
# against the pre-fix binary (all 257 files x 3 backends): EXACTLY five real
# memory64 spec files move, all into `module_decline`, and nothing else moves
# — the delta on every backend balances to zero against these five:
#
#   binary_leb128_64.wast     no_exports     -> module_decline (all 3)
#   endianness64.wast         all_declined   -> module_decline (arm, riscv)
#                              partial        -> module_decline (aarch64)
#   load64.wast                ok            -> module_decline (arm)
#                              all_declined   -> module_decline (riscv)
#                              partial        -> module_decline (aarch64)
#   memory64-imports.wast      no_exports     -> module_decline (all 3)
#   memory_redundancy64.wast   partial        -> module_decline (all 3)
#
# `no_exports` FALLING is the correct direction here, not a hole in the
# refusal: `binary_leb128_64.wast`/`memory64-imports.wast` declare a memory64
# memory AND have no exported functions, so before this fix the "no exported
# functions" check fired first (nothing upstream knew the memory was 64-bit);
# now `refuse_memory64_module` runs earlier and reports the REAL reason. `arm:
# ok` falling by exactly one (16->15) is `load64.wast` specifically — a
# genuine memory64 module that used to compile "ok" (silently, wrongly — the
# #1209 finding) and is now correctly refused; it is the ONLY `ok`-bucket
# departure on any backend (confirmed by the exhaustive diff: `func_ptrs.wast`,
# the census's other `module_decline` file touching the `ok` count on paper,
# is IDENTICALLY `module_decline` — the pre-existing #1168 multi-module
# label-collision refusal — on the pre-fix baseline too, so it is not part of
# this delta). `memory64` family's own reported `ok` count (1, both before and
# after) is UNCHANGED and is `i64.wast`, a plain MVP-core i64-arithmetic file
# mis-attributed to the `memory64` family by the `64\.wast$` filename
# pattern — not a memory64 module, and not evidence of a hole in the refusal.
PINS = {
    "arm": dict(ok=15, partial=30, all_declined=94, module_decline=99,
                no_module=9, no_exports=9, parse_fail=1, panic=0,
                other_error=0),
    "riscv": dict(ok=9, partial=33, all_declined=96, module_decline=100,
                  no_module=9, no_exports=9, parse_fail=1, panic=0,
                  other_error=0),
    "aarch64": dict(ok=21, partial=23, all_declined=80, module_decline=114,
                    no_module=9, no_exports=9, parse_fail=1, panic=0,
                    other_error=0),
}

# Doc-cited derived figure, re-asserted at runtime against the pins above so
# this comment line cannot rot: at-least-one-export (ok+partial) per backend:
# arm=45 riscv=42 aarch64=44 (RQ-66-BOTHWRONG: 47/43/47 -> 45/42/44 — the five
# memory64 files' ok+partial losses above, see the PINS comment)
AT_LEAST_ONE_EXPORT = {"arm": 45, "riscv": 42, "aarch64": 44}


def classify(output: str, rc: int) -> str:
    if "panicked" in output:
        return "panic"
    if "Failed to parse WAST" in output:
        return "parse_fail"
    if "No module found" in output:
        return "no_module"
    if "No exported functions" in output:
        return "no_exports"
    if "no functions compiled successfully" in output:
        return "all_declined"
    if "#952:" in output:
        # #1168: since the .wast path applies the #235 reachable-callgraph
        # closure, an object can hold ONLY non-exported helpers (every export
        # declined, a callee compiled). The #952 gate then reports
        # "N of N requested export(s) were skipped". That is all_declined by
        # this census's own definition — `partial` means >= 1 EXPORT compiled,
        # and AT_LEAST_ONE_EXPORT = ok + partial is the doc-cited figure — so
        # the N-of-N form is classified by what it says, not by the gate name.
        m = re.search(r"#952: (\d+) of (\d+) requested export", output)
        if m and m.group(1) == m.group(2):
            return "all_declined"
        return "partial"
    if rc == 0:
        return "ok"
    # RQ-65-MVPCORE (#1017/#1225): a single-module .wast now compiles on the
    # single-module path, which exposed the VCR-MEM-002 multi-memory decline
    # family to this census for the first time (the merge had never handed a
    # backend a second memory). Its messages carry the machine tag
    # `multi-memory (#406)` and say "cannot be compiled ... compiles only on
    # --relocatable" — a decline with a reason, matched on its TAG so a
    # rewording of the prose cannot move 22 files into `other_error`.
    if re.search(r"refus|declin|multi-memory \(#406\)", output, re.IGNORECASE):
        return "module_decline"
    return "other_error"


def run_backend(synth: Path, backend: str, files, jobs: int):
    counts = {b: 0 for b in BUCKETS}
    examples = {}  # bucket -> first (file, message) for the report

    def one(wast: Path):
        with tempfile.TemporaryDirectory() as td:
            out = Path(td) / (wast.stem + ".elf")
            p = subprocess.run(
                [str(synth), "compile", str(wast), "-o", str(out),
                 "--all-exports", *BACKENDS[backend]],
                capture_output=True, text=True, timeout=300,
            )
        return wast.name, classify(p.stdout + p.stderr, p.returncode), \
            (p.stdout + p.stderr).strip().splitlines()[:1]

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        for name, bucket, msg in ex.map(one, files):
            counts[bucket] += 1
            examples.setdefault(bucket, []).append((name, msg))
    return counts, examples



# ---------------------------------------------------------------------------
# RQ-63-SPECFAM (v0.63): the per-family split.
#
# This census publishes ONE derived figure per backend (`at-least-one-export`).
# That figure is correct and gated, and it is the wrong number to plan from: it
# averages families synth TARGETS with families synth has never implemented.
# Split by family it says two things the aggregate hides — MVP core is 12 of
# 80 fully-ok on arm (the scalar foundation every other family rests on;
# 14 of 114 in v0.63 before the family re-attribution and the #1225 path fix
# below), and 89 files (35 % of the suite) are families with ZERO support on
# any backend, which is a declared BOUNDARY rather than a failure.
#
# Families are matched on the suite's own filenames — the merged proposals are
# named there (simd_*, ref_*, table_*, memory_copy, return_call, try*, gc_*).
# Ordered: the first pattern that matches wins, MVP core is the fallback.
# ---------------------------------------------------------------------------
#
# RQ-65-MVPCORE (#1017, v0.65): two families were mis-attributed to MVP core,
# and the pin below moved 114 -> 79 when they were re-attributed:
#   * MULTI-MEMORY. The proposal merged into the core suite (Wasm 3.0,
#     2025-09-17; suite commit 4b24564 added the files) as DIGIT-SUFFIXED TWINS
#     of the core files — `address0.wast` beside `address.wast`, `load0..2`,
#     `memory_size0..3`, `data0/1`, `linking0..3`, `imports0..4`, ... — plus
#     `memory-multi.wast` and `data_drop0.wast`. Content-verified: every one
#     declares 2..21 memories per module (`exports0` 21, `data0` 19). The old
#     `^multi.?memory|^memory_multi` pattern matched NONE of them (and never
#     matched `memory-multi` either — hyphen vs underscore), so 32 of them sat
#     in MVP core and the family's top arm blocker ("multi-memory: an op on
#     memory N cannot be lowered into a self-contained image", 17 files as the
#     SOLE blocker) was a multi-memory decline mis-filed as a scalar-core one.
#     The family is matched BEFORE the features it twins (`data0` is a
#     multi-memory data test, `linking0` a multi-memory linking test) so a
#     decline there is attributed to the capability actually missing.
#   * RELAXED SIMD lane files: `i8x16_relaxed_swizzle`, `i16x8_relaxed_q15mulr_s`,
#     `i32x4_relaxed_trunc` — git-recorded renames from
#     `proposals/relaxed-simd/` in the same suite commit; they start with a lane
#     type, not `relaxed_`.
#   Also: `^data\b` could never match `data0` (no word boundary between `a` and
#   `0`), which is how `data0`/`data1` fell through to MVP core too.
# Digit-suffixed twins are enumerated, not `\d\.wast$`-wildcarded: `i32.wast`
# and `f64.wast` end in a digit too, and `address64.wast` is memory64.
# ---------------------------------------------------------------------------
FAMILIES = [
    ("SIMD",               r"^simd_"),
    ("relaxed SIMD",       r"^relaxed_|^i(8x16|16x8|32x4)_relaxed_"),
    ("threads / atomics",  r"^atomic|shared|thread"),
    ("GC",                 r"^gc_|^struct|^array|^ref_(cast|test)|^type-(sub|equiv|rec)|^br_on_(cast|null)"),
    ("exception handling", r"^try|^throw|^tag|^rethrow|^exception"),
    ("tail call",          r"^return_call"),
    ("multi-memory",       r"^(address|align|binary|data|exports|float_exprs|float_memory"
                           r"|imports|linking|load|memory_copy|memory_fill|memory_init"
                           r"|memory_size|memory_trap|start|store|traps)\d\.wast$"
                           r"|^memory-multi\.wast$|^data_drop\d\.wast$"
                           r"|^multi.?memory|^memory_multi"),
    ("reference types",    r"^ref_|^table_|^table\.|^elem|^linking"),
    ("bulk memory",        r"^memory_(copy|fill|init|grow)|^data[._]|^data\.wast$|^bulk"),
    ("memory64",           r"64\.wast$|^address64|^align64|^memory64"),
    ("multi-value",        r"^multi.?value|^func_ptrs"),
    ("MVP core",           r".*"),
]


def family_of(name: str) -> str:
    for label, pat in FAMILIES:
        if re.search(pat, name):
            return label
    return "MVP core"


# RQ-63-SPECFAM, hardened after the v0.63 cold review. The FIRST version of
# this pin checked only that the DOC said 14 — it could not fail when the
# census moved, which is the doc-says-doc shape. These are the measured
# per-family `ok` counts, pinned like the bucket PINS above so a family count
# that moves reddens the census itself rather than drifting until someone
# re-reads the doc.
#
# v0.65 (RQ-65-MVPCORE): MVP core is 80 files, not 114 (see FAMILIES), and its
# `ok` counts are measured on the single-module path / refusing merge (#1225):
# arm 14 -> 12, riscv 11 -> 9, aarch64 21 -> 18 — with 12 / 9 / 18 of 80 being
# the row, not of 114. `multi-memory` is pinned too now that it is a family.
#
# EXTENDED after RQ-66-BOTHWRONG (#1210): the census's own investigation of
# `arm: ok` falling 16->15 needed the `memory64` family's `ok` count named
# per-file, and it was not pinned — exactly the drift this pin exists to
# prevent, in a family this release just made a refusal decision about.
# `memory64`, `bulk memory`, `reference types` and `multi-value` are added.
# NAMED, because "family assigned by filename" proves nothing about content:
# `memory64`'s `ok` survivors are `i64.wast` (all 3 backends) and, on
# aarch64 only, ALSO `f64.wast` — both plain MVP-core numeric-op files
# mis-attributed by the family's `64\.wast$` filename pattern, not memory64
# modules; every GENUINE memory64 file is `module_decline` on every backend
# (verified file-by-file, see the PINS comment above). `bulk memory`'s one
# `ok` (arm only) is `memory_fill.wast`, a real bulk-memory op, unaffected by
# this PR. `reference types` and `multi-value` are 0 everywhere; the one
# `multi-value` file (`func_ptrs.wast`) is `module_decline` via the
# pre-existing #1168 multi-module label-collision refusal, unchanged by this
# PR (confirmed identical on the pre-fix binary).
FAMILY_OK_PINS = {
    "arm":     {"MVP core": 12, "multi-memory": 1, "SIMD": 0, "GC": 0,
                "relaxed SIMD": 0, "exception handling": 0, "tail call": 0,
                "memory64": 1, "bulk memory": 1, "reference types": 0,
                "multi-value": 0},
    "riscv":   {"MVP core": 9, "multi-memory": 0, "SIMD": 0, "GC": 0,
                "relaxed SIMD": 0, "exception handling": 0, "tail call": 0,
                "memory64": 0, "bulk memory": 0, "reference types": 0,
                "multi-value": 0},
    "aarch64": {"MVP core": 18, "multi-memory": 1, "SIMD": 0, "GC": 0,
                "relaxed SIMD": 0, "exception handling": 0, "tail call": 0,
                "memory64": 2, "bulk memory": 0, "reference types": 0,
                "multi-value": 0},
}


def report_by_family(backend: str, per_file: dict) -> list:
    """Print the per-family split. REPORTING ONLY — never gates, because the
    pins above are the gate and a second gate on the same measurement would be
    a second source of truth for it."""
    tally = {}
    for name, bucket in per_file.items():
        tally.setdefault(family_of(name), Counter())[bucket] += 1
    print(f"\n  per-family split ({backend}) — files ok / partial / declined:")
    rows = sorted(tally.items(), key=lambda kv: -sum(kv[1].values()))
    for fam_name, ctr in rows:
        tot = sum(ctr.values())
        dec = ctr["all_declined"] + ctr["module_decline"]
        print(f"    {fam_name:<20}{tot:>5} files   {ctr['ok']:>4} ok  "
              f"{ctr['partial']:>4} partial  {dec:>4} declined")
    # The pin. Reporting became a GATE here after the cold review found the
    # doc-side pin could not fail on a census move.
    fails = []
    for fam_name, expect in FAMILY_OK_PINS.get(backend, {}).items():
        got = tally.get(fam_name, Counter())["ok"]
        if got != expect:
            fails.append(f"{backend}: family {fam_name!r} ok = {got}, "
                         f"pin = {expect} — re-measure, then update the pin "
                         f"AND docs/status/SPEC_FAMILY_CENSUS.md together")
    return fails


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--synth", default=str(ROOT / "target/debug/synth"))
    ap.add_argument("--suite", default=str(ROOT / "tests/spec-testsuite"))
    ap.add_argument("--backend", choices=sorted(BACKENDS), action="append",
                    help="restrict to one backend (repeatable); default all. "
                         "Restricting SKIPS the pin gate for the others but "
                         "never weakens the ones that run.")
    ap.add_argument("-j", "--jobs", type=int, default=os.cpu_count() or 4)
    args = ap.parse_args()

    fails = []

    # Structural guard: the two never-raise pins.
    for be, pins in PINS.items():
        for never in ("panic", "other_error"):
            if pins[never] != 0:
                fails.append(
                    f"PINS[{be!r}][{never!r}] = {pins[never]} — this pin may "
                    f"never be raised above 0; fix the defect instead")
    # Structural guard: the doc-cited derived figure must equal ok+partial.
    for be, pins in PINS.items():
        derived = pins["ok"] + pins["partial"]
        if AT_LEAST_ONE_EXPORT[be] != derived:
            fails.append(
                f"AT_LEAST_ONE_EXPORT[{be!r}] = {AT_LEAST_ONE_EXPORT[be]} but "
                f"PINS say ok+partial = {derived} — the doc-cited figure "
                f"rotted; move them together")
    if fails:
        for f in fails:
            print(f"FAIL: {f}")
        return 1

    synth = Path(args.synth)
    if not synth.is_file():
        print(f"FAIL: synth binary not found at {synth} — build it first "
              f"(cargo build --features riscv --bin synth)")
        return 1

    suite = Path(args.suite)
    files = sorted(suite.glob("*.wast")) if suite.is_dir() else []
    if len(files) != EXPECTED_WAST_FILES:
        print(f"FAIL: expected {EXPECTED_WAST_FILES} top-level .wast files in "
              f"{suite}, found {len(files)}.")
        if len(files) == 0:
            print("  The suite is EMPTY or missing. In CI this means the "
                  "checkout lacks `submodules: recursive`; locally run:")
            print("    git submodule update --init tests/spec-testsuite")
            print("  A census over an empty directory is a vacuous success — "
                  "refusing to report one (#1095).")
        else:
            print("  The submodule commit moved. Re-measure, then update "
                  "EXPECTED_WAST_FILES, PINS, and the doc rows together.")
        return 1

    backends = args.backend or sorted(BACKENDS)
    for be in backends:
        counts, examples = run_backend(synth, be, files, args.jobs)
        print(f"\n== {be} census over {len(files)} files ==")
        for b in BUCKETS:
            marker = ""
            if counts[b] != PINS[be][b]:
                marker = f"   <-- PIN {PINS[be][b]}"
                fails.append(
                    f"{be}: bucket {b!r} = {counts[b]}, pin = {PINS[be][b]}")
            print(f"  {b:15} {counts[b]:4}{marker}")
        for b in ("panic", "other_error"):
            for name, msg in examples.get(b, []):
                print(f"    {b}: {name}: {msg[0] if msg else '(no output)'}")
        alo = counts["ok"] + counts["partial"]
        print(f"  at-least-one-export = {alo} "
              f"(doc-cited {AT_LEAST_ONE_EXPORT[be]})")
        # RQ-63-SPECFAM: the same measurement, split by family. Reporting only.
        per_file = {name: b for b, rows in examples.items() for name, _ in rows}
        fails.extend(report_by_family(be, per_file))

    print()
    if fails:
        print(f"RESULT: FAIL ({len(fails)} pin mismatch(es))")
        for f in fails:
            print(f"  {f}")
        print("A count that moved is a compiler-behavior change: verify it is "
              "intended, then update PINS here AND the README/FEATURE_MATRIX "
              "rows in the same PR (claims.yaml binds them).")
        return 1
    print(f"RESULT: PASS — census matches pins for: {', '.join(backends)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
