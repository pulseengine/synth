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
  all_declined   every function was a per-function loud decline — "no
                 functions compiled successfully (N skipped)"
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

Baseline measured 2026-09-01 on the pinned suite commit
345367358f065375524498749470720d9cdd1418 (257 top-level .wast files; the
repo's subdirectories carry 27 more inside proposals/, deliberately out of
scope — the top level IS the merged spec, proposals are not).

Usage:
  python3 scripts/spec_compile_census.py [--synth PATH] [--suite DIR]
                                         [--backend arm|riscv|aarch64] [-j N]

ci-status: wired — .github/workflows/spec-suite.yml runs this on every PR/push
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
PINS = {
    "arm": dict(ok=23, partial=69, all_declined=135, module_decline=4,
                no_module=9, no_exports=16, parse_fail=1, panic=0,
                other_error=0),
    "riscv": dict(ok=13, partial=69, all_declined=145, module_decline=4,
                  no_module=9, no_exports=16, parse_fail=1, panic=0,
                  other_error=0),
    "aarch64": dict(ok=27, partial=33, all_declined=113, module_decline=58,
                    no_module=9, no_exports=16, parse_fail=1, panic=0,
                    other_error=0),
}

# Doc-cited derived figure, re-asserted at runtime against the pins above so
# this comment line cannot rot: at-least-one-export (ok+partial) per backend:
# arm=92 riscv=82 aarch64=60
AT_LEAST_ONE_EXPORT = {"arm": 92, "riscv": 82, "aarch64": 60}


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
        return "partial"
    if rc == 0:
        return "ok"
    if re.search(r"refus|declin", output, re.IGNORECASE):
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
