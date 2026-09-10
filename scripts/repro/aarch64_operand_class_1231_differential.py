#!/usr/bin/env python3
# ci-status: wired
# ci-checks: compiles >= 3
"""RQ-66-UNWATCHED (#1231): the AArch64 selector confuses operand CLASSES —
"local.set: expected GP operand, got FP" — because its home-slot model
treats every local as GP-class, so an FP-typed local cannot be homed.

THE DEFECT. `synth compile <file>.wast -b aarch64 --all-exports`, per-
function skip reason:

    aarch64 selector: local.set: expected GP operand, got FP

Consistent with the sibling decline "function homes its parameters ... but
declares a FLOAT parameter — the aarch64 home-slot model is single-class"
(referenced in the issue; not re-measured here). A loud decline, not a wrong
answer — AArch64 accepts 1.6% of real modules (#1017/#1225 census), and this
class sits on the path of almost anything the backend would newly accept.

THE ISSUE'S OWN FILE-LEVEL TABLE IS WRONG FOR align.wast, AND THAT IS WORTH
STATING PLAINLY: `align.wast` carries 25 top-level `(module ...)` forms, so
`synth compile align.wast -b aarch64 --all-exports` (the file-level census
invocation) takes the #1225 multi-module MERGE path, which refuses the WHOLE
FILE before any per-function selection runs (module 23 needs an i64/f32/f64
result the merge's i32-only signature tables cannot represent). This class
is UNREACHABLE on that invocation for align.wast — it cannot contribute 1 to
a count measured that way. It only reproduces on the SINGLE-MODULE path (the
real MVP-core census's per-module extraction, #1017/#1225), which is exactly
what `aarch64_align_f32_switch_1231.wat` is: `f32_align_switch` extracted
verbatim from align.wast (module at line 458, function at line 462) into its
own file. The corrected accounting: `local_set.wast` (2, whole-file) +
`memory_redundancy.wast` (1, whole-file) + the align.wast extraction (1) = 4
— same total the issue reports, reached by the route that can actually
measure it.

MEASURED (exact pin; `--allow-skipped-exports` so a decline doesn't also
trip the unrelated #952 export-skip gate):

  local_set.wast          2   (type-local-f32, type-local-f64)
  memory_redundancy.wast  1   (test_dead_store)
  align_f32_switch (ext.) 1   (f32_align_switch, single-module extraction)
  TOTAL                   4

Usage:
  python3 scripts/repro/aarch64_operand_class_1231_differential.py
    [--synth PATH] [--suite DIR]
"""

import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
HERE = Path(__file__).resolve().parent

NEEDLE = "local.set: expected GP operand, got FP"

# ---------------------------------------------------------------------------
# KNOWN — (source, is_suite_file) -> exact count. A pin that moves in either
# direction is red.
# ---------------------------------------------------------------------------
KNOWN: dict[str, int] = {
    "local_set.wast": 2,
    "memory_redundancy.wast": 1,
    "aarch64_align_f32_switch_1231.wat": 1,
}


def measure(synth: Path, path: Path) -> int:
    p = subprocess.run(
        [str(synth), "compile", str(path), "-b", "aarch64",
         "--all-exports", "--allow-skipped-exports", "-o", "/dev/null"],
        capture_output=True, text=True, timeout=120,
    )
    return (p.stdout + p.stderr).count(NEEDLE)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--synth", default=str(ROOT / "target/debug/synth"))
    ap.add_argument("--suite", default=str(ROOT / "tests/spec-testsuite"))
    args = ap.parse_args()

    synth = Path(args.synth)
    if not synth.is_file():
        print(f"FAIL: synth binary not found at {synth} — build it first "
              f"(cargo build -p synth-cli)")
        return 1
    suite = Path(args.suite)

    sources = {
        "local_set.wast": suite / "local_set.wast",
        "memory_redundancy.wast": suite / "memory_redundancy.wast",
        "aarch64_align_f32_switch_1231.wat": HERE / "aarch64_align_f32_switch_1231.wat",
    }
    for name, path in sources.items():
        if not path.is_file():
            print(f"FAIL: {path} missing")
            return 1

    fails: list[str] = []
    n_compiles = 0
    total = 0
    print(f"{'source':<38}{'measured':>9}{'pin':>6}")
    for name, path in sources.items():
        n_compiles += 1
        got = measure(synth, path)
        want = KNOWN[name]
        total += got
        marker = "" if got == want else "  <-- PIN MISMATCH"
        print(f"{name:<38}{got:>9}{want:>6}{marker}")
        if got != want:
            fails.append(
                f"{name}: measured {got} instances of {NEEDLE!r}, pin says "
                f"{want}. Re-measure, then update KNOWN here.")

    print(f"#1231 CHECKS={n_compiles}/3 sources; TOTAL={total}")
    print(f"#1231 PINS={len(KNOWN)}")
    if fails:
        print(f"RESULT: FAIL ({len(fails)} mismatch(es))")
        for f in fails:
            print(f"  {f}")
        return 1
    print(f"RESULT: PASS — {total} local.set GP/FP operand-class confusions "
          f"pinned exactly as measured across {len(sources)} sources")
    return 0


if __name__ == "__main__":
    sys.exit(main())
