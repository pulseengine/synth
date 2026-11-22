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

CLOSED BY #1763 (v0.92 batch 2). The cause named above was the cause: the
selector read and wrote every local through the GP file. It now takes the
decoder's declared float locals, and a float local is read into an FP temp
and written from one. Measured with the pre-fix and the fixed binary on the
same three sources: 2 / 1 / 1 instances before, 0 / 0 / 0 after. The three
KNOWN entries are deleted (closed by a fix, not merged or re-keyed).

WHAT THE ORACLE ASSERTS NOW. A count of zero is what a refusal of the whole
file would also produce, so zero alone proves nothing. Each source also names
the exports that used to carry the refusal, and each of them must be COMPILED:
the CLI must print no `skipping function '<export>'` line for it, for any
reason. The needle is widened to both directions of the class ("expected GP
operand, got FP" and "expected FP operand, got GP", any operator), which
measured 7 over the whole top-level suite before the fix and 0 after; over
these three sources it must be 0. The EXECUTED evidence that the newly
compiled code is right is `crates/synth-oracle/tests/float_local_file_1763.rs`
(kiln against unicorn, 94 AArch64 cases).

Usage:
  python3 scripts/repro/aarch64_operand_class_1231_differential.py
    [--synth PATH] [--suite DIR]
"""

import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
HERE = Path(__file__).resolve().parent

# Both directions of the operand-class refusal, whatever operator reports it.
NEEDLES = ("expected GP operand, got FP", "expected FP operand, got GP")

# ---------------------------------------------------------------------------
# KNOWN — source -> exact count of still-open instances. A pin that moves in
# either direction is red. EMPTY since #1763: every source measures 0, and a
# source absent from this table is held to 0.
# ---------------------------------------------------------------------------
KNOWN: dict[str, int] = {}

# The exports that carried the refusal before #1763 (2 + 1 + 1, the table
# this oracle pinned). Each must be compiled, not skipped for any reason.
MUST_COMPILE = {
    "local_set.wast": ("type-local-f32", "type-local-f64"),
    "memory_redundancy.wast": ("test_dead_store",),
    "aarch64_align_f32_switch_1231.wat": ("f32_align_switch",),
}


def measure(synth: Path, path: Path) -> tuple[int, str]:
    """(instances of the class, the CLI's whole output)."""
    # A real output path: the aarch64 driver writes a safety manifest beside
    # the object, so `-o /dev/null` fails AFTER a successful compile.
    with tempfile.TemporaryDirectory(prefix="synth-1231-") as d:
        p = subprocess.run(
            [str(synth), "compile", str(path), "-b", "aarch64",
             "--all-exports", "--allow-skipped-exports",
             "-o", str(Path(d) / "out.o")],
            capture_output=True, text=True, timeout=120,
        )
    out = p.stdout + p.stderr
    return sum(out.count(n) for n in NEEDLES), out


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
    compiled = 0
    expected = sum(len(v) for v in MUST_COMPILE.values())
    print(f"{'source':<38}{'measured':>9}{'pin':>6}{'compiled':>10}")
    for name, path in sources.items():
        n_compiles += 1
        got, out = measure(synth, path)
        want = KNOWN.get(name, 0)
        total += got
        marker = "" if got == want else "  <-- PIN MISMATCH"
        ok = [e for e in MUST_COMPILE[name]
              if f"skipping function '{e}'" not in out]
        # No function compiled at all: nothing above is evidence of anything.
        if "no functions compiled successfully" in out or "Compiled " not in out:
            ok = []
        compiled += len(ok)
        print(f"{name:<38}{got:>9}{want:>6}"
              f"{len(ok):>8}/{len(MUST_COMPILE[name])}{marker}")
        if got != want:
            fails.append(
                f"{name}: measured {got} operand-class refusals, pin says "
                f"{want}. Re-measure, then update KNOWN here.")
        for e in MUST_COMPILE[name]:
            if e not in ok:
                fails.append(
                    f"{name}: export '{e}' is not compiled — it carried the "
                    f"#1231 refusal before #1763 and must compile now.")

    print(f"#1231 CHECKS={n_compiles}/3 sources; TOTAL={total}")
    print(f"#1231 PINS={len(KNOWN)}")
    print(f"#1231 CLOSED: {compiled} of {expected} formerly refused exports compile")
    if fails:
        print(f"RESULT: FAIL ({len(fails)} mismatch(es))")
        for f in fails:
            print(f"  {f}")
        return 1
    print(f"RESULT: PASS — {total} GP/FP operand-class refusals across "
          f"{len(sources)} sources, and the {compiled} exports that carried "
          f"them compile")
    return 0


if __name__ == "__main__":
    sys.exit(main())
