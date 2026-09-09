#!/usr/bin/env python3
# ci-status: wired
# ci-checks: compiles >= 12
"""RQ-66-UNWATCHED (#1229): the ARM direct selector (and RISC-V's sibling)
REJECT VALID spec modules — "stack underflow: malformed WASM or compiler
bug" — on the stack-polymorphic dead-code shape the WASM spec allows after
an unconditional terminator (`unreachable`/`br`/`br_table`/`return`).

THE DEFECT. `synth compile <file>.wast --cortex-m --all-exports` (the v0.65
census invocation, #1225), per-function skip reason:

    instruction selection failed: Synthesis failed: stack underflow:
    malformed WASM or compiler bug

Every one of the six files below is accepted whole by wasmtime — "malformed
WASM" is not the branch that actually fired. Per WASM's stack-polymorphic
typing of dead code (spec 3.3.6): once an `unreachable`/`br`/`br_table`/
`return` executes, everything up to the enclosing `end` is UNREACHABLE and
type-checks against an infinite-depth polymorphic operand stack — the
validator lets it pop values that were never really pushed. The direct
selector's real, explicit `Vec<StackVal>` (`pop_operand` /
`crates/synth-synthesis/src/instruction_selector.rs:1484` and its three
sibling call sites) has no such model: it walks dead code as if it were
live, and the first pop past the top raises this exact message.
RISC-V's own explicit-stack selector
(`crates/synth-backend-riscv/src/selector.rs:136`,
`"invalid program — stack underflow at op {0:?}"`) is the same defect in a
sibling implementation, not a coincidence of wording.

THE #1207/#1229 JOINT VERDICT — one shared missing capability, evidenced,
with an honest boundary on how far it reaches. MEASURED: across these six
files, AArch64 raises this defect's message class ZERO times; its only two
declines on `br.wast` ("call to function N: value stack holds ... but the
callee takes ...", "operand-stack underflow") are a call-ARITY check on a
DIFFERENT construct (`call`/`call_indirect`), not the dead-code-after-
terminator shape this file measures — a different mechanism, not a partial
hit on this one. AArch64's `WasmOp::End` handler
(`crates/synth-backend-aarch64/src/selector.rs:2207`) carries a `reachable`
flag and an explicit end-of-block arity check
("end: value-carrying block left no result on the value stack") that ARM's
and RISC-V's selectors simply do not have anywhere. That single missing
capability — track reachability across an unconditional terminator, and only
assert value-stack arity on the REACHABLE fall-through edge — is the fix for
#1229 IN FULL (dead code stops being walked as live, so `pop_operand` stops
underflowing on synthesized-away values; AArch64 already has zero instances
of this class, so nothing here contradicts porting its mechanism).

For #1207 the same port is necessary but NOT sufficient, and the #1207
oracle's own measurement says exactly how much of it: only 1 of its 13
fixtures (`cu_add_tee`, a `br_if` that consumes a loop's only result through
real control flow) is caught by AArch64's existing check — the other 12
(`type-empty-{block,loop,if}-{i32,i64,f32,f64}`, a COMPLETELY EMPTY body with
a declared result) are silently accepted by ALL THREE backends, AArch64
included. AArch64's own arity check evidently does not fire on an empty
frame (behavior measured; the exact guard that skips it has not been traced
in this pass). VERDICT: #1207 and #1229 are ONE missing capability in the
ARM/RISC-V direct selectors, not two independent defects — but porting
AArch64's mechanism verbatim would close #1229 completely and #1207 only
1/13 of the way; the empty-body arity check is a second, narrower gap that
exists even in the one implementation that has the reachability model at
all. Filed as a decline (not fixed) here per the issue: it costs reach but
is the SOLE blocker of zero files in this population (every file carrying it
also carries an unrelated decline) and a fix needs its own execution oracle
over the newly-accepted dead-code shapes — this file watches the count; it
does not lift the decline.

MEASURED (re-derive with `--synth <path>`; every count here is exact-pinned):

  file             arm   riscv
  ---------------- ----  -----
  br.wast            12     31
  br_table.wast       4      4
  call.wast           3      0
  loop.wast           1      1
  return.wast        29      0
  unreachable.wast   25     20
  TOTAL              74     56

(arm total of 74 matches the issue exactly; the riscv split differs in shape
from the issue's rougher "3 files each" paraphrase — re-measured here per
file, which is the authority.)

Usage:
  python3 scripts/repro/false_reject_1229_differential.py [--synth PATH]
    [--suite DIR]
"""

import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent

FILES = ["br.wast", "br_table.wast", "call.wast", "loop.wast", "return.wast",
         "unreachable.wast"]

BACKENDS = {
    "arm": (["--cortex-m"], "stack underflow: malformed WASM or compiler bug"),
    "riscv": (["-b", "riscv"], "invalid program — stack underflow"),
}

# ---------------------------------------------------------------------------
# KNOWN — (file, backend) -> exact count. A pin that moves in EITHER
# direction is red (a fix landing without updating this IS the regression
# this file exists to catch, and a genuine fix must move this pin in the
# same PR that lands it — see #1229's own "filed rather than fixed" note).
# ---------------------------------------------------------------------------
KNOWN: dict[tuple[str, str], int] = {
    ("br.wast", "arm"): 12,
    ("br_table.wast", "arm"): 4,
    ("call.wast", "arm"): 3,
    ("loop.wast", "arm"): 1,
    ("return.wast", "arm"): 29,
    ("unreachable.wast", "arm"): 25,
    ("br.wast", "riscv"): 31,
    ("br_table.wast", "riscv"): 4,
    ("call.wast", "riscv"): 0,
    ("loop.wast", "riscv"): 1,
    ("return.wast", "riscv"): 0,
    ("unreachable.wast", "riscv"): 20,
}
assert set(KNOWN) == {(f, b) for f in FILES for b in BACKENDS}


def measure(synth: Path, suite: Path, wast: str, backend: str) -> int:
    flags, needle = BACKENDS[backend]
    p = subprocess.run(
        [str(synth), "compile", str(suite / wast), *flags,
         "--all-exports", "--allow-skipped-exports",
         "-o", "/dev/null"],
        capture_output=True, text=True, timeout=300,
    )
    return (p.stdout + p.stderr).count(needle)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--synth", default=str(ROOT / "target/debug/synth"))
    ap.add_argument("--suite", default=str(ROOT / "tests/spec-testsuite"))
    args = ap.parse_args()

    synth = Path(args.synth)
    if not synth.is_file():
        print(f"FAIL: synth binary not found at {synth} — build it first "
              f"(cargo build --features riscv -p synth-cli)")
        return 1
    suite = Path(args.suite)
    for f in FILES:
        if not (suite / f).is_file():
            print(f"FAIL: {suite / f} missing — checkout needs "
                  f"`submodules: recursive`")
            return 1

    fails: list[str] = []
    n_compiles = 0
    total = 0
    print(f"{'file':<18}{'backend':<8}{'measured':>9}{'pin':>6}")
    for f in FILES:
        for be in BACKENDS:
            n_compiles += 1
            got = measure(synth, suite, f, be)
            want = KNOWN[(f, be)]
            total += got
            marker = "" if got == want else "  <-- PIN MISMATCH"
            print(f"{f:<18}{be:<8}{got:>9}{want:>6}{marker}")
            if got != want:
                fails.append(
                    f"{f} / {be}: measured {got} instances of the false-"
                    f"reject class, pin says {want}. Re-measure, then update "
                    f"KNOWN here — moving DOWN without a fix is as red as "
                    f"moving up without one.")

    print(f"#1229 CHECKS={n_compiles}/12 (file,backend) cells; "
          f"TOTAL false-rejects={total}")
    print(f"#1229 PINS={len(KNOWN)}")
    if fails:
        print(f"RESULT: FAIL ({len(fails)} mismatch(es))")
        for f in fails:
            print(f"  {f}")
        return 1
    print(f"RESULT: PASS — {total} false-rejections of valid WASM pinned "
          f"exactly as measured across {len(FILES)} files x {len(BACKENDS)} "
          f"backends")
    return 0


if __name__ == "__main__":
    sys.exit(main())
