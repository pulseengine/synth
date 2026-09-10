#!/usr/bin/env python3
# ci-status: wired
# ci-checks: compiles >= 39
"""RQ-66-UNWATCHED (#1207): `synth compile` ACCEPTS invalid WebAssembly —
exit 0, ELF emitted, on modules wasmtime rejects at validation.

THE DEFECT, per the issue's own repro (a stack-height violation at a
`loop`-`(result i32)` end: `br_if` pops the loop's only value, and the
fall-through path reaches the loop's end with the result stack empty):

    (module
      (func (export "cu_add_tee") (param i32) (result i32) (local i32)
        (loop (result i32)
          local.get 1 i32.const 1 i32.add local.tee 1
          local.get 0 i32.lt_s
          br_if 0)))

wasmtime (41.0.0): "type mismatch: expected i32 but nothing on stack"
(rejected at validation, before any execution). `synth compile ... --target
cortex-m4 --all-exports`: exit 0, ELF emitted. Same class as #1209 (memory64
accepted and silently wrong) — a compiler that accepts invalid input has no
defined obligation about what it emits — except #1209 has 513 pinned
divergence counts and this had NOTHING watching it before this file.

WHY A CURATED FIXTURE SET, NOT A FULL SPEC-SUITE `assert_invalid` CENSUS.
The issue's own "suggested gate" is to feed every `assert_invalid` form in
the suite to `synth compile` and require non-zero exit. That census was
tried and discarded: most of the suite's ~144 `assert_invalid`-bearing files
carry invalid modules for reasons that have NOTHING to do with this defect
(duplicate exports, unknown locals, import/export shape errors, ops synth
does not lower at all) — `synth compile` already exits non-zero on plenty of
those, but for UNRELATED reasons (parse/decode declines, unsupported-op
declines). Scoring "exit != 0" as "correctly declined" over that population
would manufacture a large green number that mostly measures synth's feature
gaps, not this validator gap, and the pin would move on every unrelated
lowering change — exactly the vacuous-census failure this project keeps
finding and re-banning. So this oracle uses a SMALL fixture set restricted
to ops synth otherwise fully supports (i32/i64/f32/f64 consts, block/loop/if,
locals, br_if), so the ONLY possible reason to reject is the stack-height
violation at a value-carrying construct's end.

THE FIXTURE FAMILY — all real spec-suite `assert_invalid` entries (not
invented), the minimal "declared result, nothing produced" shape:
`type-empty-{i32,i64,f32,f64}` x `{block,loop,if}` (`tests/spec-testsuite/
block.wast` lines 505-517, `loop.wast` lines 609-621, `if.wast` lines
844-856), plus the issue's own richer `cu_add_tee` repro (a `br_if` that
consumes the ONLY value a `loop (result i32)` needs at its end — the same
defect through actual control flow rather than an empty body).

MEASURED: of 13 fixtures x 3 backends = 39 cells, ARM and RISC-V accept all
13 (wrongly) and AArch64 accepts 12 of 13 — it declines ONLY `cu_add_tee`
("aarch64 selector: end: value-carrying block left no result on the value
stack"), which is a REAL but PARTIAL capability: AArch64's `End` handler
(`crates/synth-backend-aarch64/src/selector.rs`, `WasmOp::End`) DOES check
stack occupancy for a value-carrying frame's fall-through edge, yet still
accepts all 12 `type-empty-*` fixtures (a completely EMPTY block/loop/if
body with a declared result). ONE PLAUSIBLE MECHANISM, traced but not
proven exhaustively: at the construct's OPEN (`WasmOp::Block`, line ~1675,
and the sibling `Loop`/`If` sites) the frame's arity comes from
`block_arity.get(ord).copied().unwrap_or((0, 0))` — a decoder-provided
per-occurrence side-table with a VOID fallback. If that lookup misses for
these trivially-empty bodies, `result_arity` becomes 0, and the `End`
check's own `frame.result_arity == 1` guard is then trivially false — the
check never fires, not because the empty body is special-cased, but because
the arity it would check against silently degraded to void first. This
explains the measured 12/12 accepts without requiring a second, independent
bug in the `End` handler itself; it has not been confirmed by tracing why
the side-table lookup misses for an empty body specifically. The 12
fixtures are, regardless of mechanism, a THREE-BACKEND-UNIVERSAL defect;
only the 1 richer fixture shows AArch64 ahead of ARM/RISC-V (see the #1229 sibling
oracle's docstring for what AArch64 has that ARM/RISC-V lack, and the joint
verdict on whether #1207 and #1229 share a root cause).

Ground truth: each fixture is confirmed invalid by wasmtime IN-PROCESS
(`wasmtime.Module.validate`, no CLI dependency) every run — this oracle
would fail loudly if a fixture were ever accidentally valid.

Usage:
  python3 scripts/repro/invalid_accept_1207_differential.py [--synth PATH]
"""

import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime

ROOT = Path(__file__).resolve().parent.parent.parent

BACKENDS = {
    "arm": ["--cortex-m"],
    "riscv": ["-b", "riscv"],
    "aarch64": ["-b", "aarch64"],
}

# ---------------------------------------------------------------------------
# The fixture family. Every entry MUST be rejected by wasmtime (asserted at
# runtime, not assumed) — this oracle proves synth's ACCEPTANCE is wrong, and
# that proof is worthless if the fixture were secretly valid.
# ---------------------------------------------------------------------------
FIXTURES: dict[str, str] = {}
for ctor in ("block", "loop", "if"):
    for ty in ("i32", "i64", "f32", "f64"):
        if ctor == "if":
            body = f'(if (i32.const 0) (then))'
        else:
            body = f"({ctor})"
        FIXTURES[f"type-empty-{ctor}-{ty}"] = (
            f'(module (func (export "f") (result {ty}) {body}))'
        )

FIXTURES["cu_add_tee"] = """\
(module
  (func (export "cu_add_tee") (param i32) (result i32) (local i32)
    (loop (result i32)
      local.get 1 i32.const 1 i32.add local.tee 1
      local.get 0 i32.lt_s
      br_if 0)))
"""

assert len(FIXTURES) == 13, f"expected 13 fixtures, got {len(FIXTURES)}"

# ---------------------------------------------------------------------------
# KNOWN — (fixture, backend) -> verdict. Exact pin: a cell that moves in
# EITHER direction (a false accept fixed, or a decline that regresses to an
# accept) is red. Default is "accept" (the defect); only exceptions listed.
# ---------------------------------------------------------------------------
DECLINES: set[tuple[str, str]] = {
    ("cu_add_tee", "aarch64"),
}
KNOWN: dict[tuple[str, str], str] = {
    (name, be): ("decline" if (name, be) in DECLINES else "accept")
    for name in FIXTURES
    for be in BACKENDS
}
EXPECT_ACCEPT = sum(1 for v in KNOWN.values() if v == "accept")
EXPECT_DECLINE = sum(1 for v in KNOWN.values() if v == "decline")
assert EXPECT_ACCEPT + EXPECT_DECLINE == 39


def wasmtime_confirms_invalid(wat_text: str, engine: wasmtime.Engine) -> str | None:
    """Returns the rejection message, or None if wasmtime ACCEPTED it (a fatal
    harness bug — the fixture would no longer prove anything)."""
    wasm_bytes = wasmtime.wat2wasm(wat_text)
    try:
        wasmtime.Module.validate(engine, wasm_bytes)
        return None
    except Exception as exc:  # noqa: BLE001 - the message IS the evidence
        return str(exc)


def run_synth(synth: Path, wat_path: Path, backend: str) -> tuple[int, str]:
    p = subprocess.run(
        [str(synth), "compile", str(wat_path), *BACKENDS[backend],
         "--all-exports", "-o", str(wat_path.with_suffix(".elf"))],
        capture_output=True, text=True, timeout=60,
    )
    return p.returncode, (p.stdout + p.stderr)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--synth", default=str(ROOT / "target/debug/synth"))
    args = ap.parse_args()

    synth = Path(args.synth)
    if not synth.is_file():
        print(f"FAIL: synth binary not found at {synth} — build it first "
              f"(cargo build -p synth-cli)")
        return 1

    engine = wasmtime.Engine()
    fails: list[str] = []
    n_compiles = 0
    n_accept = 0
    n_decline = 0

    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        for name, wat_text in FIXTURES.items():
            reject_msg = wasmtime_confirms_invalid(wat_text, engine)
            if reject_msg is None:
                fails.append(
                    f"HARNESS BUG: fixture {name!r} was ACCEPTED by wasmtime — "
                    f"it is not invalid WebAssembly and proves nothing here")
                continue
            wat_path = tmp / f"{name}.wat"
            wat_path.write_text(wat_text)
            for be in BACKENDS:
                rc, output = run_synth(synth, wat_path, be)
                n_compiles += 1
                got = "accept" if rc == 0 else "decline"
                want = KNOWN[(name, be)]
                if got == "accept":
                    n_accept += 1
                else:
                    n_decline += 1
                if got != want:
                    fails.append(
                        f"{name} / {be}: synth {got}ed (exit={rc}), pin says "
                        f"{want} — wasmtime rejects this module with "
                        f"{reject_msg!r}. A pin move is a real behavior change: "
                        f"re-measure, then update KNOWN/DECLINES here.")
                # Sanity on the one declining cell: the decline must be the
                # RIGHT kind (a stack/value-arity refusal), not some unrelated
                # failure that happens to exit non-zero.
                if got == "decline" and be == "aarch64" and name == "cu_add_tee":
                    if "value stack" not in output and "no result" not in output:
                        fails.append(
                            f"{name} / {be}: declined, but not for the expected "
                            f"reason (want a value-stack/arity message): "
                            f"{output.strip().splitlines()[-1:] }")

    print(f"#1207 fixtures={len(FIXTURES)} backends={len(BACKENDS)} "
          f"compiles={n_compiles} accepted(wrong)={n_accept} declined={n_decline}")
    print(f"#1207 CHECKS={n_compiles}/39 cells classified")
    print(f"#1207 PINS={len(KNOWN)}")

    if fails:
        print(f"RESULT: FAIL ({len(fails)} mismatch(es))")
        for f in fails:
            print(f"  {f}")
        return 1
    print(f"RESULT: PASS — {n_accept} wrongly-accepted invalid module(s) "
          f"pinned exactly as measured; {n_decline} correctly declined "
          f"(AArch64/cu_add_tee only — a partial capability ARM/RISC-V lack "
          f"entirely, see #1229 sibling oracle)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
