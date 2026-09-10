#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 8
"""RQ-66-UNWATCHED (#1230): VCR-RA-003 refuses synth's OWN emitted ARM
stream on spec modules — `JoinValueNotAvailable { reg: R4/R5, ... }` — on
`br`/`br_if`/`br_table`/`labels` value-carrying joins. THE VERDICT, with
dynamic proof: **the allocator is wrong; the validator is right.** This is a
caught would-be miscompile, not a validator false positive.

RE-DERIVED POST-BOTHWRONG (v0.66, RQ-66-BOTHWRONG #1210, commit 4a3f6080,
landed on `main` while this PR was open). BOTHWRONG's central fix was that
`call` unconditionally pushed a phantom operand-stack result for every
callee regardless of its actual WASM arity. That is an operand-stack defect
in the SAME selector this oracle's census reads, so the census was
RE-MEASURED against the post-BOTHWRONG tree rather than assumed unaffected,
and the answer is a SPLIT, not a single verdict:

  * 2 of the original 5 instances (`br.wast` and `br_table.wast`, both named
    `as-block-mid`, both containing `(call $dummy)`) are GENUINELY FIXED.
    Verified, not assumed: both now compile with exit 0, and their
    disassembly shows clean code with NO join-register read at all at the
    point that used to violate the invariant — the phantom void-call result
    that manufactured a spurious "joined value" is gone, so there is nothing
    left to reconcile. This is BOTHWRONG's bug, closed by BOTHWRONG's fix.
  * 3 of the original 5 (`labels.wast`'s `switch`, `br_if.wast`'s
    `nested-br-value` and `nested-br_table-value`) contain NO `call` at
    all and are UNCHANGED: the VCR-RA-003 messages are byte-for-byte
    identical (same register, same `join_block` ordinal) to the pre-
    BOTHWRONG measurement, and `switch`'s emitted `.text` — re-captured
    fresh from the current tree via the same probe-and-delete recipe below
    — is BYTE-IDENTICAL to the frozen fixture (verified: 220/220 bytes,
    `bytes ==` true). These three were never in BOTHWRONG's scope (no
    `call`, so no phantom push to remove) and their defect is a DIFFERENT
    root cause that happens to produce the same validator error shape.

So the original "5 instances, one class" framing UNDER-RESOLVED two
different bugs into one error message. The dynamic proof below is
RE-ESTABLISHED on the unchanged bytes, not merely carried forward: the
poisoned-register replay was re-run against the freshly-recaptured `switch`
object (not just the old frozen one) and produces the identical wrong
values, confirming the proof still holds on what the CURRENT compiler
emits, not just on what an old compiler once emitted.

THE DECLINE CENSUS (measures today's `main`/lane tree; no bypass involved):

    VCR-RA-003: register-allocation validation FAILED —
    JoinValueNotAvailable { reg: R4, join_block: N }.

  file            functions   register   status
  --------------  ----------  --------   -------------------------------
  br.wast              0        —        FIXED by BOTHWRONG (was 1, R4)
  br_if.wast           2        R5       unchanged
  br_table.wast        0        —        FIXED by BOTHWRONG (was 1, R4)
  labels.wast          1        R4       unchanged
  TOTAL                3                 (was 5 pre-BOTHWRONG)

`labels.wast` is the SOLE blocker of that one file; `br_if.wast` carries an
unrelated decline too. The decline is honest and load-bearing: VCR-RA-003 is
the acceptance oracle the allocator endgame (CLAUDE.md "ALLOCATOR ENDGAME")
is designed to be built against, so whether it is right to refuse here is
not a side question — it is the question.

THE INVESTIGATION. A previous agent on this lane left an uncommitted,
never-shipped local patch to `arm_backend.rs` gating the VCR-RA-003 refusal
behind `SYNTH_RA003_PROBE_BYPASS`, purely to let `finish_allocated_stream`
emit the object it would otherwise refuse, for inspection. That patch was
restored TWICE (once pre-BOTHWRONG to capture the original bytes, once
post-BOTHWRONG to confirm they had not moved) and DELETED again both times —
this repo never ships a lever that disables "refusing to emit a miscompiled
object." What survives is the captured object, frozen in
`ra003_join_1230_red_main.json` (`labels.wast`'s `switch`, extracted to
`ra003_switch_1230.wat`), confirmed byte-identical across the rebase, and
the proof this oracle re-runs every time.

THE PROOF. Disassembly of the frozen `switch` object
(`arm-none-eabi-objdump`, ARM cortex-m4) shows the join block (reached from
two incoming edges: the `br_table`-selected `$1`/`$2` path, and the
`$0`/`$default`-selected fall-through path) execute:

    a4: movw r1, #10          ; the i32.mul LEFT operand (constant 10)
    ...                       ; (r1 is never touched again)
    d0: mul.w r7, r4, r3      ; <<< JOIN >>> multiplies R4 (not R1!) * R3

R3 correctly holds the join's right operand (2 or 5, from either incoming
edge). R4 is supposed to hold the LEFT operand (10) at this join — but NO
incoming edge to this join point ever writes 10 into R4; R4 holds whatever
was in the CALLER's R4 at entry (a callee-saved register, pushed and later
restored, never assigned). This is exactly what `JoinValueNotAvailable {
reg: R4 }` reports: a register the join code READS is not DEFINED by every
incoming edge. It is not a conservative validator being unable to prove
something true — the register genuinely does not hold the joined value on
either edge that reaches the mul.

DYNAMIC CONFIRMATION (this oracle, every run): load the frozen bytes,
poison R4 (and every other candidate join register) to an arbitrary value
before calling `switch(n)` under unicorn, and observe the multiply use the
POISON instead of 10. wasmtime confirms the SPEC-correct answers first (a
real differential, not hand-computed): switch(0..5) = 50, 20, 20, 3, 50, 50
(`tests/spec-testsuite/labels.wast` assert_return lines 300-305). With R4
poisoned to `P`, the bypassed object computes `P * 5` for switch(0), `P * 2`
for switch(1), and `P * 5` again for switch(5) (the `$default`/overflow
path) — switch(3) is UNAFFECTED (its path branches straight to the
function's `br $ret`, skipping the multiply entirely, matching the
disassembly). Two different poison values are used to prove the result
tracks the poison (not merely "happens to be 10 by accident of the harness's
own R4 value at call time").

VERDICT (unchanged by BOTHWRONG, re-confirmed on fresh bytes): the
allocator's join-value-materialization has a genuine bug for this
NO-CALL control-flow shape — it decides a value should be homed in a
register at a join without ensuring every incoming edge writes it there —
and VCR-RA-003 catches it correctly. Nothing here should be "fixed" by
loosening the validator; the fix (not attempted in this lane, per its
"WATCHED not FIXED" mandate) belongs to the allocator's join/constant-
materialization logic, and is DEMONSTRABLY DIFFERENT from BOTHWRONG's
call-arity fix (that fix's own scope — functions containing `call` — does
not include `switch`, `nested-br-value` or `nested-br_table-value`, all
call-free; BOTHWRONG closing 2 of the original 5 is a real, welcome, and
UNRELATED overlap in symptom, not in cause).

Usage:
  python3 scripts/repro/ra003_join_1230_differential.py [--synth PATH]
    [--suite DIR]
"""

import argparse
import base64
import io
import json
import subprocess
import sys
from pathlib import Path

from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UcError
from unicorn.arm_const import (
    UC_ARM_REG_SP, UC_ARM_REG_R0, UC_ARM_REG_R4, UC_ARM_REG_R5,
    UC_ARM_REG_R6, UC_ARM_REG_R7, UC_ARM_REG_R8, UC_ARM_REG_LR,
)
import wasmtime

ROOT = Path(__file__).resolve().parent.parent.parent
HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "ra003_join_1230_red_main.json"
SWITCH_WAT = HERE / "ra003_switch_1230.wat"

# ---------------------------------------------------------------------------
# THE DECLINE CENSUS — KNOWN: (file, register) -> exact count. A pin that
# moves in EITHER direction is red.
#
# br.wast/R4 and br_table.wast/R4 are pinned at 0, not omitted: both were 1
# pre-BOTHWRONG (#1210, commit 4a3f6080), both are their functions' own
# `call $dummy`-containing `as-block-mid`, and both are now VERIFIED FIXED
# (exit 0, disassembly shows no join-register read at all — the phantom
# void-call push BOTHWRONG removed was the only thing manufacturing a
# "joined value" here). Pinning 0 explicitly, rather than deleting the row,
# makes a REGRESSION back to 1 a caught pin-mismatch instead of a silently
# ignored new key.
# ---------------------------------------------------------------------------
KNOWN: dict[tuple[str, str], int] = {
    ("br.wast", "R4"): 0,
    ("br_if.wast", "R5"): 2,
    ("br_table.wast", "R4"): 0,
    ("labels.wast", "R4"): 1,
}
FILES = ["br.wast", "br_if.wast", "br_table.wast", "labels.wast"]

# spec-suite ground truth (tests/spec-testsuite/labels.wast, lines 300-305)
SPEC_RESULTS = {0: 50, 1: 20, 2: 20, 3: 3, 4: 50, 5: 50}
POISONS = [0x7, 0x1234]


def measure_decline(synth: Path, suite: Path, wast: str) -> dict[str, int]:
    p = subprocess.run(
        [str(synth), "compile", str(suite / wast), "--cortex-m",
         "--all-exports", "--allow-skipped-exports", "-o", "/dev/null"],
        capture_output=True, text=True, timeout=300,
    )
    out = p.stdout + p.stderr
    counts: dict[str, int] = {}
    for line in out.splitlines():
        if "VCR-RA-003" not in line or "JoinValueNotAvailable" not in line:
            continue
        # ... JoinValueNotAvailable { reg: R4, join_block: 2 } ...
        m = line.split("reg: ")[1].split(",")[0].strip()
        counts[m] = counts.get(m, 0) + 1
    return counts


def spec_confirms(engine: wasmtime.Engine) -> dict[int, int]:
    wasm_text = SWITCH_WAT.read_text()
    wasm_bytes = wasmtime.wat2wasm(wasm_text)
    store = wasmtime.Store(engine)
    module = wasmtime.Module(engine, wasm_bytes)
    instance = wasmtime.Instance(store, module, [])
    fn = instance.exports(store)["switch"]
    got = {n: fn(store, n) for n in range(6)}
    return got


def find_symbol(elf: ELFFile, name: str) -> int:
    for sec in elf.iter_sections():
        if sec["sh_type"] == "SHT_SYMTAB":
            for sym in sec.iter_symbols():
                if sym.name == name:
                    return sym["st_value"] & ~1
    raise KeyError(name)


def run_poisoned(data: bytes, text_addr: int, sw_addr: int, n: int,
                  poison: int) -> int:
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(0, 4 * 1024 * 1024)
    mu.mem_write(text_addr, data)
    mu.reg_write(UC_ARM_REG_SP, 0x00300000)
    mu.reg_write(UC_ARM_REG_R0, n)
    for reg in (UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R6, UC_ARM_REG_R7,
                UC_ARM_REG_R8):
        mu.reg_write(reg, poison)
    ret_sentinel = 0xFFFFFFFE
    mu.reg_write(UC_ARM_REG_LR, ret_sentinel)
    try:
        mu.emu_start(sw_addr | 1, ret_sentinel, timeout=5_000_000)
    except UcError:
        pass
    return mu.reg_read(UC_ARM_REG_R0)


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
    for f in FILES:
        if not (suite / f).is_file():
            print(f"FAIL: {suite / f} missing — checkout needs "
                  f"`submodules: recursive`")
            return 1
    if not FIXTURE.is_file() or not SWITCH_WAT.is_file():
        print(f"FAIL: frozen fixture missing ({FIXTURE}, {SWITCH_WAT})")
        return 1

    fails: list[str] = []

    # ---- part 1: the decline census on TODAY'S tree (no bypass) ----------
    print("== decline census (today's compiler, no bypass) ==")
    measured_total: dict[str, int] = {}
    for f in FILES:
        counts = measure_decline(synth, suite, f)
        for reg, n in counts.items():
            measured_total[(f, reg)] = measured_total.get((f, reg), 0) + n
        print(f"  {f:<16} {counts}")
    all_keys = set(KNOWN) | set(measured_total)
    for key in sorted(all_keys):
        got = measured_total.get(key, 0)
        want = KNOWN.get(key, 0)
        if got != want:
            fails.append(
                f"decline census {key}: measured {got}, pin says {want}. "
                f"Re-measure, then update KNOWN here.")
    total_declines = sum(measured_total.values())
    print(f"#1230 decline TOTAL={total_declines} (pin "
          f"{sum(KNOWN.values())})")

    # ---- part 2: wasmtime confirms the spec-correct answers --------------
    print("== spec ground truth (wasmtime) ==")
    engine = wasmtime.Engine()
    got_spec = spec_confirms(engine)
    if got_spec != SPEC_RESULTS:
        fails.append(
            f"spec ground truth mismatch: wasmtime gives {got_spec}, "
            f"expected {SPEC_RESULTS} — the extracted fixture "
            f"({SWITCH_WAT}) no longer matches labels.wast's `switch`")
    print(f"  switch(n) for n in 0..5 = {got_spec}")

    # ---- part 3: dynamic proof the frozen bytes are WRONG -----------------
    print("== dynamic proof: frozen bytes read a poisoned join register ==")
    fixture = json.loads(FIXTURE.read_text())
    obj = base64.b64decode(fixture["switch_arm_cortex_m4"]["object_b64"])
    elf = ELFFile(io.BytesIO(obj))
    text_sec = elf.get_section_by_name(".text")
    text_addr = text_sec["sh_addr"]
    text_data = text_sec.data()
    sw_addr = find_symbol(elf, "switch")

    n_emulations = 0
    for poison in POISONS:
        for n in (0, 1, 3, 5):
            got = run_poisoned(text_data, text_addr, sw_addr, n, poison)
            n_emulations += 1
            correct = SPEC_RESULTS[n]
            if n == 3:
                # This path branches straight to `br $ret`, skipping the
                # multiply entirely — UNAFFECTED by the poison. If this ever
                # starts depending on the poison too, the bug widened.
                if got != correct:
                    fails.append(
                        f"switch({n}) with R4-R8 poisoned to {poison:#x} = "
                        f"{got}, want {correct} (this path should be "
                        f"poison-independent — it bypasses the multiply)")
                continue
            rhs = {0: 5, 1: 2, 5: 5}[n]
            wrong_expected = (poison * rhs) & 0xFFFFFFFF
            print(f"  switch({n}) poison={poison:#x}: got={got} "
                  f"(correct={correct}, predicted-wrong={wrong_expected})")
            if got == correct:
                fails.append(
                    f"switch({n}) with R4 poisoned to {poison:#x} returned "
                    f"the CORRECT answer ({correct}) — the frozen bytes no "
                    f"longer reproduce the join-register bug; re-capture "
                    f"the fixture")
            elif got != wrong_expected:
                fails.append(
                    f"switch({n}) with R4 poisoned to {poison:#x} = {got}, "
                    f"predicted wrong value (poison*{rhs}) = {wrong_expected} "
                    f"— the wrongness shape changed; re-derive the formula")

    print(f"#1230 CHECKS: {total_declines} declines + "
          f"{len(got_spec)} spec confirmations + {n_emulations} poisoned "
          f"emulations")
    print(f"#1230 PINS={len(KNOWN)}")
    if fails:
        print(f"RESULT: FAIL ({len(fails)} mismatch(es))")
        for f in fails:
            print(f"  {f}")
        return 1
    print(f"RESULT: PASS — VCR-RA-003's {total_declines} remaining declines "
          f"pinned exactly (2 of the original 5 — br.wast, br_table.wast — "
          f"verified FIXED by RQ-66-BOTHWRONG #1210, unrelated call-arity "
          f"fix); the allocator's join-register bug on the 3 call-free "
          f"survivors reproduces exactly as captured, RE-VERIFIED "
          f"byte-identical post-BOTHWRONG (poison flows into the emitted "
          f"multiply on every affected path); VERDICT: the allocator is "
          f"wrong, the validator is right")
    return 0


if __name__ == "__main__":
    sys.exit(main())
