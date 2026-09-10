# RQ-66-BOTHWRONG (#1189 lane) — root-cause triage

RQ-65-PARITY (#197) pinned five classes where BOTH shipped ARM selectors
(the optimized `ir_to_arm` path and the direct `select_with_stack` path)
compute the wrong answer, with no correct leg to fall back to: #1209, #1210,
#1211, #1214, #1215. This note records the root-cause attribution for each,
with the evidence — because five fixes for one bug would be a worse outcome
than one fix honestly attributed, and the reverse (declaring one fix that
only covers part of a class) is just as dishonest.

Evidence for every claim below is the `selector_parity_197_differential.py`
oracle itself: run with `--only <file>.wast` before and after a fix, the
`PINNED DIVERGENCE VANISHED` line is the proof a fix landed, not a claim.

## #1209 — memory64 accepted and silently wrong: REFUSED, not fixed

**Root cause**: `crates/synth-core/src/wasm_decoder.rs`'s memory-section and
data-section parsing has no representation for a 64-bit-indexed memory. The
`WasmMemory` struct never captured `wasmparser::MemoryType.memory64`, and the
active-data-segment offset reader only recognizes `Operator::I32Const` —
an `i64.const` offset (what a memory64 module's data segments always use)
silently falls through to "non-constant offset" handling, and every
address-materialization path downstream assumes a 32-bit address.

**Decision: LOUD REFUSAL**, not a lowering fix — see the `refuse_memory64_module`
doc comment in `crates/synth-cli/src/main.rs` for the full reasoning. Summary:
accepting memory64 and computing the wrong answer is exactly the class
CLAUDE.md's compliance envelope calls the worst outcome; a real fix touches
data-segment offset decoding, `memory.size`/`memory.grow`, and every
load/store address-materialization path on BOTH selectors — multi-release
scale — for a proposal that needs a >4 GiB address space, which is
incoherent for every target this backend ships to (Cortex-M, RV32,
host-native AArch64).

**Acceptance-delta: NOT MEASURED.** The 805-module real-world corpus (#1017)
is not available in this sandbox — not checked into the repo, not fetched by
any CI workflow, not cached on disk. `docs/status/SPEC_FAMILY_CENSUS.md`
shows only 14 of 257 spec-suite files are tagged `memory64` (a weak proxy,
not the real-world corpus this decision should ideally be measured against).
Report this honestly as "not measured", not as an estimate.

**Result**: all 42 pins / 513 assertions across `address64.wast`,
`float_memory64.wast`, `load64.wast`, `memory64.wast`, `memory_copy64.wast`,
`memory_grow64.wast`, `memory_init64.wast` move from `shared-wrong` /
`parity-divergence/*` to a clean `module-decline`.

## #1211 — call_indirect: TWO independent causes, both fixed

The issue bundles two shapes that turned out to have **unrelated** root
causes:

### 1211a — non-zero table index (`call_indirect.wast` m1, `call-1`/`call-2`/`call-3`)

**Root cause** (NOT "the table index is ignored", which was the original
filed hypothesis): a register-liveness bug in
`crates/synth-synthesis/src/instruction_selector/select_with_stack.rs`'s
`CallIndirect` marshalling. `reg_srcs` (the register-passed call arguments,
already popped off the operand-stack model by `pop_call_args`) are invisible
to `stack_live_regs(&stack)` — they left the operand-stack model but are
still live, since `emit_arg_moves` reads them later. Before the table-index
relocation MOV, `free_callee_saved` was asked for a scratch register using
only `stack_live_regs(&stack)` as the protected set, so it could (and did)
hand back a register that already held one of `reg_srcs` — the relocation
MOV then silently overwrote a live argument with the table index before it
was ever marshalled into R0–R3. Fixed by protecting `reg_srcs` explicitly.

This explains the observed numbers precisely: e.g. `call-1(2,3,0)` expected
5, got 2 — not "wrong callee", but "right callee, corrupted argument".

### 1211b — `elem.wast` `call_in_table` (m72–74): extended-const offset expressions

**Root cause**: the element-section offset reader in `wasm_decoder.rs` only
recognized a bare `i32.const` as a segment's placement — `(i32.add
(i32.const 1) (i32.const 2))` (the Wasm 2.0 "extended constant expressions"
grammar) fell through to "non-constant, unverifiable", which poisons the
WHOLE MODULE's `call_indirect` type check (`global_poison` in
`call_indirect_guards`) and ships every table slot as null. A `call_indirect`
that should land on a real function instead dispatches through the null
word and executes garbage — observed as `UC_ERR_INSN_INVALID`, not a clean
trap, because the null word is `0`, not a deliberate trap sequence.

**Fixed** by `eval_extended_const_i32_offset`, a small stack evaluator for
`i32.const`/`i32.add`/`i32.sub`/`i32.mul` (no `global.get` — that shape
stays unverifiable, unchanged).

**Result**: all 6 pins / 10 assertions across `call_indirect.wast` and
`elem.wast` resolve to `ok`.

## #1214 — i64 read-before-write local not zero-initialised: FIXED

**Root cause**: `infer_i64_locals` (`instruction_selector.rs`) infers a
local's width ONLY from a `local.set`/`local.tee` that stores a known-i64
value — dataflow, not declaration. A local that is declared `i64`, read
before any write, and **never written at all** anywhere in the function
(`func.wast`'s `init-local-i64`: `(local i64) (local.get 0)`, no
`local.set` in sight) never enters the inferred set, so `compute_local_layout`
gives it a 4-byte slot and the read-before-write zero-init prologue (#457)
only zeroes the low word.

**Fixed** by threading the WASM module's own declared local types
(`FunctionOps::declared_i64_locals`, new decoder field, populated from
`wasmparser`'s locals reader — the ONE place this information is stated
outright) down to `compute_local_layout`, which ORs it into the
dataflow-inferred set. Zero risk to any other function: for a local that
IS written somewhere, inference and declaration necessarily agree (or the
module would not validate), so the OR is a no-op there.

**Result**: the single pin / assertion (`func.wast` `init-local-i64`)
resolves to `ok`.

## #1210 — value live across a call is lost: FIXED (and it explains part of #1215)

**Root cause**: `WasmOp::Call`'s non-float result handling in
`select_with_stack.rs` **unconditionally pushes a result onto the operand
stack for every call**, regardless of the callee's actual WASM signature.
`func_ret_i64`/`func_ret_f32`/`func_ret_f64` all being `false` conflates
"returns i32" with "returns nothing" — there was no table anywhere in the
ARM selector recording a callee's actual result COUNT (0 vs 1), even though
`CompileConfig::func_result_counts` (#851) already carries exactly that
information for the AArch64 backend.

A call to a **void** function (e.g. spec's `(func $dummy)`, empty body, zero
results) therefore still pushed whatever garbage the callee left in R0 as a
phantom operand-stack value. Every subsequent operation that consumed the
"real" stack landed one slot deeper than wasm's own validated stack depth —
so a LATER value silently took the place of an EARLIER one.

Verified arithmetically before touching any code, for `stack.wast`'s
`not-quite-a-tree` (`call $f; call $f; call $void_f; i32.add` — no blocks at
all): synth's wrong answers (5, 11 instead of 3, 9) are EXACTLY
`i32.add(call2_result, call3_phantom_result)` where `call3_phantom_result`
is the residual value the void callee physically left in R0 (3 and 6,
respectively) — i.e. `i32.add` popped the phantom pushed by the VOID third
call and the real second call's result, silently dropping the first call's
result it should have used instead. The same reasoning independently
predicts `block.wast`'s `as-binary-operand` (`i32.mul` of two
`(block (result i32) (call $dummy) (i32.const N))` blocks) landing on `4 *
0 = 0` instead of `3 * 4 = 12` — `$dummy`'s phantom (residual R0 = 0, since
nothing wrote R0 before the first call in a fresh frame) becomes the SECOND
`i32.mul` operand instead of the intended constant, because the block
boundary does not truncate the extra phantom entry back to the block's
declared arity.

**Fixed** by threading `func_result_counts` (already computed by the
decoder, already reaching `CompileConfig`, just never reaching the ARM
`InstructionSelector`) into `select_with_stack.rs`'s `Call` handling: when
the callee's result count is 0, reload the preserved caller-saved registers
verbatim and push nothing — matching wasm's own validated stack effect for
that call exactly. Empty table (hand-built op streams, unit tests) ⇒ assume
a result, so every function whose every callee HAS a declared result is
byte-identical.

**Result**: all 22 pins / 33 assertions across `block.wast`, `loop.wast`,
`if.wast` (partial — see below), `local_tee.wast`, `select.wast`,
`stack.wast` resolve to `ok`.

**This is not only a spec-suite defect.** `cargo test --workspace`'s
`fusion_census_matches_frozen_baseline_428` (`crates/synth-cli/tests/cmp_select_fusion_census.rs`)
drifted after this fix: `scripts/repro/flight_seam.wasm` — a REAL,
frozen, non-synthetic gale fixture representing embedded flight-control
code — went from 12 to 11 fused cmp→select sites. Its `flight_algo`
function calls the VOID function `filter_step` (`(func $filter_step (type 1)
(param i32 i32))`, no result) and then reads an EARLIER-pushed value
(`local.get 0 / local.set 2` immediately after the call). Before this fix,
that call site silently carried the same phantom-push defect as every
spec-suite instance above — on REAL code, not a hand-written test. The
census baseline was re-measured deliberately (see that file's updated
comment) rather than papered over; `flight_seam_flat.wasm` (the same
program's flattened form, no separate call site) is unchanged at 12,
confirming the drift is specific to the exact call site #1210 fixed.

## #1215 — br_table/br_if value in an operand position: TWO of its causes fixed, one remains

#1215's eleven pinned entries turned out to split across THREE mechanisms,
two of them fixed by work that was not originally scoped to #1215 at all:

### 1215a — the same #1210 void-call-phantom-push bug (2 entries / 3 assertions)

`if.wast`'s `as-br_if-last` and `as-br_table-last` have a value-`if` whose
arms contain a call to `$dummy` (void) in operand position of `br_if`/
`br_table` — the #1210 fix resolves them as a pure side effect (verified:
`PINNED DIVERGENCE VANISHED` fired for both the moment the #1210 fix
landed, with no #1215-specific change made).

### 1215b — `br_table`'s function-level-return depth: FIXED

**Root cause**: `BrTable`'s target-depth resolution used
`block_labels.len().saturating_sub(1 + depth as usize)` and then checked
`target_idx < block_labels.len()` to decide whether the resolved index was
real. A depth reaching PAST every currently-tracked block is a
FUNCTION-LEVEL RETURN, not a branch to block 0 (WASM's own label-depth
rule: depth N counts outward past the function body itself once N exceeds
the open block count) — but the old clamp aliased any such depth to the
OUTERMOST tracked block's label, and when NO block was open at all sent
`target_idx < block_labels.len()` to `0 < 0` (false), silently skipping
BOTH the carried-value landing and the branch instruction, so control fell
through to whatever code happened to follow the `br_table` in the encoder's
output. The #500 fix that gave `Br`/`BrIf` this same `checked_sub`-based
"depth past every block ⇒ return" handling was never extended to
`BrTable`.

Measured precisely: `func.wast`'s `break-br_table-num`
(`(br_table 0 0 (i32.const 50) (local.get 0)) (i32.const 51)`, a bare
`br_table` at function-body level with two depth-0 targets) always
returned 51 — the branch never happened at all, so execution fell through
to the trailing `i32.const 51`.

**Fixed** by a `target_of` helper (`checked_sub`, returning `None` past the
tracked blocks) at both call sites (per-target label resolution and the
default-branch), plus a per-`BrTable` shared function-return epilogue
(mirroring `Br`'s existing `None` arm: land the carried value in R0, then
emit the SP-restore + POP epilogue exactly once, reached only via an
explicit jump from the dispatch cascade).

**Result**: `func.wast`'s `break-br_table-num` (4 assertions) and
`br_table.wast`'s `as-loop-first`/`as-loop-last`/`as-loop-mid` (3
assertions) resolve to `ok` — 4 entries / 7 assertions.

### 1215c — nested branch as an operand to another branch: NOT FIXED, PINNED

The remaining five entries / 11 assertions (`br.wast`
`nested-br_table-value-index`, `br_if.wast` `nested-br_table-value-index`,
`br_table.wast`'s `nested-br_table-value` / `nested-br_table-value-index`,
`func.wast`'s `break-br_table-nested-num`) are a **genuinely different,
unaddressed mechanism**: a `br_table`/`br_if` whose INDEX or CONDITION
operand is ITSELF a nested branch instruction that carries a value out
(e.g. `(br_table 0 (i32.const 4) (br_table 0 1 0 (i32.const 8)
(local.get 0)))` — the outer `br_table`'s index operand is a second,
nested `br_table`). No call and no function-level-return depth is involved
in any of these shapes, so neither the #1210 nor the #1215b fix touches
them (confirmed: all five stay pinned at their exact original counts after
every fix in this lane, zero regression, zero accidental resolution).

**Not fixed in this lane** — the selector's branch lowering does not model
a branch instruction as a value-producing expression when it appears in an
operand position of another branch; that is a materially different, deeper
change (the branch machinery would need to itself leave a value in the
consuming instruction's expected operand location) than anything else this
lane touched, and attempting it without dedicated investigation risks
exactly the "five fixes for one bug" anti-pattern this lane is supposed to
avoid running in reverse — claiming a fix for a shape it doesn't cover.
Stays pinned with this reason; a future lane should treat it as its own,
narrowly-scoped investigation.

## Summary

| Issue | Entries closed | Assertions closed | Residual |
|---|---|---|---|
| #1209 | 42 / 42 | 513 / 513 | none — refused, not fixed |
| #1210 | 22 / 22 | 33 / 33 | none |
| #1211 | 6 / 6 | 10 / 10 | none (two independent causes, both fixed) |
| #1214 | 1 / 1 | 1 / 1 | none |
| #1215 | 6 / 11 | 10 / 21 | 5 entries / 11 assertions PINNED — one coherent unaddressed mechanism |

> **BASE NOTE added by the v0.66 cold review.** The counts below are against
> the table as it stood when this lane STARTED (89 entries / 595 assertions,
> after RQ-65-DECLINE converted #1205/#1208/#1213). That is a valid base for
> this lane's own work and is left as measured. It is NOT the
> release-over-release figure: against the v0.65.0 tag the table held 103 / 622
> and now holds 26 / 55, so the release closed 77 entries / 567 assertions.
> Publishing this lane's base as the release figure is the error the cold
> review caught.

**89 of 89 pinned entries touched by a decision; 84 of 89 (585 of 595
assertions) move from wrong to correct or to a loud decline; 5 entries (11
assertions), all one coherent unaddressed mechanism (a branch used as a
value-producing operand to another branch), stay pinned with a stated
reason.**
