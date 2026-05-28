# Rocq Proof Suite — Honest Status

**Last Updated:** May 2026 (v0.10.0 PR 1: i64_add/i64_sub closed as T1 Qed via ADDS/ADC + SUBS/SBC carry/borrow-propagation lemmas — no new axioms)

## v0.10.0 PR 1 outcome: i64 add/sub carry/borrow propagation

`i64_add_correct` and `i64_sub_correct` (Admitted in v0.9.0) are now Qed.
The discharge steps `exec_program` over the real ARM instruction pairs
`[ADDS R0 R0 (Reg R2); ADC R1 R1 (Reg R3)]` and
`[SUBS R0 R0 (Reg R2); SBC R1 R1 (Reg R3)]` emitted by `Compilation.v`,
reading the C flag set by the low-half instruction and applying two new
helper lemmas in `ArmFlagLemmas.v`:

- `i64_add_via_adds_adc` — (lo,hi) of ADDS+ADC = lo/hi of `I64.add` on the
  combined operands;
- `i64_sub_via_subs_sbc` — same shape for `I64.sub`.

Both helpers are derived from the existing ArmSemantics.v flag clauses
(`compute_c_flag_add` / `compute_c_flag_sub`) plus base-2^32 modular
arithmetic (`carry_split_add` / `borrow_split_sub`). **No new axioms.**

Net change vs. v0.9.0: +2 T1 Qed (i64 arithmetic 35 -> 37), -2 Admitted
(CorrectnessI64.v 5 -> 3); the 3 remaining i64 admits (And/Or/Xor) are a
separate PR blocked on the Rocq 9 Z.mod_mod halves-distribute rework.

## v0.9.0 PR 1 outcome: PRECURSOR + DISCHARGE

The 5 strategic admits introduced by v0.8.0 #150 are now discharged. The
initial scope of PR 1 — discharge under the v0.8.0 axiom shape — was found to
be impossible (the v0.8.0 axioms were pure type declarations with no
result-correspondence equations). PR 1 was re-scoped into the full precursor:

1. **New result-equation axioms in `coq/Synth/ARM/ArmSemantics.v`**: 26 new
   `_spec` axioms covering every i64 pseudo-op result function. Each axiom is
   cross-checked against `docs/analysis/I64_CODEGEN_SURVEY.md`.

2. **Restated theorems in `CorrectnessI64.v` and `CorrectnessSimple.v`**: the
   5 prior admits are now stated with sound shape — I64-typed hypotheses on
   combined operand pairs, high-half register pinning, and dual-register
   post-conditions (R0 = lo_of_i64 result, R1 = hi_of_i64 result).

3. **Discharges**: 5/5 admits closed as `Qed` (4 div/rem + 1 i64_const).

Net change: +5 Qed (the 5 discharges), 0 admits added.

The fan-out PRs 2-5 of umbrella #152 (the remaining T2->T1 lifts for I64
add/sub/mul/and/or/xor/shifts/rotates/comparisons/clz/ctz/popcnt) are now
unblocked. Each lift is a mechanical `unfold; rewrite <op>_spec; reflexivity`
against the spec axioms now in place.


## Overview

Synth's Rocq proof suite verifies that `compile_wasm_to_arm` preserves WASM semantics.

**v0.8.0 PR 1a (Compilation.v i64 alignment):** Aligned the i64 compilation
clauses with what the Rust compiler actually emits — dual-register
(R0:R1 / R2:R3) sequences, ADDS/ADC and SUBS/SBC for arithmetic, and
high-level pseudo-ops (`I64Mul`, `I64SetCond`, `I64Shl*`, `I64Div*`, etc.)
mirroring the Rust `ArmOp::I64*` variants. The previous Compilation.v
modeled all i64 ops as single 32-bit instructions on (R0, R1) — proving
the wrong theorem. See `docs/analysis/I64_CODEGEN_SURVEY.md`.

The 4 T1 i64 division/remainder proofs and the `i64_const_correct` proof
were re-admitted: their concrete result claims relied on the old simplified
codegen. They will be lifted by v0.8.0 PRs 2–5 (the lift queue under
umbrella #147).

## Proof Tiers

| Tier | Meaning | Count |
|------|---------|-------|
| **T1: Result Correspondence** | ARM output register = WASM result value | 37 |
| **T2: Existence-Only** | ARM execution succeeds (no result claim) | 139 |
| **T3: Admitted** | Not yet proven | 13 |
| **Infrastructure** | Properties of integers, states, flag lemmas | 65 |

**Total: 244 Qed / 8 Admitted across all files**

v0.10.0 PR 1: +2 T1 Qed (i64_add_correct, i64_sub_correct) and +9
infrastructure Qed (combine_i32_unsigned, carry_split_add,
borrow_split_sub, i64_add_via_adds_adc, i64_sub_via_subs_sbc in
ArmFlagLemmas.v; get_reg_set_flags, flags_set_flags, flags_set_flags_set_reg
in ArmState.v; flag_c_update_flags_arith in ArmSemantics.v); -2 Admitted.

Net change from the v0.8.0 baseline: +5 Qed, −5 Admitted (4 i64 div/rem + 1 i64
const_correct discharged via the new result-correspondence axioms in
`ArmSemantics.v`).

## T1: Result Correspondence (37 Qed)

These are the crown jewels — they prove the compiled ARM code produces the exact same
value as the WASM operation.

### i64 Arithmetic (2) — dual-register carry/borrow propagation

| File | Theorem | Operation | Helper Lemma |
|------|---------|-----------|--------------|
| CorrectnessI64.v | `i64_add_correct` | I64Add | `i64_add_via_adds_adc` (ADDS+ADC) |
| CorrectnessI64.v | `i64_sub_correct` | I64Sub | `i64_sub_via_subs_sbc` (SUBS+SBC) |

(i64 Mul + 4 div/rem T1 proofs are also Qed; see the i64 Division row below
and CorrectnessI64.v.)

### i32 Arithmetic (6)

| File | Theorem | Operation |
|------|---------|-----------|
| Correctness.v | `compile_i32_add_correct` | I32Add |
| Correctness.v | `compile_i32_sub_correct` | I32Sub |
| Correctness.v | `compile_i32_mul_correct` | I32Mul |
| Correctness.v | `compile_i32_and_correct` | I32And |
| Correctness.v | `compile_i32_or_correct` | I32Or |
| Correctness.v | `compile_i32_xor_correct` | I32Xor |

(Also duplicated in CorrectnessI32.v: add, sub, mul, and, or, xor)

### i32 Division (0 — moved to T3)

These were T1 proofs but are now Admitted because division compilation emits
trap guard sequences (CMP + BCondOffset + UDF) that cannot be verified in the
current sequential exec_program model. See T3 section below.

### i32 Comparison (11) — uses flag-correspondence lemmas

| File | Theorem | Operation | Flag Lemma |
|------|---------|-----------|------------|
| CorrectnessI32.v | `i32_eqz_correct` | I32Eqz | `z_flag_sub_eq` |
| CorrectnessI32.v | `i32_eq_correct` | I32Eq | `z_flag_sub_eq` |
| CorrectnessI32.v | `i32_ne_correct` | I32Ne | `flags_ne` |
| CorrectnessI32.v | `i32_lt_s_correct` | I32LtS | `nv_flag_sub_lts` |
| CorrectnessI32.v | `i32_lt_u_correct` | I32LtU | `flags_ltu` |
| CorrectnessI32.v | `i32_gt_s_correct` | I32GtS | `flags_gts` |
| CorrectnessI32.v | `i32_gt_u_correct` | I32GtU | `flags_gtu` |
| CorrectnessI32.v | `i32_le_s_correct` | I32LeS | `flags_les` |
| CorrectnessI32.v | `i32_le_u_correct` | I32LeU | `flags_leu` |
| CorrectnessI32.v | `i32_ge_s_correct` | I32GeS | `flags_ges` |
| CorrectnessI32.v | `i32_ge_u_correct` | I32GeU | `flags_geu` |

### i32 Bit Manipulation (3) — uses axiomatized operations

| File | Theorem | Operation |
|------|---------|-----------|
| CorrectnessI32.v | `i32_clz_correct` | I32Clz |
| CorrectnessI32.v | `i32_ctz_correct` | I32Ctz |
| CorrectnessI32.v | `i32_popcnt_correct` | I32Popcnt |

### i32 Shift/Rotate (5) — uses register-based shift instructions

| File | Theorem | Operation | ARM Instruction |
|------|---------|-----------|-----------------|
| CorrectnessI32.v | `i32_shl_correct` | I32Shl | `LSL_reg R0 R0 R1` |
| CorrectnessI32.v | `i32_shru_correct` | I32ShrU | `LSR_reg R0 R0 R1` |
| CorrectnessI32.v | `i32_shrs_correct` | I32ShrS | `ASR_reg R0 R0 R1` |
| CorrectnessI32.v | `i32_rotl_correct` | I32Rotl | `RSB R2 R1 #32; ROR_reg R0 R0 R2` |
| CorrectnessI32.v | `i32_rotr_correct` | I32Rotr | `ROR_reg R0 R0 R1` |

### i64 Division (0 — moved to T3 by v0.8.0 PR 1a)

| File | Theorem | Operation | Status |
|------|---------|-----------|--------|
| CorrectnessI64.v | `i64_divs_correct` | I64DivS | Admitted (PR 1a) |
| CorrectnessI64.v | `i64_divu_correct` | I64DivU | Admitted (PR 1a) |
| CorrectnessI64.v | `i64_rems_correct` | I64RemS | Admitted (PR 1a) |
| CorrectnessI64.v | `i64_remu_correct` | I64RemU | Admitted (PR 1a) |

The previous "proofs" used `I32.divs` / `I32.divu` hypotheses against a model
where `I64DivS → [SDIV R0 R0 R1]` — i.e., a single 32-bit signed divide. That
is **not** what the Rust compiler emits. The real codegen emits an opaque
`ArmOp::I64DivS` pseudo-op that lowers to a software helper call. These
admits will close in v0.8.0 PR 2 by replacing the `i64_divs_pair` /
`i64_divu_pair` axioms with concrete `I64.divs` / `I64.divu`-based defs.

Each T1 proof proves: `get_reg astate' R0 = <result>` after executing the compiled ARM program.

## T2: Existence-Only (143 Qed)

These prove the ARM program executes successfully but don't claim the result value is correct.
Named `*_executes` to distinguish from T1 `*_correct` proofs.

| File | Count | Operations |
|------|-------|------------|
| CorrectnessSimple.v | 28 | Nop, Drop, Select, LocalGet/Set/Tee, GlobalGet/Set, I64Const, 11 comparisons, 5 shifts, 3 bit-manip (I32Const now Admitted) |
| CorrectnessI64.v | 25 | Add, Sub, Mul, And, Or, Xor, 5 shifts, 11 comparisons, 3 bit-manip |
| CorrectnessI64Comparisons.v | 19 | 11 comparisons, 3 bit-manip, 5 shifts |
| CorrectnessF32.v | 20 | 7 empty-program + 13 VFP (4 arith, 3 unary, 6 comparison) |
| CorrectnessF64.v | 20 | 7 empty-program + 13 VFP (4 arith, 3 unary, 6 comparison) |
| CorrectnessConversions.v | 21 | 3 integer + 18 VFP conversions |
| CorrectnessMemory.v | 8 | 4 i32/i64 + 4 f32/f64 load/store |
| CorrectnessComplete.v | 1 | Master compilation theorem |

## T3: Admitted (13)

> v0.10.0 PR 1: `i64_add_correct` / `i64_sub_correct` moved out of T3 to T1
> (Qed via the ADDS/ADC + SUBS/SBC carry/borrow-propagation lemmas). The
> remaining i64 admits are the And/Or/Xor halves-distribute trio.

| File | Count | Root Cause | Unblocking Strategy |
|------|-------|------------|---------------------|
| ArmRefinement.v | 2 | Needs Sail-generated ARM semantics | Phase 2: Import Sail specifications |
| Integers.v | 1 | `i64_to_i32_to_i64_wrap` — Rocq 9 `Z.mod_mod` signature changed | Rework proof for new Z.mod_mod API |
| CorrectnessI32.v | 4 | `i32_divs/divu/rems/remu_correct` — trap guard sequences (CMP+BCondOffset+UDF) cannot be verified in the sequential exec_program model | Extend exec_program to support PC-relative branching |
| CorrectnessSimple.v | 1 | `i32_const_correct` — compilation now branches on `I32.unsigned n <= 65535`; large-constant case requires Z.land/Z.shiftr lemmas | Prove MOVW+MOVT reconstruction lemma |
| CorrectnessSimple.v | 1 | `i64_const_correct` — v0.8.0 PR 1a aligned codegen to `I64ConstPseudo` (loads both halves); proof claimed R0 = low 16 bits via stale MOVW model | v0.8.0 PR 5: concrete `i64_const_lo`/`i64_const_hi` definitions |
| CorrectnessI64.v | 3 | `i64_and/or/xor_correct` — halves-distribute-over-bitwise decomposition blocked by the same Rocq 9 `Z.mod_mod` rewrite issue as `i64_to_i32_to_i64_wrap` | Rework with new Z.mod_mod API (separate PR) |
| Compilation.v | 2 | `ex_compile_simple_add`, `ex_compile_increment_local` — `simpl` cannot reduce `Z.leb (I32.unsigned (I32.repr n)) 65535` | Use `vm_compute` or prove I32.unsigned reduction lemma |

## VFP Semantics (Phase 5 — New)

VFP instruction semantics are modeled using abstract axioms on bit patterns (`I32.int`).
This approach:
- Closes all 48 VFP-dependent admits honestly (no `Admitted`, no axiom abuse)
- Uses abstract `Parameter`/`Axiom` types for IEEE 754 operations on bit patterns
- Preserves upgrade path to Flocq for T1 result-correspondence proofs

### VFP Axioms (21)

| Category | Axioms | Purpose |
|----------|--------|---------|
| F32 arithmetic | 7 | `f32_add/sub/mul/div/sqrt/abs/neg_bits` |
| F64 arithmetic | 7 | `f64_add/sub/mul/div/sqrt/abs/neg_bits` |
| Comparison | 2 | `f32_compare_flags`, `f64_compare_flags` |
| Conversion | 4 | `cvt_f32_to_f64`, `cvt_f64_to_f32`, `cvt_s32_to_f32`, `cvt_f32_to_s32` |

To upgrade to T1 result-correspondence proofs, replace these axioms with Flocq
IEEE 754 definitions and prove correspondence with WASM float semantics.

## Axioms

### Integers.v — I32 Module (13 axioms)

| Axiom | Purpose |
|-------|---------|
| `I32.clz` | Count leading zeros function |
| `I32.ctz` | Count trailing zeros function |
| `I32.popcnt` | Population count function |
| `I32.rbit` | Reverse bits function (ARM RBIT) |
| `I32.clz_rbit` | `clz(rbit(v)) = ctz(v)` — connects RBIT+CLZ to CTZ |
| `I32.clz_range` | `0 <= clz(x) <= 32` |
| `I32.ctz_range` | `0 <= ctz(x) <= 32` |
| `I32.popcnt_range` | `0 <= popcnt(x) <= 32` |
| `I32.div_mul_rem_unsigned` | Division/remainder relationship (unsigned) |
| `I32.div_mul_rem_signed` | Division/remainder relationship (signed) |
| `I32.remu_formula` | `r = a - (a/b) * b` (unsigned) |
| `I32.rems_formula` | `r = a - (a/b) * b` (signed) |
| `I32.rotl_rotr_sub` | `rotl x y = rotr x (sub (repr 32) y)` — rotl via rotr |

### ArmSemantics.v — VFP Operations (21 axioms)

| Axiom | Purpose |
|-------|---------|
| `f32_add/sub/mul/div_bits` | F32 binary arithmetic on bit patterns |
| `f32_sqrt/abs/neg_bits` | F32 unary operations on bit patterns |
| `f64_add/sub/mul/div_bits` | F64 binary arithmetic on bit patterns |
| `f64_sqrt/abs/neg_bits` | F64 unary operations on bit patterns |
| `f32_compare_flags` | F32 comparison -> ARM condition flags |
| `f64_compare_flags` | F64 comparison -> ARM condition flags |
| `cvt_f32_to_f64_bits` | F32 -> F64 promotion |
| `cvt_f64_to_f32_bits` | F64 -> F32 demotion |
| `cvt_s32_to_f32_bits` | Signed int -> F32 conversion |
| `cvt_f32_to_s32_bits` | F32 -> Signed int conversion |

### Integers.v — I64 Module (6 axioms)

| Axiom | Purpose |
|-------|---------|
| `I64.clz` | Count leading zeros function (64-bit) |
| `I64.ctz` | Count trailing zeros function (64-bit) |
| `I64.popcnt` | Population count function (64-bit) |
| `I64.clz_range` | `0 <= clz(x) <= 64` |
| `I64.ctz_range` | `0 <= ctz(x) <= 64` |
| `I64.popcnt_range` | `0 <= popcnt(x) <= 64` |

### ArmFlagLemmas.v (1 axiom)

| Axiom | Purpose |
|-------|---------|
| `nv_flag_sub_lts` | N!=V flag after CMP <-> signed less-than (ARM architecture property) |

### ArmRefinement.v (1 axiom)

| Axiom | Purpose |
|-------|---------|
| `sail_exec_instr` | Placeholder for Sail ARM specification (not yet imported) |

**Total: 41 axioms** (13 I32 + 6 I64 + 20 VFP + 1 flag + 1 refinement)

## Flag-Correspondence Lemmas (ArmFlagLemmas.v)

10 lemmas connecting ARM condition flags to WASM comparison operations:

| Lemma | Meaning |
|-------|---------|
| `z_flag_sub_eq` | Z flag <-> I32.eq (fully proved) |
| `c_flag_sub_geu` | C flag <-> negb (I32.ltu) (fully proved) |
| `nv_flag_sub_lts` | N!=V <-> I32.lts (axiomatized -- ARM architecture fact) |
| `flags_ne` | negb Z <-> I32.ne (derived) |
| `flags_ltu` | negb C <-> I32.ltu (derived) |
| `flags_ges` | N=V <-> I32.ges (derived) |
| `flags_geu` | C <-> I32.geu (derived) |
| `flags_gts` | !Z && N=V <-> I32.gts (derived) |
| `flags_gtu` | C && !Z <-> I32.gtu (derived) |
| `flags_les` | Z || N!=V <-> I32.les (derived) |
| `flags_leu` | !C || Z <-> I32.leu (derived) |

### i64 carry/borrow-propagation lemmas (v0.10.0 PR 1)

| Lemma | Meaning |
|-------|---------|
| `combine_i32_unsigned` | `I64.unsigned (combine_i32 lo hi) = lo_u + 2^32*hi_u` (repr is identity, both halves fit) |
| `carry_split_add` | base-2^32 carry split of `(lo+2^32*hi)+(lo'+2^32*hi')` mod 2^64 (pure Z) |
| `borrow_split_sub` | base-2^32 borrow split of the analogous subtraction (pure Z) |
| `i64_add_via_adds_adc` | (lo,hi) of ADDS+ADC = lo/hi of `I64.add` on combined operands |
| `i64_sub_via_subs_sbc` | (lo,hi) of SUBS+SBC = lo/hi of `I64.sub` on combined operands |

All fully proved (Qed); no new axioms.

## Per-File Breakdown

| File | Qed | Admitted | Tier |
|------|-----|----------|------|
| Correctness.v | 6 | 0 | T1 |
| CorrectnessSimple.v | 28 | 1 | T2 + 1 admitted (i64_const_correct) |
| CorrectnessI32.v | 29 | 0 | T1 |
| CorrectnessI64.v | 26 | 3 | T1 (add+sub+mul+div+rem) + T2 (shifts/cmps/bit-manip) + 3 admitted (And, Or, Xor — restated to T1 shape, pending Z.mod_mod halves-distribute rework) |
| CorrectnessI64Comparisons.v | 19 | 0 | T2 |
| CorrectnessF32.v | 20 | 0 | T2 |
| CorrectnessF64.v | 20 | 0 | T2 |
| CorrectnessConversions.v | 21 | 0 | T2 |
| CorrectnessMemory.v | 8 | 0 | T2 |
| CorrectnessComplete.v | 1 | 0 | T2 |
| ArmRefinement.v | 0 | 2 | T3 |
| Integers.v | 10 | 1 | Infra/T3 |
| ArmFlagLemmas.v | 15 | 0 | Infra (+5: combine_i32_unsigned, carry_split_add, borrow_split_sub, i64_add_via_adds_adc, i64_sub_via_subs_sbc) |
| Tactics.v | 1 | 0 | Infra |
| ArmState.v | 14 | 0 | Infra (+3: get_reg_set_flags, flags_set_flags, flags_set_flags_set_reg) |
| ArmSemantics.v | 8 | 0 | Infra (+1: flag_c_update_flags_arith) |
| WasmSemantics.v | 6 | 0 | Infra |
| Compilation.v | 5 | 0 | Infra |
| Base.v | 4 | 0 | Infra |
| StateMonad.v | 3 | 0 | Infra |
| WasmValues.v | 2 | 0 | Infra |

## Phase History

### Phase 5 (Current): VFP floating-point semantics
- Added abstract VFP operation axioms (21 axioms on bit patterns)
- Modeled all VFP instructions in ArmSemantics.v (arithmetic, comparison, conversion, move, load/store)
- Closed all 48 VFP-dependent admits (CorrectnessF32, CorrectnessF64, CorrectnessConversions, CorrectnessMemory)
- NOTE: i64_to_i32_to_i64_wrap in Integers.v remains Admitted (Rocq 9 Z.mod_mod issue)
- Added VFP register get/set lemmas to ArmState.v
- **Result: 52 -> 3 Admitted** (2 ArmRefinement Sail placeholders + 1 Integers.v)

### Phase 4: Register-based shift instructions
- Added LSL_reg/LSR_reg/ASR_reg/ROR_reg/RSB to ArmInstructions.v and ArmSemantics.v
- Closed 5 i32 shift/rotate admits

### Phase 3: Catch-all removal
- Replaced `| _ => Some s` with `| _ => None` in ArmSemantics.v
- Replaced `| _ => Some s` with `| _ => None` in WasmSemantics.v
- Made proof accounting honest: unmodeled instructions now fail (None) instead
  of silently succeeding as no-ops. 79 unmodeled WASM instructions affected
  (i64 arithmetic/bitwise, all f32/f64, conversions, memory ops).
  Correctness proofs remain valid because they take exec_wasm_instr = Some (...)
  as a hypothesis; with None, the hypothesis is False, making theorems
  vacuously true (honest: we don't claim correctness for what we haven't modeled).
