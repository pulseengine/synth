# Rocq Proof Suite — Honest Status

**Last Updated:** April 2026

## Overview

Synth's Rocq proof suite verifies that `compile_wasm_to_arm` preserves WASM semantics.
After adding VFP floating-point semantics to ArmSemantics.v, all 48 previously-admitted
VFP proofs are closed. 3 admits remain: 2 ArmRefinement Sail integration placeholders
and 1 `i64_to_i32_to_i64_wrap` lemma in Integers.v (Rocq 9 `Z.mod_mod` migration issue).

## Proof Tiers

| Tier | Meaning | Count |
|------|---------|-------|
| **T1: Result Correspondence** | ARM output register = WASM result value | 39 |
| **T2: Existence-Only** | ARM execution succeeds (no result claim) | 143 |
| **T3: Admitted** | Not yet proven | 3 |
| **Infrastructure** | Properties of integers, states, flag lemmas | 59 |

**Total: 241 Qed / 3 Admitted across all files**

## T1: Result Correspondence (39 Qed)

These are the crown jewels — they prove the compiled ARM code produces the exact same
value as the WASM operation.

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

### i32 Division (4)

| File | Theorem | Operation |
|------|---------|-----------|
| CorrectnessI32.v | `i32_divs_correct` | I32DivS |
| CorrectnessI32.v | `i32_divu_correct` | I32DivU |
| CorrectnessI32.v | `i32_rems_correct` | I32RemS |
| CorrectnessI32.v | `i32_remu_correct` | I32RemU |

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

### i64 Division (4) — uses I32 division (32-bit register limitation)

| File | Theorem | Operation |
|------|---------|-----------|
| CorrectnessI64.v | `i64_divs_correct` | I64DivS |
| CorrectnessI64.v | `i64_divu_correct` | I64DivU |
| CorrectnessI64.v | `i64_rems_correct` | I64RemS |
| CorrectnessI64.v | `i64_remu_correct` | I64RemU |

Note: i64 div/rem proofs use `I32.divs`/`I32.divu` hypotheses (what ARM actually computes
with 32-bit registers), not `I64.divs`/`I64.divu`.

Each T1 proof proves: `get_reg astate' R0 = <result>` after executing the compiled ARM program.

## T2: Existence-Only (143 Qed)

These prove the ARM program executes successfully but don't claim the result value is correct.
Named `*_executes` to distinguish from T1 `*_correct` proofs.

| File | Count | Operations |
|------|-------|------------|
| CorrectnessSimple.v | 29 | Nop, Drop, Select, LocalGet/Set/Tee, GlobalGet/Set, I32Const, I64Const, 11 comparisons, 5 shifts, 3 bit-manip |
| CorrectnessI64.v | 25 | Add, Sub, Mul, And, Or, Xor, 5 shifts, 11 comparisons, 3 bit-manip |
| CorrectnessI64Comparisons.v | 19 | 11 comparisons, 3 bit-manip, 5 shifts |
| CorrectnessF32.v | 20 | 7 empty-program + 13 VFP (4 arith, 3 unary, 6 comparison) |
| CorrectnessF64.v | 20 | 7 empty-program + 13 VFP (4 arith, 3 unary, 6 comparison) |
| CorrectnessConversions.v | 21 | 3 integer + 18 VFP conversions |
| CorrectnessMemory.v | 8 | 4 i32/i64 + 4 f32/f64 load/store |
| CorrectnessComplete.v | 1 | Master compilation theorem |

## T3: Admitted (3)

| File | Count | Root Cause | Unblocking Strategy |
|------|-------|------------|---------------------|
| ArmRefinement.v | 2 | Needs Sail-generated ARM semantics | Phase 2: Import Sail specifications |
| Integers.v | 1 | `i64_to_i32_to_i64_wrap` — Rocq 9 `Z.mod_mod` signature changed | Rework proof for new Z.mod_mod API |

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

## Per-File Breakdown

| File | Qed | Admitted | Tier |
|------|-----|----------|------|
| Correctness.v | 6 | 0 | T1 |
| CorrectnessSimple.v | 29 | 0 | T2 |
| CorrectnessI32.v | 29 | 0 | T1 |
| CorrectnessI64.v | 29 | 0 | T1+T2 |
| CorrectnessI64Comparisons.v | 19 | 0 | T2 |
| CorrectnessF32.v | 20 | 0 | T2 |
| CorrectnessF64.v | 20 | 0 | T2 |
| CorrectnessConversions.v | 21 | 0 | T2 |
| CorrectnessMemory.v | 8 | 0 | T2 |
| CorrectnessComplete.v | 1 | 0 | T2 |
| ArmRefinement.v | 0 | 2 | T3 |
| Integers.v | 10 | 1 | Infra/T3 |
| ArmFlagLemmas.v | 10 | 0 | Infra |
| Tactics.v | 1 | 0 | Infra |
| ArmState.v | 11 | 0 | Infra |
| ArmSemantics.v | 7 | 0 | Infra |
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
- Made proof accounting honest
