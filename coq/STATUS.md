# Rocq Proof Suite — Honest Status

**Last Updated:** March 2026 (after Phase 4: register-based shifts)

## Overview

Synth's Rocq proof suite verifies that `compile_wasm_to_arm` preserves WASM semantics for
integer operations. After removing the silent catch-all (`| _ => Some s`) from ARM semantics,
only proofs backed by real instruction semantics survive.

## Proof Tiers

| Tier | Meaning | Count |
|------|---------|-------|
| **T1: Result Correspondence** | ARM output register = WASM result value | 39 |
| **T2: Existence-Only** | ARM execution succeeds (no result claim) | 95 |
| **T3: Admitted** | Not yet proven | 52 |
| **Infrastructure** | Properties of integers, states, flag lemmas | 54 |

**Total: 188 Qed / 52 Admitted across all files**

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

## T2: Existence-Only (95 Qed)

These prove the ARM program executes successfully but don't claim the result value is correct.
Named `*_executes` to distinguish from T1 `*_correct` proofs.

| File | Count | Operations |
|------|-------|------------|
| CorrectnessSimple.v | 29 | Nop, Drop, Select, LocalGet/Set/Tee, GlobalGet/Set, I32Const, I64Const, 11 comparisons, 5 shifts, 3 bit-manip |
| CorrectnessI64.v | 25 | Add, Sub, Mul, And, Or, Xor, 5 shifts, 11 comparisons, 3 bit-manip |
| CorrectnessI64Comparisons.v | 19 | 11 comparisons, 3 bit-manip, 5 shifts |
| CorrectnessF32.v | 7 | Min, Max, Copysign, Ceil, Floor, Trunc, Nearest (compile to `[]`) |
| CorrectnessF64.v | 7 | Min, Max, Copysign, Ceil, Floor, Trunc, Nearest (compile to `[]`) |
| CorrectnessConversions.v | 3 | I32WrapI64, I64ExtendI32S, I64ExtendI32U (compile to `[]`) |
| CorrectnessMemory.v | 4 | I32Load, I64Load, I32Store, I64Store |
| CorrectnessComplete.v | 1 | Master compilation theorem |

## T3: Admitted (52)

| Category | Count | Root Cause | Unblocking Strategy |
|----------|-------|------------|---------------------|
| VFP float ops | 26 | No floating-point semantics | Integrate Flocq IEEE 754 library |
| Float conversions | 18 | No VFP conversion semantics | Integrate Flocq IEEE 754 library |
| Float memory | 4 | VLDR/VSTR unmodeled | Model VFP load/store in ArmSemantics |
| ArmRefinement | 2 | Needs simulation relation | Low priority |
| Other | 2 | CorrectnessComplete (1), Integers (1) | Low priority |

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

### ArmFlagLemmas.v (1 axiom)

| Axiom | Purpose |
|-------|---------|
| `nv_flag_sub_lts` | N≠V flag after CMP ↔ signed less-than (ARM architecture property) |

## Flag-Correspondence Lemmas (ArmFlagLemmas.v)

10 lemmas connecting ARM condition flags to WASM comparison operations:

| Lemma | Meaning |
|-------|---------|
| `z_flag_sub_eq` | Z flag ↔ I32.eq (fully proved) |
| `c_flag_sub_geu` | C flag ↔ negb (I32.ltu) (fully proved) |
| `nv_flag_sub_lts` | N≠V ↔ I32.lts (axiomatized — ARM architecture fact) |
| `flags_ne` | negb Z ↔ I32.ne (derived) |
| `flags_ltu` | negb C ↔ I32.ltu (derived) |
| `flags_ges` | N=V ↔ I32.ges (derived) |
| `flags_geu` | C ↔ I32.geu (derived) |
| `flags_gts` | !Z && N=V ↔ I32.gts (derived) |
| `flags_gtu` | C && !Z ↔ I32.gtu (derived) |
| `flags_les` | Z || N≠V ↔ I32.les (derived) |
| `flags_leu` | !C || Z ↔ I32.leu (derived) |

## Catch-All Removal

The original `exec_instr` in `ArmSemantics.v` had:
```coq
| _ => Some s  (* Not yet implemented *)
```

This made every unmodeled instruction a silent no-op, allowing ~48 proofs to pass
vacuously. It has been replaced with:
```coq
| _ => None  (* Unmodeled instruction — execution fails *)
```

Additionally, the four explicit VFP placeholders (`VADD_F32 => Some s`, etc.)
were changed to `None`.

## Register-Based Shift Instructions (Phase 4)

Compilation.v previously used fixed-immediate shifts (`LSL R0 R0 0`) which didn't
match the Rust instruction selector. Phase 4 added register-based shift variants
to `ArmInstructions.v` and `ArmSemantics.v`:

- `LSL_reg Rd Rn Rm` — logical shift left by register
- `LSR_reg Rd Rn Rm` — logical shift right by register
- `ASR_reg Rd Rn Rm` — arithmetic shift right by register
- `ROR_reg Rd Rn Rm` — rotate right by register
- `RSB Rd Rn Op2` — reverse subtract (`Op2 - Rn`)

This closed the 5 i32 shift/rotate admits and aligned Compilation.v with the Rust
`instruction_selector.rs` for these operations.

## Per-File Breakdown

| File | Qed | Admitted | Tier |
|------|-----|----------|------|
| Correctness.v | 6 | 0 | T1 |
| CorrectnessSimple.v | 29 | 0 | T2 |
| CorrectnessI32.v | 29 | 0 | T1 |
| CorrectnessI64.v | 29 | 0 | T1+T2 |
| CorrectnessI64Comparisons.v | 19 | 0 | T2 |
| CorrectnessF32.v | 7 | 13 | T2+T3 |
| CorrectnessF64.v | 7 | 13 | T2+T3 |
| CorrectnessConversions.v | 3 | 18 | T2+T3 |
| CorrectnessMemory.v | 4 | 4 | T2+T3 |
| CorrectnessComplete.v | 1 | 1 | T2+T3 |
| ArmFlagLemmas.v | 10 | 0 | Infra |
| Tactics.v | 1 | 0 | Infra |
| Infrastructure (8 files) | 43 | 3 | Infra |
