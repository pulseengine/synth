# Rocq Proof Suite — Honest Status

**Last Updated: 2026-07-10 (recount: 470 Qed / 8 Admitted, +2 admit., crude
`grep "Qed\."` over `coq/Synth/**/*.v` — same method as prior recounts)

The headline count is CI-gated: `claims.yaml` + `scripts/claim_check.py`
re-derive `Qed.`/`Admitted.`/`admit.` counts from `coq/Synth/**/*.v` on every
commit. When a proof lands, update this file, README.md, CLAUDE.md AND
`claims.yaml` in the same PR.

## 2026-07 executor upgrade: SBCS + CMPcc + a branch-taking executor (#242)

The flat-executor capability gap named by VCR-SEL-001 increment 4 is closed:

- **SBCS** (flags-writing subtract-with-carry) and **CMPCond** (conditionally
  executed CMP, e.g. CMPEQ) are in `exec_instr`, with borrow-aware
  three-operand C/V helpers (`compute_c_flag_sbc` / `compute_v_flag_sbc`).
  The flag math is transcribed, not invented: bridged to the ASL
  `AddWithCarry` / `ConditionHolds` formulations in `SailArmBridge.v`
  round 3 (`sail_bridge_sbcs_reg`, `sail_bridge_cmp_cond_reg`,
  `sail_condition_holds_eq`).
- **`exec_program_pc` / `exec_program_br`** (ArmSemantics.v): a PC-indexed,
  fuel-bounded executor in which `BCondOffset` actually takes the branch.
  The flat `exec_program` is untouched (BCondOffset stays a no-op there),
  so every existing proof still discharges.
- **`VcrSelExpansion.v`** (new, 29 Qed, 0 admits): the ten binary
  I64SetCond rules re-proven at EXPANSION tier — against the encoder's
  actual dual-precision chains (CMP lo,lo; SBCS/CMPEQ hi,hi; MOVcc) —
  with no `i64_setcond_bits` axiom.
- **`i32_divu_correct`** (CorrectnessI32.v): the first #73 trap-guard
  admit DISCHARGED, restated against `exec_program_br` (the BNE skips the
  UDF; extra `I32.valid_unsigned` divisor hypothesis makes the raw-Z
  divu guard and the mod-2^32 Z-flag agree). Compilation.v's I32DivS
  guard offsets corrected for real branch semantics (2→3, 0→1).

**Total admits: 8** (was 9) — 3 i32 division/remainder trap guards
(div_s/rem_s/rem_u, #73 — restatement against `exec_program_br` pending,
no new executor capability needed), 2 Compilation.v, 1 CorrectnessSimple.v,
2 ArmRefinement.v. The headline count grew 291 → 467 because the recount
now includes everything landed since 2026-06-04 (SailArmBridge rounds 1–3,
VcrSelRules increments, VcrSelExpansion, i64 certifying validation lemmas).

## v0.11.0 outcome: true i64 T1 parity

`i64_and_correct` / `i64_or_correct` / `i64_xor_correct` are now **Qed** —
the final i64 bitwise T1 lifts. This completes i64 T1 result-correspondence
parity with i32 (40 i64 T1 Qed, **0 i64 admits**).

New helpers (all Qed, no axioms): `div32_mod64`
(`(a mod 2^64)/2^32 = (a/2^32) mod 2^32`, bit-extensionality), `and_hi_combine`
+ the or/xor lo/hi combine analogues. The three theorem exec-proofs step
`exec_program` over the flag-free pairs `[AND R0 R0 R2; AND R1 R1 R3]`
(ORR/EOR identical) and apply the combine lemmas — the `i64_add_correct`
template minus flag-peeling.

**Total admits: 8** (was 12) — 3 i32 division (separate exec_program-model
gap #73), 2 Compilation.v, 1 CorrectnessSimple.v, 2 ArmRefinement.v. No
remaining i64 admits.

## v0.10.0 PR 2 outcome: Z.mod_mod wrap closed + bitwise lift infrastructure

`i64_to_i32_to_i64_wrap` (Common/Integers.v) — the long-standing Rocq 9
`Z.mod_mod` Admit — is now Qed (canonical symbolic-atom modular proof; no
axioms). Landed the bitwise halves-distribute infrastructure for the i64
and/or/xor T1 lifts: six pure-Z distribution lemmas (`{land,lor,lxor}_{low,high}32`),
`combine_i32_raw`, `mod64_mod32`, `combine_lo32`/`combine_hi32`, and
`and_lo_combine` — all Qed, no axioms.

**Deferred to v0.11.0:** `i64_and_correct` / `i64_or_correct` /
`i64_xor_correct` remain Admitted (3 admits). The remaining work is the
high-half combine helper (`(Z.land X Y mod 2^64)/2^32 mod 2^32`, via
`ZDivEucl.mod_mul_r`), the or/xor analogues, and the three theorem
exec-proofs (template: `i64_add_correct` minus flag handling). The
infrastructure to close them is in place.

**Total admits: 12** — 3 i32 division (separate exec_program-model gap),
2 Compilation.v, 1 CorrectnessSimple.v, 3 i64 and/or/xor (above),
2 ArmRefinement.v.

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

3. **Discharges**: 5/5 admits closed as `Qed` (3 div/rem + 1 i64_const).

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
| **T1: Result Correspondence** | ARM output register = WASM result value | 37¹ |
| **T2: Existence-Only** | ARM execution succeeds (no result claim) | 139¹ |
| **T3: Admitted / admit.** | Not yet proven | 11 (8 Admitted + 2 admit.) |
| **Infrastructure** | Properties of integers, states, flag lemmas | 65¹ |

¹ T1/T2/Infrastructure tier classification is the 2026-06-04 semantic recount
and predates the VcrSelRules (42), VcrSelPilot (7) and SailArmBridge (92) Qed;
see the per-file breakdown below for current per-file counts. The T3 row and
the headline total are re-derived by the claim gate.

**Total: 470 Qed / 8 Admitted (+2 admit.) across all files** (recount 2026-07-10, CI-gated via `claims.yaml`)

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
| CorrectnessI32.v | 3 | `i32_divs/divu/rems/remu_correct` — trap guard sequences (CMP+BCondOffset+UDF) cannot be verified in the sequential exec_program model | Extend exec_program to support PC-relative branching |
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

**Total: 93 Axiom/Parameter declarations** (recount 2026-07-10,
`grep -E '^\s*(Axiom|Parameter) '` over `coq/Synth/**/*.v`; CI-gated via
`claims.yaml`): 19 Integers.v (13 I32 + 6 I64), 72 ArmSemantics.v (the 21 VFP
bit-pattern axioms tabled above + the i64 pseudo-op `_spec` result axioms +
abstract operation parameters), 1 ArmFlagLemmas.v (`nv_flag_sub_lts`),
1 ArmRefinement.v (`sail_exec_instr`). The tables above enumerate the
originally-documented subset; the grep count is the authoritative trusted-base
size.

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

Recount 2026-07-10 (`grep -oE 'Qed\.'` / `'Admitted\.'` per file):

| File | Qed | Admitted | Tier |
|------|-----|----------|------|
| Correctness.v | 6 | 0 | T1 |
| CorrectnessSimple.v | 28 | 1 | T2 + 1 admitted (i64_const_correct) |
| CorrectnessI32.v | 28 | 3 | T1 + 3 admitted (i32_divu discharged #697) (i32 div/rem trap guards — exec_program model gap, #73) |
| CorrectnessI64.v | 46 | 0 | T1 (arith/bitwise/div/rem) + T2 (shifts/cmps/bit-manip) — 0 i64 admits since v0.11.0 |
| CorrectnessI64Comparisons.v | 19 | 0 | T2 |
| CorrectnessF32.v | 20 | 0 | T2 |
| CorrectnessF64.v | 20 | 0 | T2 |
| CorrectnessConversions.v | 21 | 0 | T2 |
| CorrectnessMemory.v | 8 | 0 | T2 |
| CorrectnessComplete.v | 0 | 0 | commentary only (tier taxonomy) |
| ArmRefinement.v | 0 | 2 | T3 (+ the 2 `admit.` tactics) |
| Integers.v | 11 | 0 | Infra (i64_to_i32_to_i64_wrap closed v0.10.0 PR 2) |
| ArmFlagLemmas.v | 46 | 0 | Infra (flag correspondence + i64 carry/borrow/shift lemmas) |
| Tactics.v | 1 | 0 | Infra |
| ArmState.v | 14 | 0 | Infra |
| ArmSemantics.v | 8 | 0 | Infra |
| SailArmBridge.v | 92 | 0 | Infra (VCR-ISA-001 Sail/ASL bridge: AddWithCarry family + ALU + shifts + moves) |
| WasmSemantics.v | 6 | 0 | Infra |
| Compilation.v | 3 | 2 | Infra + 2 admitted (`ex_compile_*` examples — Z.leb reduction) |
| Base.v | 4 | 0 | Infra |
| StateMonad.v | 3 | 0 | Infra |
| WasmValues.v | 2 | 0 | Infra |
| VcrSelPilot.v | 7 | 0 | T1 (register-polymorphic; VCR-SEL-001 go/abandon measurement) |
| VcrSelRules.v | 42 | 0 | T1 (register-polymorphic; the WIRED VCR-SEL-001 increment-1+2+3+4 rule table — 40 rule theorems 1:1 with `coq/vcr_sel_rules.manifest`, coverage-gated by `//coq:vcr_sel_rules_coverage`, + 2 mod-32 helper lemmas #683) |
| **Total** | **470** | **9** | (+2 `admit.`) |

## VCR-SEL-001 increments 1 (2026-07-07) + 2 + 3 + 4 (2026-07-08): VcrSelRules.v

The wired selector-DSL rule table's obligations: one universally-quantified
T1 theorem per rule in `crates/synth-synthesis/src/sel_dsl`.

Increment 1 — the tier-A six
(`rule_i32_{add,sub,mul,and,or,xor}_correct`, discharged by
`synth_binop_proof_poly` verbatim) plus `rule_i32_rotl_correct` (stepped
proof with the explicit `rs <> rn` scratch non-aliasing hypothesis the rule
table carries as a side condition).

Increment 2 — the i32 register shifts + rotr
(`rule_i32_{shl,shr_s,shr_u,rotr}_correct`: measured tier-A, single
instruction, no scratch — discharged by the same `synth_binop_proof_poly`)
plus the ten i32 comparisons
(`rule_i32_{eq,ne,lt_s,lt_u,gt_s,gt_u,le_s,le_u,ge_s,ge_u}_correct`, the
CMP+SetCond shape modeled as `CMP; MOV rd #0; MOVcc rd #1` per the
Compilation.v convention; NO aliasing side conditions — CMP latches NZCV
before `rd` is written, so the universal quantifier admits every aliasing.
Seven close with `synth_cmp_binop_proof_poly` — the fixed-register
`synth_cmp_binop_proof` generalized to universally-quantified registers —
and `ne`/`lt_s`/`lt_u` use the same manual scripts as their
CorrectnessI32.v ancestors, register-generalized verbatim).

Increment 3 — the i64 register-pair family
(`rule_i64_{add,sub,and,or,xor}_correct`, quantified over SIX registers
under three explicit aliasing hypotheses, pair-result T1 proving BOTH words;
plus `rule_i64_eqz_correct`, the `I64SetCondZ` pseudo-op shape).

Increment 4 — the scratch-using/multi-instruction tier + the binary
`I64SetCond` comparison family
(`rule_i32_{clz,popcnt}_correct` via `synth_unop_proof_poly`;
`rule_i32_ctz_correct`, the two-instruction RBIT+CLZ scratch=dest shape,
stepped proof closing with `I32.clz_rbit`;
`rule_i64_{eq,ne,lt_s,lt_u,gt_s,gt_u,le_s,le_u,ge_s,ge_u}_correct` via
`synth_i64_setcond_proof_poly` against `i64_setcond_bits_spec` — pseudo-op
tier: the encoder's CMP-lo/SBCS-hi expansion is below the flat executor,
see `docs/design/vcr-sel-001-increment-4.md`).

**40 Qed / 0 Admitted**, same T1 bound as the pilot ("the ARM sequence
computes the named result", not WASM refinement). These 47 Qed (pilot +
rules) are included in the 2026-07-10 recount above.

## DSL coverage vs model relevance (per-op-family metric, #667)

The Rocq suite proves things in two very different places, and #73's
"retirement by subtraction" of the divergent monolithic model is only
measurable if they are counted separately:

- **DSL-served** — the op's *shipped* lowering is a `sel_dsl` rule with a
  1:1 Qed theorem in `VcrSelRules.v`, register-polymorphic, mirror-pinned
  byte-identical to the hand-written arm(s) (`SYNTH_SEL_DSL`, **default ON**
  since the increment-1..4 flip — opt-out `SYNTH_NO_SEL_DSL=1`). These proofs
  are about the code that ships — and now, by default, the code that DOES ship.
- **model-only** — the op is proven only against `compile_wasm_to_arm`
  (Compilation.v), the fixed-register model that diverges from the shipped
  Rust selector in documented ways (#73). Evidence about a model, not the
  binary.
- **unverified** — the shipped selector lowers the op but no Rocq theorem
  covers it in either form.

Every op family the shipped ARM selectors lower, as of increment 4
(update this table whenever a rule lands or a model arm is retired):

| Op family | ops | DSL-served | model-only | unverified |
|---|---|---|---|---|
| i32 ALU (add/sub/mul/and/or/xor) | 6 | **6** | 0 | 0 |
| i32 shifts/rotates (shl/shr_s/shr_u/rotr/rotl) | 5 | **5** | 0 | 0 |
| i32 binary comparisons (eq..ge_u) | 10 | **10** | 0 | 0 |
| i32.eqz (CMP-imm shape) | 1 | 0 | 1 | 0 |
| i32 bit-manip (clz/ctz/popcnt) | 3 | **3**¹ | 0 | 0 |
| i32 div/rem (trap-guarded) | 4 | 0 | 4² | 0 |
| i32 sign-extend (extend8_s/16_s) | 2 | 0 | 0 | 2 |
| i32.const | 1 | 0 | 1 | 0 |
| i64 pair ALU (add/sub/and/or/xor) | 5 | **5** | 0 | 0 |
| i64 comparisons (eqz + eq..ge_u) | 11 | **11**¹ | 0 | 0 |
| i64 mul/div/rem | 4 | 0 | 4 | 0 |
| i64 shifts/rotates (pair pseudo-ops) | 5 | 0 | 5 | 0 |
| i64 bit-manip (clz/ctz/popcnt) | 3 | 0 | 3 | 0 |
| i64 wrap/extend (wrap_i64, extend_i32_s/u) | 3 | 0 | 3 | 0 |
| i64 sign-extend (extend8/16/32_s) | 3 | 0 | 0 | 3 |
| i64.const | 1 | 0 | 1 | 0 |
| f32/f64 arithmetic + comparisons³ | 40 | 0 | 40 | 0 |
| conversions (trunc/convert/demote/promote) | 18 | 0 | 18 | 0 |
| memory load/store (i32/i64/f32/f64, basic) | 8 | 0 | 8 | 0 |
| bulk memory (memory.copy/fill), memory.size/grow | 4 | 0 | 0 | 4 |
| locals/globals (get/set/tee) | 5 | 0 | 5 | 0 |
| parametric (drop/select/nop) | 3 | 0 | 3 | 0 |
| control flow (block/loop/br/br_if/return/call/…) | ~10 | 0 | 0 | ~10 |
| **Total (≈)** | **155** | **40 (26%)** | **96 (62%)** | **19 (12%)** |

¹ pseudo-op tier: `popcnt`, `i64.eqz` and the ten binary i64 comparisons are
proven at the `ArmOp` pseudo-op boundary (the selector's emission, which is
what the DSL owns); the encoder expansions below that boundary
(shift-and-add popcnt, the CMP-lo/SBCS-hi chain) are covered by the
differential oracles, not Rocq — see `docs/design/vcr-sel-001-increment-4.md`.
² the 4 i32 div/rem model proofs are the T3 trap-guard admits (#73,
`BCondOffset` executor gap).
³ the f32/f64 model rows ride the 21 VFP axioms; the shipped ARM path
additionally gates FPU ops behind the #369/GI-FPU work.

**Retirement criterion (#73):** a `compile_wasm_to_arm` arm may be deleted
(and its Correctness* theorem retired) once its family is DSL-served — the
DSL theorem is strictly stronger (register-polymorphic, mirror-pinned to
the shipped bytes). The model-only column is the shrinking measure; report
it per release.

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
