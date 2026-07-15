(** * VCR-ISA-001 (#667): the selector rule table's Rocq lowerings, GENERATED.

GENERATED FILE — DO NOT EDIT BY HAND.

Emitted by [crate::sel_dsl::generate_rocq_lowering_source] from the
shipped rule table [crates/synth-synthesis/src/sel_dsl/mod.rs] (RULES),
the SAME table that produces the shipped Rust lowering
([sel_dsl/generated.rs]). This module is the SINGLE SOURCE of the Rocq
model definitions: [VcrSelRules.v] re-exports every rule
([Definition rule_X := Gen.rule_X]) and states the correctness theorems
directly about these generated sequences — so the model the theorems
are ABOUT cannot silently diverge from the shipped selector for the
covered ops (the #682 vacuous-proof failure mode, closed at the
instruction-sequence level: a RULES change regenerates this file and
the matching correctness Qed stops compiling).

Pinned up-to-date by the [rocq_generated_lowering_is_up_to_date] cargo
test; regenerate with
[SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl]. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.
Import ListNotations.
Open Scope Z_scope.

Module Gen.

Definition rule_i32_add (rd rn rm : arm_reg) : arm_program :=
  [ADD rd rn (Reg rm)].

Definition rule_i32_sub (rd rn rm : arm_reg) : arm_program :=
  [SUB rd rn (Reg rm)].

Definition rule_i32_mul (rd rn rm : arm_reg) : arm_program :=
  [MUL rd rn rm].

Definition rule_i32_and (rd rn rm : arm_reg) : arm_program :=
  [AND rd rn (Reg rm)].

Definition rule_i32_or (rd rn rm : arm_reg) : arm_program :=
  [ORR rd rn (Reg rm)].

Definition rule_i32_xor (rd rn rm : arm_reg) : arm_program :=
  [EOR rd rn (Reg rm)].

Definition rule_i32_rotl (rd rn rm rs : arm_reg) : arm_program :=
  [RSB rs rm (Imm (I32.repr 32)); ROR_reg rd rn rs].

Definition rule_i32_shl (rd rn rm rs : arm_reg) : arm_program :=
  [AND rs rm (Imm (I32.repr 31)); LSL_reg rd rn rs].

Definition rule_i32_shr_s (rd rn rm rs : arm_reg) : arm_program :=
  [AND rs rm (Imm (I32.repr 31)); ASR_reg rd rn rs].

Definition rule_i32_shr_u (rd rn rm rs : arm_reg) : arm_program :=
  [AND rs rm (Imm (I32.repr 31)); LSR_reg rd rn rs].

Definition rule_i32_rotr (rd rn rm : arm_reg) : arm_program :=
  [ROR_reg rd rn rm].

Definition rule_i32_eq (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVEQ rd (Imm I32.one)].

Definition rule_i32_ne (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVNE rd (Imm I32.one)].

Definition rule_i32_lt_s (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVLT rd (Imm I32.one)].

Definition rule_i32_lt_u (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVLO rd (Imm I32.one)].

Definition rule_i32_gt_s (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVGT rd (Imm I32.one)].

Definition rule_i32_gt_u (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVHI rd (Imm I32.one)].

Definition rule_i32_le_s (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVLE rd (Imm I32.one)].

Definition rule_i32_le_u (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVLS rd (Imm I32.one)].

Definition rule_i32_ge_s (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVGE rd (Imm I32.one)].

Definition rule_i32_ge_u (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVHS rd (Imm I32.one)].

Definition rule_i32_eqz (rd rn : arm_reg) : arm_program :=
  [CMP rn (Imm I32.zero); MOV rd (Imm I32.zero); MOVEQ rd (Imm I32.one)].

Definition rule_i64_add (rdlo rdhi rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [ADDS rdlo rnlo (Reg rmlo); ADC rdhi rnhi (Reg rmhi)].

Definition rule_i64_sub (rdlo rdhi rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [SUBS rdlo rnlo (Reg rmlo); SBC rdhi rnhi (Reg rmhi)].

Definition rule_i64_and (rdlo rdhi rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [AND rdlo rnlo (Reg rmlo); AND rdhi rnhi (Reg rmhi)].

Definition rule_i64_or (rdlo rdhi rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [ORR rdlo rnlo (Reg rmlo); ORR rdhi rnhi (Reg rmhi)].

Definition rule_i64_xor (rdlo rdhi rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [EOR rdlo rnlo (Reg rmlo); EOR rdhi rnhi (Reg rmhi)].

Definition rule_i64_eqz (rd rnlo rnhi : arm_reg) : arm_program :=
  [I64SetCondZ rd rnlo rnhi].

Definition rule_i32_clz (rd rm : arm_reg) : arm_program :=
  [CLZ rd rm].

Definition rule_i32_ctz (rd rm : arm_reg) : arm_program :=
  [RBIT rd rm; CLZ rd rd].

Definition rule_i32_popcnt (rd rm : arm_reg) : arm_program :=
  [POPCNT rd rm].

Definition rule_i64_eq (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64SetCond rd rnlo rnhi rmlo rmhi Cond_EQ].

Definition rule_i64_ne (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64SetCond rd rnlo rnhi rmlo rmhi Cond_NE].

Definition rule_i64_lt_s (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64SetCond rd rnlo rnhi rmlo rmhi Cond_LT].

Definition rule_i64_lt_u (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64SetCond rd rnlo rnhi rmlo rmhi Cond_CC].

Definition rule_i64_gt_s (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64SetCond rd rnlo rnhi rmlo rmhi Cond_GT].

Definition rule_i64_gt_u (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64SetCond rd rnlo rnhi rmlo rmhi Cond_HI].

Definition rule_i64_le_s (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64SetCond rd rnlo rnhi rmlo rmhi Cond_LE].

Definition rule_i64_le_u (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64SetCond rd rnlo rnhi rmlo rmhi Cond_LS].

Definition rule_i64_ge_s (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64SetCond rd rnlo rnhi rmlo rmhi Cond_GE].

Definition rule_i64_ge_u (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64SetCond rd rnlo rnhi rmlo rmhi Cond_CS].

Definition rule_i64_clz (rd rnlo rnhi : arm_reg) : arm_program :=
  [I64ClzPseudo rd rnlo rnhi].

Definition rule_i64_ctz (rd rnlo rnhi : arm_reg) : arm_program :=
  [I64CtzPseudo rd rnlo rnhi].

Definition rule_i64_popcnt (rd rnlo rnhi : arm_reg) : arm_program :=
  [I64PopcntPseudo rd rnlo rnhi].

Definition rule_i64_mul (rdlo rdhi rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64MulPseudo rdlo rdhi rnlo rnhi rmlo rmhi].

Definition rule_i64_shl (rdlo rdhi rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64ShlPseudo rdlo rdhi rnlo rnhi rmlo rmhi].

Definition rule_i64_shr_u (rdlo rdhi rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64ShrUPseudo rdlo rdhi rnlo rnhi rmlo rmhi].

Definition rule_i64_shr_s (rdlo rdhi rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [I64ShrSPseudo rdlo rdhi rnlo rnhi rmlo rmhi].

Definition rule_i64_rotl (rdlo rdhi rnlo rnhi rmlo : arm_reg) : arm_program :=
  [I64RotlPseudo rdlo rdhi rnlo rnhi rmlo].

Definition rule_i64_rotr (rdlo rdhi rnlo rnhi rmlo : arm_reg) : arm_program :=
  [I64RotrPseudo rdlo rdhi rnlo rnhi rmlo].

End Gen.
