(** * VCR-ISA-001 (#667): generated-vs-hand-written lowering cross-check.

GENERATED FILE — DO NOT EDIT BY HAND.

Emitted by [crate::sel_dsl::generate_rocq_gencheck_source]. One
[reflexivity] Qed per rule proving the GENERATED lowering
([VcrSelRulesGenerated.Gen.rule_X], emitted straight from the shipped
[sel_dsl::RULES] table) is definitionally equal to the HAND-WRITTEN
[VcrSelRules.rule_X] the correctness theorems are stated about. If the
shipped selector's sequence for a covered op ever diverges from the
model, the matching [reflexivity] stops type-checking — the gate goes
red under [//coq:verify_proofs]. Coq's kernel is the oracle; there is no
text normalizer to get wrong (the #682 lesson).

Pinned up-to-date by the [rocq_gencheck_is_up_to_date] cargo test;
regenerate with
[SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl]. *)

Require Import Synth.ARM.ArmInstructions.
Require Import Synth.Synth.VcrSelRules.
Require Import Synth.Synth.VcrSelRulesGenerated.

Lemma check_rule_i32_add : Gen.rule_i32_add = rule_i32_add.
Proof. reflexivity. Qed.

Lemma check_rule_i32_sub : Gen.rule_i32_sub = rule_i32_sub.
Proof. reflexivity. Qed.

Lemma check_rule_i32_mul : Gen.rule_i32_mul = rule_i32_mul.
Proof. reflexivity. Qed.

Lemma check_rule_i32_and : Gen.rule_i32_and = rule_i32_and.
Proof. reflexivity. Qed.

Lemma check_rule_i32_or : Gen.rule_i32_or = rule_i32_or.
Proof. reflexivity. Qed.

Lemma check_rule_i32_xor : Gen.rule_i32_xor = rule_i32_xor.
Proof. reflexivity. Qed.

Lemma check_rule_i32_rotl : Gen.rule_i32_rotl = rule_i32_rotl.
Proof. reflexivity. Qed.

Lemma check_rule_i32_shl : Gen.rule_i32_shl = rule_i32_shl.
Proof. reflexivity. Qed.

Lemma check_rule_i32_shr_s : Gen.rule_i32_shr_s = rule_i32_shr_s.
Proof. reflexivity. Qed.

Lemma check_rule_i32_shr_u : Gen.rule_i32_shr_u = rule_i32_shr_u.
Proof. reflexivity. Qed.

Lemma check_rule_i32_rotr : Gen.rule_i32_rotr = rule_i32_rotr.
Proof. reflexivity. Qed.

Lemma check_rule_i32_eq : Gen.rule_i32_eq = rule_i32_eq.
Proof. reflexivity. Qed.

Lemma check_rule_i32_ne : Gen.rule_i32_ne = rule_i32_ne.
Proof. reflexivity. Qed.

Lemma check_rule_i32_lt_s : Gen.rule_i32_lt_s = rule_i32_lt_s.
Proof. reflexivity. Qed.

Lemma check_rule_i32_lt_u : Gen.rule_i32_lt_u = rule_i32_lt_u.
Proof. reflexivity. Qed.

Lemma check_rule_i32_gt_s : Gen.rule_i32_gt_s = rule_i32_gt_s.
Proof. reflexivity. Qed.

Lemma check_rule_i32_gt_u : Gen.rule_i32_gt_u = rule_i32_gt_u.
Proof. reflexivity. Qed.

Lemma check_rule_i32_le_s : Gen.rule_i32_le_s = rule_i32_le_s.
Proof. reflexivity. Qed.

Lemma check_rule_i32_le_u : Gen.rule_i32_le_u = rule_i32_le_u.
Proof. reflexivity. Qed.

Lemma check_rule_i32_ge_s : Gen.rule_i32_ge_s = rule_i32_ge_s.
Proof. reflexivity. Qed.

Lemma check_rule_i32_ge_u : Gen.rule_i32_ge_u = rule_i32_ge_u.
Proof. reflexivity. Qed.

Lemma check_rule_i64_add : Gen.rule_i64_add = rule_i64_add.
Proof. reflexivity. Qed.

Lemma check_rule_i64_sub : Gen.rule_i64_sub = rule_i64_sub.
Proof. reflexivity. Qed.

Lemma check_rule_i64_and : Gen.rule_i64_and = rule_i64_and.
Proof. reflexivity. Qed.

Lemma check_rule_i64_or : Gen.rule_i64_or = rule_i64_or.
Proof. reflexivity. Qed.

Lemma check_rule_i64_xor : Gen.rule_i64_xor = rule_i64_xor.
Proof. reflexivity. Qed.

Lemma check_rule_i64_eqz : Gen.rule_i64_eqz = rule_i64_eqz.
Proof. reflexivity. Qed.

Lemma check_rule_i32_clz : Gen.rule_i32_clz = rule_i32_clz.
Proof. reflexivity. Qed.

Lemma check_rule_i32_ctz : Gen.rule_i32_ctz = rule_i32_ctz.
Proof. reflexivity. Qed.

Lemma check_rule_i32_popcnt : Gen.rule_i32_popcnt = rule_i32_popcnt.
Proof. reflexivity. Qed.

Lemma check_rule_i64_eq : Gen.rule_i64_eq = rule_i64_eq.
Proof. reflexivity. Qed.

Lemma check_rule_i64_ne : Gen.rule_i64_ne = rule_i64_ne.
Proof. reflexivity. Qed.

Lemma check_rule_i64_lt_s : Gen.rule_i64_lt_s = rule_i64_lt_s.
Proof. reflexivity. Qed.

Lemma check_rule_i64_lt_u : Gen.rule_i64_lt_u = rule_i64_lt_u.
Proof. reflexivity. Qed.

Lemma check_rule_i64_gt_s : Gen.rule_i64_gt_s = rule_i64_gt_s.
Proof. reflexivity. Qed.

Lemma check_rule_i64_gt_u : Gen.rule_i64_gt_u = rule_i64_gt_u.
Proof. reflexivity. Qed.

Lemma check_rule_i64_le_s : Gen.rule_i64_le_s = rule_i64_le_s.
Proof. reflexivity. Qed.

Lemma check_rule_i64_le_u : Gen.rule_i64_le_u = rule_i64_le_u.
Proof. reflexivity. Qed.

Lemma check_rule_i64_ge_s : Gen.rule_i64_ge_s = rule_i64_ge_s.
Proof. reflexivity. Qed.

Lemma check_rule_i64_ge_u : Gen.rule_i64_ge_u = rule_i64_ge_u.
Proof. reflexivity. Qed.
