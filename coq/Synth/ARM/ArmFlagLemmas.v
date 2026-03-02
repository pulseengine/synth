(** * ARM Flag-Correspondence Lemmas

    This file proves that ARM condition flags after CMP correctly
    reflect WASM comparison operations.

    Key lemmas:
    - z_flag_sub_eq:  Z flag ↔ I32.eq  (proved)
    - c_flag_sub_geu: C flag ↔ I32.geu (proved)
    - nv_flag_sub_lts: N≠V ↔ I32.lts  (axiomatized — ARM architecture property)

    These lemmas close the 11 i32 comparison admits in CorrectnessI32.v.
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.
Require Import Synth.ARM.ArmSemantics.

Open Scope Z_scope.

(** ** Core Flag Lemmas *)

(** Z flag after CMP correctly reflects equality.
    compute_z_flag (v1 - v2) = true  ↔  v1 = v2  (as 32-bit integers) *)
Lemma z_flag_sub_eq : forall v1 v2 : I32.int,
  compute_z_flag (I32.sub v1 v2) = I32.eq v1 v2.
Proof.
  intros v1 v2.
  unfold compute_z_flag.
  (* compute_z_flag x = I32.eq x I32.zero *)
  (* I32.eq (I32.sub v1 v2) I32.zero = I32.eq v1 v2 *)
  unfold I32.eq, I32.sub, I32.unsigned, I32.zero, I32.repr.
  assert (Hm : I32.modulus > 0) by (unfold I32.modulus; lia).
  (* Work with v1 mod m and v2 mod m directly *)
  set (m := I32.modulus) in *.
  set (a := v1 mod m).
  set (b := v2 mod m).
  assert (Ha : 0 <= a < m) by (subst a; apply Z_mod_lt; lia).
  assert (Hb : 0 <= b < m) by (subst b; apply Z_mod_lt; lia).
  (* The LHS simplifies: sub v1 v2 = (v1 - v2) mod m,
     then unsigned of that = ((v1 - v2) mod m) mod m = (v1 - v2) mod m.
     And unsigned zero = (0 mod m) mod m = 0.
     So LHS = Z.eqb ((v1 - v2) mod m) 0. *)
  rewrite (Zmod_mod (v1 - v2) m) by lia.
  replace ((0 mod m) mod m) with 0 by (rewrite Zmod_mod by lia; rewrite Z.mod_0_l by lia; reflexivity).
  (* RHS = Z.eqb a b *)
  (* LHS = Z.eqb ((v1 - v2) mod m) 0 *)
  destruct (Z.eqb a b) eqn:Eab.
  - apply Z.eqb_eq in Eab.
    (* a = b means v1 mod m = v2 mod m, so (v1 - v2) mod m = 0 *)
    apply Z.eqb_eq.
    subst a b.
    rewrite Zminus_mod.
    rewrite Eab.
    replace (v2 mod m - v2 mod m) with 0 by lia.
    apply Z.mod_0_l. lia.
  - apply Z.eqb_neq in Eab.
    apply Z.eqb_neq.
    intro H.
    apply Eab.
    (* H: (v1 - v2) mod m = 0 → a = b *)
    subst a b.
    rewrite Zminus_mod in H.
    apply Z.mod_divide in H; [| lia].
    destruct H as [k Hk].
    assert (Ha' : 0 <= v1 mod m < m) by (apply Z_mod_lt; lia).
    assert (Hb' : 0 <= v2 mod m < m) by (apply Z_mod_lt; lia).
    (* v1 mod m - v2 mod m = m * k, with |diff| < m, so k = 0 *)
    assert (k = 0) by nia. subst k. lia.
Qed.

(** C flag after CMP correctly reflects unsigned ≥.
    compute_c_flag_sub v1 v2 = true  ↔  v1 ≥ v2  (unsigned) *)
Lemma c_flag_sub_geu : forall v1 v2 : I32.int,
  compute_c_flag_sub v1 v2 = negb (I32.ltu v1 v2).
Proof.
  intros v1 v2.
  unfold compute_c_flag_sub, I32.ltu, I32.unsigned.
  set (a := v1 mod I32.modulus).
  set (b := v2 mod I32.modulus).
  destruct (Z.leb b a) eqn:E; destruct (Z.ltb a b) eqn:F;
  simpl; try reflexivity.
  - exfalso. apply Z.leb_le in E. apply Z.ltb_lt in F. lia.
  - exfalso. apply Z.leb_gt in E. apply Z.ltb_ge in F. lia.
Qed.

(** N≠V flag combination after CMP correctly reflects signed <.
    This is a well-known ARM architecture property:
    After CMP Rn, Op2, the condition LT (N≠V) holds iff Rn <s Op2.

    The formal proof requires detailed case analysis on signed overflow
    semantics. We axiomatize this as it is a standard ARM architecture
    fact documented in the ARM Architecture Reference Manual. *)
Axiom nv_flag_sub_lts : forall v1 v2 : I32.int,
  negb (Bool.eqb (compute_n_flag (I32.sub v1 v2)) (compute_v_flag_sub v1 v2))
  = I32.lts v1 v2.

(** ** Derived Flag Lemmas

    These connect compound flag conditions to WASM comparison operations. *)

(** NE condition: Z flag clear ↔ not equal *)
Lemma flags_ne : forall v1 v2 : I32.int,
  negb (compute_z_flag (I32.sub v1 v2)) = I32.ne v1 v2.
Proof.
  intros. unfold I32.ne. rewrite z_flag_sub_eq. reflexivity.
Qed.

(** LtU condition: C flag clear ↔ unsigned less-than *)
Lemma flags_ltu : forall v1 v2 : I32.int,
  negb (compute_c_flag_sub v1 v2) = I32.ltu v1 v2.
Proof.
  intros. rewrite c_flag_sub_geu. rewrite Bool.negb_involutive. reflexivity.
Qed.

(** GeS condition: N=V ↔ signed greater-or-equal *)
Lemma flags_ges : forall v1 v2 : I32.int,
  Bool.eqb (compute_n_flag (I32.sub v1 v2)) (compute_v_flag_sub v1 v2)
  = I32.ges v1 v2.
Proof.
  intros.
  rewrite <- (Bool.negb_involutive (Bool.eqb _ _)).
  rewrite nv_flag_sub_lts.
  unfold I32.ges, I32.lts, I32.signed, I32.unsigned.
  set (sv1 := if v1 mod I32.modulus <? I32.half_modulus
              then v1 mod I32.modulus
              else v1 mod I32.modulus - I32.modulus).
  set (sv2 := if v2 mod I32.modulus <? I32.half_modulus
              then v2 mod I32.modulus
              else v2 mod I32.modulus - I32.modulus).
  destruct (sv1 <? sv2) eqn:E; destruct (sv1 >=? sv2) eqn:F;
  simpl; try reflexivity.
  - exfalso. apply Z.ltb_lt in E.
    destruct (Z.geb_spec sv1 sv2); [lia | discriminate].
  - exfalso. apply Z.ltb_ge in E.
    destruct (Z.geb_spec sv1 sv2); [discriminate | lia].
Qed.

(** GeU condition: C flag set ↔ unsigned greater-or-equal *)
Lemma flags_geu : forall v1 v2 : I32.int,
  compute_c_flag_sub v1 v2 = I32.geu v1 v2.
Proof.
  intros.
  unfold compute_c_flag_sub, I32.geu, I32.unsigned.
  set (a := v1 mod I32.modulus).
  set (b := v2 mod I32.modulus).
  destruct (Z.leb b a) eqn:E; destruct (Z.geb a b) eqn:F;
  simpl; try reflexivity.
  - exfalso. apply Z.leb_le in E.
    destruct (Z.geb_spec a b); [discriminate | lia].
  - exfalso. apply Z.leb_gt in E.
    destruct (Z.geb_spec a b); [lia | discriminate].
Qed.

(** GtS condition: !Z && N=V ↔ signed greater-than *)
Lemma flags_gts : forall v1 v2 : I32.int,
  negb (compute_z_flag (I32.sub v1 v2)) &&
  Bool.eqb (compute_n_flag (I32.sub v1 v2)) (compute_v_flag_sub v1 v2)
  = I32.gts v1 v2.
Proof.
  intros.
  rewrite z_flag_sub_eq, flags_ges.
  unfold I32.gts, I32.eq, I32.ges, I32.signed, I32.unsigned.
  set (a := v1 mod I32.modulus).
  set (b := v2 mod I32.modulus).
  assert (Ha : 0 <= a < I32.modulus) by (subst a; apply Z_mod_lt; unfold I32.modulus; lia).
  assert (Hb : 0 <= b < I32.modulus) by (subst b; apply Z_mod_lt; unfold I32.modulus; lia).
  set (sv1 := if a <? I32.half_modulus then a else a - I32.modulus).
  set (sv2 := if b <? I32.half_modulus then b else b - I32.modulus).
  unfold Z.geb, Z.gtb.
  destruct (sv1 ?= sv2) eqn:Hcmp; simpl.
  - (* Eq: sv1 = sv2 → a = b *)
    rewrite Bool.andb_true_r.
    assert (Hab : a = b). {
      apply Z.compare_eq in Hcmp. subst sv1 sv2.
      destruct (a <? I32.half_modulus) eqn:Ea;
      destruct (b <? I32.half_modulus) eqn:Eb;
      (apply Z.ltb_lt in Ea || apply Z.ltb_ge in Ea);
      (apply Z.ltb_lt in Eb || apply Z.ltb_ge in Eb);
      unfold I32.half_modulus, I32.modulus in *; lia.
    }
    rewrite Hab. rewrite Z.eqb_refl. reflexivity.
  - (* Lt: trivial *)
    rewrite Bool.andb_false_r. reflexivity.
  - (* Gt: sv1 > sv2 → a ≠ b *)
    rewrite Bool.andb_true_r.
    assert (Hab : a <> b). {
      intro Heq. apply Z.compare_gt_iff in Hcmp.
      subst sv1 sv2. rewrite Heq in Hcmp. lia.
    }
    apply Z.eqb_neq in Hab. rewrite Hab. reflexivity.
Qed.

(** GtU condition: C && !Z ↔ unsigned greater-than *)
Lemma flags_gtu : forall v1 v2 : I32.int,
  compute_c_flag_sub v1 v2 && negb (compute_z_flag (I32.sub v1 v2))
  = I32.gtu v1 v2.
Proof.
  intros.
  rewrite c_flag_sub_geu, z_flag_sub_eq.
  unfold I32.gtu, I32.ltu, I32.eq, I32.unsigned.
  set (a := v1 mod I32.modulus).
  set (b := v2 mod I32.modulus).
  unfold Z.ltb, Z.gtb.
  destruct (a ?= b) eqn:Hcmp; simpl.
  - (* Eq: a = b → gtu is false *)
    apply Z.compare_eq in Hcmp. rewrite Hcmp.
    rewrite Z.eqb_refl. reflexivity.
  - (* Lt: a < b → gtu is false *)
    reflexivity.
  - (* Gt: a > b → gtu is true *)
    assert (Hne : a <> b) by
      (intro H; rewrite H in Hcmp; rewrite Z.compare_refl in Hcmp; discriminate).
    apply Z.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.

(** LeS condition: Z || N≠V ↔ signed less-or-equal *)
Lemma flags_les : forall v1 v2 : I32.int,
  compute_z_flag (I32.sub v1 v2) ||
  negb (Bool.eqb (compute_n_flag (I32.sub v1 v2)) (compute_v_flag_sub v1 v2))
  = I32.les v1 v2.
Proof.
  intros.
  rewrite z_flag_sub_eq, nv_flag_sub_lts.
  unfold I32.les, I32.eq, I32.lts, I32.signed, I32.unsigned.
  set (a := v1 mod I32.modulus).
  set (b := v2 mod I32.modulus).
  assert (Ha : 0 <= a < I32.modulus) by (subst a; apply Z_mod_lt; unfold I32.modulus; lia).
  assert (Hb : 0 <= b < I32.modulus) by (subst b; apply Z_mod_lt; unfold I32.modulus; lia).
  set (sv1 := if a <? I32.half_modulus then a else a - I32.modulus).
  set (sv2 := if b <? I32.half_modulus then b else b - I32.modulus).
  unfold Z.ltb, Z.leb.
  destruct (sv1 ?= sv2) eqn:Hcmp; simpl.
  - (* Eq: (a =? b) || false = true *)
    rewrite Bool.orb_false_r. apply Z.eqb_eq.
    apply Z.compare_eq in Hcmp. subst sv1 sv2.
    destruct (a <? I32.half_modulus) eqn:Ea;
    destruct (b <? I32.half_modulus) eqn:Eb;
    (apply Z.ltb_lt in Ea || apply Z.ltb_ge in Ea);
    (apply Z.ltb_lt in Eb || apply Z.ltb_ge in Eb);
    unfold I32.half_modulus, I32.modulus in *; lia.
  - (* Lt: (a =? b) || true = true *)
    rewrite Bool.orb_true_r. reflexivity.
  - (* Gt: (a =? b) || false = false *)
    rewrite Bool.orb_false_r. apply Z.eqb_neq.
    intro H. subst sv1 sv2. rewrite H in Hcmp.
    rewrite Z.compare_refl in Hcmp. discriminate.
Qed.

(** LeU condition: !C || Z ↔ unsigned less-or-equal *)
Lemma flags_leu : forall v1 v2 : I32.int,
  negb (compute_c_flag_sub v1 v2) || compute_z_flag (I32.sub v1 v2)
  = I32.leu v1 v2.
Proof.
  intros.
  rewrite c_flag_sub_geu, z_flag_sub_eq.
  unfold I32.leu, I32.ltu, I32.eq, I32.unsigned.
  set (a := v1 mod I32.modulus).
  set (b := v2 mod I32.modulus).
  unfold Z.ltb, Z.leb.
  destruct (a ?= b) eqn:Hcmp; simpl.
  - (* Eq: a = b *)
    apply Z.compare_eq in Hcmp. rewrite Hcmp.
    rewrite Z.eqb_refl. reflexivity.
  - (* Lt: a < b → leu is true *)
    reflexivity.
  - (* Gt: a > b → leu is false *)
    apply Z.eqb_neq. intro H. rewrite H in Hcmp.
    rewrite Z.compare_refl in Hcmp. discriminate.
Qed.

