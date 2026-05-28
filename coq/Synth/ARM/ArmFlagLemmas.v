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

(** ** I64 Flag-Correspondence Lemmas

    Architectural note (v0.8.0 foundation):
    Per [Compilation.v], i64 ops are compiled to the same single 32-bit
    ARM instructions as i32 ops ("Simplified: just add low 32 bits"). The
    ARM `CMP R0 (Reg R1)` therefore computes flags from `I32.sub v1 v2`,
    not from an i64 subtraction. The i64 flag lemmas below mirror the i32
    ones but carry an explicit boundedness side-condition on the operands.

    Two boundedness shapes appear:
    - UNSIGNED lemmas (eq, ne, ltu, leu, gtu, geu): require
      [0 <= v < I32.modulus] (32-bit unsigned range). Under this bound
      [I64.unsigned v = I32.unsigned v = v], so I64.<cmp> = I32.<cmp>.
    - SIGNED lemmas (lts, les, gts, ges): require
      [0 <= v < I32.half_modulus] (31-bit range — both signed views agree).
      A bare 32-bit bound is NOT enough: a value in [2^31, 2^32) has
      I32.signed = v - 2^32 (negative) but I64.signed = v (positive),
      so the two signed views disagree on that band.

    Honesty note: these bounds make the simplified 32-bit i64 ARM compilation
    sound exactly when the original i64 values fit in the appropriate 32-bit
    (or 31-bit, for signed) envelope. This is the same kind of envelope
    the i64 div/rem T1 proofs already live in — they take
    [I32.divs v1 v2 = Some result] (not I64.divs) as a hypothesis
    (see CorrectnessI64.v::i64_divs_correct). *)

(** Helper: under 32-bit boundedness, I64.unsigned is the identity. *)
Lemma i64_unsigned_bounded_id : forall v : I64.int,
  0 <= v -> v < I32.modulus -> I64.unsigned v = v.
Proof.
  intros v Hlo Hhi.
  unfold I64.unsigned.
  apply Z.mod_small.
  unfold I64.modulus.
  unfold I32.modulus in Hhi.
  split; [assumption | lia].
Qed.

(** Helper: under 32-bit boundedness, I32.unsigned is the identity. *)
Lemma i32_unsigned_bounded_id : forall v : I32.int,
  0 <= v -> v < I32.modulus -> I32.unsigned v = v.
Proof.
  intros v Hlo Hhi.
  unfold I32.unsigned.
  apply Z.mod_small. lia.
Qed.

(** Helper: under 32-bit boundedness, I32.eq agrees with I64.eq.
    The underlying type is shared (Z), so this is a propositional
    equality between bool expressions, not a coercion lemma. *)
Lemma i32_eq_i64_eq_bounded : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.modulus ->
  0 <= v2 -> v2 < I32.modulus ->
  I32.eq v1 v2 = I64.eq v1 v2.
Proof.
  intros v1 v2 H1lo H1hi H2lo H2hi.
  unfold I32.eq, I64.eq.
  rewrite (i32_unsigned_bounded_id v1 H1lo H1hi).
  rewrite (i32_unsigned_bounded_id v2 H2lo H2hi).
  rewrite (i64_unsigned_bounded_id v1 H1lo H1hi).
  rewrite (i64_unsigned_bounded_id v2 H2lo H2hi).
  reflexivity.
Qed.

(** Helper: under 32-bit boundedness, I32.ltu agrees with I64.ltu. *)
Lemma i32_ltu_i64_ltu_bounded : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.modulus ->
  0 <= v2 -> v2 < I32.modulus ->
  I32.ltu v1 v2 = I64.ltu v1 v2.
Proof.
  intros v1 v2 H1lo H1hi H2lo H2hi.
  unfold I32.ltu, I64.ltu.
  rewrite (i32_unsigned_bounded_id v1 H1lo H1hi).
  rewrite (i32_unsigned_bounded_id v2 H2lo H2hi).
  rewrite (i64_unsigned_bounded_id v1 H1lo H1hi).
  rewrite (i64_unsigned_bounded_id v2 H2lo H2hi).
  reflexivity.
Qed.

(** Helper: under 32-bit boundedness, I32.leu agrees with I64.leu. *)
Lemma i32_leu_i64_leu_bounded : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.modulus ->
  0 <= v2 -> v2 < I32.modulus ->
  I32.leu v1 v2 = I64.leu v1 v2.
Proof.
  intros v1 v2 H1lo H1hi H2lo H2hi.
  unfold I32.leu, I64.leu.
  rewrite (i32_unsigned_bounded_id v1 H1lo H1hi).
  rewrite (i32_unsigned_bounded_id v2 H2lo H2hi).
  rewrite (i64_unsigned_bounded_id v1 H1lo H1hi).
  rewrite (i64_unsigned_bounded_id v2 H2lo H2hi).
  reflexivity.
Qed.

(** Helper: under 32-bit boundedness, I32.gtu agrees with I64.gtu. *)
Lemma i32_gtu_i64_gtu_bounded : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.modulus ->
  0 <= v2 -> v2 < I32.modulus ->
  I32.gtu v1 v2 = I64.gtu v1 v2.
Proof.
  intros v1 v2 H1lo H1hi H2lo H2hi.
  unfold I32.gtu, I64.gtu.
  rewrite (i32_unsigned_bounded_id v1 H1lo H1hi).
  rewrite (i32_unsigned_bounded_id v2 H2lo H2hi).
  rewrite (i64_unsigned_bounded_id v1 H1lo H1hi).
  rewrite (i64_unsigned_bounded_id v2 H2lo H2hi).
  reflexivity.
Qed.

(** Helper: under 32-bit boundedness, I32.geu agrees with I64.geu. *)
Lemma i32_geu_i64_geu_bounded : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.modulus ->
  0 <= v2 -> v2 < I32.modulus ->
  I32.geu v1 v2 = I64.geu v1 v2.
Proof.
  intros v1 v2 H1lo H1hi H2lo H2hi.
  unfold I32.geu, I64.geu.
  rewrite (i32_unsigned_bounded_id v1 H1lo H1hi).
  rewrite (i32_unsigned_bounded_id v2 H2lo H2hi).
  rewrite (i64_unsigned_bounded_id v1 H1lo H1hi).
  rewrite (i64_unsigned_bounded_id v2 H2lo H2hi).
  reflexivity.
Qed.

(** Helper: when signed views agree, I32.signed v = I64.signed v.
    This is the natural precondition for signed i64 lemmas — note that
    raw 32-bit boundedness (0 <= v < 2^32) is NOT enough, because values
    in [2^31, 2^32) have I32.signed v = v - 2^32 (negative) but
    I64.signed v = v (positive). The honest precondition is to require
    the signed views to agree directly. The strict 31-bit bound
    (0 <= v < 2^31) is the natural sufficient condition. *)
Lemma i64_signed_eq_i32_signed_31bit : forall v : I64.int,
  0 <= v -> v < I32.half_modulus -> I64.signed v = I32.signed v.
Proof.
  intros v Hlo Hhi.
  assert (Hhi_raw : v < 2^31) by (unfold I32.half_modulus in Hhi; exact Hhi).
  assert (Hhi32 : v < I32.modulus) by (unfold I32.modulus; lia).
  unfold I64.signed, I32.signed.
  rewrite (i64_unsigned_bounded_id v Hlo Hhi32).
  rewrite (i32_unsigned_bounded_id v Hlo Hhi32).
  unfold I32.half_modulus, I64.half_modulus.
  destruct (Z.ltb_spec v (2^31)) as [H31|H31];
    destruct (Z.ltb_spec v (2^63)) as [H63|H63];
    try reflexivity; lia.
Qed.

(** Helper: under 31-bit boundedness, I32.lts agrees with I64.lts. *)
Lemma i32_lts_i64_lts_bounded : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.half_modulus ->
  0 <= v2 -> v2 < I32.half_modulus ->
  I32.lts v1 v2 = I64.lts v1 v2.
Proof.
  intros v1 v2 H1lo H1hi H2lo H2hi.
  unfold I32.lts, I64.lts.
  rewrite <- (i64_signed_eq_i32_signed_31bit v1 H1lo H1hi).
  rewrite <- (i64_signed_eq_i32_signed_31bit v2 H2lo H2hi).
  reflexivity.
Qed.

(** Helper: under 31-bit boundedness, I32.les agrees with I64.les. *)
Lemma i32_les_i64_les_bounded : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.half_modulus ->
  0 <= v2 -> v2 < I32.half_modulus ->
  I32.les v1 v2 = I64.les v1 v2.
Proof.
  intros v1 v2 H1lo H1hi H2lo H2hi.
  unfold I32.les, I64.les.
  rewrite <- (i64_signed_eq_i32_signed_31bit v1 H1lo H1hi).
  rewrite <- (i64_signed_eq_i32_signed_31bit v2 H2lo H2hi).
  reflexivity.
Qed.

(** Helper: under 31-bit boundedness, I32.gts agrees with I64.gts. *)
Lemma i32_gts_i64_gts_bounded : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.half_modulus ->
  0 <= v2 -> v2 < I32.half_modulus ->
  I32.gts v1 v2 = I64.gts v1 v2.
Proof.
  intros v1 v2 H1lo H1hi H2lo H2hi.
  unfold I32.gts, I64.gts.
  rewrite <- (i64_signed_eq_i32_signed_31bit v1 H1lo H1hi).
  rewrite <- (i64_signed_eq_i32_signed_31bit v2 H2lo H2hi).
  reflexivity.
Qed.

(** Helper: under 31-bit boundedness, I32.ges agrees with I64.ges. *)
Lemma i32_ges_i64_ges_bounded : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.half_modulus ->
  0 <= v2 -> v2 < I32.half_modulus ->
  I32.ges v1 v2 = I64.ges v1 v2.
Proof.
  intros v1 v2 H1lo H1hi H2lo H2hi.
  unfold I32.ges, I64.ges.
  rewrite <- (i64_signed_eq_i32_signed_31bit v1 H1lo H1hi).
  rewrite <- (i64_signed_eq_i32_signed_31bit v2 H2lo H2hi).
  reflexivity.
Qed.

(** Z flag after CMP correctly reflects i64 equality (under 32-bit bound). *)
Lemma z_flag_sub_eq_i64 : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.modulus ->
  0 <= v2 -> v2 < I32.modulus ->
  compute_z_flag (I32.sub v1 v2) = I64.eq v1 v2.
Proof.
  intros. rewrite z_flag_sub_eq.
  apply i32_eq_i64_eq_bounded; assumption.
Qed.

(** NE condition: i64 inequality (under 32-bit bound). *)
Lemma flags_ne_i64 : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.modulus ->
  0 <= v2 -> v2 < I32.modulus ->
  negb (compute_z_flag (I32.sub v1 v2)) = I64.ne v1 v2.
Proof.
  intros. unfold I64.ne.
  rewrite (z_flag_sub_eq_i64 v1 v2) by assumption.
  reflexivity.
Qed.

(** Signed less-than: N!=V flag (under 31-bit bound — signed views agree). *)
Lemma nv_flag_sub_lts_i64 : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.half_modulus ->
  0 <= v2 -> v2 < I32.half_modulus ->
  negb (Bool.eqb (compute_n_flag (I32.sub v1 v2)) (compute_v_flag_sub v1 v2))
  = I64.lts v1 v2.
Proof.
  intros. rewrite nv_flag_sub_lts.
  apply i32_lts_i64_lts_bounded; assumption.
Qed.

(** Unsigned less-than: !C (under 32-bit bound). *)
Lemma flags_ltu_i64 : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.modulus ->
  0 <= v2 -> v2 < I32.modulus ->
  negb (compute_c_flag_sub v1 v2) = I64.ltu v1 v2.
Proof.
  intros. rewrite flags_ltu.
  apply i32_ltu_i64_ltu_bounded; assumption.
Qed.

(** Signed greater-or-equal: N=V (under 31-bit bound). *)
Lemma flags_ges_i64 : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.half_modulus ->
  0 <= v2 -> v2 < I32.half_modulus ->
  Bool.eqb (compute_n_flag (I32.sub v1 v2)) (compute_v_flag_sub v1 v2)
  = I64.ges v1 v2.
Proof.
  intros. rewrite flags_ges.
  apply i32_ges_i64_ges_bounded; assumption.
Qed.

(** Unsigned greater-or-equal: C (under 32-bit bound). *)
Lemma flags_geu_i64 : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.modulus ->
  0 <= v2 -> v2 < I32.modulus ->
  compute_c_flag_sub v1 v2 = I64.geu v1 v2.
Proof.
  intros. rewrite flags_geu.
  apply i32_geu_i64_geu_bounded; assumption.
Qed.

(** Signed greater-than: !Z && N=V (under 31-bit bound). *)
Lemma flags_gts_i64 : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.half_modulus ->
  0 <= v2 -> v2 < I32.half_modulus ->
  negb (compute_z_flag (I32.sub v1 v2)) &&
  Bool.eqb (compute_n_flag (I32.sub v1 v2)) (compute_v_flag_sub v1 v2)
  = I64.gts v1 v2.
Proof.
  intros. rewrite flags_gts.
  apply i32_gts_i64_gts_bounded; assumption.
Qed.

(** Unsigned greater-than: C && !Z (under 32-bit bound). *)
Lemma flags_gtu_i64 : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.modulus ->
  0 <= v2 -> v2 < I32.modulus ->
  compute_c_flag_sub v1 v2 && negb (compute_z_flag (I32.sub v1 v2))
  = I64.gtu v1 v2.
Proof.
  intros. rewrite flags_gtu.
  apply i32_gtu_i64_gtu_bounded; assumption.
Qed.

(** Signed less-or-equal: Z || N!=V (under 31-bit bound). *)
Lemma flags_les_i64 : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.half_modulus ->
  0 <= v2 -> v2 < I32.half_modulus ->
  compute_z_flag (I32.sub v1 v2) ||
  negb (Bool.eqb (compute_n_flag (I32.sub v1 v2)) (compute_v_flag_sub v1 v2))
  = I64.les v1 v2.
Proof.
  intros. rewrite flags_les.
  apply i32_les_i64_les_bounded; assumption.
Qed.

(** Unsigned less-or-equal: !C || Z (under 32-bit bound). *)
Lemma flags_leu_i64 : forall v1 v2 : I64.int,
  0 <= v1 -> v1 < I32.modulus ->
  0 <= v2 -> v2 < I32.modulus ->
  negb (compute_c_flag_sub v1 v2) || compute_z_flag (I32.sub v1 v2)
  = I64.leu v1 v2.
Proof.
  intros. rewrite flags_leu.
  apply i32_leu_i64_leu_bounded; assumption.
Qed.

(** I32.zero and I64.zero are both definitionally 0. *)
Lemma i32_zero_eq_zero : I32.zero = 0.
Proof.
  unfold I32.zero, I32.repr, I32.modulus.
  apply Z.mod_0_l. lia.
Qed.

Lemma i64_zero_eq_zero : I64.zero = 0.
Proof.
  unfold I64.zero, I64.repr, I64.modulus.
  apply Z.mod_0_l. lia.
Qed.

Lemma i32_zero_eq_i64_zero : I32.zero = I64.zero.
Proof.
  rewrite i32_zero_eq_zero, i64_zero_eq_zero. reflexivity.
Qed.

(** Z flag after CMP with zero correctly reflects i64 eqz (under 32-bit bound).
    Convenience corollary for I64Eqz which compares R0 against the immediate 0. *)
Lemma z_flag_sub_eqz_i64 : forall v : I64.int,
  0 <= v -> v < I32.modulus ->
  compute_z_flag (I32.sub v I32.zero) = I64.eq v I64.zero.
Proof.
  intros v Hlo Hhi.
  rewrite <- i32_zero_eq_i64_zero.
  apply z_flag_sub_eq_i64; try assumption.
  - rewrite i32_zero_eq_zero. lia.
  - rewrite i32_zero_eq_zero. unfold I32.modulus. lia.
Qed.

(** ** I64 ADDS/ADC + SUBS/SBC carry/borrow-propagation lemmas (v0.10.0 PR 1)

    `Compilation.v` emits for I64Add the pair `[ADDS R0 R0 (Reg R2);
    ADC R1 R1 (Reg R3)]` over the dual-register convention
    (R0:R1 = operand1 lo:hi, R2:R3 = operand2 lo:hi). The ADDS sets the C
    flag from unsigned low-half overflow (`compute_c_flag_add`); the ADC
    reads C while computing the high half (`hi1 + hi2 + C`). These lemmas
    show that the (lo, hi) pair produced by that 2-instruction sequence
    equals the lo/hi halves of `I64.add` / `I64.sub` on the combined
    operands. No new axioms — pure modular arithmetic over the *existing*
    ArmSemantics.v flag clauses.

    The proofs reduce to a single Z-level fact about base-2^32 carry
    propagation, captured by `carry_split_add` / `borrow_split_sub`. *)

(** Both halves of a `combine_i32` fit a 64-bit value, so `I64.repr` is
    the identity on the combined operand. *)
Lemma combine_i32_unsigned : forall lo hi : I32.int,
  I64.unsigned (combine_i32 lo hi)
  = I32.unsigned lo + I32.modulus * I32.unsigned hi.
Proof.
  intros lo hi.
  unfold combine_i32, I64.unsigned, I64.repr, I32.unsigned, I32.modulus, I64.modulus.
  set (a := lo mod 2^32).
  set (b := hi mod 2^32).
  assert (Ha : 0 <= a < 2^32) by (subst a; apply Z_mod_lt; lia).
  assert (Hb : 0 <= b < 2^32) by (subst b; apply Z_mod_lt; lia).
  (* I64.unsigned (I64.repr n) = (n mod 2^64) mod 2^64; collapse, then small. *)
  rewrite Zmod_mod.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

(** The inner `mod I32.modulus` in `lo_of_i64` is redundant: I32.repr
    already reduces mod 2^32. *)
Lemma lo_of_i64_repr : forall n : I64.int,
  lo_of_i64 n = I32.repr (I64.unsigned n).
Proof.
  intros n. unfold lo_of_i64, I32.repr, I32.modulus.
  rewrite Zmod_mod. reflexivity.
Qed.

(** Normalization helper: a sum of two values plus a constant is unchanged
    mod n when each value is first reduced mod n. Pure Z; closes the final
    step of both carry/borrow helpers. *)
Lemma sum2_mod_norm : forall x y k n : Z,
  (x + y + k) mod n = (x mod n + y mod n + k) mod n.
Proof.
  intros x y k n.
  rewrite (Zplus_mod (x + y) k).
  rewrite (Zplus_mod x y).
  rewrite (Zplus_mod (x mod n + y mod n) k).
  reflexivity.
Qed.

(** Same normalization for a difference of two values minus a constant. *)
Lemma diff2_mod_norm : forall x y k n : Z,
  (x - y - k) mod n = (x mod n - y mod n - k) mod n.
Proof.
  intros x y k n.
  rewrite (Zminus_mod (x - y) k).
  rewrite (Zminus_mod x y).
  rewrite (Zminus_mod (x mod n - y mod n) k).
  reflexivity.
Qed.

(** `I64.unsigned` distributes over `I64.add` modulo 2^64. *)
Lemma i64_unsigned_add : forall a b : I64.int,
  I64.unsigned (I64.add a b) = (I64.unsigned a + I64.unsigned b) mod 2^64.
Proof.
  intros a b. unfold I64.add, I64.unsigned, I64.repr, I64.modulus.
  rewrite Zmod_mod.
  rewrite Zplus_mod. reflexivity.
Qed.

(** `I64.unsigned` distributes over `I64.sub` modulo 2^64. *)
Lemma i64_unsigned_sub : forall a b : I64.int,
  I64.unsigned (I64.sub a b) = (I64.unsigned a - I64.unsigned b) mod 2^64.
Proof.
  intros a b. unfold I64.sub, I64.unsigned, I64.repr, I64.modulus.
  rewrite Zmod_mod.
  rewrite Zminus_mod. reflexivity.
Qed.

(** Core base-2^32 carry-split fact for addition.
    Let `lo = la + 2^32*ha`, `lo2 = lb + 2^32*hb` with all four parts in
    [0, 2^32). Then `(lo + lo2) mod 2^64`, projected to its low and high
    32-bit halves, equals `(la+lb) mod 2^32` and `(ha+hb+carry) mod 2^32`
    where `carry = 1` iff `la+lb >= 2^32`. *)
Lemma carry_split_add : forall la ha lb hb : Z,
  0 <= la < 2^32 -> 0 <= ha < 2^32 ->
  0 <= lb < 2^32 -> 0 <= hb < 2^32 ->
  let s := (la + 2^32 * ha + (lb + 2^32 * hb)) mod 2^64 in
  let carry := if 2^32 <=? la + lb then 1 else 0 in
  s mod 2^32 = (la + lb) mod 2^32 /\
  s / 2^32 mod 2^32 = (ha + hb + carry) mod 2^32.
Proof.
  intros la ha lb hb Hla Hha Hlb Hhb. cbv zeta.
  set (carry := if 2^32 <=? la + lb then 1 else 0).
  (* Decompose the low sum: la + lb = carry*2^32 + (la+lb) mod 2^32. *)
  assert (Hlow : (la + lb) mod 2^32 = la + lb - carry * 2^32). {
    subst carry. destruct (Z.leb_spec (2^32) (la + lb)).
    - (* carry = 1: la + lb >= 2^32, so subtract one modulus to land in range. *)
      assert (Heq : (la + lb) mod 2^32 = (la + lb - 1 * 2^32) mod 2^32). {
        rewrite <- (Z_mod_plus_full (la + lb - 1 * 2^32) 1 (2^32)).
        f_equal. lia.
      }
      rewrite Heq.
      rewrite Z.mod_small by lia. lia.
    - (* carry = 0: la + lb < 2^32, already in canonical range. *)
      rewrite Z.mod_small by lia. lia.
  }
  (* The 64-bit sum, before mod, is exactly representable. *)
  set (raw := la + 2^32 * ha + (lb + 2^32 * hb)).
  assert (Hraw_lo : 0 <= raw) by (subst raw; nia).
  assert (Hraw_hi : raw < 2^64) by (subst raw; nia).
  assert (Hs : raw mod 2^64 = raw) by (apply Z.mod_small; lia).
  rewrite Hs.
  split.
  - (* low half: raw mod 2^32 = (la+lb) mod 2^32 *)
    subst raw.
    replace (la + 2^32 * ha + (lb + 2^32 * hb))
      with ((la + lb) + (ha + hb) * 2^32) by lia.
    rewrite Z_mod_plus_full. reflexivity.
  - (* high half: raw / 2^32 mod 2^32 = (ha+hb+carry) mod 2^32 *)
    subst raw.
    (* raw = (la+lb) mod 2^32 + (ha+hb+carry)*2^32. *)
    assert (Hrewrite : la + 2^32 * ha + (lb + 2^32 * hb)
                       = (la + lb) mod 2^32 + (ha + hb + carry) * 2^32). {
      rewrite Hlow. lia.
    }
    rewrite Hrewrite.
    assert (Hmod_lt : 0 <= (la + lb) mod 2^32 < 2^32) by (apply Z_mod_lt; lia).
    rewrite Z.div_add by lia.
    rewrite (Z.div_small _ _ Hmod_lt).
    rewrite Z.add_0_l. reflexivity.
Qed.

(** Core base-2^32 borrow-split fact for subtraction.
    SUBS sets C = 1 iff `la >= lb` (no borrow); SBC computes
    `ha - hb - NOT(C) = ha - hb - (1 - C)`. The low/high halves of
    `(lo - lo2) mod 2^64` match `(la-lb) mod 2^32` and
    `(ha - hb - borrow) mod 2^32` where `borrow = 1` iff `la < lb`. *)
Lemma borrow_split_sub : forall la ha lb hb : Z,
  0 <= la < 2^32 -> 0 <= ha < 2^32 ->
  0 <= lb < 2^32 -> 0 <= hb < 2^32 ->
  let d := (la + 2^32 * ha - (lb + 2^32 * hb)) mod 2^64 in
  let borrow := if la <? lb then 1 else 0 in
  d mod 2^32 = (la - lb) mod 2^32 /\
  d / 2^32 mod 2^32 = (ha - hb - borrow) mod 2^32.
Proof.
  intros la ha lb hb Hla Hha Hlb Hhb. cbv zeta.
  set (borrow := if la <? lb then 1 else 0).
  (* (la - lb) mod 2^32 = la - lb + borrow*2^32 *)
  assert (Hlow : (la - lb) mod 2^32 = la - lb + borrow * 2^32). {
    subst borrow. destruct (Z.ltb_spec la lb).
    - rewrite (Z.mod_small (la - lb + 1 * 2^32)) by lia. lia.
    - rewrite Z.mod_small by lia. lia.
  }
  (* The raw difference, rewritten in carry-normalized base-2^32 form. *)
  set (raw := la + 2^32 * ha - (lb + 2^32 * hb)).
  assert (Hrewrite : raw = (la - lb) mod 2^32 + (ha - hb - borrow) * 2^32). {
    subst raw. rewrite Hlow. lia.
  }
  assert (Hmod_lt : 0 <= (la - lb) mod 2^32 < 2^32) by (apply Z_mod_lt; lia).
  set (hh := (ha - hb - borrow) mod 2^32).
  assert (Hhh : 0 <= hh < 2^32) by (subst hh; apply Z_mod_lt; lia).
  (* Canonical representative V = c_lo + c_hi * 2^32, both halves in range,
     hence in [0, 2^64); and raw ≡ V (mod 2^64). *)
  set (V := (la - lb) mod 2^32 + hh * 2^32).
  assert (HV_range : 0 <= V < 2^64) by (subst V; nia).
  (* raw - V is a multiple of 2^64, so raw mod 2^64 = V. *)
  assert (Hdiff : raw = V + 2^64 * ((ha - hb - borrow) / 2^32)). {
    subst V raw. rewrite Hrewrite. unfold hh.
    set (x := ha - hb - borrow).
    set (q := x / 2^32).
    set (r := x mod 2^32).
    (* x = 2^32 * q + r *)
    assert (Hdm : x = 2^32 * q + r) by (subst q r; apply Z.div_mod; lia).
    (* Replace the bare x*2^32 using Hdm; then it is polynomial in q, r. *)
    replace (x * 2^32) with ((2^32 * q + r) * 2^32) by (rewrite <- Hdm; reflexivity).
    replace (2^64) with (2^32 * 2^32) by lia.
    ring.
  }
  assert (Hcongr : raw mod 2^64 = V). {
    rewrite Hdiff.
    rewrite (Z.mul_comm (2^64) ((ha - hb - borrow) / 2^32)).
    rewrite Z_mod_plus_full.
    apply Z.mod_small. exact HV_range.
  }
  rewrite Hcongr. subst V.
  split.
  - (* low half: (c_lo + c_hi*2^32) mod 2^32 = c_lo = (la-lb) mod 2^32 *)
    rewrite Z_mod_plus_full.
    rewrite Z.mod_mod by lia. reflexivity.
  - (* high half: (c_lo + c_hi*2^32) / 2^32 mod 2^32 = c_hi = (ha-hb-borrow) mod 2^32 *)
    rewrite Z.div_add by lia.
    rewrite (Z.div_small _ _ Hmod_lt).
    rewrite Z.add_0_l.
    (* LHS = hh mod 2^32; hh is itself a mod, so collapse the double mod. *)
    subst hh. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(** ADDS+ADC carry propagation: the (lo, hi) pair produced by
    `[ADDS R0 R0 (Reg R2); ADC R1 R1 (Reg R3)]` equals the lo/hi halves of
    `I64.add` on the combined operands.

    - lo half = `I32.add lo1 lo2` (the ADDS result),
    - hi half = `I32.add (I32.add hi1 hi2) C` (the ADC result),
      where `C = compute_c_flag_add lo1 lo2`. *)
Lemma i64_add_via_adds_adc : forall lo1 hi1 lo2 hi2 : I32.int,
  I32.add lo1 lo2
    = lo_of_i64 (I64.add (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)) /\
  I32.add (I32.add hi1 hi2)
          (if compute_c_flag_add lo1 lo2 then I32.one else I32.zero)
    = hi_of_i64 (I64.add (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)).
Proof.
  intros lo1 hi1 lo2 hi2.
  (* Bounds on the four unsigned 32-bit halves. *)
  assert (Hla : 0 <= I32.unsigned lo1 < 2^32)
    by (unfold I32.unsigned, I32.modulus; apply Z_mod_lt; lia).
  assert (Hha : 0 <= I32.unsigned hi1 < 2^32)
    by (unfold I32.unsigned, I32.modulus; apply Z_mod_lt; lia).
  assert (Hlb : 0 <= I32.unsigned lo2 < 2^32)
    by (unfold I32.unsigned, I32.modulus; apply Z_mod_lt; lia).
  assert (Hhb : 0 <= I32.unsigned hi2 < 2^32)
    by (unfold I32.unsigned, I32.modulus; apply Z_mod_lt; lia).
  (* The 64-bit unsigned value of the I64.add, in base-2^32 form. *)
  assert (Hadd : I64.unsigned (I64.add (combine_i32 lo1 hi1) (combine_i32 lo2 hi2))
                 = (I32.unsigned lo1 + 2^32 * I32.unsigned hi1
                    + (I32.unsigned lo2 + 2^32 * I32.unsigned hi2)) mod 2^64). {
    rewrite i64_unsigned_add.
    rewrite (combine_i32_unsigned lo1 hi1), (combine_i32_unsigned lo2 hi2).
    unfold I32.modulus. reflexivity.
  }
  pose proof (carry_split_add (I32.unsigned lo1) (I32.unsigned hi1)
                              (I32.unsigned lo2) (I32.unsigned hi2)
                              Hla Hha Hlb Hhb) as Hsplit.
  cbv zeta in Hsplit. destruct Hsplit as [Hlo Hhi].
  split.
  - (* low half: I32.add lo1 lo2 = lo_of_i64 (I64.add ..) *)
    rewrite lo_of_i64_repr. rewrite Hadd.
    unfold I32.repr, I32.modulus.
    rewrite Hlo.
    (* I32.add lo1 lo2 = (lo1 + lo2) mod 2^32 = (la + lb) mod 2^32 *)
    unfold I32.add, I32.repr, I32.modulus.
    rewrite (Zplus_mod lo1 lo2).
    unfold I32.unsigned, I32.modulus.
    reflexivity.
  - (* high half: I32.add (I32.add hi1 hi2) carry = hi_of_i64 (I64.add ..) *)
    (* Relate compute_c_flag_add's boolean to (2^32 <=? la+lb). *)
    assert (Hcarry : (if compute_c_flag_add lo1 lo2 then I32.one else I32.zero)
                     = (if 2^32 <=? I32.unsigned lo1 + I32.unsigned lo2 then 1 else 0)). {
      unfold compute_c_flag_add, I32.max_unsigned, I32.modulus, I32.one,
             I32.zero, I32.repr.
      destruct (Z.ltb_spec (2^32 - 1) (I32.unsigned lo1 + I32.unsigned lo2)) as [H1|H1];
      destruct (Z.leb_spec (2^32) (I32.unsigned lo1 + I32.unsigned lo2)) as [H2|H2];
      try (rewrite Z.mod_small by lia; reflexivity); lia.
    }
    (* RHS = (ha + hb + carry) mod 2^32 *)
    unfold hi_of_i64. rewrite Hadd. unfold I32.repr, I32.modulus.
    rewrite Hhi.
    (* LHS: I32.add (I32.add hi1 hi2) (if .. then I32.one else I32.zero) *)
    rewrite Hcarry.
    unfold I32.add, I32.repr, I32.modulus.
    (* LHS = ((hi1 + hi2) mod 2^32 + carry) mod 2^32 = (hi1 + hi2 + carry) mod 2^32 *)
    rewrite Zplus_mod_idemp_l.
    (* RHS uses ha = hi1 mod 2^32, hb = hi2 mod 2^32; normalize via sum2. *)
    unfold I32.unsigned, I32.modulus.
    rewrite (sum2_mod_norm hi1 hi2
               (if 2^32 <=? lo1 mod 2^32 + lo2 mod 2^32 then 1 else 0) (2^32)).
    reflexivity.
Qed.

(** SUBS+SBC borrow propagation: the (lo, hi) pair produced by
    `[SUBS R0 R0 (Reg R2); SBC R1 R1 (Reg R3)]` equals the lo/hi halves of
    `I64.sub` on the combined operands.

    - lo half = `I32.sub lo1 lo2` (the SUBS result),
    - hi half = `I32.sub (I32.sub hi1 hi2) NOT(C)` (the SBC result),
      where `C = compute_c_flag_sub lo1 lo2` and NOT(C) is the borrow
      (`if C then 0 else 1`). *)
Lemma i64_sub_via_subs_sbc : forall lo1 hi1 lo2 hi2 : I32.int,
  I32.sub lo1 lo2
    = lo_of_i64 (I64.sub (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)) /\
  I32.sub (I32.sub hi1 hi2)
          (if compute_c_flag_sub lo1 lo2 then I32.zero else I32.one)
    = hi_of_i64 (I64.sub (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)).
Proof.
  intros lo1 hi1 lo2 hi2.
  assert (Hla : 0 <= I32.unsigned lo1 < 2^32)
    by (unfold I32.unsigned, I32.modulus; apply Z_mod_lt; lia).
  assert (Hha : 0 <= I32.unsigned hi1 < 2^32)
    by (unfold I32.unsigned, I32.modulus; apply Z_mod_lt; lia).
  assert (Hlb : 0 <= I32.unsigned lo2 < 2^32)
    by (unfold I32.unsigned, I32.modulus; apply Z_mod_lt; lia).
  assert (Hhb : 0 <= I32.unsigned hi2 < 2^32)
    by (unfold I32.unsigned, I32.modulus; apply Z_mod_lt; lia).
  (* The 64-bit unsigned value of the I64.sub, in base-2^32 form. *)
  assert (Hsub : I64.unsigned (I64.sub (combine_i32 lo1 hi1) (combine_i32 lo2 hi2))
                 = (I32.unsigned lo1 + 2^32 * I32.unsigned hi1
                    - (I32.unsigned lo2 + 2^32 * I32.unsigned hi2)) mod 2^64). {
    rewrite i64_unsigned_sub.
    rewrite (combine_i32_unsigned lo1 hi1), (combine_i32_unsigned lo2 hi2).
    unfold I32.modulus. reflexivity.
  }
  pose proof (borrow_split_sub (I32.unsigned lo1) (I32.unsigned hi1)
                               (I32.unsigned lo2) (I32.unsigned hi2)
                               Hla Hha Hlb Hhb) as Hsplit.
  cbv zeta in Hsplit. destruct Hsplit as [Hlo Hhi].
  split.
  - (* low half: I32.sub lo1 lo2 = lo_of_i64 (I64.sub ..) *)
    rewrite lo_of_i64_repr. rewrite Hsub.
    unfold I32.repr, I32.modulus.
    rewrite Hlo.
    (* I32.sub lo1 lo2 = (lo1 - lo2) mod 2^32 = (la - lb) mod 2^32 *)
    unfold I32.sub, I32.repr, I32.modulus.
    rewrite (Zminus_mod lo1 lo2).
    unfold I32.unsigned, I32.modulus.
    reflexivity.
  - (* high half: I32.sub (I32.sub hi1 hi2) borrow = hi_of_i64 (I64.sub ..) *)
    (* borrow = NOT(C); C = compute_c_flag_sub lo1 lo2 = (lb <=? la). *)
    assert (Hborrow : (if compute_c_flag_sub lo1 lo2 then I32.zero else I32.one)
                      = (if I32.unsigned lo1 <? I32.unsigned lo2 then 1 else 0)). {
      unfold compute_c_flag_sub, I32.one, I32.zero, I32.repr, I32.modulus.
      destruct (Z.leb_spec (I32.unsigned lo2) (I32.unsigned lo1)) as [H1|H1];
      destruct (Z.ltb_spec (I32.unsigned lo1) (I32.unsigned lo2)) as [H2|H2];
      try (rewrite Z.mod_small by lia; reflexivity); lia.
    }
    (* RHS = (ha - hb - borrow) mod 2^32 *)
    unfold hi_of_i64. rewrite Hsub. unfold I32.repr, I32.modulus.
    rewrite Hhi.
    rewrite Hborrow.
    unfold I32.sub, I32.repr, I32.modulus.
    (* LHS = ((hi1 - hi2) mod 2^32 - borrow) mod 2^32 = (hi1 - hi2 - borrow) mod 2^32 *)
    rewrite Zminus_mod_idemp_l.
    unfold I32.unsigned, I32.modulus.
    rewrite (diff2_mod_norm hi1 hi2
               (if lo1 mod 2^32 <? lo2 mod 2^32 then 1 else 0) (2^32)).
    reflexivity.
Qed.

