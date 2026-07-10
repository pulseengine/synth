(** * VCR-SEL-001 — expansion-level T1 for the binary I64SetCond family

    Increment 4 (docs/design/vcr-sel-001-increment-4.md) proved the ten
    binary i64 comparison rules at PSEUDO-OP tier: each theorem discharges
    against the [i64_setcond_bits_spec] AXIOM, because the encoder's
    dual-precision expansion below the [ArmOp] boundary needed three
    executor capabilities the flat model lacked — SBCS (a flags-WRITING
    subtract-with-carry), conditionally-executed flags-writers (CMPEQ),
    and three-operand borrow-aware C/V helpers.

    This file is the upgrade those capabilities unlock (epic #242): the
    encoder's actual expansion chains, transcribed from
    [crates/synth-backend/src/arm_encoder.rs] (ArmOp::I64SetCond, A32 arm;
    the Thumb-2 arm emits the same chain shape), proven to compute the
    WASM-spec 0/1 result WITHOUT the [i64_setcond_bits] axiom:

      - ordered (LT/GE/LO/HS):  CMP lo,lo; SBCS rd,hi,hi; MOV<cond> rd,#1;
                                MOV<inv> rd,#0
      - swapped (GT/LE/HI/LS):  the same chain on the SWAPPED operand pairs,
        testing the LT/GE/LO/HS complement — the encoder's operand-swap
        condition mapping, proven correct here via the comparison-flip
        identities (gts a b = lts b a, etc.);
      - EQ/NE:                  CMP lo,lo; CMPEQ hi,hi; MOV<cond> rd,#1;
                                MOV<inv> rd,#0 (compare highs only if lows
                                equal — the conditional flags-writer).

    [set_cond] in the encoder emits MOV<cond> rd,#1 THEN MOV<inv cond> rd,#0
    — that exact order is modeled.

    The flag math is NOT invented here: the SBCS semantics is anchored to
    the ASL AddWithCarry transcription in SailArmBridge.v
    ([sail_bridge_sbcs_reg]); this file only proves the CHAIN lemmas — that
    the borrow threaded from the low-half CMP into the high-half SBCS makes
    the final NZCV reflect the 64-bit comparison:

      - [pair_cmp_sbcs_nv_lts] : N<>V after the chain  <->  I64.lts
      - [pair_cmp_sbcs_c_geu]  : C   after the chain  <->  I64.geu
      - [pair_cmp_cmpeq_z_eq]  : Z   after the chain  <->  I64.eq

    Aliasing: no side conditions. CMP/CMPEQ write no register; SBCS reads
    rn_hi/rm_hi before writing rd; the MOVcc pair writes only rd. So the
    universal register quantification admits every aliasing — including
    select_default's in-place rd = rn_lo = R0.

    T1 bound as everywhere in VcrSelRules.v: "the ARM sequence computes the
    named result", not WASM refinement. The rule-tier theorems
    ([rule_i64_lt_s_correct] etc.) remain the coverage-gated obligations of
    the DSL table; these expansion theorems hang BELOW them, closing the
    selector-emission -> encoder-expansion gap for this family. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.
Require Import Synth.ARM.ArmSemantics.
Require Import Synth.ARM.ArmFlagLemmas.
Require Import Synth.ARM.SailArmBridge.

Import ListNotations.
Open Scope Z_scope.

(** ** Arithmetic infrastructure *)

(** The signed view of any i32 lands in [-2^31, 2^31). *)
Lemma i32_signed_range : forall x : I32.int,
  - I32.half_modulus <= I32.signed x < I32.half_modulus.
Proof.
  intros. unfold I32.signed. cbv zeta.
  pose proof (unsigned_range x) as H.
  assert (HMH : I32.modulus = 2 * I32.half_modulus) by reflexivity.
  assert (HH : 0 < I32.half_modulus) by (rewrite half_modulus_val; lia).
  destruct (Z.ltb_spec (I32.unsigned x) I32.half_modulus); lia.
Qed.

(** The core N-xor-V fact for a borrow-aware subtract: after
    [SBCS r, hi1, hi2] with carry-in [cin], N <> V holds iff the EXACT
    (unwrapped) signed difference [signed hi1 - signed hi2 - borrow] is
    negative. This is the classic "signed less-than via N != V" argument,
    made borrow-aware; V's definition ("32-bit result differs from the
    exact difference") is what makes it provable rather than axiomatic. *)
Lemma nv_sbc_exact : forall (hi1 hi2 : I32.int) (cin : bool),
  negb (Bool.eqb
          (compute_n_flag (I32.sub (I32.sub hi1 hi2)
                             (if cin then I32.zero else I32.one)))
          (compute_v_flag_sbc hi1 hi2 cin))
  = (I32.signed hi1 - I32.signed hi2 - (if cin then 0 else 1) <? 0).
Proof.
  intros.
  set (r := I32.sub (I32.sub hi1 hi2) (if cin then I32.zero else I32.one)).
  set (ex := I32.signed hi1 - I32.signed hi2 - (if cin then 0 else 1)).
  assert (HV : compute_v_flag_sbc hi1 hi2 cin = negb (I32.signed r =? ex))
    by reflexivity.
  (* signed r and the exact difference are congruent mod 2^32 *)
  assert (Hcong : I32.signed r mod I32.modulus = ex mod I32.modulus).
  { rewrite signed_mod_modulus. unfold r.
    rewrite unsigned_sbc_result.
    unfold ex.
    rewrite <- (mod3_sub (I32.signed hi1) (I32.signed hi2)
                  (if cin then 0 else 1)).
    rewrite !signed_mod_modulus.
    reflexivity. }
  assert (HM : I32.modulus = 4294967296) by apply modulus_val.
  assert (HH : I32.half_modulus = 2147483648) by apply half_modulus_val.
  assert (Hsr : - I32.half_modulus <= I32.signed r < I32.half_modulus)
    by apply i32_signed_range.
  assert (Hex : - I32.modulus <= ex < I32.modulus).
  { pose proof (i32_signed_range hi1). pose proof (i32_signed_range hi2).
    unfold ex. destruct cin; lia. }
  (* both in (-2^32, 2^32) and congruent: they differ by -M, 0 or +M *)
  assert (Hdisj : I32.signed r = ex \/ I32.signed r = ex + I32.modulus
                  \/ I32.signed r = ex - I32.modulus).
  { assert (Hd0 : (I32.signed r - ex) mod I32.modulus = 0).
    { rewrite Zminus_mod, Hcong, Z.sub_diag.
      apply Z.mod_0_l. apply modulus_nz. }
    apply Z.mod_divide in Hd0; [| apply modulus_nz].
    destruct Hd0 as [k Hk].
    rewrite HM in Hk.
    assert (Hkb : k = 0 \/ k = 1 \/ k = -1) by lia.
    destruct Hkb as [K | [K | K]]; rewrite K in Hk;
      [left | right; left | right; right]; lia. }
  rewrite HV.
  unfold compute_n_flag.
  destruct (Z.eqb_spec (I32.signed r) ex) as [He | Hne].
  - (* V clear: N is the sign of the exact difference *)
    rewrite He. cbn [negb].
    destruct (ex <? 0); reflexivity.
  - (* V set: the exact difference wrapped; N flips *)
    cbn [negb].
    destruct Hdisj as [K | [K | K]]; [contradiction | |];
      destruct (Z.ltb_spec (I32.signed r) 0) as [L1 | L1];
      destruct (Z.ltb_spec ex 0) as [L2 | L2];
      cbn [Bool.eqb negb]; try reflexivity; exfalso; lia.
Qed.

(** The signed view of a register pair: unsigned low half plus 2^32 times
    the SIGNED high half. *)
Lemma combine_i32_signed : forall lo hi : I32.int,
  I64.signed (combine_i32 lo hi)
  = I32.unsigned lo + I32.modulus * I32.signed hi.
Proof.
  intros. unfold I64.signed. cbv zeta.
  rewrite combine_i32_unsigned.
  pose proof (unsigned_range lo) as Hlo.
  pose proof (unsigned_range hi) as Hhi.
  assert (HM : I32.modulus = 4294967296) by apply modulus_val.
  assert (HH : I32.half_modulus = 2147483648) by apply half_modulus_val.
  assert (HM64 : I64.modulus = 18446744073709551616) by reflexivity.
  assert (HH64 : I64.half_modulus = 9223372036854775808) by reflexivity.
  unfold I32.signed. cbv zeta.
  rewrite HM, HH, HM64, HH64 in *.
  destruct (Z.ltb_spec (I32.unsigned lo + 4294967296 * I32.unsigned hi)
              9223372036854775808) as [L | L];
    destruct (Z.ltb_spec (I32.unsigned hi) 2147483648) as [Lh | Lh]; lia.
Qed.

(** ** The three chain lemmas — final flags of the dual-precision compare *)

(** N <> V after [CMP lo1, lo2; SBCS _, hi1, hi2]  <->  64-bit signed <. *)
Lemma pair_cmp_sbcs_nv_lts : forall lo1 hi1 lo2 hi2 : I32.int,
  negb (Bool.eqb
          (compute_n_flag
             (I32.sub (I32.sub hi1 hi2)
                (if compute_c_flag_sub lo1 lo2 then I32.zero else I32.one)))
          (compute_v_flag_sbc hi1 hi2 (compute_c_flag_sub lo1 lo2)))
  = I64.lts (combine_i32 lo1 hi1) (combine_i32 lo2 hi2).
Proof.
  intros.
  rewrite nv_sbc_exact.
  unfold I64.lts.
  rewrite !combine_i32_signed.
  unfold compute_c_flag_sub.
  pose proof (unsigned_range lo1). pose proof (unsigned_range lo2).
  pose proof (i32_signed_range hi1). pose proof (i32_signed_range hi2).
  assert (HM : I32.modulus = 4294967296) by apply modulus_val.
  assert (HH : I32.half_modulus = 2147483648) by apply half_modulus_val.
  rewrite HM in *. rewrite HH in *.
  destruct (Z.leb_spec (I32.unsigned lo2) (I32.unsigned lo1)) as [Hb | Hb];
    bool_blast.
Qed.

(** C after [CMP lo1, lo2; SBCS _, hi1, hi2]  <->  64-bit unsigned >=. *)
Lemma pair_cmp_sbcs_c_geu : forall lo1 hi1 lo2 hi2 : I32.int,
  compute_c_flag_sbc hi1 hi2 (compute_c_flag_sub lo1 lo2)
  = I64.geu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2).
Proof.
  intros.
  unfold compute_c_flag_sbc, compute_c_flag_sub, I64.geu. cbv zeta.
  rewrite !combine_i32_unsigned.
  rewrite Z.geb_leb.
  pose proof (unsigned_range lo1). pose proof (unsigned_range lo2).
  pose proof (unsigned_range hi1). pose proof (unsigned_range hi2).
  assert (HM : I32.modulus = 4294967296) by apply modulus_val.
  rewrite HM in *.
  destruct (Z.leb_spec (I32.unsigned lo2) (I32.unsigned lo1)) as [Hb | Hb];
    bool_blast.
Qed.

(** Z after [CMP lo1, lo2; CMPEQ hi1, hi2]  <->  64-bit equality.
    The conditional compare leaves the low-half Z (false) in place when the
    lows differ; otherwise the final Z is the high-half equality. *)
Lemma pair_cmp_cmpeq_z_eq : forall lo1 hi1 lo2 hi2 : I32.int,
  (if compute_z_flag (I32.sub lo1 lo2)
   then compute_z_flag (I32.sub hi1 hi2)
   else false)
  = I64.eq (combine_i32 lo1 hi1) (combine_i32 lo2 hi2).
Proof.
  intros.
  rewrite !z_flag_sub_eq.
  unfold I32.eq, I64.eq.
  rewrite !combine_i32_unsigned.
  pose proof (unsigned_range lo1). pose proof (unsigned_range lo2).
  pose proof (unsigned_range hi1). pose proof (unsigned_range hi2).
  assert (HM : I32.modulus = 4294967296) by apply modulus_val.
  rewrite HM in *.
  destruct (Z.eqb_spec (I32.unsigned lo1) (I32.unsigned lo2)) as [E | E];
    bool_blast.
Qed.

(** ** Comparison-flip identities — the operand-swap condition mapping *)

Lemma i64_gts_lts_swap : forall a b, I64.gts a b = I64.lts b a.
Proof. intros. unfold I64.gts, I64.lts. apply Z.gtb_ltb. Qed.

Lemma i64_ges_negb_lts : forall a b, I64.ges a b = negb (I64.lts a b).
Proof.
  intros. unfold I64.ges, I64.lts.
  rewrite Z.geb_leb. apply Z.leb_antisym.
Qed.

Lemma i64_les_negb_lts_swap : forall a b, I64.les a b = negb (I64.lts b a).
Proof. intros. unfold I64.les, I64.lts. apply Z.leb_antisym. Qed.

Lemma i64_ltu_negb_geu : forall a b, I64.ltu a b = negb (I64.geu a b).
Proof.
  intros. unfold I64.ltu, I64.geu.
  rewrite Z.geb_leb. apply Z.ltb_antisym.
Qed.

Lemma i64_gtu_negb_geu_swap : forall a b, I64.gtu a b = negb (I64.geu b a).
Proof.
  intros. unfold I64.gtu, I64.geu.
  rewrite Z.geb_leb, Z.gtb_ltb. apply Z.ltb_antisym.
Qed.

Lemma i64_leu_geu_swap : forall a b, I64.leu a b = I64.geu b a.
Proof. intros. unfold I64.leu, I64.geu. rewrite Z.geb_leb. reflexivity. Qed.

Lemma i64_ne_negb_eq : forall a b, I64.ne a b = negb (I64.eq a b).
Proof. intros. reflexivity. Qed.

(** ** The chain shapes

    One lemma per (final-condition) shape, quantified over the operand
    registers in the order they are COMPARED (a = first, b = second); the
    per-op theorems below instantiate them in rule order (LT/GE/LO/HS/EQ/NE)
    or swapped (GT/LE/HI/LS). Encoder order: MOV<cond> rd,#1 then
    MOV<inv> rd,#0. *)

(** The six chain programs (encoder transcriptions). Named definitions —
    also keeps the list literals out of theorem-statement term positions,
    where Base.v's map-update notation would shadow list notation. *)

Definition chain_sbcs_lt (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [CMP rnlo (Reg rmlo); SBCS rd rnhi (Reg rmhi);
   MOVLT rd (Imm I32.one); MOVGE rd (Imm I32.zero)].

Definition chain_sbcs_ge (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [CMP rnlo (Reg rmlo); SBCS rd rnhi (Reg rmhi);
   MOVGE rd (Imm I32.one); MOVLT rd (Imm I32.zero)].

Definition chain_sbcs_lo (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [CMP rnlo (Reg rmlo); SBCS rd rnhi (Reg rmhi);
   MOVLO rd (Imm I32.one); MOVHS rd (Imm I32.zero)].

Definition chain_sbcs_hs (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [CMP rnlo (Reg rmlo); SBCS rd rnhi (Reg rmhi);
   MOVHS rd (Imm I32.one); MOVLO rd (Imm I32.zero)].

Definition chain_cmpeq_eq (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [CMP rnlo (Reg rmlo); CMPCond Cond_EQ rnhi (Reg rmhi);
   MOVEQ rd (Imm I32.one); MOVNE rd (Imm I32.zero)].

Definition chain_cmpeq_ne (rd rnlo rnhi rmlo rmhi : arm_reg) : arm_program :=
  [CMP rnlo (Reg rmlo); CMPCond Cond_EQ rnhi (Reg rmhi);
   MOVNE rd (Imm I32.one); MOVEQ rd (Imm I32.zero)].

(** Normalization of the first two (unconditional) links: unfold the
    chain, reduce the executor matches, push flag/register reads through
    set_reg/set_flags, substitute the operand hypotheses. The MOVcc links
    stay stuck (their conditions sit under the executor's match binders)
    and are resolved per branch by [setcond_branch_normalize]. *)
Ltac setcond_chain_normalize H1 H2 H3 H4 :=
  unfold chain_sbcs_lt, chain_sbcs_ge, chain_sbcs_lo, chain_sbcs_hs,
         chain_cmpeq_eq, chain_cmpeq_ne;
  cbn [exec_program exec_instr eval_operand2 eval_condition];
  repeat first [ rewrite !set_reg_preserves_flags
               | rewrite !flags_set_flags ];
  rewrite !get_reg_set_flags;
  rewrite ?flag_n_update_flags_arith, ?flag_z_update_flags_arith,
          ?flag_v_update_flags_arith, ?flag_c_update_flags_arith;
  rewrite H1, H2, H3, H4.

(** Per-branch: reduce the now-concrete if/match spine, re-normalize the
    flag reads the reduction exposed. Constant-preserving reduction
    ([cbv beta iota] + delta on negb only) — a full [cbn] would evaluate
    I32.zero/I32.one to raw literals and detach the goal from the
    chain-lemma statements. *)
Ltac setcond_branch_normalize :=
  cbv beta iota delta [negb];
  repeat first [ rewrite !set_reg_preserves_flags
               | rewrite !flags_set_flags ];
  rewrite ?flag_n_update_flags_arith, ?flag_z_update_flags_arith,
          ?flag_v_update_flags_arith, ?flag_c_update_flags_arith.

(** CMP/SBCS then MOVLT #1, MOVGE #0: rd = 64-bit signed <. *)
Lemma exec_chain_sbcs_lt :
  forall astate a_lo a_hi b_lo b_hi rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = a_lo ->
  get_reg astate rnhi = a_hi ->
  get_reg astate rmlo = b_lo ->
  get_reg astate rmhi = b_hi ->
  exists s',
    exec_program (chain_sbcs_lt rd rnlo rnhi rmlo rmhi) astate = Some s' /\
    get_reg s' rd
      = (if I64.lts (combine_i32 a_lo a_hi) (combine_i32 b_lo b_hi)
         then I32.one else I32.zero).
Proof.
  intros astate a_lo a_hi b_lo b_hi rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  setcond_chain_normalize H1 H2 H3 H4.
  set (L := I64.lts (combine_i32 a_lo a_hi) (combine_i32 b_lo b_hi)).
  assert (Heqb : Bool.eqb
      (compute_n_flag
         (I32.sub (I32.sub a_hi b_hi)
            (if compute_c_flag_sub a_lo b_lo then I32.zero else I32.one)))
      (compute_v_flag_sbc a_hi b_hi (compute_c_flag_sub a_lo b_lo))
      = negb L).
  { unfold L. rewrite <- pair_cmp_sbcs_nv_lts, negb_involutive. reflexivity. }
  rewrite Heqb.
  destruct L; setcond_branch_normalize; rewrite Heqb;
    setcond_branch_normalize;
    eexists; (split; [reflexivity | apply get_set_reg_eq]).
Qed.

(** CMP/SBCS then MOVGE #1, MOVLT #0: rd = 64-bit signed >=. *)
Lemma exec_chain_sbcs_ge :
  forall astate a_lo a_hi b_lo b_hi rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = a_lo ->
  get_reg astate rnhi = a_hi ->
  get_reg astate rmlo = b_lo ->
  get_reg astate rmhi = b_hi ->
  exists s',
    exec_program (chain_sbcs_ge rd rnlo rnhi rmlo rmhi) astate = Some s' /\
    get_reg s' rd
      = (if I64.lts (combine_i32 a_lo a_hi) (combine_i32 b_lo b_hi)
         then I32.zero else I32.one).
Proof.
  intros astate a_lo a_hi b_lo b_hi rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  setcond_chain_normalize H1 H2 H3 H4.
  set (L := I64.lts (combine_i32 a_lo a_hi) (combine_i32 b_lo b_hi)).
  assert (Heqb : Bool.eqb
      (compute_n_flag
         (I32.sub (I32.sub a_hi b_hi)
            (if compute_c_flag_sub a_lo b_lo then I32.zero else I32.one)))
      (compute_v_flag_sbc a_hi b_hi (compute_c_flag_sub a_lo b_lo))
      = negb L).
  { unfold L. rewrite <- pair_cmp_sbcs_nv_lts, negb_involutive. reflexivity. }
  rewrite Heqb.
  destruct L; setcond_branch_normalize; rewrite Heqb;
    setcond_branch_normalize;
    eexists; (split; [reflexivity | apply get_set_reg_eq]).
Qed.

(** CMP/SBCS then MOVLO #1, MOVHS #0: rd = 64-bit unsigned <. *)
Lemma exec_chain_sbcs_lo :
  forall astate a_lo a_hi b_lo b_hi rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = a_lo ->
  get_reg astate rnhi = a_hi ->
  get_reg astate rmlo = b_lo ->
  get_reg astate rmhi = b_hi ->
  exists s',
    exec_program (chain_sbcs_lo rd rnlo rnhi rmlo rmhi) astate = Some s' /\
    get_reg s' rd
      = (if I64.geu (combine_i32 a_lo a_hi) (combine_i32 b_lo b_hi)
         then I32.zero else I32.one).
Proof.
  intros astate a_lo a_hi b_lo b_hi rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  setcond_chain_normalize H1 H2 H3 H4.
  set (C := I64.geu (combine_i32 a_lo a_hi) (combine_i32 b_lo b_hi)).
  assert (HC : compute_c_flag_sbc a_hi b_hi (compute_c_flag_sub a_lo b_lo)
               = C)
    by apply pair_cmp_sbcs_c_geu.
  rewrite HC.
  (* HC also rewrote the C argument inside the SBCS flags record, so the
     second MOVcc's condition is already concrete after reduction *)
  destruct C; setcond_branch_normalize;
    eexists; (split; [reflexivity | apply get_set_reg_eq]).
Qed.

(** CMP/SBCS then MOVHS #1, MOVLO #0: rd = 64-bit unsigned >=. *)
Lemma exec_chain_sbcs_hs :
  forall astate a_lo a_hi b_lo b_hi rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = a_lo ->
  get_reg astate rnhi = a_hi ->
  get_reg astate rmlo = b_lo ->
  get_reg astate rmhi = b_hi ->
  exists s',
    exec_program (chain_sbcs_hs rd rnlo rnhi rmlo rmhi) astate = Some s' /\
    get_reg s' rd
      = (if I64.geu (combine_i32 a_lo a_hi) (combine_i32 b_lo b_hi)
         then I32.one else I32.zero).
Proof.
  intros astate a_lo a_hi b_lo b_hi rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  setcond_chain_normalize H1 H2 H3 H4.
  set (C := I64.geu (combine_i32 a_lo a_hi) (combine_i32 b_lo b_hi)).
  assert (HC : compute_c_flag_sbc a_hi b_hi (compute_c_flag_sub a_lo b_lo)
               = C)
    by apply pair_cmp_sbcs_c_geu.
  rewrite HC.
  (* HC also rewrote the C argument inside the SBCS flags record, so the
     second MOVcc's condition is already concrete after reduction *)
  destruct C; setcond_branch_normalize;
    eexists; (split; [reflexivity | apply get_set_reg_eq]).
Qed.

(** CMP/CMPEQ then MOVEQ #1, MOVNE #0: rd = 64-bit equality. The
    conditionally-executed CMPEQ compares the highs only when the lows were
    equal; otherwise the low-half flags (Z clear) survive to the MOVcc. *)
Lemma exec_chain_cmpeq_eq :
  forall astate a_lo a_hi b_lo b_hi rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = a_lo ->
  get_reg astate rnhi = a_hi ->
  get_reg astate rmlo = b_lo ->
  get_reg astate rmhi = b_hi ->
  exists s',
    exec_program (chain_cmpeq_eq rd rnlo rnhi rmlo rmhi) astate = Some s' /\
    get_reg s' rd
      = (if I64.eq (combine_i32 a_lo a_hi) (combine_i32 b_lo b_hi)
         then I32.one else I32.zero).
Proof.
  intros astate a_lo a_hi b_lo b_hi rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  setcond_chain_normalize H1 H2 H3 H4.
  rewrite <- (pair_cmp_cmpeq_z_eq a_lo a_hi b_lo b_hi).
  destruct (compute_z_flag (I32.sub a_lo b_lo)) eqn:Ez1;
    setcond_branch_normalize.
  - (* lows equal: CMPEQ ran; the final Z is the high-half compare *)
    destruct (compute_z_flag (I32.sub a_hi b_hi)) eqn:Ez2;
      setcond_branch_normalize; rewrite ?Ez2;
      setcond_branch_normalize;
      eexists; (split; [reflexivity | apply get_set_reg_eq]).
  - (* lows differ: CMPEQ skipped; Z stays clear for both MOVcc links *)
    rewrite ?Ez1; setcond_branch_normalize; rewrite ?Ez1;
      setcond_branch_normalize;
      eexists; (split; [reflexivity | apply get_set_reg_eq]).
Qed.

(** CMP/CMPEQ then MOVNE #1, MOVEQ #0: rd = 64-bit disequality. *)
Lemma exec_chain_cmpeq_ne :
  forall astate a_lo a_hi b_lo b_hi rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = a_lo ->
  get_reg astate rnhi = a_hi ->
  get_reg astate rmlo = b_lo ->
  get_reg astate rmhi = b_hi ->
  exists s',
    exec_program (chain_cmpeq_ne rd rnlo rnhi rmlo rmhi) astate = Some s' /\
    get_reg s' rd
      = (if I64.eq (combine_i32 a_lo a_hi) (combine_i32 b_lo b_hi)
         then I32.zero else I32.one).
Proof.
  intros astate a_lo a_hi b_lo b_hi rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  setcond_chain_normalize H1 H2 H3 H4.
  rewrite <- (pair_cmp_cmpeq_z_eq a_lo a_hi b_lo b_hi).
  destruct (compute_z_flag (I32.sub a_lo b_lo)) eqn:Ez1;
    setcond_branch_normalize.
  - destruct (compute_z_flag (I32.sub a_hi b_hi)) eqn:Ez2;
      setcond_branch_normalize; rewrite ?Ez2;
      setcond_branch_normalize;
      eexists; (split; [reflexivity | apply get_set_reg_eq]).
  - rewrite ?Ez1; setcond_branch_normalize; rewrite ?Ez1;
      setcond_branch_normalize;
      eexists; (split; [reflexivity | apply get_set_reg_eq]).
Qed.

(** ** The ten expansion programs — 1:1 with the encoder's I64SetCond match
    arms (arm_encoder.rs). Ordered conditions compare (rn, rm); GT/LE/HI/LS
    swap to (rm, rn) and test the LT/GE/LO/HS complement. *)

Definition i64_setcond_expansion_eq (rd rnlo rnhi rmlo rmhi : arm_reg) :=
  chain_cmpeq_eq rd rnlo rnhi rmlo rmhi.
Definition i64_setcond_expansion_ne (rd rnlo rnhi rmlo rmhi : arm_reg) :=
  chain_cmpeq_ne rd rnlo rnhi rmlo rmhi.
Definition i64_setcond_expansion_lt_s (rd rnlo rnhi rmlo rmhi : arm_reg) :=
  chain_sbcs_lt rd rnlo rnhi rmlo rmhi.
Definition i64_setcond_expansion_ge_s (rd rnlo rnhi rmlo rmhi : arm_reg) :=
  chain_sbcs_ge rd rnlo rnhi rmlo rmhi.
Definition i64_setcond_expansion_gt_s (rd rnlo rnhi rmlo rmhi : arm_reg) :=
  chain_sbcs_lt rd rmlo rmhi rnlo rnhi.   (* swapped operands, test LT *)
Definition i64_setcond_expansion_le_s (rd rnlo rnhi rmlo rmhi : arm_reg) :=
  chain_sbcs_ge rd rmlo rmhi rnlo rnhi.   (* swapped operands, test GE *)
Definition i64_setcond_expansion_lt_u (rd rnlo rnhi rmlo rmhi : arm_reg) :=
  chain_sbcs_lo rd rnlo rnhi rmlo rmhi.
Definition i64_setcond_expansion_ge_u (rd rnlo rnhi rmlo rmhi : arm_reg) :=
  chain_sbcs_hs rd rnlo rnhi rmlo rmhi.
Definition i64_setcond_expansion_gt_u (rd rnlo rnhi rmlo rmhi : arm_reg) :=
  chain_sbcs_lo rd rmlo rmhi rnlo rnhi.   (* swapped operands, test LO *)
Definition i64_setcond_expansion_le_u (rd rnlo rnhi rmlo rmhi : arm_reg) :=
  chain_sbcs_hs rd rmlo rmhi rnlo rnhi.   (* swapped operands, test HS *)

(** ** The ten expansion-level T1 theorems

    Same statement shape as the pseudo-op-tier [rule_i64_*_correct] in
    VcrSelRules.v — but [exec_program] runs the encoder's expansion and NO
    [i64_setcond_bits] axiom is consumed. *)

Theorem rule_i64_eq_expansion_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (i64_setcond_expansion_eq rd rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rd =
      (if I64.eq (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  exact (exec_chain_cmpeq_eq astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi
           H1 H2 H3 H4).
Qed.

Theorem rule_i64_ne_expansion_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (i64_setcond_expansion_ne rd rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rd =
      (if I64.ne (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  destruct (exec_chain_cmpeq_ne astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi
              H1 H2 H3 H4) as [s' [Hex Hrd]].
  exists s'. split; [exact Hex |].
  rewrite Hrd, i64_ne_negb_eq.
  destruct (I64.eq (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)); reflexivity.
Qed.

Theorem rule_i64_lt_s_expansion_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (i64_setcond_expansion_lt_s rd rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rd =
      (if I64.lts (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  exact (exec_chain_sbcs_lt astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi
           H1 H2 H3 H4).
Qed.

Theorem rule_i64_ge_s_expansion_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (i64_setcond_expansion_ge_s rd rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rd =
      (if I64.ges (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  destruct (exec_chain_sbcs_ge astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi
              H1 H2 H3 H4) as [s' [Hex Hrd]].
  exists s'. split; [exact Hex |].
  rewrite Hrd, i64_ges_negb_lts.
  destruct (I64.lts (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)); reflexivity.
Qed.

Theorem rule_i64_gt_s_expansion_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (i64_setcond_expansion_gt_s rd rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rd =
      (if I64.gts (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  destruct (exec_chain_sbcs_lt astate lo2 hi2 lo1 hi1 rd rmlo rmhi rnlo rnhi
              H3 H4 H1 H2) as [s' [Hex Hrd]].
  exists s'. split; [exact Hex |].
  rewrite Hrd, i64_gts_lts_swap. reflexivity.
Qed.

Theorem rule_i64_le_s_expansion_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (i64_setcond_expansion_le_s rd rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rd =
      (if I64.les (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  destruct (exec_chain_sbcs_ge astate lo2 hi2 lo1 hi1 rd rmlo rmhi rnlo rnhi
              H3 H4 H1 H2) as [s' [Hex Hrd]].
  exists s'. split; [exact Hex |].
  rewrite Hrd, i64_les_negb_lts_swap.
  destruct (I64.lts (combine_i32 lo2 hi2) (combine_i32 lo1 hi1)); reflexivity.
Qed.

Theorem rule_i64_lt_u_expansion_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (i64_setcond_expansion_lt_u rd rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rd =
      (if I64.ltu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  destruct (exec_chain_sbcs_lo astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi
              H1 H2 H3 H4) as [s' [Hex Hrd]].
  exists s'. split; [exact Hex |].
  rewrite Hrd, i64_ltu_negb_geu.
  destruct (I64.geu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)); reflexivity.
Qed.

Theorem rule_i64_ge_u_expansion_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (i64_setcond_expansion_ge_u rd rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rd =
      (if I64.geu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  exact (exec_chain_sbcs_hs astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi
           H1 H2 H3 H4).
Qed.

Theorem rule_i64_gt_u_expansion_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (i64_setcond_expansion_gt_u rd rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rd =
      (if I64.gtu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  destruct (exec_chain_sbcs_lo astate lo2 hi2 lo1 hi1 rd rmlo rmhi rnlo rnhi
              H3 H4 H1 H2) as [s' [Hex Hrd]].
  exists s'. split; [exact Hex |].
  rewrite Hrd, i64_gtu_negb_geu_swap.
  destruct (I64.geu (combine_i32 lo2 hi2) (combine_i32 lo1 hi1)); reflexivity.
Qed.

Theorem rule_i64_le_u_expansion_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (i64_setcond_expansion_le_u rd rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rd =
      (if I64.leu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi H1 H2 H3 H4.
  destruct (exec_chain_sbcs_hs astate lo2 hi2 lo1 hi1 rd rmlo rmhi rnlo rnhi
              H3 H4 H1 H2) as [s' [Hex Hrd]].
  exists s'. split; [exact Hex |].
  rewrite Hrd, i64_leu_geu_swap. reflexivity.
Qed.
