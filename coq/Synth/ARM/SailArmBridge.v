(** * VCR-ISA-001 SPIKE — Sail/ASL-derived semantics bridge (AArch32 ADD/ADDS/CMP, register forms)

    GOAL (epic #242, VCR-ISA-001). ArmSemantics.v is a HAND-WRITTEN ARM model:
    every correctness theorem in this suite (including the 21 VCR-SEL-001 rule
    theorems) is "consistent with our own model" — a modeling bug is invisible
    to the proofs. VCR-ISA-001 wants the model anchored on an INDEPENDENTLY
    derived semantics: Arm's own machine-readable ASL specification, as
    translated to Sail by the REMS asl_to_sail tool (rems-project/sail-arm).

    WHAT THIS FILE IS. The spike's measured outcome (docs/design/
    vcr-isa-001-spike.md) is that importing the Sail-GENERATED Rocq model
    wholesale is a no-go at synth's scale: the arm-v9.4-a Coq snapshot is a
    single 42 MB armv9.v pinned to stdpp-unstable + coq-sail-stdpp, and the
    older v8.5 snapshot needed ~40 GB RAM on Coq 8.9.1. The viable re-basing
    path is per instruction: transcribe the Sail execute semantics BY HAND,
    with line-level provenance to the Sail source, and prove a BRIDGE lemma
    that ArmSemantics.v's instruction ≡ the transcription on the shared state
    projection. This file does that end-to-end for ONE instruction family —
    AArch32 ADD (register): ADD (result only), ADDS (result + NZCV), and, as
    the subtraction-flags counterpart the comparison rules rest on, CMP
    (register) — so the per-instruction cost and the abstraction gaps are
    measured facts, not estimates.

    PROVENANCE. All quoted Sail is from rems-project/sail-arm @ master
    (commit 1bf2e5574ba9, 2026-06-19), model arm-v9.4-a, which the repo README
    states is derived from the 2023-03 version of Arm's ASL specification via
    the automatic asl_to_sail translation:

      - AddWithCarry              arm-v9.4-a/src/v8_base.sail:13337
      - execute ADD (register)    arm-v9.4-a/src/instrs32.sail:457
        (execute_aarch32_instrs_ADD_r_Op_A_txt)
      - decode T1 (16-bit Thumb)  arm-v9.4-a/src/instrs32.sail:512
        (shift_t = SRType_LSL, shift_n = 0, setflags = !InITBlock())
      - execute CMP (register)    instrs32.sail
        (execute_aarch32_instrs_CMP_r_Op_A_txt:
         "AddWithCarry(R[n], NOT(shifted), '1')", flags-only)
      - Shift_C amount=0 identity arm-v9.4-a/src/v8_base.sail:41273
        ("if amount == 0 then (result, carry_out) = (value_name, carry_in)")

    THE TRANSCRIBED SLICE. The ADD execute clause, restricted to what synth's
    encoder emits for this instruction:

      function execute_aarch32_instrs_ADD_r_Op_A_txt
               (d, m, n, setflags, shift_n, shift_t) = {
          let shifted : bits(32) = Shift(R_read(m), shift_t, shift_n, PSTATE.C);
          (result, nzcv) = AddWithCarry(R_read(n), shifted, 0b0);
          if d == 15 then { ... ALUWritePC ... } else {
              R_set(d) = result;
              if setflags then {
                  (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = nzcv
              };
          }
      }

    ABSTRACTION GAPS (explicit, in trade for tractability):
      1. shift_n = 0: synth emits plain register forms (no shifted operand),
         and Shift_C with amount 0 is the identity on the value and the carry
         (v8_base.sail:41273), so [shifted = R_read(m)] and PSTATE.C is not
         read. The RegShift operand2 form is outside this bridge (it is also
         only half-modeled in ArmSemantics.v's eval_operand2).
      2. d <> 15: the ALUWritePC branch is out of scope — ArmSemantics.v has
         no PC-indexed executor (the known VCR-ISA-001 gap that also blocks
         the div/rem trap-guard admits), and synth's selector never assigns
         PC via ADD.
      3. ConditionPassed() = true: unconditional execution; synth does not
         emit ADD inside IT blocks.
      4. bits(32) is rendered as I32.int (Z modulo 2^32): Sail/ASL UInt maps
         to I32.unsigned, SInt to I32.signed, bit extraction result<31> to
         Z.testbit. The residual trust is the fidelity of this hand
         transcription — reviewable line-by-line against the quoted Sail —
         instead of the fidelity of the whole hand-written model.

    THE BRIDGE. [sail_bridge_add_reg], [sail_bridge_adds_reg] and
    [sail_bridge_cmp_reg] prove that exec_instr's ADD/ADDS/CMP agree with the
    transcription EXACTLY (register write and all four NZCV flags — no flag
    is ignored). In particular the six hand-written flag definitions
    (compute_n_flag / compute_z_flag / compute_c_flag_add /
    compute_v_flag_add / compute_c_flag_sub / compute_v_flag_sub), on which
    Compilation.v's CMP-based comparison lowerings and the VcrSelRules.v
    comparison rules ultimately rest, are proven equal to ASL's AddWithCarry
    flag outputs. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.
Require Import Synth.ARM.ArmSemantics.

Import ListNotations.
Open Scope Z_scope.

(** ** Transcription of the Sail definitions *)

(** [AddWithCarry] — v8_base.sail:13337 (N = 32):

      function AddWithCarry (x, y, carry_in) = {
          let 'unsigned_sum = UInt(x) + UInt(y) + UInt(carry_in);
          let 'signed_sum = SInt(x) + SInt(y) + UInt(carry_in);
          let result : bits('N) = unsigned_sum['N - 1 .. 0];
          let n : bits(1) = [result['N - 1]];
          let z : bits(1) = if IsZero(result) then 0b1 else 0b0;
          let c : bits(1) = if UInt(result) == unsigned_sum then 0b0 else 0b1;
          let v : bits(1) = if SInt(result) == signed_sum then 0b0 else 0b1;
          return((result, ((n @ z) @ c) @ v))
      }

    Rendering: UInt = I32.unsigned, SInt = I32.signed,
    unsigned_sum<31..0> = I32.repr unsigned_sum, result<31> = Z.testbit _ 31,
    IsZero = (=? 0). The nzcv tuple is kept in ASL order (n, z, c, v). *)
Definition sail_add_with_carry (x y : I32.int) (carry_in : bool)
    : I32.int * (bool * bool * bool * bool) :=
  let carry : Z := if carry_in then 1 else 0 in
  let unsigned_sum := I32.unsigned x + I32.unsigned y + carry in
  let signed_sum := I32.signed x + I32.signed y + carry in
  let result := I32.repr unsigned_sum in
  let n := Z.testbit (I32.unsigned result) 31 in
  let z := Z.eqb (I32.unsigned result) 0 in
  let c := negb (Z.eqb (I32.unsigned result) unsigned_sum) in
  let v := negb (Z.eqb (I32.signed result) signed_sum) in
  (result, (n, z, c, v)).

(** [NOT] on bits(32) — used by the SUB/CMP execute clauses
    ("AddWithCarry(R[n], NOT(shifted), '1')"). Bitwise complement over Z,
    brought back into range by repr — the same rendering ArmSemantics.v uses
    for MVN. *)
Definition sail_not (y : I32.int) : I32.int :=
  I32.repr (Z.lnot (I32.unsigned y)).

(** The ADD (register) execute clause, d <> 15, shift_n = 0 (gaps 1-3 above):
    [shifted = R_read(m)], so the addition is AddWithCarry(R[n], R[m], '0'). *)
Definition sail_add_r_result (rn_val rm_val : I32.int) : I32.int :=
  fst (sail_add_with_carry rn_val rm_val false).

Definition sail_add_r_flags (rn_val rm_val : I32.int) : condition_flags :=
  let '(_, (n, z, c, v)) := sail_add_with_carry rn_val rm_val false in
  mkFlags n z c v.

(** The CMP (register) execute clause, shift_n = 0: flags-only,
    AddWithCarry(R[n], NOT(R[m]), '1'). *)
Definition sail_cmp_r_flags (rn_val rm_val : I32.int) : condition_flags :=
  let '(_, (n, z, c, v)) := sail_add_with_carry rn_val (sail_not rm_val) true in
  mkFlags n z c v.

(** ** Arithmetic helpers *)

Lemma modulus_val : I32.modulus = 4294967296.
Proof. reflexivity. Qed.

Lemma half_modulus_val : I32.half_modulus = 2147483648.
Proof. reflexivity. Qed.

Lemma modulus_nz : I32.modulus <> 0.
Proof. rewrite modulus_val. lia. Qed.

Lemma unsigned_range : forall x : I32.int,
  0 <= I32.unsigned x < I32.modulus.
Proof.
  intros. unfold I32.unsigned. apply Z.mod_pos_bound.
  rewrite modulus_val. lia.
Qed.

(** The Sail-side sum-of-unsigneds representative equals our I32.add. *)
Lemma repr_add_unsigned : forall x y : I32.int,
  I32.repr (I32.unsigned x + I32.unsigned y) = I32.add x y.
Proof.
  intros. unfold I32.add, I32.repr, I32.unsigned.
  symmetry. apply Z.add_mod. apply modulus_nz.
Qed.

(** The Sail-side CMP representative (x + NOT y + 1) equals our I32.sub. *)
Lemma repr_sub_unsigned : forall x y : I32.int,
  I32.repr (I32.unsigned x + (I32.modulus - 1 - I32.unsigned y) + 1)
  = I32.sub x y.
Proof.
  intros. unfold I32.sub, I32.repr, I32.unsigned.
  replace (x mod I32.modulus + (I32.modulus - 1 - y mod I32.modulus) + 1)
    with ((x mod I32.modulus - y mod I32.modulus) + 1 * I32.modulus) by lia.
  rewrite Z_mod_plus_full.
  rewrite <- Zminus_mod. reflexivity.
Qed.

(** Splitting the mod of a sum of two in-range values. *)
Lemma sum_mod_cases : forall a b,
  0 <= a < I32.modulus -> 0 <= b < I32.modulus ->
  ((a + b) mod I32.modulus = a + b /\ a + b < I32.modulus) \/
  ((a + b) mod I32.modulus = a + b - I32.modulus /\ I32.modulus <= a + b).
Proof.
  intros a b Ha Hb.
  destruct (Z_lt_ge_dec (a + b) I32.modulus) as [L | G].
  - left. split; [apply Z.mod_small; lia | lia].
  - right. split; [| lia].
    assert (Hrw : a + b = (a + b - I32.modulus) + 1 * I32.modulus) by lia.
    rewrite Hrw at 1.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(** Splitting the mod of a difference of two in-range values. *)
Lemma diff_mod_cases : forall a b,
  0 <= a < I32.modulus -> 0 <= b < I32.modulus ->
  ((a - b) mod I32.modulus = a - b /\ b <= a) \/
  ((a - b) mod I32.modulus = a - b + I32.modulus /\ a < b).
Proof.
  intros a b Ha Hb.
  destruct (Z_le_gt_dec b a) as [L | G].
  - left. split; [apply Z.mod_small; lia | lia].
  - right. split; [| lia].
    assert (Hrw : a - b = (a - b + I32.modulus) + (-1) * I32.modulus) by lia.
    rewrite Hrw at 1.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(** Bit 31 of an in-range value is its top (sign) bit. *)
Lemma testbit31_ge : forall u,
  0 <= u < I32.modulus ->
  Z.testbit u 31 = (I32.half_modulus <=? u).
Proof.
  intros u Hu. rewrite modulus_val in Hu.
  assert (E : Z.testbit u 31 = Z.odd (u / 2 ^ 31)).
  { rewrite <- Z.bit0_odd. rewrite <- Z.shiftr_div_pow2 by lia.
    rewrite Z.shiftr_spec by lia. reflexivity. }
  rewrite E.
  assert (Hdiv : u / 2 ^ 31 = (if I32.half_modulus <=? u then 1 else 0)).
  { change (2 ^ 31) with 2147483648.
    destruct (Z.leb_spec I32.half_modulus u) as [L | L];
      rewrite half_modulus_val in L.
    - assert (1 <= u / 2147483648) by (apply Z.div_le_lower_bound; lia).
      assert (u / 2147483648 < 2) by (apply Z.div_lt_upper_bound; lia).
      lia.
    - apply Z.div_small. lia. }
  rewrite Hdiv. destruct (I32.half_modulus <=? u); reflexivity.
Qed.

(** [NOT(y)] = modulus - 1 - y on the unsigned view. *)
Lemma unsigned_not : forall y : I32.int,
  I32.unsigned (sail_not y) = I32.modulus - 1 - I32.unsigned y.
Proof.
  intros. unfold sail_not, I32.repr, I32.unsigned.
  rewrite Zmod_mod.
  pose proof (unsigned_range y) as Hy. unfold I32.unsigned in Hy.
  assert (L : Z.lnot (y mod I32.modulus) = - (y mod I32.modulus) - 1)
    by (unfold Z.lnot; lia).
  rewrite L.
  replace (- (y mod I32.modulus) - 1)
    with ((I32.modulus - 1 - y mod I32.modulus) + (-1) * I32.modulus) by lia.
  rewrite Z_mod_plus_full.
  apply Z.mod_small. lia.
Qed.

(** [NOT(y)] = -1 - y on the signed view (two's complement identity). *)
Lemma signed_not : forall y : I32.int,
  I32.signed (sail_not y) = - 1 - I32.signed y.
Proof.
  intros. unfold I32.signed. cbv zeta.
  rewrite unsigned_not.
  pose proof (unsigned_range y) as Hy.
  assert (HMH : I32.modulus = 2 * I32.half_modulus) by reflexivity.
  assert (HH : 0 < I32.half_modulus) by (rewrite half_modulus_val; lia).
  destruct (Z.ltb_spec0 (I32.modulus - 1 - I32.unsigned y) I32.half_modulus);
    destruct (Z.ltb_spec0 (I32.unsigned y) I32.half_modulus); lia.
Qed.

(** ** Tactics: reduce boolean [if]s (all conditions here are Z.ltb),
    then blast the remaining decidable comparisons. *)

Ltac destruct_ifs :=
  repeat match goal with
  | |- context [if ?b then _ else _] =>
      let E := fresh "Eif" in
      destruct b eqn:E;
      repeat match goal with
             | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
             | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
             end
  end.

Ltac bool_blast :=
  repeat first
    [ progress cbn [negb andb orb]
    | match goal with
      | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
      | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b)
      | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec0 a b)
      end ];
  try reflexivity; try lia.

(** ** Per-flag bridges: the hand-written flag definitions of
    ArmSemantics.v equal the ASL AddWithCarry outputs. *)

(** N: ASL "result<31>" ≡ our "signed result < 0". *)
Lemma sail_bridge_n_flag : forall r : I32.int,
  Z.testbit (I32.unsigned r) 31 = compute_n_flag r.
Proof.
  intros.
  rewrite (testbit31_ge _ (unsigned_range r)).
  unfold compute_n_flag, I32.signed. cbv zeta.
  pose proof (unsigned_range r) as Hr.
  assert (HMH : I32.modulus = 2 * I32.half_modulus) by reflexivity.
  assert (HH : 0 < I32.half_modulus) by (rewrite half_modulus_val; lia).
  destruct_ifs; bool_blast.
Qed.

(** Z: ASL "IsZero(result)" ≡ our "result == 0". *)
Lemma sail_bridge_z_flag : forall r : I32.int,
  (I32.unsigned r =? 0) = compute_z_flag r.
Proof.
  intros. unfold compute_z_flag, I32.eq.
  assert (E : I32.unsigned I32.zero = 0) by reflexivity.
  rewrite E. reflexivity.
Qed.

(** C (addition): ASL "UInt(result) != unsigned_sum" ≡ our unsigned-overflow
    test "max_unsigned < ux + uy". *)
Lemma sail_bridge_c_flag_add : forall x y : I32.int,
  negb (I32.unsigned (I32.add x y) =? I32.unsigned x + I32.unsigned y)
  = compute_c_flag_add x y.
Proof.
  intros.
  pose proof (unsigned_range x) as Hx.
  pose proof (unsigned_range y) as Hy.
  pose proof modulus_nz as Hnz.
  assert (Hu : I32.unsigned (I32.add x y)
               = (I32.unsigned x + I32.unsigned y) mod I32.modulus).
  { unfold I32.add, I32.repr, I32.unsigned.
    rewrite Zmod_mod. apply Z.add_mod. apply modulus_nz. }
  unfold compute_c_flag_add, I32.max_unsigned. cbv zeta.
  rewrite Hu.
  destruct (sum_mod_cases _ _ Hx Hy) as [[E L] | [E L]]; rewrite E; bool_blast.
Qed.

(** V (addition): ASL "SInt(result) != signed_sum" ≡ our sign-pattern test
    "(pos + pos = neg) or (neg + neg = pos)". *)
Lemma sail_bridge_v_flag_add : forall x y : I32.int,
  negb (I32.signed (I32.add x y) =? I32.signed x + I32.signed y)
  = compute_v_flag_add x y (I32.add x y).
Proof.
  intros.
  pose proof (unsigned_range x) as Hx.
  pose proof (unsigned_range y) as Hy.
  assert (HMH : I32.modulus = 2 * I32.half_modulus) by reflexivity.
  assert (HH : 0 < I32.half_modulus) by (rewrite half_modulus_val; lia).
  assert (Hu : I32.unsigned (I32.add x y)
               = (I32.unsigned x + I32.unsigned y) mod I32.modulus).
  { unfold I32.add, I32.repr, I32.unsigned.
    rewrite Zmod_mod. apply Z.add_mod. apply modulus_nz. }
  unfold compute_v_flag_add, I32.signed. cbv zeta.
  rewrite Hu.
  destruct (sum_mod_cases _ _ Hx Hy) as [[E L] | [E L]]; rewrite E;
    destruct_ifs; bool_blast.
Qed.

(** C (subtraction/CMP): ASL "UInt(result) != UInt(x) + UInt(NOT y) + 1"
    ≡ our no-borrow test "uy <= ux". *)
Lemma sail_bridge_c_flag_sub : forall x y : I32.int,
  negb (I32.unsigned (I32.sub x y)
        =? I32.unsigned x + (I32.modulus - 1 - I32.unsigned y) + 1)
  = compute_c_flag_sub x y.
Proof.
  intros.
  pose proof (unsigned_range x) as Hx.
  pose proof (unsigned_range y) as Hy.
  pose proof modulus_nz as Hnz.
  assert (Hu : I32.unsigned (I32.sub x y)
               = (I32.unsigned x - I32.unsigned y) mod I32.modulus).
  { unfold I32.sub, I32.repr, I32.unsigned.
    rewrite Zmod_mod. apply Zminus_mod. }
  unfold compute_c_flag_sub. cbv zeta.
  rewrite Hu.
  destruct (diff_mod_cases _ _ Hx Hy) as [[E L] | [E L]]; rewrite E; bool_blast.
Qed.

(** V (subtraction/CMP): ASL "SInt(result) != SInt(x) + SInt(NOT y) + 1"
    ≡ our sign-pattern test "(pos - neg = neg) or (neg - pos = pos)". *)
Lemma sail_bridge_v_flag_sub : forall x y : I32.int,
  negb (I32.signed (I32.sub x y) =? I32.signed x + (- 1 - I32.signed y) + 1)
  = compute_v_flag_sub x y.
Proof.
  intros.
  pose proof (unsigned_range x) as Hx.
  pose proof (unsigned_range y) as Hy.
  assert (HMH : I32.modulus = 2 * I32.half_modulus) by reflexivity.
  assert (HH : 0 < I32.half_modulus) by (rewrite half_modulus_val; lia).
  assert (Hu : I32.unsigned (I32.sub x y)
               = (I32.unsigned x - I32.unsigned y) mod I32.modulus).
  { unfold I32.sub, I32.repr, I32.unsigned.
    rewrite Zmod_mod. apply Zminus_mod. }
  unfold compute_v_flag_sub, I32.signed. cbv zeta.
  rewrite Hu.
  destruct (diff_mod_cases _ _ Hx Hy) as [[E L] | [E L]]; rewrite E;
    destruct_ifs; bool_blast.
Qed.

(** ** Whole-instruction correspondence *)

(** The transcribed AddWithCarry result equals our I32.add. *)
Lemma sail_add_r_result_eq : forall x y,
  sail_add_r_result x y = I32.add x y.
Proof.
  intros. unfold sail_add_r_result, sail_add_with_carry.
  cbv beta iota zeta. cbn [fst].
  rewrite Z.add_0_r. apply repr_add_unsigned.
Qed.

(** The transcribed AddWithCarry NZCV equals our ADDS flag computation. *)
Lemma sail_add_r_flags_eq : forall x y,
  sail_add_r_flags x y
  = update_flags_arith (I32.add x y) (compute_c_flag_add x y)
                       (compute_v_flag_add x y (I32.add x y)).
Proof.
  intros. unfold sail_add_r_flags, sail_add_with_carry.
  cbv beta iota zeta.
  rewrite !Z.add_0_r.
  rewrite repr_add_unsigned.
  unfold update_flags_arith.
  (* the Z component is definitionally equal (f_equal closes it); N/C/V need
     the per-flag bridges — sail_bridge_z_flag records the Z fact anyway *)
  f_equal.
  - apply sail_bridge_n_flag.
  - apply sail_bridge_c_flag_add.
  - apply sail_bridge_v_flag_add.
Qed.

(** The transcribed CMP NZCV equals our CMP flag computation. *)
Lemma sail_cmp_r_flags_eq : forall x y,
  sail_cmp_r_flags x y
  = update_flags_arith (I32.sub x y) (compute_c_flag_sub x y)
                       (compute_v_flag_sub x y).
Proof.
  intros. unfold sail_cmp_r_flags, sail_add_with_carry.
  cbv beta iota zeta.
  rewrite unsigned_not, signed_not.
  rewrite repr_sub_unsigned.
  unfold update_flags_arith.
  f_equal.
  - apply sail_bridge_n_flag.
  - apply sail_bridge_c_flag_sub.
  - apply sail_bridge_v_flag_sub.
Qed.

(** *** The bridge theorems — ArmSemantics.v ≡ the Sail/ASL transcription
    on the full observable state (destination register + NZCV). *)

(** ADD (register), setflags = false — e.g. T2 encoding outside an IT block,
    or the T3/A1 encodings with S=0. Sail: R_set(d) = result, PSTATE
    untouched. Ours: exec_instr (ADD ...). The states agree EXACTLY. *)
Theorem sail_bridge_add_reg : forall s rd rn rm,
  exec_instr (ADD rd rn (Reg rm)) s
  = Some (set_reg s rd (sail_add_r_result (get_reg s rn) (get_reg s rm))).
Proof.
  intros. rewrite sail_add_r_result_eq. reflexivity.
Qed.

(** ADDS (register), setflags = true — e.g. the T1 encoding outside an IT
    block ("setflags = !InITBlock()", instrs32.sail:512). Result register AND
    all four PSTATE.{N,Z,C,V} agree EXACTLY. *)
Theorem sail_bridge_adds_reg : forall s rd rn rm,
  exec_instr (ADDS rd rn (Reg rm)) s
  = Some (set_flags
            (set_reg s rd (sail_add_r_result (get_reg s rn) (get_reg s rm)))
            (sail_add_r_flags (get_reg s rn) (get_reg s rm))).
Proof.
  intros. rewrite sail_add_r_result_eq, sail_add_r_flags_eq. reflexivity.
Qed.

(** CMP (register): flags-only, "AddWithCarry(R[n], NOT(shifted), '1')".
    All four PSTATE.{N,Z,C,V} agree EXACTLY — this is the foundation under
    every CMP+conditional lowering in Compilation.v and VcrSelRules.v. *)
Theorem sail_bridge_cmp_reg : forall s rn rm,
  exec_instr (CMP rn (Reg rm)) s
  = Some (set_flags s (sail_cmp_r_flags (get_reg s rn) (get_reg s rm))).
Proof.
  intros. rewrite sail_cmp_r_flags_eq. reflexivity.
Qed.
