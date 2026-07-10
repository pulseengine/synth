(** * VCR-ISA-001 — Sail/ASL-derived semantics bridge (AArch32 integer core)

    Round 1 (spike, PR #660): ADD/ADDS/CMP (register) + all four NZCV flags.
    Round 2 (this increment): the rest of the AddWithCarry family
    (SUB/SUBS/CMN/RSB/ADC/SBC), the flag-free ALU class (AND/ORR/EOR/MVN),
    the shift class (LSL/LSR/ASR/ROR, immediate and register forms, via a
    Shift_C transcription), and MOV/MOVW/MOVT. See the ROUND 2 section
    header below for its provenance table and additional abstraction gaps.

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

(** ** ROUND 2 — AddWithCarry family + flag-free ALU + shifts + moves

    Same pin as round 1: rems-project/sail-arm @ master (commit 1bf2e5574ba9,
    2026-06-19), model arm-v9.4-a. Execute-clause provenance:

      - execute SUB (register)    instrs32.sail:15676
        "(result, nzcv) = AddWithCarry(R_read(n), not_vec(shifted), 0b1)"
      - execute RSB (register)    instrs32.sail:10337
        "(result, nzcv) = AddWithCarry(not_vec(R_read(n)), shifted, 0b1)"
      - execute ADC (register)    instrs32.sail:119
        "(result, nzcv) = AddWithCarry(R_read(n), shifted, PSTATE.C)"
      - execute SBC (register)    instrs32.sail:10946
        "(result, nzcv) = AddWithCarry(R_read(n), not_vec(shifted), PSTATE.C)"
      - execute CMN (register)    instrs32.sail:2428
        "(result, nzcv) = AddWithCarry(R_read(n), shifted, 0b0)" (flags only)
      - execute AND (register)    instrs32.sail:1141
        "let result : bits(32) = R_read(n) & shifted"
      - execute ORR (register)    instrs32.sail:8478
        "let result : bits(32) = R_read(n) | shifted"
      - execute EOR (register)    instrs32.sail:3173
        "let result : bits(32) = EOR(R_read(n), shifted)"
        (EOR = xor_vec, prelude.sail:216)
      - execute MVN (register)    instrs32.sail:8066
        "let result : bits(32) = not_vec(shifted)"
      - execute LSL (immediate)   instrs32.sail:6859
        "(result, carry) = Shift_C(R_read(m), SRType_LSL, shift_n, PSTATE.C)"
      - execute LSR (immediate)   instrs32.sail:6972 (SRType_LSR)
      - execute ASR (immediate)   instrs32.sail:1310 (SRType_ASR)
      - ROR (immediate) has no execute clause of its own: it is the
        MOV (register) instruction with shift_t = SRType_ROR, shift_n =
        UInt(imm5) <> 0 (execute at instrs32.sail:7469; DecodeImmShift
        v8_base.sail:41327 maps stype 0b11, imm5 <> 0 to (SRType_ROR,
        UInt(imm5)); imm5 == 0 is SRType_RRX — out of scope, synth never
        emits RRX)
      - execute LSL (register)    instrs32.sail:6909
        "let 'shift_n = UInt(R_read(m)[7 .. 0]);
         (result, carry) = Shift_C(R_read(n), SRType_LSL, shift_n, PSTATE.C)"
      - execute LSR (register)    instrs32.sail:7019 (SRType_LSR)
      - execute ASR (register)    instrs32.sail:1357 (SRType_ASR)
      - execute ROR (register)    instrs32.sail:10205 (SRType_ROR)
      - execute MOV (register)    instrs32.sail:7469
        "(shifted, carry) = Shift_C(R_read(m), shift_t, shift_n, PSTATE.C);
         let result : bits(32) = shifted"
      - execute MOV (immediate)   instrs32.sail:7315
        "let result : bits(32) = imm32" (MOVW = T3/A2 encoding,
        imm32 = ZeroExtend(imm16, 32))
      - execute MOVT              instrs32.sail:7722
        "R_set(d) = [R_read(d) with 31 .. 16 = imm16]"

    Shifter-helper provenance (quoted where transcribed below):

      - Shift_C   v8_base.sail:41273  (amount == 0 => (value, carry_in))
      - LSL_C     builtins.sail:69
      - LSR_C     builtins.sail:78
      - ASR_C     builtins.sail:88
      - ROR_C     builtins.sail:99

    ADDITIONAL ABSTRACTION GAPS (beyond gaps 1-4 in the file header; each is
    a measured statement about what the theorems below do NOT cover):

      5. setflags = false for the ALU/shift/move bridges. ArmSemantics.v has
         no flag-setting AND/ORR/EOR/MVN/shift/MOV forms (no ANDS/LSLS/MOVS
         arm_instr constructors), so the Sail setflags branch — N = result<31>,
         Z = IsZero(result), C = shifter carry-out, V unchanged — has no
         counterpart to bridge. The shifter carry-out IS transcribed faithfully
         in sail_{lsl,lsr,asr,ror}_c below (the new C territory Shift_C opens),
         so a future ANDS/LSLS/MOVS model extension only needs the bridge
         lemma, not a new transcription. SUBS/ADDS/CMP/CMN are unaffected
         (their flags come from AddWithCarry and ARE fully bridged).
      6. Immediate shifts bridge for shift_n in 1..31. shift_n = 32
         (LSR/ASR imm5 = 00000, DecodeImmShift v8_base.sail:41327) is a REAL
         MODEL DIVERGENCE, not just a gap: I32.shru/shrs mask the amount
         mod 32, so ArmSemantics.v computes a shift by 0 where ARM produces
         0 / the sign-fill. Compilation.v only emits WASM-masked amounts
         (0..31), so no emitted program reaches the divergence — but the
         hand-written model is WRONG about LSR/ASR #32 and a bridge for it
         is intentionally impossible until the model is fixed.
      7. Register shifts bridge under 0 < UInt(R[s]) < 32. ARM reads the low
         BYTE of the shift register (UInt(R[s]<7:0>), so amounts 32..255
         produce 0 / sign-fill / rotate-mod-32), while I32.shl/shru/shrs mask
         mod 32 — same divergence class as gap 6 for dynamic amounts >= 32.
         WASM shift semantics mask the amount mod 32 BEFORE the instruction,
         so lowered code never presents an out-of-range amount. The amount = 0
         case is bridged separately on the unsigned view
         (sail_bridge_*_reg_zero below): Shift_C with amount 0 returns the
         input bits(32) unchanged, which in the Z-rendering is the RAW
         representative, while our shift-by-0 normalizes through repr — the
         two agree on I32.unsigned (the only observation WASM values make)
         but not as raw Z, so the exact-state equality form does not apply.
      8. BIC (register) exists in the Sail model (instrs32.sail:1744) but
         ArmSemantics.v has no BIC instruction — nothing to bridge (recorded
         so the omission is a model gap, not an oversight).
      9. MOVW holds the already-expanded imm32: ArmInstructions.v's
         MOVW rd imm takes an I32.int, not the encoding's 16-bit field, so
         the bridge assumes imm = ZeroExtend(imm16, 32) (i.e. is exact only
         when UInt(imm) < 2^16 — which is what the Rust encoder emits).
         MOVT is bridged under the same UInt(imm16) < 2^16 hypothesis.
     10. RRX is out of scope entirely (synth never emits it; ArmSemantics.v
         cannot represent it). *)

(** *** Transcription: the remaining AddWithCarry users *)

(** SUB (register), d <> 15, shift_n = 0:
    "AddWithCarry(R_read(n), not_vec(shifted), 0b1)" (instrs32.sail:15676).
    Same AddWithCarry + NOT shape as CMP — SUB additionally writes R[d]. *)
Definition sail_sub_r_result (rn_val rm_val : I32.int) : I32.int :=
  fst (sail_add_with_carry rn_val (sail_not rm_val) true).

Definition sail_sub_r_flags (rn_val rm_val : I32.int) : condition_flags :=
  let '(_, (n, z, c, v)) := sail_add_with_carry rn_val (sail_not rm_val) true in
  mkFlags n z c v.

(** RSB (register): "AddWithCarry(not_vec(R_read(n)), shifted, 0b1)"
    (instrs32.sail:10337) — the NOT lands on the FIRST operand. *)
Definition sail_rsb_r_result (rn_val rm_val : I32.int) : I32.int :=
  fst (sail_add_with_carry (sail_not rn_val) rm_val true).

(** CMN (register): "AddWithCarry(R_read(n), shifted, 0b0)", flags only
    (instrs32.sail:2428) — the ADDS flag computation without the write. *)
Definition sail_cmn_r_flags (rn_val rm_val : I32.int) : condition_flags :=
  let '(_, (n, z, c, v)) := sail_add_with_carry rn_val rm_val false in
  mkFlags n z c v.

(** ADC (register): "AddWithCarry(R_read(n), shifted, PSTATE.C)"
    (instrs32.sail:119) — the first bridged op whose carry_in is the LIVE
    C flag, not a constant. *)
Definition sail_adc_r_result (rn_val rm_val : I32.int) (c : bool) : I32.int :=
  fst (sail_add_with_carry rn_val rm_val c).

(** SBC (register): "AddWithCarry(R_read(n), not_vec(shifted), PSTATE.C)"
    (instrs32.sail:10946). *)
Definition sail_sbc_r_result (rn_val rm_val : I32.int) (c : bool) : I32.int :=
  fst (sail_add_with_carry rn_val (sail_not rm_val) c).

(** *** Transcription: flag-free ALU (result paths; the setflags branch is
    gap 5) *)

(** AND/ORR/EOR on bits(32) — "R_read(n) & shifted" / "|" / "EOR(...)"
    at shift_n = 0 (Shift_C identity, so shifted = R_read(m)). bits(32)
    values are non-negative 32-bit words: rendered as Z.land/Z.lor/Z.lxor
    on the unsigned views. *)
Definition sail_and_r (x y : I32.int) : I32.int :=
  I32.repr (Z.land (I32.unsigned x) (I32.unsigned y)).
Definition sail_orr_r (x y : I32.int) : I32.int :=
  I32.repr (Z.lor (I32.unsigned x) (I32.unsigned y)).
Definition sail_eor_r (x y : I32.int) : I32.int :=
  I32.repr (Z.lxor (I32.unsigned x) (I32.unsigned y)).

(** MVN (register): "not_vec(shifted)" (instrs32.sail:8066) — [sail_not]
    from round 1 is the transcription. *)

(** *** Transcription: Shift_C and the four shifter primitives

    [LSL_C] — builtins.sail:69:
      function LSL_C (x, shift) = {
          let carry_out = if shift > 0 & shift <= 'N then x['N - shift]
                          else bitzero;
          (sail_shiftleft(x, shift), [carry_out])
      }
    sail_shiftleft on bits(32) truncates to 32 bits: repr (Z.shiftl ux n). *)
Definition sail_lsl_c (x : I32.int) (shift : Z) : I32.int * bool :=
  (I32.repr (Z.shiftl (I32.unsigned x) shift),
   if (0 <? shift) && (shift <=? 32)
   then Z.testbit (I32.unsigned x) (32 - shift)
   else false).

(** [LSR_C] — builtins.sail:78:
      let carry_out = if shift > 0 & shift <= 'N then x[shift - 1]
                      else bitzero;
      (sail_shiftright(x, shift), [carry_out])
    sail_shiftright is the logical shift on the unsigned view. *)
Definition sail_lsr_c (x : I32.int) (shift : Z) : I32.int * bool :=
  (I32.repr (Z.shiftr (I32.unsigned x) shift),
   if (0 <? shift) && (shift <=? 32)
   then Z.testbit (I32.unsigned x) (shift - 1)
   else false).

(** [ASR_C] — builtins.sail:88:
      let carry_out = if shift == 0 | 'N == 0 then bitzero else
        if shift >= 'N then x['N - 1] else x['shift - 1];
      (sail_arith_shiftright(x, shift), [carry_out])
    sail_arith_shiftright shifts the sign-extended value: Z.shiftr (signed x). *)
Definition sail_asr_c (x : I32.int) (shift : Z) : I32.int * bool :=
  (I32.repr (Z.shiftr (I32.signed x) shift),
   if shift =? 0 then false
   else if 32 <=? shift then Z.testbit (I32.unsigned x) 31
   else Z.testbit (I32.unsigned x) (shift - 1)).

(** [ROR_C] — builtins.sail:99:
      let 'm = MOD(shift, 'N);
      let result : bits('N) = LSR(x, m) | LSL(x, 'N - m);
      let carry_out : bits(1) = [result['N - 1]];
    (LSR/LSL here are the truncating bit-vector shifts, no carry.) *)
Definition sail_ror_c (x : I32.int) (shift : Z) : I32.int * bool :=
  let m := shift mod 32 in
  let result := I32.or (I32.repr (Z.shiftr (I32.unsigned x) m))
                       (I32.repr (Z.shiftl (I32.unsigned x) (32 - m))) in
  (result, Z.testbit (I32.unsigned result) 31).

Inductive sail_srtype : Type :=
  | SRType_LSL_t
  | SRType_LSR_t
  | SRType_ASR_t
  | SRType_ROR_t.

(** [Shift_C] — v8_base.sail:41273:
      function Shift_C (value_name, srtype, amount, carry_in) = {
          assert(not_bool(srtype == SRType_RRX & amount != 1));
          if amount == 0 then {
              (result, carry_out) = (value_name, carry_in)
          } else { match srtype { SRType_LSL => LSL_C(value_name, amount),
                                  ... } };
      }
    SRType_RRX omitted (gap 10). The amount = 0 arm returns the input
    bits(32) unchanged — in the Z-rendering, the raw representative
    (see gap 7). *)
Definition sail_shift_c (x : I32.int) (t : sail_srtype) (amount : Z)
    (carry_in : bool) : I32.int * bool :=
  if amount =? 0 then (x, carry_in)
  else match t with
       | SRType_LSL_t => sail_lsl_c x amount
       | SRType_LSR_t => sail_lsr_c x amount
       | SRType_ASR_t => sail_asr_c x amount
       | SRType_ROR_t => sail_ror_c x amount
       end.

(** Register-controlled shift amount: "UInt(R_read(s)[7 .. 0])" — the low
    byte of the shift register (instrs32.sail:6909/7019/1357/10205). *)
Definition sail_shift_amount8 (r : I32.int) : Z :=
  I32.unsigned r mod 256.

(** MOVT: "[R_read(d) with 31 .. 16 = imm16]" (instrs32.sail:7722) — the
    high half becomes imm16, the low half is preserved. Rendered as the OR
    of the shifted 16-bit immediate and the low 16 bits of the old value. *)
Definition sail_movt_result (old imm16 : I32.int) : I32.int :=
  I32.repr (Z.lor (Z.shiftl (I32.unsigned imm16) 16)
                  (I32.unsigned old mod 65536)).

(** *** Arithmetic helpers (round 2) *)

Lemma unsigned_repr_small : forall n,
  0 <= n < I32.modulus -> I32.unsigned (I32.repr n) = n.
Proof.
  intros. unfold I32.unsigned, I32.repr.
  rewrite Zmod_mod. apply Z.mod_small. auto.
Qed.

Lemma unsigned_repr_unsigned : forall x,
  I32.unsigned (I32.repr (I32.unsigned x)) = I32.unsigned x.
Proof.
  intros. unfold I32.unsigned, I32.repr. rewrite !Zmod_mod. reflexivity.
Qed.

(** The signed representative reduces to the unsigned one mod 2^32. *)
Lemma signed_mod_modulus : forall x,
  I32.signed x mod I32.modulus = I32.unsigned x.
Proof.
  intros. unfold I32.signed. cbv zeta.
  pose proof (unsigned_range x) as Hx.
  destruct (Z.ltb_spec (I32.unsigned x) I32.half_modulus).
  - apply Z.mod_small. lia.
  - replace (I32.unsigned x - I32.modulus)
      with (I32.unsigned x + (-1) * I32.modulus) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(** mod 2^32 distributes over the bitwise operations (bit-extensionality). *)
Lemma land_mod_modulus : forall a b,
  Z.land a b mod I32.modulus
  = Z.land (a mod I32.modulus) (b mod I32.modulus).
Proof.
  intros. unfold I32.modulus.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec i 32) as [L | L].
  - rewrite Z.mod_pow2_bits_low by lia.
    rewrite !Z.land_spec.
    rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.land_spec.
    rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lor_mod_modulus : forall a b,
  Z.lor a b mod I32.modulus
  = Z.lor (a mod I32.modulus) (b mod I32.modulus).
Proof.
  intros. unfold I32.modulus.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec i 32) as [L | L].
  - rewrite Z.mod_pow2_bits_low by lia.
    rewrite !Z.lor_spec.
    rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.lor_spec.
    rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lxor_mod_modulus : forall a b,
  Z.lxor a b mod I32.modulus
  = Z.lxor (a mod I32.modulus) (b mod I32.modulus).
Proof.
  intros. unfold I32.modulus.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec i 32) as [L | L].
  - rewrite Z.mod_pow2_bits_low by lia.
    rewrite !Z.lxor_spec.
    rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.lxor_spec.
    rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(** Shifting the canonical representative left is shifting the raw one. *)
Lemma repr_shiftl_unsigned : forall x n,
  0 <= n ->
  I32.repr (Z.shiftl (I32.unsigned x) n) = I32.repr (Z.shiftl x n).
Proof.
  intros x n Hn. unfold I32.repr, I32.unsigned.
  rewrite !Z.shiftl_mul_pow2 by lia.
  apply Z.mul_mod_idemp_l. apply modulus_nz.
Qed.

(** Sum of three with the first two canonicalized. *)
Lemma mod3_add : forall a b c,
  (a mod I32.modulus + b mod I32.modulus + c) mod I32.modulus
  = (a + b + c) mod I32.modulus.
Proof.
  intros.
  rewrite Zplus_mod.
  rewrite (Zplus_mod (a mod I32.modulus) (b mod I32.modulus)).
  rewrite !Zmod_mod.
  rewrite (Zplus_mod (a + b) c).
  rewrite (Zplus_mod a b).
  reflexivity.
Qed.

(** The RSB representative: (NOT x) + y + 1 = y - x on the unsigned view. *)
Lemma repr_rsb_unsigned : forall x y : I32.int,
  I32.repr ((I32.modulus - 1 - I32.unsigned x) + I32.unsigned y + 1)
  = I32.sub y x.
Proof.
  intros. unfold I32.sub, I32.repr, I32.unsigned.
  replace (I32.modulus - 1 - x mod I32.modulus + y mod I32.modulus + 1)
    with ((y mod I32.modulus - x mod I32.modulus) + 1 * I32.modulus) by lia.
  rewrite Z_mod_plus_full.
  rewrite <- Zminus_mod. reflexivity.
Qed.

(** Difference of three with the first two canonicalized. *)
Lemma mod3_sub : forall a b c,
  (a mod I32.modulus - b mod I32.modulus - c) mod I32.modulus
  = (a - b - c) mod I32.modulus.
Proof.
  intros.
  rewrite (Zminus_mod (a mod I32.modulus - b mod I32.modulus) c).
  rewrite <- (Zminus_mod a b).
  rewrite <- Zminus_mod.
  reflexivity.
Qed.

(** The SBC borrow representative: x + (NOT y) + 0 = x - y - 1. *)
Lemma repr_sbc_borrow_unsigned : forall x y : I32.int,
  I32.repr (I32.unsigned x + (I32.modulus - 1 - I32.unsigned y) + 0)
  = I32.sub (I32.sub x y) I32.one.
Proof.
  intros. unfold I32.sub, I32.one, I32.repr, I32.unsigned.
  replace (x mod I32.modulus + (I32.modulus - 1 - y mod I32.modulus) + 0)
    with ((x mod I32.modulus - y mod I32.modulus - 1) + 1 * I32.modulus)
    by lia.
  rewrite Z_mod_plus_full.
  rewrite mod3_sub.
  rewrite (Z.mod_small 1) by (rewrite modulus_val; lia).
  rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

(** Shift-by-small-immediate collapses the operand-masking in I32.shl etc. *)
Lemma shl_repr_small : forall x n,
  0 <= n < 32 ->
  I32.shl x (I32.repr n) = I32.repr (Z.shiftl x n).
Proof.
  intros x n Hn. unfold I32.shl.
  rewrite unsigned_repr_small by (rewrite modulus_val; lia).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma shru_repr_small : forall x n,
  0 <= n < 32 ->
  I32.shru x (I32.repr n) = I32.repr (Z.shiftr (I32.unsigned x) n).
Proof.
  intros x n Hn. unfold I32.shru.
  rewrite unsigned_repr_small by (rewrite modulus_val; lia).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma shrs_repr_small : forall x n,
  0 <= n < 32 ->
  I32.shrs x (I32.repr n) = I32.repr (Z.shiftr (I32.signed x) n).
Proof.
  intros x n Hn. unfold I32.shrs.
  rewrite unsigned_repr_small by (rewrite modulus_val; lia).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(** Normalizing the shift-amount register through repr/unsigned is invisible
    to the I32 shift operations (they only read the unsigned view). *)
Lemma shl_amt_norm : forall x y,
  I32.shl x (I32.repr (I32.unsigned y)) = I32.shl x y.
Proof.
  intros. unfold I32.shl. rewrite unsigned_repr_unsigned. reflexivity.
Qed.

Lemma shru_amt_norm : forall x y,
  I32.shru x (I32.repr (I32.unsigned y)) = I32.shru x y.
Proof.
  intros. unfold I32.shru. rewrite unsigned_repr_unsigned. reflexivity.
Qed.

Lemma shrs_amt_norm : forall x y,
  I32.shrs x (I32.repr (I32.unsigned y)) = I32.shrs x y.
Proof.
  intros. unfold I32.shrs. rewrite unsigned_repr_unsigned. reflexivity.
Qed.

Lemma rotr_amt_norm : forall x y,
  I32.rotr x (I32.repr (I32.unsigned y)) = I32.rotr x y.
Proof.
  intros. unfold I32.rotr. rewrite unsigned_repr_unsigned. reflexivity.
Qed.

(** *** Value bridges: AddWithCarry family *)

(** SUB's AddWithCarry(x, NOT y, '1') result equals our I32.sub. *)
Lemma sail_sub_r_result_eq : forall x y,
  sail_sub_r_result x y = I32.sub x y.
Proof.
  intros. unfold sail_sub_r_result, sail_add_with_carry.
  cbv beta iota zeta. cbn [fst].
  rewrite unsigned_not. apply repr_sub_unsigned.
Qed.

(** SUB's flags are CMP's flags (same AddWithCarry call) — proven in round 1. *)
Lemma sail_sub_r_flags_eq : forall x y,
  sail_sub_r_flags x y
  = update_flags_arith (I32.sub x y) (compute_c_flag_sub x y)
                       (compute_v_flag_sub x y).
Proof.
  exact sail_cmp_r_flags_eq.
Qed.

(** CMN's flags are ADDS's flags (same AddWithCarry call) — round 1 again. *)
Lemma sail_cmn_r_flags_eq : forall x y,
  sail_cmn_r_flags x y
  = update_flags_arith (I32.add x y) (compute_c_flag_add x y)
                       (compute_v_flag_add x y (I32.add x y)).
Proof.
  exact sail_add_r_flags_eq.
Qed.

(** RSB's AddWithCarry(NOT x, y, '1') result equals our I32.sub y x. *)
Lemma sail_rsb_r_result_eq : forall x y,
  sail_rsb_r_result x y = I32.sub y x.
Proof.
  intros. unfold sail_rsb_r_result, sail_add_with_carry.
  cbv beta iota zeta. cbn [fst].
  rewrite unsigned_not. apply repr_rsb_unsigned.
Qed.

(** ADC's AddWithCarry(x, y, C) result equals our (x + y) + C. *)
Lemma sail_adc_r_result_eq : forall x y c,
  sail_adc_r_result x y c
  = I32.add (I32.add x y) (if c then I32.one else I32.zero).
Proof.
  intros. destruct c;
    unfold sail_adc_r_result, sail_add_with_carry;
    cbv beta iota zeta; cbn [fst];
    unfold I32.add, I32.one, I32.zero, I32.repr, I32.unsigned;
    rewrite mod3_add; rewrite <- Zplus_mod; reflexivity.
Qed.

(** SBC's AddWithCarry(x, NOT y, C) result equals our (x - y) - NOT(C). *)
Lemma sail_sbc_r_result_eq : forall x y c,
  sail_sbc_r_result x y c
  = I32.sub (I32.sub x y) (if c then I32.zero else I32.one).
Proof.
  intros. destruct c;
    unfold sail_sbc_r_result, sail_add_with_carry;
    cbv beta iota zeta; cbn [fst];
    rewrite unsigned_not.
  - (* carry set: x + NOT y + 1 = x - y; subtracting zero renormalizes *)
    rewrite repr_sub_unsigned.
    unfold I32.sub, I32.zero, I32.repr, I32.unsigned.
    rewrite (Z.mod_small 0) by (rewrite modulus_val; lia).
    rewrite Z.sub_0_r. rewrite Zmod_mod. reflexivity.
  - (* carry clear: x + NOT y + 0 = x - y - 1 *)
    apply repr_sbc_borrow_unsigned.
Qed.

(** *** Value bridges: flag-free ALU *)

(** Sail's bits(32) AND on canonical representatives equals I32.and on raw
    ones — mod 2^32 distributes over Z.land. *)
Lemma sail_and_r_eq : forall x y, sail_and_r x y = I32.and x y.
Proof.
  intros. unfold sail_and_r, I32.and, I32.repr, I32.unsigned.
  rewrite <- land_mod_modulus. apply Zmod_mod.
Qed.

Lemma sail_orr_r_eq : forall x y, sail_orr_r x y = I32.or x y.
Proof.
  intros. unfold sail_orr_r, I32.or, I32.repr, I32.unsigned.
  rewrite <- lor_mod_modulus. apply Zmod_mod.
Qed.

Lemma sail_eor_r_eq : forall x y, sail_eor_r x y = I32.xor x y.
Proof.
  intros. unfold sail_eor_r, I32.xor, I32.repr, I32.unsigned.
  rewrite <- lxor_mod_modulus. apply Zmod_mod.
Qed.

(** *** Value bridges: Shift_C at amounts 1..31 *)

Lemma sail_shift_c_lsl_eq : forall x n cin,
  0 < n < 32 ->
  fst (sail_shift_c x SRType_LSL_t n cin) = I32.shl x (I32.repr n).
Proof.
  intros x n cin Hn. unfold sail_shift_c.
  destruct (Z.eqb_spec n 0); [lia |].
  unfold sail_lsl_c. cbn [fst].
  rewrite shl_repr_small by lia.
  apply repr_shiftl_unsigned. lia.
Qed.

Lemma sail_shift_c_lsr_eq : forall x n cin,
  0 < n < 32 ->
  fst (sail_shift_c x SRType_LSR_t n cin) = I32.shru x (I32.repr n).
Proof.
  intros x n cin Hn. unfold sail_shift_c.
  destruct (Z.eqb_spec n 0); [lia |].
  unfold sail_lsr_c. cbn [fst].
  rewrite shru_repr_small by lia. reflexivity.
Qed.

Lemma sail_shift_c_asr_eq : forall x n cin,
  0 < n < 32 ->
  fst (sail_shift_c x SRType_ASR_t n cin) = I32.shrs x (I32.repr n).
Proof.
  intros x n cin Hn. unfold sail_shift_c.
  destruct (Z.eqb_spec n 0); [lia |].
  unfold sail_asr_c. cbn [fst].
  rewrite shrs_repr_small by lia. reflexivity.
Qed.

Lemma sail_shift_c_ror_eq : forall x n cin,
  0 < n < 32 ->
  fst (sail_shift_c x SRType_ROR_t n cin) = I32.rotr x (I32.repr n).
Proof.
  intros x n cin Hn. unfold sail_shift_c.
  destruct (Z.eqb_spec n 0); [lia |].
  unfold sail_ror_c. cbv zeta. cbn [fst].
  unfold I32.rotr.
  rewrite unsigned_repr_small by (rewrite modulus_val; lia).
  rewrite (Z.mod_small n 32) by lia.
  rewrite shru_repr_small by lia.
  rewrite shl_repr_small by lia.
  rewrite (repr_shiftl_unsigned x (32 - n)) by lia.
  reflexivity.
Qed.

(** Shift_C at amount 0 is the identity on the value (raw representative). *)
Lemma sail_shift_c_zero : forall x t cin,
  fst (sail_shift_c x t 0 cin) = x.
Proof.
  intros. reflexivity.
Qed.

(** *** Whole-instruction bridge theorems — AddWithCarry family *)

(** SUB (register), setflags = false. Register write agrees EXACTLY. *)
Theorem sail_bridge_sub_reg : forall s rd rn rm,
  exec_instr (SUB rd rn (Reg rm)) s
  = Some (set_reg s rd (sail_sub_r_result (get_reg s rn) (get_reg s rm))).
Proof.
  intros. rewrite sail_sub_r_result_eq. reflexivity.
Qed.

(** SUBS (register): register write AND all four NZCV flags agree EXACTLY. *)
Theorem sail_bridge_subs_reg : forall s rd rn rm,
  exec_instr (SUBS rd rn (Reg rm)) s
  = Some (set_flags
            (set_reg s rd (sail_sub_r_result (get_reg s rn) (get_reg s rm)))
            (sail_sub_r_flags (get_reg s rn) (get_reg s rm))).
Proof.
  intros. rewrite sail_sub_r_result_eq, sail_sub_r_flags_eq. reflexivity.
Qed.

(** CMN (register): flags-only, all four NZCV agree EXACTLY. *)
Theorem sail_bridge_cmn_reg : forall s rn rm,
  exec_instr (CMN rn (Reg rm)) s
  = Some (set_flags s (sail_cmn_r_flags (get_reg s rn) (get_reg s rm))).
Proof.
  intros. rewrite sail_cmn_r_flags_eq. reflexivity.
Qed.

(** RSB (register), setflags = false (ArmSemantics.v has no RSBS). *)
Theorem sail_bridge_rsb_reg : forall s rd rn rm,
  exec_instr (RSB rd rn (Reg rm)) s
  = Some (set_reg s rd (sail_rsb_r_result (get_reg s rn) (get_reg s rm))).
Proof.
  intros. rewrite sail_rsb_r_result_eq. reflexivity.
Qed.

(** ADC (register), setflags = false: the carry_in is the LIVE C flag —
    exactly what the i64 lo/hi pair codegen (ADDS;ADC) relies on. *)
Theorem sail_bridge_adc_reg : forall s rd rn rm,
  exec_instr (ADC rd rn (Reg rm)) s
  = Some (set_reg s rd
            (sail_adc_r_result (get_reg s rn) (get_reg s rm)
                               (s.(flags).(flag_c)))).
Proof.
  intros. rewrite sail_adc_r_result_eq. reflexivity.
Qed.

(** SBC (register), setflags = false: borrow = NOT(C), the SUBS;SBC pair. *)
Theorem sail_bridge_sbc_reg : forall s rd rn rm,
  exec_instr (SBC rd rn (Reg rm)) s
  = Some (set_reg s rd
            (sail_sbc_r_result (get_reg s rn) (get_reg s rm)
                               (s.(flags).(flag_c)))).
Proof.
  intros. rewrite sail_sbc_r_result_eq. reflexivity.
Qed.

(** *** Whole-instruction bridge theorems — flag-free ALU *)

Theorem sail_bridge_and_reg : forall s rd rn rm,
  exec_instr (AND rd rn (Reg rm)) s
  = Some (set_reg s rd (sail_and_r (get_reg s rn) (get_reg s rm))).
Proof.
  intros. rewrite sail_and_r_eq. reflexivity.
Qed.

Theorem sail_bridge_orr_reg : forall s rd rn rm,
  exec_instr (ORR rd rn (Reg rm)) s
  = Some (set_reg s rd (sail_orr_r (get_reg s rn) (get_reg s rm))).
Proof.
  intros. rewrite sail_orr_r_eq. reflexivity.
Qed.

Theorem sail_bridge_eor_reg : forall s rd rn rm,
  exec_instr (EOR rd rn (Reg rm)) s
  = Some (set_reg s rd (sail_eor_r (get_reg s rn) (get_reg s rm))).
Proof.
  intros. rewrite sail_eor_r_eq. reflexivity.
Qed.

(** MVN (register): our MVN and the round-1 [sail_not] transcription are the
    same Z-rendering — the bridge records the correspondence at the
    instruction level. *)
Theorem sail_bridge_mvn_reg : forall s rd rm,
  exec_instr (MVN rd (Reg rm)) s
  = Some (set_reg s rd (sail_not (get_reg s rm))).
Proof.
  intros. reflexivity.
Qed.

(** *** Whole-instruction bridge theorems — shifts (immediate forms) *)

Theorem sail_bridge_lsl_imm : forall s rd rm shift cin,
  (0 < shift < 32)%nat ->
  exec_instr (LSL rd rm shift) s
  = Some (set_reg s rd
            (fst (sail_shift_c (get_reg s rm) SRType_LSL_t
                               (Z.of_nat shift) cin))).
Proof.
  intros. rewrite sail_shift_c_lsl_eq by lia. reflexivity.
Qed.

Theorem sail_bridge_lsr_imm : forall s rd rm shift cin,
  (0 < shift < 32)%nat ->
  exec_instr (LSR rd rm shift) s
  = Some (set_reg s rd
            (fst (sail_shift_c (get_reg s rm) SRType_LSR_t
                               (Z.of_nat shift) cin))).
Proof.
  intros. rewrite sail_shift_c_lsr_eq by lia. reflexivity.
Qed.

Theorem sail_bridge_asr_imm : forall s rd rm shift cin,
  (0 < shift < 32)%nat ->
  exec_instr (ASR rd rm shift) s
  = Some (set_reg s rd
            (fst (sail_shift_c (get_reg s rm) SRType_ASR_t
                               (Z.of_nat shift) cin))).
Proof.
  intros. rewrite sail_shift_c_asr_eq by lia. reflexivity.
Qed.

(** ROR (immediate) is MOV (register) with shift_t = SRType_ROR (see the
    provenance table: DecodeImmShift stype 0b11, imm5 <> 0). *)
Theorem sail_bridge_ror_imm : forall s rd rm shift cin,
  (0 < shift < 32)%nat ->
  exec_instr (ROR rd rm shift) s
  = Some (set_reg s rd
            (fst (sail_shift_c (get_reg s rm) SRType_ROR_t
                               (Z.of_nat shift) cin))).
Proof.
  intros. rewrite sail_shift_c_ror_eq by lia. reflexivity.
Qed.

(** *** Whole-instruction bridge theorems — shifts (register forms)

    Hypothesis 0 < UInt(R[s]) < 32 per gap 7: within it, the low-byte
    extraction UInt(R[s]<7:0>) is the identity and Sail's shift agrees with
    the mod-32 model. WASM lowerings always mask the amount first. *)

Theorem sail_bridge_lsl_reg : forall s rd rn rs cin,
  0 < I32.unsigned (get_reg s rs) < 32 ->
  exec_instr (LSL_reg rd rn rs) s
  = Some (set_reg s rd
            (fst (sail_shift_c (get_reg s rn) SRType_LSL_t
                               (sail_shift_amount8 (get_reg s rs)) cin))).
Proof.
  intros s rd rn rs cin H.
  unfold sail_shift_amount8. rewrite Z.mod_small by lia.
  rewrite sail_shift_c_lsl_eq by lia.
  rewrite shl_amt_norm. reflexivity.
Qed.

Theorem sail_bridge_lsr_reg : forall s rd rn rs cin,
  0 < I32.unsigned (get_reg s rs) < 32 ->
  exec_instr (LSR_reg rd rn rs) s
  = Some (set_reg s rd
            (fst (sail_shift_c (get_reg s rn) SRType_LSR_t
                               (sail_shift_amount8 (get_reg s rs)) cin))).
Proof.
  intros s rd rn rs cin H.
  unfold sail_shift_amount8. rewrite Z.mod_small by lia.
  rewrite sail_shift_c_lsr_eq by lia.
  rewrite shru_amt_norm. reflexivity.
Qed.

Theorem sail_bridge_asr_reg : forall s rd rn rs cin,
  0 < I32.unsigned (get_reg s rs) < 32 ->
  exec_instr (ASR_reg rd rn rs) s
  = Some (set_reg s rd
            (fst (sail_shift_c (get_reg s rn) SRType_ASR_t
                               (sail_shift_amount8 (get_reg s rs)) cin))).
Proof.
  intros s rd rn rs cin H.
  unfold sail_shift_amount8. rewrite Z.mod_small by lia.
  rewrite sail_shift_c_asr_eq by lia.
  rewrite shrs_amt_norm. reflexivity.
Qed.

Theorem sail_bridge_ror_reg : forall s rd rn rs cin,
  0 < I32.unsigned (get_reg s rs) < 32 ->
  exec_instr (ROR_reg rd rn rs) s
  = Some (set_reg s rd
            (fst (sail_shift_c (get_reg s rn) SRType_ROR_t
                               (sail_shift_amount8 (get_reg s rs)) cin))).
Proof.
  intros s rd rn rs cin H.
  unfold sail_shift_amount8. rewrite Z.mod_small by lia.
  rewrite sail_shift_c_ror_eq by lia.
  rewrite rotr_amt_norm. reflexivity.
Qed.

(** *** Register shifts at amount 0 — unsigned-view agreement (gap 7)

    Shift_C returns the raw input; our shifts renormalize through repr.
    The two agree on I32.unsigned — the observation WASM values make —
    so the amount-0 case is bridged on that view. *)

Theorem sail_bridge_lsl_reg_zero : forall s rd rn rs cin,
  I32.unsigned (get_reg s rs) = 0 ->
  exists s',
    exec_instr (LSL_reg rd rn rs) s = Some s'
    /\ I32.unsigned (get_reg s' rd)
       = I32.unsigned (fst (sail_shift_c (get_reg s rn) SRType_LSL_t 0 cin)).
Proof.
  intros s rd rn rs cin H.
  eexists. split; [reflexivity |].
  rewrite get_set_reg_eq.
  rewrite sail_shift_c_zero.
  unfold I32.shl. rewrite H.
  rewrite Z.mod_0_l by lia.
  rewrite Z.shiftl_0_r.
  unfold I32.unsigned, I32.repr. apply Zmod_mod.
Qed.

Theorem sail_bridge_lsr_reg_zero : forall s rd rn rs cin,
  I32.unsigned (get_reg s rs) = 0 ->
  exists s',
    exec_instr (LSR_reg rd rn rs) s = Some s'
    /\ I32.unsigned (get_reg s' rd)
       = I32.unsigned (fst (sail_shift_c (get_reg s rn) SRType_LSR_t 0 cin)).
Proof.
  intros s rd rn rs cin H.
  eexists. split; [reflexivity |].
  rewrite get_set_reg_eq.
  rewrite sail_shift_c_zero.
  unfold I32.shru. rewrite H.
  rewrite Z.mod_0_l by lia.
  rewrite Z.shiftr_0_r.
  apply unsigned_repr_unsigned.
Qed.

Theorem sail_bridge_asr_reg_zero : forall s rd rn rs cin,
  I32.unsigned (get_reg s rs) = 0 ->
  exists s',
    exec_instr (ASR_reg rd rn rs) s = Some s'
    /\ I32.unsigned (get_reg s' rd)
       = I32.unsigned (fst (sail_shift_c (get_reg s rn) SRType_ASR_t 0 cin)).
Proof.
  intros s rd rn rs cin H.
  eexists. split; [reflexivity |].
  rewrite get_set_reg_eq.
  rewrite sail_shift_c_zero.
  unfold I32.shrs. rewrite H.
  rewrite Z.mod_0_l by lia.
  rewrite Z.shiftr_0_r.
  unfold I32.unsigned at 1. unfold I32.repr.
  rewrite Zmod_mod. apply signed_mod_modulus.
Qed.

Theorem sail_bridge_ror_reg_zero : forall s rd rn rs cin,
  I32.unsigned (get_reg s rs) = 0 ->
  exists s',
    exec_instr (ROR_reg rd rn rs) s = Some s'
    /\ I32.unsigned (get_reg s' rd)
       = I32.unsigned (fst (sail_shift_c (get_reg s rn) SRType_ROR_t 0 cin)).
Proof.
  intros s rd rn rs cin H.
  eexists. split; [reflexivity |].
  rewrite get_set_reg_eq.
  rewrite sail_shift_c_zero.
  unfold I32.rotr. cbv zeta. rewrite H.
  rewrite Z.mod_0_l by lia.
  rewrite Z.sub_0_r.
  rewrite shru_repr_small by lia.
  rewrite Z.shiftr_0_r.
  (* shl x (repr 32): the mod-32 mask makes it a shift by 0 *)
  unfold I32.shl.
  assert (H32 : I32.unsigned (I32.repr 32) = 32)
    by (apply unsigned_repr_small; rewrite modulus_val; lia).
  rewrite H32.
  rewrite Z_mod_same_full.
  rewrite Z.shiftl_0_r.
  unfold I32.or, I32.unsigned, I32.repr.
  rewrite !Zmod_mod.
  rewrite Z.lor_diag.
  apply Zmod_mod.
Qed.

(** *** Whole-instruction bridge theorems — moves *)

(** MOV (register) is MOV_r with shift_t = SRType_LSL, shift_n = 0: the
    result is the Shift_C identity on R[m]. *)
Theorem sail_bridge_mov_reg : forall s rd rm cin,
  exec_instr (MOV rd (Reg rm)) s
  = Some (set_reg s rd
            (fst (sail_shift_c (get_reg s rm) SRType_LSL_t 0 cin))).
Proof.
  intros. reflexivity.
Qed.

(** MOVW: MOV (immediate) with result = imm32 (gap 9: our MOVW carries the
    already-expanded imm32, so the execute clause is the identity on it). *)
Theorem sail_bridge_movw : forall s rd imm,
  exec_instr (MOVW rd imm) s = Some (set_reg s rd imm).
Proof.
  intros. reflexivity.
Qed.

(** MOVT bitfield-insert equals our AND/OR/SHL formulation, for encodable
    (16-bit) immediates. *)
Lemma sail_movt_result_eq : forall old imm,
  0 <= I32.unsigned imm < 65536 ->
  sail_movt_result old imm
  = I32.or (I32.and old (I32.repr 0xFFFF)) (I32.shl imm (I32.repr 16)).
Proof.
  intros old imm Himm.
  (* the AND mask: Z.land old 0xFFFF = old mod 65536 (Z.land_ones) *)
  assert (HA : Z.land old (I32.repr 65535) = old mod 65536).
  { change (I32.repr 65535) with (Z.ones 16).
    rewrite Z.land_ones by lia.
    change (2 ^ 16) with 65536. reflexivity. }
  (* low half: (old mod 2^32) mod 2^16 = old mod 2^16 *)
  assert (Hlow : I32.unsigned old mod 65536 = old mod 65536).
  { unfold I32.unsigned, I32.modulus.
    change 65536 with (2 ^ 16).
    rewrite <- !Z.land_ones by lia.
    rewrite <- Z.land_assoc.
    change (Z.land (Z.ones 32) (Z.ones 16)) with (Z.ones 16).
    reflexivity. }
  (* high half: shifting the canonical representative = shifting raw *)
  assert (HC : I32.shl imm (I32.repr 16)
               = I32.repr (Z.shiftl (I32.unsigned imm) 16)).
  { rewrite shl_repr_small by lia.
    symmetry. apply repr_shiftl_unsigned. lia. }
  assert (Hb : 0 <= old mod 65536 < 65536)
    by (apply Z.mod_pos_bound; lia).
  unfold sail_movt_result, I32.or, I32.and.
  rewrite HC, HA, Hlow.
  unfold I32.repr.
  rewrite (Z.mod_small (old mod 65536)) by (rewrite modulus_val; lia).
  rewrite (Z.mod_small (Z.shiftl (I32.unsigned imm) 16))
    by (rewrite Z.shiftl_mul_pow2 by lia;
        change (2 ^ 16) with 65536; rewrite modulus_val; lia).
  rewrite Z.lor_comm. reflexivity.
Qed.

(** MOVT: the destination's high half becomes imm16, low half preserved. *)
Theorem sail_bridge_movt : forall s rd imm,
  0 <= I32.unsigned imm < 65536 ->
  exec_instr (MOVT rd imm) s
  = Some (set_reg s rd (sail_movt_result (get_reg s rd) imm)).
Proof.
  intros. rewrite sail_movt_result_eq by auto. reflexivity.
Qed.

(** ** ROUND 3 — SBCS (flags-writing SBC) + conditional execution (CMPcc)

    Same pin as rounds 1–2: rems-project/sail-arm @ master (commit
    1bf2e5574ba9, 2026-06-19), model arm-v9.4-a. This round anchors the two
    executor capabilities the VCR-SEL-001 increment-4 holdout named
    (docs/design/vcr-sel-001-increment-4.md): the dual-precision i64 compare
    chain's SBCS link and the conditionally-executed CMP (CMPEQ) link.

    Execute-clause provenance:

      - execute SBC (register), setflags = true   instrs32.sail:10946
        "(result, nzcv) = AddWithCarry(R_read(n), not_vec(shifted), PSTATE.C);
         ... if setflags then (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = nzcv"
        — the SAME AddWithCarry call round 2 bridged for SBC's result; round 3
        adds the nzcv write. No new transcription is needed: the flag tuple of
        [sail_add_with_carry x (sail_not y) c] IS the ASL output.
      - ConditionHolds                            v8_base.sail
        (function ConditionHolds(cond): the case table on cond<3:1> —
         '000' Z / '001' C / '010' N / '011' V / '100' C && !Z /
         '101' N == V / '110' N == V && !Z / '111' TRUE — with the final
         "if cond<0> == '1' && cond != '1111' then result = !result" invert
         bit). Every conditional A32 instruction executes under
        "if ConditionPassed() then ..."; a false condition leaves the whole
        state (registers AND PSTATE.NZCV) untouched. CMPEQ is the CMP
        (register) execute clause under ConditionHolds(EQ).

    ADDITIONAL ABSTRACTION GAP:

     11. [sail_condition_holds] is indexed by the [condition] inductive, not
         by the bits(4) encoding: the cond<3:1> grouping and the cond<0>
         invert bit are transcribed per constructor (EQ=0000 .. AL=1110).
         The '1111' arm (unconditional in A32) has no [condition]
         constructor on the Rocq side — synth never emits it. *)

(** [ConditionHolds] transcription. The [base] match is the case table on
    cond<3:1> (each pair of constructors shares a row); the outer match is
    the cond<0> invert bit (NE/CC/PL/VC/LS/LT/LE are the odd encodings). *)
Definition sail_condition_holds (cond : condition) (f : condition_flags)
    : bool :=
  let n := f.(flag_n) in let z := f.(flag_z) in
  let c := f.(flag_c) in let v := f.(flag_v) in
  let base :=
    match cond with
    | Cond_EQ | Cond_NE => z
    | Cond_CS | Cond_CC => c
    | Cond_MI | Cond_PL => n
    | Cond_VS | Cond_VC => v
    | Cond_HI | Cond_LS => c && negb z
    | Cond_GE | Cond_LT => Bool.eqb n v
    | Cond_GT | Cond_LE => Bool.eqb n v && negb z
    | Cond_AL => true
    end in
  match cond with
  | Cond_NE | Cond_CC | Cond_PL | Cond_VC | Cond_LS | Cond_LT | Cond_LE =>
      negb base
  | _ => base
  end.

(** The transcribed ConditionHolds equals the hand-written eval_condition —
    the foundation under every MOVcc arm and the new CMPCond. *)
Lemma sail_condition_holds_eq : forall cond f,
  sail_condition_holds cond f = eval_condition cond f.
Proof.
  intros cond f.
  destruct cond; unfold sail_condition_holds, eval_condition; cbv zeta;
    destruct (flag_n f), (flag_z f), (flag_c f), (flag_v f); reflexivity.
Qed.

(** *** Transcription: SBCS flags

    The nzcv tuple of AddWithCarry(x, NOT y, C) — the flags companion of
    round 2's [sail_sbc_r_result]. *)
Definition sail_sbcs_r_flags (rn_val rm_val : I32.int) (c : bool)
    : condition_flags :=
  let '(_, (n, z, cc, v)) :=
    sail_add_with_carry rn_val (sail_not rm_val) c in
  mkFlags n z cc v.

(** *** Arithmetic helpers (round 3) *)

(** Subtracting I32.zero renormalizes but does not change the value. *)
Lemma sub_sub_zero : forall x y : I32.int,
  I32.sub (I32.sub x y) I32.zero = I32.sub x y.
Proof.
  intros. unfold I32.sub, I32.zero, I32.repr.
  rewrite (Z.mod_small 0) by (rewrite modulus_val; lia).
  rewrite Z.sub_0_r. apply Zmod_mod.
Qed.

(** The SBCS result representative, both carry cases at once:
    x + NOT(y) + C = x - y - (1 - C). *)
Lemma repr_sbc_unsigned : forall (x y : I32.int) (c : bool),
  I32.repr (I32.unsigned x + (I32.modulus - 1 - I32.unsigned y)
            + (if c then 1 else 0))
  = I32.sub (I32.sub x y) (if c then I32.zero else I32.one).
Proof.
  intros. destruct c.
  - rewrite sub_sub_zero. apply repr_sub_unsigned.
  - apply repr_sbc_borrow_unsigned.
Qed.

(** The unsigned view of the SBCS result is the exact difference mod 2^32. *)
Lemma unsigned_sbc_result : forall (x y : I32.int) (c : bool),
  I32.unsigned (I32.sub (I32.sub x y) (if c then I32.zero else I32.one))
  = (I32.unsigned x - I32.unsigned y - (if c then 0 else 1)) mod I32.modulus.
Proof.
  intros. destruct c.
  - rewrite sub_sub_zero.
    unfold I32.sub, I32.repr, I32.unsigned.
    rewrite Zmod_mod, Z.sub_0_r. apply Zminus_mod.
  - unfold I32.sub, I32.one, I32.repr, I32.unsigned.
    rewrite !Zmod_mod.
    rewrite (Z.mod_small 1) by (rewrite modulus_val; lia).
    rewrite Zminus_mod_idemp_l.
    rewrite <- mod3_sub. reflexivity.
Qed.

(** *** Per-flag bridges: SBCS *)

(** C (SBCS): ASL "UInt(result) != UInt(x) + UInt(NOT y) + UInt(C)"
    ≡ the borrow-aware no-borrow test "uy + borrow <= ux". *)
Lemma sail_bridge_c_flag_sbc : forall (x y : I32.int) (c : bool),
  negb (I32.unsigned (I32.sub (I32.sub x y) (if c then I32.zero else I32.one))
        =? I32.unsigned x + (I32.modulus - 1 - I32.unsigned y)
           + (if c then 1 else 0))
  = compute_c_flag_sbc x y c.
Proof.
  intros.
  pose proof (unsigned_range x) as Hx.
  pose proof (unsigned_range y) as Hy.
  rewrite unsigned_sbc_result.
  unfold compute_c_flag_sbc. cbv zeta.
  set (b := if c then 0 else 1).
  assert (Hb : 0 <= b <= 1) by (unfold b; destruct c; lia).
  assert (Hcarry : (if c then 1 else 0) = 1 - b)
    by (unfold b; destruct c; lia).
  rewrite Hcarry.
  set (d := I32.unsigned x - I32.unsigned y - b).
  replace (I32.unsigned x + (I32.modulus - 1 - I32.unsigned y) + (1 - b))
    with (d + I32.modulus) by (unfold d; lia).
  destruct (Z_le_gt_dec 0 d) as [L | G].
  - rewrite Z.mod_small by (unfold d in *; lia).
    unfold d in *. bool_blast.
  - assert (E : d mod I32.modulus = d + I32.modulus).
    { assert (Hrw : d = (d + I32.modulus) + (-1) * I32.modulus) by lia.
      rewrite Hrw at 1.
      rewrite Z_mod_plus_full. apply Z.mod_small. unfold d in *. lia. }
    rewrite E. unfold d in *. bool_blast.
Qed.

(** V (SBCS): ASL "SInt(result) != SInt(x) + SInt(NOT y) + UInt(C)"
    ≡ compute_v_flag_sbc's "signed result differs from the exact signed
    difference" — the transcription IS the definition, modulo rearranging
    sx + (-1 - sy) + C into sx - sy - (1 - C). *)
Lemma sail_bridge_v_flag_sbc : forall (x y : I32.int) (c : bool),
  negb (I32.signed (I32.sub (I32.sub x y) (if c then I32.zero else I32.one))
        =? I32.signed x + (- 1 - I32.signed y) + (if c then 1 else 0))
  = compute_v_flag_sbc x y c.
Proof.
  intros. unfold compute_v_flag_sbc. cbv zeta.
  destruct c; do 2 f_equal; lia.
Qed.

(** *** Whole-flags and whole-instruction bridges: SBCS *)

(** The transcribed AddWithCarry(x, NOT y, C) NZCV equals the executor's
    borrow-aware SBCS flag computation. *)
Lemma sail_sbcs_r_flags_eq : forall x y c,
  sail_sbcs_r_flags x y c
  = update_flags_arith
      (I32.sub (I32.sub x y) (if c then I32.zero else I32.one))
      (compute_c_flag_sbc x y c)
      (compute_v_flag_sbc x y c).
Proof.
  intros. unfold sail_sbcs_r_flags, sail_add_with_carry.
  cbv beta iota zeta.
  rewrite unsigned_not, signed_not.
  rewrite repr_sbc_unsigned.
  unfold update_flags_arith.
  f_equal.
  - apply sail_bridge_n_flag.
  - apply sail_bridge_c_flag_sbc.
  - apply sail_bridge_v_flag_sbc.
Qed.

(** SBCS (register): result register AND all four NZCV flags agree EXACTLY
    with ASL's AddWithCarry(R[n], NOT(R[m]), PSTATE.C) + setflags write.
    This is the anchor for the new executor SBCS case — the semantics is
    transcribed, not invented. *)
Theorem sail_bridge_sbcs_reg : forall s rd rn rm,
  exec_instr (SBCS rd rn (Reg rm)) s
  = Some (set_flags
            (set_reg s rd
               (sail_sbc_r_result (get_reg s rn) (get_reg s rm)
                                  (s.(flags).(flag_c))))
            (sail_sbcs_r_flags (get_reg s rn) (get_reg s rm)
                               (s.(flags).(flag_c)))).
Proof.
  intros. rewrite sail_sbc_r_result_eq, sail_sbcs_r_flags_eq. reflexivity.
Qed.

(** *** Consistency: at carry-in = true the three-operand SBCS helpers
    collapse to the two-operand SUBS/CMP helpers (borrow = 0) — the new
    flag math agrees with the already-bridged old flag math on the shared
    boundary. *)

Lemma sbc_flags_carry_set_c : forall x y,
  compute_c_flag_sbc x y true = compute_c_flag_sub x y.
Proof.
  intros. unfold compute_c_flag_sbc, compute_c_flag_sub. cbv zeta.
  rewrite Z.add_0_r. reflexivity.
Qed.

Lemma sbc_flags_carry_set_v : forall x y,
  compute_v_flag_sbc x y true = compute_v_flag_sub x y.
Proof.
  intros.
  rewrite <- (sail_bridge_v_flag_sbc x y true).
  rewrite sub_sub_zero.
  replace (I32.signed x + (- 1 - I32.signed y) + (if true then 1 else 0))
    with (I32.signed x + (- 1 - I32.signed y) + 1) by reflexivity.
  apply sail_bridge_v_flag_sub.
Qed.

(** *** Whole-instruction bridge: conditionally-executed CMP (CMPcc)

    ASL: "if ConditionPassed() then ... AddWithCarry(R[n], NOT(shifted), '1')
    (flags only)"; a false condition leaves the state untouched. The bridge
    routes the condition through the transcribed [sail_condition_holds] and
    the flags through round 1's fully-bridged [sail_cmp_r_flags]. *)
Theorem sail_bridge_cmp_cond_reg : forall s cond rn rm,
  exec_instr (CMPCond cond rn (Reg rm)) s
  = if sail_condition_holds cond s.(flags)
    then Some (set_flags s (sail_cmp_r_flags (get_reg s rn) (get_reg s rm)))
    else Some s.
Proof.
  intros. cbn [exec_instr].
  rewrite (sail_condition_holds_eq cond (flags s)).
  destruct (eval_condition cond (flags s)).
  - rewrite sail_cmp_r_flags_eq. reflexivity.
  - reflexivity.
Qed.
