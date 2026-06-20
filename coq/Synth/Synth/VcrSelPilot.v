(** * VCR-SEL-001 pilot: register-polymorphic i32 binop lowering

    The North Star verified-selector DSL (VCR-SEL-001) needs lowering rules that
    are correct for an ARBITRARY register assignment — VCR-RA-001 (landed) picks
    the registers, VCR-RA-003 (landed) validates the assignment, so the lowering
    rule must hold for any (rd, rn, rm), not just the hardcoded R0/R1/R2 of the
    monolithic [compile_wasm_to_arm].

    GO/ABANDON MEASUREMENT (the artifact's >=70%-auto-discharge kill-criterion):
    does the EXISTING [synth_binop_proof] strategy still close the proof once the
    rule is lifted from fixed R0/R1 to universally-quantified registers —
    INCLUDING every aliasing case (rd = rn in-place reuse, rd = rm, all distinct)?
    Universal quantification over rd/rn/rm covers all aliasings in one lemma, so a
    single Qed per op = the strategy survives generalization for that op.

    [synth_binop_proof_poly] below is a VERBATIM copy of [synth_binop_proof]
    (Tactics.v) except the [unfold compile_wasm_to_arm] is replaced by unfolding
    the register-polymorphic lowerings — i.e. the discharge STEPS (intros, simpl,
    rewrite the two operand hypotheses, [get_set_reg_eq]) are unchanged. If these
    close, the tactic family auto-discharges the generalized rules. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.
Require Import Synth.ARM.ArmSemantics.
Require Import Synth.WASM.WasmValues.
Require Import Synth.WASM.WasmInstructions.
Require Import Synth.WASM.WasmSemantics.
Require Import Synth.Synth.Compilation.
Require Import Synth.Synth.Tactics.
Import ListNotations.

Open Scope Z_scope.

(** ** Register-polymorphic lowerings for the i32 single-instruction binops *)

Definition lower_i32_add (rd rn rm : arm_reg) : arm_program := [ADD rd rn (Reg rm)].
Definition lower_i32_sub (rd rn rm : arm_reg) : arm_program := [SUB rd rn (Reg rm)].
Definition lower_i32_mul (rd rn rm : arm_reg) : arm_program := [MUL rd rn rm].
Definition lower_i32_and (rd rn rm : arm_reg) : arm_program := [AND rd rn (Reg rm)].
Definition lower_i32_or  (rd rn rm : arm_reg) : arm_program := [ORR rd rn (Reg rm)].
Definition lower_i32_xor (rd rn rm : arm_reg) : arm_program := [EOR rd rn (Reg rm)].

(** ** The discharge strategy, unchanged from [synth_binop_proof]

    Only difference vs Tactics.v [synth_binop_proof]: it unfolds the
    register-polymorphic lowerings instead of [compile_wasm_to_arm], and intros
    the three extra register binders (rd rn rm). Every discharge step
    (rewrite the operand hypotheses, [get_set_reg_eq]) is identical. *)
Ltac synth_binop_proof_poly :=
  intros wstate astate v1 v2 stack' rd rn rm Hstack HR0 HR1 Hwasm;
  unfold lower_i32_add, lower_i32_sub, lower_i32_mul,
         lower_i32_and, lower_i32_or, lower_i32_xor;
  unfold exec_program, exec_instr;
  simpl;
  rewrite HR0, HR1;
  eexists; split;
  [ reflexivity
  | simpl; apply get_set_reg_eq ].

(** ** The six pilot lemmas — quantified over ARBITRARY rd rn rm

    No [rd <> rn] / [rd <> rm] side conditions: the universal quantifier admits
    every aliasing, so a Qed here is the in-place-reuse (rd = rn) case the Rust
    selector actually emits PLUS the distinct-register case, in one statement. *)

Theorem lower_i32_add_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Add wstate =
    Some (mkWasmState (VI32 (I32.add v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (lower_i32_add rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.add v1 v2.
Proof. synth_binop_proof_poly. Qed.

Theorem lower_i32_sub_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Sub wstate =
    Some (mkWasmState (VI32 (I32.sub v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (lower_i32_sub rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.sub v1 v2.
Proof. synth_binop_proof_poly. Qed.

Theorem lower_i32_mul_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Mul wstate =
    Some (mkWasmState (VI32 (I32.mul v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (lower_i32_mul rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.mul v1 v2.
Proof. synth_binop_proof_poly. Qed.

Theorem lower_i32_and_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32And wstate =
    Some (mkWasmState (VI32 (I32.and v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (lower_i32_and rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.and v1 v2.
Proof. synth_binop_proof_poly. Qed.

Theorem lower_i32_or_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Or wstate =
    Some (mkWasmState (VI32 (I32.or v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (lower_i32_or rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.or v1 v2.
Proof. synth_binop_proof_poly. Qed.

Theorem lower_i32_xor_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Xor wstate =
    Some (mkWasmState (VI32 (I32.xor v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (lower_i32_xor rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.xor v1 v2.
Proof. synth_binop_proof_poly. Qed.

(** ** The discriminating case: a multi-instruction, scratch-using op

    [I32Rotl] lowers to TWO instructions through a scratch register:
    [RSB rs rm #32; ROR_reg rd rn rs] (rs holds 32 - shift, then rotate-right by
    it = rotate-left). Unlike the six single-instruction binops above, this
    EXPOSES what the no-scratch ops dodge:

    (1) SCRATCH NON-ALIASING is a real proof obligation, not a [discriminate].
        The fixed-register proof [i32_rotl_correct] discharges [R0 <> R2] with
        [discriminate] (concrete distinct registers). Under generalization that
        becomes an explicit hypothesis [rs <> rn] — the scratch must not alias
        the value register, because [RSB] writes the scratch in instruction 1
        before [ROR] reads the value in instruction 2. THIS IS THE CONSTRAINT
        THE DSL MUST CARRY AND FEED TO THE ALLOCATOR (VCR-RA-001).

    (2) The single-instruction tactic [synth_binop_proof_poly] does NOT close it
        — a multi-instruction proof must step through the intermediate state.
        It closes with the SAME proof structure as the existing T1
        [i32_rotl_correct], parameterized over registers, with [discriminate]
        replaced by the [rs <> rn] hypothesis.

    MEASUREMENT: scratch-using ops generalize too, but NOT for free — they need
    (a) explicit scratch-non-aliasing side conditions and (b) a per-shape proof,
    not the one-line tactic. The DSL is therefore viable but must model scratch
    registers with non-aliasing constraints; the "auto-discharge" rate is ~100%
    only for the no-scratch single-instruction class. *)

Definition lower_i32_rotl (rd rn rm rs : arm_reg) : arm_program :=
  [RSB rs rm (Imm (I32.repr 32)); ROR_reg rd rn rs].

Theorem lower_i32_rotl_correct : forall wstate astate v1 v2 stack' rd rn rm rs,
  rs <> rn ->        (* scratch must not alias the value register *)
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Rotl wstate =
    Some (mkWasmState (VI32 (I32.rotl v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (lower_i32_rotl rd rn rm rs) astate = Some astate' /\
    get_reg astate' rd = I32.rotl v1 v2.
Proof.
  intros wstate astate v1 v2 stack' rd rn rm rs Hne Hstack HR0 HR1 Hwasm.
  unfold lower_i32_rotl.
  set (s1 := set_reg astate rs (I32.sub (I32.repr 32) (get_reg astate rm))).
  set (s2 := set_reg s1 rd (I32.rotr (get_reg s1 rn) (get_reg s1 rs))).
  exists s2. split.
  - subst s2 s1. simpl. reflexivity.
  - subst s2. rewrite get_set_reg_eq.
    subst s1. rewrite get_set_reg_neq by exact Hne.
    rewrite get_set_reg_eq.
    rewrite HR0, HR1.
    symmetry. apply I32.rotl_rotr_sub.
Qed.
