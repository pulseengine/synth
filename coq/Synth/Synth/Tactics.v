(** * Synth Proof Automation

    This file provides custom tactics to automate common proof patterns
    in Synth compilation correctness proofs.
*)

From Stdlib Require Import ZArith Ring.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.
Require Import Synth.ARM.ArmSemantics.
Require Import Synth.ARM.ArmFlagLemmas.
Require Import Synth.WASM.WasmValues.
Require Import Synth.WASM.WasmInstructions.
Require Import Synth.WASM.WasmSemantics.
Require Import Synth.Synth.Compilation.

(** ** Tactic: synth_binop_proof

    Automates the standard proof pattern for binary operations:
    1. Unfold compilation
    2. Execute ARM code
    3. Substitute register values
    4. Prove result equality
*)

Ltac synth_binop_proof :=
  intros wstate astate v1 v2 stack' Hstack HR0 HR1 Hwasm;
  unfold compile_wasm_to_arm;
  unfold exec_program, exec_instr;
  simpl;
  rewrite HR0, HR1;
  eexists; split;
  [ reflexivity
  | simpl; apply get_set_reg_eq ].

(** ** Tactic: synth_comparison_proof

    Automates proofs for comparison operations that produce boolean results.
*)

Ltac synth_comparison_proof :=
  intros wstate astate v1 v2 stack' Hstack HR0 HR1 Hwasm;
  unfold compile_wasm_to_arm;
  unfold exec_program;
  simpl;
  rewrite HR0, HR1;
  eexists; split;
  [ reflexivity
  | simpl; apply get_set_reg_eq ].

(** ** Tactic: synth_unop_proof

    Automates proofs for unary operations.
*)

Ltac synth_unop_proof :=
  intros wstate astate v stack' Hstack HR0 Hwasm;
  unfold compile_wasm_to_arm;
  unfold exec_program, exec_instr;
  simpl;
  rewrite HR0;
  eexists; split;
  [ reflexivity
  | simpl; apply get_set_reg_eq ].

(** ** Tactic: synth_cmp_binop_proof

    Automates comparison proofs: CMP + MOV + conditional-MOV pattern.
    Takes a flag lemma as argument to rewrite the flag condition. *)

Ltac synth_cmp_binop_proof flag_lemma :=
  intros wstate astate v1 v2 stack' Hstack HR0 HR1 Hwasm;
  unfold compile_wasm_to_arm; simpl;
  rewrite HR0, HR1; simpl;
  rewrite flag_lemma;
  destruct (_ v1 v2);
  (eexists; split; [reflexivity | apply get_set_reg_eq]).

(** ** Tactic: synth_cmp_unop_proof

    Automates unary comparison proofs (eqz): CMP + MOV + conditional-MOV. *)

Ltac synth_cmp_unop_proof flag_lemma :=
  intros wstate astate v stack' Hstack HR0 Hwasm;
  unfold compile_wasm_to_arm; simpl;
  rewrite HR0; simpl;
  rewrite flag_lemma;
  destruct (I32.eq v I32.zero);
  (eexists; split; [reflexivity | apply get_set_reg_eq]).

(** ** I64 Tactics (v0.8.0 foundation)

    Architectural note: i64 ops in this codebase compile to single 32-bit
    ARM instructions (see Compilation.v — "Simplified: just add low 32 bits").
    There is NO R0:R1 register pair — i64 values live in a single 32-bit
    register, and ARM operations compute the I32 result on the underlying Z
    representation. The T1 obligation discharged by these tactics therefore
    has shape `get_reg astate' R0 = I32.op v1 v2` (matching the actual ARM
    behavior), not `lo(I64.op v1 v2) /\ hi(I64.op v1 v2)` (which would
    presume a register-pair representation that does not exist here).

    This mirrors how the existing i64 div/rem T1 proofs in CorrectnessI64.v
    already work — they take `I32.divs v1 v2 = Some result` (not I64.divs)
    as a hypothesis. The foundation PR follows the same convention. *)

(** ** Tactic: synth_binop_proof_i64

    Automates the standard proof pattern for i64 binary operations.
    Discharges obligations of the shape:
    [
      wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
      get_reg astate R0 = v1 -> get_reg astate R1 = v2 ->
      exec_wasm_instr <I64Op> wstate = Some (...) ->
      exists astate',
        exec_program (compile_wasm_to_arm <I64Op>) astate = Some astate' /\
        get_reg astate' R0 = I32.<op> v1 v2.
    ]

    The conclusion uses `I32.<op>` (matching the actual ARM instruction
    semantics on 32-bit registers); v1, v2 have type I64.int. *)

Ltac synth_binop_proof_i64 :=
  intros;
  match goal with
  | [ HR0 : get_reg _ R0 = _, HR1 : get_reg _ R1 = _ |- _ ] =>
      unfold compile_wasm_to_arm;
      unfold exec_program, exec_instr;
      simpl;
      rewrite HR0, HR1;
      eexists; split;
      [ reflexivity
      | simpl; apply get_set_reg_eq ]
  end.

(** ** Tactic: synth_cmp_binop_proof_i64

    Automates i64 comparison proofs (CMP + MOV + conditional-MOV).
    Takes an i64 flag-correspondence lemma (from ArmFlagLemmas.v) as
    argument. The lemma must close the boundedness preconditions; we
    feed it via `apply` so the caller's i64 boundedness hypotheses
    surface as residual goals. *)

Ltac synth_cmp_binop_proof_i64 flag_lemma :=
  intros;
  match goal with
  | [ HR0 : get_reg _ R0 = _, HR1 : get_reg _ R1 = _ |- _ ] =>
      unfold compile_wasm_to_arm; simpl;
      rewrite HR0, HR1; simpl;
      rewrite flag_lemma by assumption;
      match goal with
      | |- context [if ?b then _ else _] => destruct b
      end;
      (eexists; split; [reflexivity | apply get_set_reg_eq])
  end.

(** ** Tactic: synth_cmp_unop_proof_i64

    i64 eqz variant of [synth_cmp_unop_proof]. The compilation pattern
    is CMP R0 (Imm I32.zero); MOV; MOVEQ. *)

Ltac synth_cmp_unop_proof_i64 flag_lemma :=
  intros;
  match goal with
  | [ HR0 : get_reg _ R0 = _ |- _ ] =>
      unfold compile_wasm_to_arm; simpl;
      rewrite HR0; simpl;
      rewrite flag_lemma by assumption;
      match goal with
      | |- context [if ?b then _ else _] => destruct b
      end;
      (eexists; split; [reflexivity | apply get_set_reg_eq])
  end.

(** ** Tactic: synth_simplify

    Standard simplification for Synth proofs.
*)

Ltac synth_simplify :=
  unfold exec_wasm_instr, exec_instr, exec_program;
  unfold pop2_i32, pop_i32, pop_value, pop, pop2;
  unfold push_value, push;
  unfold eval_operand2;
  unfold get_reg, set_reg;
  simpl.

(** ** Tactic: synth_destruct_stack

    Destruct WASM stack into components.
*)

Ltac synth_destruct_stack :=
  match goal with
  | [ H : ?s.(stack) = _ |- _ ] => rewrite H; simpl
  | _ => idtac
  end.

(** ** Tactic: synth_solve

    Try to automatically solve the goal using standard tactics.
*)

Ltac synth_solve :=
  try reflexivity;
  try (simpl; apply get_set_reg_eq);
  try (simpl; apply update_eq);
  try (f_equal; ring);
  try (eexists; split; [reflexivity | simpl; apply get_set_reg_eq]).

(** ** Tactic: synth_auto

    Full automation: try all tactics in sequence.
*)

Ltac synth_auto :=
  synth_simplify;
  synth_destruct_stack;
  synth_solve.

(** ** Examples of using automation *)

(* Commented out to avoid cyclic dependency - Correctness files import Tactics *)
(* Require Import Synth.Synth.Correctness.

(** Reprove i32.add using automation *)
Theorem compile_i32_add_correct_auto : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32Add wstate =
    Some (mkWasmState
            (VI32 (I32.add v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Add) astate = Some astate' /\
    get_reg astate' R0 = I32.add v1 v2.
Proof.
  synth_binop_proof.
Qed.

(** This proof is 1 line instead of 8! *)
*)
