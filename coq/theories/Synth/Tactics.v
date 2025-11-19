(** * Synth Proof Automation

    This file provides custom tactics to automate common proof patterns
    in Synth compilation correctness proofs.
*)

Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.
Require Import Synth.ARM.ArmSemantics.
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

Require Import Synth.Synth.Correctness.

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
