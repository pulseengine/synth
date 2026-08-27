(** * Correctness of the br_if lowering (#1057, RQ-60-CFOBLIG increment 1)

    gale's #1057 measurement found 178 control-flow rule instances covered
    by NEITHER verification half, and the coordinator traced the cause one
    level deeper than a naming scheme: [wasm_instr] had no control-flow
    constructor at all — there was no obligation for br_if because the
    model had no br_if. This file states and DISCHARGES that obligation
    for [BrIf], the first of the eight control-flow kinds (the subject of
    the closed miscompiles #483/#500/#509/#930 — the rules most worth an
    obligation).

    The two halves of the correspondence:

    - WASM side: [exec_wasm_seq] (WasmSemantics.v) — a taken branch is an
      observable [WBranch l] outcome, a not-taken branch falls through.

    - ARM side: [exec_program_pc]/[exec_program_br] (ArmSemantics.v) —
      the SAME branch-taking executor all four #73 i32 div/rem trap-guard
      proofs are discharged against, because a trap guard IS a
      conditional branch.

    The lowering under proof is [compile_brif] (Compilation.v): the
    shipped shape `CMP cond, #0 ; BNE <target>` with the label RESOLVED
    to a PC-relative skip count — exactly what
    select_with_stack.rs's `BrIf(depth)` arm emits after branch
    resolution.

    [brif_correct] is CONTEXT-PARAMETRIC: it holds for the compiled pair
    sitting at ANY index of ANY surrounding program, which is how emitted
    code actually appears inside a function — not only for the pair in
    isolation, where a branch decision has no observable consequence. The
    two [exec_program_br] corollaries then pin non-vacuity on a concrete
    program: the SAME code, driven only by the condition value, either
    skips a trap ([Some]) or hits it ([None]) — the decision is real. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
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

Import ListNotations.
Open Scope Z_scope.

(** ** Locating the compiled pair

    Glue between the app-shaped view of an emitted function
    ([prefix ++ compile_brif off ++ rest]) and the [nth_error] hypotheses
    [brif_correct] consumes. *)
Lemma compile_brif_nth : forall prefix rest off,
  nth_error (prefix ++ compile_brif off ++ rest) (length prefix)
    = Some (CMP R0 (Imm I32.zero))
  /\ nth_error (prefix ++ compile_brif off ++ rest) (S (length prefix))
    = Some (BCondOffset Cond_NE off).
Proof.
  induction prefix as [| a prefix IH]; intros rest off.
  - split; reflexivity.
  - destruct (IH rest off) as [H1 H2]. split; simpl; assumption.
Qed.

(** ** The correspondence theorem

    For a condition value [v] on top of the WASM stack and in R0 (this
    model's stack-top convention):

    - the WASM branch-observable executor pops the condition and decides:
      [WFallthrough] when [v = 0], [WBranch l] when [v <> 0];
    - the compiled guard, sitting at ANY [pc] of ANY program, makes the
      SAME decision: execution continues at the fall-through index
      [pc + 2] iff WASM fell through, and at the branch target
      [pc + 2 + off] iff WASM branched;
    - the ARM state is preserved up to flags (the CMP latches NZCV;
      no register moves).

    The discriminator on both sides is literally the same test
    [I32.eq v I32.zero]: the WASM side tests it directly, the ARM side
    reaches it through [z_flag_sub_eq] (the Z flag latched by
    [CMP v, #0]). No [I32.valid_unsigned] hypothesis is needed — both
    sides already work modulo 2^32. *)
Theorem brif_correct : forall l off wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  get_reg astate R0 = v ->
  exists wstate' astate',
    exec_wasm_seq ([BrIf l]) wstate
      = Some (if I32.eq v I32.zero
              then WFallthrough wstate'
              else WBranch l wstate')
    /\ wstate'.(stack) = stack'
    /\ (forall r, get_reg astate' r = get_reg astate r)
    /\ (forall prog pc fuel,
          nth_error prog pc = Some (CMP R0 (Imm I32.zero)) ->
          nth_error prog (S pc) = Some (BCondOffset Cond_NE off) ->
          exec_program_pc (S (S fuel)) prog pc astate
          = exec_program_pc fuel prog
              (if I32.eq v I32.zero
               then (pc + 2)%nat
               else (pc + 2 + Z.to_nat off)%nat) astate').
Proof.
  intros l off wstate astate v stack' Hstack HR0.
  assert (Hpop : pop_i32 wstate
      = Some (v, mkWasmState stack'
                   wstate.(locals) wstate.(globals) wstate.(memory))).
  { unfold pop_i32, pop_value, pop. rewrite Hstack. reflexivity. }
  exists (mkWasmState stack' wstate.(locals) wstate.(globals) wstate.(memory)).
  exists (set_flags astate
            (update_flags_arith (I32.sub v I32.zero)
               (compute_c_flag_sub v I32.zero)
               (compute_v_flag_sub v I32.zero))).
  split; [| split; [| split]].
  - (* WASM side: the outcome follows the condition. *)
    destruct (I32.eq v I32.zero) eqn:Hv.
    + rewrite (exec_wasm_seq_brif_not_taken l ([]) wstate v _ Hpop Hv).
      reflexivity.
    + rewrite (exec_wasm_seq_brif_taken l ([]) wstate v _ Hpop Hv).
      reflexivity.
  - (* The condition is consumed. *)
    reflexivity.
  - (* Registers preserved: CMP only latches flags. *)
    intros r. apply get_reg_set_flags.
  - (* ARM side: the compiled guard takes the same decision. *)
    intros prog pc fuel Hcmp Hbcc.
    rewrite (exec_program_pc_instr (S fuel) prog pc astate _ Hcmp I).
    cbn [exec_instr eval_operand2].
    rewrite HR0.
    replace (pc + 1)%nat with (S pc) by lia.
    erewrite (exec_program_pc_bcond fuel prog (S pc) _ Cond_NE off Hbcc).
    rewrite flags_set_flags.
    cbn [eval_condition].
    rewrite flag_z_update_flags_arith.
    rewrite z_flag_sub_eq.
    destruct (I32.eq v I32.zero) eqn:Hv; cbn [negb].
    + (* v = 0: not taken — fall through to pc + 2. *)
      replace (S pc + 1)%nat with (pc + 2)%nat by lia.
      reflexivity.
    + (* v <> 0: taken — land at pc + 2 + off. *)
      replace (S pc + 1 + Z.to_nat off)%nat
        with (pc + 2 + Z.to_nat off)%nat by lia.
      reflexivity.
Qed.

(** ** Non-vacuity: the decision is observable

    The trap-guard shape from the #73 div/rem proofs, driven by
    [compile_brif] itself: the concrete program

      CMP R0, #0 ; BNE +1 ; UDF 0

    SKIPS the trap exactly when the condition is non-zero. The same
    program, differing only in the runtime value of R0, produces [Some]
    in one case and [None] in the other — a checker that structurally
    could not fail would prove neither. *)

Theorem brif_guard_taken_skips_trap : forall astate v,
  get_reg astate R0 = v ->
  I32.eq v I32.zero = false ->
  exists astate',
    exec_program_br (compile_brif 1 ++ [UDF 0]) astate = Some astate' /\
    forall r, get_reg astate' r = get_reg astate r.
Proof.
  intros astate v HR0 Hv.
  eexists. split.
  - unfold exec_program_br.
    change (length (compile_brif 1 ++ [UDF 0])) with 3%nat.
    erewrite (exec_program_pc_instr _ _ _ _ (CMP R0 (Imm I32.zero)));
      [| reflexivity | exact I].
    cbn [exec_instr eval_operand2].
    rewrite HR0.
    erewrite (exec_program_pc_bcond _ _ _ _ Cond_NE 1); [| reflexivity].
    rewrite flags_set_flags.
    cbn [eval_condition].
    rewrite flag_z_update_flags_arith.
    rewrite z_flag_sub_eq.
    rewrite Hv. cbn [negb].
    (* Branch TAKEN: pc = 0+1+1+1 = 3 runs off the end — trap skipped. *)
    rewrite exec_program_pc_done by reflexivity.
    reflexivity.
  - intros r. apply get_reg_set_flags.
Qed.

Theorem brif_guard_not_taken_hits_trap : forall astate v,
  get_reg astate R0 = v ->
  I32.eq v I32.zero = true ->
  exec_program_br (compile_brif 1 ++ [UDF 0]) astate = None.
Proof.
  intros astate v HR0 Hv.
  unfold exec_program_br.
  change (length (compile_brif 1 ++ [UDF 0])) with 3%nat.
  erewrite (exec_program_pc_instr _ _ _ _ (CMP R0 (Imm I32.zero)));
    [| reflexivity | exact I].
  cbn [exec_instr eval_operand2].
  rewrite HR0.
  erewrite (exec_program_pc_bcond _ _ _ _ Cond_NE 1); [| reflexivity].
  rewrite flags_set_flags.
  cbn [eval_condition].
  rewrite flag_z_update_flags_arith.
  rewrite z_flag_sub_eq.
  rewrite Hv. cbn [negb].
  (* Branch NOT taken: pc = 0+1+1 = 2 is the UDF — the trap fires. *)
  erewrite (exec_program_pc_instr _ _ _ _ (UDF 0));
    [| reflexivity | exact I].
  cbn [exec_instr].
  reflexivity.
Qed.
