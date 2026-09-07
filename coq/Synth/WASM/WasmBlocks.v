(** * Structured control flow — Block / Loop / Br / End on the WASM side
    (#1057, RQ-64-CFOBLIG)

    RQ-60-CFOBLIG increment 1 gave the WASM model its first control-flow
    constructor, [BrIf], and a branch-OBSERVABLE executor [exec_wasm_seq]
    whose taken branch is a [WBranch l] outcome. What it deliberately did
    not model was the enclosing label stack that CONSUMES a [WBranch]: the
    [Block]/[Loop]/[End] structure a branch exits toward. This file is that
    half — the WASM side of the Block/End correspondence obligation.

    The representation is the SHIPPED one: the flat op stream every accepted
    function is decoded into (synth-core/src/wasm_op.rs), where [Block] and
    [Loop] open a region that the matching [End_] closes and nesting is
    positional, not an AST. Consequences:

    - a block's extent has to be FOUND: [split_block] scans forward to the
      matching [End_] (nesting-aware), returning the body and the
      continuation after the [End_];
    - execution is FUEL-bounded ([exec_wasm_blocks fuel]): the body and the
      continuation are proper sub-lists but not structural sub-terms, and a
      [Loop] re-enters its own body. [None] means "out of fuel, ill-formed,
      or unmodeled" — the same honest-decline instrument as
      [exec_wasm_instr]'s catch-all, never a silent fall-through.

    Semantics, WasmCert-style ("break" administrative outcome), for VOID
    blocks:

    - [Block body End_ cont]: run [body]; on fall-through continue with
      [cont]; on [WBranch 0] UNWIND the operand stack to the block's entry
      height and continue with [cont]; on [WBranch (S l)] propagate
      [WBranch l] outward (the branch targets an enclosing label).
    - [Loop body End_ cont]: as [Block], except [WBranch 0] re-enters the
      loop (the label is at the START).
    - [Br l]: an unconditional [WBranch l].
    - [BrIf l]: exactly [exec_wasm_seq]'s decision.
    - an [End_] with no open block: ill-formed, [None].

    Unwinding is what makes a branch with extra operands on the stack
    (valid wasm: [br] is stack-polymorphic) land on the same stack the
    fall-through path produces — the value-dimension half of the #509/#930
    miscompile class, here at arity 0.

    What this file establishes with the kernel:
    - [exec_wasm_blocks_structured_free]: on programs with none of the four
      new constructors the structured executor IS [exec_wasm_seq] — so the
      600+ existing theorems' executor is unchanged by construction;
    - the [Block]/[Loop]/[Br] unfolding lemmas the ARM-side obligation
      (BlockEndObligation.v) is stated against;
    - computed non-vacuity examples: the SAME block, differing only in the
      branch condition, lands with and without the body's tail effect; a
      counting loop iterates to its exit. A checker that could not
      distinguish those would prove nothing about End.

    What it does NOT establish: any relation to ARM code. The ARM-side
    obligation is stated, and its obstruction pinned with kernel-checked
    lemmas, in BlockEndObligation.v — this file is deliberately WASM-only
    so that nothing in it can be read as a correspondence claim. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.WASM.WasmValues.
Require Import Synth.WASM.WasmInstructions.
Require Import Synth.WASM.WasmSemantics.

Import ListNotations.
Open Scope list_scope.

(** ** Locating a block's extent

    [split_block_aux depth prog]: [prog] is the stream right after an
    opening [Block]/[Loop]; return [(body, cont)] where [body] is everything
    up to (excluding) the matching [End_] and [cont] everything after it.
    [depth] counts the blocks opened inside [body] that are still open. *)
Fixpoint split_block_aux (depth : nat) (prog : list wasm_instr)
    : option (list wasm_instr * list wasm_instr) :=
  match prog with
  | [] => None
  | End_ :: rest =>
      match depth with
      | O => Some ([], rest)
      | S d =>
          match split_block_aux d rest with
          | Some (body, cont) => Some (End_ :: body, cont)
          | None => None
          end
      end
  | Block :: rest =>
      match split_block_aux (S depth) rest with
      | Some (body, cont) => Some (Block :: body, cont)
      | None => None
      end
  | Loop :: rest =>
      match split_block_aux (S depth) rest with
      | Some (body, cont) => Some (Loop :: body, cont)
      | None => None
      end
  | i :: rest =>
      match split_block_aux depth rest with
      | Some (body, cont) => Some (i :: body, cont)
      | None => None
      end
  end.

Definition split_block (prog : list wasm_instr)
    : option (list wasm_instr * list wasm_instr) :=
  split_block_aux 0 prog.

(** A body with no nested block: its first [End_] is the matching one. *)
Definition block_free (prog : list wasm_instr) : bool :=
  forallb (fun i => match i with
                    | Block | Loop | End_ => false
                    | _ => true
                    end) prog.

Lemma split_block_block_free : forall body cont,
  block_free body = true ->
  split_block (body ++ End_ :: cont) = Some (body, cont).
Proof.
  unfold split_block.
  induction body as [| i body IH]; intros cont Hfree.
  - reflexivity.
  - unfold block_free in Hfree. simpl in Hfree.
    apply andb_prop in Hfree. destruct Hfree as [Hi Hrest].
    destruct i; try discriminate Hi; simpl; rewrite (IH cont Hrest); reflexivity.
Qed.

(** ** Unwinding

    A taken branch restores the operand stack to the TARGET block's entry
    height — for a void block, exactly the entry stack — while locals,
    globals and memory are those at the branch point. *)
Definition unwind_to (entry s : wasm_state) : wasm_state :=
  mkWasmState entry.(stack) s.(locals) s.(globals) s.(memory).

(** ** The structured executor *)

Fixpoint exec_wasm_blocks (fuel : nat) (prog : list wasm_instr)
    (s : wasm_state) : option wasm_outcome :=
  match fuel with
  | O => None
  | S fuel' =>
      match prog with
      | [] => Some (WFallthrough s)
      | Block :: rest =>
          match split_block rest with
          | Some (body, cont) =>
              match exec_wasm_blocks fuel' body s with
              | Some (WFallthrough s') => exec_wasm_blocks fuel' cont s'
              | Some (WBranch O s') =>
                  exec_wasm_blocks fuel' cont (unwind_to s s')
              | Some (WBranch (S l) s') => Some (WBranch l s')
              | None => None
              end
          | None => None
          end
      | Loop :: rest =>
          match split_block rest with
          | Some (body, cont) =>
              match exec_wasm_blocks fuel' body s with
              | Some (WFallthrough s') => exec_wasm_blocks fuel' cont s'
              | Some (WBranch O s') =>
                  exec_wasm_blocks fuel' (Loop :: rest) (unwind_to s s')
              | Some (WBranch (S l) s') => Some (WBranch l s')
              | None => None
              end
          | None => None
          end
      | End_ :: _ => None
      | Br l :: _ => Some (WBranch l s)
      | BrIf l :: rest =>
          match pop_i32 s with
          | Some (c, s') =>
              if I32.eq c I32.zero
              then exec_wasm_blocks fuel' rest s'
              else Some (WBranch l s')
          | None => None
          end
      | i :: rest =>
          match exec_wasm_instr i s with
          | Some s' => exec_wasm_blocks fuel' rest s'
          | None => None
          end
      end
  end.

(** ** Refinement: nothing changed for the existing executor

    A program with none of the four structured constructors executes
    IDENTICALLY under [exec_wasm_blocks] (given fuel for its length) and
    under RQ-60's [exec_wasm_seq] — the executor the 600+ existing theorems
    and [brif_correct] are stated against is untouched by construction. *)
Definition structured_free (prog : list wasm_instr) : bool :=
  forallb (fun i => match i with
                    | Block | Loop | Br _ | End_ => false
                    | _ => true
                    end) prog.

Lemma exec_wasm_blocks_structured_free : forall prog fuel s,
  structured_free prog = true ->
  (length prog < fuel)%nat ->
  exec_wasm_blocks fuel prog s = exec_wasm_seq prog s.
Proof.
  induction prog as [| i rest IH]; intros fuel s Hfree Hfuel.
  - destruct fuel; [simpl in Hfuel; lia | reflexivity].
  - destruct fuel as [| fuel']; [simpl in Hfuel; lia |].
    unfold structured_free in Hfree. simpl in Hfree.
    apply andb_prop in Hfree. destruct Hfree as [Hi Hrest].
    simpl in Hfuel.
    (* [cbn] restricted to the two executors, as in
       [exec_wasm_seq_brif_free]: unfolding [exec_wasm_instr] on a concrete
       constructor would erase the term the [destruct] case-splits on. *)
    destruct i; try discriminate Hi;
      cbn [exec_wasm_blocks exec_wasm_seq];
      first
        [ (* BrIf: both executors pop and decide identically *)
          destruct (pop_i32 s) as [[c s'] |];
          [ destruct (I32.eq c I32.zero);
            [ apply IH; [exact Hrest | lia] | reflexivity ]
          | reflexivity ]
        | (* every flat instruction: delegate, then recurse *)
          destruct (exec_wasm_instr _ s);
          [ apply IH; [exact Hrest | lia] | reflexivity ] ].
Qed.

(** ** Unfolding lemmas — the two-sided semantics in the shape a
    correspondence proof consumes *)

(** A branch of depth 0 out of a [Block] lands after its [End_], on the
    entry stack. *)
Lemma exec_wasm_blocks_block_taken : forall fuel rest body cont s s',
  split_block rest = Some (body, cont) ->
  exec_wasm_blocks fuel body s = Some (WBranch 0 s') ->
  exec_wasm_blocks (S fuel) (Block :: rest) s
  = exec_wasm_blocks fuel cont (unwind_to s s').
Proof.
  intros fuel rest body cont s s' Hsplit Hbody.
  cbn [exec_wasm_blocks]. rewrite Hsplit, Hbody. reflexivity.
Qed.

(** Falling through a [Block]'s body continues after its [End_]. *)
Lemma exec_wasm_blocks_block_fallthrough : forall fuel rest body cont s s',
  split_block rest = Some (body, cont) ->
  exec_wasm_blocks fuel body s = Some (WFallthrough s') ->
  exec_wasm_blocks (S fuel) (Block :: rest) s = exec_wasm_blocks fuel cont s'.
Proof.
  intros fuel rest body cont s s' Hsplit Hbody.
  cbn [exec_wasm_blocks]. rewrite Hsplit, Hbody. reflexivity.
Qed.

(** A deeper branch passes through a [Block] with its depth decremented. *)
Lemma exec_wasm_blocks_block_outer : forall fuel rest body cont s s' l,
  split_block rest = Some (body, cont) ->
  exec_wasm_blocks fuel body s = Some (WBranch (S l) s') ->
  exec_wasm_blocks (S fuel) (Block :: rest) s = Some (WBranch l s').
Proof.
  intros fuel rest body cont s s' l Hsplit Hbody.
  cbn [exec_wasm_blocks]. rewrite Hsplit, Hbody. reflexivity.
Qed.

(** A branch of depth 0 out of a [Loop] RE-ENTERS it — the label is at the
    start. This is the WASM-side fact the ARM executor cannot mirror today
    (BlockEndObligation.v, [exec_program_pc_bcond_backward_falls_through]). *)
Lemma exec_wasm_blocks_loop_reenter : forall fuel rest body cont s s',
  split_block rest = Some (body, cont) ->
  exec_wasm_blocks fuel body s = Some (WBranch 0 s') ->
  exec_wasm_blocks (S fuel) (Loop :: rest) s
  = exec_wasm_blocks fuel (Loop :: rest) (unwind_to s s').
Proof.
  intros fuel rest body cont s s' Hsplit Hbody.
  cbn [exec_wasm_blocks]. rewrite Hsplit, Hbody. reflexivity.
Qed.

(** [Br l] is an unconditional [WBranch l]. *)
Lemma exec_wasm_blocks_br : forall fuel rest s l,
  exec_wasm_blocks (S fuel) (Br l :: rest) s = Some (WBranch l s).
Proof. reflexivity. Qed.

(** ** Non-vacuity: the decision at [End_] is observable

    The SAME block, differing only in the branch condition constant. When
    the branch is taken, the body's tail ([I32Const 7]) is skipped AND the
    stack is unwound to the entry height; when it is not taken, the tail
    runs and its value is on the stack after [End_]. *)

Definition ex_state0 : wasm_state :=
  mkWasmState ([]) (fun _ => I32.zero) (fun _ => I32.zero) (fun _ => I32.zero).

Definition ex_block (cond : I32.int) : list wasm_instr :=
  [Block; I32Const cond; BrIf 0; I32Const (I32.repr 7); End_].

(** Observation: the stack after the block — its length, and the unsigned
    value on top when there is exactly one — so the two runs are compared
    by a plain [Z], never by an executor-internal term. *)
Definition ex_observe (o : option wasm_outcome) : Z * Z :=
  match o with
  | Some (WFallthrough s) =>
      (Z.of_nat (length s.(stack)),
       match s.(stack) with
       | VI32 v :: nil => I32.unsigned v
       | _ => -1
       end)
  | _ => (-1, -1)
  end.

Example ex_block_branch_taken_unwinds :
  ex_observe (exec_wasm_blocks 10 (ex_block I32.one) ex_state0) = (0, -1).
Proof. vm_compute. reflexivity. Qed.

Example ex_block_branch_not_taken_runs_tail :
  ex_observe (exec_wasm_blocks 10 (ex_block I32.zero) ex_state0) = (1, 7).
Proof. vm_compute. reflexivity. Qed.

(** A counting loop: [local 0 := 3; loop { local 0 := local 0 - 1;
    br_if 0 (local 0) }] — three iterations, exits with local 0 = 0 and an
    empty stack (each [br_if] pops its condition; each taken branch
    unwinds). *)
Definition ex_loop : list wasm_instr :=
  [Loop; LocalGet 0; I32Const I32.one; I32Sub; LocalTee 0; BrIf 0; End_].

Definition ex_state_local3 : wasm_state :=
  mkWasmState ([]) (fun _ => I32.repr 3) (fun _ => I32.zero) (fun _ => I32.zero).

Definition ex_observe_local0 (o : option wasm_outcome) : Z * Z :=
  match o with
  | Some (WFallthrough s) =>
      (Z.of_nat (length s.(stack)), I32.unsigned (s.(locals) 0%nat))
  | _ => (-1, -1)
  end.

Example ex_loop_counts_down_to_zero :
  ex_observe_local0 (exec_wasm_blocks 40 ex_loop ex_state_local3) = (0, 0).
Proof. vm_compute. reflexivity. Qed.

(** And the loop is a LOOP: with fuel for only one pass the executor
    declines rather than reporting a one-iteration result — a bounded
    executor's honest answer, never a silently truncated one. *)
Example ex_loop_needs_its_iterations :
  exec_wasm_blocks 6 ex_loop ex_state_local3 = None.
Proof. vm_compute. reflexivity. Qed.
