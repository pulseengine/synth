(** * WebAssembly Operational Semantics

    This file defines the operational semantics of WebAssembly instructions
    using a stack machine model.

    Based on synth-verify/src/wasm_semantics.rs
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.WASM.WasmValues.
Require Import Synth.WASM.WasmInstructions.

Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.

(** ** WebAssembly Machine State *)

Record wasm_state : Type := mkWasmState {
  stack : wasm_stack;
  locals : nat -> I32.int;
  globals : nat -> I32.int;
  memory : Z -> I32.int;
}.

(** ** State Accessors *)

Definition push_value (v : wasm_val) (s : wasm_state) : wasm_state :=
  mkWasmState
    (push v s.(stack))
    s.(locals)
    s.(globals)
    s.(memory).

Definition pop_value (s : wasm_state) : option (wasm_val * wasm_state) :=
  match pop s.(stack) with
  | Some (v, stack') =>
      Some (v, mkWasmState stack' s.(locals) s.(globals) s.(memory))
  | None => None
  end.

Definition pop_i32 (s : wasm_state) : option (I32.int * wasm_state) :=
  match pop_value s with
  | Some (VI32 n, s') => Some (n, s')
  | _ => None
  end.

Definition pop_i64 (s : wasm_state) : option (I64.int * wasm_state) :=
  match pop_value s with
  | Some (VI64 n, s') => Some (n, s')
  | _ => None
  end.

Definition pop2_i32 (s : wasm_state) : option (I32.int * I32.int * wasm_state) :=
  match pop2 s.(stack) with
  | Some (VI32 v1, VI32 v2, stack') =>
      Some (v1, v2, mkWasmState stack' s.(locals) s.(globals) s.(memory))
  | _ => None
  end.

Definition pop2_i64 (s : wasm_state) : option (I64.int * I64.int * wasm_state) :=
  match pop2 s.(stack) with
  | Some (VI64 v1, VI64 v2, stack') =>
      Some (v1, v2, mkWasmState stack' s.(locals) s.(globals) s.(memory))
  | _ => None
  end.

(** ** Instruction Semantics *)

(** Execute a single WebAssembly instruction *)
Definition exec_wasm_instr (i : wasm_instr) (s : wasm_state) : option wasm_state :=
  match i with
  (* Constants.

     #933 boundary normalization: [I32Const] pushes the REGISTER-NORMALIZED
     value [I32.repr n], not the raw [Z] representative [n]. This is the
     faithful model of wasm §2.4.1/§4.4.1: an [i32.const c] immediate IS a
     value of type i32 — the binary format LEB128-decodes exactly 32 bits, so
     no real module can carry an out-of-range representative like
     [2^32 + 0x10000]. The shallow [I32.int := Z] embedding admits such junk
     representatives syntactically; every arithmetic op already quotients them
     out through [I32.repr]/[I32.unsigned], and the raw const push was the ONE
     remaining injection point for un-normalized values into the machine. For
     every in-range [n] (all reachable programs) [I32.repr n = n], so this is
     byte-invisible on the reachable domain — a fidelity fix, not a theorem
     weakening (#166 gate: argued, not silent). *)
  | I32Const n =>
      Some (push_value (VI32 (I32.repr n)) s)

  | I64Const n =>
      Some (push_value (VI64 n) s)

  (* i32 arithmetic operations *)
  | I32Add =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := I32.add v1 v2 in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32Sub =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := I32.sub v1 v2 in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32Mul =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := I32.mul v1 v2 in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32DivS =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          match I32.divs v1 v2 with
          | Some result => Some (push_value (VI32 result) s')
          | None => None  (* Division by zero or overflow *)
          end
      | None => None
      end

  | I32DivU =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          match I32.divu v1 v2 with
          | Some result => Some (push_value (VI32 result) s')
          | None => None
          end
      | None => None
      end

  | I32RemS =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          match I32.rems v1 v2 with
          | Some result => Some (push_value (VI32 result) s')
          | None => None
          end
      | None => None
      end

  | I32RemU =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          match I32.remu v1 v2 with
          | Some result => Some (push_value (VI32 result) s')
          | None => None
          end
      | None => None
      end

  (* i32 bitwise operations *)
  | I32And =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := I32.and v1 v2 in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32Or =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := I32.or v1 v2 in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32Xor =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := I32.xor v1 v2 in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32Shl =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := I32.shl v1 v2 in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32ShrU =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := I32.shru v1 v2 in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32ShrS =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := I32.shrs v1 v2 in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32Rotl =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := I32.rotl v1 v2 in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32Rotr =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := I32.rotr v1 v2 in
          Some (push_value (VI32 result) s')
      | None => None
      end

  (* i32 comparison operations *)
  | I32Eqz =>
      match pop_i32 s with
      | Some (v, s') =>
          let result := if I32.eq v I32.zero then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32Eq =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := if I32.eq v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32Ne =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := if I32.ne v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32LtS =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := if I32.lts v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32LtU =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := if I32.ltu v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32LeS =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := if I32.les v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32LeU =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := if I32.leu v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32GtS =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := if I32.gts v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32GtU =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := if I32.gtu v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32GeS =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := if I32.ges v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32GeU =>
      match pop2_i32 s with
      | Some (v1, v2, s') =>
          let result := if I32.geu v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  (* i32 bit manipulation operations *)
  | I32Clz =>
      match pop_i32 s with
      | Some (v, s') =>
          let result := I32.clz v in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32Ctz =>
      match pop_i32 s with
      | Some (v, s') =>
          let result := I32.ctz v in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I32Popcnt =>
      match pop_i32 s with
      | Some (v, s') =>
          let result := I32.popcnt v in
          Some (push_value (VI32 result) s')
      | None => None
      end

  (* i64 arithmetic operations (mirror the i32 arms via pop2_i64 / VI64) *)
  | I64Add =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := I64.add v1 v2 in
          Some (push_value (VI64 result) s')
      | None => None
      end

  | I64Sub =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := I64.sub v1 v2 in
          Some (push_value (VI64 result) s')
      | None => None
      end

  | I64Mul =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := I64.mul v1 v2 in
          Some (push_value (VI64 result) s')
      | None => None
      end

  (* i64 bitwise operations *)
  | I64And =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := I64.and v1 v2 in
          Some (push_value (VI64 result) s')
      | None => None
      end

  | I64Or =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := I64.or v1 v2 in
          Some (push_value (VI64 result) s')
      | None => None
      end

  | I64Xor =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := I64.xor v1 v2 in
          Some (push_value (VI64 result) s')
      | None => None
      end

  (* i64 comparison operations *)
  | I64Eqz =>
      match pop_i64 s with
      | Some (v, s') =>
          let result := if I64.eq v I64.zero then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I64Eq =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := if I64.eq v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I64Ne =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := if I64.ne v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I64LtS =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := if I64.lts v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I64LtU =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := if I64.ltu v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I64GtS =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := if I64.gts v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I64GtU =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := if I64.gtu v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I64LeS =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := if I64.les v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I64LeU =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := if I64.leu v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I64GeS =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := if I64.ges v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  | I64GeU =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := if I64.geu v1 v2 then I32.one else I32.zero in
          Some (push_value (VI32 result) s')
      | None => None
      end

  (* i64 shift/rotate operations *)
  | I64Shl =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := I64.shl v1 v2 in
          Some (push_value (VI64 result) s')
      | None => None
      end

  | I64ShrU =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := I64.shru v1 v2 in
          Some (push_value (VI64 result) s')
      | None => None
      end

  | I64ShrS =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := I64.shrs v1 v2 in
          Some (push_value (VI64 result) s')
      | None => None
      end

  | I64Rotl =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := I64.rotl v1 v2 in
          Some (push_value (VI64 result) s')
      | None => None
      end

  | I64Rotr =>
      match pop2_i64 s with
      | Some (v1, v2, s') =>
          let result := I64.rotr v1 v2 in
          Some (push_value (VI64 result) s')
      | None => None
      end

  (* i64 bit manipulation operations *)
  | I64Clz =>
      match pop_i64 s with
      | Some (v, s') =>
          let result := I64.clz v in
          Some (push_value (VI64 result) s')
      | None => None
      end

  | I64Ctz =>
      match pop_i64 s with
      | Some (v, s') =>
          let result := I64.ctz v in
          Some (push_value (VI64 result) s')
      | None => None
      end

  | I64Popcnt =>
      match pop_i64 s with
      | Some (v, s') =>
          let result := I64.popcnt v in
          Some (push_value (VI64 result) s')
      | None => None
      end

  (* Local variable operations *)
  | LocalGet idx =>
      let value := s.(locals) idx in
      Some (push_value (VI32 value) s)

  | LocalSet idx =>
      match pop_i32 s with
      | Some (value, s') =>
          Some (mkWasmState
                  s'.(stack)
                  (s'.(locals) [idx |-> value])
                  s'.(globals)
                  s'.(memory))
      | None => None
      end

  | LocalTee idx =>
      match pop_i32 s with
      | Some (value, s') =>
          (* Tee: set local and keep value on stack *)
          let s'' := mkWasmState
                      s'.(stack)
                      (s'.(locals) [idx |-> value])
                      s'.(globals)
                      s'.(memory) in
          Some (push_value (VI32 value) s'')
      | None => None
      end

  (* Global variable operations *)
  | GlobalGet idx =>
      let value := s.(globals) idx in
      Some (push_value (VI32 value) s)

  | GlobalSet idx =>
      match pop_i32 s with
      | Some (value, s') =>
          Some (mkWasmState
                  s'.(stack)
                  s'.(locals)
                  (s'.(globals) [idx |-> value])
                  s'.(memory))
      | None => None
      end

  (* Control flow *)
  | Drop =>
      match pop_value s with
      | Some (_, s') => Some s'
      | None => None
      end

  | Select =>
      (* Pop 3 values: condition, val2, val1 *)
      (* If condition ≠ 0, push val1; else push val2 *)
      match pop_i32 s with
      | Some (cond, s') =>
          match pop_value s' with
          | Some (val2, s'') =>
              match pop_value s'' with
              | Some (val1, s''') =>
                  if I32.eq cond I32.zero
                  then Some (push_value val2 s''')
                  else Some (push_value val1 s''')
              | None => None
              end
          | None => None
          end
      | None => None
      end

  | Nop =>
      Some s

  (* br_if — FALL-THROUGH-ONLY semantics in the flat sequential executor
     (#1057, RQ-60-CFOBLIG increment 1). Popping the condition and
     continuing is correct ONLY when the branch is not taken; a taken
     branch transfers control out of the instruction sequence, which this
     one-state-in/one-state-out shape cannot represent. So the taken case
     DECLINES (None) rather than silently falling through — the #615
     silent-NOP class. The full two-sided semantics, where a taken branch
     is an observable outcome, live in [exec_wasm_seq] below. *)
  | BrIf _ =>
      match pop_i32 s with
      | Some (c, s') =>
          if I32.eq c I32.zero then Some s' else None
      | None => None
      end

  (* Unmodeled instructions fail honestly.
     The catch-all returns None (failure) rather than Some s (silent no-op)
     so the WASM model does not claim success for instructions it doesn't define.
     This matches the ArmSemantics.v fix from Phase 3.
     Proofs that assume exec_wasm_instr <unmodeled> = Some (...) become
     vacuously true, which is honest: we don't claim correctness for
     instructions we haven't modeled. *)
  | _ => None
  end.

(** Execute a sequence of instructions *)
Fixpoint exec_wasm_program (prog : list wasm_instr) (s : wasm_state) : option wasm_state :=
  match prog with
  | [] => Some s
  | i :: rest =>
      match exec_wasm_instr i s with
      | Some s' => exec_wasm_program rest s'
      | None => None
      end
  end.

(** ** Branch-observable execution (#1057, RQ-60-CFOBLIG increment 1)

    [exec_wasm_program] is a straight-line executor: it cannot represent a
    control transfer, which is why [exec_wasm_instr] declines a taken
    [BrIf]. [exec_wasm_seq] makes the transfer OBSERVABLE instead of
    unrepresentable: executing a sequence either falls through its end
    ([WFallthrough]) or exits early toward the label at the given depth
    ([WBranch l]) — the WasmCert-style "break" administrative outcome at
    the smallest scale that can state a correspondence with the ARM
    branch-taking executor [exec_program_br] (ArmSemantics.v). What it
    deliberately does NOT model yet: the enclosing label stack
    ([Block]/[Loop]/[End]) that would CONSUME a [WBranch] and resume at
    the target — that is the named follow-up, not this increment. *)

Inductive wasm_outcome : Type :=
  | WFallthrough : wasm_state -> wasm_outcome
  | WBranch : nat -> wasm_state -> wasm_outcome.

Fixpoint exec_wasm_seq (prog : list wasm_instr) (s : wasm_state)
    : option wasm_outcome :=
  match prog with
  | [] => Some (WFallthrough s)
  | BrIf l :: rest =>
      match pop_i32 s with
      | Some (c, s') =>
          if I32.eq c I32.zero
          then exec_wasm_seq rest s'      (* not taken: fall through *)
          else Some (WBranch l s')        (* taken: exit toward depth l *)
      | None => None
      end
  | i :: rest =>
      match exec_wasm_instr i s with
      | Some s' => exec_wasm_seq rest s'
      | None => None
      end
  end.

(** A program is branch-free when it contains no [BrIf]. *)
Definition brif_free (prog : list wasm_instr) : bool :=
  forallb (fun i => match i with BrIf _ => false | _ => true end) prog.

(** On branch-free programs the outcome executor IS the straight-line
    executor: [exec_wasm_seq] refines [exec_wasm_program] with a
    [WFallthrough] wrapper. This pins the new executor to the one the 600+
    existing theorems are stated against — the extension cannot have
    changed straight-line behavior. *)
Lemma exec_wasm_seq_brif_free : forall prog s,
  brif_free prog = true ->
  exec_wasm_seq prog s =
  match exec_wasm_program prog s with
  | Some s' => Some (WFallthrough s')
  | None => None
  end.
Proof.
  induction prog as [| i rest IH]; intros s Hfree.
  - reflexivity.
  - unfold brif_free in Hfree. simpl in Hfree.
    apply andb_prop in Hfree. destruct Hfree as [Hi Hrest].
    (* [cbn] restricted to the two executors: unfolding [exec_wasm_instr]
       on a concrete constructor would erase the term the [destruct]
       case-splits on. *)
    destruct i; try discriminate Hi;
      cbn [exec_wasm_seq exec_wasm_program];
      destruct (exec_wasm_instr _ s);
      first [ apply IH; exact Hrest | reflexivity ].
Qed.

(** Unfolding pair for a [BrIf] at the head of a sequence — the two-sided
    semantics in the shape the correspondence proof consumes. *)
Lemma exec_wasm_seq_brif_taken : forall l rest s c s',
  pop_i32 s = Some (c, s') ->
  I32.eq c I32.zero = false ->
  exec_wasm_seq (BrIf l :: rest) s = Some (WBranch l s').
Proof.
  intros l rest s c s' Hpop Hc. simpl. rewrite Hpop, Hc. reflexivity.
Qed.

Lemma exec_wasm_seq_brif_not_taken : forall l rest s c s',
  pop_i32 s = Some (c, s') ->
  I32.eq c I32.zero = true ->
  exec_wasm_seq (BrIf l :: rest) s = exec_wasm_seq rest s'.
Proof.
  intros l rest s c s' Hpop Hc. simpl. rewrite Hpop, Hc. reflexivity.
Qed.

(** ** Properties *)

(** Determinacy *)
Theorem exec_wasm_instr_deterministic : forall i s s1 s2,
  exec_wasm_instr i s = Some s1 ->
  exec_wasm_instr i s = Some s2 ->
  s1 = s2.
Proof.
  intros i s s1 s2 H1 H2.
  rewrite H1 in H2.
  injection H2. auto.
Qed.

(** Type preservation for I32Add *)
Theorem i32_add_type_preservation : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exists result,
    exec_wasm_instr I32Add s =
    Some (mkWasmState
            (VI32 result :: stack')
            s.(locals)
            s.(globals)
            s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  exists (I32.add v1 v2).
  unfold exec_wasm_instr.
  unfold pop2_i32, pop2.
  rewrite Hstack.
  simpl. reflexivity.
Qed.

(** I32Add is commutative *)
Theorem i32_add_commutative : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  let result1 := I32.add v1 v2 in
  let result2 := I32.add v2 v1 in
  result1 = result2.
Proof.
  intros. apply I32.add_commut.
Qed.

(** Executing an empty program doesn't change state *)
Theorem exec_wasm_program_nil : forall s,
  exec_wasm_program (@nil wasm_instr) s = Some s.
Proof.
  intros. reflexivity.
Qed.

(** Program composition *)
Theorem exec_wasm_program_app : forall p1 p2 s,
  exec_wasm_program (p1 ++ p2) s =
  match exec_wasm_program p1 s with
  | Some s' => exec_wasm_program p2 s'
  | None => None
  end.
Proof.
  induction p1; intros.
  - simpl. reflexivity.
  - simpl. destruct (exec_wasm_instr a s) eqn:E.
    + apply IHp1.
    + reflexivity.
Qed.

(** LocalGet after LocalSet returns the set value *)
Theorem local_set_get : forall idx value s stack',
  s.(stack) = VI32 value :: stack' ->
  exec_wasm_instr (LocalSet idx) s =
  Some (mkWasmState
          stack'
          (s.(locals) [idx |-> value])
          s.(globals)
          s.(memory)) /\
  forall s',
    exec_wasm_instr (LocalSet idx) s = Some s' ->
    exec_wasm_instr (LocalGet idx) s' =
    Some (push_value (VI32 value) s').
Proof.
  intros idx value s stack' Hstack.
  split.
  - unfold exec_wasm_instr.
    unfold pop_i32, pop_value, pop.
    rewrite Hstack. simpl. reflexivity.
  - intros s' Hset.
    unfold exec_wasm_instr in Hset.
    unfold pop_i32, pop_value, pop in Hset.
    rewrite Hstack in Hset.
    simpl in Hset.
    injection Hset as Heq. subst s'.
    unfold exec_wasm_instr, push_value.
    simpl.
    rewrite update_eq.
    reflexivity.
Qed.
