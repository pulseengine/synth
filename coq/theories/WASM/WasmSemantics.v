(** * WebAssembly Operational Semantics

    This file defines the operational semantics of WebAssembly instructions
    using a stack machine model.

    Based on synth-verify/src/wasm_semantics.rs
*)

Require Import ZArith.
Require Import List.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.WASM.WasmValues.
Require Import Synth.WASM.WasmInstructions.

Import ListNotations.
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
  (* Constants *)
  | I32Const n =>
      Some (push_value (VI32 n) s)

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

  (* Not yet implemented *)
  | _ => Some s
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
  exec_wasm_program [] s = Some s.
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
  - simpl. destruct (exec_wasm_instr a s) eqn:E; auto.
    apply IHp1.
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
