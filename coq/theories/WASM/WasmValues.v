(** * WebAssembly Values

    This file defines WebAssembly value types.
*)

Require Import ZArith.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.

Open Scope Z_scope.

(** ** WebAssembly Value Types *)

Inductive wasm_val : Type :=
  | VI32 : I32.int -> wasm_val
  | VI64 : I64.int -> wasm_val
  | VF32 : I32.int -> wasm_val  (* Represented as bit pattern *)
  | VF64 : I64.int -> wasm_val. (* Represented as bit pattern *)

(** ** Stack *)

Definition wasm_stack := list wasm_val.

(** ** Stack Operations *)

Definition push (v : wasm_val) (stack : wasm_stack) : wasm_stack :=
  v :: stack.

Definition pop (stack : wasm_stack) : option (wasm_val * wasm_stack) :=
  match stack with
  | [] => None
  | v :: rest => Some (v, rest)
  end.

Definition pop2 (stack : wasm_stack) : option (wasm_val * wasm_val * wasm_stack) :=
  match stack with
  | v2 :: v1 :: rest => Some (v1, v2, rest)
  | _ => None
  end.

(** ** Type Checking Helpers *)

Definition is_i32 (v : wasm_val) : bool :=
  match v with
  | VI32 _ => true
  | _ => false
  end.

Definition is_i64 (v : wasm_val) : bool :=
  match v with
  | VI64 _ => true
  | _ => false
  end.

Definition is_f32 (v : wasm_val) : bool :=
  match v with
  | VF32 _ => true
  | _ => false
  end.

Definition is_f64 (v : wasm_val) : bool :=
  match v with
  | VF64 _ => true
  | _ => false
  end.

(** ** Extract Values (with type checking) *)

Definition get_i32 (v : wasm_val) : option I32.int :=
  match v with
  | VI32 n => Some n
  | _ => None
  end.

Definition get_i64 (v : wasm_val) : option I64.int :=
  match v with
  | VI64 n => Some n
  | _ => None
  end.

Definition get_f32 (v : wasm_val) : option I32.int :=
  match v with
  | VF32 bits => Some bits
  | _ => None
  end.

Definition get_f64 (v : wasm_val) : option I64.int :=
  match v with
  | VF64 bits => Some bits
  | _ => None
  end.

(** ** Properties *)

Theorem push_pop : forall v stack,
  pop (push v stack) = Some (v, stack).
Proof.
  intros. reflexivity.
Qed.

Theorem pop2_push2 : forall v1 v2 stack,
  pop2 (push v2 (push v1 stack)) = Some (v1, v2, stack).
Proof.
  intros. reflexivity.
Qed.
