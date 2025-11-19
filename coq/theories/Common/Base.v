(** * Common Base Definitions for Synth Verification

    This file contains common utilities and notations used throughout
    the Synth verification framework.
*)

Require Import ZArith.
Require Import List.
Require Import Omega.
Import ListNotations.
Open Scope Z_scope.

(** ** Decidable Equality *)

(** A type has decidable equality if we can decide whether two values are equal *)
Class EqDec (A : Type) := {
  eq_dec : forall (x y : A), {x = y} + {x <> y}
}.

(** ** Option Monad *)

Definition bind_option {A B : Type} (m : option A) (f : A -> option B) : option B :=
  match m with
  | Some x => f x
  | None => None
  end.

Notation "x >>= f" := (bind_option x f) (at level 42, left associativity).

Definition ret_option {A : Type} (x : A) : option A := Some x.

(** ** Result Type for Error Handling *)

Inductive result (A : Type) : Type :=
  | Ok : A -> result A
  | Error : string -> result A.

Arguments Ok {A}.
Arguments Error {A}.

Definition bind_result {A B : Type} (m : result A) (f : A -> result B) : result B :=
  match m with
  | Ok x => f x
  | Error msg => Error msg
  end.

Notation "x >>=r f" := (bind_result x f) (at level 42, left associativity).

Definition ret_result {A : Type} (x : A) : result A := Ok x.

(** ** Function Update *)

(** Update a function at a specific point *)
Definition update {A B : Type} `{EqDec A} (f : A -> B) (x : A) (v : B) : A -> B :=
  fun y => if eq_dec x y then v else f y.

Notation "f [ x |-> v ]" := (update f x v) (at level 10).

(** ** Theorems about update *)

Theorem update_eq : forall {A B : Type} `{EqDec A} (f : A -> B) (x : A) (v : B),
  (f [x |-> v]) x = v.
Proof.
  intros. unfold update.
  destruct (eq_dec x x); [reflexivity | contradiction].
Qed.

Theorem update_neq : forall {A B : Type} `{EqDec A} (f : A -> B) (x y : A) (v : B),
  x <> y ->
  (f [x |-> v]) y = f y.
Proof.
  intros. unfold update.
  destruct (eq_dec x y); [contradiction | reflexivity].
Qed.

Theorem update_shadow : forall {A B : Type} `{EqDec A} (f : A -> B) (x : A) (v1 v2 : B),
  (f [x |-> v1]) [x |-> v2] = f [x |-> v2].
Proof.
  intros. extensionality y.
  unfold update.
  destruct (eq_dec x y); reflexivity.
Qed.

Theorem update_commute : forall {A B : Type} `{EqDec A} (f : A -> B) (x1 x2 : A) (v1 v2 : B),
  x1 <> x2 ->
  (f [x1 |-> v1]) [x2 |-> v2] = (f [x2 |-> v2]) [x1 |-> v1].
Proof.
  intros. extensionality y.
  unfold update.
  destruct (eq_dec x1 y); destruct (eq_dec x2 y); try reflexivity.
  - subst. contradiction.
Qed.

(** ** Byte Operations *)

Definition byte := Z.

Definition byte_bound : byte := 256.

Definition valid_byte (b : byte) : Prop :=
  0 <= b < byte_bound.

(** ** Useful Tactics *)

Ltac inv H := inversion H; subst; clear H.

Ltac break_match :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X eqn:?
  | [ H : context[match ?X with _ => _ end] |- _ ] => destruct X eqn:?
  end.

Ltac solve_by_inversion :=
  match goal with
  | [ H : _ |- _ ] => solve [inversion H]
  end.
