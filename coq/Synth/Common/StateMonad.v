(** * State Monad for Processor State

    This file provides a state monad for modeling processor state
    transformations.
*)

Require Import Synth.Common.Base.

(** ** State Monad Definition *)

Definition State (S A : Type) := S -> A * S.

Definition ret {S A : Type} (x : A) : State S A :=
  fun s => (x, s).

Definition bind {S A B : Type} (m : State S A) (f : A -> State S B) : State S B :=
  fun s =>
    let '(x, s') := m s in
    f x s'.

Notation "x <- m ; f" := (bind m (fun x => f))
  (at level 60, right associativity).

Definition get {S : Type} : State S S :=
  fun s => (s, s).

Definition put {S : Type} (s : S) : State S unit :=
  fun _ => (tt, s).

Definition modify {S : Type} (f : S -> S) : State S unit :=
  fun s => (tt, f s).

Definition run_state {S A : Type} (m : State S A) (s : S) : A * S := m s.

Definition eval_state {S A : Type} (m : State S A) (s : S) : A :=
  fst (run_state m s).

Definition exec_state {S A : Type} (m : State S A) (s : S) : S :=
  snd (run_state m s).

(** ** State Monad Laws *)

Theorem bind_ret_left : forall {S A B : Type} (x : A) (f : A -> State S B),
  bind (ret x) f = f x.
Proof.
  intros. reflexivity.
Qed.

Theorem bind_ret_right : forall {S A : Type} (m : State S A),
  bind m ret = m.
Proof.
  intros. extensionality s.
  unfold bind, ret.
  destruct (m s). reflexivity.
Qed.

Theorem bind_assoc : forall {S A B C : Type} (m : State S A)
                             (f : A -> State S B) (g : B -> State S C),
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  intros. extensionality s.
  unfold bind.
  destruct (m s). reflexivity.
Qed.
