(** * ARM Processor State

    This file formalizes the ARM processor state, including:
    - General-purpose registers (R0-R15)
    - Condition flags (N, Z, C, V)
    - VFP (floating-point) registers
    - Memory

    Based on synth-verify/src/arm_semantics.rs
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.

Import ListNotations.
Open Scope Z_scope.

(** ** ARM Registers *)

Inductive arm_reg : Type :=
  | R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7
  | R8 | R9 | R10 | R11 | R12
  | SP  (* R13 - Stack Pointer *)
  | LR  (* R14 - Link Register *)
  | PC. (* R15 - Program Counter *)

(** Decidable equality for registers *)
Lemma arm_reg_eq_dec : forall (r1 r2 : arm_reg), {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality.
Defined.

#[export] Instance arm_reg_EqDec : EqDec arm_reg := {
  eq_dec := arm_reg_eq_dec
}.

(** Convert register to index (0-15) *)
Definition reg_to_nat (r : arm_reg) : nat :=
  match r with
  | R0 => 0 | R1 => 1 | R2 => 2 | R3 => 3
  | R4 => 4 | R5 => 5 | R6 => 6 | R7 => 7
  | R8 => 8 | R9 => 9 | R10 => 10 | R11 => 11
  | R12 => 12 | SP => 13 | LR => 14 | PC => 15
  end.

(** ** VFP (Floating-Point) Registers *)

Inductive vfp_reg : Type :=
  (* Single-precision registers S0-S31 *)
  | S0 | S1 | S2 | S3 | S4 | S5 | S6 | S7
  | S8 | S9 | S10 | S11 | S12 | S13 | S14 | S15
  | S16 | S17 | S18 | S19 | S20 | S21 | S22 | S23
  | S24 | S25 | S26 | S27 | S28 | S29 | S30 | S31
  (* Double-precision registers D0-D15 *)
  | D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7
  | D8 | D9 | D10 | D11 | D12 | D13 | D14 | D15.

(** Convert VFP register to index (0-47) *)
Definition vfp_reg_to_nat (r : vfp_reg) : nat :=
  match r with
  | S0 => 0 | S1 => 1 | S2 => 2 | S3 => 3
  | S4 => 4 | S5 => 5 | S6 => 6 | S7 => 7
  | S8 => 8 | S9 => 9 | S10 => 10 | S11 => 11
  | S12 => 12 | S13 => 13 | S14 => 14 | S15 => 15
  | S16 => 16 | S17 => 17 | S18 => 18 | S19 => 19
  | S20 => 20 | S21 => 21 | S22 => 22 | S23 => 23
  | S24 => 24 | S25 => 25 | S26 => 26 | S27 => 27
  | S28 => 28 | S29 => 29 | S30 => 30 | S31 => 31
  | D0 => 32 | D1 => 33 | D2 => 34 | D3 => 35
  | D4 => 36 | D5 => 37 | D6 => 38 | D7 => 39
  | D8 => 40 | D9 => 41 | D10 => 42 | D11 => 43
  | D12 => 44 | D13 => 45 | D14 => 46 | D15 => 47
  end.

(** Decidable equality for VFP registers *)
Lemma vfp_reg_eq_dec : forall (r1 r2 : vfp_reg), {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality.
Defined.

#[export] Instance vfp_reg_EqDec : EqDec vfp_reg := {
  eq_dec := vfp_reg_eq_dec
}.

(** ** Condition Flags *)

Record condition_flags : Type := mkFlags {
  flag_n : bool;  (* Negative *)
  flag_z : bool;  (* Zero *)
  flag_c : bool;  (* Carry *)
  flag_v : bool   (* Overflow *)
}.

(** ** Register File *)

Definition regfile := arm_reg -> I32.int.
Definition vfp_regfile := vfp_reg -> I32.int.

(** ** Memory Model *)

(** Simplified memory model: address -> word *)
Definition memory := Z -> I32.int.

(** ** ARM Processor State *)

Record arm_state : Type := mkArmState {
  regs : regfile;
  flags : condition_flags;
  vfp_regs : vfp_regfile;
  mem : memory;
  (* WASM integration: locals and globals *)
  locals : nat -> I32.int;
  globals : nat -> I32.int;
}.

(** ** State Accessors *)

Definition get_reg (s : arm_state) (r : arm_reg) : I32.int :=
  s.(regs) r.

Definition set_reg (s : arm_state) (r : arm_reg) (v : I32.int) : arm_state :=
  mkArmState
    (s.(regs) [r |-> v])
    s.(flags)
    s.(vfp_regs)
    s.(mem)
    s.(locals)
    s.(globals).

Definition get_vfp_reg (s : arm_state) (r : vfp_reg) : I32.int :=
  s.(vfp_regs) r.

Definition set_vfp_reg (s : arm_state) (r : vfp_reg) (v : I32.int) : arm_state :=
  mkArmState
    s.(regs)
    s.(flags)
    (s.(vfp_regs) [r |-> v])
    s.(mem)
    s.(locals)
    s.(globals).

Definition set_flags (s : arm_state) (f : condition_flags) : arm_state :=
  mkArmState
    s.(regs)
    f
    s.(vfp_regs)
    s.(mem)
    s.(locals)
    s.(globals).

Definition load_mem (s : arm_state) (addr : Z) : I32.int :=
  s.(mem) addr.

Definition store_mem (s : arm_state) (addr : Z) (v : I32.int) : arm_state :=
  mkArmState
    s.(regs)
    s.(flags)
    s.(vfp_regs)
    (s.(mem) [addr |-> v])
    s.(locals)
    s.(globals).

Definition get_local (s : arm_state) (idx : nat) : I32.int :=
  s.(locals) idx.

Definition set_local (s : arm_state) (idx : nat) (v : I32.int) : arm_state :=
  mkArmState
    s.(regs)
    s.(flags)
    s.(vfp_regs)
    s.(mem)
    (s.(locals) [idx |-> v])
    s.(globals).

Definition get_global (s : arm_state) (idx : nat) : I32.int :=
  s.(globals) idx.

Definition set_global (s : arm_state) (idx : nat) (v : I32.int) : arm_state :=
  mkArmState
    s.(regs)
    s.(flags)
    s.(vfp_regs)
    s.(mem)
    s.(locals)
    (s.(globals) [idx |-> v]).

(** ** Properties *)

(** Getting a register after setting it returns the set value *)
Theorem get_set_reg_eq : forall s r v,
  get_reg (set_reg s r v) r = v.
Proof.
  intros. unfold get_reg, set_reg. simpl.
  apply update_eq.
Qed.

(** Getting a different register after setting returns the old value *)
Theorem get_set_reg_neq : forall s r1 r2 v,
  r1 <> r2 ->
  get_reg (set_reg s r1 v) r2 = get_reg s r2.
Proof.
  intros. unfold get_reg, set_reg. simpl.
  apply update_neq. auto.
Qed.

(** Setting a register doesn't affect flags *)
Theorem set_reg_preserves_flags : forall s r v,
  (set_reg s r v).(flags) = s.(flags).
Proof.
  intros. reflexivity.
Qed.

(** Setting a register doesn't affect memory *)
Theorem set_reg_preserves_mem : forall s r v,
  (set_reg s r v).(mem) = s.(mem).
Proof.
  intros. reflexivity.
Qed.

(** Loading memory after storing returns the stored value *)
Theorem load_store_mem_eq : forall s addr v,
  load_mem (store_mem s addr v) addr = v.
Proof.
  intros. unfold load_mem, store_mem. simpl.
  apply update_eq.
Qed.

(** Loading from a different address after storing returns old value *)
Theorem load_store_mem_neq : forall s addr1 addr2 v,
  addr1 <> addr2 ->
  load_mem (store_mem s addr1 v) addr2 = load_mem s addr2.
Proof.
  intros. unfold load_mem, store_mem. simpl.
  apply update_neq. auto.
Qed.
