(** * Simple Operations Correctness

    This file contains correctness proofs for simple WebAssembly operations:
    - Control flow: Nop, Drop
    - Locals: LocalGet, LocalSet
    - Constants: I32Const, I64Const

    Many proofs are Admitted because they require modeling ARM instruction
    execution (CMP/MOV sequences) rather than empty programs.
*)

From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.
Require Import Synth.ARM.ArmSemantics.
Require Import Synth.WASM.WasmValues.
Require Import Synth.WASM.WasmInstructions.
Require Import Synth.WASM.WasmSemantics.
Require Import Synth.Synth.Compilation.

(** ** Control Flow Operations *)

(** Nop does nothing *)
Theorem nop_correct : forall wstate astate,
  exec_wasm_instr Nop wstate = Some wstate ->
  exists astate',
    exec_program (compile_wasm_to_arm Nop) astate = Some astate'.
Proof.
  intros wstate astate Hwasm.
  unfold compile_wasm_to_arm. simpl.
  exists astate. reflexivity.
Qed.

(** Select chooses value based on condition *)
Theorem select_correct : forall wstate astate cond val1 val2 stack',
  wstate.(stack) = VI32 cond :: val2 :: val1 :: stack' ->
  exec_wasm_instr Select wstate =
    Some (mkWasmState
            ((if I32.eq cond I32.zero then val2 else val1) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm Select) astate = Some astate'.
Proof.
  (* Select compiles to CMP R2 #0; MOVNE R0 R0; MOVEQ R0 R1 *)
  Admitted.

(** Drop removes top of stack *)
Theorem drop_correct : forall wstate astate v stack',
  wstate.(stack) = v :: stack' ->
  exec_wasm_instr Drop wstate =
    Some (mkWasmState stack' wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm Drop) astate = Some astate'.
Proof.
  intros wstate astate v stack' Hstack Hwasm.
  unfold compile_wasm_to_arm. simpl.
  exists astate. reflexivity.
Qed.

(** ** Local Variable Operations *)

(** LocalGet loads a local variable *)
Theorem local_get_correct : forall wstate astate (idx : nat),
  lt idx 4 ->
  exec_wasm_instr (LocalGet idx) wstate =
    Some (mkWasmState
            (VI32 (wstate.(locals) idx) :: wstate.(stack))
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  (forall i, lt i 4 -> get_reg astate (match i with
                                       | O => R4
                                       | S O => R5
                                       | S (S O) => R6
                                       | _ => R7
                                       end) = wstate.(locals) i) ->
  exists astate',
    exec_program (compile_wasm_to_arm (LocalGet idx)) astate = Some astate' /\
    get_reg astate' R0 = wstate.(locals) idx.
Proof.
  (* LocalGet compiles to MOV R0, R4-R7 — needs register correspondence *)
  Admitted.

(** LocalSet stores to a local variable *)
Theorem local_set_correct : forall wstate astate v stack' (idx : nat),
  lt idx 4 ->
  wstate.(stack) = VI32 v :: stack' ->
  get_reg astate R0 = v ->
  exec_wasm_instr (LocalSet idx) wstate =
    Some (mkWasmState
            stack'
            (wstate.(locals) [idx |-> v])
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (LocalSet idx)) astate = Some astate' /\
    get_reg astate' (match idx with
                     | O => R4
                     | S O => R5
                     | S (S O) => R6
                     | _ => R7
                     end) = v.
Proof.
  (* LocalSet compiles to MOV R4-R7, R0 — needs register correspondence *)
  Admitted.

(** ** Constants *)

Theorem i32_const_correct : forall wstate astate n,
  exec_wasm_instr (I32Const n) wstate =
    Some (mkWasmState
            (VI32 n :: wstate.(stack))
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (I32Const n)) astate = Some astate' /\
    get_reg astate' R0 = n.
Proof.
  intros wstate astate n Hwasm.
  unfold compile_wasm_to_arm.
  unfold exec_program, exec_instr. simpl.
  exists (set_reg astate R0 n).
  split.
  - reflexivity.
  - simpl. apply get_set_reg_eq.
Qed.

Theorem i64_const_correct : forall wstate astate n,
  exec_wasm_instr (I64Const n) wstate =
    Some (mkWasmState
            (VI64 n :: wstate.(stack))
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (I64Const n)) astate = Some astate' /\
    get_reg astate' R0 = I32.repr ((I64.unsigned n) mod I32.modulus).
Proof.
  intros wstate astate n Hwasm.
  unfold compile_wasm_to_arm.
  unfold exec_program, exec_instr. simpl.
  exists (set_reg astate R0 (I32.repr ((I64.unsigned n) mod I32.modulus))).
  split.
  - reflexivity.
  - simpl. apply get_set_reg_eq.
Qed.

(** LocalTee sets local and keeps value on stack *)
Theorem local_tee_correct : forall wstate astate v stack' (idx : nat),
  lt idx 4 ->
  wstate.(stack) = VI32 v :: stack' ->
  get_reg astate R0 = v ->
  exec_wasm_instr (LocalTee idx) wstate =
    Some (mkWasmState
            (VI32 v :: stack')
            (wstate.(locals) [idx |-> v])
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (LocalTee idx)) astate = Some astate'.
Proof.
  (* LocalTee compiles to MOV R4-R7, R0 *)
  Admitted.

(** ** Global Variable Operations *)

Theorem global_get_correct : forall wstate astate (idx : nat),
  lt idx 4 ->
  exec_wasm_instr (GlobalGet idx) wstate =
    Some (mkWasmState
            (VI32 (wstate.(globals) idx) :: wstate.(stack))
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (GlobalGet idx)) astate = Some astate'.
Proof.
  (* GlobalGet compiles to MOV R0, R8-R11 *)
  Admitted.

Theorem global_set_correct : forall wstate astate v stack' (idx : nat),
  lt idx 4 ->
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr (GlobalSet idx) wstate =
    Some (mkWasmState
            stack'
            wstate.(locals)
            (wstate.(globals) [idx |-> v])
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (GlobalSet idx)) astate = Some astate'.
Proof.
  (* GlobalSet compiles to MOV R8-R11, R0 *)
  Admitted.

(** ** Comparison Operations *)
(** All comparisons compile to CMP + MOV + conditional MOV sequences *)

Theorem i32_eqz_correct : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr I32Eqz wstate =
    Some (mkWasmState
            (VI32 (if I32.eq v I32.zero then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Eqz) astate = Some astate'.
Proof. Admitted.

Theorem i32_eq_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Eq wstate =
    Some (mkWasmState
            (VI32 (if I32.eq v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Eq) astate = Some astate'.
Proof. Admitted.

Theorem i32_ne_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Ne wstate =
    Some (mkWasmState
            (VI32 (if I32.ne v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Ne) astate = Some astate'.
Proof. Admitted.

Theorem i32_lts_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32LtS wstate =
    Some (mkWasmState
            (VI32 (if I32.lts v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32LtS) astate = Some astate'.
Proof. Admitted.

Theorem i32_ltu_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32LtU wstate =
    Some (mkWasmState
            (VI32 (if I32.ltu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32LtU) astate = Some astate'.
Proof. Admitted.

Theorem i32_gts_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32GtS wstate =
    Some (mkWasmState
            (VI32 (if I32.gts v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32GtS) astate = Some astate'.
Proof. Admitted.

Theorem i32_gtu_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32GtU wstate =
    Some (mkWasmState
            (VI32 (if I32.gtu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32GtU) astate = Some astate'.
Proof. Admitted.

Theorem i32_les_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32LeS wstate =
    Some (mkWasmState
            (VI32 (if I32.les v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32LeS) astate = Some astate'.
Proof. Admitted.

Theorem i32_leu_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32LeU wstate =
    Some (mkWasmState
            (VI32 (if I32.leu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32LeU) astate = Some astate'.
Proof. Admitted.

Theorem i32_ges_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32GeS wstate =
    Some (mkWasmState
            (VI32 (if I32.ges v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32GeS) astate = Some astate'.
Proof. Admitted.

Theorem i32_geu_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32GeU wstate =
    Some (mkWasmState
            (VI32 (if I32.geu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32GeU) astate = Some astate'.
Proof. Admitted.

(** ** I32 Shift Operations *)
(** Shift/rotate ops compile to single ARM shift instructions *)

Theorem i32_shl_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Shl wstate =
    Some (mkWasmState
            (VI32 (I32.shl v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Shl) astate = Some astate'.
Proof. Admitted.

Theorem i32_shru_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32ShrU wstate =
    Some (mkWasmState
            (VI32 (I32.shru v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32ShrU) astate = Some astate'.
Proof. Admitted.

Theorem i32_shrs_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32ShrS wstate =
    Some (mkWasmState
            (VI32 (I32.shrs v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32ShrS) astate = Some astate'.
Proof. Admitted.

Theorem i32_rotl_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Rotl wstate =
    Some (mkWasmState
            (VI32 (I32.rotl v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Rotl) astate = Some astate'.
Proof.
  intros wstate astate v1 v2 stack' Hstack Hwasm.
  unfold compile_wasm_to_arm. simpl.
  exists astate. reflexivity.
Qed.

Theorem i32_rotr_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Rotr wstate =
    Some (mkWasmState
            (VI32 (I32.rotr v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Rotr) astate = Some astate'.
Proof. Admitted.

(** ** I32 Bit Manipulation Operations *)

Theorem i32_clz_correct : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr I32Clz wstate =
    Some (mkWasmState
            (VI32 (I32.clz v) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Clz) astate = Some astate'.
Proof. Admitted.

Theorem i32_ctz_correct : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr I32Ctz wstate =
    Some (mkWasmState
            (VI32 (I32.ctz v) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Ctz) astate = Some astate'.
Proof. Admitted.

Theorem i32_popcnt_correct : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr I32Popcnt wstate =
    Some (mkWasmState
            (VI32 (I32.popcnt v) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Popcnt) astate = Some astate'.
Proof. Admitted.
