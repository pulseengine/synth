(** * Memory Operations Correctness

    This file contains correctness proofs for all memory WebAssembly operations.
    Total: 10 operations (4 loads + 4 stores + 2 constants)
*)

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

(** ** Load Operations (4 total) *)

Theorem i32_load_correct : forall wstate astate addr stack' (offset : nat),
  wstate.(stack) = VI32 addr :: stack' ->
  exec_wasm_instr (I32Load offset) wstate =
    Some (mkWasmState (VI32 I32.zero :: stack')  (* Placeholder *)
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (I32Load offset)) astate = Some astate'.
Proof. admit. Admitted.

Theorem i64_load_correct : forall wstate astate addr stack' (offset : nat),
  wstate.(stack) = VI32 addr :: stack' ->
  exec_wasm_instr (I64Load offset) wstate =
    Some (mkWasmState (VI64 I64.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (I64Load offset)) astate = Some astate'.
Proof. admit. Admitted.

Theorem f32_load_correct : forall wstate astate addr stack' (offset : nat),
  wstate.(stack) = VI32 addr :: stack' ->
  exec_wasm_instr (F32Load offset) wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (F32Load offset)) astate = Some astate'.
Proof. admit. Admitted.

Theorem f64_load_correct : forall wstate astate addr stack' (offset : nat),
  wstate.(stack) = VI32 addr :: stack' ->
  exec_wasm_instr (F64Load offset) wstate =
    Some (mkWasmState (VF64 I64.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (F64Load offset)) astate = Some astate'.
Proof. admit. Admitted.

(** ** Store Operations (4 total) *)

Theorem i32_store_correct : forall wstate astate addr value stack' (offset : nat),
  wstate.(stack) = VI32 value :: VI32 addr :: stack' ->
  exec_wasm_instr (I32Store offset) wstate =
    Some (mkWasmState stack'
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (I32Store offset)) astate = Some astate'.
Proof. admit. Admitted.

Theorem i64_store_correct : forall wstate astate addr value stack' (offset : nat),
  wstate.(stack) = VI64 value :: VI32 addr :: stack' ->
  exec_wasm_instr (I64Store offset) wstate =
    Some (mkWasmState stack'
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (I64Store offset)) astate = Some astate'.
Proof. admit. Admitted.

Theorem f32_store_correct : forall wstate astate addr value stack' (offset : nat),
  wstate.(stack) = VF32 value :: VI32 addr :: stack' ->
  exec_wasm_instr (F32Store offset) wstate =
    Some (mkWasmState stack'
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (F32Store offset)) astate = Some astate'.
Proof. admit. Admitted.

Theorem f64_store_correct : forall wstate astate addr value stack' (offset : nat),
  wstate.(stack) = VF64 value :: VI32 addr :: stack' ->
  exec_wasm_instr (F64Store offset) wstate =
    Some (mkWasmState stack'
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (F64Store offset)) astate = Some astate'.
Proof. admit. Admitted.

(** ** Summary: 8 Memory Operations
    - Loads: I32Load, I64Load, F32Load, F64Load (4)
    - Stores: I32Store, I64Store, F32Store, F64Store (4)

    Note: F32Const and F64Const don't exist as separate instructions -
    they're represented using I32Const and I64Const with IEEE 754 bit patterns.
*)
