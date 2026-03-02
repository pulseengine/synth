(** * Memory Operations Correctness

    This file contains correctness proofs for memory WebAssembly operations.
    Total: 8 operations (4 loads + 4 stores)

    Status after catch-all removal:
    - 4 Qed: I32/I64 loads and stores (LDR/STR have real semantics)
    - 4 Admitted: F32/F64 loads and stores (VLDR/VSTR have no modeled semantics)
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

(** Helper tactic for single-instruction memory proofs *)
Ltac solve_mem_single :=
  intros; unfold compile_wasm_to_arm;
  unfold exec_program; simpl;
  eexists; reflexivity.

(** ** Integer Load Operations — Qed *)

Theorem i32_load_executes : forall wstate astate addr stack' (offset : nat),
  wstate.(stack) = VI32 addr :: stack' ->
  exec_wasm_instr (I32Load offset) wstate =
    Some (mkWasmState (VI32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (I32Load offset)) astate = Some astate'.
Proof. solve_mem_single. Qed.

Theorem i64_load_executes : forall wstate astate addr stack' (offset : nat),
  wstate.(stack) = VI32 addr :: stack' ->
  exec_wasm_instr (I64Load offset) wstate =
    Some (mkWasmState (VI64 I64.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (I64Load offset)) astate = Some astate'.
Proof. solve_mem_single. Qed.

(** ** Float Load Operations — Admitted *)

Theorem f32_load_executes : forall wstate astate addr stack' (offset : nat),
  wstate.(stack) = VI32 addr :: stack' ->
  exec_wasm_instr (F32Load offset) wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (F32Load offset)) astate = Some astate'.
Proof. (* ADMITTED: VLDR_F32 has no modeled semantics *) Admitted.

Theorem f64_load_executes : forall wstate astate addr stack' (offset : nat),
  wstate.(stack) = VI32 addr :: stack' ->
  exec_wasm_instr (F64Load offset) wstate =
    Some (mkWasmState (VF64 I64.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (F64Load offset)) astate = Some astate'.
Proof. (* ADMITTED: VLDR_F64 has no modeled semantics *) Admitted.

(** ** Integer Store Operations — Qed *)

Theorem i32_store_executes : forall wstate astate addr value stack' (offset : nat),
  wstate.(stack) = VI32 value :: VI32 addr :: stack' ->
  exec_wasm_instr (I32Store offset) wstate =
    Some (mkWasmState stack'
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (I32Store offset)) astate = Some astate'.
Proof. solve_mem_single. Qed.

Theorem i64_store_executes : forall wstate astate addr value stack' (offset : nat),
  wstate.(stack) = VI64 value :: VI32 addr :: stack' ->
  exec_wasm_instr (I64Store offset) wstate =
    Some (mkWasmState stack'
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (I64Store offset)) astate = Some astate'.
Proof. solve_mem_single. Qed.

(** ** Float Store Operations — Admitted *)

Theorem f32_store_executes : forall wstate astate addr value stack' (offset : nat),
  wstate.(stack) = VF32 value :: VI32 addr :: stack' ->
  exec_wasm_instr (F32Store offset) wstate =
    Some (mkWasmState stack'
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (F32Store offset)) astate = Some astate'.
Proof. (* ADMITTED: VSTR_F32 has no modeled semantics *) Admitted.

Theorem f64_store_executes : forall wstate astate addr value stack' (offset : nat),
  wstate.(stack) = VF64 value :: VI32 addr :: stack' ->
  exec_wasm_instr (F64Store offset) wstate =
    Some (mkWasmState stack'
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (F64Store offset)) astate = Some astate'.
Proof. (* ADMITTED: VSTR_F64 has no modeled semantics *) Admitted.

(** ** Summary: 8 Memory Operations
    - 4 Qed: I32Load, I64Load, I32Store, I64Store (LDR/STR have real semantics)
    - 4 Admitted: F32Load, F64Load, F32Store, F64Store (VLDR/VSTR unmodeled)
*)
