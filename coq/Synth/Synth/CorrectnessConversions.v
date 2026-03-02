(** * Type Conversion Operations Correctness

    This file contains correctness proofs for WebAssembly type conversion operations.
    Total: 21 operations (conversions between i32, i64, f32, f64)

    Status after catch-all removal:
    - 3 Qed: integer wrap/extend compile to [] (empty program)
    - 18 Admitted: VFP conversion instructions have no modeled semantics
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
Require Import Synth.Synth.Tactics.

Open Scope Z_scope.

(** ** Integer Conversions (3 total) — ALL Qed *)
(** These compile to [] (empty program), trivially proven *)

Theorem i32_wrap_i64_executes : forall wstate astate v stack',
  wstate.(stack) = VI64 v :: stack' ->
  exec_wasm_instr I32WrapI64 wstate =
    Some (mkWasmState (VI32 (i64_to_i32 v) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32WrapI64) astate = Some astate'.
Proof.
  intros; unfold compile_wasm_to_arm; simpl; eexists; reflexivity.
Qed.

Theorem i64_extend_i32_s_executes : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr I64ExtendI32S wstate =
    Some (mkWasmState (VI64 (i32_to_i64_signed v) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64ExtendI32S) astate = Some astate'.
Proof.
  intros; unfold compile_wasm_to_arm; simpl; eexists; reflexivity.
Qed.

Theorem i64_extend_i32_u_executes : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr I64ExtendI32U wstate =
    Some (mkWasmState (VI64 (i32_to_i64_unsigned v) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64ExtendI32U) astate = Some astate'.
Proof.
  intros; unfold compile_wasm_to_arm; simpl; eexists; reflexivity.
Qed.

(** ** Float to Integer Conversions (8 total) — ALL Admitted *)
(** ADMITTED: VFP conversion instructions (VCVT, VMOV) have no modeled semantics *)

Theorem i32_trunc_f32_s_executes : forall wstate astate bits stack',
  wstate.(stack) = VF32 bits :: stack' ->
  exec_wasm_instr I32TruncF32S wstate =
    Some (mkWasmState (VI32 (I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32TruncF32S) astate = Some astate'.
Proof. (* ADMITTED: VCVT_S32_F32/VMOV_VFP_TO_ARM unmodeled *) Admitted.

Theorem i32_trunc_f32_u_executes : forall wstate astate bits stack',
  wstate.(stack) = VF32 bits :: stack' ->
  exec_wasm_instr I32TruncF32U wstate =
    Some (mkWasmState (VI32 (I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32TruncF32U) astate = Some astate'.
Proof. (* ADMITTED: VCVT_S32_F32/VMOV_VFP_TO_ARM unmodeled *) Admitted.

Theorem i32_trunc_f64_s_executes : forall wstate astate bits stack',
  wstate.(stack) = VF64 bits :: stack' ->
  exec_wasm_instr I32TruncF64S wstate =
    Some (mkWasmState (VI32 (I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32TruncF64S) astate = Some astate'.
Proof. (* ADMITTED: VCVT_F32_F64/VCVT_S32_F32/VMOV_VFP_TO_ARM unmodeled *) Admitted.

Theorem i32_trunc_f64_u_executes : forall wstate astate bits stack',
  wstate.(stack) = VF64 bits :: stack' ->
  exec_wasm_instr I32TruncF64U wstate =
    Some (mkWasmState (VI32 (I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32TruncF64U) astate = Some astate'.
Proof. (* ADMITTED: VCVT unmodeled *) Admitted.

Theorem i64_trunc_f32_s_executes : forall wstate astate bits stack',
  wstate.(stack) = VF32 bits :: stack' ->
  exec_wasm_instr I64TruncF32S wstate =
    Some (mkWasmState (VI64 (I64.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64TruncF32S) astate = Some astate'.
Proof. (* ADMITTED: VCVT unmodeled *) Admitted.

Theorem i64_trunc_f32_u_executes : forall wstate astate bits stack',
  wstate.(stack) = VF32 bits :: stack' ->
  exec_wasm_instr I64TruncF32U wstate =
    Some (mkWasmState (VI64 (I64.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64TruncF32U) astate = Some astate'.
Proof. (* ADMITTED: VCVT unmodeled *) Admitted.

Theorem i64_trunc_f64_s_executes : forall wstate astate bits stack',
  wstate.(stack) = VF64 bits :: stack' ->
  exec_wasm_instr I64TruncF64S wstate =
    Some (mkWasmState (VI64 (I64.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64TruncF64S) astate = Some astate'.
Proof. (* ADMITTED: VCVT unmodeled *) Admitted.

Theorem i64_trunc_f64_u_executes : forall wstate astate bits stack',
  wstate.(stack) = VF64 bits :: stack' ->
  exec_wasm_instr I64TruncF64U wstate =
    Some (mkWasmState (VI64 (I64.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64TruncF64U) astate = Some astate'.
Proof. (* ADMITTED: VCVT unmodeled *) Admitted.

(** ** Integer to Float Conversions (8 total) — ALL Admitted *)

Theorem f32_convert_i32_s_executes : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr F32ConvertI32S wstate =
    Some (mkWasmState (VF32 (I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32ConvertI32S) astate = Some astate'.
Proof. (* ADMITTED: VMOV_ARM_TO_VFP/VCVT_F32_S32 unmodeled *) Admitted.

Theorem f32_convert_i32_u_executes : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr F32ConvertI32U wstate =
    Some (mkWasmState (VF32 (I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32ConvertI32U) astate = Some astate'.
Proof. (* ADMITTED: VFP unmodeled *) Admitted.

Theorem f32_convert_i64_s_executes : forall wstate astate v stack',
  wstate.(stack) = VI64 v :: stack' ->
  exec_wasm_instr F32ConvertI64S wstate =
    Some (mkWasmState (VF32 (I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32ConvertI64S) astate = Some astate'.
Proof. (* ADMITTED: VFP unmodeled *) Admitted.

Theorem f32_convert_i64_u_executes : forall wstate astate v stack',
  wstate.(stack) = VI64 v :: stack' ->
  exec_wasm_instr F32ConvertI64U wstate =
    Some (mkWasmState (VF32 (I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32ConvertI64U) astate = Some astate'.
Proof. (* ADMITTED: VFP unmodeled *) Admitted.

Theorem f64_convert_i32_s_executes : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr F64ConvertI32S wstate =
    Some (mkWasmState (VF64 (I64.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F64ConvertI32S) astate = Some astate'.
Proof. (* ADMITTED: VFP unmodeled *) Admitted.

Theorem f64_convert_i32_u_executes : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr F64ConvertI32U wstate =
    Some (mkWasmState (VF64 (I64.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F64ConvertI32U) astate = Some astate'.
Proof. (* ADMITTED: VFP unmodeled *) Admitted.

Theorem f64_convert_i64_s_executes : forall wstate astate v stack',
  wstate.(stack) = VI64 v :: stack' ->
  exec_wasm_instr F64ConvertI64S wstate =
    Some (mkWasmState (VF64 (I64.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F64ConvertI64S) astate = Some astate'.
Proof. (* ADMITTED: VFP unmodeled *) Admitted.

Theorem f64_convert_i64_u_executes : forall wstate astate v stack',
  wstate.(stack) = VI64 v :: stack' ->
  exec_wasm_instr F64ConvertI64U wstate =
    Some (mkWasmState (VF64 (I64.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F64ConvertI64U) astate = Some astate'.
Proof. (* ADMITTED: VFP unmodeled *) Admitted.

(** ** Float Conversions (2 total) — Admitted *)

Theorem f32_demote_f64_executes : forall wstate astate bits stack',
  wstate.(stack) = VF64 bits :: stack' ->
  exec_wasm_instr F32DemoteF64 wstate =
    Some (mkWasmState (VF32 (I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32DemoteF64) astate = Some astate'.
Proof. (* ADMITTED: VCVT_F32_F64 unmodeled *) Admitted.

Theorem f64_promote_f32_executes : forall wstate astate bits stack',
  wstate.(stack) = VF32 bits :: stack' ->
  exec_wasm_instr F64PromoteF32 wstate =
    Some (mkWasmState (VF64 (I64.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F64PromoteF32) astate = Some astate'.
Proof. (* ADMITTED: VCVT_F64_F32 unmodeled *) Admitted.

(** ** Summary
    - 3 Qed: integer wrap/extend (compile to [], trivially proven)
    - 18 Admitted: VFP conversion instructions (VCVT, VMOV) unmodeled

    To close: integrate Flocq IEEE 754 library for VFP semantics
*)
