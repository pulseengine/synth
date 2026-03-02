(** * F32 Operations Correctness

    This file contains correctness proofs for F32 WebAssembly operations.
    Total: 20 operations (14 arithmetic/special + 6 comparisons)

    Status after catch-all removal:
    - 7 Qed: operations compiling to [] (empty program), trivially proven
    - 13 Admitted: VFP instructions have no modeled semantics
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

(** ** F32 Arithmetic Operations — VFP, no semantics *)
(** ADMITTED: Requires VFP floating-point semantics (Flocq integration) *)

Theorem f32_add_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VF32 v2 :: VF32 v1 :: stack' ->
  exec_wasm_instr F32Add wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Add) astate = Some astate'.
Proof.
  (* ADMITTED: VADD_F32 has no modeled semantics — requires Flocq *)
Admitted.

Theorem f32_sub_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VF32 v2 :: VF32 v1 :: stack' ->
  exec_wasm_instr F32Sub wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Sub) astate = Some astate'.
Proof.
  (* ADMITTED: VSUB_F32 has no modeled semantics — requires Flocq *)
Admitted.

Theorem f32_mul_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VF32 v2 :: VF32 v1 :: stack' ->
  exec_wasm_instr F32Mul wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Mul) astate = Some astate'.
Proof.
  (* ADMITTED: VMUL_F32 has no modeled semantics — requires Flocq *)
Admitted.

Theorem f32_div_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VF32 v2 :: VF32 v1 :: stack' ->
  exec_wasm_instr F32Div wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Div) astate = Some astate'.
Proof.
  (* ADMITTED: VDIV_F32 has no modeled semantics — requires Flocq *)
Admitted.

(** ** F32 Special Operations *)

Theorem f32_sqrt_executes : forall wstate astate v stack',
  wstate.(stack) = VF32 v :: stack' ->
  exec_wasm_instr F32Sqrt wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Sqrt) astate = Some astate'.
Proof.
  (* ADMITTED: VSQRT_F32 has no modeled semantics — requires Flocq *)
Admitted.

(** These 7 compile to [] (empty program) — trivially proven *)

Theorem f32_min_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VF32 v2 :: VF32 v1 :: stack' ->
  exec_wasm_instr F32Min wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Min) astate = Some astate'.
Proof.
  intros; unfold compile_wasm_to_arm; simpl; eexists; reflexivity.
Qed.

Theorem f32_max_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VF32 v2 :: VF32 v1 :: stack' ->
  exec_wasm_instr F32Max wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Max) astate = Some astate'.
Proof.
  intros; unfold compile_wasm_to_arm; simpl; eexists; reflexivity.
Qed.

Theorem f32_abs_executes : forall wstate astate v stack',
  wstate.(stack) = VF32 v :: stack' ->
  exec_wasm_instr F32Abs wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Abs) astate = Some astate'.
Proof.
  (* ADMITTED: VABS_F32 has no modeled semantics — requires Flocq *)
Admitted.

Theorem f32_neg_executes : forall wstate astate v stack',
  wstate.(stack) = VF32 v :: stack' ->
  exec_wasm_instr F32Neg wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Neg) astate = Some astate'.
Proof.
  (* ADMITTED: VNEG_F32 has no modeled semantics — requires Flocq *)
Admitted.

Theorem f32_copysign_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VF32 v2 :: VF32 v1 :: stack' ->
  exec_wasm_instr F32Copysign wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Copysign) astate = Some astate'.
Proof.
  intros; unfold compile_wasm_to_arm; simpl; eexists; reflexivity.
Qed.

Theorem f32_ceil_executes : forall wstate astate v stack',
  wstate.(stack) = VF32 v :: stack' ->
  exec_wasm_instr F32Ceil wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Ceil) astate = Some astate'.
Proof.
  intros; unfold compile_wasm_to_arm; simpl; eexists; reflexivity.
Qed.

Theorem f32_floor_executes : forall wstate astate v stack',
  wstate.(stack) = VF32 v :: stack' ->
  exec_wasm_instr F32Floor wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Floor) astate = Some astate'.
Proof.
  intros; unfold compile_wasm_to_arm; simpl; eexists; reflexivity.
Qed.

Theorem f32_trunc_executes : forall wstate astate v stack',
  wstate.(stack) = VF32 v :: stack' ->
  exec_wasm_instr F32Trunc wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Trunc) astate = Some astate'.
Proof.
  intros; unfold compile_wasm_to_arm; simpl; eexists; reflexivity.
Qed.

Theorem f32_nearest_executes : forall wstate astate v stack',
  wstate.(stack) = VF32 v :: stack' ->
  exec_wasm_instr F32Nearest wstate =
    Some (mkWasmState (VF32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Nearest) astate = Some astate'.
Proof.
  intros; unfold compile_wasm_to_arm; simpl; eexists; reflexivity.
Qed.

(** ** F32 Comparison Operations *)
(** ADMITTED: VCMP_F32 has no modeled semantics *)

Theorem f32_eq_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VF32 v2 :: VF32 v1 :: stack' ->
  exec_wasm_instr F32Eq wstate =
    Some (mkWasmState (VI32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Eq) astate = Some astate'.
Proof.
  (* ADMITTED: VCMP_F32 has no modeled semantics — requires Flocq *)
Admitted.

Theorem f32_ne_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VF32 v2 :: VF32 v1 :: stack' ->
  exec_wasm_instr F32Ne wstate =
    Some (mkWasmState (VI32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Ne) astate = Some astate'.
Proof.
  (* ADMITTED: VCMP_F32 has no modeled semantics — requires Flocq *)
Admitted.

Theorem f32_lt_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VF32 v2 :: VF32 v1 :: stack' ->
  exec_wasm_instr F32Lt wstate =
    Some (mkWasmState (VI32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Lt) astate = Some astate'.
Proof.
  (* ADMITTED: VCMP_F32 has no modeled semantics — requires Flocq *)
Admitted.

Theorem f32_gt_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VF32 v2 :: VF32 v1 :: stack' ->
  exec_wasm_instr F32Gt wstate =
    Some (mkWasmState (VI32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Gt) astate = Some astate'.
Proof.
  (* ADMITTED: VCMP_F32 has no modeled semantics — requires Flocq *)
Admitted.

Theorem f32_le_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VF32 v2 :: VF32 v1 :: stack' ->
  exec_wasm_instr F32Le wstate =
    Some (mkWasmState (VI32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Le) astate = Some astate'.
Proof.
  (* ADMITTED: VCMP_F32 has no modeled semantics — requires Flocq *)
Admitted.

Theorem f32_ge_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VF32 v2 :: VF32 v1 :: stack' ->
  exec_wasm_instr F32Ge wstate =
    Some (mkWasmState (VI32 I32.zero :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm F32Ge) astate = Some astate'.
Proof.
  (* ADMITTED: VCMP_F32 has no modeled semantics — requires Flocq *)
Admitted.

(** ** Summary: 20 F32 Operations
    - 7 Qed: Min, Max, Copysign, Ceil, Floor, Trunc, Nearest (compile to [])
    - 13 Admitted: VFP instructions with no modeled semantics
      - 4 arithmetic (VADD/VSUB/VMUL/VDIV_F32)
      - 3 unary (VSQRT/VABS/VNEG_F32)
      - 6 comparisons (VCMP_F32)

    To close: integrate Flocq IEEE 754 library for VFP semantics
*)
