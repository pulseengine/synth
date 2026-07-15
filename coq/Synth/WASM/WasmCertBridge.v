(** * VCR-WASM-001 — WasmCert-Coq refinement bridge (BOUNDED first increment)

    This file proves that synth's stack-machine executor [exec_wasm_instr]
    AGREES with the WasmCert-Coq reference rule (WasmCertReference.v) for ONE
    total operation: i32.add. It is the WASM-side analogue of SailArmBridge.v's
    per-instruction bridge lemmas (VCR-ISA-001 / #667).

    SCOPE (honest, named): bounded first increment — 1 op anchored, 1 real-Qed
    refinement lemma, establishing the pattern. Full integer/control-flow
    coverage and a real external WasmCert-Coq/CompCert coq dependency (this file
    uses a hand transcription of the reference, see WasmCertReference.v) are the
    named follow-up.

    NON-VACUITY (why a WRONG synth semantics fails this file):
    - [i32_add_refines_wasmcert_op] is NOT [reflexivity]: synth's [I32.add x y]
      is [repr (x + y)] over RAW representatives, whereas the WasmCert/CompCert
      reference [wasmcert_i32_add x y] is [repr (unsigned x + unsigned y)] —
      operands normalized first. Equal mod 2^32, but definitionally distinct;
      the proof discharges the raw-vs-normalized gap via [Zplus_mod].
    - [i32_add_exec_refines_wasmcert] routes the claim through the REAL
      [exec_wasm_instr I32Add]. If [exec_wasm_instr I32Add] were miswired to
      compute [I32.sub]/[I32.mul] (or pushed the wrong value / wrong stack
      shape), this theorem would be unprovable: the pushed result would not be
      [wasmcert_i32_add v1 v2]. The reference pins the OPERATION, not the shape.
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.WASM.WasmValues.
Require Import Synth.WASM.WasmInstructions.
Require Import Synth.WASM.WasmSemantics.
Require Import Synth.WASM.WasmCertReference.

Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.

(** ** Algebraic core: synth's i32.add equals the WasmCert reference rule.

    synth:      [I32.add x y      = repr (x + y)]            (raw operands)
    WasmCert:   [wasmcert_i32_add = repr (unsigned x + unsigned y)]  (normalized)

    These agree because [unsigned n = n mod 2^32] and addition commutes with
    [mod] ([Zplus_mod]). This is the step that would break if synth added the
    operands under a different operation. *)
Theorem i32_add_refines_wasmcert_op : forall x y,
  I32.add x y = wasmcert_i32_add x y.
Proof.
  intros x y.
  unfold I32.add, wasmcert_i32_add, I32.repr, I32.unsigned.
  (* Goal: (x + y) mod m = ((x mod m) + (y mod m)) mod m *)
  rewrite Zplus_mod.
  reflexivity.
Qed.

(** ** Executor-level refinement: [exec_wasm_instr I32Add] pushes exactly the
       WasmCert reference result on top of the popped stack.

    Mirrors the shape of [i32_add_type_preservation] in WasmSemantics.v, but
    the pushed value is pinned to the INDEPENDENT reference
    [wasmcert_i32_add v1 v2], not to synth's own [I32.add]. *)
Theorem i32_add_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Add s =
  Some (mkWasmState
          (VI32 (wasmcert_i32_add v1 v2) :: stack')
          s.(locals)
          s.(globals)
          s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  simpl.
  (* the executor pushes [VI32 (I32.add v1 v2)]; rewrite to the reference *)
  rewrite i32_add_refines_wasmcert_op.
  reflexivity.
Qed.
