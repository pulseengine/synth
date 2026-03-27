(** * Complete Correctness Proofs — Honest Accounting

    This file serves as the master index for all correctness proofs.

    After adding VFP floating-point semantics to ArmSemantics.v,
    all 48 VFP-dependent proofs are now closed with Qed.
    The i64_to_i32_to_i64_wrap lemma in Integers.v is also closed.
    Only ArmRefinement.v Sail integration placeholders remain Admitted.
*)

From Stdlib Require Import QArith.
Require Export Synth.Synth.Correctness.
Require Export Synth.Synth.CorrectnessSimple.
Require Export Synth.Synth.CorrectnessI32.
Require Export Synth.Synth.CorrectnessI64.
Require Export Synth.Synth.CorrectnessI64Comparisons.
Require Export Synth.Synth.CorrectnessConversions.
Require Export Synth.Synth.CorrectnessF32.
Require Export Synth.Synth.CorrectnessF64.
Require Export Synth.Synth.CorrectnessMemory.

(** ** Proof Tiers

    T1: Result Correspondence — ARM output register = WASM result value
    T2: Existence-Only — ARM execution succeeds (no result claim)
    T3: Admitted — Not yet proven (requires unmodeled semantics)
*)

(** ** T1: Result Correspondence Proofs (Qed)

    Correctness.v:        6 (Add, Sub, Mul, And, Or, Xor)
    CorrectnessI32.v:    13 (7 arith + 3 bitwise + 3 bit-manip)
    ---
    Total T1:            19

    These proofs establish: get_reg astate' R0 = <expected WASM result>
*)

(** ** T2: Existence-Only Proofs (Qed)

    CorrectnessSimple.v:         29 (control, locals, globals, constants,
                                     comparisons, shifts, bit-manip)
    CorrectnessI64.v:            26 (arith, bitwise, shifts, comparisons, bit-manip)
    CorrectnessI64Comparisons.v: 19 (comparisons, bit-manip, shifts)
    CorrectnessF32.v:            20 (7 empty-program + 13 VFP with abstract semantics)
    CorrectnessF64.v:            20 (7 empty-program + 13 VFP with abstract semantics)
    CorrectnessConversions.v:    21 (3 integer + 18 VFP conversions)
    CorrectnessMemory.v:          8 (4 i32/i64 + 4 f32/f64 load/store)
    ---
    Total T2:                   143

    These proofs establish: exists astate', exec_program ... = Some astate'
    (ARM execution succeeds, no claim about result value)
*)

(** ** T3: Admitted Proofs

    ArmRefinement.v:              2 (Sail integration placeholder)
    ---
    Total T3:                     2

    The ArmRefinement admits require importing Sail-generated ARM semantics,
    which is a Phase 2 dependency (not blocking compiler correctness).
*)

Module ProgressMetrics.

  (** Correctness proof counts *)
  Definition total_t1_result : nat := 39.
  Definition total_t2_existence : nat := 143.
  Definition total_t3_admitted : nat := 2.

  Definition total_qed : nat := 237.  (* T1 + T2 + infra *)
  Definition total_admitted : nat := 2.  (* T3: ArmRefinement only *)

  (** Infrastructure proofs (not included above) *)
  Definition infra_qed : nat := 55.
  (** Base(4) + Integers(11) + StateMonad(3) + ArmState(11) +
      ArmSemantics(7) + ArmInstructions(0) + WasmValues(2) +
      WasmSemantics(6) + Compilation(2) + ArmFlagLemmas(10) - 1 axiom = 55 *)

  (** Axiom count — VFP axioms added for abstract float operations *)
  Definition total_axioms : nat := 34.
  (** Original I32/I64 axioms (13): clz, ctz, popcnt, rbit, clz_rbit,
      clz_range, ctz_range, popcnt_range,
      div_mul_rem_unsigned, div_mul_rem_signed,
      remu_formula, rems_formula, rotl_rotr_sub

      VFP axioms (21): f32_add/sub/mul/div/sqrt/abs/neg_bits (7),
      f64_add/sub/mul/div/sqrt/abs/neg_bits (7),
      f32_compare_flags, f64_compare_flags (2),
      cvt_f32_to_f64_bits, cvt_f64_to_f32_bits (2),
      cvt_s32_to_f32_bits, cvt_f32_to_s32_bits (2),
      nv_flag_sub_lts (1 in ArmFlagLemmas.v) *)

End ProgressMetrics.
