(** * Complete Correctness Proofs — Honest Accounting

    This file serves as the master index for all correctness proofs.

    After removing the catch-all (| _ => Some s) from ArmSemantics.v,
    only proofs backed by real ARM semantics survive as Qed.
    VFP-dependent proofs are honestly Admitted.
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
    CorrectnessF32.v:             7 (empty-program: min, max, copysign, ceil, floor, trunc, nearest)
    CorrectnessF64.v:             7 (same as F32)
    CorrectnessConversions.v:     3 (i32_wrap, i64_extend_s, i64_extend_u)
    CorrectnessMemory.v:          4 (i32/i64 load/store)
    ---
    Total T2:                    95

    These proofs establish: exists astate', exec_program ... = Some astate'
    (ARM execution succeeds, no claim about result value)
*)

(** ** T3: Admitted Proofs

    CorrectnessI32.v:            16 (5 shifts + 11 comparisons)
    CorrectnessI64.v:             4 (divs, divu, rems, remu)
    CorrectnessF32.v:            13 (VFP arithmetic + comparisons)
    CorrectnessF64.v:            13 (VFP arithmetic + comparisons)
    CorrectnessConversions.v:    18 (VFP conversion instructions)
    CorrectnessMemory.v:          4 (float load/store: VLDR/VSTR)
    ArmRefinement.v:              2 (Sail integration placeholder)
    Integers.v:                   1 (i64_to_i32_to_i64_wrap)
    ---
    Total T3:                    71

    Breakdown by root cause:
    - VFP unmodeled (48): All f32/f64 ops, conversions, float memory
    - Flag-correspondence (11): i32 comparisons
    - Fixed-immediate shifts (5): i32 shifts/rotates
    - Division correspondence (4): i64 division/remainder
    - Other (3): ArmRefinement Sail placeholders, integer wrap lemma
*)

Module ProgressMetrics.

  (** Correctness proof counts *)
  Definition total_t1_result : nat := 19.
  Definition total_t2_existence : nat := 95.
  Definition total_t3_admitted : nat := 71.

  Definition total_qed : nat := 114.  (* T1 + T2 *)
  Definition total_admitted : nat := 71.  (* T3 *)

  (** Infrastructure proofs (not included above) *)
  Definition infra_qed : nat := 40.
  (** Base(4) + Integers(10) + StateMonad(3) + ArmState(6) +
      ArmSemantics(7) + ArmInstructions(0) + WasmValues(2) +
      WasmSemantics(6) + Compilation(2) = 40 *)

  (** Axiom count *)
  Definition total_axioms : nat := 12.
  (** Integers.v: clz, ctz, popcnt, rbit, clz_rbit,
      clz_range, ctz_range, popcnt_range,
      div_mul_rem_unsigned, div_mul_rem_signed,
      remu_formula, rems_formula *)

End ProgressMetrics.
