(** * Complete Correctness Proofs — Honest Accounting

    This file serves as the master index for all correctness proofs.

    After v0.8.0 PR 1a (Compilation.v i64 alignment) the i64 operations now
    compile to dual-register-pair sequences (R0:R1 result, R2:R3 second
    operand) matching the Rust codegen, via ADDS/ADC/SUBS/SBC for arithmetic
    and high-level I64*Pseudo opcodes for multiply/shift/rotate/compare/div/
    rem/const/extend/wrap/load/store. The 4 T1 i64 div/rem proofs and the
    i64_const_correct proof were re-admitted pending the v0.8.0 lift queue
    (umbrella issue #147, PRs 2–5).

    Other admits (unchanged from prior baseline):
    - 4 i32 division proofs: sequential model cannot skip UDF via BCondOffset
    - 1 i32_const proof: Z.leb branch requires I32.unsigned reduction
    - 2 Compilation.v examples: same Z.leb reduction issue
    - 2 ArmRefinement.v Sail placeholders + 1 Integers.v Z.mod_mod.
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
    CorrectnessI32.v:    25 (3 arith + 3 bitwise + 3 bit-manip + 5 shift/rotate +
                              11 comparison)
                           (4 division proofs Admitted — trap guard sequences)
    ---
    Total T1:            ~30 across files

    PR 1a (v0.8.0): 4 previously-Qed i64 division/remainder T1 proofs and the
    i64_const_correct T1 proof were re-admitted; they were stated against a
    simplified codegen that did not match the Rust compiler. Re-proving these
    against the aligned model is the job of v0.8.0 PRs 2–5.

    These proofs establish: get_reg astate' R0 = <expected WASM result>
*)

(** ** T2: Existence-Only Proofs (Qed)

    CorrectnessSimple.v:         28 (control, locals, globals, comparisons,
                                     shifts, bit-manip)
                                    (I32Const, I64Const Admitted — see T3)
    CorrectnessI64.v:            22 (arith, bitwise, shifts, comparisons, bit-manip)
                                    (4 div/rem Admitted — see T3)
    CorrectnessI64Comparisons.v: 19 (comparisons, bit-manip, shifts)
    CorrectnessF32.v:            20 (7 empty-program + 13 VFP with abstract semantics)
    CorrectnessF64.v:            20 (7 empty-program + 13 VFP with abstract semantics)
    CorrectnessConversions.v:    21 (3 integer + 18 VFP conversions)
    CorrectnessMemory.v:          8 (4 i32/i64 + 4 f32/f64 load/store)
    ---
    Total T2:                   ~138

    These proofs establish: exists astate', exec_program ... = Some astate'
    (ARM execution succeeds, no claim about result value)
*)

(** ** T3: Admitted Proofs

    ArmRefinement.v:              2 (Sail integration placeholder)
    Integers.v:                   1 (i64_to_i32_to_i64_wrap, Rocq 9 Z.mod_mod)
    CorrectnessI32.v:             4 (divs, divu, rems, remu — trap guard sequences)
    CorrectnessI64.v:             4 (divs, divu, rems, remu — v0.8.0 PR 1a re-admit)
    CorrectnessSimple.v:          2 (i32_const Z.leb, i64_const PR 1a re-admit)
    Compilation.v:                2 (examples — same Z.leb reduction issue)
    ---
    Total T3:                    15

    Unblocking strategies:
    - ArmRefinement: Import Sail-generated ARM semantics (Phase 2)
    - i32 division proofs: Extend exec_program to support PC-relative branching
    - i64 division/i64_const proofs: v0.8.0 lift queue (#147 PRs 2–5) — replace
      i64_*_pair / i64_const_lo|hi axioms with concrete definitions
    - i32_const proof: Prove I32.unsigned reduction lemma or use vm_compute
    - Compilation.v examples: Same vm_compute / reduction approach
*)

Module ProgressMetrics.

  (** Correctness proof counts (after v0.8.0 PR 1a) *)
  Definition total_t1_result : nat := 30.
  Definition total_t2_existence : nat := 138.
  Definition total_t3_admitted : nat := 15.

  Definition total_qed : nat := 228.  (* T1 + T2 + infra *)
  Definition total_admitted : nat := 15.  (* T3: see breakdown above *)

  (** Infrastructure proofs (not included above) *)
  Definition infra_qed : nat := 55.
  (** Base(4) + Integers(11) + StateMonad(3) + ArmState(11) +
      ArmSemantics(7) + ArmInstructions(0) + WasmValues(2) +
      WasmSemantics(6) + Compilation(0, was 2 — examples now Admitted) +
      ArmFlagLemmas(10) + misc(1) = 55
      Note: Compilation.v examples became Admitted but infra count
      not yet adjusted — needs audit. *)

  (** Axiom count — VFP + i64 pseudo-op bit-pattern axioms *)
  Definition total_axioms : nat := 64.
  (** Original I32/I64 axioms (13): clz, ctz, popcnt, rbit, clz_rbit,
      clz_range, ctz_range, popcnt_range,
      div_mul_rem_unsigned, div_mul_rem_signed,
      remu_formula, rems_formula, rotl_rotr_sub

      VFP axioms (20): f32_add/sub/mul/div/sqrt/abs/neg_bits (7),
      f64_add/sub/mul/div/sqrt/abs/neg_bits (7),
      f32_compare_flags, f64_compare_flags (2),
      cvt_f32_to_f64_bits, cvt_f64_to_f32_bits (2),
      cvt_s32_to_f32_bits, cvt_f32_to_s32_bits (2),

      ArmFlagLemmas: nv_flag_sub_lts (1),

      v0.8.0 PR 1a i64 pseudo-op axioms (~25):
        i64_mul_lo/hi_bits (2), i64_shl/shru/shrs_lo/hi_bits (6),
        i64_rotl/rotr_lo/hi_bits (4), i64_clz/ctz/popcnt_bits (3),
        i64_setcond/setcondz_bits (2), i64_divs/divu/rems/remu_pair (4),
        i64_const_lo/hi (2), i64_extend_s_hi (1), i64_load_lo/hi (2). *)

End ProgressMetrics.
