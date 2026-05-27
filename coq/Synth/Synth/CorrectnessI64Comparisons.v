(** * Correctness Proofs for I64 Comparison Operations

    v0.8.0 (#149/#150) baseline: each i64 comparison op compiles to a single
    high-level pseudo-op (`I64SetCond R0 R0 R1 R2 R3 <cond>` for binary cmps,
    `I64SetCondZ R0 R0 R1` for `i64.eqz`). The pseudo-ops are introduced as
    axiomatic result functions in `ArmSemantics.v` (`i64_setcond_bits`,
    `i64_setcondz_bits`).

    v0.9.0 PR 1 (#153) precursor: the `i64_setcond_bits_spec` and
    `i64_setcondz_bits_spec` axioms pin those result functions to the
    WASM-spec form `if I64.<cmp> (combine_i32 lo hi) ... then I32.one else I32.zero`.

    v0.9.0 PR 4 (this file): the 11 i64 comparison theorems are lifted from
    T2 (existence-only) to T1 (result-correspondence) using:

    - **I64-typed hypotheses**: operands are pinned via lo/hi halves living
      in (R0:R1) and (R2:R3) for binops, and (R0:R1) for `i64.eqz`. The
      combined 64-bit operand is `combine_i32 lo hi`.

    - **Single-register post-condition**: WASM i64 comparisons return an
      *i32 boolean* (0 or 1), so the postcondition pins only R0:
        get_reg astate' R0 = if I64.<cmp> v1 v2 then I32.one else I32.zero
      where `v1 := combine_i32 lo1 hi1`, `v2 := combine_i32 lo2 hi2`.

    - **No `exec_wasm_instr` hypothesis**: per the precursor PR's pattern,
      the vacuous `exec_wasm_instr I64Eq wstate = Some ...` hypothesis is
      dropped (WasmSemantics.v does not model i64 comparisons, so that
      hypothesis is False and the prior T2 theorems were vacuously true).

    The proof of each theorem is mechanical:
      1. `unfold compile_wasm_to_arm, exec_program, exec_instr; simpl`
         exposes the `I64SetCond ...` pseudo-op step,
      2. `rewrite HR0, HR1, HR2, HR3` substitutes register reads,
      3. `rewrite i64_setcond_bits_spec; simpl` reduces the axiomatic result
         function to the WASM-spec `if I64.<cmp> ... then I32.one else I32.zero`
         form (the `simpl` reduces the inner `match cond` to the specific
         comparison),
      4. `eexists; split; [reflexivity | apply get_set_reg_eq]` closes both
         halves of the existential.

    Architectural finding: the i64 flag-correspondence lemmas added in #149
    (`z_flag_sub_eq_i64`, `flags_ne_i64`, ..., `z_flag_sub_eqz_i64`) and the
    `synth_cmp_binop_proof_i64` / `synth_cmp_unop_proof_i64` tactics are
    **not used** by this PR. Those lemmas/tactics presupposed that i64 cmps
    would lower to a CMP+MOV+conditional-MOV sequence (mirroring the i32 path),
    in which case the proof would need to reflect ARM N/Z/C/V flags back into
    WASM cmp semantics. Under the actual v0.8.0 codegen, i64 cmps lower to a
    single `I64SetCond` pseudo-op whose semantic axiom already returns the
    WASM-spec result directly, so no flag bridging is required. The lemmas
    remain in `ArmFlagLemmas.v` for the i32 path (which still uses them) and
    are available for any future direct dual-precision CMP/SBC modelling.
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import QArith.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.
Require Import Synth.ARM.ArmSemantics.
Require Import Synth.WASM.WasmValues.
Require Import Synth.WASM.WasmInstructions.
Require Import Synth.WASM.WasmSemantics.
Require Import Synth.Synth.Compilation.

Import ListNotations.
Open Scope Z_scope.

(** Helper tactics retained from the v0.8.0 baseline for the bit-manipulation
    and shift/rotate T2 proofs further down this file. *)
Ltac solve_single_arm :=
  intros; unfold compile_wasm_to_arm;
  unfold exec_program; simpl;
  eexists; reflexivity.

Ltac solve_empty_arm :=
  intros; unfold compile_wasm_to_arm; simpl;
  eexists; reflexivity.

(** ** I64 Comparison Operations — T1 lifts (v0.9.0 PR 4)

    Each theorem below corresponds to a row of the per-op table in the PR body.
    The dispatch is uniform: the spec axiom `i64_setcond_bits_spec` (binary)
    or `i64_setcondz_bits_spec` (unary) is the sole non-mechanical step. *)

Theorem i64_eqz_correct : forall astate lo hi,
  get_reg astate R0 = lo ->
  get_reg astate R1 = hi ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Eqz) astate = Some astate' /\
    get_reg astate' R0 =
      (if I64.eq (combine_i32 lo hi) I64.zero then I32.one else I32.zero).
Proof.
  intros astate lo hi HR0 HR1.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1.
  rewrite i64_setcondz_bits_spec.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

Theorem i64_eq_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Eq) astate = Some astate' /\
    get_reg astate' R0 =
      (if I64.eq (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 HR0 HR1 HR2 HR3.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_setcond_bits_spec; simpl.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

Theorem i64_ne_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Ne) astate = Some astate' /\
    get_reg astate' R0 =
      (if I64.ne (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 HR0 HR1 HR2 HR3.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_setcond_bits_spec; simpl.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

Theorem i64_lts_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64LtS) astate = Some astate' /\
    get_reg astate' R0 =
      (if I64.lts (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 HR0 HR1 HR2 HR3.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_setcond_bits_spec; simpl.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

Theorem i64_ltu_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64LtU) astate = Some astate' /\
    get_reg astate' R0 =
      (if I64.ltu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 HR0 HR1 HR2 HR3.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_setcond_bits_spec; simpl.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

Theorem i64_gts_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64GtS) astate = Some astate' /\
    get_reg astate' R0 =
      (if I64.gts (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 HR0 HR1 HR2 HR3.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_setcond_bits_spec; simpl.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

Theorem i64_gtu_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64GtU) astate = Some astate' /\
    get_reg astate' R0 =
      (if I64.gtu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 HR0 HR1 HR2 HR3.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_setcond_bits_spec; simpl.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

Theorem i64_les_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64LeS) astate = Some astate' /\
    get_reg astate' R0 =
      (if I64.les (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 HR0 HR1 HR2 HR3.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_setcond_bits_spec; simpl.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

Theorem i64_leu_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64LeU) astate = Some astate' /\
    get_reg astate' R0 =
      (if I64.leu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 HR0 HR1 HR2 HR3.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_setcond_bits_spec; simpl.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

Theorem i64_ges_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64GeS) astate = Some astate' /\
    get_reg astate' R0 =
      (if I64.ges (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 HR0 HR1 HR2 HR3.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_setcond_bits_spec; simpl.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

Theorem i64_geu_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64GeU) astate = Some astate' /\
    get_reg astate' R0 =
      (if I64.geu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof.
  intros astate lo1 hi1 lo2 hi2 HR0 HR1 HR2 HR3.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_setcond_bits_spec; simpl.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

(** ** I64 Bit Manipulation Operations *)

Theorem i64_clz_correct : forall wstate astate v stack',
  wstate.(stack) = VI64 v :: stack' ->
  exec_wasm_instr I64Clz wstate =
    Some (mkWasmState
            (VI64 (I64.clz v) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Clz) astate = Some astate'.
Proof.
  (* Compiles to [CLZ R0 R0] — always Some *)
  solve_single_arm.
Qed.

Theorem i64_ctz_correct : forall wstate astate v stack',
  wstate.(stack) = VI64 v :: stack' ->
  exec_wasm_instr I64Ctz wstate =
    Some (mkWasmState
            (VI64 (I64.ctz v) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Ctz) astate = Some astate'.
Proof.
  (* Compiles to [RBIT R0 R0; CLZ R0 R0] — two instructions, both always Some *)
  intros; unfold compile_wasm_to_arm.
  unfold exec_program; simpl.
  eexists; reflexivity.
Qed.

Theorem i64_popcnt_correct : forall wstate astate v stack',
  wstate.(stack) = VI64 v :: stack' ->
  exec_wasm_instr I64Popcnt wstate =
    Some (mkWasmState
            (VI64 (I64.popcnt v) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Popcnt) astate = Some astate'.
Proof.
  (* Compiles to [POPCNT R0 R0] — always Some *)
  solve_single_arm.
Qed.

(** ** I64 Shift/Rotate Operations *)

Theorem i64_shl_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Shl wstate =
    Some (mkWasmState
            (VI64 (I64.shl v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Shl) astate = Some astate'.
Proof. solve_single_arm. Qed.

Theorem i64_shru_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64ShrU wstate =
    Some (mkWasmState
            (VI64 (I64.shru v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64ShrU) astate = Some astate'.
Proof. solve_single_arm. Qed.

Theorem i64_shrs_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64ShrS wstate =
    Some (mkWasmState
            (VI64 (I64.shrs v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64ShrS) astate = Some astate'.
Proof. solve_single_arm. Qed.

Theorem i64_rotl_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Rotl wstate =
    Some (mkWasmState
            (VI64 (I64.rotl v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Rotl) astate = Some astate'.
Proof.
  (* I64Rotl compiles to [RSB R2 R1 (Imm 32); ROR_reg R0 R0 R2] *)
  intros; unfold compile_wasm_to_arm; simpl; eexists; reflexivity.
Qed.

Theorem i64_rotr_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Rotr wstate =
    Some (mkWasmState
            (VI64 (I64.rotr v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Rotr) astate = Some astate'.
Proof.
  (* Compiles to [ROR R0 R0 0] — always Some *)
  solve_single_arm.
Qed.
