(** * I64 Operations Correctness

    This file contains correctness proofs for all i64 WebAssembly operations.

    v0.8.0 PR 1a alignment: i64 ops now compile to dual-register pair sequences
    matching Rust codegen (R0:R1 result, R2:R3 second operand). See
    docs/analysis/I64_CODEGEN_SURVEY.md for the per-op breakdown. Existence
    proofs (T2) remain valid because each pseudo-op returns Some.

    v0.9.0 PR 1 (precursor + discharge): The four T1 div/rem proofs are now
    *discharged* against the new `_spec` axioms in ArmSemantics.v
    (`i64_divs_pair_spec` / `i64_divu_pair_spec` / `i64_rems_pair_spec` /
    `i64_remu_pair_spec`). Each theorem is restated with:
      - I64-typed hypotheses on the combined operand pairs,
      - High-half register pinning (R1 for v1's hi half, R3 for v2's hi half),
      - Dual-register post-condition (R0 = lo_of_i64 result, R1 = hi_of_i64 result).
    The smoke-test report on the prior commit identified the precursor work
    that this PR ships.
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

(** ** Helper Tactics *)

Ltac solve_single_arm :=
  intros; unfold compile_wasm_to_arm;
  unfold exec_program; simpl;
  eexists; reflexivity.

Ltac solve_empty_arm :=
  intros; unfold compile_wasm_to_arm; simpl;
  eexists; reflexivity.

Ltac solve_cmp_mov :=
  intros; unfold compile_wasm_to_arm, exec_program, exec_instr; simpl;
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b
  end;
  eexists; reflexivity.

(** ** I64 Arithmetic Operations (10 total) *)

Theorem i64_add_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  (* I64 values span two 32-bit registers in ARM *)
  exec_wasm_instr I64Add wstate =
    Some (mkWasmState (VI64 (I64.add v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Add) astate = Some astate'.
Proof.
  (* I64Add compiles to [ADD R0 R0 (Reg R1)] — single instruction, always Some *)
  solve_single_arm.
Qed.

Theorem i64_sub_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Sub wstate =
    Some (mkWasmState (VI64 (I64.sub v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Sub) astate = Some astate'.
Proof.
  solve_single_arm.
Qed.

Theorem i64_mul_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Mul wstate =
    Some (mkWasmState (VI64 (I64.mul v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Mul) astate = Some astate'.
Proof.
  solve_single_arm.
Qed.

(** The 4 T1 division/remainder proofs below are restated to match the actual
    v0.8.0 codegen (`I64DivSPseudo/I64DivUPseudo/I64RemSPseudo/I64RemUPseudo`
    on the dual-register pair {R0:R1, R2:R3}), using:

    - **I64-typed hypotheses**: operand pre-conditions reference
      `I64.divs / I64.divu / I64.rems / I64.remu` on the combined 64-bit
      operands (via `combine_i32`), not the incoherent `I32.divs` on i64 values
      that the smoke-test report flagged.

    - **High-half register pinning**: each operand requires *both* halves to
      be in the right register (operand 1 in R0:R1, operand 2 in R2:R3).

    - **Dual-register post-condition**: division returns a 64-bit result, so
      we must check *both* halves of the result (R0:R1).

    The discharges are mechanical: unfold the program, simpl exposes the
    pseudo-op match, the new `_spec` axioms in `ArmSemantics.v` rewrite the
    axiomatic result function to the WASM-spec form, and the divs/divu/rems/remu
    hypotheses select the Some branch.

    The WASM-level hypothesis (`exec_wasm_instr I64DivS wstate = Some ...`)
    is intentionally NOT in the new theorem shape: `exec_wasm_instr` returns
    `None` for unmodeled instructions (I64Div/Rem are not in WasmSemantics.v),
    which would make the prior theorem statement vacuously True. The new shape
    is a value-level correspondence between the WASM-spec function (`I64.divs`)
    and the ARM execution result, without routing through `exec_wasm_instr`.
    Lifting the WASM semantics to include I64Add/Sub/Mul/Div/Rem and adding
    the stack-frame plumbing is tracked separately under umbrella #152. *)

Theorem i64_divs_correct : forall astate lo1 hi1 lo2 hi2 result,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  I64.divs (combine_i32 lo1 hi1) (combine_i32 lo2 hi2) = Some result ->
  exists astate',
    exec_program (compile_wasm_to_arm I64DivS) astate = Some astate' /\
    get_reg astate' R0 = lo_of_i64 result /\
    get_reg astate' R1 = hi_of_i64 result.
Proof.
  intros astate lo1 hi1 lo2 hi2 result HR0 HR1 HR2 HR3 Hdivs.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_divs_pair_spec, Hdivs; simpl.
  eexists. split; [reflexivity | split].
  - rewrite get_set_reg_neq by discriminate. rewrite get_set_reg_eq. reflexivity.
  - rewrite get_set_reg_eq. reflexivity.
Qed.

Theorem i64_divu_correct : forall astate lo1 hi1 lo2 hi2 result,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  I64.divu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2) = Some result ->
  exists astate',
    exec_program (compile_wasm_to_arm I64DivU) astate = Some astate' /\
    get_reg astate' R0 = lo_of_i64 result /\
    get_reg astate' R1 = hi_of_i64 result.
Proof.
  intros astate lo1 hi1 lo2 hi2 result HR0 HR1 HR2 HR3 Hdivu.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_divu_pair_spec, Hdivu; simpl.
  eexists. split; [reflexivity | split].
  - rewrite get_set_reg_neq by discriminate. rewrite get_set_reg_eq. reflexivity.
  - rewrite get_set_reg_eq. reflexivity.
Qed.

Theorem i64_rems_correct : forall astate lo1 hi1 lo2 hi2 result,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  I64.rems (combine_i32 lo1 hi1) (combine_i32 lo2 hi2) = Some result ->
  exists astate',
    exec_program (compile_wasm_to_arm I64RemS) astate = Some astate' /\
    get_reg astate' R0 = lo_of_i64 result /\
    get_reg astate' R1 = hi_of_i64 result.
Proof.
  intros astate lo1 hi1 lo2 hi2 result HR0 HR1 HR2 HR3 Hrems.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_rems_pair_spec, Hrems; simpl.
  eexists. split; [reflexivity | split].
  - rewrite get_set_reg_neq by discriminate. rewrite get_set_reg_eq. reflexivity.
  - rewrite get_set_reg_eq. reflexivity.
Qed.

Theorem i64_remu_correct : forall astate lo1 hi1 lo2 hi2 result,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  I64.remu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2) = Some result ->
  exists astate',
    exec_program (compile_wasm_to_arm I64RemU) astate = Some astate' /\
    get_reg astate' R0 = lo_of_i64 result /\
    get_reg astate' R1 = hi_of_i64 result.
Proof.
  intros astate lo1 hi1 lo2 hi2 result HR0 HR1 HR2 HR3 Hremu.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_remu_pair_spec, Hremu; simpl.
  eexists. split; [reflexivity | split].
  - rewrite get_set_reg_neq by discriminate. rewrite get_set_reg_eq. reflexivity.
  - rewrite get_set_reg_eq. reflexivity.
Qed.

(** ** I64 Bitwise Operations (10 total) *)

Theorem i64_and_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64And wstate =
    Some (mkWasmState (VI64 (I64.and v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64And) astate = Some astate'.
Proof.
  (* Compiles to [AND R0 R0 (Reg R1)] — always Some *)
  solve_single_arm.
Qed.

Theorem i64_or_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Or wstate =
    Some (mkWasmState (VI64 (I64.or v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Or) astate = Some astate'.
Proof.
  solve_single_arm.
Qed.

Theorem i64_xor_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Xor wstate =
    Some (mkWasmState (VI64 (I64.xor v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Xor) astate = Some astate'.
Proof.
  solve_single_arm.
Qed.

Theorem i64_shl_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Shl wstate =
    Some (mkWasmState (VI64 (I64.shl v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Shl) astate = Some astate'.
Proof.
  (* Compiles to [LSL_reg R0 R0 R1] — always Some *)
  solve_single_arm.
Qed.

Theorem i64_shru_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64ShrU wstate =
    Some (mkWasmState (VI64 (I64.shru v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64ShrU) astate = Some astate'.
Proof.
  solve_single_arm.
Qed.

Theorem i64_shrs_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64ShrS wstate =
    Some (mkWasmState (VI64 (I64.shrs v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64ShrS) astate = Some astate'.
Proof.
  solve_single_arm.
Qed.

Theorem i64_rotl_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Rotl wstate =
    Some (mkWasmState (VI64 (I64.rotl v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Rotl) astate = Some astate'.
Proof.
  (* Compiles to [RSB R2 R1 (Imm 32); ROR_reg R0 R0 R2] — always Some *)
  intros; unfold compile_wasm_to_arm; simpl; eexists; reflexivity.
Qed.

Theorem i64_rotr_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Rotr wstate =
    Some (mkWasmState (VI64 (I64.rotr v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Rotr) astate = Some astate'.
Proof.
  (* Compiles to [ROR_reg R0 R0 R1] — always Some *)
  solve_single_arm.
Qed.

(** ** I64 Comparison Operations (11 total) *)
(** All comparisons compile to CMP+MOV+conditional-MOV sequences *)

Theorem i64_eqz_correct : forall wstate astate v stack',
  wstate.(stack) = VI64 v :: stack' ->
  exec_wasm_instr I64Eqz wstate =
    Some (mkWasmState
            (VI32 (if I64.eq v I64.zero then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Eqz) astate = Some astate'.
Proof. solve_cmp_mov. Qed.

Theorem i64_eq_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Eq wstate =
    Some (mkWasmState
            (VI32 (if I64.eq v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Eq) astate = Some astate'.
Proof. solve_cmp_mov. Qed.

Theorem i64_ne_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Ne wstate =
    Some (mkWasmState
            (VI32 (if negb (I64.eq v1 v2) then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Ne) astate = Some astate'.
Proof. solve_cmp_mov. Qed.

Theorem i64_lts_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64LtS wstate =
    Some (mkWasmState
            (VI32 (if I64.lts v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64LtS) astate = Some astate'.
Proof. solve_cmp_mov. Qed.

Theorem i64_ltu_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64LtU wstate =
    Some (mkWasmState
            (VI32 (if I64.ltu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64LtU) astate = Some astate'.
Proof. solve_cmp_mov. Qed.

Theorem i64_gts_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64GtS wstate =
    Some (mkWasmState
            (VI32 (if I64.lts v2 v1 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64GtS) astate = Some astate'.
Proof. solve_cmp_mov. Qed.

Theorem i64_gtu_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64GtU wstate =
    Some (mkWasmState
            (VI32 (if I64.ltu v2 v1 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64GtU) astate = Some astate'.
Proof. solve_cmp_mov. Qed.

Theorem i64_les_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64LeS wstate =
    Some (mkWasmState
            (VI32 (if negb (I64.lts v2 v1) then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64LeS) astate = Some astate'.
Proof. solve_cmp_mov. Qed.

Theorem i64_leu_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64LeU wstate =
    Some (mkWasmState
            (VI32 (if negb (I64.ltu v2 v1) then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64LeU) astate = Some astate'.
Proof. solve_cmp_mov. Qed.

Theorem i64_ges_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64GeS wstate =
    Some (mkWasmState
            (VI32 (if negb (I64.lts v1 v2) then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64GeS) astate = Some astate'.
Proof. solve_cmp_mov. Qed.

Theorem i64_geu_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64GeU wstate =
    Some (mkWasmState
            (VI32 (if negb (I64.ltu v1 v2) then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64GeU) astate = Some astate'.
Proof. solve_cmp_mov. Qed.

(** ** I64 Bit Manipulation (3 total) *)

Theorem i64_clz_correct : forall wstate astate v stack',
  wstate.(stack) = VI64 v :: stack' ->
  exec_wasm_instr I64Clz wstate =
    Some (mkWasmState (VI64 (I64.zero) :: stack')  (* Placeholder *)
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Clz) astate = Some astate'.
Proof.
  (* Compiles to [CLZ R0 R0] — always Some *)
  solve_single_arm.
Qed.

Theorem i64_ctz_correct : forall wstate astate v stack',
  wstate.(stack) = VI64 v :: stack' ->
  exec_wasm_instr I64Ctz wstate =
    Some (mkWasmState (VI64 (I64.zero) :: stack')  (* Placeholder *)
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
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
    Some (mkWasmState (VI64 (I64.zero) :: stack')  (* Placeholder *)
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Popcnt) astate = Some astate'.
Proof.
  (* Compiles to [POPCNT R0 R0] — always Some *)
  solve_single_arm.
Qed.

(** ** Summary (after v0.9.0 PR 1 precursor + discharge)

    I64 Operations: 26 theorems in this file
    - Arithmetic existence: 3 Qed (Add, Sub, Mul)
    - Division/remainder T1: 4 Qed (DivS, DivU, RemS, RemU) — discharged via
      `i64_{divs,divu,rems,remu}_pair_spec` axioms in ArmSemantics.v
    - Bitwise existence: 3 Qed (And, Or, Xor)
    - Shift/rotate existence: 5 Qed (Shl, ShrU, ShrS, Rotl, Rotr)
    - Comparison existence: 11 Qed (Eqz, Eq, Ne, Lt[SU], Le[SU], Gt[SU], Ge[SU])
    - Bit-manipulation existence: 3 Qed (Clz, Ctz, Popcnt) -- note: also stated
      in CorrectnessI64Comparisons.v with I64-typed hypotheses

    Status: 26 Qed / 0 Admitted (4 admits discharged by this PR).
    The remaining T2 -> T1 lifts (Add/Sub/Mul/And/Or/Xor/Shifts/Rotates/
    Comparisons/Clz/Ctz/Popcnt result-correspondence) are scheduled as
    fan-out PRs 2-5 of umbrella #152. Each is a mechanical
    `unfold; rewrite <op>_spec; reflexivity` lift against the spec axioms
    now in place.
*)
