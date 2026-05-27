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

    v0.9.0 PR 2 (i64 arith + bitwise T1 lifts): The Add/Sub/Mul/And/Or/Xor
    theorems are restated to the same shape (I64-typed hypotheses, high-half
    register pinning, dual-register post-condition):
      - **i64_mul_correct** is discharged as Qed via `i64_mul_{lo,hi}_bits_spec`.
      - **i64_add_correct** / **i64_sub_correct** are Admitted pending a
        carry-/borrow-propagation lemma over the existing ArmSemantics.v
        ADDS+ADC and SUBS+SBC pairs (no new axiom needed; the property is
        a derivable consequence of the existing flag semantics).
      - **i64_and_correct** / **i64_or_correct** / **i64_xor_correct** are
        Admitted pending halves-distribute-over-bitwise decomposition lemmas
        in Common/Integers.v — same Rocq 9 `Z.mod_mod` obstacle that already
        blocks `i64_to_i32_to_i64_wrap` (Integers.v:387).
    No new spec axioms introduced; all gaps are mechanical proof engineering
    against the existing infrastructure, tracked as v0.9.0 PR 2 follow-ups.
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

(** v0.9.0 PR 2 lift: Add/Sub/Mul restated with I64-typed hypotheses,
    high-half register pinning, and dual-register post-conditions —
    matching the shape established by PR 1 (#153) for div/rem and const.

    - **i64_mul_correct** discharges cleanly via the spec axioms
      `i64_mul_lo_bits_spec` / `i64_mul_hi_bits_spec` added in PR 1.
    - **i64_add_correct** / **i64_sub_correct** require a carry-propagation
      lemma over the real ARM ADDS+ADC / SUBS+SBC pair (the C flag set by
      ADDS/SUBS feeds the carry-in of ADC/SBC). That lemma does not exist
      yet in the proof infrastructure — see PR-body follow-up — so these
      remain `Admitted` with a precise gap citation. Per the v0.9.0 PR 2
      task brief, no new spec axiom is introduced; the carry-propagation
      lemma is a *provable* property of the existing ARM semantics in
      `ArmSemantics.v` and is tracked as a follow-up.

    The previous theorem shape (existence-only with a vacuous
    `exec_wasm_instr I64<Op> wstate = Some ...` hypothesis) has been
    removed: `WasmSemantics.v` does not model i64 Add/Sub/Mul, so that
    hypothesis was always False (vacuous truth). The restated shape gives
    a real correspondence between the WASM-spec function (`I64.{add,sub,
    mul}`) and the ARM execution result, mirroring how PR 1 restated
    div/rem and const. *)

Theorem i64_add_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Add) astate = Some astate' /\
    get_reg astate' R0 = lo_of_i64 (I64.add (combine_i32 lo1 hi1)
                                            (combine_i32 lo2 hi2)) /\
    get_reg astate' R1 = hi_of_i64 (I64.add (combine_i32 lo1 hi1)
                                            (combine_i32 lo2 hi2)).
Proof.
  (* ADMITTED: I64Add compiles to ADDS R0 R0 (Reg R2); ADC R1 R1 (Reg R3).
     The ADDS sets the C flag from `compute_c_flag_add lo1 lo2`, and ADC
     reads that C flag to compute `hi1 + hi2 + C`. Closing the result
     correspondence requires a carry-propagation lemma over the existing
     ArmSemantics.v ADDS/ADC pair (no new axiom needed — the property is
     provable, but the helper is not yet present). Tracked as v0.9.0 PR 2
     follow-up; no new spec axiom is introduced. *)
Admitted.

Theorem i64_sub_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Sub) astate = Some astate' /\
    get_reg astate' R0 = lo_of_i64 (I64.sub (combine_i32 lo1 hi1)
                                            (combine_i32 lo2 hi2)) /\
    get_reg astate' R1 = hi_of_i64 (I64.sub (combine_i32 lo1 hi1)
                                            (combine_i32 lo2 hi2)).
Proof.
  (* ADMITTED: I64Sub compiles to SUBS R0 R0 (Reg R2); SBC R1 R1 (Reg R3).
     SUBS sets the C flag (borrow inverted) via `compute_c_flag_sub`, and
     SBC reads it to compute `hi1 - hi2 - NOT(C)`. Same gap as i64_add:
     needs a borrow-propagation lemma over the ArmSemantics.v SUBS/SBC
     pair. No new spec axiom introduced; tracked as v0.9.0 PR 2 follow-up. *)
Admitted.

Theorem i64_mul_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Mul) astate = Some astate' /\
    get_reg astate' R0 = lo_of_i64 (I64.mul (combine_i32 lo1 hi1)
                                            (combine_i32 lo2 hi2)) /\
    get_reg astate' R1 = hi_of_i64 (I64.mul (combine_i32 lo1 hi1)
                                            (combine_i32 lo2 hi2)).
Proof.
  intros astate lo1 hi1 lo2 hi2 HR0 HR1 HR2 HR3.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2, HR3.
  rewrite i64_mul_lo_bits_spec, i64_mul_hi_bits_spec; simpl.
  eexists. split; [reflexivity | split].
  - rewrite get_set_reg_neq by discriminate. rewrite get_set_reg_eq. reflexivity.
  - rewrite get_set_reg_eq. reflexivity.
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

(** v0.9.0 PR 2 lift: And/Or/Xor restated with dual-register
    post-conditions referencing `I64.and / I64.or / I64.xor` on the
    combined operand pair.

    Each compiles to two parallel 32-bit bitwise ops on the lo/hi pair:
      I64And => [AND R0 R0 (Reg R2); AND R1 R1 (Reg R3)]
      I64Or  => [ORR R0 R0 (Reg R2); ORR R1 R1 (Reg R3)]
      I64Xor => [EOR R0 R0 (Reg R2); EOR R1 R1 (Reg R3)]

    Result correspondence requires a "halves-distribute-over-bitwise"
    lemma in `Common/Integers.v`:
      lo_of_i64 (I64.and a b) = I32.and (lo_of_i64 a) (lo_of_i64 b)
      hi_of_i64 (I64.and a b) = I32.and (hi_of_i64 a) (hi_of_i64 b)
    (and the same for or/xor). These lemmas are provable from
    `Z.land_ones` / `Z.lor_spec` / `Z.lxor_spec` plus modular
    arithmetic, but the existing `i64_to_i32_to_i64_wrap` (Integers.v:387)
    is already `Admitted` because Rocq 9's `Z.mod_mod` signature changed
    and `rewrite` cannot disambiguate nested mod subterms — the same
    obstacle blocks a clean discharge here.

    Per the v0.9.0 PR 2 task brief, no new spec axiom is introduced. The
    decomposition lemma is purely arithmetic (no codegen claim), and is
    tracked as a follow-up alongside the Rocq 9 `Z.mod_mod` rework. *)

Theorem i64_and_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64And) astate = Some astate' /\
    get_reg astate' R0 = lo_of_i64 (I64.and (combine_i32 lo1 hi1)
                                            (combine_i32 lo2 hi2)) /\
    get_reg astate' R1 = hi_of_i64 (I64.and (combine_i32 lo1 hi1)
                                            (combine_i32 lo2 hi2)).
Proof.
  (* ADMITTED: needs `lo_of_i64_and` / `hi_of_i64_and` helper lemmas in
     Common/Integers.v. The ARM execution yields R0 = I32.and lo1 lo2 and
     R1 = I32.and hi1 hi2; correspondence with the dual-register post-
     condition reduces to the halves-distribute-over-Z.land property,
     blocked by the same Rocq 9 Z.mod_mod issue as
     `i64_to_i32_to_i64_wrap`. No new spec axiom introduced. *)
Admitted.

Theorem i64_or_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Or) astate = Some astate' /\
    get_reg astate' R0 = lo_of_i64 (I64.or (combine_i32 lo1 hi1)
                                           (combine_i32 lo2 hi2)) /\
    get_reg astate' R1 = hi_of_i64 (I64.or (combine_i32 lo1 hi1)
                                           (combine_i32 lo2 hi2)).
Proof.
  (* ADMITTED: same shape as i64_and_correct — needs `lo_of_i64_or` /
     `hi_of_i64_or` decomposition lemmas. Tracked as v0.9.0 PR 2
     follow-up; no new spec axiom introduced. *)
Admitted.

Theorem i64_xor_correct : forall astate lo1 hi1 lo2 hi2,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = lo2 ->
  get_reg astate R3 = hi2 ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Xor) astate = Some astate' /\
    get_reg astate' R0 = lo_of_i64 (I64.xor (combine_i32 lo1 hi1)
                                            (combine_i32 lo2 hi2)) /\
    get_reg astate' R1 = hi_of_i64 (I64.xor (combine_i32 lo1 hi1)
                                            (combine_i32 lo2 hi2)).
Proof.
  (* ADMITTED: same shape as i64_and_correct — needs `lo_of_i64_xor` /
     `hi_of_i64_xor` decomposition lemmas. Tracked as v0.9.0 PR 2
     follow-up; no new spec axiom introduced. *)
Admitted.

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

(** ** Summary (after v0.9.0 PR 2 — i64 arith + bitwise restated)

    I64 Operations: 26 theorems in this file
    - Arithmetic T1: 1 Qed (Mul via `i64_mul_{lo,hi}_bits_spec`) +
      2 Admitted (Add, Sub — gap: ADDS/ADC + SUBS/SBC carry-propagation
      lemma over existing ArmSemantics.v; no new spec axiom needed).
    - Division/remainder T1: 4 Qed (DivS, DivU, RemS, RemU) — discharged
      via `i64_{divs,divu,rems,remu}_pair_spec` axioms in ArmSemantics.v.
    - Bitwise T1: 0 Qed + 3 Admitted (And, Or, Xor — gap: halves-distribute
      decomposition lemmas blocked by Rocq 9 `Z.mod_mod` rewrite issue,
      same root cause as `i64_to_i32_to_i64_wrap`).
    - Shift/rotate existence: 5 Qed (Shl, ShrU, ShrS, Rotl, Rotr) — T1
      lifts scheduled as v0.9.0 PR 3.
    - Comparison existence: 11 Qed (Eqz, Eq, Ne, Lt[SU], Le[SU], Gt[SU],
      Ge[SU]) — T1 lifts scheduled as v0.9.0 PR 4.
    - Bit-manipulation existence: 3 Qed (Clz, Ctz, Popcnt) — T1 lifts
      scheduled as v0.9.0 PR 5.

    Net change vs. main: +1 Qed (i64_mul_correct lifted to T1 with dual-
    register post-condition); 5 prior `solve_single_arm` existence proofs
    (Add/Sub/And/Or/Xor) restated to the umbrella's required T1 shape and
    Admitted with explicit gap citations — no new axioms.
*)
