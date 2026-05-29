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
      - **i64_add_correct** / **i64_sub_correct** were Admitted in v0.9.0
        pending a carry-/borrow-propagation lemma over the existing
        ArmSemantics.v ADDS+ADC and SUBS+SBC pairs. **v0.10.0 PR 1 closes
        both as Qed** via the new `i64_add_via_adds_adc` /
        `i64_sub_via_subs_sbc` lemmas in `ArmFlagLemmas.v` (derived from
        the existing flag clauses + base-2^32 modular arithmetic; no new
        axiom).
      - **i64_and_correct** / **i64_or_correct** / **i64_xor_correct** are
        Admitted pending halves-distribute-over-bitwise decomposition lemmas
        in Common/Integers.v — same Rocq 9 `Z.mod_mod` obstacle that already
        blocks `i64_to_i32_to_i64_wrap` (Integers.v:387).
    No new spec axioms introduced; all gaps are mechanical proof engineering
    against the existing infrastructure, tracked as v0.9.0 PR 2 follow-ups.

    v0.9.0 PR 3 (i64 shifts + rotates T1 lifts): The Shl/ShrU/ShrS/Rotl/Rotr
    theorems are lifted to the same dual-register T1 shape as the div/rem
    and mul proofs. Each compiles to a single dual-register pseudo-op
    (`I64ShlPseudo`/`I64ShrUPseudo`/`I64ShrSPseudo` consume R0:R1 as the
    operand and R2 as the 32-bit shift count; `I64RotlPseudo`/`I64RotrPseudo`
    consume R0:R1 as the operand and R2 as the rotate amount). The lo/hi
    spec axioms in `ArmSemantics.v` (`i64_{shl,shru,shrs,rotl,rotr}_{lo,hi}_bits_spec`,
    shipped in the precursor PR #153) equate the axiomatic result to
    `lo_of_i64`/`hi_of_i64` of the WASM-spec function applied to the
    combined 64-bit operand and `combine_i32 cnt I32.zero` (high half of
    the count is logically zero — WASM shifts/rotates mask the count
    modulo 64, and the encoder relies on this).
    All five lift cleanly to Qed via the mechanical
      `intros; unfold compile_wasm_to_arm; simpl; rewrite Hregs;
       rewrite <spec>; eexists; split; ...; reflexivity`
    pattern. The `exec_wasm_instr` hypothesis is intentionally dropped
    per the PR-1/PR-2/PR-4 pattern: even though `WasmSemantics.v` does
    model i64 shifts/rotates, the new theorem shape gives a direct
    value-level correspondence between the WASM-spec function
    (`I64.{shl,shru,shrs,rotl,rotr}`) and the ARM execution result,
    without routing through `exec_wasm_instr`. No new spec axioms.

    v0.9.0 PR 5 (i64 bit-manipulation T1 lifts — final lift batch): The
    Clz/Ctz/Popcnt theorems are lifted from existence-only (with a
    placeholder `VI64 I64.zero` post-stack) to T1 with:
      - I64-typed hypothesis on the combined operand (lo in R0, hi in R1),
      - Single-register post-condition (R0 = `i64_to_i32 (I64.<op> v)`),
      - No `exec_wasm_instr` hypothesis (per the PR-1..PR-4 pattern).
    Each compiles to a single dual-input pseudo-op
    (`I64{Clz,Ctz,Popcnt}Pseudo R0 R0 R1`) whose semantics write
    `i64_{clz,ctz,popcnt}_bits vnlo vnhi` to R0; the spec axioms shipped
    in v0.9.0 PR 1 (#153) equate that to `i64_to_i32 (I64.{clz,ctz,popcnt}
    (combine_i32 lo hi))`. All three discharge as Qed via the mechanical
      intros; unfold compile_wasm_to_arm; simpl; rewrite Hregs;
      rewrite <op>_bits_spec; eexists; split;
      [reflexivity | apply get_set_reg_eq]
    pattern. No new spec axioms, no new Admitted proofs. This completes
    the v0.9.0 lift queue for CorrectnessI64.v.
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.
Require Import Synth.ARM.ArmSemantics.
Require Import Synth.ARM.ArmFlagLemmas.
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
  intros astate lo1 hi1 lo2 hi2 HR0 HR1 HR2 HR3.
  (* I64Add => [ADDS R0 R0 (Reg R2); ADC R1 R1 (Reg R3)]. ADDS writes
     I32.add lo1 lo2 to R0 and sets flag_c = compute_c_flag_add lo1 lo2;
     ADC then reads that flag and R1/R3 (untouched by ADDS, which only
     wrote R0 + flags) to write I32.add (I32.add hi1 hi2) carry into R1. *)
  unfold compile_wasm_to_arm.
  cbn [exec_program exec_instr eval_operand2].
  (* The ADC reads R1, R3 and flag_c from the post-ADDS state
     set_flags (set_reg astate R0 _) (update_flags_arith _ c _). *)
  rewrite flags_set_flags_set_reg.
  rewrite flag_c_update_flags_arith.
  pose proof (i64_add_via_adds_adc lo1 hi1 lo2 hi2) as [Hlo Hhi].
  eexists. split; [reflexivity | split].
  - (* R0 half: the ADC wrote R1, so R0 still holds the ADDS result.
       Final state = set_reg (set_flags (set_reg astate R0 _) _) R1 _. *)
    rewrite (get_set_reg_neq _ R1 R0) by discriminate.
    rewrite get_reg_set_flags.
    rewrite get_set_reg_eq.
    rewrite HR0, HR2. exact Hlo.
  - (* R1 half: the ADC result equals the hi half. *)
    rewrite get_set_reg_eq.
    rewrite !get_reg_set_flags.
    rewrite (get_set_reg_neq astate R0 R1) by discriminate.
    rewrite (get_set_reg_neq astate R0 R3) by discriminate.
    rewrite HR0, HR1, HR2, HR3. exact Hhi.
Qed.

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
  intros astate lo1 hi1 lo2 hi2 HR0 HR1 HR2 HR3.
  (* I64Sub => [SUBS R0 R0 (Reg R2); SBC R1 R1 (Reg R3)]. SUBS writes
     I32.sub lo1 lo2 to R0 and sets flag_c = compute_c_flag_sub lo1 lo2
     (C = no-borrow); SBC then reads that flag and R1/R3 to write
     I32.sub (I32.sub hi1 hi2) NOT(C) into R1. *)
  unfold compile_wasm_to_arm.
  cbn [exec_program exec_instr eval_operand2].
  rewrite flags_set_flags_set_reg.
  rewrite flag_c_update_flags_arith.
  pose proof (i64_sub_via_subs_sbc lo1 hi1 lo2 hi2) as [Hlo Hhi].
  eexists. split; [reflexivity | split].
  - (* R0 half: the SBC wrote R1, so R0 still holds the SUBS result.
       Final state = set_reg (set_flags (set_reg astate R0 _) _) R1 _. *)
    rewrite (get_set_reg_neq _ R1 R0) by discriminate.
    rewrite get_reg_set_flags.
    rewrite get_set_reg_eq.
    rewrite HR0, HR2. exact Hlo.
  - (* R1 half: the SBC result equals the hi half. *)
    rewrite get_set_reg_eq.
    rewrite !get_reg_set_flags.
    rewrite (get_set_reg_neq astate R0 R1) by discriminate.
    rewrite (get_set_reg_neq astate R0 R3) by discriminate.
    rewrite HR0, HR1, HR2, HR3. exact Hhi.
Qed.

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

(** ** v0.10.0 PR 2: bitwise halves-distribute helpers (pure Z, no axioms)

    A bitwise op commutes with taking the low 32 bits (mod 2^32) and with
    taking the high 32 bits (/ 2^32). Proven by bit extensionality for the
    low half and by the shiftr-distributes lemmas for the high half. *)

Lemma land_low32 : forall a b : Z,
  Z.land a b mod 2 ^ 32 = Z.land (a mod 2 ^ 32) (b mod 2 ^ 32).
Proof.
  intros a b. rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'; intros n Hn.
  rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec, ?Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit (Z.ones 32) n); reflexivity.
Qed.

Lemma lor_low32 : forall a b : Z,
  Z.lor a b mod 2 ^ 32 = Z.lor (a mod 2 ^ 32) (b mod 2 ^ 32).
Proof.
  intros a b. rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'; intros n Hn.
  rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec, ?Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit (Z.ones 32) n); reflexivity.
Qed.

Lemma lxor_low32 : forall a b : Z,
  Z.lxor a b mod 2 ^ 32 = Z.lxor (a mod 2 ^ 32) (b mod 2 ^ 32).
Proof.
  intros a b. rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'; intros n Hn.
  rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec, ?Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit (Z.ones 32) n); reflexivity.
Qed.

Lemma land_high32 : forall a b : Z,
  Z.land a b / 2 ^ 32 = Z.land (a / 2 ^ 32) (b / 2 ^ 32).
Proof.
  intros a b. rewrite <- !Z.shiftr_div_pow2 by lia. apply Z.shiftr_land.
Qed.

Lemma lor_high32 : forall a b : Z,
  Z.lor a b / 2 ^ 32 = Z.lor (a / 2 ^ 32) (b / 2 ^ 32).
Proof.
  intros a b. rewrite <- !Z.shiftr_div_pow2 by lia. apply Z.shiftr_lor.
Qed.

Lemma lxor_high32 : forall a b : Z,
  Z.lxor a b / 2 ^ 32 = Z.lxor (a / 2 ^ 32) (b / 2 ^ 32).
Proof.
  intros a b. rewrite <- !Z.shiftr_div_pow2 by lia. apply Z.shiftr_lxor.
Qed.

(** combine_i32 as a raw Z: the sum fits in 64 bits, so the I64.repr mod
    is the identity. *)
Lemma combine_i32_raw : forall lo hi : I32.int,
  combine_i32 lo hi = I32.unsigned lo + 2 ^ 32 * I32.unsigned hi.
Proof.
  intros lo hi. unfold combine_i32, I64.repr, I32.modulus, I64.modulus.
  assert (Hl : 0 <= I32.unsigned lo < 2 ^ 32)
    by (unfold I32.unsigned, I32.modulus; apply Z_mod_lt; lia).
  assert (Hh : 0 <= I32.unsigned hi < 2 ^ 32)
    by (unfold I32.unsigned, I32.modulus; apply Z_mod_lt; lia).
  assert (H64 : 2 ^ 64 = 2 ^ 32 * 2 ^ 32) by reflexivity.
  apply Z.mod_small. nia.
Qed.

(** (w mod 2^64) mod 2^32 = w mod 2^32 (2^32 divides 2^64). *)
Lemma mod64_mod32 : forall w, (w mod 2 ^ 64) mod 2 ^ 32 = w mod 2 ^ 32.
Proof.
  intros w. rewrite <- !Z.land_ones by lia.
  rewrite <- Z.land_assoc. f_equal.
Qed.

(** The low 32 bits of combine_i32 lo hi are I32.unsigned lo. *)
Lemma combine_lo32 : forall lo hi : I32.int,
  combine_i32 lo hi mod 2 ^ 32 = I32.unsigned lo.
Proof.
  intros lo hi. rewrite combine_i32_raw.
  assert (Hl : 0 <= I32.unsigned lo < 2 ^ 32)
    by (unfold I32.unsigned, I32.modulus; apply Z_mod_lt; lia).
  rewrite (Z.mul_comm (2 ^ 32) (I32.unsigned hi)).
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity.
Qed.

(** The high 32 bits of combine_i32 lo hi are I32.unsigned hi. *)
Lemma combine_hi32 : forall lo hi : I32.int,
  combine_i32 lo hi / 2 ^ 32 mod 2 ^ 32 = I32.unsigned hi.
Proof.
  intros lo hi. rewrite combine_i32_raw.
  assert (Hl : 0 <= I32.unsigned lo < 2 ^ 32)
    by (unfold I32.unsigned, I32.modulus; apply Z_mod_lt; lia).
  assert (Hh : 0 <= I32.unsigned hi < 2 ^ 32)
    by (unfold I32.unsigned, I32.modulus; apply Z_mod_lt; lia).
  rewrite (Z.mul_comm (2 ^ 32) (I32.unsigned hi)).
  rewrite Z.div_add by lia.
  rewrite (Z.div_small (I32.unsigned lo) (2 ^ 32)) by lia.
  rewrite Z.add_0_l. rewrite Z.mod_small by lia. reflexivity.
Qed.

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

(** v0.9.0 PR 3 lift: Shl/ShrU/ShrS/Rotl/Rotr restated with I64-typed
    hypotheses (operand lo/hi in R0:R1, 32-bit shift/rotate count in R2)
    and dual-register post-conditions. The spec axioms in `ArmSemantics.v`
    embed `combine_i32 cnt I32.zero` for the WASM-spec second operand
    because the encoder masks the count modulo 64 and the high half of
    the count is therefore logically zero. Each discharges via the
    mechanical
      intros; unfold compile_wasm_to_arm; simpl; rewrite Hregs;
      rewrite <op>_lo_bits_spec, <op>_hi_bits_spec; eexists;
      split; [reflexivity | split];
      [rewrite get_set_reg_neq by discriminate; apply get_set_reg_eq
       | apply get_set_reg_eq].
    pattern. No new spec axioms introduced. *)

Theorem i64_shl_correct : forall astate lo1 hi1 cnt,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = cnt ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Shl) astate = Some astate' /\
    get_reg astate' R0 =
      lo_of_i64 (I64.shl (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)) /\
    get_reg astate' R1 =
      hi_of_i64 (I64.shl (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).
Proof.
  intros astate lo1 hi1 cnt HR0 HR1 HR2.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2.
  rewrite i64_shl_lo_bits_spec, i64_shl_hi_bits_spec; simpl.
  eexists. split; [reflexivity | split].
  - rewrite get_set_reg_neq by discriminate. rewrite get_set_reg_eq. reflexivity.
  - rewrite get_set_reg_eq. reflexivity.
Qed.

Theorem i64_shru_correct : forall astate lo1 hi1 cnt,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = cnt ->
  exists astate',
    exec_program (compile_wasm_to_arm I64ShrU) astate = Some astate' /\
    get_reg astate' R0 =
      lo_of_i64 (I64.shru (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)) /\
    get_reg astate' R1 =
      hi_of_i64 (I64.shru (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).
Proof.
  intros astate lo1 hi1 cnt HR0 HR1 HR2.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2.
  rewrite i64_shru_lo_bits_spec, i64_shru_hi_bits_spec; simpl.
  eexists. split; [reflexivity | split].
  - rewrite get_set_reg_neq by discriminate. rewrite get_set_reg_eq. reflexivity.
  - rewrite get_set_reg_eq. reflexivity.
Qed.

Theorem i64_shrs_correct : forall astate lo1 hi1 cnt,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = cnt ->
  exists astate',
    exec_program (compile_wasm_to_arm I64ShrS) astate = Some astate' /\
    get_reg astate' R0 =
      lo_of_i64 (I64.shrs (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)) /\
    get_reg astate' R1 =
      hi_of_i64 (I64.shrs (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).
Proof.
  intros astate lo1 hi1 cnt HR0 HR1 HR2.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2.
  rewrite i64_shrs_lo_bits_spec, i64_shrs_hi_bits_spec; simpl.
  eexists. split; [reflexivity | split].
  - rewrite get_set_reg_neq by discriminate. rewrite get_set_reg_eq. reflexivity.
  - rewrite get_set_reg_eq. reflexivity.
Qed.

Theorem i64_rotl_correct : forall astate lo1 hi1 cnt,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = cnt ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Rotl) astate = Some astate' /\
    get_reg astate' R0 =
      lo_of_i64 (I64.rotl (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)) /\
    get_reg astate' R1 =
      hi_of_i64 (I64.rotl (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).
Proof.
  intros astate lo1 hi1 cnt HR0 HR1 HR2.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2.
  rewrite i64_rotl_lo_bits_spec, i64_rotl_hi_bits_spec; simpl.
  eexists. split; [reflexivity | split].
  - rewrite get_set_reg_neq by discriminate. rewrite get_set_reg_eq. reflexivity.
  - rewrite get_set_reg_eq. reflexivity.
Qed.

Theorem i64_rotr_correct : forall astate lo1 hi1 cnt,
  get_reg astate R0 = lo1 ->
  get_reg astate R1 = hi1 ->
  get_reg astate R2 = cnt ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Rotr) astate = Some astate' /\
    get_reg astate' R0 =
      lo_of_i64 (I64.rotr (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)) /\
    get_reg astate' R1 =
      hi_of_i64 (I64.rotr (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).
Proof.
  intros astate lo1 hi1 cnt HR0 HR1 HR2.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1, HR2.
  rewrite i64_rotr_lo_bits_spec, i64_rotr_hi_bits_spec; simpl.
  eexists. split; [reflexivity | split].
  - rewrite get_set_reg_neq by discriminate. rewrite get_set_reg_eq. reflexivity.
  - rewrite get_set_reg_eq. reflexivity.
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

(** v0.9.0 PR 5 lift: Clz/Ctz/Popcnt restated with I64-typed hypotheses
    (operand lo/hi in R0:R1) and a single-register post-condition (R0
    holds the i32 count — `clz/ctz/popcnt` of a 64-bit value fit in 32
    bits, so the codegen produces just one half).

    Each compiles to a single pseudo-op (`I64{Clz,Ctz,Popcnt}Pseudo R0 R0 R1`)
    whose semantics write `i64_{clz,ctz,popcnt}_bits vnlo vnhi` into R0.
    The spec axioms `i64_{clz,ctz,popcnt}_bits_spec` in `ArmSemantics.v`
    equate that axiomatic result function to `i64_to_i32 (I64.{clz,ctz,
    popcnt} (combine_i32 lo hi))`, where `i64_to_i32` truncates the
    64-bit count to its low 32 bits (always lossless because the count
    is bounded by 64, see `I64.{clz,ctz,popcnt}_range` axioms).

    All three discharge via the mechanical
      intros; unfold compile_wasm_to_arm; simpl; rewrite Hregs;
      rewrite <spec>; eexists; split; [reflexivity | apply get_set_reg_eq]
    pattern. The `exec_wasm_instr` hypothesis is intentionally dropped
    per the PR-1/PR-2/PR-3/PR-4 pattern: although `WasmSemantics.v` *does*
    model i64 clz/ctz/popcnt (lines 458-481, pushing `VI64 (I64.<op> v)`),
    the new theorem shape gives a direct value-level correspondence
    between the WASM-spec function and the ARM execution result (the
    `i64_to_i32` cast captures the 32-bit return convention of the
    pseudo-op). No new spec axioms. *)

Theorem i64_clz_correct : forall astate lo hi,
  get_reg astate R0 = lo ->
  get_reg astate R1 = hi ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Clz) astate = Some astate' /\
    get_reg astate' R0 = i64_to_i32 (I64.clz (combine_i32 lo hi)).
Proof.
  intros astate lo hi HR0 HR1.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1.
  rewrite i64_clz_bits_spec.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

Theorem i64_ctz_correct : forall astate lo hi,
  get_reg astate R0 = lo ->
  get_reg astate R1 = hi ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Ctz) astate = Some astate' /\
    get_reg astate' R0 = i64_to_i32 (I64.ctz (combine_i32 lo hi)).
Proof.
  intros astate lo hi HR0 HR1.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1.
  rewrite i64_ctz_bits_spec.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

Theorem i64_popcnt_correct : forall astate lo hi,
  get_reg astate R0 = lo ->
  get_reg astate R1 = hi ->
  exists astate',
    exec_program (compile_wasm_to_arm I64Popcnt) astate = Some astate' /\
    get_reg astate' R0 = i64_to_i32 (I64.popcnt (combine_i32 lo hi)).
Proof.
  intros astate lo hi HR0 HR1.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1.
  rewrite i64_popcnt_bits_spec.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

(** ** Summary (after v0.9.0 PR 2 — i64 arith + bitwise restated)

    I64 Operations: 26 theorems in this file
    - Arithmetic T1: 3 Qed (Mul via `i64_mul_{lo,hi}_bits_spec`; Add via
      `i64_add_via_adds_adc`; Sub via `i64_sub_via_subs_sbc` — v0.10.0 PR 1
      closed the Add/Sub carry/borrow-propagation gap with no new axioms).
    - Division/remainder T1: 4 Qed (DivS, DivU, RemS, RemU) — discharged
      via `i64_{divs,divu,rems,remu}_pair_spec` axioms in ArmSemantics.v.
    - Bitwise T1: 0 Qed + 3 Admitted (And, Or, Xor — gap: halves-distribute
      decomposition lemmas blocked by Rocq 9 `Z.mod_mod` rewrite issue,
      same root cause as `i64_to_i32_to_i64_wrap`).
    - Shift/rotate T1: 5 Qed (Shl, ShrU, ShrS, Rotl, Rotr) — discharged
      via `i64_{shl,shru,shrs,rotl,rotr}_{lo,hi}_bits_spec` axioms in
      ArmSemantics.v (v0.9.0 PR 3).
    - Comparison existence: 11 Qed (Eqz, Eq, Ne, Lt[SU], Le[SU], Gt[SU],
      Ge[SU]) — T1 lifts scheduled as v0.9.0 PR 4.
    - Bit-manipulation T1: 3 Qed (Clz, Ctz, Popcnt) — discharged via
      `i64_{clz,ctz,popcnt}_bits_spec` axioms in ArmSemantics.v
      (v0.9.0 PR 5 — final lift batch).

    v0.10.0 PR 1 net change vs. v0.9.0: +2 Qed (i64_add_correct,
    i64_sub_correct closed via the ADDS/ADC + SUBS/SBC carry/borrow-
    propagation lemmas in ArmFlagLemmas.v). 3 Admitted remain in this file
    (And/Or/Xor — separate PR, blocked on the Rocq 9 Z.mod_mod
    halves-distribute rework). No new axioms.
*)
