(** * I32 Operations Correctness

    This file contains correctness proofs for all i32 WebAssembly operations.
    Total: 29 theorems — 29 Qed, 0 Admitted

    Strategy:
    - Arithmetic (add, sub, mul, and, or, xor): synth_binop_proof tactic
    - Division (divs, divu) + remainder (rems, remu): Qed against the
      branch-taking executor exec_program_br — the trap guard's BCondOffset
      actually skips the UDF (#73); divs discharges the DOUBLE guard
      (divide-by-zero + INT_MIN/-1 overflow) with a case split on the
      dividend-is-INT_MIN compare
    - Comparisons: flag-correspondence lemmas from ArmFlagLemmas.v
    - Bit manipulation: axiom-based (I32.clz/rbit/popcnt)
    - Shifts: Qed — mod-32 mask + register shift (#682)
*)

From Stdlib Require Import ZArith Lia Znumtheory.
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
Require Import Synth.ARM.ArmFlagLemmas.

Open Scope Z_scope.

(** ** I32 Arithmetic Operations (10 total) *)

(** Already proven in Correctness.v, reproving with automation *)

Theorem i32_add_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32Add wstate =
    Some (mkWasmState (VI32 (I32.add v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Add) astate = Some astate' /\
    get_reg astate' R0 = I32.add v1 v2.
Proof. synth_binop_proof. Qed.

Theorem i32_sub_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32Sub wstate =
    Some (mkWasmState (VI32 (I32.sub v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Sub) astate = Some astate' /\
    get_reg astate' R0 = I32.sub v1 v2.
Proof. synth_binop_proof. Qed.

Theorem i32_mul_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32Mul wstate =
    Some (mkWasmState (VI32 (I32.mul v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Mul) astate = Some astate' /\
    get_reg astate' R0 = I32.mul v1 v2.
Proof. synth_binop_proof. Qed.

(** Division operations — trap-guarded sequences (#73).

    The compilation emits CMP + BCondOffset + UDF trap guards before the
    actual SDIV/UDIV. Under the flat sequential [exec_program] these are
    unprovable (BCondOffset is a no-op there, so the UDF is always reached
    and returns None); the PC-indexed branch-taking executor
    [exec_program_br] (ArmSemantics.v) is the model that can take the
    guard's skip.

    Status: ALL FOUR div/rem theorems are DISCHARGED against
    [exec_program_br] below (guard + UDIV/SDIV + MLS tail);
    [i32_divs_correct] closes the family with the INT_MIN/-1 double-guard
    case split — the last i32 admit of #73. *)

(** i32.div_s — the LAST div/rem trap-guard proof, discharged against the
    branch-taking executor [exec_program_br] (#73). The compiled sequence
    carries the DOUBLE guard: CMP R1,#0; BNE +1; UDF (divide-by-zero), then
    MOVW/MOVT R2 := 0x80000000; CMP R0,R2; BNE +3 — and only when the
    dividend IS INT_MIN — CMN R1,#1; BNE +1; UDF (INT_MIN/-1 overflow);
    finally SDIV. [I32.divs v1 v2 = Some result] supplies both guard
    discharges: the divisor is non-zero (first BNE taken), and NOT
    (signed v1 = INT_MIN ∧ signed v2 = -1) — so when the second CMP finds
    the dividend equal to 0x80000000 the CMN must find the divisor ≠ -1
    (third BNE taken). Both paths land on the SDIV, whose model is
    [I32.divs] itself.

    [I32.valid_unsigned v2] is the same register-normalization hypothesis
    as in [i32_divu_correct] (raw [v2 =? 0] model guard vs the CMP's
    [v2 mod 2^32] Z-flag). The INT_MIN and -1 guard comparisons need no
    such hypothesis: [I32.signed] already works mod 2^32, exactly like the
    flags. This restatement is only provable because [I32.divs]'s overflow
    guard now tests the signed interpretation (see Integers.v) — against
    the old raw-representative guard the theorem was FALSE at
    v1 = 0x80000000, v2 = 0xFFFFFFFF (model said Some, hardware traps). *)
Theorem i32_divs_correct : forall wstate astate v1 v2 stack' result,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  I32.valid_unsigned v2 ->
  I32.divs v1 v2 = Some result ->
  exec_wasm_instr I32DivS wstate =
    Some (mkWasmState (VI32 result :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program_br (compile_wasm_to_arm I32DivS) astate = Some astate' /\
    get_reg astate' R0 = result.
Proof.
  intros wstate astate v1 v2 stack' result Hstack HR0 HR1 Hval Hdivs Hwasm.
  (* Peel the divs guards: the divisor is non-zero, and the INT_MIN/-1
     overflow conjunction is false. *)
  assert (Hnz : v2 <> 0).
  { unfold I32.divs in Hdivs.
    destruct (Z.eqb_spec v2 0); [discriminate | assumption]. }
  assert (Hovf : (Z.eqb (I32.signed v1) I32.min_signed
                  && Z.eqb (I32.signed v2) (-1))%bool = false).
  { unfold I32.divs in Hdivs.
    destruct (Z.eqb_spec v2 0); [discriminate |].
    destruct ((Z.eqb (I32.signed v1) I32.min_signed
               && Z.eqb (I32.signed v2) (-1))%bool) eqn:E;
      [discriminate | reflexivity]. }
  (* The Z flag latched by CMP R1,#0 is false (divu precedent). *)
  assert (Hz : compute_z_flag (I32.sub v2 I32.zero) = false).
  { rewrite z_flag_sub_eq.
    unfold I32.eq.
    replace (I32.unsigned I32.zero) with 0 by reflexivity.
    apply Z.eqb_neq.
    unfold I32.unsigned.
    rewrite Z.mod_small; [exact Hnz |].
    unfold I32.valid_unsigned, I32.max_unsigned, I32.modulus in *. lia. }
  unfold exec_program_br.
  change (length (compile_wasm_to_arm I32DivS)) with 11%nat.
  (* pc = 0: CMP R1,#0 latches the flags, registers untouched. *)
  erewrite (exec_program_pc_instr _ _ _ _ (CMP R1 (Imm I32.zero)));
    [| reflexivity | exact I].
  cbn [exec_instr eval_operand2].
  (* pc = 1: BNE +1 — Z=0, branch TAKEN, skips the ÷0 UDF. *)
  erewrite (exec_program_pc_bcond _ _ _ _ Cond_NE 1); [| reflexivity].
  rewrite flags_set_flags.
  cbn [eval_condition].
  rewrite flag_z_update_flags_arith.
  rewrite HR1, Hz.
  cbn [negb].
  (* pc = 3: MOVW R2,#0 — low half of INT_MIN. *)
  erewrite (exec_program_pc_instr _ _ _ _ (MOVW R2 (I32.repr 0)));
    [| reflexivity | exact I].
  cbn [exec_instr].
  (* pc = 4: MOVT R2,#0x8000 — R2 = 0x80000000 = 2147483648. *)
  erewrite (exec_program_pc_instr _ _ _ _ (MOVT R2 (I32.repr 32768)));
    [| reflexivity | exact I].
  cbn [exec_instr].
  rewrite get_set_reg_eq.
  replace (I32.or (I32.and (I32.repr 0) (I32.repr 65535))
             (I32.shl (I32.repr 32768) (I32.repr 16)))
    with 2147483648 by reflexivity.
  (* pc = 5: CMP R0,R2 — compares the dividend against INT_MIN. *)
  erewrite (exec_program_pc_instr _ _ _ _ (CMP R0 (Reg R2)));
    [| reflexivity | exact I].
  cbn [exec_instr eval_operand2].
  rewrite get_set_reg_eq.
  rewrite !(get_set_reg_neq _ R2 R0) by discriminate.
  rewrite !get_reg_set_flags.
  rewrite HR0.
  (* pc = 6: BNE +3 — case split on dividend = INT_MIN. *)
  erewrite (exec_program_pc_bcond _ _ _ _ Cond_NE 3); [| reflexivity].
  rewrite flags_set_flags.
  cbn [eval_condition].
  rewrite flag_z_update_flags_arith.
  rewrite z_flag_sub_eq.
  destruct (I32.eq v1 2147483648) eqn:Hmin; cbn [negb].
  - (* Dividend IS INT_MIN: fall through to the CMN R1,#1 overflow guard,
       which must find the divisor ≠ -1 (else divs would have trapped). *)
    assert (Hsv1 : I32.signed v1 = I32.min_signed).
    { unfold I32.eq in Hmin.
      apply Z.eqb_eq in Hmin.
      replace (I32.unsigned 2147483648) with 2147483648 in Hmin
        by reflexivity.
      unfold I32.signed. rewrite Hmin. reflexivity. }
    assert (Hsv2 : Z.eqb (I32.signed v2) (-1) = false).
    { rewrite Hsv1, Z.eqb_refl in Hovf. cbn [andb] in Hovf. exact Hovf. }
    apply Z.eqb_neq in Hsv2.
    (* The Z flag latched by CMN R1,#1 is therefore false. *)
    assert (Hz3 : compute_z_flag (I32.add v2 I32.one) = false).
    { unfold compute_z_flag, I32.eq.
      replace (I32.unsigned I32.zero) with 0 by reflexivity.
      apply Z.eqb_neq. intro Heq0.
      apply Hsv2.
      unfold I32.unsigned, I32.add, I32.repr in Heq0.
      change I32.one with 1 in Heq0.
      rewrite Zmod_mod in Heq0.
      assert (Hu : v2 mod I32.modulus = I32.modulus - 1).
      { assert (HM : 0 < I32.modulus) by (unfold I32.modulus; lia).
        assert (Hb : 0 <= v2 mod I32.modulus < I32.modulus)
          by (apply Z.mod_pos_bound; lia).
        rewrite <- Zplus_mod_idemp_l in Heq0.
        destruct (Z.eqb_spec (v2 mod I32.modulus) (I32.modulus - 1))
          as [E | E]; [exact E |].
        rewrite Z.mod_small in Heq0; lia. }
      unfold I32.signed, I32.unsigned.
      rewrite Hu.
      reflexivity. }
    (* pc = 7: CMN R1,#1 latches Z = (v2 + 1 == 0). *)
    erewrite (exec_program_pc_instr _ _ _ _ (CMN R1 (Imm I32.one)));
      [| reflexivity | exact I].
    cbn [exec_instr eval_operand2].
    rewrite !get_reg_set_flags.
    rewrite !(get_set_reg_neq _ R2 R1) by discriminate.
    rewrite !get_reg_set_flags.
    rewrite HR1.
    (* pc = 8: BNE +1 — divisor ≠ -1, branch TAKEN, skips the overflow UDF. *)
    erewrite (exec_program_pc_bcond _ _ _ _ Cond_NE 1); [| reflexivity].
    rewrite flags_set_flags.
    cbn [eval_condition].
    rewrite flag_z_update_flags_arith.
    rewrite Hz3.
    cbn [negb].
    (* pc = 10: SDIV R0,R0,R1 — the model is I32.divs itself. *)
    erewrite (exec_program_pc_instr _ _ _ _ (SDIV R0 R0 R1));
      [| reflexivity | exact I].
    cbn [exec_instr].
    rewrite !get_reg_set_flags.
    rewrite !(get_set_reg_neq _ R2 R0) by discriminate.
    rewrite !(get_set_reg_neq _ R2 R1) by discriminate.
    rewrite !get_reg_set_flags.
    rewrite HR0, HR1, Hdivs.
    cbn beta iota.
    (* pc = 11: off the end — the program completed. *)
    rewrite exec_program_pc_done; [| reflexivity].
    eexists. split.
    + reflexivity.
    + apply get_set_reg_eq.
  - (* Dividend ≠ INT_MIN: branch straight to the SDIV. *)
    erewrite (exec_program_pc_instr _ _ _ _ (SDIV R0 R0 R1));
      [| reflexivity | exact I].
    cbn [exec_instr].
    rewrite !get_reg_set_flags.
    rewrite !(get_set_reg_neq _ R2 R0) by discriminate.
    rewrite !(get_set_reg_neq _ R2 R1) by discriminate.
    rewrite !get_reg_set_flags.
    rewrite HR0, HR1, Hdivs.
    cbn beta iota.
    rewrite exec_program_pc_done; [| reflexivity].
    eexists. split.
    + reflexivity.
    + apply get_set_reg_eq.
Qed.

(** i32.div_u — the FIRST trap-guard proof discharged against the
    branch-taking executor [exec_program_br] (#73): the compiled sequence
    is CMP R1,#0; BNE +1; UDF; UDIV — with a non-zero divisor the CMP
    latches Z=0, the BNE is TAKEN (pc skips the UDF), and the UDIV
    computes the quotient. The flat [exec_program] cannot state this
    (BCondOffset is a no-op there, so UDF is always reached).

    The extra [I32.valid_unsigned v2] hypothesis is the register
    well-formedness the flat model left implicit: [I32.divu]'s trap guard
    tests the RAW representative [v2 =? 0] while the CMP Z-flag observes
    [v2 mod 2^32]; the two agree exactly on normalized 32-bit values
    (every value a [set_reg]-produced state can hold). *)
Theorem i32_divu_correct : forall wstate astate v1 v2 stack' result,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  I32.valid_unsigned v2 ->
  I32.divu v1 v2 = Some result ->
  exec_wasm_instr I32DivU wstate =
    Some (mkWasmState (VI32 result :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program_br (compile_wasm_to_arm I32DivU) astate = Some astate' /\
    get_reg astate' R0 = result.
Proof.
  intros wstate astate v1 v2 stack' result Hstack HR0 HR1 Hval Hdivu Hwasm.
  (* The divisor is non-zero — otherwise divu would have trapped. *)
  assert (Hnz : v2 <> 0).
  { unfold I32.divu in Hdivu.
    destruct (Z.eqb_spec v2 0); [discriminate | assumption]. }
  (* The Z flag latched by CMP R1,#0 is therefore false. *)
  assert (Hz : compute_z_flag (I32.sub v2 I32.zero) = false).
  { rewrite z_flag_sub_eq.
    unfold I32.eq.
    replace (I32.unsigned I32.zero) with 0 by reflexivity.
    apply Z.eqb_neq.
    unfold I32.unsigned.
    rewrite Z.mod_small; [exact Hnz |].
    unfold I32.valid_unsigned, I32.max_unsigned, I32.modulus in *. lia. }
  (* Symbolic execution goes through the one-step exec_program_pc_* rewrite
     lemmas — cbn/simpl on the executor fixpoint is exponential (see the
     warning at the lemmas in ArmSemantics.v). *)
  unfold exec_program_br.
  change (length (compile_wasm_to_arm I32DivU)) with 4%nat.
  (* pc = 0: CMP R1,#0 latches the flags, registers untouched. *)
  erewrite (exec_program_pc_instr _ _ _ _ (CMP R1 (Imm I32.zero)));
    [| reflexivity | exact I].
  cbn [exec_instr eval_operand2].
  (* pc = 1: BNE +1 — Z=0, so the branch is TAKEN, skipping the UDF. *)
  erewrite (exec_program_pc_bcond _ _ _ _ Cond_NE 1); [| reflexivity].
  rewrite flags_set_flags.
  cbn [eval_condition].
  rewrite flag_z_update_flags_arith.
  rewrite HR1, Hz.
  cbn [negb].
  (* pc = 3: UDIV R0,R0,R1 computes the quotient. *)
  erewrite (exec_program_pc_instr _ _ _ _ (UDIV R0 R0 R1));
    [| reflexivity | exact I].
  cbn [exec_instr].
  rewrite !get_reg_set_flags.
  rewrite HR0, HR1, Hdivu.
  cbn beta iota.
  (* pc = 4: off the end — the program completed. *)
  rewrite exec_program_pc_done; [| reflexivity].
  eexists. split.
  - reflexivity.
  - apply get_set_reg_eq.
Qed.

(** i32.rem_s — trap-guard restatement against [exec_program_br] (#73).
    Identical shape to [i32_remu_correct] but with SDIV: CMP R1,#0; BNE +1;
    UDF; SDIV R2,R0,R1; MLS R0,R2,R1,R0. The single divide-by-zero guard
    is the only trap in both the code and the [I32.rems] model — signed
    remainder does not trap on INT_MIN/-1 (and neither does this sequence).
    [I32.divs v1 v2 = Some quotient] gives both [v2 <> 0] and the SDIV
    result; MLS then computes v1 - quotient*v2. *)
Theorem i32_rems_correct : forall wstate astate v1 v2 stack' result quotient,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  I32.valid_unsigned v2 ->
  I32.divs v1 v2 = Some quotient ->
  result = I32.sub v1 (I32.mul quotient v2) ->
  I32.rems v1 v2 = Some result ->
  exec_wasm_instr I32RemS wstate =
    Some (mkWasmState (VI32 result :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program_br (compile_wasm_to_arm I32RemS) astate = Some astate' /\
    get_reg astate' R0 = result.
Proof.
  intros wstate astate v1 v2 stack' result quotient
    Hstack HR0 HR1 Hval Hdivs Hresult Hrems Hwasm.
  (* The divisor is non-zero — otherwise divs would have trapped. *)
  assert (Hnz : v2 <> 0).
  { unfold I32.divs in Hdivs.
    destruct (Z.eqb_spec v2 0); [discriminate | assumption]. }
  assert (Hz : compute_z_flag (I32.sub v2 I32.zero) = false).
  { rewrite z_flag_sub_eq.
    unfold I32.eq.
    replace (I32.unsigned I32.zero) with 0 by reflexivity.
    apply Z.eqb_neq.
    unfold I32.unsigned.
    rewrite Z.mod_small; [exact Hnz |].
    unfold I32.valid_unsigned, I32.max_unsigned, I32.modulus in *. lia. }
  unfold exec_program_br.
  change (length (compile_wasm_to_arm I32RemS)) with 5%nat.
  (* pc = 0: CMP R1,#0 latches the flags. *)
  erewrite (exec_program_pc_instr _ _ _ _ (CMP R1 (Imm I32.zero)));
    [| reflexivity | exact I].
  cbn [exec_instr eval_operand2].
  (* pc = 1: BNE +1 — Z=0, branch TAKEN, skips the UDF. *)
  erewrite (exec_program_pc_bcond _ _ _ _ Cond_NE 1); [| reflexivity].
  rewrite flags_set_flags.
  cbn [eval_condition].
  rewrite flag_z_update_flags_arith.
  rewrite HR1, Hz.
  cbn [negb].
  (* pc = 3: SDIV R2,R0,R1 -> R2 = quotient. *)
  erewrite (exec_program_pc_instr _ _ _ _ (SDIV R2 R0 R1));
    [| reflexivity | exact I].
  cbn [exec_instr].
  rewrite !get_reg_set_flags.
  rewrite HR0, HR1, Hdivs.
  cbn beta iota.
  (* pc = 4: MLS R0,R2,R1,R0 -> R0 = v1 - quotient*v2. *)
  erewrite (exec_program_pc_instr _ _ _ _ (MLS R0 R2 R1 R0));
    [| reflexivity | exact I].
  cbn [exec_instr].
  rewrite (get_set_reg_eq _ R2).
  rewrite (get_set_reg_neq _ R2 R1) by discriminate.
  rewrite (get_set_reg_neq _ R2 R0) by discriminate.
  rewrite !get_reg_set_flags.
  rewrite HR0, HR1.
  cbn beta iota.
  (* pc = 5: off the end. *)
  rewrite exec_program_pc_done; [| reflexivity].
  eexists. split.
  - reflexivity.
  - rewrite get_set_reg_eq. symmetry. exact Hresult.
Qed.

(** i32.rem_u — trap-guard restatement against [exec_program_br] (#73),
    the same vehicle that discharged [i32_divu_correct]. The compiled
    sequence is CMP R1,#0; BNE +1; UDF; UDIV R2,R0,R1; MLS R0,R2,R1,R0:
    with a non-zero divisor the CMP latches Z=0, the BNE is TAKEN (pc skips
    the UDF), UDIV puts the quotient in R2, and MLS computes
    R0 - R2*R1 = v1 - quotient*v2 = the remainder. The [I32.valid_unsigned v2]
    hypothesis is the same register-normalization the flat model left
    implicit (raw [v2 =? 0] guard vs the CMP's [v2 mod 2^32] Z-flag). *)
Theorem i32_remu_correct : forall wstate astate v1 v2 stack' result quotient,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  I32.valid_unsigned v2 ->
  I32.divu v1 v2 = Some quotient ->
  result = I32.sub v1 (I32.mul quotient v2) ->
  I32.remu v1 v2 = Some result ->
  exec_wasm_instr I32RemU wstate =
    Some (mkWasmState (VI32 result :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program_br (compile_wasm_to_arm I32RemU) astate = Some astate' /\
    get_reg astate' R0 = result.
Proof.
  intros wstate astate v1 v2 stack' result quotient
    Hstack HR0 HR1 Hval Hdivu Hresult Hremu Hwasm.
  (* The divisor is non-zero — otherwise divu would have trapped. *)
  assert (Hnz : v2 <> 0).
  { unfold I32.divu in Hdivu.
    destruct (Z.eqb_spec v2 0); [discriminate | assumption]. }
  (* The Z flag latched by CMP R1,#0 is therefore false. *)
  assert (Hz : compute_z_flag (I32.sub v2 I32.zero) = false).
  { rewrite z_flag_sub_eq.
    unfold I32.eq.
    replace (I32.unsigned I32.zero) with 0 by reflexivity.
    apply Z.eqb_neq.
    unfold I32.unsigned.
    rewrite Z.mod_small; [exact Hnz |].
    unfold I32.valid_unsigned, I32.max_unsigned, I32.modulus in *. lia. }
  unfold exec_program_br.
  change (length (compile_wasm_to_arm I32RemU)) with 5%nat.
  (* pc = 0: CMP R1,#0 latches the flags, registers untouched. *)
  erewrite (exec_program_pc_instr _ _ _ _ (CMP R1 (Imm I32.zero)));
    [| reflexivity | exact I].
  cbn [exec_instr eval_operand2].
  (* pc = 1: BNE +1 — Z=0, so the branch is TAKEN, skipping the UDF. *)
  erewrite (exec_program_pc_bcond _ _ _ _ Cond_NE 1); [| reflexivity].
  rewrite flags_set_flags.
  cbn [eval_condition].
  rewrite flag_z_update_flags_arith.
  rewrite HR1, Hz.
  cbn [negb].
  (* pc = 3: UDIV R2,R0,R1 -> R2 = quotient. *)
  erewrite (exec_program_pc_instr _ _ _ _ (UDIV R2 R0 R1));
    [| reflexivity | exact I].
  cbn [exec_instr].
  rewrite !get_reg_set_flags.
  rewrite HR0, HR1, Hdivu.
  cbn beta iota.
  (* pc = 4: MLS R0,R2,R1,R0 -> R0 = R0 - R2*R1 = v1 - quotient*v2. *)
  erewrite (exec_program_pc_instr _ _ _ _ (MLS R0 R2 R1 R0));
    [| reflexivity | exact I].
  cbn [exec_instr].
  rewrite (get_set_reg_eq _ R2).
  rewrite (get_set_reg_neq _ R2 R1) by discriminate.
  rewrite (get_set_reg_neq _ R2 R0) by discriminate.
  rewrite !get_reg_set_flags.
  rewrite HR0, HR1.
  cbn beta iota.
  (* pc = 5: off the end — the program completed. *)
  rewrite exec_program_pc_done; [| reflexivity].
  eexists. split.
  - reflexivity.
  - rewrite get_set_reg_eq. symmetry. exact Hresult.
Qed.

(** ** I32 Bitwise Operations (10 total) *)

Theorem i32_and_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32And wstate =
    Some (mkWasmState (VI32 (I32.and v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32And) astate = Some astate' /\
    get_reg astate' R0 = I32.and v1 v2.
Proof. synth_binop_proof. Qed.

Theorem i32_or_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32Or wstate =
    Some (mkWasmState (VI32 (I32.or v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Or) astate = Some astate' /\
    get_reg astate' R0 = I32.or v1 v2.
Proof. synth_binop_proof. Qed.

Theorem i32_xor_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32Xor wstate =
    Some (mkWasmState (VI32 (I32.xor v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Xor) astate = Some astate' /\
    get_reg astate' R0 = I32.xor v1 v2.
Proof. synth_binop_proof. Qed.

(** Shift operations — register-based, matching the Rust instruction
    selector. #682: the amount is masked mod 32 through R12 (ARMv7-M
    register shifts consume Rm[7:0]; WASM requires mod 32 — the old bare
    single-instruction lowering was wrong on hardware and its proof
    vacuous, since I32.shl masks internally). Z-level mask lemmas below
    duplicate VcrSelRules.v pending consolidation into Common/Integers. *)

Lemma land31_mod32' : forall a : Z, (Z.land a 31) mod 32 = a mod 32.
Proof.
  intros a. change 31 with (Z.ones 5).
  rewrite Z.land_ones by lia.
  change (2 ^ 5) with 32. apply Z.mod_mod. lia.
Qed.

Lemma mod_modulus_mod32' : forall a : Z, (a mod 4294967296) mod 32 = a mod 32.
Proof.
  intros a.
  symmetry. apply Zmod_div_mod; [lia | lia | exists 134217728; reflexivity].
Qed.

Theorem i32_shl_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32Shl wstate =
    Some (mkWasmState (VI32 (I32.shl v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Shl) astate = Some astate' /\
    get_reg astate' R0 = I32.shl v1 v2.
Proof.
  intros wstate astate v1 v2 stack' Hstack HR0 HR1 Hwasm.
  unfold compile_wasm_to_arm.
  set (s1 := set_reg astate R12 (I32.and (get_reg astate R1) (I32.repr 31))).
  set (s2 := set_reg s1 R0 (I32.shl (get_reg s1 R0) (get_reg s1 R12))).
  exists s2. split.
  - subst s2 s1. simpl. reflexivity.
  - subst s2. rewrite get_set_reg_eq.
    subst s1. rewrite get_set_reg_neq by discriminate.
    rewrite get_set_reg_eq.
    rewrite HR0, HR1.
    unfold I32.shl, I32.and, I32.repr, I32.unsigned, I32.modulus.
    change (31 mod 4294967296) with 31.
    rewrite !mod_modulus_mod32', land31_mod32'.
    reflexivity.
Qed.

Theorem i32_shru_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32ShrU wstate =
    Some (mkWasmState (VI32 (I32.shru v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32ShrU) astate = Some astate' /\
    get_reg astate' R0 = I32.shru v1 v2.
Proof.
  intros wstate astate v1 v2 stack' Hstack HR0 HR1 Hwasm.
  unfold compile_wasm_to_arm.
  set (s1 := set_reg astate R12 (I32.and (get_reg astate R1) (I32.repr 31))).
  set (s2 := set_reg s1 R0 (I32.shru (get_reg s1 R0) (get_reg s1 R12))).
  exists s2. split.
  - subst s2 s1. simpl. reflexivity.
  - subst s2. rewrite get_set_reg_eq.
    subst s1. rewrite get_set_reg_neq by discriminate.
    rewrite get_set_reg_eq.
    rewrite HR0, HR1.
    unfold I32.shru, I32.and, I32.repr, I32.unsigned, I32.modulus.
    change (31 mod 4294967296) with 31.
    rewrite !mod_modulus_mod32', land31_mod32'.
    reflexivity.
Qed.

Theorem i32_shrs_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32ShrS wstate =
    Some (mkWasmState (VI32 (I32.shrs v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32ShrS) astate = Some astate' /\
    get_reg astate' R0 = I32.shrs v1 v2.
Proof.
  intros wstate astate v1 v2 stack' Hstack HR0 HR1 Hwasm.
  unfold compile_wasm_to_arm.
  set (s1 := set_reg astate R12 (I32.and (get_reg astate R1) (I32.repr 31))).
  set (s2 := set_reg s1 R0 (I32.shrs (get_reg s1 R0) (get_reg s1 R12))).
  exists s2. split.
  - subst s2 s1. simpl. reflexivity.
  - subst s2. rewrite get_set_reg_eq.
    subst s1. rewrite get_set_reg_neq by discriminate.
    rewrite get_set_reg_eq.
    rewrite HR0, HR1.
    unfold I32.shrs, I32.and, I32.repr, I32.unsigned, I32.modulus.
    change (31 mod 4294967296) with 31.
    rewrite !mod_modulus_mod32', land31_mod32'.
    reflexivity.
Qed.

Theorem i32_rotl_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32Rotl wstate =
    Some (mkWasmState (VI32 (I32.rotl v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Rotl) astate = Some astate' /\
    get_reg astate' R0 = I32.rotl v1 v2.
Proof.
  (* Compiles to [RSB R2 R1 (Imm 32); ROR_reg R0 R0 R2] *)
  (* ARM computes: R2 = 32 - R1, then R0 = rotr(R0, R2) *)
  (* By rotl_rotr_sub axiom: rotl v1 v2 = rotr v1 (sub (repr 32) v2) *)
  intros wstate astate v1 v2 stack' Hstack HR0 HR1 Hwasm.
  unfold compile_wasm_to_arm.
  (* Provide explicit witness to avoid simpl-in-goal issues *)
  set (s1 := set_reg astate R2 (I32.sub (I32.repr 32) (get_reg astate R1))).
  set (s2 := set_reg s1 R0 (I32.rotr (get_reg s1 R0) (get_reg s1 R2))).
  exists s2. split.
  - subst s2 s1. simpl. reflexivity.
  - subst s2. rewrite get_set_reg_eq.
    subst s1. rewrite get_set_reg_neq by discriminate.
    rewrite get_set_reg_eq.
    rewrite HR0, HR1.
    symmetry. apply I32.rotl_rotr_sub.
Qed.

Theorem i32_rotr_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32Rotr wstate =
    Some (mkWasmState (VI32 (I32.rotr v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Rotr) astate = Some astate' /\
    get_reg astate' R0 = I32.rotr v1 v2.
Proof.
  (* Compiles to [ROR_reg R0 R0 R1] *)
  synth_binop_proof.
Qed.

(** ** I32 Comparison Operations (11 total) *)
(** These proofs claim result correspondence: the ARM result register
    contains the same value as the WASM comparison result.
    This requires tracing through CMP flag computation and conditional MOV.
    The proofs need detailed reasoning about flag_z, flag_n, flag_v, flag_c
    after CMP, which ties into the I32.eq/lts/ltu/etc definitions.
    These remain Admitted pending flag-correspondence lemmas. *)

Theorem i32_eqz_correct : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  get_reg astate R0 = v ->
  exec_wasm_instr I32Eqz wstate =
    Some (mkWasmState
            (VI32 (if I32.eq v I32.zero then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Eqz) astate = Some astate' /\
    get_reg astate' R0 = (if I32.eq v I32.zero then I32.one else I32.zero).
Proof. synth_cmp_unop_proof z_flag_sub_eq. Qed.

Theorem i32_eq_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32Eq wstate =
    Some (mkWasmState
            (VI32 (if I32.eq v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Eq) astate = Some astate' /\
    get_reg astate' R0 = (if I32.eq v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof z_flag_sub_eq. Qed.

Theorem i32_ne_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32Ne wstate =
    Some (mkWasmState
            (VI32 (if I32.ne v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Ne) astate = Some astate' /\
    get_reg astate' R0 = (if I32.ne v1 v2 then I32.one else I32.zero).
Proof.
  intros wstate astate v1 v2 stack' Hstack HR0 HR1 Hwasm.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1; simpl.
  rewrite <- flags_ne.
  destruct (compute_z_flag (I32.sub v1 v2));
  (eexists; split; [reflexivity | apply get_set_reg_eq]).
Qed.

Theorem i32_lts_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32LtS wstate =
    Some (mkWasmState
            (VI32 (if I32.lts v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32LtS) astate = Some astate' /\
    get_reg astate' R0 = (if I32.lts v1 v2 then I32.one else I32.zero).
Proof.
  intros wstate astate v1 v2 stack' Hstack HR0 HR1 Hwasm.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1; simpl.
  rewrite <- nv_flag_sub_lts.
  destruct (Bool.eqb (compute_n_flag (I32.sub v1 v2)) (compute_v_flag_sub v1 v2));
  (eexists; split; [reflexivity | apply get_set_reg_eq]).
Qed.

Theorem i32_ltu_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32LtU wstate =
    Some (mkWasmState
            (VI32 (if I32.ltu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32LtU) astate = Some astate' /\
    get_reg astate' R0 = (if I32.ltu v1 v2 then I32.one else I32.zero).
Proof.
  intros wstate astate v1 v2 stack' Hstack HR0 HR1 Hwasm.
  unfold compile_wasm_to_arm; simpl.
  rewrite HR0, HR1; simpl.
  rewrite <- flags_ltu.
  destruct (compute_c_flag_sub v1 v2);
  (eexists; split; [reflexivity | apply get_set_reg_eq]).
Qed.

Theorem i32_gts_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32GtS wstate =
    Some (mkWasmState
            (VI32 (if I32.gts v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32GtS) astate = Some astate' /\
    get_reg astate' R0 = (if I32.gts v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof flags_gts. Qed.

Theorem i32_gtu_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32GtU wstate =
    Some (mkWasmState
            (VI32 (if I32.gtu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32GtU) astate = Some astate' /\
    get_reg astate' R0 = (if I32.gtu v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof flags_gtu. Qed.

Theorem i32_les_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32LeS wstate =
    Some (mkWasmState
            (VI32 (if I32.les v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32LeS) astate = Some astate' /\
    get_reg astate' R0 = (if I32.les v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof flags_les. Qed.

Theorem i32_leu_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32LeU wstate =
    Some (mkWasmState
            (VI32 (if I32.leu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32LeU) astate = Some astate' /\
    get_reg astate' R0 = (if I32.leu v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof flags_leu. Qed.

Theorem i32_ges_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32GeS wstate =
    Some (mkWasmState
            (VI32 (if I32.ges v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32GeS) astate = Some astate' /\
    get_reg astate' R0 = (if I32.ges v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof flags_ges. Qed.

Theorem i32_geu_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32GeU wstate =
    Some (mkWasmState
            (VI32 (if I32.geu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32GeU) astate = Some astate' /\
    get_reg astate' R0 = (if I32.geu v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof flags_geu. Qed.

(** ** I32 Bit Manipulation (3 total) *)
(** CLZ/CTZ/POPCNT now use proper axiomatized semantics from I32.clz/rbit/popcnt *)

Theorem i32_clz_correct : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  get_reg astate R0 = v ->
  exec_wasm_instr I32Clz wstate =
    Some (mkWasmState (VI32 (I32.clz v) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Clz) astate = Some astate' /\
    get_reg astate' R0 = I32.clz v.
Proof.
  (* CLZ compiles to [CLZ R0 R0], ARM semantics: I32.clz (get_reg s R0) *)
  intros wstate astate v stack' Hstack HR0 Hwasm.
  unfold compile_wasm_to_arm.
  simpl.
  rewrite HR0.
  eexists. split.
  - reflexivity.
  - apply get_set_reg_eq.
Qed.

Theorem i32_ctz_correct : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  get_reg astate R0 = v ->
  exec_wasm_instr I32Ctz wstate =
    Some (mkWasmState (VI32 (I32.ctz v) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Ctz) astate = Some astate' /\
    get_reg astate' R0 = I32.ctz v.
Proof.
  (* CTZ compiles to [RBIT R0 R0; CLZ R0 R0] *)
  (* After RBIT: R0 = I32.rbit v *)
  (* After CLZ: R0 = I32.clz (I32.rbit v) = I32.ctz v (by clz_rbit axiom) *)
  intros wstate astate v stack' Hstack HR0 Hwasm.
  unfold compile_wasm_to_arm.
  simpl.
  rewrite HR0.
  eexists. split.
  - reflexivity.
  - rewrite get_set_reg_eq.
    apply I32.clz_rbit.
Qed.

Theorem i32_popcnt_correct : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  get_reg astate R0 = v ->
  exec_wasm_instr I32Popcnt wstate =
    Some (mkWasmState (VI32 (I32.popcnt v) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Popcnt) astate = Some astate' /\
    get_reg astate' R0 = I32.popcnt v.
Proof.
  (* POPCNT compiles to [POPCNT R0 R0], ARM semantics: I32.popcnt (get_reg s R0) *)
  intros wstate astate v stack' Hstack HR0 Hwasm.
  unfold compile_wasm_to_arm.
  simpl.
  rewrite HR0.
  eexists. split.
  - reflexivity.
  - apply get_set_reg_eq.
Qed.

(** ** Summary

    I32 theorems: 29 total — 29 Qed, 0 Admitted
    - Arithmetic: 7 Qed (Add, Sub, Mul, DivS, DivU, RemS, RemU — the four
      div/rem trap-guard proofs against the branch-taking exec_program_br,
      #73; DivS discharges the INT_MIN/-1 double guard)
    - Bitwise: 8 Qed (And, Or, Xor, Shl, ShrU, ShrS, Rotl, Rotr)
    - Comparison: 11 Qed (EQZ, EQ, NE, LtS, LtU, GtS, GtU, LeS, LeU, GeS, GeU)
    - Bit manipulation: 3 Qed (CLZ/CTZ/POPCNT using axiomatized I32.clz/ctz/popcnt)

    The 11 comparison proofs use flag-correspondence lemmas from ArmFlagLemmas.v.
    The signed comparison proofs (LtS, GtS, LeS, GeS) depend on the nv_flag_sub_lts
    axiom (N≠V ↔ signed less-than), a standard ARM architecture property.
    The rotl proof uses the rotl_rotr_sub axiom connecting rotl to rotr via RSB.
*)
