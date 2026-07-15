(** * VCR-SEL-001 increments 1+2+3+4: Rocq obligations of the wired selector rule table

    One universally-quantified T1 theorem per rule in the checked-in DSL table
    [crates/synth-synthesis/src/sel_dsl/mod.rs] (RULES), naming 1:1:

      Rust rule [rule_i32_add]  <->  [Definition rule_i32_add]
                                <->  [Theorem rule_i32_add_correct]

    VCR-ISA-001 (#667) "generate, don't mirror": each [Definition rule_X]
    below is a RE-EXPORT of the GENERATED [Gen.rule_X]
    ([VcrSelRulesGenerated.v], emitted by
    [crate::sel_dsl::generate_rocq_lowering_source] from the SAME shipped
    RULES table that produces the Rust lowering [sel_dsl/generated.rs]).
    There is no hand-written copy of the instruction sequences left in this
    file — the generated file is the single source for the 40 covered ops,
    so the model cannot drift from the shipped selector (the #682
    vacuous-proof failure mode). If the shipped table changes, regeneration
    changes [Gen.rule_X], and the matching correctness theorem below stops
    compiling: the 40 Qed themselves are the divergence gate (strictly
    stronger than the retired [VcrSelRulesGenCheck.v] reflexivity check,
    which could only compare against a hand-written mirror).
    The theorems prove the T1 bound carried over from the pilot
    ([VcrSelPilot.v], the 2026-06-20 go/abandon measurement): the emitted ARM
    sequence computes the op's I32 result in [rd] for EVERY register
    assignment satisfying the rule's side conditions — not full WASM
    refinement (that upgrade is VCR-WASM-001/VCR-ISA-001 territory).

    COVERAGE GATE: a rule without its Qed here cannot merge —
    [//coq:vcr_sel_rules_coverage] (part of the [//coq:verify_proofs] suite)
    checks [coq/vcr_sel_rules.manifest] (pinned to the Rust RULES table by a
    cargo test) against this file and rejects unfinished (non-Qed) proofs.

    Tier A (no-scratch single-instruction: add/sub/mul/and/or/xor, and since
    increment 2 the register shifts shl/shr_s/shr_u + rotr) discharges with
    [synth_binop_proof_poly] — verbatim [synth_binop_proof] (Tactics.v)
    modulo the lowering-unfold target, exactly as the pilot measured (6/6).
    Tier B ([rule_i32_rotl], RSB scratch + ROR) carries the explicit
    [rs <> rn] scratch non-aliasing hypothesis — the side condition the DSL
    records in the rule table and the generated Rust enforces at runtime.

    INCREMENT 2 also adds the ten i32 comparisons (the Rust CMP+SetCond
    shape; [ArmOp::SetCond rd cond] is modeled here — following the
    established Compilation.v convention — as [MOV rd #0; MOVcc rd #1], so
    each rule is the three-instruction flat program
    [CMP rn (Reg rm); MOV rd (Imm 0); MOVcc rd (Imm 1)]). Comparisons need
    NO aliasing side conditions: CMP latches NZCV into the state's flags
    before [rd] is written, so the universal quantifier admits every
    rd/rn/rm aliasing. Discharge is [synth_cmp_binop_proof] (Tactics.v)
    generalized to universally-quantified registers
    ([synth_cmp_binop_proof_poly] below), with the same three manual
    variants (ne / lt_s / lt_u) the fixed-register proofs in
    CorrectnessI32.v use, parameterized over registers verbatim.

    INCREMENT 3 extends the DSL into the i64 register-pair family — the
    two-instruction pair shapes (ADDS+ADC / SUBS+SBC / ANDx2 / ORRx2 /
    EORx2) plus the single-instruction [I64SetCondZ] shape for i64.eqz.
    An i64 value lives in a (lo, hi) register pair, so each pair rule is
    quantified over SIX registers and its theorem proves BOTH result
    words. The pair shapes are where register generalization earns its
    keep: the low-half instruction writes [rdlo] before the high-half
    instruction reads [rnhi]/[rmhi], so a rule that could not state
    "the destination must not be clobbered before use" would be exactly
    how #632-class bugs happen. Three explicit aliasing hypotheses per
    pair rule (carried as [SideCondition::NotAlias] in the Rust table and
    enforced Ok-or-Err in the generated lowering):

      - [rdhi <> rdlo] — the high write must not destroy the low result;
      - [rdlo <> rnhi] and [rdlo <> rmhi] — the low write must not
        clobber a high-half operand the second instruction still reads.

    In-place lowering ([rdlo = rnlo], [rdhi = rnhi] — what
    [select_default]'s fixed R0:R1 += R2:R3 arms emit) satisfies all
    three, so one Qed per rule covers both selectors' assignments.
    Discharge: the value-level carry/borrow lemmas already proven for the
    fixed-register ancestors ([i64_add_via_adds_adc] /
    [i64_sub_via_subs_sbc] in ArmFlagLemmas.v; the halves-distribute
    combine lemmas in CorrectnessI64.v), applied under the generalized
    register bookkeeping — no new axiom. The theorem shape follows the
    CorrectnessI64.v ancestors: a value-level correspondence between the
    WASM-spec function ([I64.add] etc. on [combine_i32]-combined
    operands) and the ARM execution result, both halves pinned. *)

From Stdlib Require Import List.
From Stdlib Require Import Lia ZArith Znumtheory.
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
Require Import Synth.ARM.ArmFlagLemmas.
(* Increment 3: the halves-distribute combine lemmas
   ({and,or,xor}_{lo,hi}_combine) proven for the fixed-register i64
   bitwise ancestors live in CorrectnessI64.v — imported, not duplicated. *)
Require Import Synth.Synth.CorrectnessI64.
(* VCR-ISA-001 (#667): the GENERATED lowerings — the single source the
   [Definition rule_X := Gen.rule_X] re-exports below bind against. *)
Require Import Synth.Synth.VcrSelRulesGenerated.
Import ListNotations.

Open Scope Z_scope.

(** ** The rule lowerings — RE-EXPORTED from the generated [Gen] module
    ([VcrSelRulesGenerated.v]), 1:1 with sel_dsl::RULES / sel_dsl::generated.
    Every [rule_X] is definitionally [Gen.rule_X]; the sequences themselves
    are documented in the section comments below and live ONLY in the
    generated file. *)

Definition rule_i32_add := Gen.rule_i32_add.
Definition rule_i32_sub := Gen.rule_i32_sub.
Definition rule_i32_mul := Gen.rule_i32_mul.
Definition rule_i32_and := Gen.rule_i32_and.
Definition rule_i32_or  := Gen.rule_i32_or.
Definition rule_i32_xor := Gen.rule_i32_xor.

(** Tier B: two instructions through a scratch register [rs] — rotate left by
    [rm] = rotate right by (32 - [rm]). [RSB] writes the scratch in
    instruction 1 before [ROR] reads the value register in instruction 2, so
    [rs] must not alias [rn]: the side condition the rule table carries. *)
Definition rule_i32_rotl := Gen.rule_i32_rotl.

(** ** Increment 2: i32 register shifts + rotr.

    #682 SOUNDNESS FIX: the single-instruction shift rules were WRONG on
    hardware — ARMv7-M register shifts consume Rm[7:0] and yield 0 (LSL/LSR)
    or the sign (ASR) for amounts >= 32, while WASM requires amount mod 32.
    The model's LSL_reg/LSR_reg/ASR_reg use I32.shl/shru/shrs, which mask
    mod 32 INTERNALLY (WASM-like) — so the old Qeds were vacuous against
    real hardware (the exact divergence SailArmBridge.v documents as gaps
    6-7). The rules now materialize the mask explicitly:
    [AND rs rm #31; shift rd rn rs] — correct under BOTH the current model
    semantics and real Rm[7:0] hardware. The scratch [rs] carries the
    [rs <> rn] non-aliasing side condition (rotl pattern); the Rust side
    passes R12 (never allocatable, #212), so the condition always holds.
    ROR is exempt: rotation is cyclic, so Rm[7:0] mod 32 = WASM semantics. *)

Definition rule_i32_shl   := Gen.rule_i32_shl.
Definition rule_i32_shr_s := Gen.rule_i32_shr_s.
Definition rule_i32_shr_u := Gen.rule_i32_shr_u.
Definition rule_i32_rotr  := Gen.rule_i32_rotr.

(** The mask identity: ANDing the amount with 31 does not change the
    mod-32 shift the I32 semantics performs. Z-level plumbing first. *)
Lemma land31_mod32 : forall a : Z, (Z.land a 31) mod 32 = a mod 32.
Proof.
  intros a. change 31 with (Z.ones 5).
  rewrite Z.land_ones by lia.
  change (2 ^ 5) with 32. apply Z.mod_mod. lia.
Qed.

Lemma mod_modulus_mod32 : forall a : Z, (a mod 4294967296) mod 32 = a mod 32.
Proof.
  intros a.
  symmetry. apply Zmod_div_mod; [lia | lia | exists 134217728; reflexivity].
Qed.

(** ** Increment 2: i32 comparisons — the Rust rule emits
    [Cmp {rn, Reg(rm)}; SetCond {rd, cond}]; per the established
    Compilation.v convention the [SetCond] pseudo-op is modeled as
    [MOV rd #0; MOVcc rd #1] over the flags CMP latched. No aliasing side
    conditions: the flags transfer is through NZCV, not a register, so the
    theorems below hold for EVERY rd/rn/rm assignment. *)

Definition rule_i32_eq   := Gen.rule_i32_eq.
Definition rule_i32_ne   := Gen.rule_i32_ne.
Definition rule_i32_lt_s := Gen.rule_i32_lt_s.
Definition rule_i32_lt_u := Gen.rule_i32_lt_u.
Definition rule_i32_gt_s := Gen.rule_i32_gt_s.
Definition rule_i32_gt_u := Gen.rule_i32_gt_u.
Definition rule_i32_le_s := Gen.rule_i32_le_s.
Definition rule_i32_le_u := Gen.rule_i32_le_u.
Definition rule_i32_ge_s := Gen.rule_i32_ge_s.
Definition rule_i32_ge_u := Gen.rule_i32_ge_u.

(** ** The discharge tactic — verbatim [synth_binop_proof] (Tactics.v) modulo
    the lowering-unfold target, as measured by the pilot. *)
Ltac synth_binop_proof_poly :=
  intros wstate astate v1 v2 stack' rd rn rm Hstack HR0 HR1 Hwasm;
  unfold rule_i32_add, rule_i32_sub, rule_i32_mul,
         rule_i32_and, rule_i32_or, rule_i32_xor,
         rule_i32_shl, rule_i32_shr_s, rule_i32_shr_u, rule_i32_rotr,
         Gen.rule_i32_add, Gen.rule_i32_sub, Gen.rule_i32_mul,
         Gen.rule_i32_and, Gen.rule_i32_or, Gen.rule_i32_xor,
         Gen.rule_i32_shl, Gen.rule_i32_shr_s, Gen.rule_i32_shr_u,
         Gen.rule_i32_rotr;
  unfold exec_program, exec_instr;
  simpl;
  rewrite HR0, HR1;
  eexists; split;
  [ reflexivity
  | simpl; apply get_set_reg_eq ].

(** ** Tier-A theorems — quantified over ARBITRARY rd rn rm (no aliasing
    side conditions: the universal quantifier admits every aliasing, including
    the in-place rd = rn reuse the selector actually emits). *)

Theorem rule_i32_add_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Add wstate =
    Some (mkWasmState (VI32 (I32.add v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_add rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.add v1 v2.
Proof. synth_binop_proof_poly. Qed.

Theorem rule_i32_sub_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Sub wstate =
    Some (mkWasmState (VI32 (I32.sub v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_sub rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.sub v1 v2.
Proof. synth_binop_proof_poly. Qed.

Theorem rule_i32_mul_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Mul wstate =
    Some (mkWasmState (VI32 (I32.mul v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_mul rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.mul v1 v2.
Proof. synth_binop_proof_poly. Qed.

Theorem rule_i32_and_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32And wstate =
    Some (mkWasmState (VI32 (I32.and v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_and rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.and v1 v2.
Proof. synth_binop_proof_poly. Qed.

Theorem rule_i32_or_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Or wstate =
    Some (mkWasmState (VI32 (I32.or v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_or rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.or v1 v2.
Proof. synth_binop_proof_poly. Qed.

Theorem rule_i32_xor_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Xor wstate =
    Some (mkWasmState (VI32 (I32.xor v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_xor rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.xor v1 v2.
Proof. synth_binop_proof_poly. Qed.

(** ** Tier-B theorem — with the explicit [rs <> rn] hypothesis the rule
    table carries as [SideCondition::NotAlias(Rs, Rn)] and the generated Rust
    enforces (Ok-or-Err). Stepped proof (the single-instruction tactic cannot
    close a two-instruction sequence), same structure as the pilot's. *)

Theorem rule_i32_rotl_correct : forall wstate astate v1 v2 stack' rd rn rm rs,
  rs <> rn ->        (* scratch must not alias the value register *)
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Rotl wstate =
    Some (mkWasmState (VI32 (I32.rotl v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_rotl rd rn rm rs) astate = Some astate' /\
    get_reg astate' rd = I32.rotl v1 v2.
Proof.
  intros wstate astate v1 v2 stack' rd rn rm rs Hne Hstack HR0 HR1 Hwasm.
  unfold rule_i32_rotl, Gen.rule_i32_rotl.
  set (s1 := set_reg astate rs (I32.sub (I32.repr 32) (get_reg astate rm))).
  set (s2 := set_reg s1 rd (I32.rotr (get_reg s1 rn) (get_reg s1 rs))).
  exists s2. split.
  - subst s2 s1. simpl. reflexivity.
  - subst s2. rewrite get_set_reg_eq.
    subst s1. rewrite get_set_reg_neq by exact Hne.
    rewrite get_set_reg_eq.
    rewrite HR0, HR1.
    symmetry. apply I32.rotl_rotr_sub.
Qed.

(** ** Increment-2 tier-A theorems: register shifts + rotr — discharged by
    the SAME [synth_binop_proof_poly], exactly like the ALU six (the shift
    rules are single-instruction no-scratch shapes; their fixed-register
    ancestors in CorrectnessI32.v already close with [synth_binop_proof]). *)

Theorem rule_i32_shl_correct : forall wstate astate v1 v2 stack' rd rn rm rs,
  rs <> rn ->        (* mask scratch must not alias the value register *)
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Shl wstate =
    Some (mkWasmState (VI32 (I32.shl v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_shl rd rn rm rs) astate = Some astate' /\
    get_reg astate' rd = I32.shl v1 v2.
Proof.
  intros wstate astate v1 v2 stack' rd rn rm rs Hne Hstack HR0 HR1 Hwasm.
  unfold rule_i32_shl, Gen.rule_i32_shl.
  set (s1 := set_reg astate rs (I32.and (get_reg astate rm) (I32.repr 31))).
  set (s2 := set_reg s1 rd (I32.shl (get_reg s1 rn) (get_reg s1 rs))).
  exists s2. split.
  - subst s2 s1. simpl. reflexivity.
  - subst s2. rewrite get_set_reg_eq.
    subst s1. rewrite get_set_reg_neq by exact Hne.
    rewrite get_set_reg_eq.
    rewrite HR0, HR1.
    unfold I32.shl, I32.and, I32.repr, I32.unsigned, I32.modulus.
    change (31 mod 4294967296) with 31.
    rewrite !mod_modulus_mod32, land31_mod32.
    reflexivity.
Qed.

Theorem rule_i32_shr_s_correct : forall wstate astate v1 v2 stack' rd rn rm rs,
  rs <> rn ->        (* mask scratch must not alias the value register *)
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32ShrS wstate =
    Some (mkWasmState (VI32 (I32.shrs v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_shr_s rd rn rm rs) astate = Some astate' /\
    get_reg astate' rd = I32.shrs v1 v2.
Proof.
  intros wstate astate v1 v2 stack' rd rn rm rs Hne Hstack HR0 HR1 Hwasm.
  unfold rule_i32_shr_s, Gen.rule_i32_shr_s.
  set (s1 := set_reg astate rs (I32.and (get_reg astate rm) (I32.repr 31))).
  set (s2 := set_reg s1 rd (I32.shrs (get_reg s1 rn) (get_reg s1 rs))).
  exists s2. split.
  - subst s2 s1. simpl. reflexivity.
  - subst s2. rewrite get_set_reg_eq.
    subst s1. rewrite get_set_reg_neq by exact Hne.
    rewrite get_set_reg_eq.
    rewrite HR0, HR1.
    unfold I32.shrs, I32.and, I32.repr, I32.unsigned, I32.modulus.
    change (31 mod 4294967296) with 31.
    rewrite !mod_modulus_mod32, land31_mod32.
    reflexivity.
Qed.

Theorem rule_i32_shr_u_correct : forall wstate astate v1 v2 stack' rd rn rm rs,
  rs <> rn ->        (* mask scratch must not alias the value register *)
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32ShrU wstate =
    Some (mkWasmState (VI32 (I32.shru v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_shr_u rd rn rm rs) astate = Some astate' /\
    get_reg astate' rd = I32.shru v1 v2.
Proof.
  intros wstate astate v1 v2 stack' rd rn rm rs Hne Hstack HR0 HR1 Hwasm.
  unfold rule_i32_shr_u, Gen.rule_i32_shr_u.
  set (s1 := set_reg astate rs (I32.and (get_reg astate rm) (I32.repr 31))).
  set (s2 := set_reg s1 rd (I32.shru (get_reg s1 rn) (get_reg s1 rs))).
  exists s2. split.
  - subst s2 s1. simpl. reflexivity.
  - subst s2. rewrite get_set_reg_eq.
    subst s1. rewrite get_set_reg_neq by exact Hne.
    rewrite get_set_reg_eq.
    rewrite HR0, HR1.
    unfold I32.shru, I32.and, I32.repr, I32.unsigned, I32.modulus.
    change (31 mod 4294967296) with 31.
    rewrite !mod_modulus_mod32, land31_mod32.
    reflexivity.
Qed.

Theorem rule_i32_rotr_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Rotr wstate =
    Some (mkWasmState (VI32 (I32.rotr v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_rotr rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.rotr v1 v2.
Proof. synth_binop_proof_poly. Qed.

(** ** Increment-2 comparison discharge tactic — verbatim
    [synth_cmp_binop_proof] (Tactics.v) modulo (a) the three extra register
    binders and (b) the lowering-unfold target, mirroring how
    [synth_binop_proof_poly] generalizes [synth_binop_proof]. *)
Ltac synth_cmp_binop_proof_poly flag_lemma :=
  intros wstate astate v1 v2 stack' rd rn rm Hstack HR0 HR1 Hwasm;
  unfold rule_i32_eq, rule_i32_ne, rule_i32_lt_s, rule_i32_lt_u,
         rule_i32_gt_s, rule_i32_gt_u, rule_i32_le_s, rule_i32_le_u,
         rule_i32_ge_s, rule_i32_ge_u,
         Gen.rule_i32_eq, Gen.rule_i32_ne, Gen.rule_i32_lt_s,
         Gen.rule_i32_lt_u, Gen.rule_i32_gt_s, Gen.rule_i32_gt_u,
         Gen.rule_i32_le_s, Gen.rule_i32_le_u, Gen.rule_i32_ge_s,
         Gen.rule_i32_ge_u;
  simpl;
  rewrite HR0, HR1; simpl;
  rewrite flag_lemma;
  destruct (_ v1 v2);
  (eexists; split; [reflexivity | apply get_set_reg_eq]).

(** ** Increment-2 comparison theorems — quantified over ARBITRARY rd rn rm
    (no side conditions: CMP latches NZCV before rd is written, so every
    aliasing is admitted). Seven close with the poly tactic + the same flag
    lemma their fixed-register ancestors use; ne / lt_s / lt_u use the same
    manual scripts as CorrectnessI32.v, register-generalized verbatim. *)

Theorem rule_i32_eq_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Eq wstate =
    Some (mkWasmState
            (VI32 (if I32.eq v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_eq rd rn rm) astate = Some astate' /\
    get_reg astate' rd = (if I32.eq v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof_poly z_flag_sub_eq. Qed.

Theorem rule_i32_ne_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Ne wstate =
    Some (mkWasmState
            (VI32 (if I32.ne v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_ne rd rn rm) astate = Some astate' /\
    get_reg astate' rd = (if I32.ne v1 v2 then I32.one else I32.zero).
Proof.
  intros wstate astate v1 v2 stack' rd rn rm Hstack HR0 HR1 Hwasm.
  unfold rule_i32_ne, Gen.rule_i32_ne; simpl.
  rewrite HR0, HR1; simpl.
  rewrite <- flags_ne.
  destruct (compute_z_flag (I32.sub v1 v2));
  (eexists; split; [reflexivity | apply get_set_reg_eq]).
Qed.

Theorem rule_i32_lt_s_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32LtS wstate =
    Some (mkWasmState
            (VI32 (if I32.lts v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_lt_s rd rn rm) astate = Some astate' /\
    get_reg astate' rd = (if I32.lts v1 v2 then I32.one else I32.zero).
Proof.
  intros wstate astate v1 v2 stack' rd rn rm Hstack HR0 HR1 Hwasm.
  unfold rule_i32_lt_s, Gen.rule_i32_lt_s; simpl.
  rewrite HR0, HR1; simpl.
  rewrite <- nv_flag_sub_lts.
  destruct (Bool.eqb (compute_n_flag (I32.sub v1 v2)) (compute_v_flag_sub v1 v2));
  (eexists; split; [reflexivity | apply get_set_reg_eq]).
Qed.

Theorem rule_i32_lt_u_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32LtU wstate =
    Some (mkWasmState
            (VI32 (if I32.ltu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_lt_u rd rn rm) astate = Some astate' /\
    get_reg astate' rd = (if I32.ltu v1 v2 then I32.one else I32.zero).
Proof.
  intros wstate astate v1 v2 stack' rd rn rm Hstack HR0 HR1 Hwasm.
  unfold rule_i32_lt_u, Gen.rule_i32_lt_u; simpl.
  rewrite HR0, HR1; simpl.
  rewrite <- flags_ltu.
  destruct (compute_c_flag_sub v1 v2);
  (eexists; split; [reflexivity | apply get_set_reg_eq]).
Qed.

Theorem rule_i32_gt_s_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32GtS wstate =
    Some (mkWasmState
            (VI32 (if I32.gts v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_gt_s rd rn rm) astate = Some astate' /\
    get_reg astate' rd = (if I32.gts v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof_poly flags_gts. Qed.

Theorem rule_i32_gt_u_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32GtU wstate =
    Some (mkWasmState
            (VI32 (if I32.gtu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_gt_u rd rn rm) astate = Some astate' /\
    get_reg astate' rd = (if I32.gtu v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof_poly flags_gtu. Qed.

Theorem rule_i32_le_s_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32LeS wstate =
    Some (mkWasmState
            (VI32 (if I32.les v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_le_s rd rn rm) astate = Some astate' /\
    get_reg astate' rd = (if I32.les v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof_poly flags_les. Qed.

Theorem rule_i32_le_u_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32LeU wstate =
    Some (mkWasmState
            (VI32 (if I32.leu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_le_u rd rn rm) astate = Some astate' /\
    get_reg astate' rd = (if I32.leu v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof_poly flags_leu. Qed.

Theorem rule_i32_ge_s_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32GeS wstate =
    Some (mkWasmState
            (VI32 (if I32.ges v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_ge_s rd rn rm) astate = Some astate' /\
    get_reg astate' rd = (if I32.ges v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof_poly flags_ges. Qed.

Theorem rule_i32_ge_u_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32GeU wstate =
    Some (mkWasmState
            (VI32 (if I32.geu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_ge_u rd rn rm) astate = Some astate' /\
    get_reg astate' rd = (if I32.geu v1 v2 then I32.one else I32.zero).
Proof. synth_cmp_binop_proof_poly flags_geu. Qed.

(** ** Increment 3: the i64 register-pair rule lowerings — 1:1 with
    sel_dsl::RULES / sel_dsl::generated. An i64 value is a (lo, hi)
    register pair; operand 1 is (rnlo, rnhi), operand 2 is (rmlo, rmhi),
    the result pair is (rdlo, rdhi). *)

Definition rule_i64_add := Gen.rule_i64_add.
Definition rule_i64_sub := Gen.rule_i64_sub.
Definition rule_i64_and := Gen.rule_i64_and.
Definition rule_i64_or  := Gen.rule_i64_or.
Definition rule_i64_xor := Gen.rule_i64_xor.

(** i64.eqz — unary, single [I64SetCondZ] pseudo-op (the SetCondZ shape);
    the 0/1 result is a single i32 register, so no pair side conditions. *)
Definition rule_i64_eqz := Gen.rule_i64_eqz.

(** ** Increment-3 discharge tactics.

    [synth_i64_carry_pair_proof_poly] — the flags-coupled pair shapes
    (ADDS+ADC / SUBS+SBC): verbatim the stepped structure of the
    fixed-register [i64_add_correct] / [i64_sub_correct] proofs
    (CorrectnessI64.v) modulo (a) the six register binders, (b) the
    lowering-unfold target, and (c) the three aliasing hypotheses standing
    in for what was [discriminate] on concrete registers. Parameterized by
    the ArmFlagLemmas.v carry/borrow-propagation lemma.

    [synth_i64_bitwise_pair_proof_poly] — the flag-free parallel-halves
    shapes (ANDx2/ORRx2/EORx2), parameterized by the lo/hi
    halves-distribute lemmas from CorrectnessI64.v. *)

Ltac synth_i64_carry_pair_proof_poly carry_lemma :=
  intros astate lo1 hi1 lo2 hi2 rdlo rdhi rnlo rnhi rmlo rmhi
         Hdd Hdnh Hdmh HR0 HR1 HR2 HR3;
  unfold rule_i64_add, rule_i64_sub, Gen.rule_i64_add, Gen.rule_i64_sub;
  cbn [exec_program exec_instr eval_operand2];
  rewrite flags_set_flags_set_reg;
  rewrite flag_c_update_flags_arith;
  let Hpair := fresh "Hpair" in
  pose proof (carry_lemma lo1 hi1 lo2 hi2) as Hpair;
  let Hlo := fresh "Hlo" in
  let Hhi := fresh "Hhi" in
  destruct Hpair as [Hlo Hhi];
  eexists; split;
  [ reflexivity
  | split;
    [ (* lo word: the high-half write must not have destroyed it. *)
      rewrite (get_set_reg_neq _ rdhi rdlo) by exact Hdd;
      rewrite get_reg_set_flags;
      rewrite get_set_reg_eq;
      rewrite HR0, HR2; exact Hlo
    | (* hi word: the high-half instruction read its operands from the
         post-low-half state, where rdlo was already written. *)
      rewrite get_set_reg_eq;
      rewrite !get_reg_set_flags;
      rewrite (get_set_reg_neq astate rdlo rnhi) by exact Hdnh;
      rewrite (get_set_reg_neq astate rdlo rmhi) by exact Hdmh;
      rewrite HR0, HR1, HR2, HR3; exact Hhi ] ].

Ltac synth_i64_bitwise_pair_proof_poly lo_lemma hi_lemma :=
  intros astate lo1 hi1 lo2 hi2 rdlo rdhi rnlo rnhi rmlo rmhi
         Hdd Hdnh Hdmh HR0 HR1 HR2 HR3;
  unfold rule_i64_and, rule_i64_or, rule_i64_xor,
         Gen.rule_i64_and, Gen.rule_i64_or, Gen.rule_i64_xor;
  cbn [exec_program exec_instr eval_operand2];
  eexists; split;
  [ reflexivity
  | split;
    [ rewrite (get_set_reg_neq _ rdhi rdlo) by exact Hdd;
      rewrite get_set_reg_eq;
      rewrite HR0, HR2; apply lo_lemma
    | rewrite get_set_reg_eq;
      rewrite (get_set_reg_neq astate rdlo rnhi) by exact Hdnh;
      rewrite (get_set_reg_neq astate rdlo rmhi) by exact Hdmh;
      rewrite HR1, HR3; apply hi_lemma ] ].

(** ** Increment-3 pair theorems — quantified over all SIX registers,
    under the three explicit aliasing hypotheses the rule table carries.
    Pair-result T1: BOTH words of the result are proven. *)

Theorem rule_i64_add_correct :
  forall astate lo1 hi1 lo2 hi2 rdlo rdhi rnlo rnhi rmlo rmhi,
  rdhi <> rdlo ->    (* high write must not destroy the low result *)
  rdlo <> rnhi ->    (* low write must not clobber operand-1's high half *)
  rdlo <> rmhi ->    (* low write must not clobber operand-2's high half *)
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_add rdlo rdhi rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rdlo = lo_of_i64 (I64.add (combine_i32 lo1 hi1)
                                              (combine_i32 lo2 hi2)) /\
    get_reg astate' rdhi = hi_of_i64 (I64.add (combine_i32 lo1 hi1)
                                              (combine_i32 lo2 hi2)).
Proof. synth_i64_carry_pair_proof_poly i64_add_via_adds_adc. Qed.

Theorem rule_i64_sub_correct :
  forall astate lo1 hi1 lo2 hi2 rdlo rdhi rnlo rnhi rmlo rmhi,
  rdhi <> rdlo ->
  rdlo <> rnhi ->
  rdlo <> rmhi ->
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_sub rdlo rdhi rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rdlo = lo_of_i64 (I64.sub (combine_i32 lo1 hi1)
                                              (combine_i32 lo2 hi2)) /\
    get_reg astate' rdhi = hi_of_i64 (I64.sub (combine_i32 lo1 hi1)
                                              (combine_i32 lo2 hi2)).
Proof. synth_i64_carry_pair_proof_poly i64_sub_via_subs_sbc. Qed.

Theorem rule_i64_and_correct :
  forall astate lo1 hi1 lo2 hi2 rdlo rdhi rnlo rnhi rmlo rmhi,
  rdhi <> rdlo ->
  rdlo <> rnhi ->
  rdlo <> rmhi ->
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_and rdlo rdhi rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rdlo = lo_of_i64 (I64.and (combine_i32 lo1 hi1)
                                              (combine_i32 lo2 hi2)) /\
    get_reg astate' rdhi = hi_of_i64 (I64.and (combine_i32 lo1 hi1)
                                              (combine_i32 lo2 hi2)).
Proof. synth_i64_bitwise_pair_proof_poly and_lo_combine and_hi_combine. Qed.

Theorem rule_i64_or_correct :
  forall astate lo1 hi1 lo2 hi2 rdlo rdhi rnlo rnhi rmlo rmhi,
  rdhi <> rdlo ->
  rdlo <> rnhi ->
  rdlo <> rmhi ->
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_or rdlo rdhi rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rdlo = lo_of_i64 (I64.or (combine_i32 lo1 hi1)
                                             (combine_i32 lo2 hi2)) /\
    get_reg astate' rdhi = hi_of_i64 (I64.or (combine_i32 lo1 hi1)
                                             (combine_i32 lo2 hi2)).
Proof. synth_i64_bitwise_pair_proof_poly or_lo_combine or_hi_combine. Qed.

Theorem rule_i64_xor_correct :
  forall astate lo1 hi1 lo2 hi2 rdlo rdhi rnlo rnhi rmlo rmhi,
  rdhi <> rdlo ->
  rdlo <> rnhi ->
  rdlo <> rmhi ->
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_xor rdlo rdhi rnlo rnhi rmlo rmhi) astate
      = Some astate' /\
    get_reg astate' rdlo = lo_of_i64 (I64.xor (combine_i32 lo1 hi1)
                                              (combine_i32 lo2 hi2)) /\
    get_reg astate' rdhi = hi_of_i64 (I64.xor (combine_i32 lo1 hi1)
                                              (combine_i32 lo2 hi2)).
Proof. synth_i64_bitwise_pair_proof_poly xor_lo_combine xor_hi_combine. Qed.

(** i64.eqz — the SetCondZ shape. Single instruction, no pair side
    conditions (the pseudo-op reads both operand halves before writing
    [rd], so every rd/rnlo/rnhi aliasing is admitted). Value-level T1 via
    the [i64_setcondz_bits_spec] axiom, exactly like the fixed-register
    bit-manipulation ancestors (i64_clz/ctz/popcnt in CorrectnessI64.v). *)
Theorem rule_i64_eqz_correct : forall astate lo hi rd rnlo rnhi,
  get_reg astate rnlo = lo ->
  get_reg astate rnhi = hi ->
  exists astate',
    exec_program (rule_i64_eqz rd rnlo rnhi) astate = Some astate' /\
    get_reg astate' rd =
      (if I64.eq (combine_i32 lo hi) I64.zero then I32.one else I32.zero).
Proof.
  intros astate lo hi rd rnlo rnhi HR0 HR1.
  unfold rule_i64_eqz, Gen.rule_i64_eqz; simpl.
  rewrite HR0, HR1.
  rewrite i64_setcondz_bits_spec.
  eexists. split; [reflexivity | apply get_set_reg_eq].
Qed.

(** ** Increment 4: scratch-using and multi-instruction shapes + the binary
    [I64SetCond] comparison family.

    i32 bit-manipulation:

    - [rule_i32_clz] — single [CLZ] (tier A, unary);
    - [rule_i32_ctz] — the TWO-instruction [RBIT rd rm; CLZ rd rd] shape
      with the scratch=dest trick: instruction 1 writes the bit-reversed
      value into [rd] itself, instruction 2 reads it back — NO extra
      scratch register and NO aliasing side condition (every rd/rm
      aliasing is admitted: RBIT reads [rm] before writing [rd], and the
      second instruction only reads [rd]). Stepped proof closing with the
      [I32.clz_rbit] axiom, exactly like the fixed-register ancestor
      ([i32_ctz_correct], CorrectnessI32.v), register-generalized;
    - [rule_i32_popcnt] — HONEST TIER NOTE: at the [ArmOp] level the
      selector emits a single [Popcnt] pseudo-op, which is what the rule
      mirrors and what this file proves (against the axiomatized
      [I32.popcnt], like the ancestors). The encoder's shift-and-add
      expansion BELOW the ArmOp boundary (where the #632 clobber lived)
      is not modeled here — same pseudo-op-tier honesty as [i64.eqz] and
      the [I64SetCond] family below.

    The binary i64 comparison family ([rule_i64_eq] .. [rule_i64_ge_u]) —
    the shape #615 re-implemented on A32 and where cond-mapping bugs
    live. Both selectors emit ONE [ArmOp::I64SetCond] pseudo-op per
    comparison; the rules mirror that pseudo-op with the condition the
    hand-written arms choose (LO=Cond_CC, HS=Cond_CS), and each theorem
    discharges against the [i64_setcond_bits_spec] axiom — the
    register-generalized form of the fixed-register ancestors in
    CorrectnessI64Comparisons.v. No side conditions: the pseudo-op reads
    all four operand halves before writing [rd], so every aliasing is
    admitted.

    WHAT THE FLAT EXECUTOR CANNOT EXPRESS (the honest bound): the
    encoder expands [I64SetCond] to the dual-precision flags-chain
    [CMP lo,lo; SBCS rd,hi,hi; MOVcc] (ordered conditions, with the
    GT/LE/HI/LS operand swap) or [CMP lo,lo; CMPEQ hi,hi; MOVcc]
    (EQ/NE). Verifying THAT expansion (rather than the pseudo-op) needs
    three things the flat model lacks today: (a) a flag-SETTING SBC
    ([SBCS] — the model's [SBC] reads C but writes no flags), (b)
    conditionally-executed flags-writers ([CMPEQ] — the model's only
    conditional forms are the register-writing [MOVcc] family), and (c)
    three-operand borrow-aware C/V flag helpers ([compute_c_flag_sub] /
    [compute_v_flag_sub] are two-operand). That is the same executor gap
    the VCR-ISA-001 spike hit with [BCondOffset] (a no-op in the flat
    executor): pseudo-op-tier proofs are the honest ceiling until the
    Sail-generated model lands. Documented in
    docs/design/vcr-sel-001-increment-4.md. *)

Definition rule_i32_clz    := Gen.rule_i32_clz.
Definition rule_i32_ctz    := Gen.rule_i32_ctz.
Definition rule_i32_popcnt := Gen.rule_i32_popcnt.

(** The binary I64SetCond comparison rules — 1:1 with the Rust table.
    Condition mapping is the hand-written arms' (and Compilation.v's):
    lt_u -> Cond_CC (LO), gt_u -> Cond_HI, le_u -> Cond_LS,
    ge_u -> Cond_CS (HS). *)
Definition rule_i64_eq   := Gen.rule_i64_eq.
Definition rule_i64_ne   := Gen.rule_i64_ne.
Definition rule_i64_lt_s := Gen.rule_i64_lt_s.
Definition rule_i64_lt_u := Gen.rule_i64_lt_u.
Definition rule_i64_gt_s := Gen.rule_i64_gt_s.
Definition rule_i64_gt_u := Gen.rule_i64_gt_u.
Definition rule_i64_le_s := Gen.rule_i64_le_s.
Definition rule_i64_le_u := Gen.rule_i64_le_u.
Definition rule_i64_ge_s := Gen.rule_i64_ge_s.
Definition rule_i64_ge_u := Gen.rule_i64_ge_u.

(** ** Increment-4 discharge tactics.

    [synth_unop_proof_poly] — verbatim [synth_unop_proof] (Tactics.v)
    modulo the two register binders and the lowering-unfold target,
    mirroring how [synth_binop_proof_poly] generalizes
    [synth_binop_proof]. Closes the single-instruction unary shapes
    (clz, popcnt).

    [synth_i64_setcond_proof_poly] — the register-generalized form of
    the CorrectnessI64Comparisons.v ancestors' uniform script: expose
    the pseudo-op step, substitute the four operand-half reads, reduce
    the [i64_setcond_bits_spec] axiom on the concrete condition. *)

Ltac synth_unop_proof_poly :=
  intros wstate astate v stack' rd rm Hstack HR0 Hwasm;
  unfold rule_i32_clz, rule_i32_popcnt,
         Gen.rule_i32_clz, Gen.rule_i32_popcnt;
  unfold exec_program, exec_instr;
  simpl;
  rewrite HR0;
  eexists; split;
  [ reflexivity
  | simpl; apply get_set_reg_eq ].

Ltac synth_i64_setcond_proof_poly :=
  intros astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi HR0 HR1 HR2 HR3;
  unfold rule_i64_eq, rule_i64_ne, rule_i64_lt_s, rule_i64_lt_u,
         rule_i64_gt_s, rule_i64_gt_u, rule_i64_le_s, rule_i64_le_u,
         rule_i64_ge_s, rule_i64_ge_u,
         Gen.rule_i64_eq, Gen.rule_i64_ne, Gen.rule_i64_lt_s,
         Gen.rule_i64_lt_u, Gen.rule_i64_gt_s, Gen.rule_i64_gt_u,
         Gen.rule_i64_le_s, Gen.rule_i64_le_u, Gen.rule_i64_ge_s,
         Gen.rule_i64_ge_u;
  simpl;
  rewrite HR0, HR1, HR2, HR3;
  rewrite i64_setcond_bits_spec; simpl;
  eexists; split; [reflexivity | apply get_set_reg_eq].

(** ** Increment-4 i32 bit-manipulation theorems — quantified over
    ARBITRARY rd rm (no side conditions; see the section comment). *)

Theorem rule_i32_clz_correct : forall wstate astate v stack' rd rm,
  wstate.(stack) = VI32 v :: stack' ->
  get_reg astate rm = v ->
  exec_wasm_instr I32Clz wstate =
    Some (mkWasmState (VI32 (I32.clz v) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_clz rd rm) astate = Some astate' /\
    get_reg astate' rd = I32.clz v.
Proof. synth_unop_proof_poly. Qed.

(** The two-instruction scratch=dest shape: RBIT writes the reversed
    value into [rd], CLZ reads it back from [rd] — stepped proof closing
    with [I32.clz_rbit], like [rule_i32_rotl_correct]'s structure but
    with no aliasing hypothesis needed (the "scratch" IS the dest). *)
Theorem rule_i32_ctz_correct : forall wstate astate v stack' rd rm,
  wstate.(stack) = VI32 v :: stack' ->
  get_reg astate rm = v ->
  exec_wasm_instr I32Ctz wstate =
    Some (mkWasmState (VI32 (I32.ctz v) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_ctz rd rm) astate = Some astate' /\
    get_reg astate' rd = I32.ctz v.
Proof.
  intros wstate astate v stack' rd rm Hstack HR0 Hwasm.
  unfold rule_i32_ctz, Gen.rule_i32_ctz.
  set (s1 := set_reg astate rd (I32.rbit (get_reg astate rm))).
  set (s2 := set_reg s1 rd (I32.clz (get_reg s1 rd))).
  exists s2. split.
  - subst s2 s1. simpl. reflexivity.
  - subst s2. rewrite get_set_reg_eq.
    subst s1. rewrite get_set_reg_eq.
    rewrite HR0. apply I32.clz_rbit.
Qed.

(** Pseudo-op-tier T1: proves the [POPCNT] ArmOp the selector emits
    (against the axiomatized [I32.popcnt]); the encoder's shift-and-add
    expansion below the ArmOp boundary is outside the model. *)
Theorem rule_i32_popcnt_correct : forall wstate astate v stack' rd rm,
  wstate.(stack) = VI32 v :: stack' ->
  get_reg astate rm = v ->
  exec_wasm_instr I32Popcnt wstate =
    Some (mkWasmState (VI32 (I32.popcnt v) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_popcnt rd rm) astate = Some astate' /\
    get_reg astate' rd = I32.popcnt v.
Proof. synth_unop_proof_poly. Qed.

(** ** Increment-4 binary I64SetCond theorems — quantified over all FIVE
    registers (result + two operand pairs), no side conditions.
    Pseudo-op-tier T1 against [i64_setcond_bits_spec], the
    register-generalized CorrectnessI64Comparisons.v ancestors. *)

Theorem rule_i64_eq_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_eq rd rnlo rnhi rmlo rmhi) astate = Some astate' /\
    get_reg astate' rd =
      (if I64.eq (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof. synth_i64_setcond_proof_poly. Qed.

Theorem rule_i64_ne_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_ne rd rnlo rnhi rmlo rmhi) astate = Some astate' /\
    get_reg astate' rd =
      (if I64.ne (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof. synth_i64_setcond_proof_poly. Qed.

Theorem rule_i64_lt_s_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_lt_s rd rnlo rnhi rmlo rmhi) astate = Some astate' /\
    get_reg astate' rd =
      (if I64.lts (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof. synth_i64_setcond_proof_poly. Qed.

Theorem rule_i64_lt_u_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_lt_u rd rnlo rnhi rmlo rmhi) astate = Some astate' /\
    get_reg astate' rd =
      (if I64.ltu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof. synth_i64_setcond_proof_poly. Qed.

Theorem rule_i64_gt_s_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_gt_s rd rnlo rnhi rmlo rmhi) astate = Some astate' /\
    get_reg astate' rd =
      (if I64.gts (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof. synth_i64_setcond_proof_poly. Qed.

Theorem rule_i64_gt_u_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_gt_u rd rnlo rnhi rmlo rmhi) astate = Some astate' /\
    get_reg astate' rd =
      (if I64.gtu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof. synth_i64_setcond_proof_poly. Qed.

Theorem rule_i64_le_s_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_le_s rd rnlo rnhi rmlo rmhi) astate = Some astate' /\
    get_reg astate' rd =
      (if I64.les (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof. synth_i64_setcond_proof_poly. Qed.

Theorem rule_i64_le_u_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_le_u rd rnlo rnhi rmlo rmhi) astate = Some astate' /\
    get_reg astate' rd =
      (if I64.leu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof. synth_i64_setcond_proof_poly. Qed.

Theorem rule_i64_ge_s_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_ge_s rd rnlo rnhi rmlo rmhi) astate = Some astate' /\
    get_reg astate' rd =
      (if I64.ges (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof. synth_i64_setcond_proof_poly. Qed.

Theorem rule_i64_ge_u_correct :
  forall astate lo1 hi1 lo2 hi2 rd rnlo rnhi rmlo rmhi,
  get_reg astate rnlo = lo1 ->
  get_reg astate rnhi = hi1 ->
  get_reg astate rmlo = lo2 ->
  get_reg astate rmhi = hi2 ->
  exists astate',
    exec_program (rule_i64_ge_u rd rnlo rnhi rmlo rmhi) astate = Some astate' /\
    get_reg astate' rd =
      (if I64.geu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)
       then I32.one else I32.zero).
Proof. synth_i64_setcond_proof_poly. Qed.
