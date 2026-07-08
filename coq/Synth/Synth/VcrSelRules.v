(** * VCR-SEL-001 increments 1+2: Rocq obligations of the wired selector rule table

    One universally-quantified T1 theorem per rule in the checked-in DSL table
    [crates/synth-synthesis/src/sel_dsl/mod.rs] (RULES), naming 1:1:

      Rust rule [rule_i32_add]  <->  [Definition rule_i32_add]
                                <->  [Theorem rule_i32_add_correct]

    Each [Definition] below is the register-polymorphic ARM sequence the
    generated Rust lowering ([sel_dsl/generated.rs]) emits — byte-for-byte the
    hand-written [select_default] arm it mirrors (pinned by the Rust-side
    mirror test). The theorems prove the T1 bound carried over from the pilot
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
    CorrectnessI32.v use, parameterized over registers verbatim. *)

From Stdlib Require Import List.
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
Import ListNotations.

Open Scope Z_scope.

(** ** The rule lowerings — 1:1 with sel_dsl::RULES / sel_dsl::generated *)

Definition rule_i32_add (rd rn rm : arm_reg) : arm_program := [ADD rd rn (Reg rm)].
Definition rule_i32_sub (rd rn rm : arm_reg) : arm_program := [SUB rd rn (Reg rm)].
Definition rule_i32_mul (rd rn rm : arm_reg) : arm_program := [MUL rd rn rm].
Definition rule_i32_and (rd rn rm : arm_reg) : arm_program := [AND rd rn (Reg rm)].
Definition rule_i32_or  (rd rn rm : arm_reg) : arm_program := [ORR rd rn (Reg rm)].
Definition rule_i32_xor (rd rn rm : arm_reg) : arm_program := [EOR rd rn (Reg rm)].

(** Tier B: two instructions through a scratch register [rs] — rotate left by
    [rm] = rotate right by (32 - [rm]). [RSB] writes the scratch in
    instruction 1 before [ROR] reads the value register in instruction 2, so
    [rs] must not alias [rn]: the side condition the rule table carries. *)
Definition rule_i32_rotl (rd rn rm rs : arm_reg) : arm_program :=
  [RSB rs rm (Imm (I32.repr 32)); ROR_reg rd rn rs].

(** ** Increment 2: i32 register shifts + rotr — tier A (single instruction,
    no scratch; the shift amount is masked mod 32 by the I32 semantics of
    LSL_reg/LSR_reg/ASR_reg/ROR_reg, matching WASM). *)

Definition rule_i32_shl   (rd rn rm : arm_reg) : arm_program := [LSL_reg rd rn rm].
Definition rule_i32_shr_s (rd rn rm : arm_reg) : arm_program := [ASR_reg rd rn rm].
Definition rule_i32_shr_u (rd rn rm : arm_reg) : arm_program := [LSR_reg rd rn rm].
Definition rule_i32_rotr  (rd rn rm : arm_reg) : arm_program := [ROR_reg rd rn rm].

(** ** Increment 2: i32 comparisons — the Rust rule emits
    [Cmp {rn, Reg(rm)}; SetCond {rd, cond}]; per the established
    Compilation.v convention the [SetCond] pseudo-op is modeled as
    [MOV rd #0; MOVcc rd #1] over the flags CMP latched. No aliasing side
    conditions: the flags transfer is through NZCV, not a register, so the
    theorems below hold for EVERY rd/rn/rm assignment. *)

Definition rule_i32_eq (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVEQ rd (Imm I32.one)].
Definition rule_i32_ne (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVNE rd (Imm I32.one)].
Definition rule_i32_lt_s (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVLT rd (Imm I32.one)].
Definition rule_i32_lt_u (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVLO rd (Imm I32.one)].
Definition rule_i32_gt_s (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVGT rd (Imm I32.one)].
Definition rule_i32_gt_u (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVHI rd (Imm I32.one)].
Definition rule_i32_le_s (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVLE rd (Imm I32.one)].
Definition rule_i32_le_u (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVLS rd (Imm I32.one)].
Definition rule_i32_ge_s (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVGE rd (Imm I32.one)].
Definition rule_i32_ge_u (rd rn rm : arm_reg) : arm_program :=
  [CMP rn (Reg rm); MOV rd (Imm I32.zero); MOVHS rd (Imm I32.one)].

(** ** The discharge tactic — verbatim [synth_binop_proof] (Tactics.v) modulo
    the lowering-unfold target, as measured by the pilot. *)
Ltac synth_binop_proof_poly :=
  intros wstate astate v1 v2 stack' rd rn rm Hstack HR0 HR1 Hwasm;
  unfold rule_i32_add, rule_i32_sub, rule_i32_mul,
         rule_i32_and, rule_i32_or, rule_i32_xor,
         rule_i32_shl, rule_i32_shr_s, rule_i32_shr_u, rule_i32_rotr;
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
  unfold rule_i32_rotl.
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

Theorem rule_i32_shl_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32Shl wstate =
    Some (mkWasmState (VI32 (I32.shl v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_shl rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.shl v1 v2.
Proof. synth_binop_proof_poly. Qed.

Theorem rule_i32_shr_s_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32ShrS wstate =
    Some (mkWasmState (VI32 (I32.shrs v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_shr_s rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.shrs v1 v2.
Proof. synth_binop_proof_poly. Qed.

Theorem rule_i32_shr_u_correct : forall wstate astate v1 v2 stack' rd rn rm,
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate rn = v1 ->
  get_reg astate rm = v2 ->
  exec_wasm_instr I32ShrU wstate =
    Some (mkWasmState (VI32 (I32.shru v1 v2) :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (rule_i32_shr_u rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.shru v1 v2.
Proof. synth_binop_proof_poly. Qed.

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
         rule_i32_ge_s, rule_i32_ge_u;
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
  unfold rule_i32_ne; simpl.
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
  unfold rule_i32_lt_s; simpl.
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
  unfold rule_i32_lt_u; simpl.
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
