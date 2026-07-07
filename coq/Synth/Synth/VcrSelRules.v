(** * VCR-SEL-001 increment 1: Rocq obligations of the wired selector rule table

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

    Tier A (no-scratch single-instruction: add/sub/mul/and/or/xor) discharges
    with [synth_binop_proof_poly] — verbatim [synth_binop_proof] (Tactics.v)
    modulo the lowering-unfold target, exactly as the pilot measured (6/6).
    Tier B ([rule_i32_rotl], RSB scratch + ROR) carries the explicit
    [rs <> rn] scratch non-aliasing hypothesis — the side condition the DSL
    records in the rule table and the generated Rust enforces at runtime. *)

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

(** ** The discharge tactic — verbatim [synth_binop_proof] (Tactics.v) modulo
    the lowering-unfold target, as measured by the pilot. *)
Ltac synth_binop_proof_poly :=
  intros wstate astate v1 v2 stack' rd rn rm Hstack HR0 HR1 Hwasm;
  unfold rule_i32_add, rule_i32_sub, rule_i32_mul,
         rule_i32_and, rule_i32_or, rule_i32_xor;
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
