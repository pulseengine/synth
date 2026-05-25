(** * I64 Operations Correctness

    This file contains correctness proofs for all i64 WebAssembly operations.

    v0.8.0 PR 1a alignment: i64 ops now compile to dual-register pair sequences
    matching Rust codegen (R0:R1 result, R2:R3 second operand). See
    docs/analysis/I64_CODEGEN_SURVEY.md for the per-op breakdown. Existence
    proofs (T2) remain valid because each pseudo-op returns Some. The four
    T1 div/rem proofs were re-admitted pending the v0.8.0 lift queue (#147
    PRs 2–5) — see the block-comment above the four Admitted theorems.
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

(* The 4 T1 division/remainder proofs below were previously stated against the
   simplified single-instruction model (I64DivS -> SDIV R0 R0 R1, etc.) and used
   I32.divs / I32.divu hypotheses — which is *not* what the Rust compiler
   actually emits. The real compiler emits high-level ArmOp::I64DivS / DivU /
   RemS / RemU pseudo-ops that lower to gale software-helper calls
   (__aeabi_ldivmod, __aeabi_uldivmod). See
   docs/analysis/I64_CODEGEN_SURVEY.md §7 for the survey.

   Re-stating these proofs against the aligned model requires concrete
   semantics for the i64_divs_pair / i64_divu_pair / i64_rems_pair /
   i64_remu_pair axioms (which currently capture the trap-vs-success
   structure only). Lifting is tracked under the v0.8.0 umbrella (#147)
   PRs 2–5: the lift queue closes these admits by replacing the bit-pattern
   axioms with concrete I64.divs / I64.divu / I64.rems / I64.remu defs and
   proving the lo/hi decomposition matches the helper's ABI.

   For this PR (1a — Compilation.v alignment) the proofs are Admitted so that
   we do not silently prove the wrong theorem (umbrella's falsification
   clause). *)

Theorem i64_divs_correct : forall wstate astate v1 v2 stack' result,
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  I32.divs v1 v2 = Some result ->
  exec_wasm_instr I64DivS wstate =
    Some (mkWasmState (VI64 result :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64DivS) astate = Some astate' /\
    get_reg astate' R0 = result.
Proof.
  (* Pending v0.8.0 lift queue (#147 PR 2): replace i64_divs_pair axiom with
     concrete I64.divs lo/hi decomposition. *)
Admitted.

Theorem i64_divu_correct : forall wstate astate v1 v2 stack' result,
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  I32.divu v1 v2 = Some result ->
  exec_wasm_instr I64DivU wstate =
    Some (mkWasmState (VI64 result :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64DivU) astate = Some astate' /\
    get_reg astate' R0 = result.
Proof.
  (* Pending v0.8.0 lift queue (#147 PR 2): replace i64_divu_pair axiom. *)
Admitted.

Theorem i64_rems_correct : forall wstate astate v1 v2 stack' result quotient,
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  I32.divs v1 v2 = Some quotient ->
  result = I32.sub v1 (I32.mul quotient v2) ->
  I32.rems v1 v2 = Some result ->
  exec_wasm_instr I64RemS wstate =
    Some (mkWasmState (VI64 result :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64RemS) astate = Some astate' /\
    get_reg astate' R0 = result.
Proof.
  (* Pending v0.8.0 lift queue (#147 PR 2): replace i64_rems_pair axiom. *)
Admitted.

Theorem i64_remu_correct : forall wstate astate v1 v2 stack' result quotient,
  wstate.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  I32.divu v1 v2 = Some quotient ->
  result = I32.sub v1 (I32.mul quotient v2) ->
  I32.remu v1 v2 = Some result ->
  exec_wasm_instr I64RemU wstate =
    Some (mkWasmState (VI64 result :: stack')
            wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I64RemU) astate = Some astate' /\
    get_reg astate' R0 = result.
Proof.
  (* Pending v0.8.0 lift queue (#147 PR 2): replace i64_remu_pair axiom. *)
Admitted.

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

(** ** Summary (after v0.8.0 PR 1a alignment)

    I64 Operations: 26 theorems in this file
    - Arithmetic existence: 3 Qed (Add, Sub, Mul)
    - Division/remainder T1: 4 Admitted, pending v0.8.0 lift queue (#147 PRs 2–5)
    - Bitwise existence: 3 Qed (And, Or, Xor)
    - Shift/rotate existence: 5 Qed (Shl, ShrU, ShrS, Rotl, Rotr)
    - Comparison existence: 11 Qed (Eqz, Eq, Ne, Lt*, Gt*, Le*, Ge*)
    - Bit-manipulation existence: 3 Qed (Clz, Ctz, Popcnt) — note: also stated
      in CorrectnessI64Comparisons.v with I64-typed hypotheses

    Status: 22 Qed / 4 Admitted (down from 29 Qed / 0 Admitted).
    The previous "29 Qed" total proved the WRONG theorem (compiler was emitting
    i64 ADD as single 32-bit ADD); aligning Compilation.v with the real codegen
    requires reproving div/rem against the new pseudo-op axioms.
*)
