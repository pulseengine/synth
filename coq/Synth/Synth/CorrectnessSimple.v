(** * Simple Operations Correctness

    This file contains correctness proofs for simple WebAssembly operations:
    - Control flow: Nop, Drop, Select
    - Locals: LocalGet, LocalSet, LocalTee
    - Globals: GlobalGet, GlobalSet
    - Constants: I32Const, I64Const
    - i32 comparisons (existence-only form)
    - i32 shift/rotate operations (existence-only form)
    - i32 bit manipulation (existence-only form)

    Strategy: All proofs in this file prove only existence (exists astate'),
    without specifying result correspondence. This is sufficient because
    every ARM instruction in exec_instr returns Some for non-division ops.
*)

From Stdlib Require Import Lia.
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

(** ** Helper Tactics *)

(** Solve proofs where compile_wasm_to_arm produces an empty program *)
Ltac solve_empty :=
  intros; unfold compile_wasm_to_arm; simpl;
  eexists; reflexivity.

(** Solve proofs for single non-division ARM instructions *)
Ltac solve_single_instr :=
  intros; unfold compile_wasm_to_arm;
  unfold exec_program; simpl;
  eexists; reflexivity.

(** Solve proofs for CMP+MOV+conditional-MOV sequences (3 instructions).
    All three instructions always return Some. *)
Ltac solve_cmp_mov_sequence :=
  intros; unfold compile_wasm_to_arm, exec_program, exec_instr; simpl;
  (* After full unfolding, the goal may contain if-expressions from
     conditional MOVs. Destruct all boolean conditions. *)
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b
  end;
  eexists; reflexivity.

(** ** Control Flow Operations *)

(** Nop does nothing *)
Theorem nop_correct : forall wstate astate,
  exec_wasm_instr Nop wstate = Some wstate ->
  exists astate',
    exec_program (compile_wasm_to_arm Nop) astate = Some astate'.
Proof.
  intros wstate astate Hwasm.
  unfold compile_wasm_to_arm. simpl.
  exists astate. reflexivity.
Qed.

(** Select chooses value based on condition *)
Theorem select_correct : forall wstate astate cond val1 val2 stack',
  wstate.(stack) = VI32 cond :: val2 :: val1 :: stack' ->
  exec_wasm_instr Select wstate =
    Some (mkWasmState
            ((if I32.eq cond I32.zero then val2 else val1) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm Select) astate = Some astate'.
Proof.
  (* Select compiles to [CMP R2 (Imm I32.zero); MOVNE R0 (Reg R0); MOVEQ R0 (Reg R1)] *)
  (* All three instructions always return Some *)
  solve_cmp_mov_sequence.
Qed.

(** Drop removes top of stack *)
Theorem drop_correct : forall wstate astate v stack',
  wstate.(stack) = v :: stack' ->
  exec_wasm_instr Drop wstate =
    Some (mkWasmState stack' wstate.(locals) wstate.(globals) wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm Drop) astate = Some astate'.
Proof.
  intros wstate astate v stack' Hstack Hwasm.
  unfold compile_wasm_to_arm. simpl.
  exists astate. reflexivity.
Qed.

(** ** Local Variable Operations *)

(** LocalGet loads a local variable *)
Theorem local_get_correct : forall wstate astate (idx : nat),
  lt idx 4 ->
  exec_wasm_instr (LocalGet idx) wstate =
    Some (mkWasmState
            (VI32 (wstate.(locals) idx) :: wstate.(stack))
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  (forall i, lt i 4 -> get_reg astate (match i with
                                       | O => R4
                                       | S O => R5
                                       | S (S O) => R6
                                       | _ => R7
                                       end) = wstate.(locals) i) ->
  exists astate',
    exec_program (compile_wasm_to_arm (LocalGet idx)) astate = Some astate' /\
    get_reg astate' R0 = wstate.(locals) idx.
Proof.
  (* LocalGet compiles to [MOV R0 (Reg Rn)] where Rn is R4-R7 *)
  (* MOV always returns Some (set_reg s rd v) *)
  intros wstate astate idx Hlt Hwasm Hregs.
  unfold compile_wasm_to_arm. simpl.
  destruct idx as [|[|[|[|n]]]].
  - eexists. split. reflexivity. rewrite get_set_reg_eq. apply (Hregs 0%nat). lia.
  - eexists. split. reflexivity. rewrite get_set_reg_eq. apply (Hregs 1%nat). lia.
  - eexists. split. reflexivity. rewrite get_set_reg_eq. apply (Hregs 2%nat). lia.
  - eexists. split. reflexivity. rewrite get_set_reg_eq. apply (Hregs 3%nat). lia.
  - lia.
Qed.

(** LocalSet stores to a local variable *)
Theorem local_set_correct : forall wstate astate v stack' (idx : nat),
  lt idx 4 ->
  wstate.(stack) = VI32 v :: stack' ->
  get_reg astate R0 = v ->
  exec_wasm_instr (LocalSet idx) wstate =
    Some (mkWasmState
            stack'
            (wstate.(locals) [idx |-> v])
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (LocalSet idx)) astate = Some astate' /\
    get_reg astate' (match idx with
                     | O => R4
                     | S O => R5
                     | S (S O) => R6
                     | _ => R7
                     end) = v.
Proof.
  (* LocalSet compiles to [MOV Rn (Reg R0)] where Rn is R4-R7 *)
  intros wstate astate v stack' idx Hlt Hstack HR0 Hwasm.
  unfold compile_wasm_to_arm.
  destruct idx as [|[|[|[|n]]]];
  try (simpl; eexists; split; [reflexivity |
    rewrite get_set_reg_eq; exact HR0]).
  lia.
Qed.

(** ** Constants *)

(** #166 verify-what-ships: the MOVW+MOVT large-constant reconstruction lemma.

    The large-constant compilation path emits
      MOVW R0 (repr (land u 65535))    (* low 16 bits *)
      MOVT R0 (repr (shiftr u 16))     (* high 16 bits into bits 31..16 *)
    where [u = I32.unsigned n]. This is the exact byte-level lowering the Rust
    encoder ships (instruction_selector: split-immediate MOVW/MOVT). We prove,
    by bit extensionality, that composing the two halves reconstructs [u]:

      or (and (repr (land u 65535)) (repr 0xFFFF)) (shl (repr (shiftr u 16)) 16)
        = repr u.

    Everything on the left is [_ mod 2^32], so the reconstruction produces the
    register-normalized value [repr u = repr (unsigned n) = unsigned n], NOT the
    raw representative [n]. That distinction is the crux of the [i32_const_correct]
    modeling gap documented below. *)

Local Open Scope Z_scope.

Lemma movw_movt_reconstruct_Z : forall u : Z,
  Z.lor
    (Z.land (Z.land u 65535 mod 2 ^ 32) (65535 mod 2 ^ 32) mod 2 ^ 32)
    (Z.shiftl (Z.shiftr u 16 mod 2 ^ 32) 16 mod 2 ^ 32) mod 2 ^ 32
  = u mod 2 ^ 32.
Proof.
  intros u.
  change (65535 mod 2 ^ 32) with (Z.ones 16).
  change 65535 with (Z.ones 16).
  rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'; intros i Hi.
  (* Peel outer [land (ones32)] (final mod), the [lor], and the left operand's
     [land]s down to [testbit u i]. The right operand's [shiftl] is handled per
     half below (its argument's [land] only reduces after [Z.shiftl_spec]). *)
  rewrite Z.land_spec, Z.lor_spec.
  rewrite !Z.land_spec.
  rewrite (Z.testbit_ones 32 i) by lia.
  rewrite !(Z.testbit_ones 16 i) by lia.
  (* Case on whether bit [i] lands in the low half (< 16) or high half (>= 16). *)
  destruct (Z.ltb_spec i 16) as [Hlo | Hhi].
  - (* low half: the shifted high part contributes 0 (bit index i-16 < 0). *)
    rewrite Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (i - 16)) by lia.
    rewrite Bool.orb_false_r.
    destruct (Z.testbit u i);
      destruct (i <? 32) eqn:E32, (i <? 16) eqn:E16, (0 <=? i) eqn:E0;
      cbn; try reflexivity;
      (try (exfalso; apply Z.ltb_ge in E16; lia));
      (try (exfalso; apply Z.leb_gt in E0; lia)).
  - (* high half: the low-16 mask contributes 0 at bit i (i >= 16). *)
    rewrite Z.shiftl_spec by lia.
    rewrite Z.land_spec, (Z.testbit_ones 32 (i - 16)) by lia.
    rewrite Z.shiftr_spec by lia.
    replace (i - 16 + 16) with i by lia.
    destruct (Z.testbit u i);
      destruct (i <? 32) eqn:E32, (i <? 16) eqn:E16, (0 <=? i - 16) eqn:El,
               (i - 16 <? 32) eqn:Eh, (0 <=? i) eqn:E0;
      cbn; try reflexivity;
      (try (exfalso; apply Z.ltb_lt in E16; lia));
      (try (exfalso; apply Z.ltb_ge in E32; lia));
      (try (exfalso; apply Z.leb_gt in El; lia));
      (try (exfalso; apply Z.ltb_ge in Eh; lia)).
Qed.

(** ARM-level reconstruction: after the shipped MOVW+MOVT large-constant
    sequence, R0 holds the register-normalized constant [I32.repr (I32.unsigned n)].
    This is a real, unconditional Qed about the exact instructions that ship. *)
Lemma i32_const_large_reconstruct : forall astate n,
  I32.unsigned n > 65535 ->
  exists astate',
    exec_program (compile_wasm_to_arm (I32Const n)) astate = Some astate' /\
    get_reg astate' R0 = I32.repr (I32.unsigned n).
Proof.
  intros astate n Hbig.
  unfold compile_wasm_to_arm.
  (* the guard [Z.leb (I32.unsigned n) 65535] is false *)
  replace (Z.leb (I32.unsigned n) 65535) with false
    by (symmetry; apply Z.leb_gt; lia).
  (* Execute the two-instruction [MOVW; MOVT] program. *)
  cbn [exec_program exec_instr].
  eexists. split; [reflexivity|].
  (* Reduce every [get_reg (set_reg _ R0 _) R0] (final get + MOVT's read). *)
  rewrite !get_set_reg_eq.
  unfold I32.or, I32.and, I32.shl, I32.repr, I32.unsigned.
  (* shift amount: (16 mod 2^32) mod 32 = 16 *)
  change ((16 mod 2 ^ 32) mod 32) with 16.
  apply movw_movt_reconstruct_Z.
Qed.

Local Close Scope Z_scope.

(** i32.const branches on the constant size: MOVW for [unsigned n <= 65535],
    MOVW+MOVT otherwise.

    T3 — DOCUMENTED MODELING GAP (NOT a division admit, NOT an unproven bit fact).
    The reconstruction arithmetic IS proven (see [movw_movt_reconstruct_Z] and
    [i32_const_large_reconstruct] above, both real Qed). The residual is a
    value-representation mismatch, not a missing proof:

    - [exec_wasm_instr (I32Const n)] pushes [VI32 n] with the RAW [Z]
      representative [n] (WasmSemantics does not normalize constants).
    - The MOVW+MOVT ship path (large branch) necessarily normalizes: it yields
      [I32.repr (I32.unsigned n) = I32.unsigned n], proven above.

    So [get_reg astate' R0 = n] holds UNCONDITIONALLY only in the small (MOVW)
    branch; in the large branch it holds iff [n] is register-normalized
    ([I32.valid_unsigned n], i.e. [n = I32.unsigned n]). The theorem as stated
    (no normalization hypothesis) is therefore FALSE for out-of-range
    representatives with [unsigned n > 65535] — a real counterexample exists
    (e.g. [n = 2^32 + 0x10000]).

    Two ways to close it, both a change of contract rather than a new proof:
      (a) normalize [I32Const] at the WASM boundary in the model
          (push [VI32 (I32.repr n)]), then [i32_const_large_reconstruct]
          discharges it directly; or
      (b) add the [I32.valid_unsigned n] register-normalization hypothesis
          (the same explicit contract the #73 div_s proof adopted).
    Per the #166 "never weaken a theorem to force a Qed" gate, neither is
    applied here silently; the theorem stays honestly Admitted with the
    reconstruction fact already discharged. *)
Theorem i32_const_correct : forall wstate astate n,
  exec_wasm_instr (I32Const n) wstate =
    Some (mkWasmState
            (VI32 n :: wstate.(stack))
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (I32Const n)) astate = Some astate' /\
    get_reg astate' R0 = n.
Proof.
  (* See the T3 rationale above: false in the large branch for un-normalized
     [n]; the reconstruction arithmetic itself is proven in
     [i32_const_large_reconstruct]. *)
Admitted.

(** v0.9.0 PR 1 (precursor + discharge): I64Const compiles to
    `I64ConstPseudo R0 R1 n`, which writes `(i64_const_lo n, i64_const_hi n)`
    to (R0, R1). The new result-equation axioms `i64_const_lo_spec` and
    `i64_const_hi_spec` in ArmSemantics.v pin those to `lo_of_i64 n` and
    `hi_of_i64 n` respectively. The theorem is now dual-register: it covers
    both halves. *)
Theorem i64_const_correct : forall wstate astate n,
  exec_wasm_instr (I64Const n) wstate =
    Some (mkWasmState
            (VI64 n :: wstate.(stack))
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (I64Const n)) astate = Some astate' /\
    get_reg astate' R0 = lo_of_i64 n /\
    get_reg astate' R1 = hi_of_i64 n.
Proof.
  intros wstate astate n _Hwasm.
  unfold compile_wasm_to_arm; simpl.
  eexists. split; [reflexivity | split].
  - (* R0 = lo_of_i64 n *)
    rewrite get_set_reg_neq by discriminate.
    rewrite get_set_reg_eq.
    apply i64_const_lo_spec.
  - (* R1 = hi_of_i64 n *)
    rewrite get_set_reg_eq.
    apply i64_const_hi_spec.
Qed.

(** LocalTee sets local and keeps value on stack *)
Theorem local_tee_correct : forall wstate astate v stack' (idx : nat),
  lt idx 4 ->
  wstate.(stack) = VI32 v :: stack' ->
  get_reg astate R0 = v ->
  exec_wasm_instr (LocalTee idx) wstate =
    Some (mkWasmState
            (VI32 v :: stack')
            (wstate.(locals) [idx |-> v])
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (LocalTee idx)) astate = Some astate'.
Proof.
  (* LocalTee compiles to [MOV Rn (Reg R0)] — single MOV always returns Some *)
  intros wstate astate v stack' idx Hlt Hstack HR0 Hwasm.
  unfold compile_wasm_to_arm. simpl.
  destruct idx as [|[|[|[|n]]]]; try lia;
  eexists; reflexivity.
Qed.

(** ** Global Variable Operations *)

Theorem global_get_correct : forall wstate astate (idx : nat),
  lt idx 4 ->
  exec_wasm_instr (GlobalGet idx) wstate =
    Some (mkWasmState
            (VI32 (wstate.(globals) idx) :: wstate.(stack))
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (GlobalGet idx)) astate = Some astate'.
Proof.
  intros wstate astate idx Hlt Hwasm.
  unfold compile_wasm_to_arm. simpl.
  destruct idx as [|[|[|[|n]]]]; try lia;
  eexists; reflexivity.
Qed.

Theorem global_set_correct : forall wstate astate v stack' (idx : nat),
  lt idx 4 ->
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr (GlobalSet idx) wstate =
    Some (mkWasmState
            stack'
            wstate.(locals)
            (wstate.(globals) [idx |-> v])
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm (GlobalSet idx)) astate = Some astate'.
Proof.
  intros wstate astate v stack' idx Hlt Hstack Hwasm.
  unfold compile_wasm_to_arm. simpl.
  destruct idx as [|[|[|[|n]]]]; try lia;
  eexists; reflexivity.
Qed.

(** ** Comparison Operations *)
(** All comparisons compile to CMP + MOV + conditional MOV sequences.
    All three instructions always return Some, so existence is trivial. *)

Theorem i32_eqz_executes : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr I32Eqz wstate =
    Some (mkWasmState
            (VI32 (if I32.eq v I32.zero then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Eqz) astate = Some astate'.
Proof. solve_cmp_mov_sequence. Qed.

Theorem i32_eq_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Eq wstate =
    Some (mkWasmState
            (VI32 (if I32.eq v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Eq) astate = Some astate'.
Proof. solve_cmp_mov_sequence. Qed.

Theorem i32_ne_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Ne wstate =
    Some (mkWasmState
            (VI32 (if I32.ne v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Ne) astate = Some astate'.
Proof. solve_cmp_mov_sequence. Qed.

Theorem i32_lts_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32LtS wstate =
    Some (mkWasmState
            (VI32 (if I32.lts v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32LtS) astate = Some astate'.
Proof. solve_cmp_mov_sequence. Qed.

Theorem i32_ltu_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32LtU wstate =
    Some (mkWasmState
            (VI32 (if I32.ltu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32LtU) astate = Some astate'.
Proof. solve_cmp_mov_sequence. Qed.

Theorem i32_gts_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32GtS wstate =
    Some (mkWasmState
            (VI32 (if I32.gts v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32GtS) astate = Some astate'.
Proof. solve_cmp_mov_sequence. Qed.

Theorem i32_gtu_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32GtU wstate =
    Some (mkWasmState
            (VI32 (if I32.gtu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32GtU) astate = Some astate'.
Proof. solve_cmp_mov_sequence. Qed.

Theorem i32_les_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32LeS wstate =
    Some (mkWasmState
            (VI32 (if I32.les v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32LeS) astate = Some astate'.
Proof. solve_cmp_mov_sequence. Qed.

Theorem i32_leu_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32LeU wstate =
    Some (mkWasmState
            (VI32 (if I32.leu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32LeU) astate = Some astate'.
Proof. solve_cmp_mov_sequence. Qed.

Theorem i32_ges_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32GeS wstate =
    Some (mkWasmState
            (VI32 (if I32.ges v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32GeS) astate = Some astate'.
Proof. solve_cmp_mov_sequence. Qed.

Theorem i32_geu_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32GeU wstate =
    Some (mkWasmState
            (VI32 (if I32.geu v1 v2 then I32.one else I32.zero) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32GeU) astate = Some astate'.
Proof. solve_cmp_mov_sequence. Qed.

(** ** I32 Shift Operations *)
(** Shift/rotate ops compile to single ARM shift instructions, which always return Some *)

Theorem i32_shl_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Shl wstate =
    Some (mkWasmState
            (VI32 (I32.shl v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Shl) astate = Some astate'.
Proof.
  (* Compiles to [LSL R0 R0 0] — single instruction, always Some *)
  solve_single_instr.
Qed.

Theorem i32_shru_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32ShrU wstate =
    Some (mkWasmState
            (VI32 (I32.shru v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32ShrU) astate = Some astate'.
Proof.
  solve_single_instr.
Qed.

Theorem i32_shrs_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32ShrS wstate =
    Some (mkWasmState
            (VI32 (I32.shrs v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32ShrS) astate = Some astate'.
Proof.
  solve_single_instr.
Qed.

Theorem i32_rotl_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Rotl wstate =
    Some (mkWasmState
            (VI32 (I32.rotl v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Rotl) astate = Some astate'.
Proof.
  (* I32Rotl compiles to [RSB R2 R1 (Imm 32); ROR_reg R0 R0 R2] *)
  intros; unfold compile_wasm_to_arm; simpl; eexists; reflexivity.
Qed.

Theorem i32_rotr_executes : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Rotr wstate =
    Some (mkWasmState
            (VI32 (I32.rotr v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Rotr) astate = Some astate'.
Proof.
  (* Compiles to [ROR R0 R0 0] — single instruction, always Some *)
  solve_single_instr.
Qed.

(** ** I32 Bit Manipulation Operations *)

Theorem i32_clz_executes : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr I32Clz wstate =
    Some (mkWasmState
            (VI32 (I32.clz v) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Clz) astate = Some astate'.
Proof.
  (* Compiles to [CLZ R0 R0] — single instruction, always Some *)
  solve_single_instr.
Qed.

Theorem i32_ctz_executes : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr I32Ctz wstate =
    Some (mkWasmState
            (VI32 (I32.ctz v) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Ctz) astate = Some astate'.
Proof.
  (* Compiles to [RBIT R0 R0; CLZ R0 R0] — two instructions, both always Some *)
  intros; unfold compile_wasm_to_arm.
  unfold exec_program; simpl.
  eexists; reflexivity.
Qed.

Theorem i32_popcnt_executes : forall wstate astate v stack',
  wstate.(stack) = VI32 v :: stack' ->
  exec_wasm_instr I32Popcnt wstate =
    Some (mkWasmState
            (VI32 (I32.popcnt v) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Popcnt) astate = Some astate'.
Proof.
  (* Compiles to [POPCNT R0 R0] — single instruction, always Some *)
  solve_single_instr.
Qed.
