(** * VCR-WASM-001 — WasmCert-Coq refinement bridge (phase 2: i32 batch)

    This file proves that synth's stack-machine executor [exec_wasm_instr]
    AGREES with the WasmCert-Coq reference rules (WasmCertReference.v) for the
    i32 integer fragment: add, sub, mul, and, or, xor, shl, shr_u, shr_s,
    eqz, eq, ne, lt_u, lt_s, gt_u, gt_s, le_u, le_s, ge_u — 19 ops, each with
    an op-level refinement theorem ([I32.op = wasmcert_i32_op]) and an
    executor-level theorem routing the claim through the REAL
    [exec_wasm_instr]. It is the WASM-side analogue of SailArmBridge.v's
    per-instruction bridge lemmas (VCR-ISA-001 / #667).

    SCOPE (honest, named): the reference is still a hand TRANSCRIPTION of the
    pinned coq9.0-wasm-2.2.0 sources, not the real external dependency — see
    WasmCertReference.v's header for the phase-2 feasibility verdict
    (nix-feasible, bazel-deferred on three named blockers). Remaining op
    coverage (div/rem trap rules, clz/ctz/popcnt, rotl/rotr, i64, memory,
    control flow) is the named follow-up.

    NON-VACUITY (why a WRONG synth semantics fails this file):
    - No op-level lemma is [reflexivity]-only where a real gap exists:
      * arithmetic: synth operates on RAW representatives ([I32.add x y :=
        repr (x + y)]) vs the reference's normalize-then-operate
        ([repr (unsigned x + unsigned y)]) — discharged via
        [Zplus_mod]/[Zminus_mod]/[Zmult_mod];
      * bitwise: raw-vs-normalized under [Z.land]/[Z.lor]/[Z.lxor] is a
        BIT-LEVEL fact (low 32 bits of the op equal the op of the low 32
        bits), discharged by [Z.bits_inj'] + [testbit] reasoning — not by any
        mod-homomorphism rewrite;
      * shifts: the reference's DOUBLE normalization of the shift count
        ([unsigned (repr (unsigned y mod 32))]) is collapsed by a proved
        range lemma, and for shl the raw-vs-normalized operand gap is
        discharged via [Z.shiftl_mul_pow2] + [Zmult_mod_idemp_l];
      * comparisons: the reference keeps CompCert's SUMBOOL decisions
        ([Z.eq_dec]/[Z_lt_dec], = Coqlib zeq/zlt) and WasmCert's DERIVED
        orientation (gt/le/ge from lt by swap+negation, numerics.v:974-979),
        while synth uses [Z.gtb]/[Z.leb]/[Z.geb] directly — each lemma
        discharges the boolean-vs-sumbool bridge and, for gt/le/ge, the
        real orientation gap ([Z.gtb_ltb]/[Z.leb_antisym]/[Z.geb_leb]).
    - Executor-level theorems route through the REAL [exec_wasm_instr]. If an
      op were miswired (wrong operation, wrong operand ORDER — pinned because
      sub/shl/comparisons are non-commutative — wrong stack shape, wrong
      boolean encoding), the theorem would be unprovable: the pushed value is
      pinned to the INDEPENDENT reference, with comparisons pinned to
      WasmCert's [wasm_bool] shape (numerics.v:1952-1953:
      [if b then one else zero]).
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.WASM.WasmValues.
Require Import Synth.WASM.WasmInstructions.
Require Import Synth.WASM.WasmSemantics.
Require Import Synth.WASM.WasmCertReference.

Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.

(** ** Encoding helpers: boolean tests vs CompCert's sumbool decisions *)

Lemma zeqb_eq_dec : forall a b : Z,
  (a =? b) = if Z.eq_dec a b then true else false.
Proof.
  intros a b. destruct (Z.eq_dec a b) as [E | E].
  - apply Z.eqb_eq; exact E.
  - apply Z.eqb_neq; exact E.
Qed.

Lemma zltb_lt_dec : forall a b : Z,
  (a <? b) = if Z_lt_dec a b then true else false.
Proof.
  intros a b. destruct (Z_lt_dec a b) as [L | L].
  - apply Z.ltb_lt; exact L.
  - apply Z.ltb_nlt; exact L.
Qed.

(** Synth's [I32.signed] (Z.ltb over the normalized representative) equals
    the transcribed CompCert [signed] (zlt sumbool, Integers.v:137-139). *)
Lemma signed_refines_wasmcert : forall n,
  I32.signed n = wasmcert_i32_signed n.
Proof.
  intros n. unfold I32.signed, wasmcert_i32_signed. cbv zeta.
  rewrite zltb_lt_dec. destruct (Z_lt_dec _ _); reflexivity.
Qed.

(** ** Normalization helpers *)

Lemma unsigned_repr_small : forall k,
  0 <= k < I32.modulus -> I32.unsigned (I32.repr k) = k.
Proof.
  intros k H. unfold I32.unsigned, I32.repr.
  rewrite Z.mod_mod by (unfold I32.modulus; lia).
  apply Z.mod_small. exact H.
Qed.

Lemma shift_count_range : forall y,
  0 <= I32.unsigned y mod 32 < 32.
Proof.
  intros y. apply Z.mod_pos_bound. lia.
Qed.

(** The reference's DOUBLE normalization of the shift count collapses:
    [unsigned (repr (unsigned y mod 32)) = unsigned y mod 32]. *)
Lemma shift_count_collapse : forall y,
  I32.unsigned (I32.repr (I32.unsigned y mod 32)) = I32.unsigned y mod 32.
Proof.
  intros y. apply unsigned_repr_small.
  pose proof (shift_count_range y). unfold I32.modulus. lia.
Qed.

(** ** Bit-level helpers: low 32 bits of a bitwise op = op of low 32 bits.
    These are the raw-vs-normalized discharges for and/or/xor — genuine
    [Z.testbit] facts, not mod-homomorphism rewrites. *)

Lemma land_mod_modulus : forall a b,
  Z.land a b mod I32.modulus =
  Z.land (a mod I32.modulus) (b mod I32.modulus) mod I32.modulus.
Proof.
  intros a b. change I32.modulus with (2 ^ 32).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_dec n 32) as [H | H].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite !Z.land_spec.
    rewrite !Z.mod_pow2_bits_low by lia.
    reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lor_mod_modulus : forall a b,
  Z.lor a b mod I32.modulus =
  Z.lor (a mod I32.modulus) (b mod I32.modulus) mod I32.modulus.
Proof.
  intros a b. change I32.modulus with (2 ^ 32).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_dec n 32) as [H | H].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite !Z.lor_spec.
    rewrite !Z.mod_pow2_bits_low by lia.
    reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lxor_mod_modulus : forall a b,
  Z.lxor a b mod I32.modulus =
  Z.lxor (a mod I32.modulus) (b mod I32.modulus) mod I32.modulus.
Proof.
  intros a b. change I32.modulus with (2 ^ 32).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_dec n 32) as [H | H].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite !Z.lxor_spec.
    rewrite !Z.mod_pow2_bits_low by lia.
    reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(** ** Op-level refinement: arithmetic (raw vs normalized, mod-homomorphism) *)

Theorem i32_add_refines_wasmcert_op : forall x y,
  I32.add x y = wasmcert_i32_add x y.
Proof.
  intros x y.
  unfold I32.add, wasmcert_i32_add, I32.repr, I32.unsigned.
  (* Goal: (x + y) mod m = ((x mod m) + (y mod m)) mod m *)
  rewrite Zplus_mod.
  reflexivity.
Qed.

Theorem i32_sub_refines_wasmcert_op : forall x y,
  I32.sub x y = wasmcert_i32_sub x y.
Proof.
  intros x y.
  unfold I32.sub, wasmcert_i32_sub, I32.repr, I32.unsigned.
  rewrite Zminus_mod.
  reflexivity.
Qed.

Theorem i32_mul_refines_wasmcert_op : forall x y,
  I32.mul x y = wasmcert_i32_mul x y.
Proof.
  intros x y.
  unfold I32.mul, wasmcert_i32_mul, I32.repr, I32.unsigned.
  rewrite Zmult_mod.
  reflexivity.
Qed.

(** ** Op-level refinement: bitwise (raw vs normalized, bit-level) *)

Theorem i32_and_refines_wasmcert_op : forall x y,
  I32.and x y = wasmcert_i32_and x y.
Proof.
  intros x y.
  unfold I32.and, wasmcert_i32_and, I32.repr, I32.unsigned.
  apply land_mod_modulus.
Qed.

Theorem i32_or_refines_wasmcert_op : forall x y,
  I32.or x y = wasmcert_i32_or x y.
Proof.
  intros x y.
  unfold I32.or, wasmcert_i32_or, I32.repr, I32.unsigned.
  apply lor_mod_modulus.
Qed.

Theorem i32_xor_refines_wasmcert_op : forall x y,
  I32.xor x y = wasmcert_i32_xor x y.
Proof.
  intros x y.
  unfold I32.xor, wasmcert_i32_xor, I32.repr, I32.unsigned.
  apply lxor_mod_modulus.
Qed.

(** ** Op-level refinement: shifts *)

Theorem i32_shl_refines_wasmcert_op : forall x y,
  I32.shl x y = wasmcert_i32_shl x y.
Proof.
  intros x y. unfold wasmcert_i32_shl. cbv zeta.
  rewrite shift_count_collapse.
  pose proof (shift_count_range y) as Hk.
  unfold I32.shl, I32.repr, I32.unsigned. unfold I32.unsigned in Hk.
  (* Goal: Z.shiftl x k mod m = Z.shiftl (x mod m) k mod m, 0 <= k < 32 *)
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite Zmult_mod_idemp_l.
  reflexivity.
Qed.

Theorem i32_shr_u_refines_wasmcert_op : forall x y,
  I32.shru x y = wasmcert_i32_shr_u x y.
Proof.
  intros x y. unfold wasmcert_i32_shr_u. cbv zeta.
  rewrite shift_count_collapse.
  reflexivity.
Qed.

Theorem i32_shr_s_refines_wasmcert_op : forall x y,
  I32.shrs x y = wasmcert_i32_shr_s x y.
Proof.
  intros x y. unfold wasmcert_i32_shr_s. cbv zeta.
  rewrite shift_count_collapse.
  unfold I32.shrs. rewrite signed_refines_wasmcert.
  reflexivity.
Qed.

(** ** Op-level refinement: equality tests *)

Theorem i32_eq_refines_wasmcert_op : forall x y,
  I32.eq x y = wasmcert_i32_eq x y.
Proof.
  intros x y. unfold I32.eq, wasmcert_i32_eq. apply zeqb_eq_dec.
Qed.

(** [int_eqz := eq zero] puts zero FIRST (numerics.v:970); synth's executor
    tests [I32.eq v I32.zero] — the symmetry discharge pins that they agree. *)
Theorem i32_eqz_refines_wasmcert_op : forall v,
  I32.eq v I32.zero = wasmcert_i32_eqz v.
Proof.
  intros v. unfold I32.eq, wasmcert_i32_eqz, wasmcert_i32_eq, I32.zero.
  rewrite Z.eqb_sym. apply zeqb_eq_dec.
Qed.

Theorem i32_ne_refines_wasmcert_op : forall x y,
  I32.ne x y = wasmcert_i32_ne x y.
Proof.
  intros x y. unfold I32.ne, wasmcert_i32_ne.
  rewrite i32_eq_refines_wasmcert_op. reflexivity.
Qed.

(** ** Op-level refinement: order comparisons.
    gt/le/ge discharge a REAL orientation gap: synth uses Z.gtb/Z.leb/Z.geb
    directly, the reference derives them from lt by swap+negation. *)

Theorem i32_lt_u_refines_wasmcert_op : forall x y,
  I32.ltu x y = wasmcert_i32_lt_u x y.
Proof.
  intros x y. unfold I32.ltu, wasmcert_i32_lt_u. apply zltb_lt_dec.
Qed.

Theorem i32_lt_s_refines_wasmcert_op : forall x y,
  I32.lts x y = wasmcert_i32_lt_s x y.
Proof.
  intros x y. unfold I32.lts, wasmcert_i32_lt_s.
  rewrite !signed_refines_wasmcert. apply zltb_lt_dec.
Qed.

Theorem i32_gt_u_refines_wasmcert_op : forall x y,
  I32.gtu x y = wasmcert_i32_gt_u x y.
Proof.
  intros x y. unfold I32.gtu, wasmcert_i32_gt_u, wasmcert_i32_lt_u.
  rewrite Z.gtb_ltb. apply zltb_lt_dec.
Qed.

Theorem i32_gt_s_refines_wasmcert_op : forall x y,
  I32.gts x y = wasmcert_i32_gt_s x y.
Proof.
  intros x y. unfold I32.gts, wasmcert_i32_gt_s, wasmcert_i32_lt_s.
  rewrite Z.gtb_ltb. rewrite !signed_refines_wasmcert. apply zltb_lt_dec.
Qed.

Theorem i32_le_u_refines_wasmcert_op : forall x y,
  I32.leu x y = wasmcert_i32_le_u x y.
Proof.
  intros x y. unfold I32.leu, wasmcert_i32_le_u, wasmcert_i32_lt_u.
  rewrite Z.leb_antisym. rewrite zltb_lt_dec. reflexivity.
Qed.

Theorem i32_le_s_refines_wasmcert_op : forall x y,
  I32.les x y = wasmcert_i32_le_s x y.
Proof.
  intros x y. unfold I32.les, wasmcert_i32_le_s, wasmcert_i32_lt_s.
  rewrite Z.leb_antisym. rewrite !signed_refines_wasmcert.
  rewrite zltb_lt_dec. reflexivity.
Qed.

Theorem i32_ge_u_refines_wasmcert_op : forall x y,
  I32.geu x y = wasmcert_i32_ge_u x y.
Proof.
  intros x y. unfold I32.geu, wasmcert_i32_ge_u, wasmcert_i32_lt_u.
  rewrite Z.geb_leb. rewrite Z.leb_antisym. rewrite zltb_lt_dec. reflexivity.
Qed.

Theorem i32_ge_s_refines_wasmcert_op : forall x y,
  I32.ges x y = wasmcert_i32_ge_s x y.
Proof.
  intros x y. unfold I32.ges, wasmcert_i32_ge_s, wasmcert_i32_lt_s.
  rewrite Z.geb_leb. rewrite Z.leb_antisym. rewrite !signed_refines_wasmcert.
  rewrite zltb_lt_dec. reflexivity.
Qed.

(** ** Executor-level refinement: [exec_wasm_instr] pushes exactly the
       WasmCert reference result on top of the popped stack.

    Mirrors the shape of [i32_add_type_preservation] in WasmSemantics.v, but
    the pushed value is pinned to the INDEPENDENT reference, not to synth's
    own operation. Comparisons pin WasmCert's [wasm_bool] result shape
    (numerics.v:1952-1953). Proof pattern: expose the stack, rewrite the
    reference back to synth's op via the (real) op-level refinement theorem,
    and close by conversion — the rewrite step IS the refinement content. *)

Theorem i32_add_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Add s =
  Some (mkWasmState
          (VI32 (wasmcert_i32_add v1 v2) :: stack')
          s.(locals)
          s.(globals)
          s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_add_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_sub_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Sub s =
  Some (mkWasmState
          (VI32 (wasmcert_i32_sub v1 v2) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_sub_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_mul_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Mul s =
  Some (mkWasmState
          (VI32 (wasmcert_i32_mul v1 v2) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_mul_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_and_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32And s =
  Some (mkWasmState
          (VI32 (wasmcert_i32_and v1 v2) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_and_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_or_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Or s =
  Some (mkWasmState
          (VI32 (wasmcert_i32_or v1 v2) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_or_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_xor_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Xor s =
  Some (mkWasmState
          (VI32 (wasmcert_i32_xor v1 v2) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_xor_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_shl_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Shl s =
  Some (mkWasmState
          (VI32 (wasmcert_i32_shl v1 v2) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_shl_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_shr_u_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32ShrU s =
  Some (mkWasmState
          (VI32 (wasmcert_i32_shr_u v1 v2) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_shr_u_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_shr_s_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32ShrS s =
  Some (mkWasmState
          (VI32 (wasmcert_i32_shr_s v1 v2) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_shr_s_refines_wasmcert_op.
  reflexivity.
Qed.

(** Executor-level: equality tests and comparisons pin WasmCert's
    [wasm_bool] shape ([if b then one else zero], numerics.v:1952-1953)
    with the reference boolean under the [if]. *)

Theorem i32_eqz_exec_refines_wasmcert : forall v s stack',
  s.(stack) = VI32 v :: stack' ->
  exec_wasm_instr I32Eqz s =
  Some (mkWasmState
          (VI32 (if wasmcert_i32_eqz v then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v s stack' Hstack.
  unfold exec_wasm_instr, pop_i32, pop_value, pop.
  rewrite Hstack.
  rewrite <- i32_eqz_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_eq_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Eq s =
  Some (mkWasmState
          (VI32 (if wasmcert_i32_eq v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_eq_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_ne_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32Ne s =
  Some (mkWasmState
          (VI32 (if wasmcert_i32_ne v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_ne_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_lt_u_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32LtU s =
  Some (mkWasmState
          (VI32 (if wasmcert_i32_lt_u v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_lt_u_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_lt_s_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32LtS s =
  Some (mkWasmState
          (VI32 (if wasmcert_i32_lt_s v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_lt_s_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_gt_u_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32GtU s =
  Some (mkWasmState
          (VI32 (if wasmcert_i32_gt_u v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_gt_u_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_gt_s_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32GtS s =
  Some (mkWasmState
          (VI32 (if wasmcert_i32_gt_s v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_gt_s_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_le_u_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32LeU s =
  Some (mkWasmState
          (VI32 (if wasmcert_i32_le_u v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_le_u_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_le_s_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32LeS s =
  Some (mkWasmState
          (VI32 (if wasmcert_i32_le_s v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_le_s_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_ge_u_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32GeU s =
  Some (mkWasmState
          (VI32 (if wasmcert_i32_ge_u v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_ge_u_refines_wasmcert_op.
  reflexivity.
Qed.

Theorem i32_ge_s_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  exec_wasm_instr I32GeS s =
  Some (mkWasmState
          (VI32 (if wasmcert_i32_ge_s v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i32, pop2.
  rewrite Hstack.
  rewrite <- i32_ge_s_refines_wasmcert_op.
  reflexivity.
Qed.
