(** * VCR-WASM-001 — WasmCert-Coq refinement bridge (i32 + i64 batches)

    This file proves that synth's stack-machine executor [exec_wasm_instr]
    AGREES with the WasmCert-Coq reference rules (WasmCertReference.v).
    - PHASE 2 (i32, 19 ops): add, sub, mul, and, or, xor, shl, shr_u, shr_s,
      eqz, eq, ne, lt_u, lt_s, gt_u, gt_s, le_u, le_s, ge_u — each with an
      op-level refinement theorem ([I32.op = wasmcert_i32_op]) and an
      executor-level theorem routing the claim through the REAL
      [exec_wasm_instr].
    - PHASE 3 (i64 batch, #242): add, sub, mul, and, or, xor, shl, shr_u,
      shr_s, rotl, rotr, eqz, eq, ne, lt_u, lt_s, gt_u, gt_s, le_u, le_s,
      ge_u, ge_s — op-level refinement for all 22, plus executor-level for the
      16 ops WIRED in [exec_wasm_instr] (the shifts, the two rotates, and the
      11 comparisons (incl. eqz); see the named residual below for the 6 arithmetic/
      bitwise ops the model does not yet route).
    It is the WASM-side analogue of SailArmBridge.v's per-instruction bridge
    lemmas (VCR-ISA-001 / #667).

    SCOPE (honest, named): the reference is still a hand TRANSCRIPTION of the
    pinned coq9.0-wasm-2.2.0 sources, not the real external dependency — see
    WasmCertReference.v's header for the full feasibility verdict. PHASE-3
    UPDATE (v0.48, #242): the extra-coq-package bazel/nix HOOK is now LANDED
    (blocker (1) closed), but the real dep STAYS PENDING on the unfree CompCert
    3.16 that wasmcert 2.2.0 propagates in the current nixpkgs pin (blockers
    (2)+(3)) — so this file continues to [Require Import
    Synth.WASM.WasmCertReference] and the "trusted transcription" caveat is NOT
    yet retired. It retires (mechanically) when a nixpkgs rev ships
    wasmcert >= 2.2.1.

    NAMED RESIDUALS (not forced, not admitted):
    - i64 add/sub/mul/and/or/xor have OP-LEVEL refinement only: synth's
      [exec_wasm_instr] returns [None] for the [I64Add]/…/[I64Xor] constructors
      (they are not wired in the model's match, unlike their i32 twins). Wiring
      them is a semantics-model change, out of scope for a transcription batch.
    - Remaining op coverage (div/rem trap rules, clz/ctz/popcnt, memory,
      control flow) is the named follow-up for both widths.

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

(** * VCR-WASM-001 — i64 refinement bridge (phase 3 batch)

    Proves synth's [exec_wasm_instr] AGREES with the WasmCert i64 reference
    (WasmCertReference.v's [wasmcert_i64_*]) for the i64 integer fragment. The
    helpers below are the wordsize-64 duplicates of the i32 helpers (the same
    raw-vs-normalized [Z.testbit] / shift-count-collapse content, at 2^64).

    HONEST SCOPE (named residuals). Two classes are DELIBERATELY not given
    executor-level refinement:
    - i64 add/sub/mul/and/or/xor: synth's [exec_wasm_instr] returns [None] for
      these constructors ([I64Add]/[I64Sub]/…/[I64Xor] are not wired in the
      model's match, unlike their i32 counterparts). We prove the OP-LEVEL
      refinement ([I64.op = wasmcert_i64_op], genuine raw-vs-normalized content),
      and NAME the missing executor routing as a residual — wiring them into the
      model is a semantics change, out of scope for a transcription batch.
    - i64 rotl/rotr: transcribed at the reference level (WasmCertReference.v) and
      proven op-level here; see the note at the rotate lemmas for the [n = 0]
      boundary discharge. *)

(** ** i64 encoding + normalization helpers (wordsize-64 duplicates) *)

Lemma i64_signed_refines_wasmcert : forall n,
  I64.signed n = wasmcert_i64_signed n.
Proof.
  intros n. unfold I64.signed, wasmcert_i64_signed. cbv zeta.
  rewrite zltb_lt_dec. destruct (Z_lt_dec _ _); reflexivity.
Qed.

Lemma i64_unsigned_repr_small : forall k,
  0 <= k < I64.modulus -> I64.unsigned (I64.repr k) = k.
Proof.
  intros k H. unfold I64.unsigned, I64.repr.
  rewrite Z.mod_mod by (unfold I64.modulus; lia).
  apply Z.mod_small. exact H.
Qed.

Lemma i64_shift_count_range : forall y,
  0 <= I64.unsigned y mod 64 < 64.
Proof.
  intros y. apply Z.mod_pos_bound. lia.
Qed.

Lemma i64_shift_count_collapse : forall y,
  I64.unsigned (I64.repr (I64.unsigned y mod 64)) = I64.unsigned y mod 64.
Proof.
  intros y. apply i64_unsigned_repr_small.
  pose proof (i64_shift_count_range y). unfold I64.modulus. lia.
Qed.

Lemma i64_land_mod_modulus : forall a b,
  Z.land a b mod I64.modulus =
  Z.land (a mod I64.modulus) (b mod I64.modulus) mod I64.modulus.
Proof.
  intros a b. change I64.modulus with (2 ^ 64).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_dec n 64) as [H | H].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite !Z.land_spec.
    rewrite !Z.mod_pow2_bits_low by lia.
    reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma i64_lor_mod_modulus : forall a b,
  Z.lor a b mod I64.modulus =
  Z.lor (a mod I64.modulus) (b mod I64.modulus) mod I64.modulus.
Proof.
  intros a b. change I64.modulus with (2 ^ 64).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_dec n 64) as [H | H].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite !Z.lor_spec.
    rewrite !Z.mod_pow2_bits_low by lia.
    reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma i64_lxor_mod_modulus : forall a b,
  Z.lxor a b mod I64.modulus =
  Z.lxor (a mod I64.modulus) (b mod I64.modulus) mod I64.modulus.
Proof.
  intros a b. change I64.modulus with (2 ^ 64).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_dec n 64) as [H | H].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite !Z.lxor_spec.
    rewrite !Z.mod_pow2_bits_low by lia.
    reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(** ** i64 op-level refinement: arithmetic (raw vs normalized) *)

Theorem i64_add_refines_wasmcert_op : forall x y,
  I64.add x y = wasmcert_i64_add x y.
Proof.
  intros x y.
  unfold I64.add, wasmcert_i64_add, I64.repr, I64.unsigned.
  rewrite Zplus_mod. reflexivity.
Qed.

Theorem i64_sub_refines_wasmcert_op : forall x y,
  I64.sub x y = wasmcert_i64_sub x y.
Proof.
  intros x y.
  unfold I64.sub, wasmcert_i64_sub, I64.repr, I64.unsigned.
  rewrite Zminus_mod. reflexivity.
Qed.

Theorem i64_mul_refines_wasmcert_op : forall x y,
  I64.mul x y = wasmcert_i64_mul x y.
Proof.
  intros x y.
  unfold I64.mul, wasmcert_i64_mul, I64.repr, I64.unsigned.
  rewrite Zmult_mod. reflexivity.
Qed.

(** ** i64 op-level refinement: bitwise (raw vs normalized, bit-level) *)

Theorem i64_and_refines_wasmcert_op : forall x y,
  I64.and x y = wasmcert_i64_and x y.
Proof.
  intros x y.
  unfold I64.and, wasmcert_i64_and, I64.repr, I64.unsigned.
  apply i64_land_mod_modulus.
Qed.

Theorem i64_or_refines_wasmcert_op : forall x y,
  I64.or x y = wasmcert_i64_or x y.
Proof.
  intros x y.
  unfold I64.or, wasmcert_i64_or, I64.repr, I64.unsigned.
  apply i64_lor_mod_modulus.
Qed.

Theorem i64_xor_refines_wasmcert_op : forall x y,
  I64.xor x y = wasmcert_i64_xor x y.
Proof.
  intros x y.
  unfold I64.xor, wasmcert_i64_xor, I64.repr, I64.unsigned.
  apply i64_lxor_mod_modulus.
Qed.

(** ** i64 op-level refinement: shifts *)

Theorem i64_shl_refines_wasmcert_op : forall x y,
  I64.shl x y = wasmcert_i64_shl x y.
Proof.
  intros x y. unfold wasmcert_i64_shl. cbv zeta.
  rewrite i64_shift_count_collapse.
  pose proof (i64_shift_count_range y) as Hk.
  unfold I64.shl, I64.repr, I64.unsigned. unfold I64.unsigned in Hk.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite Zmult_mod_idemp_l. reflexivity.
Qed.

Theorem i64_shr_u_refines_wasmcert_op : forall x y,
  I64.shru x y = wasmcert_i64_shr_u x y.
Proof.
  intros x y. unfold wasmcert_i64_shr_u. cbv zeta.
  rewrite i64_shift_count_collapse. reflexivity.
Qed.

Theorem i64_shr_s_refines_wasmcert_op : forall x y,
  I64.shrs x y = wasmcert_i64_shr_s x y.
Proof.
  intros x y. unfold wasmcert_i64_shr_s. cbv zeta.
  rewrite i64_shift_count_collapse.
  unfold I64.shrs. rewrite i64_signed_refines_wasmcert. reflexivity.
Qed.

(** ** i64 op-level refinement: equality tests *)

Theorem i64_eq_refines_wasmcert_op : forall x y,
  I64.eq x y = wasmcert_i64_eq x y.
Proof.
  intros x y. unfold I64.eq, wasmcert_i64_eq. apply zeqb_eq_dec.
Qed.

Theorem i64_eqz_refines_wasmcert_op : forall v,
  I64.eq v I64.zero = wasmcert_i64_eqz v.
Proof.
  intros v. unfold I64.eq, wasmcert_i64_eqz, wasmcert_i64_eq, I64.zero.
  rewrite Z.eqb_sym. apply zeqb_eq_dec.
Qed.

Theorem i64_ne_refines_wasmcert_op : forall x y,
  I64.ne x y = wasmcert_i64_ne x y.
Proof.
  intros x y. unfold I64.ne, wasmcert_i64_ne.
  rewrite i64_eq_refines_wasmcert_op. reflexivity.
Qed.

(** ** i64 op-level refinement: order comparisons *)

Theorem i64_lt_u_refines_wasmcert_op : forall x y,
  I64.ltu x y = wasmcert_i64_lt_u x y.
Proof.
  intros x y. unfold I64.ltu, wasmcert_i64_lt_u. apply zltb_lt_dec.
Qed.

Theorem i64_lt_s_refines_wasmcert_op : forall x y,
  I64.lts x y = wasmcert_i64_lt_s x y.
Proof.
  intros x y. unfold I64.lts, wasmcert_i64_lt_s.
  rewrite !i64_signed_refines_wasmcert. apply zltb_lt_dec.
Qed.

Theorem i64_gt_u_refines_wasmcert_op : forall x y,
  I64.gtu x y = wasmcert_i64_gt_u x y.
Proof.
  intros x y. unfold I64.gtu, wasmcert_i64_gt_u, wasmcert_i64_lt_u.
  rewrite Z.gtb_ltb. apply zltb_lt_dec.
Qed.

Theorem i64_gt_s_refines_wasmcert_op : forall x y,
  I64.gts x y = wasmcert_i64_gt_s x y.
Proof.
  intros x y. unfold I64.gts, wasmcert_i64_gt_s, wasmcert_i64_lt_s.
  rewrite Z.gtb_ltb. rewrite !i64_signed_refines_wasmcert. apply zltb_lt_dec.
Qed.

Theorem i64_le_u_refines_wasmcert_op : forall x y,
  I64.leu x y = wasmcert_i64_le_u x y.
Proof.
  intros x y. unfold I64.leu, wasmcert_i64_le_u, wasmcert_i64_lt_u.
  rewrite Z.leb_antisym. rewrite zltb_lt_dec. reflexivity.
Qed.

Theorem i64_le_s_refines_wasmcert_op : forall x y,
  I64.les x y = wasmcert_i64_le_s x y.
Proof.
  intros x y. unfold I64.les, wasmcert_i64_le_s, wasmcert_i64_lt_s.
  rewrite Z.leb_antisym. rewrite !i64_signed_refines_wasmcert.
  rewrite zltb_lt_dec. reflexivity.
Qed.

Theorem i64_ge_u_refines_wasmcert_op : forall x y,
  I64.geu x y = wasmcert_i64_ge_u x y.
Proof.
  intros x y. unfold I64.geu, wasmcert_i64_ge_u, wasmcert_i64_lt_u.
  rewrite Z.geb_leb. rewrite Z.leb_antisym. rewrite zltb_lt_dec. reflexivity.
Qed.

Theorem i64_ge_s_refines_wasmcert_op : forall x y,
  I64.ges x y = wasmcert_i64_ge_s x y.
Proof.
  intros x y. unfold I64.ges, wasmcert_i64_ge_s, wasmcert_i64_lt_s.
  rewrite Z.geb_leb. rewrite Z.leb_antisym. rewrite !i64_signed_refines_wasmcert.
  rewrite zltb_lt_dec. reflexivity.
Qed.

(** ** i64 op-level refinement: rotates.

    synth's [I64.rotl x y = or (shl x (repr n)) (shru x (repr (64 - n)))] with
    [n = unsigned y mod 64], where [or]/[shl]/[shru] each apply [repr] and
    re-normalize their shift count mod 64. The reference (CompCert [rol],
    Integers.v:217-219) [repr]s ONCE over the whole [Z.lor] and uses the RAW
    sub-count [64 - n]. Three gaps discharged:
    (a) the inner double-[repr] on each [Z.lor] operand — [i64_lor_mod_modulus];
    (b) [shl]'s raw operand [x] vs the reference's [unsigned x] —
        [Z.shiftl_mul_pow2] + [Zmult_mod_idemp_l];
    (c) the [n = 0] boundary: synth's [shru x (repr 64)] re-normalizes
        [64 mod 64 = 0] to a shiftr-by-0 (= [unsigned x]), while the reference
        shiftr-by-64 = 0 — reconciled because at [n = 0] the [Z.shiftl]
        operand is also [unsigned x] (shiftl-by-0) and [Z.lor] is idempotent.
    Case-split on [n = 0] handles (c); [n ∈ [1,63]] makes [(64-n) mod 64 = 64-n]. *)

Lemma i64_shl_by_repr : forall x n,
  0 <= n < 64 ->
  I64.shl x (I64.repr n) = I64.repr (Z.shiftl (I64.unsigned x) n).
Proof.
  intros x n Hn. unfold I64.shl.
  rewrite (i64_unsigned_repr_small n) by (unfold I64.modulus; lia).
  rewrite (Z.mod_small n 64) by lia.
  unfold I64.repr, I64.unsigned.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite Zmult_mod_idemp_l. reflexivity.
Qed.

Lemma i64_shru_by_repr : forall x n,
  0 <= n < 64 ->
  I64.shru x (I64.repr n) = I64.repr (Z.shiftr (I64.unsigned x) n).
Proof.
  intros x n Hn. unfold I64.shru.
  rewrite (i64_unsigned_repr_small n) by (unfold I64.modulus; lia).
  rewrite (Z.mod_small n 64) by lia. reflexivity.
Qed.

(** At n=0 the reference shiftr-by-64 vanishes; synth's shru-by-(repr 64)
    collapses to shiftr-by-0 = unsigned x, which lor-idempotently equals the
    shiftl-by-0 operand.  Proven as a bit-level Z fact. *)
Lemma shiftr_64_zero : forall u,
  0 <= u < I64.modulus -> Z.shiftr u 64 = 0.
Proof.
  intros u Hu. change I64.modulus with (2 ^ 64) in Hu.
  rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_small. lia.
Qed.

Lemma rotl_boundary_zero : forall u,
  0 <= u < I64.modulus ->
  Z.lor (Z.shiftl u 0) (Z.shiftr u 0) = Z.lor (Z.shiftl u 0) (Z.shiftr u 64).
Proof.
  intros u Hu. rewrite Z.shiftr_0_r. rewrite (shiftr_64_zero u Hu).
  rewrite Z.lor_0_r. rewrite Z.shiftl_0_r. rewrite Z.lor_diag. reflexivity.
Qed.

Theorem i64_rotl_refines_wasmcert_op : forall x y,
  I64.rotl x y = wasmcert_i64_rotl x y.
Proof.
  intros x y. unfold I64.rotl, wasmcert_i64_rotl. cbv zeta.
  set (n := I64.unsigned y mod 64).
  assert (Hn : 0 <= n < 64) by (apply Z.mod_pos_bound; lia).
  destruct (Z.eq_dec n 0) as [Hz | Hnz].
  - (* n = 0: 64 - n = 64; shru re-normalizes to 0 *)
    rewrite Hz. rewrite i64_shl_by_repr by lia.
    replace (64 - 0) with 64 by lia.
    unfold I64.shru, I64.or.
    change (I64.unsigned (I64.repr 64)) with (64 mod I64.modulus).
    change I64.modulus with (2 ^ 64).
    replace (64 mod 2 ^ 64) with 64 by (rewrite Z.mod_small; lia).
    replace (64 mod 64) with 0 by reflexivity.
    unfold I64.repr.
    rewrite <- (i64_lor_mod_modulus (Z.shiftl (I64.unsigned x) 0)
                 (Z.shiftr (I64.unsigned x) 0)).
    change (2 ^ 64) with I64.modulus.
    rewrite (rotl_boundary_zero (I64.unsigned x))
      by (unfold I64.unsigned, I64.modulus; apply Z.mod_pos_bound; lia).
    reflexivity.
  - (* n in [1,63]: (64 - n) mod 64 = 64 - n *)
    rewrite i64_shl_by_repr by lia.
    rewrite i64_shru_by_repr by lia.
    unfold I64.or, I64.repr.
    rewrite <- (i64_lor_mod_modulus (Z.shiftl (I64.unsigned x) n)
                 (Z.shiftr (I64.unsigned x) (64 - n))).
    reflexivity.
Qed.

Theorem i64_rotr_refines_wasmcert_op : forall x y,
  I64.rotr x y = wasmcert_i64_rotr x y.
Proof.
  intros x y. unfold I64.rotr, wasmcert_i64_rotr. cbv zeta.
  set (n := I64.unsigned y mod 64).
  assert (Hn : 0 <= n < 64) by (apply Z.mod_pos_bound; lia).
  destruct (Z.eq_dec n 0) as [Hz | Hnz].
  - (* n = 0: 64 - n = 64; synth shl-by-(repr 64) collapses to shl-by-0 = x *)
    rewrite Hz. rewrite i64_shru_by_repr by lia.
    replace (64 - 0) with 64 by lia.
    unfold I64.shl, I64.or.
    change (I64.unsigned (I64.repr 64)) with (64 mod I64.modulus).
    change I64.modulus with (2 ^ 64).
    replace (64 mod 2 ^ 64) with 64 by (rewrite Z.mod_small; lia).
    replace (64 mod 64) with 0 by reflexivity.
    unfold I64.repr.
    rewrite <- (i64_lor_mod_modulus (Z.shiftr (I64.unsigned x) 0)
                 (Z.shiftl x 0)).
    change (2 ^ 64) with I64.modulus.
    rewrite Z.shiftl_0_r. rewrite Z.shiftr_0_r.
    (* LHS: (lor (unsigned x) x) mod M ; RHS: (lor (unsigned x) (shiftl (unsigned x) 64)) mod M *)
    unfold I64.unsigned.
    change I64.modulus with (2 ^ 64).
    (* both sides: bit-level equality of the low 64 bits *)
    apply Z.bits_inj'. intros i Hi.
    destruct (Z_lt_dec i 64) as [Hlt | Hge].
    + rewrite !Z.mod_pow2_bits_low by lia.
      rewrite !Z.lor_spec.
      rewrite !Z.mod_pow2_bits_low by lia.
      (* shiftl (x mod M) 64 has no bit below 64 *)
      rewrite (Z.shiftl_spec (x mod 2 ^ 64) 64 i) by lia.
      rewrite (Z.testbit_neg_r (x mod 2 ^ 64) (i - 64)) by lia.
      (* low bits: x and (x mod M) agree below 64 *)
      rewrite <- (Z.mod_pow2_bits_low x 64 i) by lia.
      rewrite Bool.orb_false_r. rewrite Bool.orb_diag. reflexivity.
    + rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
  - rewrite i64_shru_by_repr by lia.
    rewrite i64_shl_by_repr by lia.
    unfold I64.or, I64.repr.
    rewrite <- (i64_lor_mod_modulus (Z.shiftr (I64.unsigned x) n)
                 (Z.shiftl (I64.unsigned x) (64 - n))).
    reflexivity.
Qed.

(** ** i64 executor-level refinement: shifts.
    [exec_wasm_instr] pushes exactly the WasmCert reference result. Mirrors the
    i32 exec lemmas but through the i64 stack path (pop2_i64 / VI64). *)

Theorem i64_shl_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Shl s =
  Some (mkWasmState
          (VI64 (wasmcert_i64_shl v1 v2) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_shl_refines_wasmcert_op. reflexivity.
Qed.

Theorem i64_shr_u_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64ShrU s =
  Some (mkWasmState
          (VI64 (wasmcert_i64_shr_u v1 v2) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_shr_u_refines_wasmcert_op. reflexivity.
Qed.

Theorem i64_shr_s_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64ShrS s =
  Some (mkWasmState
          (VI64 (wasmcert_i64_shr_s v1 v2) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_shr_s_refines_wasmcert_op. reflexivity.
Qed.

(** ** i64 executor-level refinement: rotates *)

Theorem i64_rotl_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Rotl s =
  Some (mkWasmState
          (VI64 (wasmcert_i64_rotl v1 v2) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_rotl_refines_wasmcert_op. reflexivity.
Qed.

Theorem i64_rotr_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Rotr s =
  Some (mkWasmState
          (VI64 (wasmcert_i64_rotr v1 v2) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_rotr_refines_wasmcert_op. reflexivity.
Qed.

(** ** i64 executor-level refinement: equality tests + comparisons.
    i64 compares pop two i64 and push an I32 [wasm_bool] ([if b then I32.one
    else I32.zero], numerics.v:1952-1953) — the pushed value is a VI32. *)

Theorem i64_eqz_exec_refines_wasmcert : forall v s stack',
  s.(stack) = VI64 v :: stack' ->
  exec_wasm_instr I64Eqz s =
  Some (mkWasmState
          (VI32 (if wasmcert_i64_eqz v then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v s stack' Hstack.
  unfold exec_wasm_instr, pop_i64, pop_value, pop. rewrite Hstack.
  rewrite <- i64_eqz_refines_wasmcert_op. reflexivity.
Qed.

Theorem i64_eq_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Eq s =
  Some (mkWasmState
          (VI32 (if wasmcert_i64_eq v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_eq_refines_wasmcert_op. reflexivity.
Qed.

Theorem i64_ne_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64Ne s =
  Some (mkWasmState
          (VI32 (if wasmcert_i64_ne v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_ne_refines_wasmcert_op. reflexivity.
Qed.

Theorem i64_lt_u_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64LtU s =
  Some (mkWasmState
          (VI32 (if wasmcert_i64_lt_u v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_lt_u_refines_wasmcert_op. reflexivity.
Qed.

Theorem i64_lt_s_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64LtS s =
  Some (mkWasmState
          (VI32 (if wasmcert_i64_lt_s v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_lt_s_refines_wasmcert_op. reflexivity.
Qed.

Theorem i64_gt_u_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64GtU s =
  Some (mkWasmState
          (VI32 (if wasmcert_i64_gt_u v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_gt_u_refines_wasmcert_op. reflexivity.
Qed.

Theorem i64_gt_s_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64GtS s =
  Some (mkWasmState
          (VI32 (if wasmcert_i64_gt_s v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_gt_s_refines_wasmcert_op. reflexivity.
Qed.

Theorem i64_le_u_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64LeU s =
  Some (mkWasmState
          (VI32 (if wasmcert_i64_le_u v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_le_u_refines_wasmcert_op. reflexivity.
Qed.

Theorem i64_le_s_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64LeS s =
  Some (mkWasmState
          (VI32 (if wasmcert_i64_le_s v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_le_s_refines_wasmcert_op. reflexivity.
Qed.

Theorem i64_ge_u_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64GeU s =
  Some (mkWasmState
          (VI32 (if wasmcert_i64_ge_u v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_ge_u_refines_wasmcert_op. reflexivity.
Qed.

Theorem i64_ge_s_exec_refines_wasmcert : forall v1 v2 s stack',
  s.(stack) = VI64 v2 :: VI64 v1 :: stack' ->
  exec_wasm_instr I64GeS s =
  Some (mkWasmState
          (VI32 (if wasmcert_i64_ge_s v1 v2 then I32.one else I32.zero) :: stack')
          s.(locals) s.(globals) s.(memory)).
Proof.
  intros v1 v2 s stack' Hstack.
  unfold exec_wasm_instr, pop2_i64, pop2. rewrite Hstack.
  rewrite <- i64_ge_s_refines_wasmcert_op. reflexivity.
Qed.
