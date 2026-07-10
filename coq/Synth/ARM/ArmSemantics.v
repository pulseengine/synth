(** * ARM Operational Semantics

    This file defines the operational semantics of ARM instructions.
    Each instruction is defined as a state transformation function.

    Based on synth-verify/src/arm_semantics.rs
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.

Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

(** ** Abstract VFP (Floating-Point) Operations

    VFP operations are axiomatized as abstract functions on bit patterns.
    VFP registers store I32.int values representing IEEE 754 bit patterns.

    This is sufficient for existence proofs (T2: ARM execution succeeds).
    Full result-correspondence proofs (T1) would require Flocq IEEE 754
    semantics to relate these bit-pattern operations to WASM float semantics.
*)

(** F32 arithmetic on bit patterns (single-precision, stored in S-registers) *)
Axiom f32_add_bits : I32.int -> I32.int -> I32.int.
Axiom f32_sub_bits : I32.int -> I32.int -> I32.int.
Axiom f32_mul_bits : I32.int -> I32.int -> I32.int.
Axiom f32_div_bits : I32.int -> I32.int -> I32.int.
Axiom f32_sqrt_bits : I32.int -> I32.int.
Axiom f32_abs_bits : I32.int -> I32.int.
Axiom f32_neg_bits : I32.int -> I32.int.

(** F64 arithmetic on bit patterns (double-precision, stored in D-registers) *)
Axiom f64_add_bits : I32.int -> I32.int -> I32.int.
Axiom f64_sub_bits : I32.int -> I32.int -> I32.int.
Axiom f64_mul_bits : I32.int -> I32.int -> I32.int.
Axiom f64_div_bits : I32.int -> I32.int -> I32.int.
Axiom f64_sqrt_bits : I32.int -> I32.int.
Axiom f64_abs_bits : I32.int -> I32.int.
Axiom f64_neg_bits : I32.int -> I32.int.

(** VFP comparison: updates FPSCR flags, modeled as updating ARM condition flags.
    Returns the new condition flags after comparing two VFP values. *)
Axiom f32_compare_flags : I32.int -> I32.int -> condition_flags.
Axiom f64_compare_flags : I32.int -> I32.int -> condition_flags.

(** VFP conversion operations on bit patterns *)
Axiom cvt_f32_to_f64_bits : I32.int -> I32.int.  (** F32 -> F64 promote *)
Axiom cvt_f64_to_f32_bits : I32.int -> I32.int.  (** F64 -> F32 demote *)
Axiom cvt_s32_to_f32_bits : I32.int -> I32.int.  (** Signed int -> F32 *)
Axiom cvt_f32_to_s32_bits : I32.int -> I32.int.  (** F32 -> Signed int *)

(** ** Axiomatized I64 pseudo-op result functions

    Each i64 pseudo-op writes its result(s) as a function of the inputs.
    These axioms are placeholders — they assert the existence of some result
    value matching the corresponding ArmOp encoder output. The current
    correctness proofs are existence-only (T2): they prove the program runs
    to a Some-state, not that the resulting bit-pattern equals the WASM
    semantics. Lifting these to T1 result-correspondence is the job of
    follow-up PRs (the umbrella issue #147 v0.8.0 lift queue: PRs 2–5).

    The (lo, hi) decomposition follows the Rust convention:
      i64 value v <-> (rdlo := low 32 bits of v, rdhi := high 32 bits of v).
*)

(** i64.mul: full 64-bit product *)
Axiom i64_mul_lo_bits : I32.int -> I32.int -> I32.int -> I32.int -> I32.int.
Axiom i64_mul_hi_bits : I32.int -> I32.int -> I32.int -> I32.int -> I32.int.

(** i64.shl / i64.shr_u / i64.shr_s — shift count's low half in rmlo *)
Axiom i64_shl_lo_bits  : I32.int -> I32.int -> I32.int -> I32.int.
Axiom i64_shl_hi_bits  : I32.int -> I32.int -> I32.int -> I32.int.
Axiom i64_shru_lo_bits : I32.int -> I32.int -> I32.int -> I32.int.
Axiom i64_shru_hi_bits : I32.int -> I32.int -> I32.int -> I32.int.
Axiom i64_shrs_lo_bits : I32.int -> I32.int -> I32.int -> I32.int.
Axiom i64_shrs_hi_bits : I32.int -> I32.int -> I32.int -> I32.int.

(** i64.rotl / i64.rotr — shift count in single register *)
Axiom i64_rotl_lo_bits : I32.int -> I32.int -> I32.int -> I32.int.
Axiom i64_rotl_hi_bits : I32.int -> I32.int -> I32.int -> I32.int.
Axiom i64_rotr_lo_bits : I32.int -> I32.int -> I32.int -> I32.int.
Axiom i64_rotr_hi_bits : I32.int -> I32.int -> I32.int -> I32.int.

(** i64.clz / i64.ctz / i64.popcnt — single 32-bit result *)
Axiom i64_clz_bits    : I32.int -> I32.int -> I32.int.
Axiom i64_ctz_bits    : I32.int -> I32.int -> I32.int.
Axiom i64_popcnt_bits : I32.int -> I32.int -> I32.int.

(** i64 comparison: 0/1 result selected by condition *)
Axiom i64_setcond_bits  : I32.int -> I32.int -> I32.int -> I32.int -> condition -> I32.int.
Axiom i64_setcondz_bits : I32.int -> I32.int -> I32.int.

(** i64.div_s/_u and i64.rem_s/_u — option result for trap semantics *)
Axiom i64_divs_pair : I32.int -> I32.int -> I32.int -> I32.int -> option (I32.int * I32.int).
Axiom i64_divu_pair : I32.int -> I32.int -> I32.int -> I32.int -> option (I32.int * I32.int).
Axiom i64_rems_pair : I32.int -> I32.int -> I32.int -> I32.int -> option (I32.int * I32.int).
Axiom i64_remu_pair : I32.int -> I32.int -> I32.int -> I32.int -> option (I32.int * I32.int).

(** i64.const: split a 64-bit value into 32-bit halves *)
Axiom i64_const_lo : I64.int -> I32.int.
Axiom i64_const_hi : I64.int -> I32.int.

(** i64.extend_i32_s/_u: low half is rn, high half is sign-extension or zero *)
Axiom i64_extend_s_hi : I32.int -> I32.int.
  (** sign-extension of i32 -> high half of i64; equals 0 if rn >= 0, all-ones otherwise *)

(** Memory: 8-byte load splits into two halves *)
Axiom i64_load_lo : memory -> Z -> I32.int.
Axiom i64_load_hi : memory -> Z -> I32.int.

(** ** Result-correspondence axioms for i64 pseudo-ops (v0.9.0 precursor)

    The axioms above (lines ~74-117) commit only the *type* of each pseudo-op
    result function. That is enough for existence proofs (T2: ARM execution
    succeeds), but it is *not* enough to prove that the resulting bit pattern
    equals the WASM-spec result (T1: result correspondence).

    This block adds, for each pseudo-op result function, a companion `_spec`
    axiom that pins its result to the WASM-spec operation on the combined
    64-bit value. Each spec is cross-checked against the per-op codegen survey
    `docs/analysis/I64_CODEGEN_SURVEY.md`, which in turn cites the exact
    `instruction_selector.rs` line numbers that the Rust compiler emits.

    Convention. A register pair `(lo, hi)` corresponds to the i64 value
    `combine_i32 lo hi = I64.repr (I32.unsigned lo + 2^32 * I32.unsigned hi)`.
    Projection back is via `lo_of_i64` / `hi_of_i64`.

    None semantics. Where a WASM op traps (div/rem by zero, signed-div
    overflow), the corresponding pseudo-op result is `None`. We tie that
    behaviour to `I64.divs / I64.divu / I64.rems / I64.remu` returning `None`.

    Why axioms (not definitions). The encoder lowers each pseudo-op to a
    multi-instruction ARM sequence (e.g., `I64DivS` becomes a software-helper
    call to `__aeabi_ldivmod`, `I64SetCond` becomes a dual-precision compare
    sequence). Modeling those expansions concretely in Rocq would require a
    full bit-level encoder model. Until that exists, we *axiomatize* the
    correspondence between the high-level pseudo-op and its WASM-spec meaning.

    Falsification clause. If the fuzz harness ever exhibits an input where
    the compiled ARM sequence diverges from the WASM-spec result modelled by
    a `_spec` axiom below, that axiom is false and must be retracted. Tracked
    in umbrella issue #152 (v0.9.0 lift queue). *)

(** i64.const — split a 64-bit value into 32-bit halves.
    Cross-check: I64_CODEGEN_SURVEY.md §8 ("I64Const {rdlo=R0, rdhi=R1, value}",
    instruction_selector.rs:1393–1399). The encoder lowers I64ConstPseudo to
    MOVW/MOVT for each half. *)
Axiom i64_const_lo_spec : forall n,
  i64_const_lo n = lo_of_i64 n.
Axiom i64_const_hi_spec : forall n,
  i64_const_hi n = hi_of_i64 n.

(** i64.div_s / div_u / rem_s / rem_u — software-helper pseudo-ops.
    Cross-check: I64_CODEGEN_SURVEY.md §7 (lines 1737–1779) and the encoder
    notes that these expand to __aeabi_ldivmod / __aeabi_uldivmod runtime
    helper calls. The helpers compute full 64-bit signed/unsigned division
    on the combined operand pair. Trap semantics match WASM:
      - div_s traps on y=0 and on min_signed/(-1) signed-overflow,
      - div_u traps on y=0,
      - rem_s traps only on y=0 (NOT on min_signed % -1; per WASM spec,
        i64.rem_s of min/-1 is 0 — handled by the helper, not a trap),
      - rem_u traps only on y=0. *)
Axiom i64_divs_pair_spec : forall lo1 hi1 lo2 hi2,
  i64_divs_pair lo1 hi1 lo2 hi2 =
  match I64.divs (combine_i32 lo1 hi1) (combine_i32 lo2 hi2) with
  | Some r => Some (lo_of_i64 r, hi_of_i64 r)
  | None => None
  end.
Axiom i64_divu_pair_spec : forall lo1 hi1 lo2 hi2,
  i64_divu_pair lo1 hi1 lo2 hi2 =
  match I64.divu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2) with
  | Some r => Some (lo_of_i64 r, hi_of_i64 r)
  | None => None
  end.
Axiom i64_rems_pair_spec : forall lo1 hi1 lo2 hi2,
  i64_rems_pair lo1 hi1 lo2 hi2 =
  match I64.rems (combine_i32 lo1 hi1) (combine_i32 lo2 hi2) with
  | Some r => Some (lo_of_i64 r, hi_of_i64 r)
  | None => None
  end.
Axiom i64_remu_pair_spec : forall lo1 hi1 lo2 hi2,
  i64_remu_pair lo1 hi1 lo2 hi2 =
  match I64.remu (combine_i32 lo1 hi1) (combine_i32 lo2 hi2) with
  | Some r => Some (lo_of_i64 r, hi_of_i64 r)
  | None => None
  end.

(** i64.mul — UMULL+MLA cross-product pseudo-op.
    Cross-check: I64_CODEGEN_SURVEY.md §4 (instruction_selector.rs:1646–1655).
    Encoder expands to UMULL + MLA. The full 64-bit product of the combined
    operands is the spec. *)
Axiom i64_mul_lo_bits_spec : forall lo1 hi1 lo2 hi2,
  i64_mul_lo_bits lo1 hi1 lo2 hi2 =
  lo_of_i64 (I64.mul (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)).
Axiom i64_mul_hi_bits_spec : forall lo1 hi1 lo2 hi2,
  i64_mul_hi_bits lo1 hi1 lo2 hi2 =
  hi_of_i64 (I64.mul (combine_i32 lo1 hi1) (combine_i32 lo2 hi2)).

(** i64.shl / i64.shr_u / i64.shr_s — funnel-shift pseudo-ops.
    Cross-check: I64_CODEGEN_SURVEY.md §5 (instruction_selector.rs:1658–1689).
    The shift count is the low half of operand 2 (`rmlo`); the high half of
    the count is discarded — WASM i64 shifts already mask the count modulo 64,
    and the encoder relies on `I64.{shl,shru,shrs}` doing that masking via
    `combine_i32 cnt 0` (the high half of the count is always logically zero
    for a valid WASM shift). *)
Axiom i64_shl_lo_bits_spec : forall lo1 hi1 cnt,
  i64_shl_lo_bits lo1 hi1 cnt =
  lo_of_i64 (I64.shl (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).
Axiom i64_shl_hi_bits_spec : forall lo1 hi1 cnt,
  i64_shl_hi_bits lo1 hi1 cnt =
  hi_of_i64 (I64.shl (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).
Axiom i64_shru_lo_bits_spec : forall lo1 hi1 cnt,
  i64_shru_lo_bits lo1 hi1 cnt =
  lo_of_i64 (I64.shru (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).
Axiom i64_shru_hi_bits_spec : forall lo1 hi1 cnt,
  i64_shru_hi_bits lo1 hi1 cnt =
  hi_of_i64 (I64.shru (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).
Axiom i64_shrs_lo_bits_spec : forall lo1 hi1 cnt,
  i64_shrs_lo_bits lo1 hi1 cnt =
  lo_of_i64 (I64.shrs (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).
Axiom i64_shrs_hi_bits_spec : forall lo1 hi1 cnt,
  i64_shrs_hi_bits lo1 hi1 cnt =
  hi_of_i64 (I64.shrs (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).

(** i64.rotl / i64.rotr — funnel-rotate pseudo-ops.
    Cross-check: I64_CODEGEN_SURVEY.md §5 (instruction_selector.rs:1691–1709).
    Shift amount is a single 32-bit register (rotates mask modulo 64). *)
Axiom i64_rotl_lo_bits_spec : forall lo1 hi1 cnt,
  i64_rotl_lo_bits lo1 hi1 cnt =
  lo_of_i64 (I64.rotl (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).
Axiom i64_rotl_hi_bits_spec : forall lo1 hi1 cnt,
  i64_rotl_hi_bits lo1 hi1 cnt =
  hi_of_i64 (I64.rotl (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).
Axiom i64_rotr_lo_bits_spec : forall lo1 hi1 cnt,
  i64_rotr_lo_bits lo1 hi1 cnt =
  lo_of_i64 (I64.rotr (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).
Axiom i64_rotr_hi_bits_spec : forall lo1 hi1 cnt,
  i64_rotr_hi_bits lo1 hi1 cnt =
  hi_of_i64 (I64.rotr (combine_i32 lo1 hi1) (combine_i32 cnt I32.zero)).

(** i64.clz / i64.ctz / i64.popcnt — bit-count pseudo-ops.
    Cross-check: I64_CODEGEN_SURVEY.md §6 (instruction_selector.rs:1712–1734).
    The result is a 32-bit count (0..64 fits in 7 bits) stored in `R0`. The
    spec equates it to `I64.{clz,ctz,popcnt}` of the combined operand, then
    projected to i32. (Since the count is at most 64, the projection is
    lossless.) *)
Axiom i64_clz_bits_spec : forall lo hi,
  i64_clz_bits lo hi = i64_to_i32 (I64.clz (combine_i32 lo hi)).
Axiom i64_ctz_bits_spec : forall lo hi,
  i64_ctz_bits lo hi = i64_to_i32 (I64.ctz (combine_i32 lo hi)).
Axiom i64_popcnt_bits_spec : forall lo hi,
  i64_popcnt_bits lo hi = i64_to_i32 (I64.popcnt (combine_i32 lo hi)).

(** i64 comparison pseudo-ops — single 0/1 result selected by ARM condition.
    Cross-check: I64_CODEGEN_SURVEY.md §3 (instruction_selector.rs:1535–1643).
    The encoder lowers `I64SetCond` to a multi-instruction dual-precision
    compare sequence (CMP-low, SBCS-high, MOV+conditional-MOV) and `I64SetCondZ`
    to (ORR-lo-hi, MOV+conditional-MOVEQ). The result is the WASM 0/1 outcome
    of comparing the combined 64-bit operands under the indicated condition.

    The mapping from ARM `condition` to WASM comparison is fixed by
    Compilation.v: the i64 comparison ops emit `I64SetCond ... Cond_EQ`,
    `Cond_NE`, `Cond_LT`, `Cond_CC` (LO=CC, unsigned <), `Cond_GT`,
    `Cond_HI` (unsigned >), `Cond_LE`, `Cond_LS` (unsigned <=), `Cond_GE`,
    `Cond_CS` (HS=CS, unsigned >=).

    NOTE: This spec is a *parametric family* over the ARM condition; the
    discharge of any particular i64 comparison theorem (e.g., I64Eq) further
    case-splits on the specific condition. *)
Axiom i64_setcond_bits_spec : forall lo1 hi1 lo2 hi2 cond,
  i64_setcond_bits lo1 hi1 lo2 hi2 cond =
  let v1 := combine_i32 lo1 hi1 in
  let v2 := combine_i32 lo2 hi2 in
  let bit :=
    match cond with
    | Cond_EQ => I64.eq  v1 v2
    | Cond_NE => I64.ne  v1 v2
    | Cond_LT => I64.lts v1 v2
    | Cond_CC => I64.ltu v1 v2  (* LO = CC: unsigned < *)
    | Cond_GT => I64.gts v1 v2
    | Cond_HI => I64.gtu v1 v2  (* HI: unsigned > *)
    | Cond_LE => I64.les v1 v2
    | Cond_LS => I64.leu v1 v2  (* LS: unsigned <= *)
    | Cond_GE => I64.ges v1 v2
    | Cond_CS => I64.geu v1 v2  (* HS = CS: unsigned >= *)
    | _ => false  (* other ARM conditions are not emitted for i64 cmps *)
    end in
  if bit then I32.one else I32.zero.

(** i64.eqz — unary; result is 1 iff combined operand is zero. *)
Axiom i64_setcondz_bits_spec : forall lo hi,
  i64_setcondz_bits lo hi =
  (if I64.eq (combine_i32 lo hi) I64.zero then I32.one else I32.zero).

(** i64.extend_i32_s — high half is the sign-extension of `rn`.
    Cross-check: I64_CODEGEN_SURVEY.md §8. The Rust encoder emits ASR R1, R0, #31
    to fill `rdhi` with the sign bit of `rn`. The spec equates the axiomatic
    `i64_extend_s_hi` to `I32.shrs rn 31` (which produces 0 for non-negative
    rn and all-ones for negative rn — matching the ASR #31 instruction). *)
Axiom i64_extend_s_hi_spec : forall rn,
  i64_extend_s_hi rn = I32.shrs rn (I32.repr 31).

(** i64 load — 8-byte memory load splits into low/high halves.
    Cross-check: I64_CODEGEN_SURVEY.md §9 (instruction_selector.rs:1782). The
    encoder emits a bounds-checked LDR pair: `LDR rdlo, [base, off]` and
    `LDR rdhi, [base, off+4]`. The natural correspondence:

      i64_load_lo m a = load_mem_at m a
      i64_load_hi m a = load_mem_at m (a + 4)

    However, the memory model `m : Z -> I32.int` is a host-level i32 read
    from `m` at a signed address — the encoder's bounds check and endianness
    handling are not modelled here. We therefore leave the load result
    pinned to raw memory reads at offsets 0 and 4 — the weakest spec
    consistent with the present model. PR 5 of the umbrella will revisit
    when the memory model lifts. Marked TODO #152. *)
Axiom i64_load_lo_spec : forall m a,
  i64_load_lo m a = m a.
Axiom i64_load_hi_spec : forall m a,
  i64_load_hi m a = m (a + 4).

(** ** Flag Computation Helpers *)

(** Compute negative flag: result < 0 (signed) *)
Definition compute_n_flag (result : I32.int) : bool :=
  Z.ltb (I32.signed result) 0.

(** Compute zero flag: result == 0 *)
Definition compute_z_flag (result : I32.int) : bool :=
  I32.eq result I32.zero.

(** Compute carry flag for addition *)
Definition compute_c_flag_add (x y : I32.int) : bool :=
  let ux := I32.unsigned x in
  let uy := I32.unsigned y in
  Z.ltb I32.max_unsigned (ux + uy).

(** Compute overflow flag for addition *)
Definition compute_v_flag_add (x y result : I32.int) : bool :=
  let sx := I32.signed x in
  let sy := I32.signed y in
  let sr := I32.signed result in
  (* Overflow if: pos + pos = neg OR neg + neg = pos *)
  orb
    (andb (andb (Z.leb 0 sx) (Z.leb 0 sy)) (Z.ltb sr 0))
    (andb (andb (Z.ltb sx 0) (Z.ltb sy 0)) (Z.leb 0 sr)).

(** Compute carry flag for subtraction (CMP): C = 1 when v1 >= v2 unsigned (no borrow) *)
Definition compute_c_flag_sub (v1 v2 : I32.int) : bool :=
  Z.leb (I32.unsigned v2) (I32.unsigned v1).

(** Compute overflow flag for subtraction:
    Overflow when operands have different signs and result sign differs from first operand.
    Pos - Neg -> Neg (overflow) OR Neg - Pos -> Pos (overflow) *)
Definition compute_v_flag_sub (v1 v2 : I32.int) : bool :=
  let sv1 := I32.signed v1 in
  let sv2 := I32.signed v2 in
  let sr := I32.signed (I32.sub v1 v2) in
  orb
    (andb (andb (Z.leb 0 sv1) (Z.ltb sv2 0)) (Z.ltb sr 0))
    (andb (andb (Z.ltb sv1 0) (Z.leb 0 sv2)) (Z.leb 0 sr)).

(** ** Three-operand borrow-aware flag helpers (SBCS)

    SBCS computes rn - op2 - NOT(C) and writes NZCV — the second link of the
    encoder's dual-precision i64 compare chain. The two-operand
    compute_c_flag_sub / compute_v_flag_sub cannot express the borrow-in, so
    the carry-in-aware variants below transcribe the ASL ground truth
    AddWithCarry(x, NOT(y), carry_in) (v8_base.sail:13337, quoted in
    SailArmBridge.v):

      C = "UInt(result) != unsigned_sum", i.e. carry-out of
          x + NOT(y) + carry_in, i.e. NO borrow in x - y - (1 - carry_in):
          uy + borrow <= ux;
      V = "SInt(result) != signed_sum", i.e. the 32-bit signed result differs
          from the exact signed difference sx - sy - borrow.

    Proven equal to the ASL formulation in SailArmBridge.v
    (sail_sbcs_r_flags_eq / sail_bridge_sbcs_reg); proven to collapse to the
    two-operand SUBS/CMP helpers at carry_in = true
    (sbc_flags_carry_set_c / sbc_flags_carry_set_v there). *)

Definition compute_c_flag_sbc (v1 v2 : I32.int) (carry_in : bool) : bool :=
  let borrow := if carry_in then 0 else 1 in
  Z.leb (I32.unsigned v2 + borrow) (I32.unsigned v1).

Definition compute_v_flag_sbc (v1 v2 : I32.int) (carry_in : bool) : bool :=
  let borrow := if carry_in then 0 else 1 in
  let borrow_in := if carry_in then I32.zero else I32.one in
  let exact := I32.signed v1 - I32.signed v2 - borrow in
  negb (Z.eqb (I32.signed (I32.sub (I32.sub v1 v2) borrow_in)) exact).

(** Update flags after arithmetic operation *)
Definition update_flags_arith (result : I32.int) (c v : bool) : condition_flags :=
  mkFlags
    (compute_n_flag result)
    (compute_z_flag result)
    c
    v.

(** The C flag stored by update_flags_arith is exactly its `c` argument.
    Used by the i64 ADDS/ADC + SUBS/SBC carry/borrow discharges to read the
    flag set by the low-half instruction. *)
Lemma flag_c_update_flags_arith : forall result c v,
  (update_flags_arith result c v).(flag_c) = c.
Proof.
  intros. unfold update_flags_arith. reflexivity.
Qed.

(** The remaining projections of update_flags_arith — used by the
    expansion-level I64SetCond proofs (VcrSelExpansion.v) to read the
    N/Z/V flags latched by the CMP-lo/SBCS-hi chain. *)
Lemma flag_n_update_flags_arith : forall result c v,
  (update_flags_arith result c v).(flag_n) = compute_n_flag result.
Proof.
  intros. unfold update_flags_arith. reflexivity.
Qed.

Lemma flag_z_update_flags_arith : forall result c v,
  (update_flags_arith result c v).(flag_z) = compute_z_flag result.
Proof.
  intros. unfold update_flags_arith. reflexivity.
Qed.

Lemma flag_v_update_flags_arith : forall result c v,
  (update_flags_arith result c v).(flag_v) = v.
Proof.
  intros. unfold update_flags_arith. reflexivity.
Qed.

(** ** Instruction Semantics *)

(** Execute a single ARM instruction *)
Definition exec_instr (i : arm_instr) (s : arm_state) : option arm_state :=
  match i with
  (* Arithmetic operations *)
  | ADD rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.add v1 v2 in
      Some (set_reg s rd result)

  | SUB rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.sub v1 v2 in
      Some (set_reg s rd result)

  (* ADDS: ADD setting flags from unsigned overflow.
     C flag is set iff rn + op2 overflows the 32-bit range. *)
  | ADDS rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.add v1 v2 in
      let c := compute_c_flag_add v1 v2 in
      let v := compute_v_flag_add v1 v2 result in
      let new_flags := update_flags_arith result c v in
      Some (set_flags (set_reg s rd result) new_flags)

  (* ADC: ADD with carry, reading the C flag set by a prior ADDS.
     Computes rn + op2 + C. Does not set flags itself (unlike ADCS). *)
  | ADC rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let carry_in := if s.(flags).(flag_c) then I32.one else I32.zero in
      let result := I32.add (I32.add v1 v2) carry_in in
      Some (set_reg s rd result)

  (* SUBS: SUB setting flags from unsigned borrow. *)
  | SUBS rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.sub v1 v2 in
      let c := compute_c_flag_sub v1 v2 in
      let v := compute_v_flag_sub v1 v2 in
      let new_flags := update_flags_arith result c v in
      Some (set_flags (set_reg s rd result) new_flags)

  (* SBC: SUB with carry (borrow inverted), reading the C flag set by a prior SUBS.
     Computes rn - op2 - NOT(C) = rn - op2 - 1 + C. *)
  | SBC rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let borrow_in := if s.(flags).(flag_c) then I32.zero else I32.one in
      let result := I32.sub (I32.sub v1 v2) borrow_in in
      Some (set_reg s rd result)

  (* SBCS: SBC additionally writing NZCV — same result as SBC, flags from the
     borrow-aware three-operand helpers (ASL AddWithCarry(x, NOT y, C) with
     setflags=true; bridged in SailArmBridge.v). *)
  | SBCS rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let cin := s.(flags).(flag_c) in
      let borrow_in := if cin then I32.zero else I32.one in
      let result := I32.sub (I32.sub v1 v2) borrow_in in
      let c := compute_c_flag_sbc v1 v2 cin in
      let v := compute_v_flag_sbc v1 v2 cin in
      let new_flags := update_flags_arith result c v in
      Some (set_flags (set_reg s rd result) new_flags)

  | MUL rd rn rm =>
      let v1 := get_reg s rn in
      let v2 := get_reg s rm in
      let result := I32.mul v1 v2 in
      Some (set_reg s rd result)

  | SDIV rd rn rm =>
      let v1 := get_reg s rn in
      let v2 := get_reg s rm in
      match I32.divs v1 v2 with
      | Some result => Some (set_reg s rd result)
      | None => None  (* Division by zero or overflow *)
      end

  | UDIV rd rn rm =>
      let v1 := get_reg s rn in
      let v2 := get_reg s rm in
      match I32.divu v1 v2 with
      | Some result => Some (set_reg s rd result)
      | None => None  (* Division by zero *)
      end

  | MLS rd rn rm ra =>
      (* MLS: rd = ra - (rn * rm) *)
      let vn := get_reg s rn in
      let vm := get_reg s rm in
      let va := get_reg s ra in
      let product := I32.mul vn vm in
      let result := I32.sub va product in
      Some (set_reg s rd result)

  (* Bitwise operations *)
  | AND rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.and v1 v2 in
      Some (set_reg s rd result)

  | ORR rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.or v1 v2 in
      Some (set_reg s rd result)

  | EOR rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.xor v1 v2 in
      Some (set_reg s rd result)

  | MVN rd op2 =>
      let v := eval_operand2 op2 s in
      let result := I32.repr (Z.lnot (I32.unsigned v)) in
      Some (set_reg s rd result)

  (* Shift operations — immediate *)
  | LSL rd rn shift =>
      let v := get_reg s rn in
      let shift_amt := I32.repr (Z.of_nat shift) in
      let result := I32.shl v shift_amt in
      Some (set_reg s rd result)

  | LSR rd rn shift =>
      let v := get_reg s rn in
      let shift_amt := I32.repr (Z.of_nat shift) in
      let result := I32.shru v shift_amt in
      Some (set_reg s rd result)

  | ASR rd rn shift =>
      let v := get_reg s rn in
      let shift_amt := I32.repr (Z.of_nat shift) in
      let result := I32.shrs v shift_amt in
      Some (set_reg s rd result)

  | ROR rd rn shift =>
      let v := get_reg s rn in
      let shift_amt := I32.repr (Z.of_nat shift) in
      let result := I32.rotr v shift_amt in
      Some (set_reg s rd result)

  (* Shift operations — register (shift amount in Rm, masked to 0-31 by I32.shl etc.) *)
  | LSL_reg rd rn rm =>
      let v := get_reg s rn in
      let shift_amt := get_reg s rm in
      Some (set_reg s rd (I32.shl v shift_amt))

  | LSR_reg rd rn rm =>
      let v := get_reg s rn in
      let shift_amt := get_reg s rm in
      Some (set_reg s rd (I32.shru v shift_amt))

  | ASR_reg rd rn rm =>
      let v := get_reg s rn in
      let shift_amt := get_reg s rm in
      Some (set_reg s rd (I32.shrs v shift_amt))

  | ROR_reg rd rn rm =>
      let v := get_reg s rn in
      let shift_amt := get_reg s rm in
      Some (set_reg s rd (I32.rotr v shift_amt))

  (* Reverse subtract: RSB Rd, Rn, Op2 = Op2 - Rn *)
  | RSB rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      Some (set_reg s rd (I32.sub v2 v1))

  (* Move operations *)
  | MOV rd op2 =>
      let v := eval_operand2 op2 s in
      Some (set_reg s rd v)

  | MOVEQ rd op2 =>
      (* Conditional move: only move if Z flag is set (equal) *)
      if s.(flags).(flag_z) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s  (* No operation if condition false *)

  | MOVNE rd op2 =>
      (* Conditional move: only move if Z flag is clear (not equal) *)
      if s.(flags).(flag_z) then
        Some s  (* No operation if condition false *)
      else
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)

  | MOVLT rd op2 =>
      (* Less than (signed): N != V *)
      if Bool.eqb s.(flags).(flag_n) s.(flags).(flag_v) then
        Some s
      else
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)

  | MOVLE rd op2 =>
      (* Less or equal (signed): Z set OR N != V *)
      if s.(flags).(flag_z) || negb (Bool.eqb s.(flags).(flag_n) s.(flags).(flag_v)) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s

  | MOVGT rd op2 =>
      (* Greater than (signed): Z clear AND N == V *)
      if negb s.(flags).(flag_z) && Bool.eqb s.(flags).(flag_n) s.(flags).(flag_v) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s

  | MOVGE rd op2 =>
      (* Greater or equal (signed): N == V *)
      if Bool.eqb s.(flags).(flag_n) s.(flags).(flag_v) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s

  | MOVLO rd op2 =>
      (* Lower (unsigned): C clear *)
      if s.(flags).(flag_c) then
        Some s
      else
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)

  | MOVLS rd op2 =>
      (* Lower or same (unsigned): C clear OR Z set *)
      if negb s.(flags).(flag_c) || s.(flags).(flag_z) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s

  | MOVHI rd op2 =>
      (* Higher (unsigned): C set AND Z clear *)
      if s.(flags).(flag_c) && negb s.(flags).(flag_z) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s

  | MOVHS rd op2 =>
      (* Higher or same (unsigned): C set *)
      if s.(flags).(flag_c) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s

  | MOVW rd imm =>
      (* Move 16-bit immediate to lower 16 bits *)
      Some (set_reg s rd imm)

  | MOVT rd imm =>
      (* Move 16-bit immediate to upper 16 bits *)
      let current := get_reg s rd in
      let lower := I32.and current (I32.repr 0xFFFF) in
      let upper := I32.shl imm (I32.repr 16) in
      let result := I32.or lower upper in
      Some (set_reg s rd result)

  (* Comparison *)
  | CMP rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.sub v1 v2 in
      (* Update flags but don't write to register *)
      let c := compute_c_flag_sub v1 v2 in
      let v := compute_v_flag_sub v1 v2 in
      let new_flags := update_flags_arith result c v in
      Some (set_flags s new_flags)

  (* Conditionally-executed CMP (CMPEQ etc.): executes the compare — and
     REWRITES all four NZCV flags — only when the condition holds on the
     CURRENT flags; otherwise the flags (and everything else) are untouched.
     Generalizes conditional execution beyond the MOVcc family. *)
  | CMPCond cond rn op2 =>
      if eval_condition cond s.(flags) then
        let v1 := get_reg s rn in
        let v2 := eval_operand2 op2 s in
        let result := I32.sub v1 v2 in
        let c := compute_c_flag_sub v1 v2 in
        let v := compute_v_flag_sub v1 v2 in
        let new_flags := update_flags_arith result c v in
        Some (set_flags s new_flags)
      else
        Some s

  (* Bit manipulation — axiomatized via I32.clz/rbit/popcnt *)
  | CLZ rd rm =>
      let v := get_reg s rm in
      Some (set_reg s rd (I32.clz v))

  | RBIT rd rm =>
      let v := get_reg s rm in
      Some (set_reg s rd (I32.rbit v))

  | POPCNT rd rm =>
      let v := get_reg s rm in
      Some (set_reg s rd (I32.popcnt v))

  (* Memory operations *)
  | LDR rd rn offset =>
      let base := get_reg s rn in
      let addr := I32.add base (I32.repr offset) in
      let value := load_mem s (I32.signed addr) in
      Some (set_reg s rd value)

  | STR rd rn offset =>
      let base := get_reg s rn in
      let addr := I32.add base (I32.repr offset) in
      let value := get_reg s rd in
      Some (store_mem s (I32.signed addr) value)

  (* Trap instruction — always fails *)
  | UDF _ => None

  (* CMN: compare negated — sets flags based on addition (rn + op2) *)
  | CMN rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.add v1 v2 in
      let c := compute_c_flag_add v1 v2 in
      let v := compute_v_flag_add v1 v2 result in
      let new_flags := update_flags_arith result c v in
      Some (set_flags s new_flags)

  (* BCondOffset: conditional branch with instruction offset.

     exec_instr is a pure state transformer with no program-counter view, so
     it cannot express the jump; the branch is taken by the PC-indexed
     executor exec_program_pc / exec_program_br below, which intercepts
     BCondOffset BEFORE delegating to exec_instr. Within exec_instr (i.e.
     within the legacy flat exec_program) BCondOffset remains a state no-op —
     this preserves every proof written against the flat executor.

     The trap-guarded div/rem sequences (CMP + BCondOffset + UDF + SDIV/UDIV)
     are proven against exec_program_br, where the taken branch skips the
     UDF (CorrectnessI32.v, the former #73 T3 admits). *)
  | BCondOffset _cond _offset =>
      Some s  (* No-op at the instruction level; branched in exec_program_pc *)

  (* Control flow - simplified *)
  | B offset =>
      (* Branch: update PC *)
      let current_pc := get_reg s PC in
      let new_pc := I32.add current_pc (I32.repr offset) in
      Some (set_reg s PC new_pc)

  | BL offset =>
      (* Branch with link: save return address in LR *)
      let current_pc := get_reg s PC in
      let return_addr := I32.add current_pc (I32.repr 4) in
      let s' := set_reg s LR return_addr in
      let new_pc := I32.add current_pc (I32.repr offset) in
      Some (set_reg s' PC new_pc)

  | BX rm =>
      (* Branch and exchange *)
      let target := get_reg s rm in
      Some (set_reg s PC target)

  (* VFP F32 arithmetic operations *)
  | VADD_F32 sd sn sm =>
      let vn := get_vfp_reg s sn in
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_add_bits vn vm))

  | VSUB_F32 sd sn sm =>
      let vn := get_vfp_reg s sn in
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_sub_bits vn vm))

  | VMUL_F32 sd sn sm =>
      let vn := get_vfp_reg s sn in
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_mul_bits vn vm))

  | VDIV_F32 sd sn sm =>
      let vn := get_vfp_reg s sn in
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_div_bits vn vm))

  | VSQRT_F32 sd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_sqrt_bits vm))

  | VABS_F32 sd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_abs_bits vm))

  | VNEG_F32 sd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_neg_bits vm))

  (* VFP F64 arithmetic operations *)
  | VADD_F64 dd dn dm =>
      let vn := get_vfp_reg s dn in
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_add_bits vn vm))

  | VSUB_F64 dd dn dm =>
      let vn := get_vfp_reg s dn in
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_sub_bits vn vm))

  | VMUL_F64 dd dn dm =>
      let vn := get_vfp_reg s dn in
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_mul_bits vn vm))

  | VDIV_F64 dd dn dm =>
      let vn := get_vfp_reg s dn in
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_div_bits vn vm))

  | VSQRT_F64 dd dm =>
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_sqrt_bits vm))

  | VABS_F64 dd dm =>
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_abs_bits vm))

  | VNEG_F64 dd dm =>
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_neg_bits vm))

  (* VFP comparison operations — update condition flags via VMRS APSR_nzcv, FPSCR *)
  | VCMP_F32 sn sm =>
      let vn := get_vfp_reg s sn in
      let vm := get_vfp_reg s sm in
      Some (set_flags s (f32_compare_flags vn vm))

  | VCMP_F64 dn dm =>
      let vn := get_vfp_reg s dn in
      let vm := get_vfp_reg s dm in
      Some (set_flags s (f64_compare_flags vn vm))

  (* VFP conversion operations *)
  | VCVT_F32_F64 sd dm =>
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s sd (cvt_f64_to_f32_bits vm))

  | VCVT_F64_F32 dd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s dd (cvt_f32_to_f64_bits vm))

  | VCVT_S32_F32 sd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (cvt_f32_to_s32_bits vm))

  | VCVT_F32_S32 sd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (cvt_s32_to_f32_bits vm))

  (* VFP move operations *)
  | VMOV sd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd vm)

  | VMOV_ARM_TO_VFP sd rm =>
      let vm := get_reg s rm in
      Some (set_vfp_reg s sd vm)

  | VMOV_VFP_TO_ARM rd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_reg s rd vm)

  (* VFP memory operations *)
  | VLDR_F32 sd rn offset =>
      let base := get_reg s rn in
      let addr := I32.add base (I32.repr offset) in
      let value := load_mem s (I32.signed addr) in
      Some (set_vfp_reg s sd value)

  | VSTR_F32 sd rn offset =>
      let base := get_reg s rn in
      let addr := I32.add base (I32.repr offset) in
      let value := get_vfp_reg s sd in
      Some (store_mem s (I32.signed addr) value)

  | VLDR_F64 dd rn offset =>
      let base := get_reg s rn in
      let addr := I32.add base (I32.repr offset) in
      let value := load_mem s (I32.signed addr) in
      Some (set_vfp_reg s dd value)

  | VSTR_F64 dd rn offset =>
      let base := get_reg s rn in
      let addr := I32.add base (I32.repr offset) in
      let value := get_vfp_reg s dd in
      Some (store_mem s (I32.signed addr) value)

  (* ===== i64 pseudo-op semantics =====
     Each pseudo-op reads the relevant register pair(s) and writes the axiomatized
     result(s) into the destination pair. These are existence-level semantics
     suitable for T2 proofs; T1 lifting requires replacing the bit-pattern axioms
     with concrete I64.* operations (umbrella issue #147 v0.8.0 lift queue). *)

  | I64MulPseudo rdlo rdhi rnlo rnhi rmlo rmhi =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      let vmlo := get_reg s rmlo in
      let vmhi := get_reg s rmhi in
      let lo := i64_mul_lo_bits vnlo vnhi vmlo vmhi in
      let hi := i64_mul_hi_bits vnlo vnhi vmlo vmhi in
      Some (set_reg (set_reg s rdlo lo) rdhi hi)

  | I64ShlPseudo rdlo rdhi rnlo rnhi rmlo _rmhi =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      let cnt  := get_reg s rmlo in
      let lo := i64_shl_lo_bits vnlo vnhi cnt in
      let hi := i64_shl_hi_bits vnlo vnhi cnt in
      Some (set_reg (set_reg s rdlo lo) rdhi hi)

  | I64ShrUPseudo rdlo rdhi rnlo rnhi rmlo _rmhi =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      let cnt  := get_reg s rmlo in
      let lo := i64_shru_lo_bits vnlo vnhi cnt in
      let hi := i64_shru_hi_bits vnlo vnhi cnt in
      Some (set_reg (set_reg s rdlo lo) rdhi hi)

  | I64ShrSPseudo rdlo rdhi rnlo rnhi rmlo _rmhi =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      let cnt  := get_reg s rmlo in
      let lo := i64_shrs_lo_bits vnlo vnhi cnt in
      let hi := i64_shrs_hi_bits vnlo vnhi cnt in
      Some (set_reg (set_reg s rdlo lo) rdhi hi)

  | I64RotlPseudo rdlo rdhi rnlo rnhi shift =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      let cnt  := get_reg s shift in
      let lo := i64_rotl_lo_bits vnlo vnhi cnt in
      let hi := i64_rotl_hi_bits vnlo vnhi cnt in
      Some (set_reg (set_reg s rdlo lo) rdhi hi)

  | I64RotrPseudo rdlo rdhi rnlo rnhi shift =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      let cnt  := get_reg s shift in
      let lo := i64_rotr_lo_bits vnlo vnhi cnt in
      let hi := i64_rotr_hi_bits vnlo vnhi cnt in
      Some (set_reg (set_reg s rdlo lo) rdhi hi)

  | I64ClzPseudo rd rnlo rnhi =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      Some (set_reg s rd (i64_clz_bits vnlo vnhi))

  | I64CtzPseudo rd rnlo rnhi =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      Some (set_reg s rd (i64_ctz_bits vnlo vnhi))

  | I64PopcntPseudo rd rnlo rnhi =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      Some (set_reg s rd (i64_popcnt_bits vnlo vnhi))

  | I64SetCond rd rnlo rnhi rmlo rmhi cond =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      let vmlo := get_reg s rmlo in
      let vmhi := get_reg s rmhi in
      Some (set_reg s rd (i64_setcond_bits vnlo vnhi vmlo vmhi cond))

  | I64SetCondZ rd rnlo rnhi =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      Some (set_reg s rd (i64_setcondz_bits vnlo vnhi))

  | I64DivSPseudo rdlo rdhi rnlo rnhi rmlo rmhi =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      let vmlo := get_reg s rmlo in
      let vmhi := get_reg s rmhi in
      match i64_divs_pair vnlo vnhi vmlo vmhi with
      | Some (lo, hi) => Some (set_reg (set_reg s rdlo lo) rdhi hi)
      | None => None  (* trap: divide by zero / signed overflow *)
      end

  | I64DivUPseudo rdlo rdhi rnlo rnhi rmlo rmhi =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      let vmlo := get_reg s rmlo in
      let vmhi := get_reg s rmhi in
      match i64_divu_pair vnlo vnhi vmlo vmhi with
      | Some (lo, hi) => Some (set_reg (set_reg s rdlo lo) rdhi hi)
      | None => None  (* trap: divide by zero *)
      end

  | I64RemSPseudo rdlo rdhi rnlo rnhi rmlo rmhi =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      let vmlo := get_reg s rmlo in
      let vmhi := get_reg s rmhi in
      match i64_rems_pair vnlo vnhi vmlo vmhi with
      | Some (lo, hi) => Some (set_reg (set_reg s rdlo lo) rdhi hi)
      | None => None
      end

  | I64RemUPseudo rdlo rdhi rnlo rnhi rmlo rmhi =>
      let vnlo := get_reg s rnlo in
      let vnhi := get_reg s rnhi in
      let vmlo := get_reg s rmlo in
      let vmhi := get_reg s rmhi in
      match i64_remu_pair vnlo vnhi vmlo vmhi with
      | Some (lo, hi) => Some (set_reg (set_reg s rdlo lo) rdhi hi)
      | None => None
      end

  | I64ConstPseudo rdlo rdhi v =>
      Some (set_reg (set_reg s rdlo (i64_const_lo v)) rdhi (i64_const_hi v))

  | I64ExtendI32SPseudo rdlo rdhi rn =>
      let v := get_reg s rn in
      (* Low half is rn; high half is sign-extension axiom *)
      Some (set_reg (set_reg s rdlo v) rdhi (i64_extend_s_hi v))

  | I64ExtendI32UPseudo rdlo rdhi rn =>
      let v := get_reg s rn in
      (* Low half is rn; high half is zero *)
      Some (set_reg (set_reg s rdlo v) rdhi I32.zero)

  | I32WrapI64Pseudo rd rnlo =>
      (* Keeps low half in rd; drops high half *)
      let v := get_reg s rnlo in
      Some (set_reg s rd v)

  | I64LoadPseudo rdlo rdhi addr offset =>
      let base := get_reg s addr in
      let a := I32.signed (I32.add base (I32.repr offset)) in
      Some (set_reg (set_reg s rdlo (i64_load_lo s.(mem) a)) rdhi (i64_load_hi s.(mem) a))

  | I64StorePseudo rnlo rnhi addr offset =>
      let base := get_reg s addr in
      let a := I32.signed (I32.add base (I32.repr offset)) in
      let lo := get_reg s rnlo in
      let hi := get_reg s rnhi in
      Some (store_mem (store_mem s a lo) (a + 4) hi)
  end.

(** Execute a sequence of instructions *)
Fixpoint exec_program (prog : list arm_instr) (s : arm_state) : option arm_state :=
  match prog with
  | [] => Some s
  | i :: rest =>
      match exec_instr i s with
      | Some s' => exec_program rest s'
      | None => None
      end
  end.

(** ** PC-indexed bounded executor — BCondOffset takes branches

    The flat [exec_program] above executes a list sequentially and cannot
    skip instructions, which is why [BCondOffset] is a no-op there and the
    trap-guarded div/rem proofs were T3 admits (#73). [exec_program_pc] is
    the step-indexed (fuel-bounded) executor with an explicit instruction
    index:

      - [nth_error prog pc = None] — the pc ran off the end: the program
        completed, return the current state;
      - [BCondOffset cond off] — if [cond] holds on the current flags, jump
        to [pc + 1 + off] (skipping [off] instructions); otherwise fall
        through to [pc + 1]. The instruction itself never changes the state.
      - any other instruction — delegate to [exec_instr], advance to
        [pc + 1].

    Fuel discipline: every step advances [pc] by at least 1 ([Z.to_nat] of a
    negative offset is 0, so even a malformed backward branch falls through
    forward), so [S (length prog)] fuel always suffices from pc = 0 — that is
    what [exec_program_br] supplies. Compilation.v only emits forward
    (skip-ahead) offsets. *)

Fixpoint exec_program_pc (fuel : nat) (prog : list arm_instr) (pc : nat)
    (s : arm_state) : option arm_state :=
  match fuel with
  | O => None  (* out of fuel — cannot happen with exec_program_br's budget *)
  | S fuel' =>
      match nth_error prog pc with
      | None => Some s
      | Some (BCondOffset cond off) =>
          let pc' := if eval_condition cond s.(flags)
                     then (pc + 1 + Z.to_nat off)%nat
                     else (pc + 1)%nat in
          exec_program_pc fuel' prog pc' s
      | Some i =>
          match exec_instr i s with
          | Some s' => exec_program_pc fuel' prog (pc + 1)%nat s'
          | None => None
          end
      end
  end.

(** The branch-taking program executor: run from index 0 with sufficient
    fuel. This is the executor the div/rem trap-guard theorems use. *)
Definition exec_program_br (prog : list arm_instr) (s : arm_state)
    : option arm_state :=
  exec_program_pc (S (length prog)) prog 0 s.

(** ** Properties *)

(** Determinacy: executing an instruction produces at most one result *)
Theorem exec_instr_deterministic : forall i s s1 s2,
  exec_instr i s = Some s1 ->
  exec_instr i s = Some s2 ->
  s1 = s2.
Proof.
  intros i s s1 s2 H1 H2.
  rewrite H1 in H2.
  injection H2. auto.
Qed.

(** ADD is commutative in the operands *)
Theorem add_commutative : forall rd rn rm s,
  exec_instr (ADD rd rn (Reg rm)) s =
  exec_instr (ADD rd rm (Reg rn)) s.
Proof.
  intros. simpl.
  unfold eval_operand2.
  rewrite I32.add_commut.
  reflexivity.
Qed.

(** Setting a register doesn't affect other registers *)
Theorem exec_preserves_other_regs : forall rd rn rm s r,
  r <> rd ->
  match exec_instr (ADD rd rn (Reg rm)) s with
  | Some s' => get_reg s' r = get_reg s r
  | None => True
  end.
Proof.
  intros rd rn rm s r Hneq. simpl. unfold eval_operand2.
  apply get_set_reg_neq. auto.
Qed.

(** ADD with zero normalizes the register value *)
Theorem add_zero_right : forall rd rn s,
  exec_instr (ADD rd rn (Imm I32.zero)) s =
  Some (set_reg s rd (I32.repr (get_reg s rn))).
Proof.
  intros. simpl. unfold eval_operand2.
  rewrite I32.add_zero. reflexivity.
Qed.

(** MOV transfers the value correctly *)
Theorem mov_correct : forall rd rs s,
  exec_instr (MOV rd (Reg rs)) s =
  Some (set_reg s rd (get_reg s rs)).
Proof.
  intros. simpl. reflexivity.
Qed.

(** Executing an empty program doesn't change state *)
Theorem exec_program_nil : forall s,
  exec_program (@nil arm_instr) s = Some s.
Proof.
  intros. reflexivity.
Qed.

(** Executing programs is associative (sequential composition) *)
Theorem exec_program_app : forall p1 p2 s,
  exec_program (p1 ++ p2) s =
  match exec_program p1 s with
  | Some s' => exec_program p2 s'
  | None => None
  end.
Proof.
  induction p1; intros.
  - simpl. reflexivity.
  - simpl. destruct (exec_instr a s) eqn:E.
    + apply IHp1.
    + reflexivity.
Qed.
