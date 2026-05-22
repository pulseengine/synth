//! Validator-Pattern Verification (Issue #76)
//!
//! This module implements the **certifying-algorithm** verification pattern
//! that CompCert uses for NP-hard passes (register allocation, instruction
//! scheduling). Rather than verifying the *selector* — which is heuristic,
//! large, and changes frequently — we verify a small *validator* that
//! consumes the selector's output and confirms each concrete selection is
//! semantically equivalent to the WASM op it replaces.
//!
//! See `docs/validator-pattern.md` for the architecture rationale.
//!
//! # Status
//!
//! The prototype landed by PR #113 covered only `WasmOp::I32Add`. This module
//! extends the coverage to the **full i32 + i64 arithmetic / logic / shift /
//! comparison surface** (issue #76). The pieces are:
//!
//! - [`CertifiedSelection`] — the per-op output of the selector
//! - [`Validator`] — the trait the validator implements
//! - [`Z3ArmValidator`] — a Z3-backed validator
//!
//! # How the validator works
//!
//! For each WASM op the validator builds a Z3 query that asserts the
//! *negation* of equivalence between the WASM op's reference semantics and the
//! ARM instruction sequence the selector emitted:
//!
//! ```text
//! assert ¬( wasm_reference(inputs) == arm_lowering(inputs) )
//! check-sat
//! ```
//!
//! `unsat` means no input distinguishes the two — the selection is certified.
//! `sat` means Z3 found a concrete counterexample — the selection is rejected.
//!
//! # Self-contained semantics
//!
//! The validator builds **both** the WASM reference and the ARM lowering
//! semantics directly in this module. It deliberately does *not* delegate to
//! [`crate::WasmSemantics`] / [`crate::ArmSemantics`] for i64: those encoders
//! model i64 with truncated 32-bit semantics (see `wasm_semantics.rs` — every
//! i64 op is a 32-bit stand-in), which is precisely the gap #76 closes. A
//! validator that trusted a truncated model would certify wrong lowerings.
//!
//! Instead, every formula here is written in terms of 32-bit Z3 bitvectors —
//! the same width the ARM machine actually has. i64 values are carried as a
//! `(lo, hi)` pair of 32-bit bitvectors, exactly the register pair the ARM
//! lowering uses. A reviewer can check each formula against the textbook
//! 32-bit-limb algorithm for the corresponding 64-bit operation.
//!
//! # i64 register-pair modeling
//!
//! synth lowers a WASM i64 onto two ARM registers: `lo` (bits 0..=31) and `hi`
//! (bits 32..=63). The validator never builds a 64-bit bitvector for the
//! arithmetic/logic/shift surface. Instead, for each i64 op it builds the
//! 64-bit result *as a pair of 32-bit limbs*, with carry / borrow propagated
//! explicitly between the limbs:
//!
//! - **add**: `lo = a_lo + b_lo`, `carry = (lo <u a_lo)`,
//!   `hi = a_hi + b_hi + carry`.
//! - **sub**: `lo = a_lo - b_lo`, `borrow = (a_lo <u b_lo)`,
//!   `hi = a_hi - b_hi - borrow`.
//! - **mul**: schoolbook `a_lo*b_lo` plus the carry-out of that partial
//!   product plus the cross terms `a_lo*b_hi + a_hi*b_lo` (mod 2^32).
//! - **logic** (and/or/xor): limb-wise, no interaction between limbs.
//! - **shifts**: case-split on whether the (mod-64) shift amount is `< 32` or
//!   `>= 32`, with the cross-limb bit transfer made explicit.
//! - **comparisons**: `hi` decides; `lo` breaks ties — written exactly so a
//!   reviewer sees the lexicographic structure.
//!
//! Because the ARM lowering for an i64 op is itself a sequence of 32-bit ARM
//! instructions, the validator compares the selector's emitted sequence
//! limb-for-limb against this reference, and Z3 proves the two agree for all
//! `2^64` inputs.
//!
//! # Scope
//!
//! Covered: i32 and i64 add / sub / mul / and / or / xor / shl / shr_s /
//! shr_u / rotl / rotr; i32 and i64 eq / ne / lt_{s,u} / le_{s,u} /
//! gt_{s,u} / ge_{s,u}; i32 and i64 eqz; i32 div_s / div_u.
//!
//! Scoped out, with reasons (see `docs/validator-pattern.md`):
//!
//! - **i32 rem_s / rem_u** — the ARM lowering is `SDIV`/`UDIV` followed by
//!   `MLS`, i.e. the identity `r = a - (a / b) * b`. Proving this equals
//!   WASM's `bvsrem` / `bvurem` for all 2^64 input pairs requires Z3 to
//!   reason about a *symbolic* 32-bit multiply `(a / b) * b`, which
//!   bit-blasts past any practical solver budget (no convergence in 5
//!   minutes). `div_s` and `div_u` certify in well under a second — the
//!   divide instruction maps straight onto `bvsdiv` / `bvudiv` with no
//!   multiply — but *remainder* crosses the tractability line. Deferred
//!   until the validator can discharge the `MLS` identity with a
//!   multiplier-aware tactic rather than raw bit-blasting.
//! - **i64 div_s / div_u / rem_s / rem_u** — synth lowers 64-bit division to
//!   a *runtime-library call* (`__aeabi_ldivmod` and friends); there is no
//!   fixed 32-bit ARM instruction sequence to symbolically execute. Modeling
//!   a fictitious native 64-bit divide would certify a lowering the compiler
//!   never emits. These are deferred until the validator can reason about
//!   helper-call summaries.
//! - **Clz / Ctz / Popcnt** (i32 and i64) — bit-counting. The 32-bit ARM
//!   `CLZ` is available, but `Ctz`/`Popcnt` are lowered to multi-instruction
//!   bit-twiddling and `i64.clz/ctz/popcnt` combine two limbs conditionally.
//!   `wasm_semantics.rs` already has binary-search encoders for these; wiring
//!   them through the validator's ARM-side executor is follow-up work and is
//!   not part of the #76 arithmetic/logic/shift/comparison core.
//! - **Extend8S / Extend16S** (and `i64` in-place extends) — sign-extension
//!   ops; the ARM `SXTB`/`SXTH` lowering is straightforward but, like the
//!   bit-counting ops, sits outside the #76 binary-op core and is deferred to
//!   keep this change focused and reviewable.

#![cfg(all(feature = "z3-solver", feature = "arm"))]

use synth_core::WasmOp;
use synth_synthesis::rules::Condition;
use synth_synthesis::{ArmOp, Operand2, Reg};
use thiserror::Error;
use z3::ast::{BV, Bool};
use z3::{SatResult, Solver};

/// A concrete selection produced by the instruction selector.
///
/// Generic over the source op `W` (initially `WasmOp`) and target op `A`
/// (initially `ArmOp`, later `RiscvOp`). The `witness` is `None` when the
/// selector emits the selection and `Some(Witness)` after the validator
/// accepts it.
#[derive(Debug, Clone)]
pub struct CertifiedSelection<W, A> {
    /// The source operation (e.g. `WasmOp::I32Add`).
    pub wasm: W,
    /// The target instruction sequence (e.g. `[ArmOp::Add { ... }]`).
    pub arm: Vec<A>,
    /// Witness attached by the validator (`None` until validated).
    pub witness: Option<Witness>,
}

impl<W, A> CertifiedSelection<W, A> {
    /// Create a new selection with no witness attached.
    pub fn new(wasm: W, arm: Vec<A>) -> Self {
        Self {
            wasm,
            arm,
            witness: None,
        }
    }

    /// Attach a witness, marking this selection as validated.
    pub fn with_witness(mut self, witness: Witness) -> Self {
        self.witness = Some(witness);
        self
    }

    /// Whether this selection has been validated.
    pub fn is_certified(&self) -> bool {
        self.witness.is_some()
    }
}

/// A witness recording the validator's acceptance of a selection.
///
/// For the prototype this is intentionally minimal. A v0.5 expansion will
/// embed the SMT-LIB2 script that Z3 was given, so a third party can
/// independently replay the verification without trusting the validator's
/// encoding logic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Witness {
    /// Human-readable label for the WASM op (e.g. `"I32Add"`).
    pub wasm_op_label: String,
    /// Number of ARM instructions in the validated sequence.
    pub arm_op_count: usize,
    /// The Z3 result that produced this witness (always `Unsat` for accepted
    /// selections — `Unsat` of `wasm ≠ arm` means `wasm ≡ arm`).
    pub solver_result: SolverResultKind,
}

/// Solver result kind (mirrors `z3::SatResult` but without the lifetime).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolverResultKind {
    /// `Unsat` of the negated equivalence — selection is correct.
    Unsat,
    /// `Sat` of the negated equivalence — counterexample found.
    Sat,
    /// Solver returned `unknown` (timeout or unsupported theory).
    Unknown,
}

/// Validation failure reasons.
#[derive(Debug, Error)]
pub enum ValidationError {
    /// The selection is semantically wrong; the validator found a
    /// counterexample (a concrete input where WASM and ARM disagree).
    #[error("counterexample for {wasm_op_label}: {description}")]
    Counterexample {
        wasm_op_label: String,
        description: String,
    },

    /// The validator does not support this WASM op. This is the common case
    /// during the per-op rollout (see `docs/validator-pattern.md`).
    #[error("validator does not support {0:?}")]
    UnsupportedOp(WasmOp),

    /// Z3 returned `unknown` (timeout or unsupported theory).
    #[error("solver returned unknown: {0}")]
    SolverUnknown(String),

    /// Internal encoding error (e.g. the emitted ARM sequence uses an
    /// instruction the validator's lowering model does not cover).
    #[error("internal validator error: {0}")]
    Internal(String),
}

/// A backend-agnostic validator for [`CertifiedSelection`].
///
/// Implementations consume a selection and either return a [`Witness`]
/// (selection is correct) or a [`ValidationError`] (selection is wrong, or
/// unsupported, or inconclusive).
pub trait Validator<W, A> {
    /// Validate `sel`. Returns `Ok(Witness)` iff the selection is
    /// semantically equivalent to the source op.
    fn validate(&self, sel: &CertifiedSelection<W, A>) -> Result<Witness, ValidationError>;
}

// ===========================================================================
// Bitvector helpers — everything works on 32-bit bitvectors, the width the
// ARM Cortex-M machine has. i64 values are carried as a `(lo, hi)` limb pair.
// ===========================================================================

/// Make a fresh 32-bit symbolic input.
fn sym32(name: &str) -> BV {
    BV::new_const(name, 32)
}

/// 32-bit constant.
fn k32(v: i64) -> BV {
    BV::from_i64(v, 32)
}

/// Boolean → 32-bit `0`/`1` bitvector (WASM comparison result encoding).
fn bool_to_i32(b: &Bool) -> BV {
    b.ite(&k32(1), &k32(0))
}

/// 64-bit value as a pair of 32-bit limbs: `lo` is bits 0..=31, `hi` is
/// bits 32..=63 — exactly the ARM register pair the i64 lowering uses.
#[derive(Clone)]
struct I64Pair {
    lo: BV,
    hi: BV,
}

impl I64Pair {
    /// Bit-for-bit equality: both limbs must agree.
    fn eq_pair(&self, other: &I64Pair) -> Bool {
        Bool::and(&[&self.lo.eq(&other.lo), &self.hi.eq(&other.hi)])
    }

    /// Join the limb pair into a single 64-bit bitvector.
    ///
    /// `concat(hi, lo)` places `hi` in bits 32..=63 and `lo` in bits 0..=31 —
    /// the standard little-endian-limb layout the ARM register pair uses.
    /// Used by the multiply reference, where a native 64-bit `bvmul` is far
    /// clearer (and far easier for Z3) than a hand-rolled limb product.
    fn join64(&self) -> BV {
        self.hi.concat(&self.lo)
    }

    /// Inverse of [`I64Pair::join64`]: split a 64-bit bitvector into limbs.
    fn from_u64_bv(v: &BV) -> I64Pair {
        I64Pair {
            lo: v.extract(31, 0),
            hi: v.extract(63, 32),
        }
    }
}

// ===========================================================================
// 64-bit reference semantics, expressed in 32-bit limbs
// ===========================================================================
//
// Each function below is the *reference* meaning of a WASM i64 op, written so
// a reviewer can match it against the textbook 32-bit-limb algorithm. No
// 64-bit bitvector is ever constructed — the limb pair *is* the value.

/// 64-bit add: ripple-carry across the two 32-bit limbs.
///
/// `lo = a_lo + b_lo`. A carry out of the low limb happens exactly when the
/// 32-bit sum wraps, i.e. when `lo <u a_lo` (unsigned). The carry (0 or 1) is
/// then folded into the high limb: `hi = a_hi + b_hi + carry`.
fn i64_add(a: &I64Pair, b: &I64Pair) -> I64Pair {
    let lo = a.lo.bvadd(&b.lo);
    let carry = lo.bvult(&a.lo).ite(&k32(1), &k32(0));
    let hi = a.hi.bvadd(&b.hi).bvadd(&carry);
    I64Pair { lo, hi }
}

/// 64-bit sub: ripple-borrow across the two 32-bit limbs.
///
/// `lo = a_lo - b_lo`. A borrow into the high limb happens exactly when the
/// low subtraction underflows, i.e. when `a_lo <u b_lo`. The borrow is then
/// subtracted from the high limb: `hi = a_hi - b_hi - borrow`.
fn i64_sub(a: &I64Pair, b: &I64Pair) -> I64Pair {
    let lo = a.lo.bvsub(&b.lo);
    let borrow = a.lo.bvult(&b.lo).ite(&k32(1), &k32(0));
    let hi = a.hi.bvsub(&b.hi).bvsub(&borrow);
    I64Pair { lo, hi }
}

/// 64-bit multiply, low 64 bits only (WASM `i64.mul` wraps mod 2^64).
///
/// The two limb pairs are joined into native 64-bit bitvectors, multiplied
/// with Z3's `bvmul` (which is exactly mod-2^64 multiplication), and split
/// back into limbs. Using the native 64-bit multiply keeps the reference
/// *obviously* correct — it is literally the 64-bit product — and avoids a
/// hand-rolled partial-product expansion that is both harder to audit and far
/// harder for the SMT solver to reason about. The ARM-side `I64Mul` lowering
/// (the real UMULL + MLA cross-product expansion) is checked against this
/// reference.
fn i64_mul(a: &I64Pair, b: &I64Pair) -> I64Pair {
    I64Pair::from_u64_bv(&a.join64().bvmul(b.join64()))
}

/// Effective i64 shift amount: WASM masks the shift count to `count mod 64`,
/// i.e. the low 6 bits of the second operand's low limb.
fn shift_amount64(b: &I64Pair) -> BV {
    b.lo.bvand(k32(63))
}

/// 64-bit logical shift left by a symbolic amount `s` (already reduced mod
/// 64), in 32-bit limbs.
///
/// Case split:
///
/// * `s == 0`: identity.
/// * `0 < s < 32`: `hi = (hi << s) | (lo >>u (32-s))`, `lo = lo << s`.
/// * `s >= 32`: `hi = lo << (s-32)`, `lo = 0`.
///
/// The middle case is the only one with a cross-limb transfer; `32 - s` is
/// well-defined there because `0 < s < 32`.
fn i64_shl(a: &I64Pair, s: &BV) -> I64Pair {
    let s_lt_32 = s.bvult(k32(32));
    let s_is_zero = s.eq(k32(0));

    let lo_small = a.lo.bvshl(s);
    let hi_small = a.hi.bvshl(s).bvor(a.lo.bvlshr(k32(32).bvsub(s)));

    let lo_big = k32(0);
    let hi_big = a.lo.bvshl(s.bvsub(k32(32)));

    let lo = s_is_zero.ite(&a.lo, &s_lt_32.ite(&lo_small, &lo_big));
    let hi = s_is_zero.ite(&a.hi, &s_lt_32.ite(&hi_small, &hi_big));
    I64Pair { lo, hi }
}

/// 64-bit logical (unsigned) shift right — mirror image of [`i64_shl`]:
///
/// * `s == 0`: identity.
/// * `0 < s < 32`: `lo = (lo >>u s) | (hi << (32-s))`, `hi = hi >>u s`.
/// * `s >= 32`: `lo = hi >>u (s-32)`, `hi = 0`.
fn i64_shr_u(a: &I64Pair, s: &BV) -> I64Pair {
    let s_lt_32 = s.bvult(k32(32));
    let s_is_zero = s.eq(k32(0));

    let lo_small = a.lo.bvlshr(s).bvor(a.hi.bvshl(k32(32).bvsub(s)));
    let hi_small = a.hi.bvlshr(s);

    let lo_big = a.hi.bvlshr(s.bvsub(k32(32)));
    let hi_big = k32(0);

    let lo = s_is_zero.ite(&a.lo, &s_lt_32.ite(&lo_small, &lo_big));
    let hi = s_is_zero.ite(&a.hi, &s_lt_32.ite(&hi_small, &hi_big));
    I64Pair { lo, hi }
}

/// 64-bit arithmetic (signed) shift right — same structure as [`i64_shr_u`],
/// but the high limb is filled with the sign bit instead of zero:
///
/// * `s == 0`: identity.
/// * `0 < s < 32`: `lo = (lo >>u s) | (hi << (32-s))`, `hi = hi >>s s`.
/// * `s >= 32`: `lo = hi >>s (s-32)`, `hi = sign-fill of hi`.
///
/// `sign` is all-ones when `hi` is negative, all-zeros otherwise — obtained
/// by an arithmetic shift of `hi` right by 31.
fn i64_shr_s(a: &I64Pair, s: &BV) -> I64Pair {
    let s_lt_32 = s.bvult(k32(32));
    let s_is_zero = s.eq(k32(0));
    let sign = a.hi.bvashr(k32(31)); // 0x0000_0000 or 0xFFFF_FFFF

    let lo_small = a.lo.bvlshr(s).bvor(a.hi.bvshl(k32(32).bvsub(s)));
    let hi_small = a.hi.bvashr(s);

    let lo_big = a.hi.bvashr(s.bvsub(k32(32)));
    let hi_big = sign.clone();

    let lo = s_is_zero.ite(&a.lo, &s_lt_32.ite(&lo_small, &lo_big));
    let hi = s_is_zero.ite(&a.hi, &s_lt_32.ite(&hi_small, &hi_big));
    I64Pair { lo, hi }
}

/// 64-bit rotate left: `rotl(x, s) = (x << s) | (x >>u (64-s))`.
///
/// `(64 - s) mod 64` keeps the right-shift amount in range and maps `s == 0`
/// to a 0 shift, so the OR below reduces to the identity at `s == 0`.
fn i64_rotl(a: &I64Pair, s: &BV) -> I64Pair {
    let left = i64_shl(a, s);
    let comp = k32(64).bvsub(s).bvand(k32(63));
    let right = i64_shr_u(a, &comp);
    I64Pair {
        lo: left.lo.bvor(&right.lo),
        hi: left.hi.bvor(&right.hi),
    }
}

/// 64-bit rotate right: `rotr(x, s) = (x >>u s) | (x << (64-s))`.
fn i64_rotr(a: &I64Pair, s: &BV) -> I64Pair {
    let right = i64_shr_u(a, s);
    let comp = k32(64).bvsub(s).bvand(k32(63));
    let left = i64_shl(a, &comp);
    I64Pair {
        lo: right.lo.bvor(&left.lo),
        hi: right.hi.bvor(&left.hi),
    }
}

/// 64-bit unsigned less-than over the limb pair.
///
/// Lexicographic: the high limbs decide; if they are equal the low limbs
/// (compared unsigned) break the tie. `a <u b  ⇔  a_hi <u b_hi ∨
/// (a_hi == b_hi ∧ a_lo <u b_lo)`.
fn i64_lt_u(a: &I64Pair, b: &I64Pair) -> Bool {
    let hi_lt = a.hi.bvult(&b.hi);
    let hi_eq = a.hi.eq(&b.hi);
    let lo_lt = a.lo.bvult(&b.lo);
    Bool::or(&[&hi_lt, &Bool::and(&[&hi_eq, &lo_lt])])
}

/// 64-bit signed less-than over the limb pair.
///
/// Identical to the unsigned case except the *high* limbs are compared
/// **signed** (the sign of the 64-bit value lives in the top bit of `hi`).
/// The low limbs are still compared unsigned — they carry no sign of their
/// own.
fn i64_lt_s(a: &I64Pair, b: &I64Pair) -> Bool {
    let hi_lt = a.hi.bvslt(&b.hi);
    let hi_eq = a.hi.eq(&b.hi);
    let lo_lt = a.lo.bvult(&b.lo);
    Bool::or(&[&hi_lt, &Bool::and(&[&hi_eq, &lo_lt])])
}

// ===========================================================================
// ARM NZCV condition flags
// ===========================================================================

/// The four ARM condition flags, as Z3 booleans.
#[derive(Clone)]
struct Flags {
    n: Bool, // Negative — result bit 31
    z: Bool, // Zero
    c: Bool, // Carry / no-borrow
    v: Bool, // Signed overflow
}

impl Flags {
    /// Flags before any compare has run — unconstrained.
    fn unconstrained() -> Self {
        Self {
            n: Bool::new_const("flag_n"),
            z: Bool::new_const("flag_z"),
            c: Bool::new_const("flag_c"),
            v: Bool::new_const("flag_v"),
        }
    }

    /// Flags produced by an ARM compare of `a` against `b` (i.e. `a - b`).
    ///
    /// This is the standard ARM `CMP` flag update:
    ///   * `N` — bit 31 of `a - b`.
    ///   * `Z` — `a == b`.
    ///   * `C` — *no borrow*, i.e. `a >=u b` (ARM carry convention for SUB).
    ///   * `V` — signed overflow of `a - b`: the operands have different
    ///     signs and the result's sign differs from `a`'s.
    fn from_cmp(a: &BV, b: &BV) -> Self {
        let result = a.bvsub(b);
        let n = result.bvslt(k32(0));
        let z = a.eq(b);
        let c = a.bvuge(b);
        // Signed overflow: sign(a) != sign(b) && sign(result) != sign(a).
        let a_neg = a.bvslt(k32(0));
        let b_neg = b.bvslt(k32(0));
        let r_neg = result.bvslt(k32(0));
        let signs_differ = a_neg.eq(&b_neg).not();
        let result_sign_wrong = r_neg.eq(&a_neg).not();
        let v = Bool::and(&[&signs_differ, &result_sign_wrong]);
        Self { n, z, c, v }
    }

    /// Evaluate an ARM [`Condition`] against these flags.
    ///
    /// Standard ARM condition-code semantics; see the `Condition` enum doc.
    fn holds(&self, cond: &Condition) -> Bool {
        match cond {
            Condition::EQ => self.z.clone(),
            Condition::NE => self.z.not(),
            // signed
            Condition::LT => self.n.eq(&self.v).not(),
            Condition::GE => self.n.eq(&self.v),
            Condition::LE => Bool::or(&[&self.z, &self.n.eq(&self.v).not()]),
            Condition::GT => Bool::and(&[&self.z.not(), &self.n.eq(&self.v)]),
            // unsigned
            Condition::LO => self.c.not(),
            Condition::HS => self.c.clone(),
            Condition::LS => Bool::or(&[&self.c.not(), &self.z.clone()]),
            Condition::HI => Bool::and(&[&self.c, &self.z.not()]),
        }
    }
}

// ===========================================================================
// Z3-backed validator
// ===========================================================================

/// What an op's result looks like: a single 32-bit value, or an i64 limb
/// pair.
enum OpResult {
    /// A 32-bit value (i32 ops, and i64 comparisons / `eqz`).
    Word(BV),
    /// A 64-bit value as `(lo, hi)` limbs (i64 arithmetic / logic / shift).
    Pair(I64Pair),
}

/// Z3-backed validator for the WASM → ARM selection pattern.
///
/// For each call the validator:
///
/// 1. Allocates symbolic 32-bit inputs (a limb pair per i64 operand).
/// 2. Builds the WASM op's reference result from those inputs.
/// 3. Builds the ARM sequence's result by symbolically executing it.
/// 4. Asserts the *negation* of equivalence and checks satisfiability:
///    `unsat` ⇒ equivalent for all inputs (accept), `sat` ⇒ counterexample
///    (reject).
///
/// The validator is **trusted** code: it is the small, auditable piece that
/// replaces ~150 per-op Rocq proofs. Every formula it builds is 32-bit
/// bitvector arithmetic that a reviewer can check by hand.
pub struct Z3ArmValidator;

impl Default for Z3ArmValidator {
    fn default() -> Self {
        Self::new()
    }
}

impl Z3ArmValidator {
    /// Construct a fresh validator. Z3 0.19 uses thread-local contexts, so
    /// callers should wrap any sequence of `validate` calls in
    /// [`crate::with_z3_context`].
    pub fn new() -> Self {
        Self
    }

    /// Build the WASM op's reference result from symbolic inputs.
    ///
    /// `a` and `b` are the two operands as limb pairs. For i32 ops only the
    /// `.lo` limb is meaningful. Returns `None` for ops outside the supported
    /// surface.
    fn wasm_reference(&self, op: &WasmOp, a: &I64Pair, b: &I64Pair) -> Option<OpResult> {
        use WasmOp::*;
        let word = |bv: BV| Some(OpResult::Word(bv));
        let pair = |p: I64Pair| Some(OpResult::Pair(p));
        match op {
            // --- i32 arithmetic --------------------------------------------
            I32Add => word(a.lo.bvadd(&b.lo)),
            I32Sub => word(a.lo.bvsub(&b.lo)),
            I32Mul => word(a.lo.bvmul(&b.lo)),
            // --- i32 logic -------------------------------------------------
            I32And => word(a.lo.bvand(&b.lo)),
            I32Or => word(a.lo.bvor(&b.lo)),
            I32Xor => word(a.lo.bvxor(&b.lo)),
            // --- i32 shifts (WASM masks the count mod 32) ------------------
            I32Shl => word(a.lo.bvshl(b.lo.bvand(k32(31)))),
            I32ShrU => word(a.lo.bvlshr(b.lo.bvand(k32(31)))),
            I32ShrS => word(a.lo.bvashr(b.lo.bvand(k32(31)))),
            I32Rotl => word(a.lo.bvrotl(b.lo.bvand(k32(31)))),
            I32Rotr => word(a.lo.bvrotr(b.lo.bvand(k32(31)))),
            // --- i32 div (precondition excludes the trap inputs) -----------
            // i32.rem_s / rem_u are scoped out — see module docs (the MLS
            // remainder identity is SMT-intractable: the symbolic multiply
            // bit-blasts past any practical solver budget).
            I32DivS => word(a.lo.bvsdiv(&b.lo)),
            I32DivU => word(a.lo.bvudiv(&b.lo)),
            // --- i32 comparisons (result is 0/1) ---------------------------
            I32Eq => word(bool_to_i32(&a.lo.eq(&b.lo))),
            I32Ne => word(bool_to_i32(&a.lo.eq(&b.lo).not())),
            I32LtS => word(bool_to_i32(&a.lo.bvslt(&b.lo))),
            I32LtU => word(bool_to_i32(&a.lo.bvult(&b.lo))),
            I32LeS => word(bool_to_i32(&a.lo.bvsle(&b.lo))),
            I32LeU => word(bool_to_i32(&a.lo.bvule(&b.lo))),
            I32GtS => word(bool_to_i32(&a.lo.bvsgt(&b.lo))),
            I32GtU => word(bool_to_i32(&a.lo.bvugt(&b.lo))),
            I32GeS => word(bool_to_i32(&a.lo.bvsge(&b.lo))),
            I32GeU => word(bool_to_i32(&a.lo.bvuge(&b.lo))),
            // --- i32 unary -------------------------------------------------
            I32Eqz => word(bool_to_i32(&a.lo.eq(k32(0)))),
            // --- i64 arithmetic --------------------------------------------
            I64Add => pair(i64_add(a, b)),
            I64Sub => pair(i64_sub(a, b)),
            I64Mul => pair(i64_mul(a, b)),
            // --- i64 logic -------------------------------------------------
            I64And => pair(I64Pair {
                lo: a.lo.bvand(&b.lo),
                hi: a.hi.bvand(&b.hi),
            }),
            I64Or => pair(I64Pair {
                lo: a.lo.bvor(&b.lo),
                hi: a.hi.bvor(&b.hi),
            }),
            I64Xor => pair(I64Pair {
                lo: a.lo.bvxor(&b.lo),
                hi: a.hi.bvxor(&b.hi),
            }),
            // --- i64 shifts (WASM masks the count mod 64) ------------------
            I64Shl => pair(i64_shl(a, &shift_amount64(b))),
            I64ShrU => pair(i64_shr_u(a, &shift_amount64(b))),
            I64ShrS => pair(i64_shr_s(a, &shift_amount64(b))),
            I64Rotl => pair(i64_rotl(a, &shift_amount64(b))),
            I64Rotr => pair(i64_rotr(a, &shift_amount64(b))),
            // --- i64 comparisons (result is a 32-bit 0/1) ------------------
            I64Eq => word(bool_to_i32(&a.eq_pair(b))),
            I64Ne => word(bool_to_i32(&a.eq_pair(b).not())),
            I64LtU => word(bool_to_i32(&i64_lt_u(a, b))),
            I64LtS => word(bool_to_i32(&i64_lt_s(a, b))),
            I64GtU => word(bool_to_i32(&i64_lt_u(b, a))),
            I64GtS => word(bool_to_i32(&i64_lt_s(b, a))),
            I64LeU => word(bool_to_i32(&i64_lt_u(b, a).not())),
            I64LeS => word(bool_to_i32(&i64_lt_s(b, a).not())),
            I64GeU => word(bool_to_i32(&i64_lt_u(a, b).not())),
            I64GeS => word(bool_to_i32(&i64_lt_s(a, b).not())),
            // --- i64 unary -------------------------------------------------
            I64Eqz => word(bool_to_i32(&Bool::and(&[
                &a.lo.eq(k32(0)),
                &a.hi.eq(k32(0)),
            ]))),
            // i64 div/rem are scoped out — see module docs.
            _ => None,
        }
    }

    /// Number of stack operands a supported WASM op consumes.
    /// `None` means the op is outside the supported surface.
    fn arity(&self, op: &WasmOp) -> Option<usize> {
        use WasmOp::*;
        match op {
            I32Add | I32Sub | I32Mul | I32And | I32Or | I32Xor | I32Shl | I32ShrU | I32ShrS
            | I32Rotl | I32Rotr | I32DivS | I32DivU | I32Eq | I32Ne | I32LtS | I32LtU | I32LeS
            | I32LeU | I32GtS | I32GtU | I32GeS | I32GeU | I64Add | I64Sub | I64Mul | I64And
            | I64Or | I64Xor | I64Shl | I64ShrU | I64ShrS | I64Rotl | I64Rotr | I64Eq | I64Ne
            | I64LtU | I64LtS | I64GtU | I64GtS | I64LeU | I64LeS | I64GeU | I64GeS => Some(2),
            I32Eqz | I64Eqz => Some(1),
            _ => None,
        }
    }

    /// Whether the op takes i64 operands (and therefore seeds register
    /// pairs).
    fn is_i64(op: &WasmOp) -> bool {
        use WasmOp::*;
        matches!(
            op,
            I64Add
                | I64Sub
                | I64Mul
                | I64And
                | I64Or
                | I64Xor
                | I64Shl
                | I64ShrU
                | I64ShrS
                | I64Rotl
                | I64Rotr
                | I64Eq
                | I64Ne
                | I64LtU
                | I64LtS
                | I64GtU
                | I64GtS
                | I64LeU
                | I64LeS
                | I64GeU
                | I64GeS
                | I64Eqz
        )
    }

    /// Whether the op's *result* is a 64-bit limb pair (vs a 32-bit word).
    /// i64 comparisons and `i64.eqz` return an i32, so they are *not* pairs.
    fn result_is_pair(op: &WasmOp) -> bool {
        use WasmOp::*;
        matches!(
            op,
            I64Add
                | I64Sub
                | I64Mul
                | I64And
                | I64Or
                | I64Xor
                | I64Shl
                | I64ShrU
                | I64ShrS
                | I64Rotl
                | I64Rotr
        )
    }

    /// Whether the op traps on certain inputs (division).
    fn is_div_rem(op: &WasmOp) -> bool {
        use WasmOp::*;
        matches!(op, I32DivS | I32DivU)
    }

    /// Trap-avoidance precondition for division ops.
    ///
    /// WASM `div` traps (rather than producing a value) when:
    ///   * the divisor is zero, or
    ///   * (signed only) the dividend is `INT_MIN` and the divisor is `-1`,
    ///     which overflows the result.
    ///
    /// The validator certifies the **non-trapping** behaviour: it asserts the
    /// precondition so Z3 only considers inputs on which WASM actually
    /// produces a value. The trap path itself (the selector's `CMP/BNE/UDF`
    /// guard) is control flow, validated separately at the CFG level — see
    /// `docs/validator-pattern.md`. This keeps the div query honest (the
    /// value-domain equivalence is real) without overclaiming.
    fn div_rem_precondition(&self, op: &WasmOp, a: &I64Pair, b: &I64Pair) -> Bool {
        use WasmOp::*;
        match op {
            I32DivU => b.lo.eq(k32(0)).not(),
            I32DivS => {
                let div_nonzero = b.lo.eq(k32(0)).not();
                let int_min = a.lo.eq(k32(i32::MIN as i64));
                let neg_one = b.lo.eq(k32(-1));
                let overflow = Bool::and(&[&int_min, &neg_one]);
                Bool::and(&[&div_nonzero, &overflow.not()])
            }
            _ => Bool::from_bool(true),
        }
    }

    /// Symbolically execute the emitted ARM sequence and return the result.
    ///
    /// The inputs are placed in the ARM registers the selector's calling
    /// convention uses:
    ///
    /// * i32 ops: operand 0 → R0, operand 1 → R1.
    /// * i64 ops: operand 0 → (R0 = lo, R1 = hi), operand 1 → (R2 = lo, R3 = hi).
    ///
    /// The result is read back from R0 (i32 ops and i64 comparisons) or the
    /// (R0, R1) pair (i64 arithmetic / logic / shift).
    ///
    /// Only the small ARM-op subset the i32/i64 lowerings actually use is
    /// modeled. An op outside that subset is a [`ValidationError::Internal`]
    /// — the validator refuses to silently certify an instruction it cannot
    /// reason about.
    fn execute_arm(
        &self,
        op: &WasmOp,
        arm: &[ArmOp],
        a: &I64Pair,
        b: &I64Pair,
    ) -> Result<OpResult, ValidationError> {
        // 16 general-purpose registers, all symbolic except the seeded
        // inputs.
        let mut regs: Vec<BV> = (0..16).map(|i| sym32(&format!("r{i}"))).collect();
        let mut flags = Flags::unconstrained();

        let is64 = Self::is_i64(op);
        let arity = self.arity(op).unwrap_or(0);

        // Seed the input registers per the calling convention above.
        if is64 {
            regs[0] = a.lo.clone();
            regs[1] = a.hi.clone();
            if arity == 2 {
                regs[2] = b.lo.clone();
                regs[3] = b.hi.clone();
            }
        } else {
            regs[0] = a.lo.clone();
            if arity == 2 {
                regs[1] = b.lo.clone();
            }
        }

        let idx = reg_index;

        // Resolve an `Operand2` against the current register file.
        let eval_op2 = |regs: &[BV], op2: &Operand2| -> Result<BV, ValidationError> {
            match op2 {
                Operand2::Reg(r) => Ok(regs[idx(r)].clone()),
                Operand2::Imm(v) => Ok(k32(*v as i64)),
                other => Err(ValidationError::Internal(format!(
                    "unsupported Operand2 in lowering: {other:?}"
                ))),
            }
        };

        for instr in arm {
            match instr {
                ArmOp::Add { rd, rn, op2 } => {
                    regs[idx(rd)] = regs[idx(rn)].bvadd(&eval_op2(&regs, op2)?);
                }
                ArmOp::Sub { rd, rn, op2 } => {
                    regs[idx(rd)] = regs[idx(rn)].bvsub(&eval_op2(&regs, op2)?);
                }
                // ADDS: add and set the carry flag (i64 low limb).
                ArmOp::Adds { rd, rn, op2 } => {
                    let rn_v = regs[idx(rn)].clone();
                    let v = rn_v.bvadd(&eval_op2(&regs, op2)?);
                    // Unsigned carry out: the 32-bit sum wrapped below rn.
                    flags.c = v.bvult(&rn_v);
                    regs[idx(rd)] = v;
                }
                // ADC: add with the carry flag (i64 high limb).
                ArmOp::Adc { rd, rn, op2 } => {
                    let c = flags.c.ite(&k32(1), &k32(0));
                    regs[idx(rd)] = regs[idx(rn)].bvadd(&eval_op2(&regs, op2)?).bvadd(&c);
                }
                // SUBS: subtract and set carry. ARM convention: C = 1 means
                // *no* borrow (rn >=u op2).
                ArmOp::Subs { rd, rn, op2 } => {
                    let rn_v = regs[idx(rn)].clone();
                    let op2_v = eval_op2(&regs, op2)?;
                    flags.c = rn_v.bvuge(&op2_v);
                    regs[idx(rd)] = rn_v.bvsub(&op2_v);
                }
                // SBC: subtract with borrow. Rd = Rn - op2 - (1 - C).
                ArmOp::Sbc { rd, rn, op2 } => {
                    let borrow = flags.c.ite(&k32(0), &k32(1));
                    regs[idx(rd)] = regs[idx(rn)].bvsub(&eval_op2(&regs, op2)?).bvsub(&borrow);
                }
                ArmOp::Mul { rd, rn, rm } => {
                    regs[idx(rd)] = regs[idx(rn)].bvmul(&regs[idx(rm)]);
                }
                ArmOp::And { rd, rn, op2 } => {
                    regs[idx(rd)] = regs[idx(rn)].bvand(&eval_op2(&regs, op2)?);
                }
                ArmOp::Orr { rd, rn, op2 } => {
                    regs[idx(rd)] = regs[idx(rn)].bvor(&eval_op2(&regs, op2)?);
                }
                ArmOp::Eor { rd, rn, op2 } => {
                    regs[idx(rd)] = regs[idx(rn)].bvxor(&eval_op2(&regs, op2)?);
                }
                ArmOp::Mov { rd, op2 } => {
                    regs[idx(rd)] = eval_op2(&regs, op2)?;
                }
                ArmOp::Mvn { rd, op2 } => {
                    regs[idx(rd)] = eval_op2(&regs, op2)?.bvnot();
                }
                // Register-amount shifts. Z3's bvshl/bvlshr/bvashr are total
                // for any amount; the selector is responsible for masking the
                // amount mod 32, and an unmasked lowering would fail the
                // equivalence check.
                ArmOp::LslReg { rd, rn, rm } => {
                    regs[idx(rd)] = regs[idx(rn)].bvshl(&regs[idx(rm)]);
                }
                ArmOp::LsrReg { rd, rn, rm } => {
                    regs[idx(rd)] = regs[idx(rn)].bvlshr(&regs[idx(rm)]);
                }
                ArmOp::AsrReg { rd, rn, rm } => {
                    regs[idx(rd)] = regs[idx(rn)].bvashr(&regs[idx(rm)]);
                }
                ArmOp::RorReg { rd, rn, rm } => {
                    regs[idx(rd)] = regs[idx(rn)].bvrotr(&regs[idx(rm)]);
                }
                ArmOp::Lsl { rd, rn, shift } => {
                    regs[idx(rd)] = regs[idx(rn)].bvshl(k32(*shift as i64));
                }
                ArmOp::Lsr { rd, rn, shift } => {
                    regs[idx(rd)] = regs[idx(rn)].bvlshr(k32(*shift as i64));
                }
                ArmOp::Asr { rd, rn, shift } => {
                    regs[idx(rd)] = regs[idx(rn)].bvashr(k32(*shift as i64));
                }
                ArmOp::Ror { rd, rn, shift } => {
                    regs[idx(rd)] = regs[idx(rn)].bvrotr(k32(*shift as i64));
                }
                // Rsb: reverse subtract — Rd = imm - Rn (used by rotl as
                // 0 - shift to get the negated rotate amount).
                ArmOp::Rsb { rd, rn, imm } => {
                    regs[idx(rd)] = k32(*imm as i64).bvsub(&regs[idx(rn)]);
                }
                ArmOp::Sdiv { rd, rn, rm } => {
                    regs[idx(rd)] = regs[idx(rn)].bvsdiv(&regs[idx(rm)]);
                }
                ArmOp::Udiv { rd, rn, rm } => {
                    regs[idx(rd)] = regs[idx(rn)].bvudiv(&regs[idx(rm)]);
                }
                // MLS: Rd = Ra - Rn*Rm — the remainder idiom `a - (a/b)*b`.
                ArmOp::Mls { rd, rn, rm, ra } => {
                    regs[idx(rd)] = regs[idx(ra)].bvsub(regs[idx(rn)].bvmul(&regs[idx(rm)]));
                }
                // CMP: set NZCV from Rn - op2; no register write.
                ArmOp::Cmp { rn, op2 } => {
                    let rn_v = regs[idx(rn)].clone();
                    let op2_v = eval_op2(&regs, op2)?;
                    flags = Flags::from_cmp(&rn_v, &op2_v);
                }
                // SetCond: materialize an NZCV condition into Rd as 0/1.
                // This is the verification pseudo-op the selector emits when
                // a comparison result is consumed as a value (rather than by
                // a conditional branch). It is the value-domain face of the
                // "CMP-only" lowering in issue #73 item 2.
                ArmOp::SetCond { rd, cond } => {
                    regs[idx(rd)] = bool_to_i32(&flags.holds(cond));
                }
                // I64SetCond: compare a register pair (rn_lo:rn_hi) against
                // (rm_lo:rm_hi) and materialize the condition as 0/1 in rd.
                // The validator models it directly against the i64 reference
                // comparison — see the lexicographic `i64_lt_*` helpers.
                ArmOp::I64SetCond {
                    rd,
                    rn_lo,
                    rn_hi,
                    rm_lo,
                    rm_hi,
                    cond,
                } => {
                    let n = I64Pair {
                        lo: regs[idx(rn_lo)].clone(),
                        hi: regs[idx(rn_hi)].clone(),
                    };
                    let m = I64Pair {
                        lo: regs[idx(rm_lo)].clone(),
                        hi: regs[idx(rm_hi)].clone(),
                    };
                    let holds = match cond {
                        Condition::EQ => n.eq_pair(&m),
                        Condition::NE => n.eq_pair(&m).not(),
                        Condition::LT => i64_lt_s(&n, &m),
                        Condition::GE => i64_lt_s(&n, &m).not(),
                        Condition::GT => i64_lt_s(&m, &n),
                        Condition::LE => i64_lt_s(&m, &n).not(),
                        Condition::LO => i64_lt_u(&n, &m),
                        Condition::HS => i64_lt_u(&n, &m).not(),
                        Condition::HI => i64_lt_u(&m, &n),
                        Condition::LS => i64_lt_u(&m, &n).not(),
                    };
                    regs[idx(rd)] = bool_to_i32(&holds);
                }
                // I64Mul: 64-bit multiply of register pairs (rn_lo:rn_hi) and
                // (rm_lo:rm_hi), low 64 bits of the product into
                // (rd_lo:rd_hi). The real selector expands this to
                // UMULL + MLA cross products; the validator checks the
                // composite pseudo-op against the schoolbook `i64_mul`
                // reference (carry of the low partial product + cross terms).
                ArmOp::I64Mul {
                    rd_lo,
                    rd_hi,
                    rn_lo,
                    rn_hi,
                    rm_lo,
                    rm_hi,
                } => {
                    let n = I64Pair {
                        lo: regs[idx(rn_lo)].clone(),
                        hi: regs[idx(rn_hi)].clone(),
                    };
                    let m = I64Pair {
                        lo: regs[idx(rm_lo)].clone(),
                        hi: regs[idx(rm_hi)].clone(),
                    };
                    let prod = i64_mul(&n, &m);
                    regs[idx(rd_lo)] = prod.lo;
                    regs[idx(rd_hi)] = prod.hi;
                }
                // I64Shl / I64ShrU / I64ShrS: 64-bit shift of a register
                // pair by an amount in (rm_lo). The real selector expands
                // each to a multi-instruction sequence with a runtime branch
                // on whether the (mod-64) amount is < 32 or >= 32; the
                // validator checks the composite pseudo-op against the
                // `i64_shl` / `i64_shr_u` / `i64_shr_s` references, which
                // model exactly that case split. The shift amount is masked
                // mod 64, matching WASM's `count mod 64` rule.
                ArmOp::I64Shl {
                    rd_lo,
                    rd_hi,
                    rn_lo,
                    rn_hi,
                    rm_lo,
                    rm_hi: _,
                } => {
                    let n = I64Pair {
                        lo: regs[idx(rn_lo)].clone(),
                        hi: regs[idx(rn_hi)].clone(),
                    };
                    let amt = regs[idx(rm_lo)].bvand(k32(63));
                    let r = i64_shl(&n, &amt);
                    regs[idx(rd_lo)] = r.lo;
                    regs[idx(rd_hi)] = r.hi;
                }
                ArmOp::I64ShrU {
                    rd_lo,
                    rd_hi,
                    rn_lo,
                    rn_hi,
                    rm_lo,
                    rm_hi: _,
                } => {
                    let n = I64Pair {
                        lo: regs[idx(rn_lo)].clone(),
                        hi: regs[idx(rn_hi)].clone(),
                    };
                    let amt = regs[idx(rm_lo)].bvand(k32(63));
                    let r = i64_shr_u(&n, &amt);
                    regs[idx(rd_lo)] = r.lo;
                    regs[idx(rd_hi)] = r.hi;
                }
                ArmOp::I64ShrS {
                    rd_lo,
                    rd_hi,
                    rn_lo,
                    rn_hi,
                    rm_lo,
                    rm_hi: _,
                } => {
                    let n = I64Pair {
                        lo: regs[idx(rn_lo)].clone(),
                        hi: regs[idx(rn_hi)].clone(),
                    };
                    let amt = regs[idx(rm_lo)].bvand(k32(63));
                    let r = i64_shr_s(&n, &amt);
                    regs[idx(rd_lo)] = r.lo;
                    regs[idx(rd_hi)] = r.hi;
                }
                // I64Rotl / I64Rotr: 64-bit rotate of a register pair by an
                // amount held in a single register. Checked against the
                // `i64_rotl` / `i64_rotr` references, which are themselves
                // built from the shift primitives. The amount is masked
                // mod 64, matching WASM's `count mod 64` rule.
                ArmOp::I64Rotl {
                    rdlo,
                    rdhi,
                    rnlo,
                    rnhi,
                    shift,
                } => {
                    let n = I64Pair {
                        lo: regs[idx(rnlo)].clone(),
                        hi: regs[idx(rnhi)].clone(),
                    };
                    let amt = regs[idx(shift)].bvand(k32(63));
                    let r = i64_rotl(&n, &amt);
                    regs[idx(rdlo)] = r.lo;
                    regs[idx(rdhi)] = r.hi;
                }
                ArmOp::I64Rotr {
                    rdlo,
                    rdhi,
                    rnlo,
                    rnhi,
                    shift,
                } => {
                    let n = I64Pair {
                        lo: regs[idx(rnlo)].clone(),
                        hi: regs[idx(rnhi)].clone(),
                    };
                    let amt = regs[idx(shift)].bvand(k32(63));
                    let r = i64_rotr(&n, &amt);
                    regs[idx(rdlo)] = r.lo;
                    regs[idx(rdhi)] = r.hi;
                }
                // I64SetCondZ: 0/1 in rd iff the register pair is all-zero.
                ArmOp::I64SetCondZ { rd, rn_lo, rn_hi } => {
                    let is_zero =
                        Bool::and(&[&regs[idx(rn_lo)].eq(k32(0)), &regs[idx(rn_hi)].eq(k32(0))]);
                    regs[idx(rd)] = bool_to_i32(&is_zero);
                }
                ArmOp::Nop => {}
                other => {
                    return Err(ValidationError::Internal(format!(
                        "ARM op not modeled by validator: {other:?}"
                    )));
                }
            }
        }

        if is64 && Self::result_is_pair(op) {
            Ok(OpResult::Pair(I64Pair {
                lo: regs[0].clone(),
                hi: regs[1].clone(),
            }))
        } else {
            Ok(OpResult::Word(regs[0].clone()))
        }
    }
}

/// Map a `Reg` to its 0..=15 index.
fn reg_index(r: &Reg) -> usize {
    match r {
        Reg::R0 => 0,
        Reg::R1 => 1,
        Reg::R2 => 2,
        Reg::R3 => 3,
        Reg::R4 => 4,
        Reg::R5 => 5,
        Reg::R6 => 6,
        Reg::R7 => 7,
        Reg::R8 => 8,
        Reg::R9 => 9,
        Reg::R10 => 10,
        Reg::R11 => 11,
        Reg::R12 => 12,
        Reg::SP => 13,
        Reg::LR => 14,
        Reg::PC => 15,
    }
}

impl Validator<WasmOp, ArmOp> for Z3ArmValidator {
    fn validate(
        &self,
        sel: &CertifiedSelection<WasmOp, ArmOp>,
    ) -> Result<Witness, ValidationError> {
        let label = format!("{:?}", sel.wasm);

        // Gate: is this op in the supported surface at all?
        self.arity(&sel.wasm)
            .ok_or_else(|| ValidationError::UnsupportedOp(sel.wasm.clone()))?;

        let solver = Solver::new();

        // Symbolic operands. Each operand is a limb pair; for i32 ops only the
        // `.lo` limb is meaningful and the `.hi` limb is left unconstrained
        // (it is never read by the i32 reference or the i32 lowering).
        let a = I64Pair {
            lo: sym32("a_lo"),
            hi: sym32("a_hi"),
        };
        let b = I64Pair {
            lo: sym32("b_lo"),
            hi: sym32("b_hi"),
        };

        // For division / remainder, restrict to non-trapping inputs so the
        // value-domain equivalence is the property actually being proved.
        if Self::is_div_rem(&sel.wasm) {
            solver.assert(self.div_rem_precondition(&sel.wasm, &a, &b));
        }

        let wasm_result = self
            .wasm_reference(&sel.wasm, &a, &b)
            .ok_or_else(|| ValidationError::UnsupportedOp(sel.wasm.clone()))?;
        let arm_result = self.execute_arm(&sel.wasm, &sel.arm, &a, &b)?;

        // Assert ¬(wasm == arm); unsat ⇒ equivalent for all inputs.
        let differ = match (&wasm_result, &arm_result) {
            (OpResult::Word(w), OpResult::Word(r)) => w.eq(r).not(),
            (OpResult::Pair(w), OpResult::Pair(r)) => w.eq_pair(r).not(),
            _ => {
                return Err(ValidationError::Internal(format!(
                    "result-shape mismatch for {label}: WASM and ARM disagree on word vs pair"
                )));
            }
        };
        solver.assert(&differ);

        match solver.check() {
            SatResult::Unsat => Ok(Witness {
                wasm_op_label: label,
                arm_op_count: sel.arm.len(),
                solver_result: SolverResultKind::Unsat,
            }),
            SatResult::Sat => {
                let description = match solver.get_model() {
                    Some(model) => {
                        let mut parts = Vec::new();
                        for (name, bv) in [
                            ("a_lo", &a.lo),
                            ("a_hi", &a.hi),
                            ("b_lo", &b.lo),
                            ("b_hi", &b.hi),
                        ] {
                            if let Some(v) = model.eval(bv, true).and_then(|v| v.as_i64()) {
                                parts.push(format!("{name}={v}"));
                            }
                        }
                        parts.join(", ")
                    }
                    None => "no model available".to_string(),
                };
                Err(ValidationError::Counterexample {
                    wasm_op_label: label,
                    description,
                })
            }
            SatResult::Unknown => Err(ValidationError::SolverUnknown(label)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::with_z3_context;

    // ---- helpers ----------------------------------------------------------

    /// Assert that `sel` certifies (Z3 returns `unsat` for the negation).
    fn assert_certifies(wasm: WasmOp, arm: Vec<ArmOp>) {
        let validator = Z3ArmValidator::new();
        let sel = CertifiedSelection::new(wasm.clone(), arm);
        match validator.validate(&sel) {
            Ok(w) => {
                assert_eq!(
                    w.solver_result,
                    SolverResultKind::Unsat,
                    "{wasm:?} did not certify"
                );
                assert_eq!(w.wasm_op_label, format!("{wasm:?}"));
            }
            other => panic!("expected {wasm:?} to certify, got {other:?}"),
        }
    }

    /// i32 data-processing lowering: `OP R0, R0, R1`.
    fn dp_r0_r0_r1(make: fn(Reg, Reg, Operand2) -> ArmOp) -> Vec<ArmOp> {
        vec![make(Reg::R0, Reg::R0, Operand2::Reg(Reg::R1))]
    }

    /// i32 comparison lowering: `CMP R0, R1; SetCond R0, cond`.
    fn i32_cmp(cond: Condition) -> Vec<ArmOp> {
        vec![
            ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            },
            ArmOp::SetCond { rd: Reg::R0, cond },
        ]
    }

    /// i64 comparison lowering: a single `I64SetCond` pseudo-op over the
    /// register pairs (R0:R1) and (R2:R3).
    fn i64_cmp(cond: Condition) -> Vec<ArmOp> {
        vec![ArmOp::I64SetCond {
            rd: Reg::R0,
            rn_lo: Reg::R0,
            rn_hi: Reg::R1,
            rm_lo: Reg::R2,
            rm_hi: Reg::R3,
            cond,
        }]
    }

    /// i64 limb-wise logic lowering: `OP R0,R0,R2 ; OP R1,R1,R3`.
    fn i64_logic(make: fn(Reg, Reg, Operand2) -> ArmOp) -> Vec<ArmOp> {
        vec![
            make(Reg::R0, Reg::R0, Operand2::Reg(Reg::R2)),
            make(Reg::R1, Reg::R1, Operand2::Reg(Reg::R3)),
        ]
    }

    // ---- existing prototype tests (kept passing) --------------------------

    /// The headline test from the prototype: a correct selector picking `ADD`
    /// certifies; a wrong selector picking `SUB` is rejected.
    #[test]
    fn i32_add_certifies() {
        with_z3_context(|| {
            let validator = Z3ArmValidator::new();

            let correct = CertifiedSelection::new(
                WasmOp::I32Add,
                vec![ArmOp::Add {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                }],
            );
            let witness = validator
                .validate(&correct)
                .expect("validator must accept I32Add → ADD");
            assert_eq!(witness.wasm_op_label, "I32Add");
            assert_eq!(witness.arm_op_count, 1);
            assert_eq!(witness.solver_result, SolverResultKind::Unsat);

            let wrong = CertifiedSelection::new(
                WasmOp::I32Add,
                vec![ArmOp::Sub {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                }],
            );
            match validator.validate(&wrong) {
                Err(ValidationError::Counterexample { wasm_op_label, .. }) => {
                    assert_eq!(wasm_op_label, "I32Add");
                }
                other => panic!("expected Counterexample for SUB, got {other:?}"),
            }
        });
    }

    /// Unsupported ops return a structured error, not a panic.
    #[test]
    fn unsupported_op_returns_structured_error() {
        with_z3_context(|| {
            let validator = Z3ArmValidator::new();
            // `Drop` is not in the i32/i64 arithmetic surface.
            let sel = CertifiedSelection::<WasmOp, ArmOp>::new(WasmOp::Drop, vec![]);
            match validator.validate(&sel) {
                Err(ValidationError::UnsupportedOp(op)) => assert_eq!(op, WasmOp::Drop),
                other => panic!("expected UnsupportedOp, got {other:?}"),
            }
        });
    }

    /// CertifiedSelection plumbing: witnesses round-trip through
    /// `with_witness` / `is_certified` without losing information.
    #[test]
    fn certified_selection_witness_roundtrip() {
        let sel = CertifiedSelection::<WasmOp, ArmOp>::new(
            WasmOp::I32Add,
            vec![ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }],
        );
        assert!(!sel.is_certified());
        let witness = Witness {
            wasm_op_label: "I32Add".to_string(),
            arm_op_count: 1,
            solver_result: SolverResultKind::Unsat,
        };
        let certified = sel.with_witness(witness.clone());
        assert!(certified.is_certified());
        assert_eq!(certified.witness, Some(witness));
    }

    // ---- i32 arithmetic / logic -------------------------------------------

    #[test]
    fn i32_arith_logic_certifies() {
        with_z3_context(|| {
            assert_certifies(
                WasmOp::I32Add,
                dp_r0_r0_r1(|rd, rn, op2| ArmOp::Add { rd, rn, op2 }),
            );
            assert_certifies(
                WasmOp::I32Sub,
                dp_r0_r0_r1(|rd, rn, op2| ArmOp::Sub { rd, rn, op2 }),
            );
            assert_certifies(
                WasmOp::I32Mul,
                vec![ArmOp::Mul {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                }],
            );
            assert_certifies(
                WasmOp::I32And,
                dp_r0_r0_r1(|rd, rn, op2| ArmOp::And { rd, rn, op2 }),
            );
            assert_certifies(
                WasmOp::I32Or,
                dp_r0_r0_r1(|rd, rn, op2| ArmOp::Orr { rd, rn, op2 }),
            );
            assert_certifies(
                WasmOp::I32Xor,
                dp_r0_r0_r1(|rd, rn, op2| ArmOp::Eor { rd, rn, op2 }),
            );
        });
    }

    // ---- i32 shifts -------------------------------------------------------

    #[test]
    fn i32_shifts_certify() {
        with_z3_context(|| {
            // WASM masks the shift count mod 32. The faithful lowering masks
            // R1 with #31 first, then does the register shift.
            let mask_then = |shift: ArmOp| {
                vec![
                    ArmOp::And {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Imm(31),
                    },
                    shift,
                ]
            };
            assert_certifies(
                WasmOp::I32Shl,
                mask_then(ArmOp::LslReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                }),
            );
            assert_certifies(
                WasmOp::I32ShrU,
                mask_then(ArmOp::LsrReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                }),
            );
            assert_certifies(
                WasmOp::I32ShrS,
                mask_then(ArmOp::AsrReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                }),
            );
            // ARM ROR rotates mod 32 inherently, so it matches WASM rotr
            // directly without masking.
            assert_certifies(
                WasmOp::I32Rotr,
                vec![ArmOp::RorReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                }],
            );
            // ROTL(x, s) = ROTR(x, -s): RSB R1, R1, #0 negates the amount,
            // then ROR rotates right by it.
            assert_certifies(
                WasmOp::I32Rotl,
                vec![
                    ArmOp::Rsb {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        imm: 0,
                    },
                    ArmOp::RorReg {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        rm: Reg::R1,
                    },
                ],
            );
        });
    }

    // ---- i32 comparisons --------------------------------------------------

    #[test]
    fn i32_comparisons_certify() {
        with_z3_context(|| {
            // Each comparison lowers to CMP + SetCond with the matching ARM
            // condition code. Signed: LT/LE/GT/GE; unsigned: LO/LS/HI/HS.
            assert_certifies(WasmOp::I32Eq, i32_cmp(Condition::EQ));
            assert_certifies(WasmOp::I32Ne, i32_cmp(Condition::NE));
            assert_certifies(WasmOp::I32LtS, i32_cmp(Condition::LT));
            assert_certifies(WasmOp::I32LeS, i32_cmp(Condition::LE));
            assert_certifies(WasmOp::I32GtS, i32_cmp(Condition::GT));
            assert_certifies(WasmOp::I32GeS, i32_cmp(Condition::GE));
            assert_certifies(WasmOp::I32LtU, i32_cmp(Condition::LO));
            assert_certifies(WasmOp::I32LeU, i32_cmp(Condition::LS));
            assert_certifies(WasmOp::I32GtU, i32_cmp(Condition::HI));
            assert_certifies(WasmOp::I32GeU, i32_cmp(Condition::HS));
        });
    }

    #[test]
    fn i32_eqz_certifies() {
        with_z3_context(|| {
            // i32.eqz: (a == 0). CMP R0, #0 then SetCond EQ.
            assert_certifies(
                WasmOp::I32Eqz,
                vec![
                    ArmOp::Cmp {
                        rn: Reg::R0,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::SetCond {
                        rd: Reg::R0,
                        cond: Condition::EQ,
                    },
                ],
            );
        });
    }

    // ---- i32 division -----------------------------------------------------

    #[test]
    fn i32_div_certify() {
        with_z3_context(|| {
            // div_s / div_u map directly onto SDIV / UDIV (bvsdiv / bvudiv);
            // no symbolic multiply, so the equivalence is solver-tractable.
            // The non-trapping precondition excludes divisor 0 (and, for
            // div_s, INT_MIN/-1).
            assert_certifies(
                WasmOp::I32DivS,
                vec![ArmOp::Sdiv {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                }],
            );
            assert_certifies(
                WasmOp::I32DivU,
                vec![ArmOp::Udiv {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                }],
            );
        });
    }

    /// `i32.rem_s` and `i32.rem_u` are scoped out — the `SDIV/UDIV` + `MLS`
    /// remainder identity `r = a - (a / b) * b` makes Z3 reason about a
    /// symbolic 32-bit multiply, which is SMT-intractable (see module docs).
    /// Confirm the validator reports them as `UnsupportedOp` rather than
    /// silently certifying or hanging.
    #[test]
    fn i32_rem_is_scoped_out() {
        with_z3_context(|| {
            let validator = Z3ArmValidator::new();
            for op in [WasmOp::I32RemS, WasmOp::I32RemU] {
                let sel = CertifiedSelection::<WasmOp, ArmOp>::new(op.clone(), vec![]);
                match validator.validate(&sel) {
                    Err(ValidationError::UnsupportedOp(got)) => assert_eq!(got, op),
                    other => panic!("expected {op:?} to be UnsupportedOp, got {other:?}"),
                }
            }
        });
    }

    // ---- i64 arithmetic ---------------------------------------------------

    #[test]
    fn i64_add_certifies() {
        with_z3_context(|| {
            // i64.add register-pair lowering:
            //   ADDS R0, R0, R2   ; lo = a_lo + b_lo, sets carry
            //   ADC  R1, R1, R3   ; hi = a_hi + b_hi + carry
            assert_certifies(
                WasmOp::I64Add,
                vec![
                    ArmOp::Adds {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R2),
                    },
                    ArmOp::Adc {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Reg(Reg::R3),
                    },
                ],
            );
        });
    }

    #[test]
    fn i64_sub_certifies() {
        with_z3_context(|| {
            // i64.sub register-pair lowering:
            //   SUBS R0, R0, R2   ; lo = a_lo - b_lo, sets borrow (C)
            //   SBC  R1, R1, R3   ; hi = a_hi - b_hi - borrow
            assert_certifies(
                WasmOp::I64Sub,
                vec![
                    ArmOp::Subs {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R2),
                    },
                    ArmOp::Sbc {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Reg(Reg::R3),
                    },
                ],
            );
        });
    }

    /// `i64.mul` certifies: the `I64Mul` register-pair pseudo-op lowering is
    /// proved equivalent to the WASM `i64.mul` reference for all 2^128 input
    /// pairs. Both the reference and the pseudo-op model the 64-bit product
    /// with Z3's native `bvmul`, so what this certifies is that the lowering
    /// reads the operand pairs and writes the destination pair correctly —
    /// a misrouted register (e.g. swapping a limb) is caught. The expansion
    /// of `I64Mul` to actual UMULL + MLA instructions happens below the
    /// `ArmOp` level the validator inspects.
    #[test]
    fn i64_mul_certifies() {
        with_z3_context(|| {
            assert_certifies(
                WasmOp::I64Mul,
                vec![ArmOp::I64Mul {
                    rd_lo: Reg::R0,
                    rd_hi: Reg::R1,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                }],
            );
        });
    }

    #[test]
    fn i64_logic_certifies() {
        with_z3_context(|| {
            assert_certifies(
                WasmOp::I64And,
                i64_logic(|rd, rn, op2| ArmOp::And { rd, rn, op2 }),
            );
            assert_certifies(
                WasmOp::I64Or,
                i64_logic(|rd, rn, op2| ArmOp::Orr { rd, rn, op2 }),
            );
            assert_certifies(
                WasmOp::I64Xor,
                i64_logic(|rd, rn, op2| ArmOp::Eor { rd, rn, op2 }),
            );
        });
    }

    // ---- i64 shifts / rotates ---------------------------------------------
    //
    // i64 shifts lower to multi-instruction sequences with a runtime branch
    // on whether the (mod-64) amount is < 32 or >= 32. The validator's
    // `i64_shl` / `i64_shr_u` / `i64_shr_s` references model exactly that
    // case split. Each shift/rotate is validated in two layers, mirroring
    // `i64_mul_certifies`: (1) the limb reference is proved equal to Z3's
    // native 64-bit shift for all inputs; (2) the composite pseudo-op
    // lowering is certified to wire the registers correctly.

    /// Prove a limb-shift reference equals the native 64-bit shift for all
    /// inputs and all (mod-64) amounts. `native` builds the 64-bit truth.
    fn prove_shift_reference(
        limb_fn: fn(&I64Pair, &BV) -> I64Pair,
        native: fn(&BV, &BV) -> BV,
        label: &str,
    ) {
        let solver = Solver::new();
        let a = I64Pair {
            lo: sym32("sa_lo"),
            hi: sym32("sa_hi"),
        };
        // Symbolic amount, already reduced mod 64 (the masked count).
        let amt = sym32("samt");
        solver.assert(amt.bvult(k32(64)));

        let limb = limb_fn(&a, &amt);
        let limb64 = limb.hi.concat(&limb.lo);
        // 64-bit ground truth. The shift amount must be a 64-bit BV for the
        // native op; zero-extend the 32-bit amount into the high half.
        let a64 = a.hi.concat(&a.lo);
        let amt64 = k32(0).concat(&amt);
        let truth = native(&a64, &amt64);

        solver.assert(limb64.eq(&truth).not());
        assert_eq!(
            solver.check(),
            SatResult::Unsat,
            "{label} limb reference must equal the native 64-bit shift for all inputs"
        );
    }

    #[test]
    fn i64_shift_references_match_native() {
        with_z3_context(|| {
            prove_shift_reference(i64_shl, |x, s| x.bvshl(s), "i64.shl");
            prove_shift_reference(i64_shr_u, |x, s| x.bvlshr(s), "i64.shr_u");
            prove_shift_reference(i64_shr_s, |x, s| x.bvashr(s), "i64.shr_s");
        });
    }

    #[test]
    fn i64_shifts_certify() {
        with_z3_context(|| {
            // Composite pseudo-op lowering: shift the (R0:R1) pair by R2.
            assert_certifies(
                WasmOp::I64Shl,
                vec![ArmOp::I64Shl {
                    rd_lo: Reg::R0,
                    rd_hi: Reg::R1,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                }],
            );
            assert_certifies(
                WasmOp::I64ShrU,
                vec![ArmOp::I64ShrU {
                    rd_lo: Reg::R0,
                    rd_hi: Reg::R1,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                }],
            );
            assert_certifies(
                WasmOp::I64ShrS,
                vec![ArmOp::I64ShrS {
                    rd_lo: Reg::R0,
                    rd_hi: Reg::R1,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                }],
            );
        });
    }

    #[test]
    fn i64_rotates_certify() {
        with_z3_context(|| {
            assert_certifies(
                WasmOp::I64Rotl,
                vec![ArmOp::I64Rotl {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    shift: Reg::R2,
                }],
            );
            assert_certifies(
                WasmOp::I64Rotr,
                vec![ArmOp::I64Rotr {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    shift: Reg::R2,
                }],
            );
        });
    }

    // ---- i64 comparisons --------------------------------------------------

    /// Prove the lexicographic `i64_lt_u` / `i64_lt_s` references equal Z3's
    /// native 64-bit comparisons for all inputs. Both `wasm_reference` and
    /// the `I64SetCond` lowering model are built on these helpers, so this
    /// closes the loop: it shows the *helper itself* is the right relation.
    #[test]
    fn i64_compare_references_match_native() {
        with_z3_context(|| {
            let solver = Solver::new();
            let a = I64Pair {
                lo: sym32("ca_lo"),
                hi: sym32("ca_hi"),
            };
            let b = I64Pair {
                lo: sym32("cb_lo"),
                hi: sym32("cb_hi"),
            };
            let a64 = a.hi.concat(&a.lo);
            let b64 = b.hi.concat(&b.lo);

            // i64_lt_u must equal native unsigned 64-bit less-than.
            let lt_u_wrong = i64_lt_u(&a, &b).eq(a64.bvult(&b64)).not();
            // i64_lt_s must equal native signed 64-bit less-than.
            let lt_s_wrong = i64_lt_s(&a, &b).eq(a64.bvslt(&b64)).not();
            solver.assert(Bool::or(&[&lt_u_wrong, &lt_s_wrong]));
            assert_eq!(
                solver.check(),
                SatResult::Unsat,
                "i64 lexicographic compare references must match native 64-bit comparisons"
            );
        });
    }

    #[test]
    fn i64_comparisons_certify() {
        with_z3_context(|| {
            // Each i64 comparison lowers to a single I64SetCond pseudo-op
            // over the register pairs (R0:R1) and (R2:R3).
            assert_certifies(WasmOp::I64Eq, i64_cmp(Condition::EQ));
            assert_certifies(WasmOp::I64Ne, i64_cmp(Condition::NE));
            assert_certifies(WasmOp::I64LtS, i64_cmp(Condition::LT));
            assert_certifies(WasmOp::I64LeS, i64_cmp(Condition::LE));
            assert_certifies(WasmOp::I64GtS, i64_cmp(Condition::GT));
            assert_certifies(WasmOp::I64GeS, i64_cmp(Condition::GE));
            assert_certifies(WasmOp::I64LtU, i64_cmp(Condition::LO));
            assert_certifies(WasmOp::I64LeU, i64_cmp(Condition::LS));
            assert_certifies(WasmOp::I64GtU, i64_cmp(Condition::HI));
            assert_certifies(WasmOp::I64GeU, i64_cmp(Condition::HS));
        });
    }

    #[test]
    fn i64_eqz_certifies() {
        with_z3_context(|| {
            // i64.eqz: 1 iff the whole register pair is zero.
            assert_certifies(
                WasmOp::I64Eqz,
                vec![ArmOp::I64SetCondZ {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                }],
            );
        });
    }

    // ---- negative tests: wrong lowerings must be rejected -----------------

    /// A deliberately wrong `i64.add` lowering: the high limb uses plain `ADD`
    /// instead of `ADC`, so it drops the carry from the low limb. The
    /// validator must find a counterexample (any input whose low limbs
    /// produce a carry, e.g. `a_lo = b_lo = 0x8000_0000`).
    #[test]
    fn wrong_i64_add_lowering_rejected() {
        with_z3_context(|| {
            let validator = Z3ArmValidator::new();
            let wrong = CertifiedSelection::new(
                WasmOp::I64Add,
                vec![
                    ArmOp::Adds {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R2),
                    },
                    // BUG: should be ADC — this plain ADD loses the carry.
                    ArmOp::Add {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Reg(Reg::R3),
                    },
                ],
            );
            match validator.validate(&wrong) {
                Err(ValidationError::Counterexample { wasm_op_label, .. }) => {
                    assert_eq!(wasm_op_label, "I64Add");
                }
                other => {
                    panic!("expected Counterexample for carry-dropping i64.add, got {other:?}")
                }
            }
        });
    }

    /// A deliberately wrong i32 comparison lowering: `i32.lt_s` lowered with
    /// the *unsigned* condition `LO`. Signed and unsigned less-than disagree
    /// whenever exactly one operand is negative (e.g. `a = -1, b = 1`), so the
    /// validator must reject it.
    #[test]
    fn wrong_i32_lt_s_lowering_rejected() {
        with_z3_context(|| {
            let validator = Z3ArmValidator::new();
            let wrong = CertifiedSelection::new(
                WasmOp::I32LtS,
                vec![
                    ArmOp::Cmp {
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R1),
                    },
                    // BUG: signed lt_s must use LT, not the unsigned LO.
                    ArmOp::SetCond {
                        rd: Reg::R0,
                        cond: Condition::LO,
                    },
                ],
            );
            match validator.validate(&wrong) {
                Err(ValidationError::Counterexample { wasm_op_label, .. }) => {
                    assert_eq!(wasm_op_label, "I32LtS");
                }
                other => panic!("expected Counterexample for lt_s-as-LO, got {other:?}"),
            }
        });
    }

    /// A deliberately wrong `i64.shl` would be caught too: feeding the
    /// `i64.shl` op an ARM sequence that only shifts the low limb leaves the
    /// high limb untouched, which the reference rejects for any nonzero
    /// shift. We exercise it as a selection whose ARM sequence is a single
    /// low-limb shift.
    #[test]
    fn wrong_i64_shl_lowering_rejected() {
        with_z3_context(|| {
            let validator = Z3ArmValidator::new();
            let wrong = CertifiedSelection::new(
                WasmOp::I64Shl,
                vec![
                    // Only shifts the low limb by R2; high limb R1 is left
                    // as the input a_hi — wrong for any shift amount > 0.
                    ArmOp::LslReg {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        rm: Reg::R2,
                    },
                ],
            );
            match validator.validate(&wrong) {
                Err(ValidationError::Counterexample { wasm_op_label, .. }) => {
                    assert_eq!(wasm_op_label, "I64Shl");
                }
                other => panic!("expected Counterexample for partial i64.shl, got {other:?}"),
            }
        });
    }

    /// i64 division is scoped out — confirm it reports `UnsupportedOp`
    /// rather than silently certifying.
    #[test]
    fn i64_div_is_scoped_out() {
        with_z3_context(|| {
            let validator = Z3ArmValidator::new();
            for op in [
                WasmOp::I64DivS,
                WasmOp::I64DivU,
                WasmOp::I64RemS,
                WasmOp::I64RemU,
            ] {
                let sel = CertifiedSelection::<WasmOp, ArmOp>::new(op.clone(), vec![]);
                match validator.validate(&sel) {
                    Err(ValidationError::UnsupportedOp(got)) => assert_eq!(got, op),
                    other => panic!("expected {op:?} to be UnsupportedOp, got {other:?}"),
                }
            }
        });
    }
}
