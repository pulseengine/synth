//! Solver-agnostic bitvector / boolean term types (#553).
//!
//! `BV` and `Bool` wrap [`ordeal::BvTerm`] / [`ordeal::BoolTerm`] behind the
//! exact method surface the semantics encoders (`wasm_semantics.rs`,
//! `arm_semantics.rs`) previously used from `z3::ast::{BV, Bool}` — so the
//! encoders stay in their native idiom while becoming solver-independent.
//! Both backends (the default pure-Rust `ordeal` engine and the optional
//! feature-gated Z3 differential oracle) consume these terms; see
//! `solver.rs`.
//!
//! # Commutative-operand canonicalization (interim shim)
//!
//! ordeal 0.4 has no term normalization yet (scoped upstream for ordeal
//! v0.8.0, pulseengine/ordeal#29): syntactically commuted operands of a
//! commutative op (`a*b` vs `b*a`) can blast to structurally distinct AIGs
//! and, for `Mul`, hit a CDCL cliff. Until v0.8.0 lands, the constructors for
//! the commutative ops (`bvadd`, `bvmul`, `bvand`, `bvor`, `bvxor`, and the
//! `Eq`/`Ne` predicates) order their operands by a deterministic structural
//! key, so both sides of an equivalence query build the *same* term for the
//! same commuted expression. This is a pure reordering of arguments to
//! commutative SMT-LIB operations — semantics are untouched (the Z3 oracle
//! sees the identical canonicalized query).

use ordeal::{BoolTerm, BvTerm, Sort};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;

/// Bit-mask of `width` low bits (saturating at 128).
fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// A bitvector term of a known width.
///
/// Mirrors the `z3::ast::BV` call surface used by the semantics encoders.
#[derive(Clone, Debug)]
pub struct BV {
    term: BvTerm,
    width: u32,
}

/// A boolean term (predicate).
///
/// Mirrors the `z3::ast::Bool` call surface used by the semantics encoders.
#[derive(Clone, Debug)]
pub struct Bool {
    term: BoolTerm,
}

// ---------------------------------------------------------------------------
// Structural ordering for canonicalization
// ---------------------------------------------------------------------------

fn bv_rank(t: &BvTerm) -> u8 {
    match t {
        BvTerm::Const { .. } => 0,
        BvTerm::Var { .. } => 1,
        BvTerm::Add(..) => 2,
        BvTerm::Sub(..) => 3,
        BvTerm::Mul(..) => 4,
        BvTerm::Udiv(..) => 5,
        BvTerm::And(..) => 6,
        BvTerm::Or(..) => 7,
        BvTerm::Xor(..) => 8,
        BvTerm::Shl(..) => 9,
        BvTerm::Lshr(..) => 10,
        BvTerm::Ashr(..) => 11,
        BvTerm::Rotr(..) => 12,
        BvTerm::Extract { .. } => 13,
        BvTerm::Concat(..) => 14,
        BvTerm::ZeroExt { .. } => 15,
        BvTerm::SignExt { .. } => 16,
        BvTerm::Ite { .. } => 17,
    }
}

fn bool_rank(t: &BoolTerm) -> u8 {
    match t {
        BoolTerm::Eq(..) => 0,
        BoolTerm::Ne(..) => 1,
        BoolTerm::Ult(..) => 2,
        BoolTerm::Ule(..) => 3,
        BoolTerm::Ugt(..) => 4,
        BoolTerm::Uge(..) => 5,
        BoolTerm::Slt(..) => 6,
        BoolTerm::Sle(..) => 7,
        BoolTerm::Sgt(..) => 8,
        BoolTerm::Sge(..) => 9,
        BoolTerm::Not(..) => 10,
        BoolTerm::And(..) => 11,
        BoolTerm::Or(..) => 12,
    }
}

/// Total, deterministic structural order over `BvTerm` (canonicalization key).
fn ord_bv(a: &BvTerm, b: &BvTerm) -> Ordering {
    bv_rank(a).cmp(&bv_rank(b)).then_with(|| match (a, b) {
        (
            BvTerm::Const {
                value: va,
                sort: sa,
            },
            BvTerm::Const {
                value: vb,
                sort: sb,
            },
        ) => sa.width.cmp(&sb.width).then(va.cmp(vb)),
        (BvTerm::Var { name: na, sort: sa }, BvTerm::Var { name: nb, sort: sb }) => {
            sa.width.cmp(&sb.width).then_with(|| na.cmp(nb))
        }
        (BvTerm::Add(a1, a2), BvTerm::Add(b1, b2))
        | (BvTerm::Sub(a1, a2), BvTerm::Sub(b1, b2))
        | (BvTerm::Mul(a1, a2), BvTerm::Mul(b1, b2))
        | (BvTerm::Udiv(a1, a2), BvTerm::Udiv(b1, b2))
        | (BvTerm::And(a1, a2), BvTerm::And(b1, b2))
        | (BvTerm::Or(a1, a2), BvTerm::Or(b1, b2))
        | (BvTerm::Xor(a1, a2), BvTerm::Xor(b1, b2))
        | (BvTerm::Shl(a1, a2), BvTerm::Shl(b1, b2))
        | (BvTerm::Lshr(a1, a2), BvTerm::Lshr(b1, b2))
        | (BvTerm::Ashr(a1, a2), BvTerm::Ashr(b1, b2))
        | (BvTerm::Rotr(a1, a2), BvTerm::Rotr(b1, b2))
        | (BvTerm::Concat(a1, a2), BvTerm::Concat(b1, b2)) => {
            ord_bv(a1, b1).then_with(|| ord_bv(a2, b2))
        }
        (
            BvTerm::Extract {
                hi: ha,
                lo: la,
                arg: aa,
            },
            BvTerm::Extract {
                hi: hb,
                lo: lb,
                arg: ab,
            },
        ) => ha.cmp(hb).then(la.cmp(lb)).then_with(|| ord_bv(aa, ab)),
        (BvTerm::ZeroExt { by: ba, arg: aa }, BvTerm::ZeroExt { by: bb, arg: ab })
        | (BvTerm::SignExt { by: ba, arg: aa }, BvTerm::SignExt { by: bb, arg: ab }) => {
            ba.cmp(bb).then_with(|| ord_bv(aa, ab))
        }
        (
            BvTerm::Ite {
                cond: ca,
                then_: ta,
                else_: ea,
            },
            BvTerm::Ite {
                cond: cb,
                then_: tb,
                else_: eb,
            },
        ) => ord_bool(ca, cb)
            .then_with(|| ord_bv(ta, tb))
            .then_with(|| ord_bv(ea, eb)),
        // Different ranks were handled above; same-rank pairs are all matched.
        _ => unreachable!("ord_bv: rank-equal variants are exhaustively matched"),
    })
}

/// Total, deterministic structural order over `BoolTerm`.
fn ord_bool(a: &BoolTerm, b: &BoolTerm) -> Ordering {
    bool_rank(a).cmp(&bool_rank(b)).then_with(|| match (a, b) {
        (BoolTerm::Eq(a1, a2), BoolTerm::Eq(b1, b2))
        | (BoolTerm::Ne(a1, a2), BoolTerm::Ne(b1, b2))
        | (BoolTerm::Ult(a1, a2), BoolTerm::Ult(b1, b2))
        | (BoolTerm::Ule(a1, a2), BoolTerm::Ule(b1, b2))
        | (BoolTerm::Ugt(a1, a2), BoolTerm::Ugt(b1, b2))
        | (BoolTerm::Uge(a1, a2), BoolTerm::Uge(b1, b2))
        | (BoolTerm::Slt(a1, a2), BoolTerm::Slt(b1, b2))
        | (BoolTerm::Sle(a1, a2), BoolTerm::Sle(b1, b2))
        | (BoolTerm::Sgt(a1, a2), BoolTerm::Sgt(b1, b2))
        | (BoolTerm::Sge(a1, a2), BoolTerm::Sge(b1, b2)) => {
            ord_bv(a1, b1).then_with(|| ord_bv(a2, b2))
        }
        (BoolTerm::Not(a1), BoolTerm::Not(b1)) => ord_bool(a1, b1),
        (BoolTerm::And(a1, a2), BoolTerm::And(b1, b2))
        | (BoolTerm::Or(a1, a2), BoolTerm::Or(b1, b2)) => {
            ord_bool(a1, b1).then_with(|| ord_bool(a2, b2))
        }
        _ => unreachable!("ord_bool: rank-equal variants are exhaustively matched"),
    })
}

/// Order two operands of a commutative op deterministically (the interim
/// canonicalization shim — see the module docs).
fn canonical_pair(a: BvTerm, b: BvTerm) -> (Box<BvTerm>, Box<BvTerm>) {
    if ord_bv(&a, &b) == Ordering::Greater {
        (Box::new(b), Box::new(a))
    } else {
        (Box::new(a), Box::new(b))
    }
}

/// Recursively canonicalize a term built *outside* the shim constructors
/// (`ordeal::lowering` helpers build e.g. `Mul(q, b)` verbatim): reorder
/// every commutative node bottom-up so shim-built and lowering-built
/// expressions of the same value share one structure. Without this, the two
/// sides of an equivalence query can differ by a commuted `Mul` — precisely
/// the CDCL cliff the canonicalization exists to avoid.
fn canonicalize_bv(t: &BvTerm) -> BvTerm {
    let bin = |a: &BvTerm, b: &BvTerm| (Box::new(canonicalize_bv(a)), Box::new(canonicalize_bv(b)));
    let comm = |a: &BvTerm, b: &BvTerm| canonical_pair(canonicalize_bv(a), canonicalize_bv(b));
    match t {
        BvTerm::Const { .. } | BvTerm::Var { .. } => t.clone(),
        BvTerm::Add(a, b) => {
            let (a, b) = comm(a, b);
            BvTerm::Add(a, b)
        }
        BvTerm::Mul(a, b) => {
            let (a, b) = comm(a, b);
            BvTerm::Mul(a, b)
        }
        BvTerm::And(a, b) => {
            let (a, b) = comm(a, b);
            BvTerm::And(a, b)
        }
        BvTerm::Or(a, b) => {
            let (a, b) = comm(a, b);
            BvTerm::Or(a, b)
        }
        BvTerm::Xor(a, b) => {
            let (a, b) = comm(a, b);
            BvTerm::Xor(a, b)
        }
        BvTerm::Sub(a, b) => {
            let (a, b) = bin(a, b);
            BvTerm::Sub(a, b)
        }
        BvTerm::Udiv(a, b) => {
            let (a, b) = bin(a, b);
            BvTerm::Udiv(a, b)
        }
        BvTerm::Shl(a, b) => {
            let (a, b) = bin(a, b);
            BvTerm::Shl(a, b)
        }
        BvTerm::Lshr(a, b) => {
            let (a, b) = bin(a, b);
            BvTerm::Lshr(a, b)
        }
        BvTerm::Ashr(a, b) => {
            let (a, b) = bin(a, b);
            BvTerm::Ashr(a, b)
        }
        BvTerm::Rotr(a, b) => {
            let (a, b) = bin(a, b);
            BvTerm::Rotr(a, b)
        }
        BvTerm::Concat(a, b) => {
            let (a, b) = bin(a, b);
            BvTerm::Concat(a, b)
        }
        BvTerm::Extract { hi, lo, arg } => BvTerm::Extract {
            hi: *hi,
            lo: *lo,
            arg: Box::new(canonicalize_bv(arg)),
        },
        BvTerm::ZeroExt { by, arg } => BvTerm::ZeroExt {
            by: *by,
            arg: Box::new(canonicalize_bv(arg)),
        },
        BvTerm::SignExt { by, arg } => BvTerm::SignExt {
            by: *by,
            arg: Box::new(canonicalize_bv(arg)),
        },
        BvTerm::Ite { cond, then_, else_ } => BvTerm::Ite {
            cond: Box::new(canonicalize_bool(cond)),
            then_: Box::new(canonicalize_bv(then_)),
            else_: Box::new(canonicalize_bv(else_)),
        },
    }
}

fn canonicalize_bool(t: &BoolTerm) -> BoolTerm {
    let bin = |a: &BvTerm, b: &BvTerm| (Box::new(canonicalize_bv(a)), Box::new(canonicalize_bv(b)));
    let comm = |a: &BvTerm, b: &BvTerm| canonical_pair(canonicalize_bv(a), canonicalize_bv(b));
    match t {
        BoolTerm::Eq(a, b) => {
            let (a, b) = comm(a, b);
            BoolTerm::Eq(a, b)
        }
        BoolTerm::Ne(a, b) => {
            let (a, b) = comm(a, b);
            BoolTerm::Ne(a, b)
        }
        BoolTerm::Ult(a, b) => {
            let (a, b) = bin(a, b);
            BoolTerm::Ult(a, b)
        }
        BoolTerm::Ule(a, b) => {
            let (a, b) = bin(a, b);
            BoolTerm::Ule(a, b)
        }
        BoolTerm::Ugt(a, b) => {
            let (a, b) = bin(a, b);
            BoolTerm::Ugt(a, b)
        }
        BoolTerm::Uge(a, b) => {
            let (a, b) = bin(a, b);
            BoolTerm::Uge(a, b)
        }
        BoolTerm::Slt(a, b) => {
            let (a, b) = bin(a, b);
            BoolTerm::Slt(a, b)
        }
        BoolTerm::Sle(a, b) => {
            let (a, b) = bin(a, b);
            BoolTerm::Sle(a, b)
        }
        BoolTerm::Sgt(a, b) => {
            let (a, b) = bin(a, b);
            BoolTerm::Sgt(a, b)
        }
        BoolTerm::Sge(a, b) => {
            let (a, b) = bin(a, b);
            BoolTerm::Sge(a, b)
        }
        BoolTerm::Not(a) => BoolTerm::Not(Box::new(canonicalize_bool(a))),
        BoolTerm::And(a, b) => BoolTerm::And(
            Box::new(canonicalize_bool(a)),
            Box::new(canonicalize_bool(b)),
        ),
        BoolTerm::Or(a, b) => BoolTerm::Or(
            Box::new(canonicalize_bool(a)),
            Box::new(canonicalize_bool(b)),
        ),
    }
}

// ---------------------------------------------------------------------------
// BV
// ---------------------------------------------------------------------------

impl BV {
    /// The underlying ordeal term (consumed by the Z3 oracle translation).
    #[cfg_attr(not(feature = "z3-solver"), allow(dead_code))]
    pub(crate) fn term(&self) -> &BvTerm {
        &self.term
    }

    /// If this is a free variable, its name.
    pub(crate) fn var_name(&self) -> Option<&str> {
        match &self.term {
            BvTerm::Var { name, .. } => Some(name),
            _ => None,
        }
    }

    /// A fresh free (symbolic) bitvector variable.
    pub fn new_const(name: impl Into<String>, width: u32) -> Self {
        Self {
            term: BvTerm::Var {
                name: name.into(),
                sort: Sort::new(width),
            },
            width,
        }
    }

    /// A concrete constant from a signed value (two's-complement, masked).
    pub fn from_i64(value: i64, width: u32) -> Self {
        Self {
            term: BvTerm::Const {
                value: (value as u64 as u128) & mask(width),
                sort: Sort::new(width),
            },
            width,
        }
    }

    /// A concrete constant from an unsigned value (masked to width).
    pub fn from_u64(value: u64, width: u32) -> Self {
        Self {
            term: BvTerm::Const {
                value: (value as u128) & mask(width),
                sort: Sort::new(width),
            },
            width,
        }
    }

    /// Bit width of this term.
    pub fn get_size(&self) -> u32 {
        self.width
    }

    fn binop(
        &self,
        other: impl Borrow<BV>,
        f: impl FnOnce(Box<BvTerm>, Box<BvTerm>) -> BvTerm,
    ) -> BV {
        let other = other.borrow();
        BV {
            term: f(Box::new(self.term.clone()), Box::new(other.term.clone())),
            width: self.width,
        }
    }

    fn commutative(
        &self,
        other: impl Borrow<BV>,
        f: impl FnOnce(Box<BvTerm>, Box<BvTerm>) -> BvTerm,
    ) -> BV {
        let other = other.borrow();
        let (a, b) = canonical_pair(self.term.clone(), other.term.clone());
        BV {
            term: f(a, b),
            width: self.width,
        }
    }

    // --- Arithmetic ---

    /// Modular addition.
    pub fn bvadd(&self, other: impl Borrow<BV>) -> BV {
        self.commutative(other, BvTerm::Add)
    }

    /// Modular subtraction.
    pub fn bvsub(&self, other: impl Borrow<BV>) -> BV {
        self.binop(other, BvTerm::Sub)
    }

    /// Modular multiplication.
    pub fn bvmul(&self, other: impl Borrow<BV>) -> BV {
        self.commutative(other, BvTerm::Mul)
    }

    /// Unsigned division (SMT-LIB: division by zero yields all-ones).
    pub fn bvudiv(&self, other: impl Borrow<BV>) -> BV {
        self.binop(other, BvTerm::Udiv)
    }

    /// Signed division (SMT-LIB semantics, via `ordeal::lowering`).
    pub fn bvsdiv(&self, other: impl Borrow<BV>) -> BV {
        BV {
            term: canonicalize_bv(&ordeal::lowering::bvsdiv(
                self.term.clone(),
                other.borrow().term.clone(),
                self.width,
            )),
            width: self.width,
        }
    }

    /// Unsigned remainder (via `ordeal::lowering`).
    pub fn bvurem(&self, other: impl Borrow<BV>) -> BV {
        BV {
            term: canonicalize_bv(&ordeal::lowering::bvurem(
                self.term.clone(),
                other.borrow().term.clone(),
                self.width,
            )),
            width: self.width,
        }
    }

    /// Signed remainder (via `ordeal::lowering`).
    pub fn bvsrem(&self, other: impl Borrow<BV>) -> BV {
        BV {
            term: canonicalize_bv(&ordeal::lowering::bvsrem(
                self.term.clone(),
                other.borrow().term.clone(),
                self.width,
            )),
            width: self.width,
        }
    }

    /// Two's-complement negation (via `ordeal::lowering`).
    pub fn bvneg(&self) -> BV {
        BV {
            term: canonicalize_bv(&ordeal::lowering::bvneg(self.term.clone(), self.width)),
            width: self.width,
        }
    }

    // --- Bitwise ---

    /// Bitwise AND.
    pub fn bvand(&self, other: impl Borrow<BV>) -> BV {
        self.commutative(other, BvTerm::And)
    }

    /// Bitwise OR.
    pub fn bvor(&self, other: impl Borrow<BV>) -> BV {
        self.commutative(other, BvTerm::Or)
    }

    /// Bitwise XOR.
    pub fn bvxor(&self, other: impl Borrow<BV>) -> BV {
        self.commutative(other, BvTerm::Xor)
    }

    /// Bitwise NOT (via `ordeal::lowering`).
    pub fn bvnot(&self) -> BV {
        BV {
            term: canonicalize_bv(&ordeal::lowering::bvnot(self.term.clone(), self.width)),
            width: self.width,
        }
    }

    // --- Shifts / rotates ---

    /// Logical shift left (SMT-LIB oversize semantics: amount >= width → 0).
    pub fn bvshl(&self, other: impl Borrow<BV>) -> BV {
        self.binop(other, BvTerm::Shl)
    }

    /// Logical shift right.
    pub fn bvlshr(&self, other: impl Borrow<BV>) -> BV {
        self.binop(other, BvTerm::Lshr)
    }

    /// Arithmetic shift right.
    pub fn bvashr(&self, other: impl Borrow<BV>) -> BV {
        self.binop(other, BvTerm::Ashr)
    }

    /// Rotate left by a term amount (via `ordeal::lowering`).
    pub fn bvrotl(&self, other: impl Borrow<BV>) -> BV {
        BV {
            term: canonicalize_bv(&ordeal::lowering::bvrotl(
                self.term.clone(),
                other.borrow().term.clone(),
                self.width,
            )),
            width: self.width,
        }
    }

    /// Rotate right by a term amount.
    pub fn bvrotr(&self, other: impl Borrow<BV>) -> BV {
        self.binop(other, BvTerm::Rotr)
    }

    // --- Structural ---

    /// Bit extraction `[hi:lo]` (inclusive).
    pub fn extract(&self, hi: u32, lo: u32) -> BV {
        BV {
            term: BvTerm::Extract {
                hi,
                lo,
                arg: Box::new(self.term.clone()),
            },
            width: hi - lo + 1,
        }
    }

    /// Concatenation: `self` becomes the high bits.
    pub fn concat(&self, other: impl Borrow<BV>) -> BV {
        let other = other.borrow();
        BV {
            term: BvTerm::Concat(Box::new(self.term.clone()), Box::new(other.term.clone())),
            width: self.width + other.width,
        }
    }

    /// Zero-extension by `by` bits.
    pub fn zero_ext(&self, by: u32) -> BV {
        BV {
            term: BvTerm::ZeroExt {
                by,
                arg: Box::new(self.term.clone()),
            },
            width: self.width + by,
        }
    }

    /// Sign-extension by `by` bits.
    pub fn sign_ext(&self, by: u32) -> BV {
        BV {
            term: BvTerm::SignExt {
                by,
                arg: Box::new(self.term.clone()),
            },
            width: self.width + by,
        }
    }

    // --- Predicates ---

    fn cmp_op(
        &self,
        other: impl Borrow<BV>,
        f: impl FnOnce(Box<BvTerm>, Box<BvTerm>) -> BoolTerm,
    ) -> Bool {
        Bool {
            term: f(
                Box::new(self.term.clone()),
                Box::new(other.borrow().term.clone()),
            ),
        }
    }

    /// Equality predicate (canonicalized — `=` is commutative).
    pub fn eq(&self, other: impl Borrow<BV>) -> Bool {
        let (a, b) = canonical_pair(self.term.clone(), other.borrow().term.clone());
        Bool {
            term: BoolTerm::Eq(a, b),
        }
    }

    /// Disequality predicate (canonicalized — `distinct` is commutative).
    pub fn ne(&self, other: impl Borrow<BV>) -> Bool {
        let (a, b) = canonical_pair(self.term.clone(), other.borrow().term.clone());
        Bool {
            term: BoolTerm::Ne(a, b),
        }
    }

    /// Unsigned less-than.
    pub fn bvult(&self, other: impl Borrow<BV>) -> Bool {
        self.cmp_op(other, BoolTerm::Ult)
    }

    /// Unsigned less-or-equal.
    pub fn bvule(&self, other: impl Borrow<BV>) -> Bool {
        self.cmp_op(other, BoolTerm::Ule)
    }

    /// Unsigned greater-than.
    pub fn bvugt(&self, other: impl Borrow<BV>) -> Bool {
        self.cmp_op(other, BoolTerm::Ugt)
    }

    /// Unsigned greater-or-equal.
    pub fn bvuge(&self, other: impl Borrow<BV>) -> Bool {
        self.cmp_op(other, BoolTerm::Uge)
    }

    /// Signed less-than.
    pub fn bvslt(&self, other: impl Borrow<BV>) -> Bool {
        self.cmp_op(other, BoolTerm::Slt)
    }

    /// Signed less-or-equal.
    pub fn bvsle(&self, other: impl Borrow<BV>) -> Bool {
        self.cmp_op(other, BoolTerm::Sle)
    }

    /// Signed greater-than.
    pub fn bvsgt(&self, other: impl Borrow<BV>) -> Bool {
        self.cmp_op(other, BoolTerm::Sgt)
    }

    /// Signed greater-or-equal.
    pub fn bvsge(&self, other: impl Borrow<BV>) -> Bool {
        self.cmp_op(other, BoolTerm::Sge)
    }

    // --- Constant folding (test convenience; mirrors z3's simplify()) ---

    /// Return `self` unchanged; pair with [`BV::as_i64`] / [`BV::as_u64`],
    /// which concretely evaluate closed terms (the z3 idiom
    /// `x.simplify().as_i64()` keeps working).
    pub fn simplify(&self) -> BV {
        self.clone()
    }

    /// Concrete value of a closed (variable-free) term, as z3's `as_i64`
    /// reports it: the *unsigned* value when it fits in `i64`.
    pub fn as_i64(&self) -> Option<i64> {
        self.eval_closed().and_then(|v| i64::try_from(v).ok())
    }

    /// Concrete value of a closed (variable-free) term as `u64`.
    pub fn as_u64(&self) -> Option<u64> {
        self.eval_closed().and_then(|v| u64::try_from(v).ok())
    }

    fn eval_closed(&self) -> Option<u128> {
        ordeal::eval::eval_bv(&self.term, &ordeal::eval::Env::new()).ok()
    }
}

// ---------------------------------------------------------------------------
// Bool
// ---------------------------------------------------------------------------

impl Bool {
    /// The underlying ordeal term.
    pub(crate) fn term(&self) -> &BoolTerm {
        &self.term
    }

    /// A fresh free (symbolic) boolean variable.
    ///
    /// ordeal's fragment has no boolean variables, so this is encoded as
    /// `var != 0` over a fresh 1-bit bitvector variable — an exact bridge.
    pub fn new_const(name: impl Into<String>) -> Self {
        let var = BvTerm::Var {
            name: name.into(),
            sort: Sort::new(1),
        };
        Self {
            term: BoolTerm::Ne(
                Box::new(var),
                Box::new(BvTerm::Const {
                    value: 0,
                    sort: Sort::new(1),
                }),
            ),
        }
    }

    /// The boolean literal `true` / `false`.
    pub fn from_bool(value: bool) -> Self {
        Self::literal(value)
    }

    /// Boolean equality (iff), encoded as `(a ∧ b) ∨ (¬a ∧ ¬b)` — the
    /// fragment has no native boolean `=`.
    pub fn eq(&self, other: impl Borrow<Bool>) -> Bool {
        let a = self.term.clone();
        let b = other.borrow().term.clone();
        Bool {
            term: BoolTerm::Or(
                Box::new(BoolTerm::And(Box::new(a.clone()), Box::new(b.clone()))),
                Box::new(BoolTerm::And(
                    Box::new(BoolTerm::Not(Box::new(a))),
                    Box::new(BoolTerm::Not(Box::new(b))),
                )),
            ),
        }
    }

    /// Logical negation.
    pub fn not(&self) -> Bool {
        Bool {
            term: BoolTerm::Not(Box::new(self.term.clone())),
        }
    }

    /// N-ary conjunction (empty slice is `true`).
    pub fn and(values: &[&Bool]) -> Bool {
        Self::fold(values, BoolTerm::And, true)
    }

    /// N-ary disjunction (empty slice is `false`).
    pub fn or(values: &[&Bool]) -> Bool {
        Self::fold(values, BoolTerm::Or, false)
    }

    fn fold(
        values: &[&Bool],
        f: impl Fn(Box<BoolTerm>, Box<BoolTerm>) -> BoolTerm,
        empty: bool,
    ) -> Bool {
        let mut iter = values.iter();
        let Some(first) = iter.next() else {
            return Self::literal(empty);
        };
        let mut acc = first.term.clone();
        for v in iter {
            acc = f(Box::new(acc), Box::new(v.term.clone()));
        }
        Bool { term: acc }
    }

    /// The boolean literal `true` / `false` (as a trivially decided
    /// comparison — the fragment has no boolean constants).
    fn literal(value: bool) -> Bool {
        let zero = || {
            Box::new(BvTerm::Const {
                value: 0,
                sort: Sort::new(1),
            })
        };
        Bool {
            term: if value {
                BoolTerm::Eq(zero(), zero())
            } else {
                BoolTerm::Ne(zero(), zero())
            },
        }
    }

    /// If-then-else over bitvector branches (the bool→BV bridge;
    /// `BvTerm::Ite` is native in ordeal 0.4).
    pub fn ite(&self, then_: impl Borrow<BV>, else_: impl Borrow<BV>) -> BV {
        let then_ = then_.borrow();
        let else_ = else_.borrow();
        BV {
            term: BvTerm::Ite {
                cond: Box::new(self.term.clone()),
                then_: Box::new(then_.term.clone()),
                else_: Box::new(else_.term.clone()),
            },
            width: then_.width,
        }
    }

    /// Return `self` unchanged; pair with [`Bool::as_bool`], which concretely
    /// evaluates closed predicates (the z3 `simplify().as_bool()` idiom).
    pub fn simplify(&self) -> Bool {
        self.clone()
    }

    /// Concrete value of a closed (variable-free) predicate.
    pub fn as_bool(&self) -> Option<bool> {
        ordeal::eval::eval_bool(&self.term, &ordeal::eval::Env::new()).ok()
    }
}

// ---------------------------------------------------------------------------
// Display (SMT-LIB-style mnemonics; used by tests and diagnostics)
// ---------------------------------------------------------------------------

fn fmt_bv(t: &BvTerm, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match t {
        BvTerm::Const { value, sort } => write!(f, "(_ bv{} {})", value, sort.width),
        BvTerm::Var { name, .. } => write!(f, "{}", name),
        BvTerm::Add(a, b) => fmt_bin(f, "bvadd", a, b),
        BvTerm::Sub(a, b) => fmt_bin(f, "bvsub", a, b),
        BvTerm::Mul(a, b) => fmt_bin(f, "bvmul", a, b),
        BvTerm::Udiv(a, b) => fmt_bin(f, "bvudiv", a, b),
        BvTerm::And(a, b) => fmt_bin(f, "bvand", a, b),
        BvTerm::Or(a, b) => fmt_bin(f, "bvor", a, b),
        BvTerm::Xor(a, b) => fmt_bin(f, "bvxor", a, b),
        BvTerm::Shl(a, b) => fmt_bin(f, "bvshl", a, b),
        BvTerm::Lshr(a, b) => fmt_bin(f, "bvlshr", a, b),
        BvTerm::Ashr(a, b) => fmt_bin(f, "bvashr", a, b),
        BvTerm::Rotr(a, b) => fmt_bin(f, "bvrotr", a, b),
        BvTerm::Extract { hi, lo, arg } => {
            write!(f, "((_ extract {} {}) ", hi, lo)?;
            fmt_bv(arg, f)?;
            write!(f, ")")
        }
        BvTerm::Concat(a, b) => fmt_bin(f, "concat", a, b),
        BvTerm::ZeroExt { by, arg } => {
            write!(f, "((_ zero_extend {}) ", by)?;
            fmt_bv(arg, f)?;
            write!(f, ")")
        }
        BvTerm::SignExt { by, arg } => {
            write!(f, "((_ sign_extend {}) ", by)?;
            fmt_bv(arg, f)?;
            write!(f, ")")
        }
        BvTerm::Ite { cond, then_, else_ } => {
            write!(f, "(ite ")?;
            fmt_bool(cond, f)?;
            write!(f, " ")?;
            fmt_bv(then_, f)?;
            write!(f, " ")?;
            fmt_bv(else_, f)?;
            write!(f, ")")
        }
    }
}

fn fmt_bin(f: &mut fmt::Formatter<'_>, op: &str, a: &BvTerm, b: &BvTerm) -> fmt::Result {
    write!(f, "({} ", op)?;
    fmt_bv(a, f)?;
    write!(f, " ")?;
    fmt_bv(b, f)?;
    write!(f, ")")
}

fn fmt_bool(t: &BoolTerm, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let bin = |f: &mut fmt::Formatter<'_>, op: &str, a: &BvTerm, b: &BvTerm| -> fmt::Result {
        write!(f, "({} ", op)?;
        fmt_bv(a, f)?;
        write!(f, " ")?;
        fmt_bv(b, f)?;
        write!(f, ")")
    };
    match t {
        BoolTerm::Eq(a, b) => bin(f, "=", a, b),
        BoolTerm::Ne(a, b) => bin(f, "distinct", a, b),
        BoolTerm::Ult(a, b) => bin(f, "bvult", a, b),
        BoolTerm::Ule(a, b) => bin(f, "bvule", a, b),
        BoolTerm::Ugt(a, b) => bin(f, "bvugt", a, b),
        BoolTerm::Uge(a, b) => bin(f, "bvuge", a, b),
        BoolTerm::Slt(a, b) => bin(f, "bvslt", a, b),
        BoolTerm::Sle(a, b) => bin(f, "bvsle", a, b),
        BoolTerm::Sgt(a, b) => bin(f, "bvsgt", a, b),
        BoolTerm::Sge(a, b) => bin(f, "bvsge", a, b),
        BoolTerm::Not(a) => {
            write!(f, "(not ")?;
            fmt_bool(a, f)?;
            write!(f, ")")
        }
        BoolTerm::And(a, b) => {
            write!(f, "(and ")?;
            fmt_bool(a, f)?;
            write!(f, " ")?;
            fmt_bool(b, f)?;
            write!(f, ")")
        }
        BoolTerm::Or(a, b) => {
            write!(f, "(or ")?;
            fmt_bool(a, f)?;
            write!(f, " ")?;
            fmt_bool(b, f)?;
            write!(f, ")")
        }
    }
}

impl fmt::Display for BV {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_bv(&self.term, f)
    }
}

impl fmt::Display for Bool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_bool(&self.term, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn const_folding_matches_z3_idiom() {
        let a = BV::from_i64(40, 32);
        let b = BV::from_i64(2, 32);
        assert_eq!(a.bvadd(&b).simplify().as_i64(), Some(42));
        assert_eq!(a.bvsub(&b).simplify().as_i64(), Some(38));
        // as_i64 reports the unsigned value (z3 behavior the tests rely on).
        assert_eq!(BV::from_i64(-1, 32).as_i64(), Some(0xFFFF_FFFF));
    }

    #[test]
    fn commutative_construction_is_canonical() {
        let x = BV::new_const("x", 32);
        let y = BV::new_const("y", 32);
        // a*b and b*a must build the identical term (the v0.8.0 interim shim).
        assert_eq!(x.bvmul(&y).to_string(), y.bvmul(&x).to_string());
        assert_eq!(x.bvadd(&y).to_string(), y.bvadd(&x).to_string());
        assert_eq!(x.eq(&y).to_string(), y.eq(&x).to_string());
        // Non-commutative ops must NOT be reordered.
        assert_ne!(x.bvsub(&y).to_string(), y.bvsub(&x).to_string());
    }

    #[test]
    fn display_uses_smtlib_mnemonics() {
        let x = BV::new_const("x", 32);
        let s = x.bvadd(BV::from_i64(1, 32)).to_string();
        assert!(s.contains("bvadd"), "{s}");
    }
}
