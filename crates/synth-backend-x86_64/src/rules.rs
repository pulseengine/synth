//! The x86-64 lowering RULE TABLE for the simple integer ops — lane X2
//! (RQ-91-X86ALU, #1741).
//!
//! One row per wasm op: the operand type and the x86 form that computes it.
//! The selector ([`crate::selector`]) holds one generic routine per
//! [`Lowering`] shape (where the operands are, which temporary receives the
//! result); WHICH instruction a wasm op becomes is read from this table and
//! nowhere else. The table is data so that a model of the lowering can later
//! be GENERATED from it (the `sel_dsl::RULES` / #667 pattern) instead of
//! written out a second time by hand. No proof is claimed for x86-64 (VCR-X86-001 costs 2
//! and 3); the rows are checked by execution against kiln
//! (`crates/synth-oracle/tests/x86_64_alu_kiln_oracle.rs`).
//!
//! NOT IN THE TABLE, and declined by the selector by name: `div`/`rem` (the
//! x86 `div`/`idiv` FAULT on a zero divisor and on `INT_MIN / -1`, where wasm
//! traps on the first and returns 0 for `rem_s`; they need explicit guards,
//! lane X4), `clz`/`ctz`/`popcnt` (their one-instruction encodings are above
//! the baseline ISA level, lane X4), and every float op.

use synth_core::WasmOp;

use crate::inst::{AluOp, Cond, Ext, ShiftOp};

/// A wasm integer value type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    I32,
    I64,
}

/// The shape of one lowering.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lowering {
    /// `a = a OP b` with `op r/m, r`. `commutes` lets the result land in
    /// `b`'s temporary when `a` has none.
    Alu { op: AluOp, commutes: bool },
    /// `a = a * b` with `imul r, r/m` (commutes).
    Mul,
    /// `a = a SHIFT (b mod width)`, the count in `cl`.
    Shift(ShiftOp),
    /// `cmp a, b; setCC; movzbl` — an i32 0/1.
    Compare(Cond),
    /// `test a, a; sete; movzbl` — an i32 0/1.
    Eqz,
    /// A widening move of the operand's low part; `to` is the result type.
    Extend { ext: Ext, to: Ty },
    /// `i64.extend_i32_u`: a 32-bit `mov`, which zeroes bits 63:32.
    ZeroExtend,
    /// `i32.wrap_i64`: no instruction. The value keeps its register and is
    /// retyped; nothing reads bits 63:32 of an i32 value.
    Wrap,
}

/// One row: `op` takes operands of type `ty` and is lowered as `lower`.
#[derive(Clone, Debug, PartialEq)]
pub struct Rule {
    pub op: WasmOp,
    pub ty: Ty,
    pub lower: Lowering,
}

const fn alu(op: WasmOp, ty: Ty, alu: AluOp, commutes: bool) -> Rule {
    Rule {
        op,
        ty,
        lower: Lowering::Alu { op: alu, commutes },
    }
}

const fn shift(op: WasmOp, ty: Ty, s: ShiftOp) -> Rule {
    Rule {
        op,
        ty,
        lower: Lowering::Shift(s),
    }
}

const fn cmp(op: WasmOp, ty: Ty, c: Cond) -> Rule {
    Rule {
        op,
        ty,
        lower: Lowering::Compare(c),
    }
}

const fn ext(op: WasmOp, ty: Ty, ext: Ext, to: Ty) -> Rule {
    Rule {
        op,
        ty,
        lower: Lowering::Extend { ext, to },
    }
}

use Ty::{I32, I64};

/// The table. A wasm compare `a REL b` is `cmp a, b` followed by the x86
/// condition of the same name: signed `<` is `l`, unsigned `<` is `b`
/// (below), signed `>` is `g`, unsigned `>` is `a` (above).
pub static RULES: &[Rule] = &[
    // ---- i32 ----
    alu(WasmOp::I32Add, I32, AluOp::Add, true),
    alu(WasmOp::I32Sub, I32, AluOp::Sub, false),
    alu(WasmOp::I32And, I32, AluOp::And, true),
    alu(WasmOp::I32Or, I32, AluOp::Or, true),
    alu(WasmOp::I32Xor, I32, AluOp::Xor, true),
    Rule {
        op: WasmOp::I32Mul,
        ty: I32,
        lower: Lowering::Mul,
    },
    shift(WasmOp::I32Shl, I32, ShiftOp::Shl),
    shift(WasmOp::I32ShrS, I32, ShiftOp::Sar),
    shift(WasmOp::I32ShrU, I32, ShiftOp::Shr),
    shift(WasmOp::I32Rotl, I32, ShiftOp::Rol),
    shift(WasmOp::I32Rotr, I32, ShiftOp::Ror),
    cmp(WasmOp::I32Eq, I32, Cond::E),
    cmp(WasmOp::I32Ne, I32, Cond::Ne),
    cmp(WasmOp::I32LtS, I32, Cond::L),
    cmp(WasmOp::I32LtU, I32, Cond::B),
    cmp(WasmOp::I32GtS, I32, Cond::G),
    cmp(WasmOp::I32GtU, I32, Cond::A),
    cmp(WasmOp::I32LeS, I32, Cond::Le),
    cmp(WasmOp::I32LeU, I32, Cond::Be),
    cmp(WasmOp::I32GeS, I32, Cond::Ge),
    cmp(WasmOp::I32GeU, I32, Cond::Ae),
    Rule {
        op: WasmOp::I32Eqz,
        ty: I32,
        lower: Lowering::Eqz,
    },
    ext(WasmOp::I32Extend8S, I32, Ext::SxBL, I32),
    ext(WasmOp::I32Extend16S, I32, Ext::SxWL, I32),
    // ---- i64 ----
    alu(WasmOp::I64Add, I64, AluOp::Add, true),
    alu(WasmOp::I64Sub, I64, AluOp::Sub, false),
    alu(WasmOp::I64And, I64, AluOp::And, true),
    alu(WasmOp::I64Or, I64, AluOp::Or, true),
    alu(WasmOp::I64Xor, I64, AluOp::Xor, true),
    Rule {
        op: WasmOp::I64Mul,
        ty: I64,
        lower: Lowering::Mul,
    },
    shift(WasmOp::I64Shl, I64, ShiftOp::Shl),
    shift(WasmOp::I64ShrS, I64, ShiftOp::Sar),
    shift(WasmOp::I64ShrU, I64, ShiftOp::Shr),
    shift(WasmOp::I64Rotl, I64, ShiftOp::Rol),
    shift(WasmOp::I64Rotr, I64, ShiftOp::Ror),
    cmp(WasmOp::I64Eq, I64, Cond::E),
    cmp(WasmOp::I64Ne, I64, Cond::Ne),
    cmp(WasmOp::I64LtS, I64, Cond::L),
    cmp(WasmOp::I64LtU, I64, Cond::B),
    cmp(WasmOp::I64GtS, I64, Cond::G),
    cmp(WasmOp::I64GtU, I64, Cond::A),
    cmp(WasmOp::I64LeS, I64, Cond::Le),
    cmp(WasmOp::I64LeU, I64, Cond::Be),
    cmp(WasmOp::I64GeS, I64, Cond::Ge),
    cmp(WasmOp::I64GeU, I64, Cond::Ae),
    Rule {
        op: WasmOp::I64Eqz,
        ty: I64,
        lower: Lowering::Eqz,
    },
    ext(WasmOp::I64Extend8S, I64, Ext::SxBQ, I64),
    ext(WasmOp::I64Extend16S, I64, Ext::SxWQ, I64),
    ext(WasmOp::I64Extend32S, I64, Ext::SxLQ, I64),
    // ---- conversions ----
    ext(WasmOp::I64ExtendI32S, I32, Ext::SxLQ, I64),
    Rule {
        op: WasmOp::I64ExtendI32U,
        ty: I32,
        lower: Lowering::ZeroExtend,
    },
    Rule {
        op: WasmOp::I32WrapI64,
        ty: I64,
        lower: Lowering::Wrap,
    },
];

/// The rule for `op`, if the table has one.
pub fn rule_for(op: &WasmOp) -> Option<&'static Rule> {
    RULES.iter().find(|r| r.op == *op)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_op_has_at_most_one_rule() {
        for (i, a) in RULES.iter().enumerate() {
            for b in &RULES[i + 1..] {
                assert_ne!(a.op, b.op, "two rules for {:?}", a.op);
            }
        }
        assert_eq!(RULES.len(), 52);
    }

    /// The ops whose x86 instruction FAULTS where wasm does not, or whose
    /// short encoding is above the baseline, have no row.
    #[test]
    fn division_and_bit_counts_have_no_rule() {
        for op in [
            WasmOp::I32DivS,
            WasmOp::I32DivU,
            WasmOp::I32RemS,
            WasmOp::I32RemU,
            WasmOp::I64DivS,
            WasmOp::I64DivU,
            WasmOp::I64RemS,
            WasmOp::I64RemU,
            WasmOp::I32Clz,
            WasmOp::I32Ctz,
            WasmOp::I32Popcnt,
            WasmOp::I64Clz,
            WasmOp::I64Ctz,
            WasmOp::I64Popcnt,
        ] {
            assert!(rule_for(&op).is_none(), "{op:?} has a rule");
        }
    }

    /// Signedness is carried by the condition, and by the shift, never by the
    /// operand: a signed op must not share its rule with its unsigned twin.
    #[test]
    fn signed_and_unsigned_twins_differ() {
        for (s, u) in [
            (WasmOp::I32LtS, WasmOp::I32LtU),
            (WasmOp::I32GtS, WasmOp::I32GtU),
            (WasmOp::I32LeS, WasmOp::I32LeU),
            (WasmOp::I32GeS, WasmOp::I32GeU),
            (WasmOp::I32ShrS, WasmOp::I32ShrU),
            (WasmOp::I64LtS, WasmOp::I64LtU),
            (WasmOp::I64GtS, WasmOp::I64GtU),
            (WasmOp::I64LeS, WasmOp::I64LeU),
            (WasmOp::I64GeS, WasmOp::I64GeU),
            (WasmOp::I64ShrS, WasmOp::I64ShrU),
            (WasmOp::I64ExtendI32S, WasmOp::I64ExtendI32U),
        ] {
            let (a, b) = (rule_for(&s).unwrap(), rule_for(&u).unwrap());
            assert_eq!(a.ty, b.ty);
            assert_ne!(a.lower, b.lower, "{s:?} and {u:?} share a lowering");
        }
    }
}
