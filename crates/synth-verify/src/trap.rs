//! Trap-preservation obligations (VCR-VER-002, synth #166 / ordeal#59).
//!
//! WASM operations like `div_s`, `load`/`store`, `call_indirect`, and
//! `unreachable` are **partial**: they trap on some inputs. A validator that
//! proves only *value* equivalence over a total model cannot see a lowering that
//! **drops a trap** — deleting a trapping guard looks value-equal
//! (synth#633/#666/#665/#642/#709). This module is the thin synth-facing layer
//! over [`ordeal::trap`]: it maps synth's [`WasmOp`]s to trap conditions built
//! over synth's own [`BV`]/[`Bool`] terms, and exposes the trap-preservation
//! gate so "the trap survived the lowering" becomes a checkable obligation.
//!
//! # Boundary (unchanged from ordeal#59)
//!
//! ordeal *classifies* operand/pointer bits — it never models op *values* (those
//! are consumer-supplied) and does no floating-point arithmetic. Every builder
//! here is a `Bool`/`BV` over the existing closed QF_BV fragment. A verdict of
//! [`TrapVerdict::Preserved`] is an ordeal `Unsat` whose LRAT certificate is
//! re-checked before it is returned, so soundness is that of the normal
//! certificate-checked pipeline.
//!
//! # Which VC for which op class
//!
//! - **div/rem** — the ARM lowering carries a value (the quotient/remainder), so
//!   the full [`prove_trap_equivalence`] (trap clause **and** guarded value
//!   clause) applies.
//! - **load/store, call_indirect, unreachable** — synth models no memory
//!   *contents* nor table *values*, so these use
//!   [`prove_trap_condition_equivalence`] (trap clause only). This is the
//!   ordeal#59 agreement.

use crate::term::{BV, Bool};
use ordeal::CheckResult;
use ordeal::trap as ot;
use synth_core::WasmOp;

pub use ordeal::trap::DivOp;

/// A value paired with the condition under which the op **traps** instead of
/// producing it — the synth-`BV`/`Bool` mirror of [`ordeal::trap::DefineOrTrap`].
/// `value` is the op's result (e.g. the ARM quotient); `may_trap` is one of the
/// trap-condition builders below.
#[derive(Clone, Debug)]
pub struct DefineOrTrap {
    /// The op's result value.
    pub value: BV,
    /// The condition under which the op traps.
    pub may_trap: Bool,
}

impl DefineOrTrap {
    fn to_ordeal(&self) -> ot::DefineOrTrap {
        ot::DefineOrTrap {
            value: self.value.term().clone(),
            may_trap: self.may_trap.term().clone(),
        }
    }
}

/// The type-check mode of a `call_indirect`, per its table — the synth-`BV`
/// mirror of [`ordeal::trap::TypeTrap`].
pub enum TypeTrap<'a> {
    /// Heterogeneous table: the element type is checked at runtime against the
    /// call's expected type id.
    Runtime {
        /// The table element's runtime type-id term.
        actual_type_id: &'a BV,
        /// The call site's expected type-id term.
        expected_id: &'a BV,
    },
    /// Closed-world / homogeneous table: the signature is discharged at compile
    /// time by the selector (synth's default — `ArmOp::CallIndirect.type_check`
    /// is `None`), so there is no runtime type-id and the type clause is `false`.
    StaticallyDischarged,
}

/// The operands of a `call_indirect` trap check (WASM §4.4.8) — the synth-`BV`
/// mirror of [`ordeal::trap::CallIndirect`].
pub struct CallIndirect<'a> {
    /// The table index operand.
    pub index: &'a BV,
    /// The table's element count.
    pub table_size: &'a BV,
    /// The loaded funcref word; a null (zero) slot traps before the call.
    pub slot_ptr: &'a BV,
    /// How the element's type is checked.
    pub type_trap: TypeTrap<'a>,
}

/// The verdict of a trap-preservation gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TrapVerdict {
    /// `Unsat` — the lowering preserves the trap (and, for the full VC, the
    /// value). The underlying LRAT certificate re-checked successfully.
    Preserved,
    /// `Sat` — a counterexample input under which the trap was dropped (or
    /// spuriously added). Carries the model's variable → value assignments.
    Dropped(Vec<(String, u128)>),
    /// `Unknown` — conservative: do **not** accept. Also returned if a
    /// `Preserved` certificate fails to re-check (an internal soundness alarm).
    Unknown,
}

// ---------------------------------------------------------------------------
// Trap-condition builders (WasmOp → Bool over operand bits)
// ---------------------------------------------------------------------------

/// Map a division/remainder [`WasmOp`] (i32 or i64) to its [`DivOp`]; `None`
/// for any non-div/rem op.
pub fn div_op(op: &WasmOp) -> Option<DivOp> {
    Some(match op {
        WasmOp::I32DivU | WasmOp::I64DivU => DivOp::DivU,
        WasmOp::I32DivS | WasmOp::I64DivS => DivOp::DivS,
        WasmOp::I32RemU | WasmOp::I64RemU => DivOp::RemU,
        WasmOp::I32RemS | WasmOp::I64RemS => DivOp::RemS,
        _ => return None,
    })
}

/// Trap condition for a div/rem op: divide-by-zero (all four) plus
/// `INT_MIN / -1` signed overflow (`div_s`/`rem_s`). The width is taken from
/// `dividend` — pass 32-bit terms for i32 ops, 64-bit for i64.
pub fn trap_div(op: DivOp, dividend: &BV, divisor: &BV) -> Bool {
    Bool::from_ordeal(ot::trap_div(
        op,
        dividend.term(),
        divisor.term(),
        dividend.get_size(),
    ))
}

/// Trap condition for `unreachable`: an unconditional trap.
pub fn trap_always() -> Bool {
    Bool::from_ordeal(ot::trap_always())
}

/// Trap condition for an OOB `load`/`store`: a `size`-byte access at `addr`
/// exceeds `mem_bound` (`addr + size >u mem_bound`, wraparound-safe). `addr`,
/// `size`, and `mem_bound` must share a width; `mem_bound` is synth's symbolic
/// native-pointer linear-memory extent.
pub fn trap_mem_oob(addr: &BV, size: &BV, mem_bound: &BV) -> Bool {
    Bool::from_ordeal(ot::trap_mem_oob(addr.term(), size.term(), mem_bound.term()))
}

/// Trap condition for `call_indirect`: `bounds ∨ null-slot ∨ type`.
pub fn trap_call_indirect(ci: &CallIndirect) -> Bool {
    // Bind the runtime type-id borrows so the `ot::TypeTrap` refs outlive the
    // `trap_call_indirect` call.
    let type_trap = match &ci.type_trap {
        TypeTrap::Runtime {
            actual_type_id,
            expected_id,
        } => ot::TypeTrap::Runtime {
            actual_type_id: actual_type_id.term(),
            expected_id: expected_id.term(),
        },
        TypeTrap::StaticallyDischarged => ot::TypeTrap::StaticallyDischarged,
    };
    let oci = ot::CallIndirect {
        index: ci.index.term(),
        table_size: ci.table_size.term(),
        slot_ptr: ci.slot_ptr.term(),
        type_trap,
    };
    Bool::from_ordeal(ot::trap_call_indirect(&oci))
}

// ---------------------------------------------------------------------------
// The gate
// ---------------------------------------------------------------------------

fn verdict(result: CheckResult) -> TrapVerdict {
    match result {
        CheckResult::Unsat(cert) => match cert.recheck() {
            Ok(()) => TrapVerdict::Preserved,
            // A certificate that does not re-check is an internal soundness
            // alarm — never report it as preserved.
            Err(_) => TrapVerdict::Unknown,
        },
        CheckResult::Sat(model) => TrapVerdict::Dropped(model.assignments),
        CheckResult::Unknown => TrapVerdict::Unknown,
    }
}

/// Full trap-preservation gate (trap clause **and** guarded value clause) — for
/// ops whose value synth models (div/rem). [`TrapVerdict::Preserved`] ⟹ the
/// lowering preserves both traps and values.
pub fn prove_trap_equivalence(orig: &DefineOrTrap, opt: &DefineOrTrap) -> TrapVerdict {
    verdict(ot::prove_trap_equivalence(
        &orig.to_ordeal(),
        &opt.to_ordeal(),
    ))
}

/// Trap-clause-only gate (`orig.may_trap ⇔ opt.may_trap`) — for ops whose value
/// synth does not model (load/store, call_indirect, unreachable).
/// [`TrapVerdict::Preserved`] ⟹ the lowering neither drops nor spuriously adds
/// the trap.
pub fn prove_trap_condition_equivalence(orig_may_trap: &Bool, opt_may_trap: &Bool) -> TrapVerdict {
    verdict(ot::prove_trap_condition_equivalence(
        orig_may_trap.term(),
        opt_may_trap.term(),
    ))
}
