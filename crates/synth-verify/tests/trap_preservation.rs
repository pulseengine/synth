//! Red-first trap-preservation gate (VCR-VER-002, synth #166 / ordeal#59).
//!
//! For each partial-op class, this constructs the correct WASM trap semantics
//! (`orig`) and two lowerings:
//!
//!   * a **trap-DROPPING** lowering (the #633/#666/#665/#642/#709 bug shape —
//!     value kept, guard removed) ⇒ the gate must return
//!     [`TrapVerdict::Dropped`] (the drop is CAUGHT), and
//!   * a **trap-PRESERVING** lowering (`opt.may_trap ≡ orig.may_trap`) ⇒ the
//!     gate must return [`TrapVerdict::Preserved`] (accepted).
//!
//! Proving both directions for every class is what makes the gate
//! non-vacuous: it actually rejects the exact trap-drop bug shapes rather than
//! trivially accepting everything.
//!
//! div/rem carry a value synth models, so they use the full
//! [`prove_trap_equivalence`] (trap + guarded value). load/store,
//! call_indirect, and unreachable have no synth value/contents model, so they
//! use [`prove_trap_condition_equivalence`] (trap clause only) — the ordeal#59
//! agreement.

use synth_verify::term::{BV, Bool};
use synth_verify::trap::{
    CallIndirect, DefineOrTrap, DivOp, TrapVerdict, TypeTrap, prove_trap_condition_equivalence,
    prove_trap_equivalence, trap_always, trap_call_indirect, trap_div, trap_mem_oob,
};

fn v(name: &str, width: u32) -> BV {
    BV::new_const(name, width)
}

fn assert_dropped(verdict: TrapVerdict, class: &str) {
    assert!(
        matches!(verdict, TrapVerdict::Dropped(_)),
        "{class}: a trap-DROPPING lowering must be CAUGHT (Dropped/Sat), got {verdict:?}"
    );
}

fn assert_preserved(verdict: TrapVerdict, class: &str) {
    assert_eq!(
        verdict,
        TrapVerdict::Preserved,
        "{class}: a trap-PRESERVING lowering must be accepted (Preserved/Unsat)"
    );
}

// ---------------------------------------------------------------------------
// div/rem — full VC (trap clause + guarded value clause)
// ---------------------------------------------------------------------------

/// Build the correct div/rem `DefineOrTrap` over 32-bit `a`/`b`.
fn div_orig(op: DivOp, a: &BV, b: &BV, value: BV) -> DefineOrTrap {
    DefineOrTrap {
        value,
        may_trap: trap_div(op, a, b),
    }
}

#[test]
fn div_rem_all_four_ops_catch_the_drop_and_accept_preservation() {
    for (op, name) in [
        (DivOp::DivU, "i32.div_u"),
        (DivOp::DivS, "i32.div_s"),
        (DivOp::RemU, "i32.rem_u"),
        (DivOp::RemS, "i32.rem_s"),
    ] {
        let a = v("a", 32);
        let b = v("b", 32);
        // The value synth models — any total function of the operands; the
        // guarded value clause only fires under ¬trap, so use a representative.
        let value = match op {
            DivOp::DivU => a.bvudiv(&b),
            DivOp::DivS => a.bvsdiv(&b),
            DivOp::RemU => a.bvurem(&b),
            DivOp::RemS => a.bvsrem(&b),
        };

        let orig = div_orig(op, &a, &b, value.clone());

        // Trap-DROPPING lowering: keeps the value, drops the guard entirely
        // (may_trap = false). The #633/#666 shape.
        let dropped = DefineOrTrap {
            value: value.clone(),
            may_trap: Bool::from_bool(false),
        };
        let verdict = prove_trap_equivalence(&orig, &dropped);
        assert_dropped(verdict.clone(), name);
        // The counterexample must exhibit the trap: divisor 0.
        if let TrapVerdict::Dropped(model) = verdict {
            let b_val = model.iter().find(|(n, _)| n == "b").map(|(_, x)| *x);
            assert_eq!(
                b_val,
                Some(0),
                "{name}: div-by-zero counterexample must set the divisor to 0"
            );
        }

        // Trap-PRESERVING lowering: same trap + same value.
        let preserved = div_orig(op, &a, &b, value);
        assert_preserved(prove_trap_equivalence(&orig, &preserved), name);
    }
}

#[test]
fn signed_div_overflow_only_drop_is_caught() {
    // A lowering that keeps the ÷0 guard but silently drops the INT_MIN/-1
    // overflow guard (a partial #642-class drop) must still be caught.
    let a = v("a", 32);
    let b = v("b", 32);
    let value = a.bvsdiv(&b);
    let orig = DefineOrTrap {
        value: value.clone(),
        may_trap: trap_div(DivOp::DivS, &a, &b), // ÷0 ∨ overflow
    };
    let overflow_dropped = DefineOrTrap {
        value,
        may_trap: trap_div(DivOp::DivU, &a, &b), // ÷0 only — overflow clause gone
    };
    assert_dropped(
        prove_trap_equivalence(&orig, &overflow_dropped),
        "i32.div_s (overflow-guard drop)",
    );
}

// ---------------------------------------------------------------------------
// load/store — trap-clause-only VC (OOB bounds)
// ---------------------------------------------------------------------------

#[test]
fn load_store_oob_bounds_drop_is_caught_and_preservation_accepted() {
    let addr = v("addr", 32);
    let bound = v("mem_bound", 32);
    let size = BV::from_u64(4, 32); // 4-byte access
    let orig_trap = trap_mem_oob(&addr, &size, &bound);

    // Trap-DROPPING lowering: the bounds check was removed (never traps).
    let dropped_trap = Bool::from_bool(false);
    assert_dropped(
        prove_trap_condition_equivalence(&orig_trap, &dropped_trap),
        "i32.store (OOB bounds drop)",
    );

    // Trap-PRESERVING lowering: identical bounds condition.
    assert_preserved(
        prove_trap_condition_equivalence(&orig_trap, &orig_trap),
        "i32.store (bounds preserved)",
    );
}

// ---------------------------------------------------------------------------
// call_indirect — trap-clause-only VC (bounds ∨ null-slot ∨ type)
// ---------------------------------------------------------------------------

#[test]
fn call_indirect_runtime_type_drop_is_caught_and_preservation_accepted() {
    let index = v("index", 32);
    let table_size = v("table_size", 32);
    let slot = v("slot", 32);
    let actual = v("actual_ty", 32);
    let expected = v("expected_ty", 32);

    let orig = trap_call_indirect(&CallIndirect {
        index: &index,
        table_size: &table_size,
        slot_ptr: &slot,
        type_trap: TypeTrap::Runtime {
            actual_type_id: &actual,
            expected_id: &expected,
        },
    });

    // Trap-DROPPING lowering: the runtime §4.4.8 type check was omitted (the
    // #676 heterogeneous-table shape) — model it as StaticallyDischarged.
    let type_dropped = trap_call_indirect(&CallIndirect {
        index: &index,
        table_size: &table_size,
        slot_ptr: &slot,
        type_trap: TypeTrap::StaticallyDischarged,
    });
    assert_dropped(
        prove_trap_condition_equivalence(&orig, &type_dropped),
        "call_indirect (runtime type-check drop)",
    );

    // Trap-DROPPING lowering: all guards removed (never traps).
    assert_dropped(
        prove_trap_condition_equivalence(&orig, &Bool::from_bool(false)),
        "call_indirect (all guards dropped)",
    );

    // Trap-PRESERVING lowering: identical condition.
    assert_preserved(
        prove_trap_condition_equivalence(&orig, &orig),
        "call_indirect (guards preserved)",
    );
}

#[test]
fn call_indirect_statically_discharged_drop_is_caught_and_preservation_accepted() {
    // synth's closed-world homogeneous tables (type_check == None): the type
    // clause is `false`, but bounds + null-slot guards still must survive.
    let index = v("index", 32);
    let table_size = v("table_size", 32);
    let slot = v("slot", 32);

    let orig = trap_call_indirect(&CallIndirect {
        index: &index,
        table_size: &table_size,
        slot_ptr: &slot,
        type_trap: TypeTrap::StaticallyDischarged,
    });

    // Trap-DROPPING lowering: bounds + null-slot guards removed.
    assert_dropped(
        prove_trap_condition_equivalence(&orig, &Bool::from_bool(false)),
        "call_indirect/static (bounds+null drop)",
    );

    // Trap-PRESERVING lowering: identical condition.
    assert_preserved(
        prove_trap_condition_equivalence(&orig, &orig),
        "call_indirect/static (guards preserved)",
    );
}

// ---------------------------------------------------------------------------
// unreachable — trap-clause-only VC (unconditional trap)
// ---------------------------------------------------------------------------

#[test]
fn unreachable_elision_is_caught_and_preservation_accepted() {
    let orig = trap_always();

    // Trap-DROPPING lowering: the unconditional trap was elided (never traps).
    assert_dropped(
        prove_trap_condition_equivalence(&orig, &Bool::from_bool(false)),
        "unreachable (trap elided)",
    );

    // Trap-PRESERVING lowering: still an unconditional trap.
    assert_preserved(
        prove_trap_condition_equivalence(&orig, &trap_always()),
        "unreachable (trap preserved)",
    );
}
