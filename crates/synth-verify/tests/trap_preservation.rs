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
//! call_indirect, unreachable, and the float→int truncations have no synth
//! value/contents model, so they use [`prove_trap_condition_equivalence`]
//! (trap clause only) — the ordeal#59 agreement.
//!
//! Phase B (ordeal 0.9.1, ordeal#59/TR-020): the float→int trunc class. The
//! trap predicate is a pure QF_BV classifier over the float operand's BIT
//! PATTERN, so on top of the two gate directions the classifier itself is
//! eval-tested against the synth #709 boundary table (the reference oracle
//! ordeal#59 called for) — both directly via `ordeal::eval` and through the
//! certificate-checked pipeline on the synth wrapper.

use synth_core::WasmOp;
use synth_verify::term::{BV, Bool};
use synth_verify::trap::{
    CallIndirect, DefineOrTrap, DivOp, FpFmt, IntTarget, TrapVerdict, TypeTrap,
    prove_trap_condition_equivalence, prove_trap_equivalence, trap_always, trap_call_indirect,
    trap_div, trap_mem_oob, trap_trunc, trunc_op,
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

// ---------------------------------------------------------------------------
// float→int trunc — trap-clause-only VC (NaN ∨ ±∞ ∨ out-of-range) — Phase B
// (ordeal 0.9.1 `trap_trunc`, ordeal#59/TR-020, synth #709)
// ---------------------------------------------------------------------------

/// The float value (widened to f64, exactly) of a bit pattern of `fmt`.
fn fval(fmt: FpFmt, p: u64) -> f64 {
    match fmt {
        FpFmt::F32 => f32::from_bits(p as u32) as f64,
        FpFmt::F64 => f64::from_bits(p),
    }
}

/// Reference: the exact WASM `iN.trunc_fM_s/u` trap predicate, computed on the
/// REAL host float. All range math is in f64, which is exact for every case
/// here (f32→f64 is exact; `trunc` of a finite float is an integer-valued f64;
/// the ±2^31 / ±2^63 / 2^32 / 2^64 / 0 bounds are exact f64 values).
fn ref_trap_trunc(x: f64, target: IntTarget, signed: bool) -> bool {
    if !x.is_finite() {
        return true;
    }
    let t = x.trunc();
    let n = target.width() as i32;
    if signed {
        !(t >= -(2f64.powi(n - 1)) && t < 2f64.powi(n - 1))
    } else {
        !(t >= 0.0 && t < 2f64.powi(n))
    }
}

/// The six trunc variants synth's decoder produces, with their WASM names.
const TRUNC_VARIANTS: [(FpFmt, IntTarget, bool, &str); 6] = [
    (FpFmt::F32, IntTarget::I32, true, "i32.trunc_f32_s"),
    (FpFmt::F32, IntTarget::I32, false, "i32.trunc_f32_u"),
    (FpFmt::F64, IntTarget::I32, true, "i32.trunc_f64_s"),
    (FpFmt::F64, IntTarget::I32, false, "i32.trunc_f64_u"),
    (FpFmt::F64, IntTarget::I64, true, "i64.trunc_f64_s"),
    (FpFmt::F64, IntTarget::I64, false, "i64.trunc_f64_u"),
];

#[test]
fn trunc_op_maps_all_six_wasm_variants() {
    assert_eq!(
        trunc_op(&WasmOp::I32TruncF32S),
        Some((FpFmt::F32, IntTarget::I32, true))
    );
    assert_eq!(
        trunc_op(&WasmOp::I32TruncF32U),
        Some((FpFmt::F32, IntTarget::I32, false))
    );
    assert_eq!(
        trunc_op(&WasmOp::I32TruncF64S),
        Some((FpFmt::F64, IntTarget::I32, true))
    );
    assert_eq!(
        trunc_op(&WasmOp::I32TruncF64U),
        Some((FpFmt::F64, IntTarget::I32, false))
    );
    assert_eq!(
        trunc_op(&WasmOp::I64TruncF64S),
        Some((FpFmt::F64, IntTarget::I64, true))
    );
    assert_eq!(
        trunc_op(&WasmOp::I64TruncF64U),
        Some((FpFmt::F64, IntTarget::I64, false))
    );
    assert_eq!(trunc_op(&WasmOp::I32Add), None);
    assert_eq!(trunc_op(&WasmOp::I32DivS), None);
}

#[test]
fn trunc_all_six_ops_catch_the_drop_and_accept_preservation() {
    for (fmt, target, signed, name) in TRUNC_VARIANTS {
        let f = v("f", fmt.total_bits());
        let orig = trap_trunc(&f, fmt, target, signed);

        // Trap-DROPPING lowering: the guard was removed entirely — the #709
        // shape (ARM VCVT saturates where WASM must trap; keeping the
        // saturated value and dropping the guard looks value-equal).
        let verdict = prove_trap_condition_equivalence(&orig, &Bool::from_bool(false));
        assert_dropped(verdict.clone(), name);
        // The counterexample must be a genuinely trapping input per the
        // real-float reference.
        if let TrapVerdict::Dropped(model) = verdict {
            let p = model
                .iter()
                .find(|(n, _)| n == "f")
                .map(|(_, x)| *x)
                .unwrap_or_else(|| panic!("{name}: counterexample model must assign f"));
            let x = fval(fmt, p as u64);
            assert!(
                ref_trap_trunc(x, target, signed),
                "{name}: counterexample {p:#x} (value {x:e}) must be a genuinely trapping input"
            );
        }

        // Trap-PRESERVING lowering: identical classifier.
        assert_preserved(
            prove_trap_condition_equivalence(&orig, &trap_trunc(&f, fmt, target, signed)),
            name,
        );
    }
}

#[test]
fn trunc_signedness_confused_guard_is_caught() {
    // A lowering that guards `i32.trunc_f32_s` with the UNSIGNED range check
    // (a partial #709-class drop: NaN/∞ still guarded, range thresholds
    // wrong) must be caught — e.g. -5.0 spuriously traps unsigned, and
    // 3e9 traps signed but not unsigned.
    let f = v("f", 32);
    let orig = trap_trunc(&f, FpFmt::F32, IntTarget::I32, true);
    let confused = trap_trunc(&f, FpFmt::F32, IntTarget::I32, false);
    let verdict = prove_trap_condition_equivalence(&orig, &confused);
    assert_dropped(
        verdict.clone(),
        "i32.trunc_f32_s (signedness-confused guard)",
    );
    // The counterexample must be an input where the two predicates genuinely
    // disagree per the real-float reference.
    if let TrapVerdict::Dropped(model) = verdict {
        let p = model
            .iter()
            .find(|(n, _)| n == "f")
            .map(|(_, x)| *x)
            .expect("counterexample model must assign f");
        let x = fval(FpFmt::F32, p as u64);
        assert_ne!(
            ref_trap_trunc(x, IntTarget::I32, true),
            ref_trap_trunc(x, IntTarget::I32, false),
            "counterexample {p:#x} (value {x:e}) must separate signed from unsigned trapping"
        );
    }
}

/// The synth #709 boundary table: `(fmt, target, signed, bits, traps, label)`.
/// This is the reference oracle for the classifier-encoding check ordeal#59
/// called for.
fn boundary_table_709() -> Vec<(FpFmt, IntTarget, bool, u64, bool, &'static str)> {
    let b32 = |x: f32| x.to_bits() as u64;
    let b64 = |x: f64| x.to_bits();
    use FpFmt::{F32, F64};
    use IntTarget::{I32, I64};
    vec![
        // --- i32.trunc_f32_s ---
        (F32, I32, true, b32(f32::NAN), true, "f32→i32_s: NaN traps"),
        (
            F32,
            I32,
            true,
            b32(f32::INFINITY),
            true,
            "f32→i32_s: +∞ traps",
        ),
        (
            F32,
            I32,
            true,
            b32(f32::NEG_INFINITY),
            true,
            "f32→i32_s: -∞ traps",
        ),
        (F32, I32, true, b32(3e9), true, "f32→i32_s: 3e9 traps"),
        (F32, I32, true, b32(-3e9), true, "f32→i32_s: -3e9 traps"),
        (
            F32,
            I32,
            true,
            0x4F00_0000, // 2^31
            true,
            "f32→i32_s: 2^31 (0x4F000000) TRAPS",
        ),
        (
            F32,
            I32,
            true,
            0xCF00_0000, // -2^31
            false,
            "f32→i32_s: -2^31 (0xCF000000) is IN-RANGE",
        ),
        (
            F32,
            I32,
            true,
            b32(2_147_483_520.0), // 2^31 - 128: largest f32 below 2^31
            false,
            "f32→i32_s: largest f32 below 2^31 converts",
        ),
        (F32, I32, true, b32(2.5), false, "f32→i32_s: 2.5 → 2"),
        // --- i32.trunc_f32_u ---
        (F32, I32, false, b32(-1.0), true, "f32→i32_u: -1.0 traps"),
        (F32, I32, false, b32(0.5), false, "f32→i32_u: 0.5 → 0"),
        (F32, I32, false, b32(-0.0), false, "f32→i32_u: -0.0 → 0"),
        (
            F32,
            I32,
            false,
            b32(4_294_967_296.0), // 2^32 (0x4F800000)
            true,
            "f32→i32_u: 2^32 traps",
        ),
        (
            F32,
            I32,
            false,
            b32(4_294_967_040.0), // 2^32 - 256: largest f32 below 2^32
            false,
            "f32→i32_u: largest f32 below 2^32 converts",
        ),
        (F32, I32, false, b32(f32::NAN), true, "f32→i32_u: NaN traps"),
        // --- i32.trunc_f64_s ---
        (
            F64,
            I32,
            true,
            b64(2f64.powi(31)),
            true,
            "f64→i32_s: 2^31 traps",
        ),
        (
            F64,
            I32,
            true,
            b64(2_147_483_647.5),
            false,
            "f64→i32_s: 2^31-0.5 → 2^31-1",
        ),
        (
            F64,
            I32,
            true,
            b64(-(2f64.powi(31))),
            false,
            "f64→i32_s: -2^31 is in range",
        ),
        (
            F64,
            I32,
            true,
            b64(-2_147_483_649.0),
            true,
            "f64→i32_s: -(2^31+1) traps",
        ),
        (F64, I32, true, b64(f64::NAN), true, "f64→i32_s: NaN traps"),
        // --- i32.trunc_f64_u ---
        (F64, I32, false, b64(-1.0), true, "f64→i32_u: -1.0 traps"),
        (
            F64,
            I32,
            false,
            b64(4_294_967_295.5),
            false,
            "f64→i32_u: 2^32-0.5 → 2^32-1",
        ),
        (
            F64,
            I32,
            false,
            b64(2f64.powi(32)),
            true,
            "f64→i32_u: 2^32 traps",
        ),
        // --- i64.trunc_f64_s ---
        (
            F64,
            I64,
            true,
            b64(2f64.powi(63)),
            true,
            "f64→i64_s: 2^63 traps",
        ),
        (
            F64,
            I64,
            true,
            0x43DF_FFFF_FFFF_FFFF, // 2^63 - 1024: largest f64 below 2^63
            false,
            "f64→i64_s: largest f64 below 2^63 converts",
        ),
        (
            F64,
            I64,
            true,
            b64(-(2f64.powi(63))),
            false,
            "f64→i64_s: -2^63 is in range",
        ),
        (
            F64,
            I64,
            true,
            0xC3E0_0000_0000_0001, // -(2^63 + 2048): next f64 below -2^63
            true,
            "f64→i64_s: below -2^63 traps",
        ),
        // --- i64.trunc_f64_u ---
        (F64, I64, false, b64(-1.0), true, "f64→i64_u: -1.0 traps"),
        (F64, I64, false, b64(0.5), false, "f64→i64_u: 0.5 → 0"),
        (
            F64,
            I64,
            false,
            b64(2f64.powi(64)),
            true,
            "f64→i64_u: 2^64 traps",
        ),
        (
            F64,
            I64,
            false,
            0x43EF_FFFF_FFFF_FFFF, // 2^64 - 2048: largest f64 below 2^64
            false,
            "f64→i64_u: largest f64 below 2^64 converts",
        ),
    ]
}

/// Encoding-correctness check (ordeal#59): eval ordeal's trunc classifier
/// directly (`ordeal::eval::eval_bool`) at the exact #709 boundary bit
/// patterns — synth's boundary table is the reference oracle. Every case is
/// also cross-checked against the real-float reference predicate, so the
/// table itself cannot drift.
#[test]
fn trunc_classifier_eval_matches_709_boundary_table() {
    use ordeal::{BvTerm, Sort, eval, trap as ot};
    for (fmt, target, signed, bits, traps, label) in boundary_table_709() {
        // The table row must agree with the real-float reference.
        assert_eq!(
            ref_trap_trunc(fval(fmt, bits), target, signed),
            traps,
            "boundary-table self-check: {label}"
        );
        let f = BvTerm::Var {
            name: "f".into(),
            sort: Sort::new(fmt.total_bits()),
        };
        let classifier = ot::trap_trunc(&f, fmt, target, signed);
        let mut env = eval::Env::new();
        env.insert("f".into(), bits as u128);
        assert_eq!(
            eval::eval_bool(&classifier, &env).expect("classifier must evaluate"),
            traps,
            "classifier eval: {label} (pattern {bits:#x})"
        );
    }
}

/// The same #709 table through the certificate-checked pipeline on the synth
/// wrapper: at a GROUND input, `trap_trunc(const) ⇔ expected` is valid iff the
/// classifier decides the pattern exactly as the table says — so `Preserved`
/// (an LRAT-re-checked Unsat) is a per-pattern verdict check.
#[test]
fn trunc_gate_decides_709_boundary_table_through_certified_pipeline() {
    for (fmt, target, signed, bits, traps, label) in boundary_table_709() {
        let ground = BV::from_u64(bits, fmt.total_bits());
        let cond = trap_trunc(&ground, fmt, target, signed);
        assert_preserved(
            prove_trap_condition_equivalence(&cond, &Bool::from_bool(traps)),
            label,
        );
    }
    // Non-vacuity control: a deliberately WRONG expectation must be rejected
    // (Dropped), so `Preserved` above is a real per-pattern decision.
    let nan = BV::from_u64(f32::NAN.to_bits() as u64, 32);
    let cond = trap_trunc(&nan, FpFmt::F32, IntTarget::I32, true);
    assert_dropped(
        prove_trap_condition_equivalence(&cond, &Bool::from_bool(false)),
        "f32→i32_s: claiming NaN does not trap",
    );
}
