//! Regression gate for #329 / PR #552.
//!
//! #552 made `wasm_stack_check` sound by bailing (`Ok`) on the stack-polymorphic
//! terminators `unreachable`/`return`/`br`/`br_table` — code after them is
//! unreachable and type-checks against an infinite polymorphic stack, so the
//! finite depth counter must not report a false underflow there.
//!
//! That pre-flight was ALSO the historical stand-in (PR #117) for a downstream
//! guarantee: `select_with_stack`'s pop sequence must not *panic* on a
//! dead-code shape like `[Unreachable, I32GeS]`. Removing the terminator guard
//! from the check means these shapes now reach the selector's walk — so the
//! downstream no-panic guarantee is no longer proxied by the check; it must be
//! tested directly. That is this file's job: feed the exact PR#117 shapes (and
//! the new dead-code shapes #552 accepts) to BOTH lowering paths and assert the
//! `wasm_ops_lower_or_error` contract — `Ok` or `Err`, never a panic.
use synth_core::WasmOp;
use synth_synthesis::{InstructionSelector, OptimizerBridge, RuleDatabase};

fn dead_code_shapes() -> Vec<(&'static str, Vec<WasmOp>)> {
    use WasmOp::*;
    vec![
        // PR #117 first crash: i32.ge_s after a depth-0 unreachable.
        ("[Unreachable, I32GeS]", vec![Unreachable, I32GeS]),
        // PR #117 second-round crash: binary/unary op after return.
        ("[Return, I64Eqz]", vec![Return, I64Eqz]),
        (
            "[Return, I64Eqz, I32Const0]",
            vec![Return, I64Eqz, I32Const(0)],
        ),
        ("[Br0, I32GeS]", vec![Br(0), I32GeS]),
        // New dead-code shapes #552 now accepts at the check level.
        ("[Return, Select]", vec![Return, Select]),
        ("[Unreachable, Drop]", vec![Unreachable, Drop]),
        ("[Return, LocalSet0]", vec![Return, LocalSet(0)]),
        ("[Unreachable, I32Add]", vec![Unreachable, I32Add]),
        (
            "[Return, I32Const0, Select]",
            vec![Return, I32Const(0), Select],
        ),
    ]
}

/// Neither lowering path may panic on a dead-code shape the #552 pre-flight now
/// lets through — `Ok` or a typed `Err` are both contract-compliant.
#[test]
fn terminator_dead_code_shapes_do_not_panic_in_lowering_329() {
    let mut panics = vec![];
    for (name, ops) in dead_code_shapes() {
        // Path B — the shipped direct selector (`select_with_stack`), whose
        // first line used to be the guard #552 loosened.
        let ops_b = ops.clone();
        if std::panic::catch_unwind(|| {
            let db = RuleDatabase::with_standard_rules();
            let mut sel = InstructionSelector::new(db.rules().to_vec());
            let _ = sel.select_with_stack(&ops_b, 2);
        })
        .is_err()
        {
            panics.push(format!("select_with_stack PANIC on {name}"));
        }

        // Path A — the optimized bridge (never guarded by the check; included
        // so the contract holds on both paths).
        let ops_a = ops.clone();
        if std::panic::catch_unwind(|| {
            let bridge = OptimizerBridge::new();
            if let Ok((instrs, _cfg, _stats)) = bridge.optimize_full(&ops_a) {
                let _ = bridge.ir_to_arm(&instrs, 2);
            }
        })
        .is_err()
        {
            panics.push(format!("optimized path PANIC on {name}"));
        }
    }
    assert!(
        panics.is_empty(),
        "#552 removed the check-level guard for these shapes; the downstream \
         no-panic contract must hold and does not: {panics:#?}"
    );
}
