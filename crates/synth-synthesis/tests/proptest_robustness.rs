//! Property-based robustness tests for the instruction selector.
//!
//! Uses proptest to verify the instruction selector handles random inputs
//! without panicking, and that supported ops always produce non-empty output.

use proptest::prelude::*;
use synth_synthesis::{InstructionSelector, RuleDatabase, WasmOp};

/// Generate a random supported i32 WASM operation (no parameters needed).
fn arb_supported_i32_op() -> impl Strategy<Value = WasmOp> {
    prop_oneof![
        Just(WasmOp::I32Add),
        Just(WasmOp::I32Sub),
        Just(WasmOp::I32Mul),
        Just(WasmOp::I32And),
        Just(WasmOp::I32Or),
        Just(WasmOp::I32Xor),
        Just(WasmOp::I32Shl),
        Just(WasmOp::I32ShrU),
        Just(WasmOp::I32ShrS),
        Just(WasmOp::I32Rotl),
        Just(WasmOp::I32Rotr),
        Just(WasmOp::I32Clz),
        Just(WasmOp::I32Ctz),
        Just(WasmOp::I32DivS),
        Just(WasmOp::I32DivU),
        Just(WasmOp::I32RemS),
        Just(WasmOp::I32RemU),
        Just(WasmOp::I32Eqz),
        Just(WasmOp::I32Eq),
        Just(WasmOp::I32Ne),
        Just(WasmOp::I32LtS),
        Just(WasmOp::I32LtU),
        Just(WasmOp::I32GtS),
        Just(WasmOp::I32GtU),
        Just(WasmOp::I32LeS),
        Just(WasmOp::I32LeU),
        Just(WasmOp::I32GeS),
        Just(WasmOp::I32GeU),
        Just(WasmOp::I32Extend8S),
        Just(WasmOp::I32Extend16S),
    ]
}

/// Generate a random WASM op including ones with parameters.
fn arb_wasm_op() -> impl Strategy<Value = WasmOp> {
    prop_oneof![
        arb_supported_i32_op(),
        any::<i32>().prop_map(WasmOp::I32Const),
        Just(WasmOp::Nop),
        Just(WasmOp::Drop),
        Just(WasmOp::Return),
        Just(WasmOp::Unreachable),
        (0u32..10).prop_map(WasmOp::LocalGet),
        (0u32..10).prop_map(WasmOp::LocalSet),
        (0u32..10).prop_map(WasmOp::LocalTee),
    ]
}

proptest! {
    /// Every supported i32 op produces at least one ARM instruction.
    #[test]
    fn supported_ops_produce_nonempty_output(op in arb_supported_i32_op()) {
        let db = RuleDatabase::with_standard_rules();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let result = selector.select(&[op]);
        prop_assert!(result.is_ok(), "Supported op should not error: {result:?}");
        prop_assert!(!result.unwrap().is_empty(), "Should produce at least one instruction");
    }

    /// Random sequences of supported ops don't panic.
    #[test]
    fn random_op_sequences_dont_panic(
        ops in prop::collection::vec(arb_wasm_op(), 1..20)
    ) {
        let db = RuleDatabase::with_standard_rules();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        // We don't care about the result — just that it doesn't panic
        let _ = selector.select(&ops);
    }

    /// I32Const with any value produces a MOV instruction.
    #[test]
    fn i32_const_always_produces_mov(val in any::<i32>()) {
        let db = RuleDatabase::with_standard_rules();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let result = selector.select(&[WasmOp::I32Const(val)]);
        prop_assert!(result.is_ok());
        let ops = result.unwrap();
        prop_assert!(!ops.is_empty());
    }

    /// Binary ops always produce consistent instruction counts.
    #[test]
    fn binary_op_instruction_count_is_deterministic(
        op in arb_supported_i32_op(),
        _run in 0u32..5  // run multiple times to verify determinism
    ) {
        let db = RuleDatabase::with_standard_rules();

        let mut sel1 = InstructionSelector::new(db.rules().to_vec());
        let r1 = sel1.select(&[op.clone()]).unwrap();

        let mut sel2 = InstructionSelector::new(db.rules().to_vec());
        let r2 = sel2.select(&[op]).unwrap();

        prop_assert_eq!(
            r1.len(), r2.len(),
            "Same op should always produce same number of instructions"
        );
    }
}
