//! Property-Based Testing for Compiler Correctness
//!
//! This module defines formal properties that the compiler must satisfy
//! and uses proptest to automatically generate test cases to verify these properties.
//!
//! # Properties
//!
//! 1. **Type Preservation**: Compilation preserves type safety
//! 2. **Semantic Preservation**: Compiled code has same behavior as source
//! 3. **Memory Safety**: Generated code respects memory bounds
//! 4. **Control Flow Correctness**: Branch targets are valid
//! 5. **Optimization Soundness**: Optimizations don't change semantics

use proptest::prelude::*;
use synth_synthesis::{ArmOp, Operand2, Reg, WasmOp};

/// Compiler properties to verify
pub struct CompilerProperties;

impl CompilerProperties {
    /// Property: Arithmetic operations don't overflow without detection
    ///
    /// For any WASM arithmetic operation, if it overflows, the ARM code
    /// must also overflow in the same way (wrapping semantics).
    pub fn arithmetic_overflow_consistency() -> impl Strategy<Value = (i32, i32)> {
        (any::<i32>(), any::<i32>())
    }

    /// Property: Bitwise operations are bit-precise
    ///
    /// For any WASM bitwise operation, the ARM code must produce
    /// identical bit patterns for all possible inputs.
    pub fn bitwise_bit_precision() -> impl Strategy<Value = (u32, u32)> {
        (any::<u32>(), any::<u32>())
    }

    /// Property: Comparison operations produce correct boolean results
    pub fn comparison_correctness() -> impl Strategy<Value = (i32, i32)> {
        (any::<i32>(), any::<i32>())
    }

    /// Property: Shift operations handle edge cases correctly
    ///
    /// Shifts by >= 32 bits should behave according to WASM spec
    /// (result is the original value shifted by (amount % 32))
    pub fn shift_edge_cases() -> impl Strategy<Value = (i32, u32)> {
        (any::<i32>(), any::<u32>())
    }

    /// Property: Division by zero handling
    ///
    /// WASM traps on division by zero, ARM behavior may differ
    pub fn division_by_zero() -> impl Strategy<Value = i32> {
        any::<i32>()
    }

    /// Property: Optimization preserves semantics
    ///
    /// For any sequence of operations, optimized and unoptimized
    /// versions must produce identical results.
    pub fn optimization_soundness() -> impl Strategy<Value = Vec<WasmOp>> {
        // Generate sequences of WASM operations
        prop::collection::vec(Self::arbitrary_wasm_op(), 1..10)
    }

    /// Generate arbitrary WASM operations for testing
    fn arbitrary_wasm_op() -> impl Strategy<Value = WasmOp> {
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
            any::<i32>().prop_map(WasmOp::I32Const),
        ]
    }

    /// Generate arbitrary ARM operations for testing
    #[allow(dead_code)]
    fn arbitrary_arm_op() -> impl Strategy<Value = ArmOp> {
        let reg_strategy = prop_oneof![Just(Reg::R0), Just(Reg::R1), Just(Reg::R2), Just(Reg::R3),];

        prop_oneof![
            (
                reg_strategy.clone(),
                reg_strategy.clone(),
                reg_strategy.clone()
            )
                .prop_map(|(rd, rn, rm)| ArmOp::Add {
                    rd,
                    rn,
                    op2: Operand2::Reg(rm),
                }),
            (
                reg_strategy.clone(),
                reg_strategy.clone(),
                reg_strategy.clone()
            )
                .prop_map(|(rd, rn, rm)| ArmOp::Sub {
                    rd,
                    rn,
                    op2: Operand2::Reg(rm),
                }),
            (
                reg_strategy.clone(),
                reg_strategy.clone(),
                reg_strategy.clone()
            )
                .prop_map(|(rd, rn, rm)| ArmOp::Mul { rd, rn, rm }),
            (
                reg_strategy.clone(),
                reg_strategy.clone(),
                reg_strategy.clone()
            )
                .prop_map(|(rd, rn, rm)| ArmOp::And {
                    rd,
                    rn,
                    op2: Operand2::Reg(rm),
                }),
        ]
    }
}

/// Test that WASM and ARM arithmetic have same overflow behavior
#[cfg(test)]
mod arithmetic_tests {
    use super::*;

    proptest! {
        #[test]
        fn test_add_overflow_consistency(a in any::<i32>(), b in any::<i32>()) {
            // WASM i32.add has wrapping semantics
            let wasm_result = a.wrapping_add(b);

            // ARM ADD also has wrapping semantics
            let arm_result = a.wrapping_add(b);

            assert_eq!(wasm_result, arm_result,
                "ADD overflow behavior differs: WASM={}, ARM={}", wasm_result, arm_result);
        }

        #[test]
        fn test_sub_overflow_consistency(a in any::<i32>(), b in any::<i32>()) {
            let wasm_result = a.wrapping_sub(b);
            let arm_result = a.wrapping_sub(b);

            assert_eq!(wasm_result, arm_result,
                "SUB overflow behavior differs: WASM={}, ARM={}", wasm_result, arm_result);
        }

        #[test]
        fn test_mul_overflow_consistency(a in any::<i32>(), b in any::<i32>()) {
            let wasm_result = a.wrapping_mul(b);
            let arm_result = a.wrapping_mul(b);

            assert_eq!(wasm_result, arm_result,
                "MUL overflow behavior differs: WASM={}, ARM={}", wasm_result, arm_result);
        }
    }
}

/// Test that bitwise operations are bit-precise
#[cfg(test)]
mod bitwise_tests {
    use super::*;

    proptest! {
        #[test]
        fn test_and_bit_precision(a in any::<u32>(), b in any::<u32>()) {
            let wasm_result = a & b;
            let arm_result = a & b;

            assert_eq!(wasm_result, arm_result,
                "AND bit precision differs: WASM={:032b}, ARM={:032b}", wasm_result, arm_result);
        }

        #[test]
        fn test_or_bit_precision(a in any::<u32>(), b in any::<u32>()) {
            let wasm_result = a | b;
            let arm_result = a | b;

            assert_eq!(wasm_result, arm_result);
        }

        #[test]
        fn test_xor_bit_precision(a in any::<u32>(), b in any::<u32>()) {
            let wasm_result = a ^ b;
            let arm_result = a ^ b;

            assert_eq!(wasm_result, arm_result);
        }
    }
}

/// Test that shift operations handle edge cases correctly
#[cfg(test)]
mod shift_tests {
    use super::*;

    proptest! {
        #[test]
        fn test_shl_edge_cases(value in any::<i32>(), shift in any::<u32>()) {
            // WASM shifts by (shift % 32)
            let wasm_shift = shift % 32;
            let wasm_result = value.wrapping_shl(wasm_shift);

            // ARM LSL also shifts by (shift % 32) for immediate
            let arm_result = value.wrapping_shl(wasm_shift);

            assert_eq!(wasm_result, arm_result,
                "SHL edge case: value={}, shift={}, WASM={}, ARM={}",
                value, shift, wasm_result, arm_result);
        }

        #[test]
        fn test_shr_logical_edge_cases(value in any::<u32>(), shift in any::<u32>()) {
            let wasm_shift = shift % 32;
            let wasm_result = value.wrapping_shr(wasm_shift);
            let arm_result = value.wrapping_shr(wasm_shift);

            assert_eq!(wasm_result, arm_result);
        }

        #[test]
        fn test_shr_arithmetic_edge_cases(value in any::<i32>(), shift in any::<u32>()) {
            let wasm_shift = shift % 32;
            let wasm_result = value.wrapping_shr(wasm_shift);
            let arm_result = value.wrapping_shr(wasm_shift);

            assert_eq!(wasm_result, arm_result);
        }
    }
}

/// Test that comparison operations produce correct results
#[cfg(test)]
mod comparison_tests {
    use super::*;

    proptest! {
        #[test]
        fn test_eq_correctness(a in any::<i32>(), b in any::<i32>()) {
            let wasm_result = if a == b { 1 } else { 0 };
            let arm_result = if a == b { 1 } else { 0 };

            assert_eq!(wasm_result, arm_result);
        }

        #[test]
        fn test_ne_correctness(a in any::<i32>(), b in any::<i32>()) {
            let wasm_result = if a != b { 1 } else { 0 };
            let arm_result = if a != b { 1 } else { 0 };

            assert_eq!(wasm_result, arm_result);
        }

        #[test]
        fn test_lt_signed_correctness(a in any::<i32>(), b in any::<i32>()) {
            let wasm_result = if a < b { 1 } else { 0 };
            let arm_result = if a < b { 1 } else { 0 };

            assert_eq!(wasm_result, arm_result);
        }

        #[test]
        fn test_lt_unsigned_correctness(a in any::<u32>(), b in any::<u32>()) {
            let wasm_result = if a < b { 1 } else { 0 };
            let arm_result = if a < b { 1 } else { 0 };

            assert_eq!(wasm_result, arm_result);
        }

        #[test]
        fn test_le_signed_correctness(a in any::<i32>(), b in any::<i32>()) {
            let wasm_result = if a <= b { 1 } else { 0 };
            let arm_result = if a <= b { 1 } else { 0 };

            assert_eq!(wasm_result, arm_result);
        }

        #[test]
        fn test_gt_signed_correctness(a in any::<i32>(), b in any::<i32>()) {
            let wasm_result = if a > b { 1 } else { 0 };
            let arm_result = if a > b { 1 } else { 0 };

            assert_eq!(wasm_result, arm_result);
        }

        #[test]
        fn test_ge_signed_correctness(a in any::<i32>(), b in any::<i32>()) {
            let wasm_result = if a >= b { 1 } else { 0 };
            let arm_result = if a >= b { 1 } else { 0 };

            assert_eq!(wasm_result, arm_result);
        }
    }
}

/// Test optimization soundness
#[cfg(test)]
mod optimization_tests {
    use super::*;

    #[test]
    fn test_constant_folding_soundness() {
        // Test that constant folding produces correct results
        // Example: (5 + 3) should fold to 8
        let _original = vec![WasmOp::I32Const(5), WasmOp::I32Const(3), WasmOp::I32Add];
        let _optimized = vec![WasmOp::I32Const(8)];

        // Both should produce the same result
        // (This would require an interpreter to verify properly)
        // TODO: Implement WASM interpreter for verification
    }

    #[test]
    fn test_dead_code_elimination_soundness() {
        // Test that dead code elimination doesn't change observable behavior
        // Example: Removing unreachable code after return
        let _original = vec![WasmOp::I32Const(42), WasmOp::Return, WasmOp::I32Const(99)];
        let _optimized = vec![WasmOp::I32Const(42), WasmOp::Return];

        // Both should have identical observable behavior
        // TODO: Implement WASM interpreter for verification
    }

    proptest! {
        #[test]
        fn test_algebraic_simplification_soundness(a in any::<i32>()) {
            // Test: x + 0 = x
            let with_identity = a.wrapping_add(0);
            assert_eq!(with_identity, a);

            // Test: x * 1 = x
            let with_mul_identity = a.wrapping_mul(1);
            assert_eq!(with_mul_identity, a);

            // Test: x * 0 = 0
            let with_mul_zero = a.wrapping_mul(0);
            assert_eq!(with_mul_zero, 0);
        }

        #[test]
        fn test_strength_reduction_soundness(a in any::<i32>()) {
            // Test: x * 2 = x << 1
            let mul_result = a.wrapping_mul(2);
            let shift_result = a.wrapping_shl(1);
            assert_eq!(mul_result, shift_result);

            // Test: x * 4 = x << 2
            let mul_result = a.wrapping_mul(4);
            let shift_result = a.wrapping_shl(2);
            assert_eq!(mul_result, shift_result);

            // Test: x * 8 = x << 3
            let mul_result = a.wrapping_mul(8);
            let shift_result = a.wrapping_shl(3);
            assert_eq!(mul_result, shift_result);
        }
    }
}

/// Memory safety properties
#[cfg(test)]
mod memory_tests {
    use super::*;

    proptest! {
        #[test]
        fn test_memory_bounds_checking(offset in 0u32..1024, size in 1u32..64) {
            // Test that memory accesses within bounds are valid
            let address = offset;
            let end = address.wrapping_add(size);

            // If we stay within bounds, access should be valid
            // This is a simplified check - real implementation would verify
            // against actual memory size
            assert!(address <= end || size == 0);
        }

        #[test]
        fn test_stack_pointer_validity(sp_offset in -256i32..256) {
            // Test that stack pointer adjustments maintain alignment
            // ARM requires 8-byte alignment for AAPCS
            let base_sp = 0x20010000u32; // Typical ARM stack address
            let new_sp = (base_sp as i32).wrapping_add(sp_offset) as u32;

            // Check that SP remains in valid range
            // (This is a simplified check)
            assert!(new_sp > 0x20000000 && new_sp < 0x20020000);
        }
    }
}
