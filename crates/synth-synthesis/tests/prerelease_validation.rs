//! Pre-release validation tests for synth v0.1.0
//!
//! Comprehensive edge-case and negative tests that exercise the full
//! WAT->WASM->instruction-selection pipeline.

use synth_synthesis::{InstructionSelector, decode_wasm_module};

// =========================================================================
// Negative tests: invalid input gives clean errors (not panics)
// =========================================================================

#[test]
fn test_empty_wasm_gives_clean_error() {
    let result = decode_wasm_module(&[]);
    assert!(result.is_err(), "Empty WASM bytes should produce an error");
}

#[test]
fn test_truncated_wasm_gives_clean_error() {
    // Just the magic number, no version or sections
    let result = decode_wasm_module(&[0x00, 0x61, 0x73, 0x6D]);
    assert!(result.is_err(), "Truncated WASM should produce an error");
}

#[test]
fn test_wrong_magic_gives_clean_error() {
    // Wrong magic, valid-looking version
    let result = decode_wasm_module(&[0xDE, 0xAD, 0xBE, 0xEF, 0x01, 0x00, 0x00, 0x00]);
    assert!(
        result.is_err(),
        "Wrong magic number should produce an error"
    );
}

#[test]
fn test_garbage_bytes_gives_clean_error() {
    let garbage: Vec<u8> = (0..100).map(|i| (i * 37 + 13) as u8).collect();
    let result = decode_wasm_module(&garbage);
    assert!(
        result.is_err(),
        "Random garbage bytes should produce an error"
    );
}

#[test]
fn test_wat_syntax_error_gives_clean_error() {
    // Invalid WAT — this should fail at the WAT->WASM conversion step
    let invalid_wat = b"(module (func (export \"bad\") (result i32) i32.add i32.add))";
    // The `wat` crate should reject or the decoder should reject
    let result = wat::parse_bytes(invalid_wat);
    // WAT with type errors may or may not parse depending on validation mode,
    // but the result should not panic
    match result {
        Ok(wasm_bytes) => {
            // Even if WAT parses, WASM decoding should work or produce an error
            let _ = decode_wasm_module(&wasm_bytes);
        }
        Err(_) => {
            // WAT parse error — that's the expected clean error
        }
    }
}

#[test]
fn test_wat_missing_closing_paren() {
    let bad_wat = b"(module (func (export \"broken\")";
    let result = wat::parse_bytes(bad_wat);
    assert!(
        result.is_err(),
        "WAT with missing closing paren should produce a parse error"
    );
}

// =========================================================================
// Full pipeline: WAT -> WASM -> decode -> instruction select
// =========================================================================

#[test]
fn test_full_pipeline_simple_add() {
    let wat = br#"(module (func (export "add") (param i32 i32) (result i32)
        local.get 0
        local.get 1
        i32.add))"#;

    let wasm = wat::parse_bytes(wat).expect("WAT should parse");
    let module = decode_wasm_module(&wasm).expect("WASM should decode");

    assert!(
        !module.functions.is_empty(),
        "Should have at least one function"
    );

    let mut selector = InstructionSelector::new(vec![]);
    // The WAT has 2 params; FunctionOps doesn't store num_params, use 2 directly
    let instrs = selector
        .select_with_stack(&module.functions[0].ops, 2)
        .expect("Instruction selection should succeed");

    assert!(!instrs.is_empty(), "Should produce ARM instructions");
}

#[test]
fn test_full_pipeline_large_function() {
    // A function with many operations: should compile without panicking
    let wat = br#"(module
        (func (export "complex") (param $n i32) (result i32)
            (local $i i32) (local $acc i32) (local $tmp i32)
            local.get $n
            local.set $acc
            local.get $n
            local.set $i
            (block $exit
                (loop $loop
                    local.get $i
                    i32.const 0
                    i32.le_s
                    br_if $exit
                    ;; acc = acc * 3 + i
                    local.get $acc
                    i32.const 3
                    i32.mul
                    local.get $i
                    i32.add
                    local.set $acc
                    ;; bit mix
                    local.get $acc
                    i32.const 5
                    i32.shr_u
                    local.get $acc
                    i32.xor
                    local.set $acc
                    ;; i -= 1
                    local.get $i
                    i32.const 1
                    i32.sub
                    local.set $i
                    br $loop
                )
            )
            local.get $acc
        )
    )"#;

    let wasm = wat::parse_bytes(wat).expect("WAT should parse");
    let module = decode_wasm_module(&wasm).expect("WASM should decode");

    let func = &module.functions[0];
    assert!(
        func.ops.len() >= 20,
        "Function should have 20+ ops (has {})",
        func.ops.len()
    );

    let mut selector = InstructionSelector::new(vec![]);
    // WAT function has 1 param ($n)
    let instrs = selector
        .select_with_stack(&func.ops, 1)
        .expect("Large function compilation should not panic");

    // Reasonable instruction count
    assert!(
        instrs.len() < func.ops.len() * 30,
        "ARM instruction count should not be exponential"
    );
}

// =========================================================================
// Constant materialization through full pipeline
// =========================================================================

#[test]
fn test_pipeline_const_edge_cases() {
    let wat = br#"(module
        (func (export "max") (result i32) i32.const 2147483647)
        (func (export "min") (result i32) i32.const -2147483648)
        (func (export "neg1") (result i32) i32.const -1)
        (func (export "zero") (result i32) i32.const 0)
    )"#;

    let wasm = wat::parse_bytes(wat).expect("WAT should parse");
    let module = decode_wasm_module(&wasm).expect("WASM should decode");

    assert_eq!(module.functions.len(), 4, "Should have 4 functions");

    for (i, func) in module.functions.iter().enumerate() {
        let mut selector = InstructionSelector::new(vec![]);
        // All functions in this WAT have 0 params
        let instrs = selector
            .select_with_stack(&func.ops, 0)
            .unwrap_or_else(|_| panic!("Function {i} should compile"));
        assert!(
            !instrs.is_empty(),
            "Function {i} should produce ARM instructions"
        );
    }
}
