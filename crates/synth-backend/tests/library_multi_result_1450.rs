//! #1450 — the published `Backend::compile_module` API refuses an exported
//! multi-result function, as the CLI does. On main 6641efec it returned `Ok`
//! with code that hands back only the function's LAST result. The CLI legs,
//! and what is deliberately not refused, are pinned in
//! `crates/synth-cli/tests/multi_result_entry_refusal_1450.rs`.

use synth_backend::ArmBackend;
use synth_core::backend::{Backend, CompileConfig};
use synth_core::wasm_decoder::decode_wasm_module;

/// `(module (func (export "two") (param i32) (result i32 i32)
///   local.get 0 i32.const 3 i32.mul  local.get 0 i32.const 5 i32.mul))`
const EXPORTED_PAIR: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x07, 0x01, 0x60, 0x01, 0x7f, 0x02, 0x7f,
    0x7f, 0x03, 0x02, 0x01, 0x00, 0x07, 0x07, 0x01, 0x03, 0x74, 0x77, 0x6f, 0x00, 0x00, 0x0a, 0x0e,
    0x01, 0x0c, 0x00, 0x20, 0x00, 0x41, 0x03, 0x6c, 0x20, 0x00, 0x41, 0x05, 0x6c, 0x0b,
];

/// PAIRED CONTROL — the same two computations, one result each:
/// `(module (func (export "first") (param i32) (result i32) local.get 0 i32.const 3 i32.mul)
///          (func (export "second") (param i32) (result i32) local.get 0 i32.const 5 i32.mul))`
const SINGLE_RESULTS: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x06, 0x01, 0x60, 0x01, 0x7f, 0x01, 0x7f,
    0x03, 0x03, 0x02, 0x00, 0x00, 0x07, 0x12, 0x02, 0x05, 0x66, 0x69, 0x72, 0x73, 0x74, 0x00, 0x00,
    0x06, 0x73, 0x65, 0x63, 0x6f, 0x6e, 0x64, 0x00, 0x01, 0x0a, 0x11, 0x02, 0x07, 0x00, 0x20, 0x00,
    0x41, 0x03, 0x6c, 0x0b, 0x07, 0x00, 0x20, 0x00, 0x41, 0x05, 0x6c, 0x0b,
];

fn cfg(relocatable: bool) -> CompileConfig {
    CompileConfig {
        relocatable,
        ..CompileConfig::default()
    }
}

#[test]
fn compile_module_refuses_an_exported_multi_result_function_1450() {
    let module = decode_wasm_module(EXPORTED_PAIR).expect("decodes");
    assert_eq!(module.func_result_counts, [2]);
    for relocatable in [false, true] {
        let err = ArmBackend::new()
            .compile_module(&module, &cfg(relocatable))
            .map(|_| ())
            .expect_err("an exported multi-result function has no return convention")
            .to_string();
        assert!(err.contains("MULTI-RESULT function"), "{err}");
        assert!(err.contains("#1450"), "cites the analysis: {err}");
    }
}

#[test]
fn single_result_exports_still_compile_1450() {
    let module = decode_wasm_module(SINGLE_RESULTS).expect("decodes");
    assert_eq!(module.func_result_counts, [1, 1]);
    for relocatable in [false, true] {
        ArmBackend::new()
            .compile_module(&module, &cfg(relocatable))
            .expect("single-result exports compile");
    }
}

/// `(module (func $two (param i32) (result i32 i32) ...x*3, x*5...)
///   (func (export "one") (param i32) (result i32) local.get 0 call $two i32.add))`
///
/// An in-module call to a multi-result function. The CLI refused it
/// (RQ-91-MVDROP) from the config's result tables; `compile_module` with a
/// default config left those empty and returned `Ok` on c4113fa6 — wasm
/// gives 8x, a one-value call model at most 6x.
const INTERNAL_CALL_OF_PAIR: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x0c, 0x02, 0x60, 0x01, 0x7f, 0x02, 0x7f,
    0x7f, 0x60, 0x01, 0x7f, 0x01, 0x7f, 0x03, 0x03, 0x02, 0x00, 0x01, 0x07, 0x07, 0x01, 0x03, 0x6f,
    0x6e, 0x65, 0x00, 0x01, 0x0a, 0x16, 0x02, 0x0c, 0x00, 0x20, 0x00, 0x41, 0x03, 0x6c, 0x20, 0x00,
    0x41, 0x05, 0x6c, 0x0b, 0x07, 0x00, 0x20, 0x00, 0x10, 0x00, 0x6a, 0x0b, 0x00, 0x0d, 0x04, 0x6e,
    0x61, 0x6d, 0x65, 0x01, 0x06, 0x01, 0x00, 0x03, 0x74, 0x77, 0x6f,
];

#[test]
fn compile_module_refuses_an_in_module_multi_result_call_1450() {
    let module = decode_wasm_module(INTERNAL_CALL_OF_PAIR).expect("decodes");
    assert_eq!(module.func_result_counts, [2, 1]);
    for relocatable in [false, true] {
        let err = ArmBackend::new()
            .compile_module(&module, &cfg(relocatable))
            .map(|_| ())
            .expect_err("a multi-result call has no lowering")
            .to_string();
        assert!(err.contains("MULTI-RESULT call"), "{err}");
    }
}
