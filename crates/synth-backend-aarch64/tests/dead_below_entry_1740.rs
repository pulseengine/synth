//! RQ-92-A64BELOW (#1740): AArch64 dead code that pops BELOW its frame's
//! entry height, through the published `Backend::compile_module` API.
//!
//! WASM validates code after an unconditional transfer against a polymorphic
//! stack, so it may pop the values the selector's model holds for the code
//! beneath the frame. Lowering that dead code popped them out of the model: a
//! debug build PANICKED at the join ("void frame must restore stack height"),
//! a release build declined with an uninformative `binop underflow`. The
//! selector now skips dead code, so these shapes compile.
//!
//! Two pins, both RED on 265235dc (a panic under `cargo test`):
//! 1. every export of both fixtures compiles (the #1691 fixture, whose
//!    `refuse_below` is the reported shape, and the #1740 fixture);
//! 2. each `b_*` below-entry export of the #1740 fixture compiles to text
//!    BYTE-IDENTICAL to its `l_*` twin — the same function with the dead code
//!    deleted. Dead code is never executed, so it may contribute no bytes and
//!    must not perturb the live code around it.
//!
//! Execution against wasmtime: scripts/repro/aarch64_dead_below_1740_differential.py.

use std::collections::BTreeMap;

use synth_backend_aarch64::AArch64Backend;
use synth_core::backend::{Backend, CompileConfig, SafetyBounds};
use synth_core::target::TargetSpec;
use synth_core::wasm_decoder::decode_wasm_module;

const FIXTURE_1691: &str = include_str!("../../../scripts/repro/if_arm_dead_value_1691.wat");
const FIXTURE_1740: &str = include_str!("../../../scripts/repro/aarch64_dead_below_1740.wat");

/// `{export name: code bytes, or that function's backend error}`.
///
/// Each function goes through `Backend::compile_function` with the per-function
/// facts the CLI threads (declared param count, blocktype-arity side-table).
/// NOT `compile_module`: on 265235dc it does not thread a function's
/// `block_arity` (`..config.clone()` keeps the caller's empty table), so every
/// value-carrying block reads as void there — a separate defect, reported with
/// this lane rather than masked by it.
fn compile(wat: &str) -> BTreeMap<String, Result<Vec<u8>, String>> {
    let wasm = wat::parse_str(wat).expect("fixture parses");
    let module = decode_wasm_module(&wasm).expect("fixture decodes");
    let mut out = BTreeMap::new();
    for func in &module.functions {
        let name = func
            .export_name
            .clone()
            .expect("every fixture function is exported");
        assert!(func.unsupported.is_none(), "{name}: decoder dropped an op");
        let cfg = CompileConfig {
            target: TargetSpec::cortex_a53(),
            safety_bounds: SafetyBounds::Software,
            current_func_param_count: Some(1),
            current_func_block_arity: func.block_arity.clone(),
            ..CompileConfig::default()
        };
        let f = AArch64Backend::new()
            .compile_function(&name, &func.ops, &cfg)
            .map(|f| f.code)
            .map_err(|e| e.to_string());
        out.insert(name, f);
    }
    out
}

/// The two `br_table` exports of the #1691 fixture carry a value through the
/// table, which the AArch64 compare chain loud-declines by name (VCR-A64-CF-001,
/// unchanged by #1740). Exact both ways: any OTHER decline is red, and so is
/// either of these starting to compile without this table moving.
const DECLINED_1691: &[&str] = &["t_f32_br_table", "t_i32_br_table"];

#[test]
fn fixture_1691_compiles_including_refuse_below_1740() {
    let funcs = compile(FIXTURE_1691);
    assert!(funcs.contains_key("refuse_below"), "{:?}", funcs.keys());
    let mut declined = Vec::new();
    for (name, r) in &funcs {
        match r {
            Ok(code) => assert!(!code.is_empty(), "{name}: emitted no code"),
            Err(e) => {
                assert!(
                    e.contains("br_table with VALUE-CARRYING targets"),
                    "{name}: unexpected decline: {e}"
                );
                declined.push(name.as_str());
            }
        }
    }
    assert_eq!(declined, DECLINED_1691);
}

#[test]
fn dead_code_below_entry_contributes_no_bytes_1740() {
    let funcs: BTreeMap<String, Vec<u8>> = compile(FIXTURE_1740)
        .into_iter()
        .map(|(n, r)| {
            let code = r.unwrap_or_else(|e| panic!("{n}: {e}"));
            (n, code)
        })
        .collect();
    let below: Vec<&String> = funcs.keys().filter(|n| n.starts_with("b_")).collect();
    // Population pin: an export silently missing would shrink the check.
    assert_eq!(below.len(), 11, "every b_* shape compiled: {below:?}");
    for name in below {
        let twin = format!("l_{}", &name[2..]);
        let (b, l) = (&funcs[name], &funcs[&twin]);
        assert!(!b.is_empty(), "{name}: emitted no code");
        assert_eq!(b, l, "{name}: dead code changed the emitted text vs {twin}");
    }
}
