//! RQ-91-A64BELOW (#1740): AArch64 dead code that pops BELOW its frame's
//! entry height, through the published `Backend::compile_function` API.
//!
//! WASM validates code after an unconditional transfer against a polymorphic
//! stack, so it may pop the values the selector's model holds for the code
//! beneath the frame. Lowering that dead code popped them out of the model: a
//! debug build PANICKED at the join ("void frame must restore stack height"),
//! a release build declined with an uninformative `binop underflow`. The
//! selector now skips dead code, so these shapes compile.
//!
//! Three pins, RED on 265235dc (the first two panic under `cargo test`):
//! 1. every export of both fixtures compiles (the #1691 fixture, whose
//!    `refuse_below` is the reported shape, and the #1740 fixture, including
//!    its seven `r_*` frames that no live edge enters — three of which an
//!    earlier cut of this change regressed to a `funop` decline);
//! 2. each `b_*` below-entry export of the #1740 fixture compiles to text
//!    BYTE-IDENTICAL to its `l_*` twin — the same function with the dead code
//!    deleted. Dead code is never executed, so it may contribute no bytes and
//!    must not perturb the live code around it.
//!
//! 3. each `w_*` float-result export returns through the FP result register:
//!    every `ret` is preceded by an `fmov` into v0. 265235dc compiled three of
//!    them to `mov x0, x9 ; ret` — silent wrong code, Refs #1747 — because it
//!    reconciled the GP placeholder of an inner float frame no edge enters.
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
/// NOT `compile_module`: it does not thread a function's `block_arity`
/// (`..config.clone()` keeps the caller's empty table), so every
/// value-carrying block reads as void there — a separate defect, #1745, not
/// fixed or masked here.
fn compile(wat: &str) -> BTreeMap<String, Result<Vec<u8>, String>> {
    compile_where(wat, |_| true)
}

/// [`compile`] restricted to the exports `keep` selects (so a pin on some
/// exports is not masked by another export panicking on the base).
fn compile_where(
    wat: &str,
    keep: impl Fn(&str) -> bool,
) -> BTreeMap<String, Result<Vec<u8>, String>> {
    let wasm = wat::parse_str(wat).expect("fixture parses");
    let module = decode_wasm_module(&wasm).expect("fixture decodes");
    let mut out = BTreeMap::new();
    for func in &module.functions {
        let name = func
            .export_name
            .clone()
            .expect("every fixture function is exported");
        if !keep(&name) {
            continue;
        }
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
    let no_live_edge = funcs.keys().filter(|n| n.starts_with("r_")).count();
    assert_eq!(no_live_edge, 7, "every r_* shape compiled");
    for name in below {
        let twin = format!("l_{}", &name[2..]);
        let (b, l) = (&funcs[name], &funcs[&twin]);
        assert!(!b.is_empty(), "{name}: emitted no code");
        assert_eq!(b, l, "{name}: dead code changed the emitted text vs {twin}");
    }
}

/// Refs #1747: a float frame whose only live edge is a `br` from an inner float
/// frame that no edge enters. Every return path must write v0 (`fmov d0/s0`);
/// 265235dc returned through `mov x0, xN` and never wrote v0.
#[test]
fn float_join_returns_through_v0_1747() {
    use synth_backend_aarch64::encoder as enc;
    let funcs = compile_where(FIXTURE_1740, |n| n.starts_with("w_"));
    let fp_to_v0: Vec<u32> = (0..32u8)
        .flat_map(|r| [enc::fmov_d(0, r), enc::fmov_s(0, r)])
        .collect();
    let gp_to_x0: Vec<u32> = (0..32u8).map(|r| enc::mov_reg64(0, r)).collect();
    let mut checked = 0;
    for (name, r) in funcs.iter().filter(|(n, _)| n.starts_with("w_")) {
        let code = r.as_ref().unwrap_or_else(|e| panic!("{name}: {e}"));
        let words: Vec<u32> = code
            .chunks(4)
            .map(|b| u32::from_le_bytes(b.try_into().unwrap()))
            .collect();
        let rets: Vec<usize> = (0..words.len())
            .filter(|&i| words[i] == enc::ret())
            .collect();
        assert!(!rets.is_empty(), "{name}: no ret");
        for i in rets {
            assert!(i > 0, "{name}: ret at word 0");
            assert!(
                !gp_to_x0.contains(&words[i - 1]),
                "{name}: returns a float through x0 (word {i}, #1747)"
            );
            assert!(
                fp_to_v0.contains(&words[i - 1]),
                "{name}: ret at word {i} not preceded by an fmov into v0"
            );
        }
        checked += 1;
    }
    assert_eq!(checked, 4, "every w_* shape checked");
}
