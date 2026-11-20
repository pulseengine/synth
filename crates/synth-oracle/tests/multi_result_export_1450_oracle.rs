//! #1450 — the EXECUTED half of the multi-result entry-point refusal.
//!
//! `crates/synth-cli/tests/multi_result_entry_refusal_1450.rs` pins the
//! refusal on every backend by exit code and diagnostic. This file is its
//! paired control, executed: the same two computations the issue's
//! `(result i32 i32)` function returns, x*3 and x*5, exported as two
//! single-result functions, compile and return what kiln returns — on
//! cortex-m4 and rv32imac, `--relocatable` — including beside an unexported,
//! uncalled multi-result function, which the refusal must not reach.
//!
//! The multi-result export itself cannot be executed here in either
//! direction: the emulator refuses a multi-value signature (there is no
//! return convention to read results by), which is the defect.
//!
//! NOT COVERED: AArch64 (the harness emulates ARM and RV32 only; its refusal
//! is pinned by the CLI test, unexecuted) and float results.
//!
//! Needs `--features exec` (kiln + unicorn).

#![cfg(feature = "exec")]

use std::path::PathBuf;

use synth_oracle::compare::{EmuOutcome, RefOutcome};
use synth_oracle::emulate::{Cpu, EmuConfig};
use synth_oracle::reference::Imports;
use synth_oracle::run_case;
use synth_oracle::synth::compile;
use synth_oracle::value::WasmValue;

const FUEL: u64 = 1_000_000;

const EXPORTED_PAIR: &str = r#"(module
  (func (export "two") (param i32) (result i32 i32)
    local.get 0 i32.const 3 i32.mul
    local.get 0 i32.const 5 i32.mul))
"#;

const SINGLE_RESULTS: &str = r#"(module
  (func (export "first") (param i32) (result i32) local.get 0 i32.const 3 i32.mul)
  (func (export "second") (param i32) (result i32) local.get 0 i32.const 5 i32.mul))
"#;

/// The same exports beside an unexported, uncalled multi-result function.
const SINGLE_RESULTS_BESIDE_UNEXPORTED_PAIR: &str = r#"(module
  (func $two (param i32) (result i32 i32)
    local.get 0 i32.const 3 i32.mul
    local.get 0 i32.const 5 i32.mul)
  (func (export "first") (param i32) (result i32) local.get 0 i32.const 3 i32.mul)
  (func (export "second") (param i32) (result i32) local.get 0 i32.const 5 i32.mul))
"#;

const VECTORS: &[u32] = &[0, 1, 7, 0x7FFF_FFFF, 0x8000_0000, 0xFFFF_FFFF, 0xDEAD_BEEF];

struct Leg {
    name: &'static str,
    cpu: Cpu,
    flags: &'static [&'static str],
}

const LEGS: &[Leg] = &[
    Leg {
        name: "cortex-m4",
        cpu: Cpu::CortexM4,
        flags: &["--target", "cortex-m4", "--relocatable", "--all-exports"],
    },
    Leg {
        name: "rv32imac",
        cpu: Cpu::Rv32Imac,
        flags: &[
            "-b",
            "riscv",
            "--target",
            "riscv32imac",
            "--relocatable",
            "--all-exports",
        ],
    },
];

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-oracle-1450-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// Compile `wat` on `leg` and run both exports over every vector; return the
/// number of cases, all of which agreed with kiln AND with the literal.
fn agree(leg: &Leg, wat: &str) -> usize {
    let wasm = wat::parse_str(wat).expect("WAT parses");
    let dir = scratch();
    let input = dir.join("m.wasm");
    std::fs::write(&input, &wasm).unwrap();
    let run = compile(&input, leg.flags, &dir.join("m.o")).expect("synth runs");
    assert!(run.status.success(), "{}: {}", leg.name, run.stderr);
    assert!(
        !run.stderr.contains("MULTI-RESULT function"),
        "{}: the refusal fired on a module with no multi-result entry point:\n{}",
        leg.name,
        run.stderr
    );
    let obj = run.object.expect("object parsed");
    let cfg = EmuConfig::new(leg.cpu);
    let imports = Imports::new();
    let mut n = 0;
    for (export, k) in [("first", 3u32), ("second", 5u32)] {
        assert_eq!(obj.relocs_in(export), 0, "{}: `{export}`", leg.name);
        for &x in VECTORS {
            let c = run_case(
                &wasm,
                &obj,
                export,
                &[WasmValue::I32(x)],
                FUEL,
                &imports,
                &cfg,
            )
            .unwrap_or_else(|e| panic!("{} {export}({x}): harness error {e:?}", leg.name));
            assert!(
                c.verdict.is_agree(),
                "{} {export}({x}): {:?} (ref {:?}, emu {:?})",
                leg.name,
                c.verdict,
                c.reference,
                c.emulator
            );
            // The expected value as a LITERAL computation too, so agreement
            // between two engines that are both wrong cannot pass.
            let want = vec![WasmValue::I32(x.wrapping_mul(k))];
            assert_eq!(c.reference, RefOutcome::Values(want.clone()));
            assert_eq!(c.emulator, EmuOutcome::Values(want));
            n += 1;
        }
    }
    n
}

#[test]
fn single_result_control_executes_equal_to_kiln() {
    let mut total = 0;
    for leg in LEGS {
        total += agree(leg, SINGLE_RESULTS);
        total += agree(leg, SINGLE_RESULTS_BESIDE_UNEXPORTED_PAIR);
    }
    // EXACT, as a literal: 2 legs x 2 modules x 2 exports x 7 vectors.
    assert_eq!(total, 56, "case count moved");
    eprintln!(
        "ORACLE multi-result-1450: {total} single-result control cases agree across {} legs",
        LEGS.len()
    );
}

/// The issue's own value, by hand: x = 7 gives 21 and 35 from the two
/// single-result exports. (On 6641efec the multi-result export returned only
/// the 35.)
#[test]
fn control_returns_21_and_35_for_7() {
    for leg in LEGS {
        let wasm = wat::parse_str(SINGLE_RESULTS).unwrap();
        let dir = scratch();
        let input = dir.join("m.wasm");
        std::fs::write(&input, &wasm).unwrap();
        let run = compile(&input, leg.flags, &dir.join("m.o")).expect("synth runs");
        let obj = run.object.expect("compiled");
        let cfg = EmuConfig::new(leg.cpu);
        for (export, want) in [("first", 21u32), ("second", 35u32)] {
            let c = run_case(
                &wasm,
                &obj,
                export,
                &[WasmValue::I32(7)],
                FUEL,
                &Imports::new(),
                &cfg,
            )
            .unwrap();
            assert_eq!(
                c.emulator,
                EmuOutcome::Values(vec![WasmValue::I32(want)]),
                "{} {export}(7)",
                leg.name
            );
        }
    }
}

#[test]
fn exported_multi_result_function_is_refused_with_no_object() {
    for leg in LEGS {
        let wasm = wat::parse_str(EXPORTED_PAIR).unwrap();
        let dir = scratch();
        let input = dir.join("m.wasm");
        std::fs::write(&input, &wasm).unwrap();
        let out = dir.join("m.o");
        let run = compile(&input, leg.flags, &out).expect("synth runs");
        assert!(
            !run.status.success(),
            "{}: exit 0 — the multi-result export was compiled",
            leg.name
        );
        assert!(run.object.is_none());
        assert!(!out.exists(), "{}: refused, yet an object exists", leg.name);
        assert!(
            run.stderr.contains("MULTI-RESULT function") && run.stderr.contains("#1450"),
            "{}: {}",
            leg.name,
            run.stderr
        );
    }
}
