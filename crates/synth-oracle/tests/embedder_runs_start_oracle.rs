//! `--embedder-runs-start`, executed (P3-BUILTINS I0; Refs #1046, #1786).
//!
//! The flag defines a module's start function as the GLOBAL symbol
//! `__synth_start` of an ARM relocatable object, and the embedder contract
//! (docs/embedder-abi-relocatable-arm.md) says the embedder calls it once,
//! after setting R11/R10/R9 and before any export. This oracle plays that
//! embedder (`synth_oracle::hosted`: `Hosted::link` calls `__synth_start`
//! when the module has a start section and the object defines the symbol)
//! and compares every following export call with kiln, which runs the start
//! function at instantiation (WASM Core §4.5.5). A symbol that is not really
//! the start function, or a start function that does not do what the wasm
//! says, shows up as a wrong value read through an export.
//!
//! Legs: an import-free module on `--relocatable` (cortex-m4, cortex-m3,
//! cortex-m7dp), and a module whose exports call an import compiled on
//! DEFAULT flags (no `--relocatable`: the #1696 host-link rule makes it the
//! same object). POTENCY: the same object with `__synth_start` removed is
//! refused by the harness, and with `__synth_start` pointed at a different
//! `() -> ()` function it disagrees with kiln.
//!
//! Needs `--features exec` (kiln + unicorn). `SYNTH` may name a prebuilt
//! binary; otherwise the test builds `synth-cli`.

#![cfg(feature = "exec")]

use std::path::PathBuf;

use synth_oracle::compare::Verdict;
use synth_oracle::emulate::{Cpu, EmuError};
use synth_oracle::hosted::{HostConfig, START_SYMBOL};
use synth_oracle::reference::Imports;
use synth_oracle::synth::{CompiledObject, compile};
use synth_oracle::value::WasmValue;
use synth_oracle::{CaseError, HostedCase, run_hosted};

const FUEL: u64 = 1_000_000;
const LINMEM: u32 = 0x2001_0000;

/// The start function stores through a callee (so the closure must carry the
/// callee too) and leaves state three exports read and one updates. `noop` is
/// a second `() -> ()` function for the potency leg.
const START_WAT: &str = r#"
(module
  (memory 1)
  (func $put (param i32 i32) local.get 0 local.get 1 i32.store)
  (func $init
    (call $put (i32.const 0) (i32.const 42))
    (call $put (i32.const 64) (i32.const 0x1234_5678)))
  (start $init)
  (func (export "noop"))
  (func (export "get") (result i32) i32.const 0 i32.load)
  (func (export "get64") (result i32) i32.const 64 i32.load)
  (func (export "bump") (result i32)
    i32.const 0 i32.const 0 i32.load i32.const 1 i32.add i32.store
    i32.const 0 i32.load))
"#;

/// Exports call an import, so the default-flags compile is a host-linked
/// object (#1696) and the start function rides the same contract.
const START_IMPORT_WAT: &str = r#"
(module
  (import "env" "add2" (func $add2 (param i32 i32) (result i32)))
  (memory 1)
  (func $init (i32.store (i32.const 8) (i32.const 1000)))
  (start $init)
  (func (export "noop"))
  (func (export "plus") (param i32) (result i32)
    (call $add2 (i32.load (i32.const 8)) (local.get 0))))
"#;

fn imports() -> Imports {
    Imports::new().func("env", "add2", |a: &[WasmValue]| match a {
        [WasmValue::I32(x), WasmValue::I32(y)] => Ok(vec![WasmValue::I32(x.wrapping_add(*y))]),
        _ => Err(format!("bad args {a:?}")),
    })
}

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-startabi-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn build(wat: &str, flags: &[&str]) -> (Vec<u8>, CompiledObject) {
    let wasm = wat::parse_str(wat).expect("WAT parses");
    let dir = scratch();
    let input = dir.join("m.wasm");
    std::fs::write(&input, &wasm).unwrap();
    let out = dir.join("m.o");
    let run = compile(&input, flags, &out).expect("synth runs");
    assert!(
        run.status.success(),
        "{flags:?}: synth compile failed: {}",
        run.stderr
    );
    let obj = run.object.expect("object parsed");
    assert!(obj.relocatable, "{flags:?}: expected an ET_REL object");
    (wasm, obj)
}

fn i(v: u32) -> WasmValue {
    WasmValue::I32(v)
}

type Step = (&'static str, Vec<WasmValue>);

fn cases(
    wasm: &[u8],
    obj: &CompiledObject,
    steps: &[Step],
    cpu: Cpu,
) -> Result<Vec<HostedCase>, CaseError> {
    let borrowed: Vec<(&str, &[WasmValue])> = steps.iter().map(|(e, a)| (*e, &a[..])).collect();
    run_hosted(
        wasm,
        obj,
        &borrowed,
        FUEL,
        &imports(),
        &HostConfig::new(cpu, LINMEM),
    )
}

/// Every step runs and agrees with kiln; returns the step count.
fn require_agree(what: &str, wasm: &[u8], obj: &CompiledObject, steps: &[Step], cpu: Cpu) -> usize {
    let cs = cases(wasm, obj, steps, cpu).unwrap_or_else(|e| panic!("{what}: harness {e:?}"));
    let bad: Vec<String> = cs
        .iter()
        .filter(|c| !c.verdict.is_agree())
        .map(|c| {
            format!(
                "{}{:?}: kiln {:?} | machine code {:?} | {:?}",
                c.export, c.args, c.reference, c.emulator, c.verdict
            )
        })
        .collect();
    assert!(bad.is_empty(), "{what}:\n  {}", bad.join("\n  "));
    assert_eq!(cs.len(), steps.len(), "{what}: the sequence ended early");
    cs.len()
}

fn start_steps() -> Vec<Step> {
    vec![
        ("get", vec![]),
        ("get64", vec![]),
        ("bump", vec![]),
        ("bump", vec![]),
        ("get", vec![]),
    ]
}

const LEGS: &[(&str, Cpu)] = &[
    ("cortex-m4", Cpu::CortexM4),
    ("cortex-m3", Cpu::CortexM3),
    ("cortex-m7dp", Cpu::CortexM7),
];

#[test]
fn synth_start_is_the_start_function() {
    let mut steps = 0;
    for (target, cpu) in LEGS {
        let flags = [
            "--target",
            target,
            "--all-exports",
            "--relocatable",
            "--embedder-runs-start",
        ];
        let (wasm, obj) = build(START_WAT, &flags);
        assert!(
            obj.func(START_SYMBOL).is_some_and(|f| f.global),
            "{target}: no GLOBAL {START_SYMBOL}"
        );
        steps += require_agree(target, &wasm, &obj, &start_steps(), *cpu);

        // Default flags, host-linked through the import (#1696).
        let flags = ["--target", target, "--all-exports", "--embedder-runs-start"];
        let (wasm, obj) = build(START_IMPORT_WAT, &flags);
        let s = vec![("plus", vec![i(5)]), ("plus", vec![i(0xFFFF_FFFF)])];
        steps += require_agree(&format!("{target} host-linked"), &wasm, &obj, &s, *cpu);
    }
    println!("ORACLE embedder-runs-start: {steps} steps agree with kiln across 3 targets");
    assert_eq!(steps, 3 * (5 + 2));
}

/// POTENCY 1: the same object WITHOUT `__synth_start` is refused by the
/// harness. It is never run as if the start function had executed.
#[test]
fn potency_missing_synth_start_is_refused() {
    let flags = [
        "--target",
        "cortex-m4",
        "--all-exports",
        "--relocatable",
        "--embedder-runs-start",
    ];
    let (wasm, mut obj) = build(START_WAT, &flags);
    assert!(obj.funcs.remove(START_SYMBOL).is_some());
    let e = cases(&wasm, &obj, &start_steps(), Cpu::CortexM4).unwrap_err();
    assert!(
        matches!(
            e,
            CaseError::Emulator(EmuError::Uninstantiated("a start function"))
        ),
        "{e:?}"
    );
}

/// POTENCY 2: `__synth_start` pointed at `noop`, another `() -> ()` function,
/// makes `get` read 0 where kiln reads 42. The comparison catches a start
/// symbol that is not the start function.
#[test]
fn potency_wrong_synth_start_disagrees() {
    for (wat, steps) in [
        (START_WAT, start_steps()),
        (START_IMPORT_WAT, vec![("plus", vec![i(5)])]),
    ] {
        let flags = [
            "--target",
            "cortex-m4",
            "--all-exports",
            "--relocatable",
            "--embedder-runs-start",
        ];
        let (wasm, mut obj) = build(wat, &flags);
        let noop = obj.func("noop").expect("noop").clone();
        assert_ne!(obj.func(START_SYMBOL).unwrap().offset, noop.offset);
        obj.funcs.insert(START_SYMBOL.to_string(), noop);
        let cs = cases(&wasm, &obj, &steps, Cpu::CortexM4).expect("harness runs");
        assert!(
            matches!(cs[0].verdict, Verdict::Disagree(_)),
            "a wrong start symbol must disagree with kiln: {:?}",
            cs[0]
        );
    }
}
