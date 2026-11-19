//! The import call boundary of a DEFAULT-FLAGS Cortex-M object, executed
//! (Refs #1696, #1755, #1699, #1758).
//!
//! A module that calls a function import is emitted as an `ET_REL` object the
//! embedder links, with or without `--relocatable`. This oracle compiles such
//! modules on DEFAULT flags (no `--relocatable`) for cortex-m4, cortex-m3 and
//! cortex-m7dp, links each object against host stubs the way an embedder does
//! (`synth_oracle::hosted`: a stub per import symbol, AAPCS arguments, every
//! caller-saved register clobbered on return, linear memory at an address the
//! test chooses, R11/R10 set to it) and requires every step to agree with
//! kiln: same return value AND the same host calls with the same arguments.
//!
//! The four defects, each with its own module so each shows its own wrong
//! value on a compiler that has it:
//!
//! - #1696: a value live across an import call (and the void-import phantom
//!   value, same root);
//! - #1755: import arguments that never reach R0-R3;
//! - #1699: the Meld dispatch fallback (`bl __meld_dispatch_import`, the
//!   import index in R0, no arguments);
//! - #1758: one object addressing linear memory two ways, so a store through
//!   one export is not what another export loads.
//!
//! PAIRED CONTROL: the same modules compiled `--relocatable` agree on every
//! step (they did before the fix too), so a red leg is the compiler's and not
//! the harness's. STRUCTURAL LEG: on every Cortex-M target and on cortex-r5
//! (A32, not executed here), the default-flags object IS the `--relocatable`
//! object, byte for byte. The potency legs at the end show each harness guard
//! red on hand-written machine code.
//!
//! Needs `--features exec` (kiln + unicorn). `SYNTH` may name a prebuilt
//! binary; otherwise the test builds `synth-cli`.

#![cfg(feature = "exec")]

use std::path::PathBuf;

use synth_oracle::compare::{EmuOutcome, RefOutcome, Verdict};
use synth_oracle::emulate::{Cpu, EmuError};
use synth_oracle::hosted::{CLOBBER, HostConfig, Hosted};
use synth_oracle::reference::Imports;
use synth_oracle::synth::{CompiledObject, FuncSym, Machine, R_ARM_THM_CALL, TextReloc, compile};
use synth_oracle::value::WasmValue;
use synth_oracle::{CaseError, HostedCase, run_hosted};

const FUEL: u64 = 1_000_000;

/// Linear memory, deliberately NOT at the self-contained image's 0x2000_0100.
const LINMEM: u32 = 0x2001_0000;
/// A second placement, far from any SRAM address.
const LINMEM_FAR: u32 = 0x3000_0000;
/// The board SRAM an absolute 0x2000_0100 access would land in.
const SRAM: (u32, u32) = (0x2000_0000, 0x1_0000);

struct Leg {
    name: &'static str,
    target: &'static str,
    cpu: Cpu,
}

const LEGS: &[Leg] = &[
    Leg {
        name: "cortex-m4",
        target: "cortex-m4",
        cpu: Cpu::CortexM4,
    },
    Leg {
        name: "cortex-m3",
        target: "cortex-m3",
        cpu: Cpu::CortexM3,
    },
    Leg {
        name: "cortex-m7dp",
        target: "cortex-m7dp",
        cpu: Cpu::CortexM7,
    },
];

/// #1696 and #1755: no local calls, so before the fix every function here
/// took the optimized path.
const CALLS_WAT: &str = r#"
(module
  (import "env" "log" (func $log (param i32)))
  (import "env" "add2" (func $add2 (param i32 i32) (result i32)))
  (import "env" "sub2" (func $sub2 (param i32 i32) (result i32)))
  ;; #1696: the parameter is live across the call.
  (func (export "call_log") (param i32) (result i32)
    local.get 0 call $log local.get 0)
  ;; #1696: a temporary is live across the call.
  (func (export "temp_across") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.mul local.get 0 call $log local.get 1 i32.add)
  ;; The void-import phantom value: the 5 must still be the result.
  (func (export "phantom") (param i32) (result i32)
    i32.const 5 local.get 0 call $log)
  (func (export "log_then_add") (param i32 i32) (result i32)
    local.get 0 call $log local.get 0 local.get 1 i32.add)
  ;; #1755: constant arguments.
  (func (export "cargs") (result i32) i32.const 3 i32.const 11 call $add2)
  ;; #1755: computed arguments.
  (func (export "dargs") (param i32 i32) (result i32)
    local.get 0 i32.const 1 i32.add local.get 1 i32.const 2 i32.add call $add2)
  ;; Argument ORDER, through a non-commutative import.
  (func (export "ordered") (param i32 i32) (result i32)
    local.get 0 local.get 1 call $sub2)
  (func (export "swapped") (param i32 i32) (result i32)
    local.get 1 local.get 0 call $sub2)
  ;; Two calls, the first result live across the second.
  (func (export "two_calls") (param i32 i32) (result i32)
    local.get 0 local.get 1 call $add2
    local.get 1 local.get 0 call $sub2
    i32.mul))
"#;

/// #1699: each export also makes a LOCAL call, which routed it to the direct
/// selector, whose non-relocatable import lowering was the Meld dispatch.
const DISPATCH_WAT: &str = r#"
(module
  (import "env" "add2" (func $add2 (param i32 i32) (result i32)))
  (import "env" "sub2" (func $sub2 (param i32 i32) (result i32)))
  (func $nop)
  (func (export "g") (result i32)
    call $nop i32.const 3 i32.const 11 call $add2)
  (func (export "h") (param i32 i32) (result i32)
    call $nop local.get 1 local.get 0 i32.sub i32.const 5 call $add2)
  (func (export "k") (param i32 i32) (result i32)
    call $nop local.get 0 local.get 1 call $sub2))
"#;

/// #1758: `st` and `ld` make no call (optimized path before the fix: absolute
/// 0x2000_0100), `ld2` and `st2` make a local call (direct selector: R11).
const MEMORY_WAT: &str = r#"
(module
  (import "env" "log" (func $log (param i32)))
  (memory 1)
  (func $h (param i32) (result i32) local.get 0)
  (func (export "ld") (param i32) (result i32) local.get 0 i32.load)
  (func (export "st") (param i32 i32) local.get 0 local.get 1 i32.store)
  (func (export "ld2") (param i32) (result i32) local.get 0 call $h i32.load)
  (func (export "st2") (param i32 i32) local.get 0 call $h local.get 1 i32.store)
  (func (export "c") (param i32) local.get 0 call $log))
"#;

fn imports() -> Imports {
    let two = |f: fn(u32, u32) -> u32| {
        move |a: &[WasmValue]| match a {
            [WasmValue::I32(x), WasmValue::I32(y)] => Ok(vec![WasmValue::I32(f(*x, *y))]),
            _ => Err(format!("bad args {a:?}")),
        }
    };
    Imports::new()
        .trace("env", "log", vec![])
        .func("env", "add2", two(u32::wrapping_add))
        .func("env", "sub2", two(u32::wrapping_sub))
}

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-importabi-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// Compile `wat` for `target`; `relocatable` adds the flag. Returns the wasm,
/// the parsed object and the object file's bytes.
fn build(wat: &str, target: &str, relocatable: bool) -> (Vec<u8>, CompiledObject, Vec<u8>) {
    let wasm = wat::parse_str(wat).expect("WAT parses");
    let dir = scratch();
    let input = dir.join("m.wasm");
    std::fs::write(&input, &wasm).unwrap();
    let out = dir.join("m.o");
    let mut flags = vec!["--target", target, "--all-exports"];
    if relocatable {
        flags.push("--relocatable");
    }
    let run = compile(&input, &flags, &out).expect("synth runs");
    assert!(
        run.status.success(),
        "{target} {flags:?}: synth compile failed: {}",
        run.stderr
    );
    let bytes = std::fs::read(&out).unwrap();
    (wasm, run.object.expect("object parsed"), bytes)
}

fn i(v: u32) -> WasmValue {
    WasmValue::I32(v)
}

type Step = (&'static str, Vec<WasmValue>);

fn show(c: &HostedCase) -> String {
    format!(
        "{}{:?}: kiln {:?} calls {:?} | machine code {:?} calls {:?} | {:?}",
        c.export, c.args, c.reference, c.ref_calls, c.emulator, c.emu_calls, c.verdict
    )
}

/// Steps and matched host calls, or what disagreed.
type Tally = Result<(usize, usize), String>;

/// Add one leg's tally to the running total, or record its failure.
fn add(total: &mut (usize, usize), red: &mut Vec<String>, t: Tally) {
    match t {
        Ok((s, c)) => *total = (total.0 + s, total.1 + c),
        Err(e) => red.push(e),
    }
}

/// Fail with every leg's disagreements, not only the first leg's.
fn require_green(red: &[String]) {
    assert!(red.is_empty(), "\n{}", red.join("\n"));
}

/// Run `steps` as ONE sequence; every step must run and agree.
fn require_agree(
    what: &str,
    wasm: &[u8],
    obj: &CompiledObject,
    steps: &[Step],
    cfg: &HostConfig,
) -> Tally {
    let borrowed: Vec<(&str, &[WasmValue])> = steps.iter().map(|(e, a)| (*e, &a[..])).collect();
    let cases = run_hosted(wasm, obj, &borrowed, FUEL, &imports(), cfg)
        .map_err(|e| format!("{what}: harness error {e:?}"))?;
    let mut bad: Vec<String> = cases
        .iter()
        .filter(|c| !c.verdict.is_agree())
        .map(show)
        .collect();
    if bad.is_empty() && cases.len() != steps.len() {
        bad.push("the sequence ended early".into());
    }
    if !bad.is_empty() {
        return Err(format!(
            "{what}: {} of {} steps disagree with kiln:\n  {}",
            bad.len(),
            cases.len(),
            bad.join("\n  ")
        ));
    }
    Ok((
        cases.len(),
        cases.iter().map(|c| c.emu_calls.len()).sum::<usize>(),
    ))
}

/// Each step on its OWN image and instance (no memory involved), so one wrong
/// step does not hide the next.
fn require_each(
    what: &str,
    wasm: &[u8],
    obj: &CompiledObject,
    steps: &[Step],
    cfg: &HostConfig,
) -> Tally {
    let mut bad = Vec::new();
    let mut calls = 0;
    for (e, a) in steps {
        match run_hosted(wasm, obj, &[(*e, &a[..])], FUEL, &imports(), cfg) {
            Ok(cases) => {
                for c in &cases {
                    calls += c.emu_calls.len();
                    if !c.verdict.is_agree() {
                        bad.push(show(c));
                    }
                }
                if cases.len() != 1 {
                    bad.push(format!("{e}{a:?}: did not run"));
                }
            }
            Err(err) => bad.push(format!("{e}{a:?}: harness error {err:?}")),
        }
    }
    if !bad.is_empty() {
        return Err(format!(
            "{what}: {} of {} steps disagree with kiln:\n  {}",
            bad.len(),
            steps.len(),
            bad.join("\n  ")
        ));
    }
    Ok((steps.len(), calls))
}

const VALS: &[u32] = &[0, 1, 7, 0x7FFF_FFFF, 0xDEAD_BEEF];

fn pairs() -> Vec<(u32, u32)> {
    vec![
        (10, 20),
        (0, 0),
        (1, 0xFFFF_FFFF),
        (0x8000_0000, 3),
        (30, 10),
    ]
}

/// #1696: the value-across-call and phantom-value shapes.
fn steps_1696() -> Vec<Step> {
    let mut s: Vec<Step> = Vec::new();
    for &v in VALS {
        s.push(("call_log", vec![i(v)]));
        s.push(("phantom", vec![i(v)]));
    }
    for (a, b) in pairs() {
        s.push(("temp_across", vec![i(a), i(b)]));
        s.push(("log_then_add", vec![i(a), i(b)]));
    }
    s
}

/// #1755: the argument shapes.
fn steps_1755() -> Vec<Step> {
    let mut s: Vec<Step> = vec![("cargs", vec![])];
    for (a, b) in pairs() {
        for e in ["dargs", "ordered", "swapped", "two_calls"] {
            s.push((e, vec![i(a), i(b)]));
        }
    }
    s
}

fn steps_1699() -> Vec<Step> {
    let mut s: Vec<Step> = vec![("g", vec![])];
    for (a, b) in pairs() {
        s.push(("h", vec![i(a), i(b)]));
        s.push(("k", vec![i(a), i(b)]));
    }
    s
}

/// #1758: stores through one model read back through the other, both ways.
fn steps_1758() -> Vec<Step> {
    vec![
        ("st", vec![i(8), i(42)]),
        ("ld", vec![i(8)]),
        ("ld2", vec![i(8)]),
        ("st2", vec![i(16), i(0xCAFE_F00D)]),
        ("ld2", vec![i(16)]),
        ("ld", vec![i(16)]),
        ("c", vec![i(5)]),
        ("ld2", vec![i(8)]),
        ("st", vec![i(65532), i(0x0102_0304)]),
        ("ld2", vec![i(65532)]),
    ]
}

#[test]
fn value_live_across_an_import_call_1696() {
    let (mut total, mut red) = ((0, 0), Vec::new());
    for leg in LEGS {
        let (wasm, obj, _) = build(CALLS_WAT, leg.target, false);
        let cfg = HostConfig::new(leg.cpu, LINMEM);
        let t = require_each(
            &format!("#1696 {}", leg.name),
            &wasm,
            &obj,
            &steps_1696(),
            &cfg,
        );
        add(&mut total, &mut red, t);
    }
    require_green(&red);
    println!(
        "ORACLE import-boundary #1696: {} steps agree across {} legs, {} host calls matched",
        total.0,
        LEGS.len(),
        total.1
    );
    assert_eq!(total, (60, 60));
}

#[test]
fn import_arguments_reach_r0_r3_1755() {
    let (mut total, mut red) = ((0, 0), Vec::new());
    for leg in LEGS {
        let (wasm, obj, _) = build(CALLS_WAT, leg.target, false);
        let cfg = HostConfig::new(leg.cpu, LINMEM);
        let t = require_each(
            &format!("#1755 {}", leg.name),
            &wasm,
            &obj,
            &steps_1755(),
            &cfg,
        );
        add(&mut total, &mut red, t);
    }
    require_green(&red);
    println!(
        "ORACLE import-boundary #1755: {} steps agree across {} legs, {} host calls matched",
        total.0,
        LEGS.len(),
        total.1
    );
    assert_eq!(total, (63, 78));
}

#[test]
fn no_dispatch_fallback_1699() {
    let (mut total, mut red) = ((0, 0), Vec::new());
    for leg in LEGS {
        let (wasm, obj, _) = build(DISPATCH_WAT, leg.target, false);
        let cfg = HostConfig::new(leg.cpu, LINMEM);
        // What a compiler with the defect emits: a call to a dispatcher no
        // contract defines. Show what arrives there, then fail.
        let dispatch: Vec<&TextReloc> = obj
            .relocs
            .iter()
            .filter(|r| r.symbol == "__meld_dispatch_import")
            .collect();
        if !dispatch.is_empty() {
            let dump = cfg.clone().raw_symbol("__meld_dispatch_import", |r| {
                // The stub the #1699 triage used: R1 + R2.
                r[1].wrapping_add(r[2])
            });
            let mut lines = Vec::new();
            for (e, a) in steps_1699() {
                let mut image = Hosted::link(&obj, &wasm, &imports(), &dump).unwrap();
                let run = image.call(e, &a).unwrap();
                let want = synth_oracle::reference::run(&wasm, e, &a, FUEL, &imports()).unwrap();
                lines.push(format!(
                    "{e}{a:?}: kiln {:?}; dispatcher entered with R0-R3 = {:?}; \
                     with an R1+R2 dispatcher the export returns {:?}",
                    want.outcome,
                    run.calls.iter().map(|c| c.args.clone()).collect::<Vec<_>>(),
                    run.outcome
                ));
            }
            red.push(format!(
                "#1699 {}: {} call site(s) go through __meld_dispatch_import, which receives \
                 the import index in R0 and no wasm arguments:\n  {}",
                leg.name,
                dispatch.len(),
                lines.join("\n  ")
            ));
            continue;
        }
        let t = require_each(
            &format!("#1699 {}", leg.name),
            &wasm,
            &obj,
            &steps_1699(),
            &cfg,
        );
        add(&mut total, &mut red, t);
    }
    require_green(&red);
    println!(
        "ORACLE import-boundary #1699: {} steps agree across {} legs, {} host calls matched",
        total.0,
        LEGS.len(),
        total.1
    );
    assert_eq!(total, (33, 33));
}

#[test]
fn one_linear_memory_model_per_object_1758() {
    let (mut total, mut red) = ((0, 0), Vec::new());
    for leg in LEGS {
        let (wasm, obj, _) = build(MEMORY_WAT, leg.target, false);
        // Two embedders. The first has board SRAM where an absolute
        // 0x2000_0100 access lands, so a wrong model reads zeros instead of
        // faulting; the second has nothing there, so it faults.
        for (name, cfg) in [
            (
                "linmem 0x20010000, SRAM mapped",
                HostConfig::new(leg.cpu, LINMEM).ram(SRAM.0, SRAM.1),
            ),
            (
                "linmem 0x30000000, no SRAM",
                HostConfig::new(leg.cpu, LINMEM_FAR),
            ),
        ] {
            let t = require_agree(
                &format!("#1758 {} ({name})", leg.name),
                &wasm,
                &obj,
                &steps_1758(),
                &cfg,
            );
            add(&mut total, &mut red, t);
            // The store is where the embedder put linear memory.
            let mut image = Hosted::link(&obj, &wasm, &imports(), &cfg).unwrap();
            let st = image.call("st", &[i(8), i(42)]).unwrap();
            let at_r11 = image.read_linmem(8, 4).unwrap();
            if at_r11 != 42u32.to_le_bytes() {
                red.push(format!(
                    "#1758 {} ({name}): st(8,42) -> {:?}; R11+8 holds {at_r11:02x?}, not 42",
                    leg.name, st.outcome
                ));
            }
        }
    }
    require_green(&red);
    println!(
        "ORACLE import-boundary #1758: {} steps agree across {} legs x 2 embedders, {} host calls matched",
        total.0,
        LEGS.len(),
        total.1
    );
    assert_eq!(total, (60, 6));
}

/// PAIRED CONTROL: `--relocatable` objects of the same modules agree on every
/// step, with or without the fix.
#[test]
fn control_relocatable_objects_agree() {
    let (mut total, mut red) = ((0, 0), Vec::new());
    for leg in LEGS {
        let cfg = HostConfig::new(leg.cpu, LINMEM).ram(SRAM.0, SRAM.1);
        let (wasm, obj, _) = build(CALLS_WAT, leg.target, true);
        let mut steps = steps_1696();
        steps.extend(steps_1755());
        let a = require_each(
            &format!("control calls {}", leg.name),
            &wasm,
            &obj,
            &steps,
            &cfg,
        );
        let (wasm, obj, _) = build(DISPATCH_WAT, leg.target, true);
        let b = require_each(
            &format!("control dispatch {}", leg.name),
            &wasm,
            &obj,
            &steps_1699(),
            &cfg,
        );
        let (wasm, obj, _) = build(MEMORY_WAT, leg.target, true);
        let c = require_agree(
            &format!("control memory {}", leg.name),
            &wasm,
            &obj,
            &steps_1758(),
            &cfg,
        );
        for t in [a, b, c] {
            add(&mut total, &mut red, t);
        }
    }
    require_green(&red);
    println!(
        "ORACLE import-boundary control: {} steps agree across {} --relocatable legs, {} host calls matched",
        total.0,
        LEGS.len(),
        total.1
    );
    assert_eq!(total, (186, 174));
}

/// STRUCTURAL: with a call to a function import, the default-flags object is the
/// `--relocatable` object, byte for byte, on every ARM target including the
/// A32 one this harness does not execute. And it is an `ET_REL` object with
/// one `R_ARM_THM_CALL` per import call against the BARE field name.
#[test]
fn default_object_is_the_relocatable_object() {
    let mut compared = 0;
    for target in ["cortex-m4", "cortex-m3", "cortex-m7dp", "cortex-r5"] {
        for (name, wat) in [
            ("calls", CALLS_WAT),
            ("dispatch", DISPATCH_WAT),
            ("memory", MEMORY_WAT),
        ] {
            let (_, obj, default) = build(wat, target, false);
            let (_, _, relocatable) = build(wat, target, true);
            assert!(obj.relocatable, "{target} {name}: not an ET_REL object");
            assert!(
                default == relocatable,
                "{target} {name}: the default-flags object ({} bytes) is not the \
                 --relocatable object ({} bytes)",
                default.len(),
                relocatable.len()
            );
            let external: std::collections::BTreeSet<&str> = obj
                .relocs
                .iter()
                .filter(|r| r.target.is_none())
                .map(|r| r.symbol.as_str())
                .collect();
            let want: &[&str] = match name {
                "calls" => &["add2", "log", "sub2"],
                "dispatch" => &["add2", "sub2"],
                _ => &["log"],
            };
            assert_eq!(
                external.into_iter().collect::<Vec<_>>(),
                want,
                "{target} {name}: undefined call targets are not the bare import field names"
            );
            compared += 1;
        }
    }
    println!(
        "ORACLE import-boundary structural: {compared} default-flags objects are byte-identical to --relocatable"
    );
    assert_eq!(compared, 12);
}

/// The derivation is keyed on a CALL to a function import and nothing else.
/// A module without an import, and a module whose import is declared but
/// never called (it references no external symbol), are still the
/// self-contained image on default flags.
#[test]
fn control_no_import_call_stays_a_self_contained_image() {
    let no_import = r#"(module (memory 1)
        (func $h (param i32) (result i32) local.get 0)
        (func (export "ld") (param i32) (result i32) local.get 0 call $h i32.load))"#;
    let never_called = r#"(module
        (import "env" "log" (func $log (param i32)))
        (memory 1)
        (func $h (param i32) (result i32) local.get 0)
        (func (export "ld") (param i32) (result i32) local.get 0 call $h i32.load))"#;
    for (name, wat) in [
        ("no import", no_import),
        ("import never called", never_called),
    ] {
        for target in ["cortex-m4", "cortex-m3", "cortex-m7dp"] {
            let (_, obj, default) = build(wat, target, false);
            let (_, rel, relocatable) = build(wat, target, true);
            assert!(!obj.relocatable, "{target} ({name}): became ET_REL");
            assert!(
                obj.relocs.iter().all(|r| r.target.is_some()),
                "{target} ({name}): an external relocation in a self-contained image"
            );
            assert!(rel.relocatable);
            assert!(default != relocatable);
        }
    }
}

// ------------------------------------------------------------ potency --

/// A hand-built Thumb object: `funcs` are laid out in order.
fn hand(funcs: &[(&str, &[u16])], relocs: Vec<TextReloc>) -> CompiledObject {
    let mut text = Vec::new();
    let mut syms = std::collections::BTreeMap::new();
    for (name, halves) in funcs {
        let offset = text.len() as u64;
        text.extend(halves.iter().flat_map(|h| h.to_le_bytes()));
        syms.insert(
            name.to_string(),
            FuncSym {
                offset,
                size: text.len() as u64 - offset,
                thumb: true,
                global: true,
            },
        );
    }
    CompiledObject {
        path: PathBuf::from("hand.o"),
        machine: Machine::Arm,
        text,
        funcs: syms,
        text_relocs: relocs.iter().map(|r| r.offset).collect(),
        relocs,
        relocatable: true,
        e_flags: 0,
    }
}

fn call_reloc(offset: u64, symbol: &str) -> TextReloc {
    TextReloc {
        offset,
        r_type: R_ARM_THM_CALL,
        symbol: symbol.to_string(),
        target: None,
    }
}

const BL: [u16; 2] = [0xF7FF, 0xFFFE];
const PUSH_R4_LR: u16 = 0xB510;
const POP_R4_PC: u16 = 0xBD10;
const MOV_R4_R0: u16 = 0x4604;
const MOV_R0_R4: u16 = 0x4620;
const BX_LR: u16 = 0x4770;

fn log_wasm() -> Vec<u8> {
    wat::parse_str(
        r#"(module (import "env" "log" (func $log (param i32)))
             (func (export "f") (param i32) (result i32)
               local.get 0 call $log local.get 0))"#,
    )
    .unwrap()
}

fn one(wasm: &[u8], obj: &CompiledObject, cfg: &HostConfig, arg: u32) -> HostedCase {
    run_hosted(wasm, obj, &[("f", &[i(arg)])], FUEL, &imports(), cfg)
        .unwrap()
        .remove(0)
}

/// The stub clobbers what AAPCS lets a callee clobber. Code that saves the
/// value in R4 agrees; the #1696 shape (`push; bl log; pop`) returns the
/// clobber and reds.
#[test]
fn potency_host_stub_clobbers_caller_saved_registers() {
    let wasm = log_wasm();
    let cfg = HostConfig::new(Cpu::CortexM4, LINMEM);
    let good = hand(
        &[(
            "f",
            &[PUSH_R4_LR, MOV_R4_R0, BL[0], BL[1], MOV_R0_R4, POP_R4_PC],
        )],
        vec![call_reloc(4, "log")],
    );
    let c = one(&wasm, &good, &cfg, 7);
    assert!(c.verdict.is_agree(), "{}", show(&c));
    assert_eq!(c.emu_calls.len(), 1);

    let bad = hand(
        &[("f", &[PUSH_R4_LR, BL[0], BL[1], POP_R4_PC])],
        vec![call_reloc(2, "log")],
    );
    let c = one(&wasm, &bad, &cfg, 7);
    assert_eq!(c.reference, RefOutcome::Values(vec![i(7)]));
    assert_eq!(c.emulator, EmuOutcome::Values(vec![i(CLOBBER)]));
    assert!(matches!(c.verdict, Verdict::Disagree(_)), "{}", show(&c));

    // A value parked in R1, R2, R3 or R12 across the call is clobbered too.
    for (reg, mov_to, mov_from) in [
        (1u32, 0x4601u16, 0x4608u16), // mov r1, r0 / mov r0, r1
        (2, 0x4602, 0x4610),
        (3, 0x4603, 0x4618),
        (12, 0x4684, 0x4660),
    ] {
        let parked = hand(
            &[(
                "f",
                &[PUSH_R4_LR, mov_to, BL[0], BL[1], mov_from, POP_R4_PC],
            )],
            vec![call_reloc(4, "log")],
        );
        let c = one(&wasm, &parked, &cfg, 7);
        assert_eq!(
            c.emulator,
            EmuOutcome::Values(vec![i(CLOBBER | reg)]),
            "R{reg}"
        );
        assert!(matches!(c.verdict, Verdict::Disagree(_)), "R{reg}");
    }
}

/// The right return value with the WRONG argument at the import is a
/// disagreement: the host calls are part of the verdict.
#[test]
fn potency_wrong_import_argument_reds_on_an_equal_result() {
    let wasm = log_wasm();
    let cfg = HostConfig::new(Cpu::CortexM4, LINMEM);
    let obj = hand(
        &[(
            "f",
            &[
                PUSH_R4_LR, MOV_R4_R0, 0x3001, /* adds r0, #1 */
                BL[0], BL[1], MOV_R0_R4, POP_R4_PC,
            ],
        )],
        vec![call_reloc(6, "log")],
    );
    let c = one(&wasm, &obj, &cfg, 7);
    assert_eq!(c.emulator, EmuOutcome::Values(vec![i(7)]));
    assert_eq!(c.emu_calls[0].args, vec![i(8)]);
    assert_eq!(c.ref_calls[0].args, vec![i(7)]);
    assert!(
        matches!(&c.verdict, Verdict::Disagree(m) if m.starts_with("host calls differ")),
        "{}",
        show(&c)
    );
    // A call the machine code never makes is the same disagreement.
    let silent = hand(&[("f", &[BX_LR])], vec![]);
    let c = one(&wasm, &silent, &cfg, 7);
    assert_eq!(c.emulator, EmuOutcome::Values(vec![i(7)]));
    assert!(matches!(&c.verdict, Verdict::Disagree(m) if m.starts_with("host calls differ")));
}

/// Linking is exact: a symbol that is not an import field is refused, as is
/// any relocation type other than `R_ARM_THM_CALL`, and an import with no
/// host function.
#[test]
fn potency_linking_refuses_what_no_contract_defines() {
    let wasm = log_wasm();
    let cfg = HostConfig::new(Cpu::CortexM4, LINMEM);
    let body: &[u16] = &[PUSH_R4_LR, MOV_R4_R0, BL[0], BL[1], MOV_R0_R4, POP_R4_PC];
    let link = |obj: &CompiledObject, imp: &Imports, cfg: &HostConfig| {
        Hosted::link(obj, &wasm, imp, cfg).err()
    };

    let dispatch = hand(
        &[("f", body)],
        vec![call_reloc(4, "__meld_dispatch_import")],
    );
    assert_eq!(
        link(&dispatch, &imports(), &cfg),
        Some(EmuError::UnresolvedSymbol("__meld_dispatch_import".into()))
    );
    // `env::log` is not the symbol `env_log` or `func_0`.
    for near in ["env_log", "func_0", "Log", ""] {
        let o = hand(&[("f", body)], vec![call_reloc(4, near)]);
        assert_eq!(
            link(&o, &imports(), &cfg),
            Some(EmuError::UnresolvedSymbol(near.into())),
            "{near:?}"
        );
    }
    // A raw stub makes the same object linkable, and sees the registers.
    let raw = cfg
        .clone()
        .raw_symbol("__meld_dispatch_import", |r| r[0] ^ 0xFFFF);
    let mut image = Hosted::link(&dispatch, &wasm, &imports(), &raw).unwrap();
    let run = image.call("f", &[i(7)]).unwrap();
    assert_eq!(run.calls.len(), 1);
    assert_eq!(run.calls[0].field, "__meld_dispatch_import");
    assert_eq!(run.calls[0].args[0], i(7));
    assert_eq!(run.outcome, EmuOutcome::Values(vec![i(7)]));

    let mut abs = call_reloc(4, "log");
    abs.r_type = 2; // R_ARM_ABS32
    let o = hand(&[("f", body)], vec![abs]);
    assert!(matches!(
        link(&o, &imports(), &cfg),
        Some(EmuError::Reloc(_))
    ));
    // A relocation on bytes that are not a BL.
    let o = hand(&[("f", body)], vec![call_reloc(0, "log")]);
    assert!(matches!(
        link(&o, &imports(), &cfg),
        Some(EmuError::Reloc(_))
    ));
    // The import exists in the module but the test serves no host function.
    let o = hand(&[("f", body)], vec![call_reloc(4, "log")]);
    assert!(matches!(
        link(&o, &Imports::new(), &cfg),
        Some(EmuError::UnresolvedSymbol(_))
    ));
    // Two imports sharing a field name cannot be told apart by the symbol.
    let twins = wat::parse_str(
        r#"(module (import "a" "log" (func (param i32))) (import "b" "log" (func (param i32)))
             (func (export "f") (param i32) (result i32) local.get 0))"#,
    )
    .unwrap();
    let both = Imports::new()
        .trace("a", "log", vec![])
        .trace("b", "log", vec![]);
    assert_eq!(
        Hosted::link(&o, &twins, &both, &cfg).err(),
        Some(EmuError::UnresolvedSymbol("log".into()))
    );
}

/// R9/R10/R11 are the embedder's: machine code that writes one is ILLEGAL
/// even when its result is right. So is a clobbered callee-saved register.
#[test]
fn potency_embedder_registers_are_checked() {
    let wasm =
        wat::parse_str(r#"(module (func (export "f") (param i32) (result i32) local.get 0))"#)
            .unwrap();
    let cfg = HostConfig::new(Cpu::CortexM4, LINMEM);
    for (name, mov) in [
        ("R9", 0x4681u16), // mov r9, r0
        ("R10", 0x4682),
        ("R11", 0x4683),
        ("R6", 0x4606),
    ] {
        let o = hand(&[("f", &[mov, BX_LR])], vec![]);
        let c = one(&wasm, &o, &cfg, 7);
        assert!(
            matches!(&c.emulator, EmuOutcome::Illegal { reason, .. } if reason.contains(name)),
            "{name}: {}",
            show(&c)
        );
        assert!(!c.verdict.is_agree(), "{name}");
    }
    let ok = hand(&[("f", &[BX_LR])], vec![]);
    assert!(one(&wasm, &ok, &cfg, 7).verdict.is_agree());
}

/// Linear memory is where the embedder put it, and it persists across the
/// calls of a sequence. R11-relative code agrees wherever memory is; the
/// #1758 shape (an absolute 0x2000_0100 base) reads board SRAM instead and
/// reds, or faults when nothing is mapped there.
#[test]
fn potency_linear_memory_is_r11_relative_and_persistent() {
    let wasm = wat::parse_str(
        r#"(module (memory 1)
             (func (export "st") (param i32 i32) local.get 0 local.get 1 i32.store)
             (func (export "ld") (param i32) (result i32) local.get 0 i32.load))"#,
    )
    .unwrap();
    let st: &[u16] = &[0xF84B, 0x1000, BX_LR]; // str.w r1, [fp, r0]
    let ld: &[u16] = &[0xF85B, 0x0000, BX_LR]; // ldr.w r0, [fp, r0]
    // movw ip, #0x100; movt ip, #0x2000; add ip, r0; ldr.w r0, [ip]
    let ld_abs: &[u16] = &[
        0xF240, 0x1C00, 0xF2C2, 0x0C00, 0x4484, 0xF8DC, 0x0000, BX_LR,
    ];
    let a8 = [i(8)];
    let a8_42 = [i(8), i(42)];
    let steps: &[(&str, &[WasmValue])] = &[("st", &a8_42), ("ld", &a8)];

    for base in [LINMEM, LINMEM_FAR] {
        let cfg = HostConfig::new(Cpu::CortexM4, base).ram(SRAM.0, SRAM.1);
        let good = hand(&[("st", st), ("ld", ld)], vec![]);
        let cases = run_hosted(&wasm, &good, steps, FUEL, &imports(), &cfg).unwrap();
        assert_eq!(cases.len(), 2);
        assert!(cases.iter().all(|c| c.verdict.is_agree()), "{base:#x}");
        assert_eq!(cases[1].emulator, EmuOutcome::Values(vec![i(42)]));
        // A fresh image does not see the previous image's store.
        let mut fresh = Hosted::link(&good, &wasm, &imports(), &cfg).unwrap();
        assert_eq!(
            fresh.call("ld", &a8).unwrap().outcome,
            EmuOutcome::Values(vec![i(0)])
        );

        let mixed = hand(&[("st", st), ("ld", ld_abs)], vec![]);
        let cases = run_hosted(&wasm, &mixed, steps, FUEL, &imports(), &cfg).unwrap();
        assert_eq!(cases[1].reference, RefOutcome::Values(vec![i(42)]));
        assert_eq!(cases[1].emulator, EmuOutcome::Values(vec![i(0)]));
        assert!(matches!(cases[1].verdict, Verdict::Disagree(_)));
    }
    // Without SRAM mapped, the absolute access is a fault, never a value.
    let cfg = HostConfig::new(Cpu::CortexM4, LINMEM_FAR);
    let mixed = hand(&[("st", st), ("ld", ld_abs)], vec![]);
    let cases = run_hosted(&wasm, &mixed, steps, FUEL, &imports(), &cfg).unwrap();
    assert!(matches!(cases[1].emulator, EmuOutcome::Illegal { .. }));
    assert!(!cases[1].verdict.is_agree());
    // An access past the end of linear memory faults too: nothing is mapped
    // behind it.
    let good = hand(&[("st", st), ("ld", ld)], vec![]);
    let mut image = Hosted::link(&good, &wasm, &imports(), &cfg).unwrap();
    assert!(matches!(
        image.call("ld", &[i(0x1_0000)]).unwrap().outcome,
        EmuOutcome::Illegal { .. }
    ));
}

/// State the harness does not write is refused, not read as zeros.
#[test]
fn potency_uninstantiated_state_is_refused() {
    let cfg = HostConfig::new(Cpu::CortexM4, LINMEM);
    let o = hand(&[("f", &[BX_LR])], vec![]);
    for (wat, what) in [
        (
            r#"(module (global (mut i32) (i32.const 1))
                 (func (export "f") (param i32) (result i32) local.get 0))"#,
            "a global",
        ),
        (
            r#"(module (memory 1) (data (i32.const 0) "x")
                 (func (export "f") (param i32) (result i32) local.get 0))"#,
            "a data segment",
        ),
    ] {
        let wasm = wat::parse_str(wat).unwrap();
        let e = run_hosted(&wasm, &o, &[("f", &[i(1)])], FUEL, &imports(), &cfg).unwrap_err();
        assert!(
            matches!(e, CaseError::Emulator(EmuError::Uninstantiated(w)) if w == what),
            "{what}"
        );
    }
    // RV32 objects and cores are not hosted.
    let wasm =
        wat::parse_str(r#"(module (func (export "f") (param i32) (result i32) local.get 0))"#)
            .unwrap();
    let rv = HostConfig::new(Cpu::Rv32Imac, LINMEM);
    assert!(matches!(
        Hosted::link(&o, &wasm, &imports(), &rv).err(),
        Some(EmuError::WrongMachine { .. })
    ));
}
