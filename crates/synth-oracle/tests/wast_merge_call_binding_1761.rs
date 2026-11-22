//! Refs #1761: on a multi-module `.wast`, a call binds to the function its
//! OWN module means.
//!
//! synth merges the modules of a `.wast` into one object with one `func_N`
//! label space. Each module still has its own function index space: index 0
//! is import 0 in a module with an import, and the first defined function in
//! a module with none. The ARM relocatable ELF builder mapped the label
//! `func_N` to the field name of import N of the MERGED import table (the
//! table of the module with the most imports) for every call site, so the
//! recursive `call 0` of an import-free module was relocated against another
//! module's import: `bl g0`, with the object defining `func_0` at the very
//! address the call meant. Exit 0.
//!
//! Three checks, on five fixtures:
//!
//! - EXECUTION (ARM). The object is linked against host stubs and run under
//!   unicorn on cortex-m4 (default flags and `--relocatable`) and cortex-m3.
//!   The reference is kiln running a single module with the same functions
//!   and imports (the "union" module): the merged modules share no state, so
//!   each export must compute what it computes there, with the same host
//!   calls in the same order.
//! - STRUCTURE (ARM, RV32, AArch64). Every call relocation of every function
//!   is read from the relocation and symbol tables and must name the callee
//!   its module means: a symbol defined at the callee's address, or the
//!   undefined symbol of the import's field.
//! - AArch64 does not lower an import call on the `.wast` merge and must say
//!   so (a refusal, exit 1); the fixture that calls no import compiles and
//!   its calls are checked structurally.
//!
//! RV32 was right before the fix (its builder let a defined function shadow
//! the import label); it now takes the same per-call-site rule. The twin
//! check found no defect there and none on AArch64.
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary; with a
//! pre-fix one 53 of the 98 execution steps fail (39 return another
//! module's import's result or make its host call; 14 cannot be linked,
//! because the object references an import that no module calls) and 20 of
//! the 47 call sites are bound to another module's import, all on ARM.

#![cfg(feature = "exec")]

use std::path::PathBuf;

use synth_oracle::emulate::Cpu;
use synth_oracle::hosted::HostConfig;
use synth_oracle::reference::Imports;
use synth_oracle::run_hosted;
use synth_oracle::synth::{CompiledObject, TextReloc, compile};
use synth_oracle::value::WasmValue;

const FUEL: u64 = 100_000;
/// R11 for the hosted image. No fixture has a memory; the address is unused.
const LINMEM: u32 = 0x2000_0000;

/// What a call site must be bound to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Callee {
    /// A function this object defines, named by one of its symbols.
    Local(&'static str),
    /// An import: the undefined symbol of its bare field name.
    Import(&'static str),
}
use Callee::{Import, Local};

struct Fixture {
    name: &'static str,
    /// The multi-module input.
    wast: &'static str,
    /// ONE module with the same exports and imports: the reference.
    union: &'static str,
    /// `(export, arguments)`; each runs on a fresh image and instance.
    steps: &'static [(&'static str, &'static [u32])],
    /// Per function (by an exported or `func_N` symbol), its call sites in
    /// code order.
    binding: &'static [(&'static str, &'static [Callee])],
    /// Some export calls an import, so default ARM flags produce the
    /// host-linked object too.
    calls_an_import: bool,
}

macro_rules! steps {
    ($($e:literal: $($a:literal),+;)+) => { &[$($(($e, &[$a])),+),+] };
}

const FIXTURES: &[Fixture] = &[
    // The issue: an import-free module calls its own function 0; the other
    // module's import 0 is `g0`.
    Fixture {
        name: "issue",
        wast: r#"
(module
  (func (export "a") (param i32) (result i32)
    (if (result i32) (i32.eqz (local.get 0))
      (then (i32.const 7))
      (else (call 0 (i32.sub (local.get 0) (i32.const 1)))))))
(module
  (import "env" "g0" (func $g0 (param i32) (result i32)))
  (import "env" "g1" (func $g1 (param i32) (result i32)))
  (func (export "b") (param i32) (result i32) (call $g1 (local.get 0))))"#,
        union: UNION_ISSUE,
        steps: steps!("a": 0, 1, 2, 5; "b": 0, 3, 0xFFFF_FFFF;),
        binding: &[("a", &[Local("a")]), ("b", &[Import("g1")])],
        calls_an_import: true,
    },
    // The same two modules in the other order: the merged table is chosen
    // by import count, not by position.
    Fixture {
        name: "issue-reversed",
        wast: r#"
(module
  (import "env" "g0" (func $g0 (param i32) (result i32)))
  (import "env" "g1" (func $g1 (param i32) (result i32)))
  (func (export "b") (param i32) (result i32) (call $g1 (local.get 0))))
(module
  (func (export "a") (param i32) (result i32)
    (if (result i32) (i32.eqz (local.get 0))
      (then (i32.const 7))
      (else (call 0 (i32.sub (local.get 0) (i32.const 1)))))))"#,
        union: UNION_ISSUE,
        steps: steps!("a": 0, 1, 2, 5; "b": 0, 3, 0xFFFF_FFFF;),
        binding: &[("a", &[Local("a")]), ("b", &[Import("g1")])],
        calls_an_import: true,
    },
    // Both modules import, with different counts. Module 1 has one import,
    // so its function 1 is DEFINED; the merged table has an import 1 (`g1`).
    // Module 1 also calls its import 0, which both modules agree on.
    Fixture {
        name: "fewer-imports",
        wast: r#"
(module
  (import "env" "g0" (func $g0 (param i32) (result i32)))
  (func (export "a") (param i32) (result i32)
    (if (result i32) (i32.eqz (local.get 0))
      (then (call $g0 (i32.const 40)))
      (else (call 1 (i32.sub (local.get 0) (i32.const 1)))))))
(module
  (import "env" "g0" (func $g0 (param i32) (result i32)))
  (import "env" "g1" (func $g1 (param i32) (result i32)))
  (func (export "b") (param i32) (result i32) (call $g0 (local.get 0))))"#,
        union: r#"(module
  (import "env" "g0" (func $g0 (param i32) (result i32)))
  (import "env" "g1" (func $g1 (param i32) (result i32)))
  (func $a (export "a") (param i32) (result i32)
    (if (result i32) (i32.eqz (local.get 0))
      (then (call $g0 (i32.const 40)))
      (else (call $a (i32.sub (local.get 0) (i32.const 1))))))
  (func (export "b") (param i32) (result i32) (call $g0 (local.get 0))))"#,
        steps: steps!("a": 0, 1, 2, 5; "b": 0, 3, 0xFFFF_FFFF;),
        binding: &[("a", &[Import("g0"), Local("a")]), ("b", &[Import("g0")])],
        calls_an_import: true,
    },
    // A non-exported callee at index 1, called twice (one call feeding the
    // other), beside a self-call at index 0; the other module's imports 0
    // and 1 are `g0` and `g1`.
    Fixture {
        name: "internal-callee",
        wast: r#"
(module
  (func (export "a") (param i32) (result i32)
    (if (result i32) (i32.gt_u (local.get 0) (i32.const 3))
      (then (call 0 (i32.const 3)))
      (else (call 1 (call 1 (local.get 0))))))
  (func (param i32) (result i32) (i32.mul (local.get 0) (i32.const 3))))
(module
  (import "env" "g0" (func $g0 (param i32) (result i32)))
  (import "env" "g1" (func $g1 (param i32) (result i32)))
  (import "env" "g2" (func $g2 (param i32) (result i32)))
  (func (export "b") (param i32) (result i32) (call $g2 (local.get 0))))"#,
        union: r#"(module
  (import "env" "g0" (func $g0 (param i32) (result i32)))
  (import "env" "g1" (func $g1 (param i32) (result i32)))
  (import "env" "g2" (func $g2 (param i32) (result i32)))
  (func $a (export "a") (param i32) (result i32)
    (if (result i32) (i32.gt_u (local.get 0) (i32.const 3))
      (then (call $a (i32.const 3)))
      (else (call $h (call $h (local.get 0))))))
  (func $h (param i32) (result i32) (i32.mul (local.get 0) (i32.const 3)))
  (func (export "b") (param i32) (result i32) (call $g2 (local.get 0))))"#,
        steps: steps!("a": 0, 1, 2, 5; "b": 0, 3, 0xFFFF_FFFF;),
        binding: &[
            ("a", &[Local("a"), Local("func_1"), Local("func_1")]),
            ("b", &[Import("g2")]),
        ],
        calls_an_import: true,
    },
    // The other module DECLARES imports and calls none. No call in the
    // object is an import call, so AArch64 compiles this one too.
    Fixture {
        name: "imports-not-called",
        wast: r#"
(module
  (func (export "a") (param i32) (result i32)
    (if (result i32) (i32.eqz (local.get 0))
      (then (i32.const 7))
      (else (call 0 (i32.sub (local.get 0) (i32.const 1)))))))
(module
  (import "env" "g0" (func $g0 (param i32) (result i32)))
  (import "env" "g1" (func $g1 (param i32) (result i32)))
  (func (export "b") (param i32) (result i32) (i32.add (local.get 0) (i32.const 1))))"#,
        union: r#"(module
  (func $a (export "a") (param i32) (result i32)
    (if (result i32) (i32.eqz (local.get 0))
      (then (i32.const 7))
      (else (call $a (i32.sub (local.get 0) (i32.const 1))))))
  (func (export "b") (param i32) (result i32) (i32.add (local.get 0) (i32.const 1))))"#,
        steps: steps!("a": 0, 1, 2, 5; "b": 0, 3, 0xFFFF_FFFF;),
        binding: &[("a", &[Local("a")]), ("b", &[])],
        calls_an_import: false,
    },
];

/// The union of the issue's two modules.
const UNION_ISSUE: &str = r#"(module
  (import "env" "g0" (func $g0 (param i32) (result i32)))
  (import "env" "g1" (func $g1 (param i32) (result i32)))
  (func $a (export "a") (param i32) (result i32)
    (if (result i32) (i32.eqz (local.get 0))
      (then (i32.const 7))
      (else (call $a (i32.sub (local.get 0) (i32.const 1))))))
  (func (export "b") (param i32) (result i32) (call $g1 (local.get 0))))"#;

/// Three host functions with three different results, so a call bound to
/// the wrong one cannot return the right value.
fn imports() -> Imports {
    let one = |f: fn(u32) -> u32| {
        move |a: &[WasmValue]| match a {
            [WasmValue::I32(x)] => Ok(vec![WasmValue::I32(f(*x))]),
            _ => Err(format!("bad args {a:?}")),
        }
    };
    Imports::new()
        .func("env", "g0", one(|x| x.wrapping_add(100)))
        .func("env", "g1", one(|x| x.wrapping_mul(2).wrapping_add(1)))
        .func("env", "g2", one(|x| x ^ 0x55))
}

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("wast-merge-1761-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// Compile `text` saved as `m.<ext>`. `Err` is synth's stderr on a refusal.
fn build(text: &str, ext: &str, flags: &[&str]) -> Result<CompiledObject, String> {
    let dir = scratch();
    let input = dir.join(format!("m.{ext}"));
    std::fs::write(&input, text).unwrap();
    let run = compile(&input, flags, &dir.join("m.o")).expect("synth runs");
    if !run.status.success() {
        return Err(run.stderr);
    }
    Ok(run.object.expect("object parsed"))
}

/// The call relocations inside `func`, in code order.
fn call_sites<'a>(obj: &'a CompiledObject, func: &str) -> Result<Vec<&'a TextReloc>, String> {
    let f = obj
        .func(func)
        .ok_or_else(|| format!("no symbol `{func}`"))?;
    let mut sites: Vec<&TextReloc> = obj
        .relocs
        .iter()
        .filter(|r| r.offset >= f.offset && r.offset < f.offset + f.size)
        .collect();
    sites.sort_by_key(|r| r.offset);
    Ok(sites)
}

/// Every call site of every function of `fx` is bound to the callee its
/// module means. Returns how many sites were checked, or what was wrong.
fn check_binding(obj: &CompiledObject, fx: &Fixture) -> Result<usize, Vec<String>> {
    let mut bad = Vec::new();
    let mut checked = 0;
    for (func, want) in fx.binding {
        let sites = match call_sites(obj, func) {
            Ok(s) => s,
            Err(e) => {
                bad.push(format!("`{func}`: {e}"));
                continue;
            }
        };
        if sites.len() != want.len() {
            bad.push(format!(
                "`{func}`: {} call relocation(s), expected {}",
                sites.len(),
                want.len()
            ));
            continue;
        }
        for (site, want) in sites.iter().zip(want.iter()) {
            checked += 1;
            let ok = match want {
                Callee::Local(name) => obj
                    .func(name)
                    .is_some_and(|c| site.target == Some(c.offset)),
                Callee::Import(field) => site.target.is_none() && site.symbol == *field,
            };
            if !ok {
                bad.push(format!(
                    "`{func}`+{:#x}: bound to `{}` ({}), expected {want:?}",
                    site.offset,
                    site.symbol,
                    match site.target {
                        Some(t) => format!("defined at .text+{t:#x}"),
                        None => "undefined".to_string(),
                    }
                ));
            }
        }
    }
    if bad.is_empty() {
        Ok(checked)
    } else {
        Err(bad)
    }
}

/// Run each step of `fx` on its own hosted image of `obj` and its own kiln
/// instance of the union module. Returns `(steps, host calls)` that agreed,
/// and every disagreement.
fn run_steps(
    what: &str,
    obj: &CompiledObject,
    fx: &Fixture,
    cpu: Cpu,
) -> (usize, usize, Vec<String>) {
    let reference =
        wat::parse_str(fx.union).unwrap_or_else(|e| panic!("{}: union WAT: {e}", fx.name));
    let cfg = HostConfig::new(cpu, LINMEM);
    let (mut agree, mut calls, mut bad) = (0, 0, Vec::new());
    for (export, args) in fx.steps {
        let args: Vec<WasmValue> = args.iter().map(|&a| WasmValue::I32(a)).collect();
        match run_hosted(
            &reference,
            obj,
            &[(*export, &args[..])],
            FUEL,
            &imports(),
            &cfg,
        ) {
            Ok(cases) if cases.len() == 1 && cases[0].verdict.is_agree() => {
                agree += 1;
                calls += cases[0].emu_calls.len();
            }
            Ok(cases) => bad.push(match cases.first() {
                Some(c) => format!(
                    "{what} {export}{args:?}: kiln {:?} calls {:?} | machine code {:?} calls {:?}",
                    c.reference, c.ref_calls, c.emulator, c.emu_calls
                ),
                None => format!("{what} {export}{args:?}: did not run"),
            }),
            Err(e) => bad.push(format!("{what} {export}{args:?}: harness error {e:?}")),
        }
    }
    (agree, calls, bad)
}

struct ArmLeg {
    name: &'static str,
    cpu: Cpu,
    flags: &'static [&'static str],
    /// Default flags: only a fixture that calls an import is host-linked.
    default_flags: bool,
}

const ARM_LEGS: &[ArmLeg] = &[
    ArmLeg {
        name: "m4-relocatable",
        cpu: Cpu::CortexM4,
        flags: &["--target", "cortex-m4", "--relocatable", "--all-exports"],
        default_flags: false,
    },
    ArmLeg {
        name: "m3-relocatable",
        cpu: Cpu::CortexM3,
        flags: &["--target", "cortex-m3", "--relocatable", "--all-exports"],
        default_flags: false,
    },
    ArmLeg {
        name: "m4-default",
        cpu: Cpu::CortexM4,
        flags: &["--target", "cortex-m4", "--all-exports"],
        default_flags: true,
    },
];

const RV32: &[&str] = &[
    "-b",
    "riscv",
    "--target",
    "riscv32imac",
    "--relocatable",
    "--all-exports",
];
const A64: &[&str] = &["-b", "aarch64", "--relocatable", "--all-exports"];

fn arm_runs(leg: &ArmLeg, fx: &Fixture) -> bool {
    !leg.default_flags || fx.calls_an_import
}

#[test]
fn merged_modules_execute_like_their_own_module() {
    let (mut steps, mut total, mut calls, mut objects) = (0, 0, 0, 0);
    let mut bad: Vec<String> = Vec::new();
    for fx in FIXTURES {
        for leg in ARM_LEGS.iter().filter(|l| arm_runs(l, fx)) {
            let what = format!("{}/{}", fx.name, leg.name);
            total += fx.steps.len();
            objects += 1;
            let obj = match build(fx.wast, "wast", leg.flags) {
                Ok(o) => o,
                Err(e) => {
                    bad.push(format!("{what}: synth refused: {e}"));
                    continue;
                }
            };
            assert!(obj.relocatable, "{what}: not a host-linked object");
            let (a, c, b) = run_steps(&what, &obj, fx, leg.cpu);
            eprintln!(
                "ORACLE wast-merge-1761 [{what}]: {} of {} steps wrong",
                b.len(),
                fx.steps.len()
            );
            steps += a;
            calls += c;
            bad.extend(b);
        }
    }
    for b in &bad {
        eprintln!("  WRONG {b}");
    }
    // EXACT literals: 5 fixtures x 7 steps on the two --relocatable legs,
    // 4 of them on the default-flags leg.
    assert_eq!((total, objects), (98, 14), "step or object count moved");
    assert!(
        bad.is_empty(),
        "{} of {total} steps disagree with kiln",
        bad.len()
    );
    assert_eq!(steps, total);
    eprintln!(
        "ORACLE wast-merge-1761 execution: {steps} steps agree across {objects} objects, {calls} host calls matched"
    );
}

#[test]
fn every_call_site_is_bound_within_its_own_module() {
    let (mut sites, mut objects) = (0, 0);
    let mut bad: Vec<String> = Vec::new();
    let mut legs: Vec<(&str, &[&str])> = ARM_LEGS.iter().map(|l| (l.name, l.flags)).collect();
    legs.push(("rv32imac", RV32));
    for fx in FIXTURES {
        for (leg, flags) in &legs {
            let what = format!("{}/{leg}", fx.name);
            objects += 1;
            let obj = match build(fx.wast, "wast", flags) {
                Ok(o) => o,
                Err(e) => {
                    bad.push(format!("{what}: synth refused: {e}"));
                    continue;
                }
            };
            // On default flags a fixture with no import call is a
            // self-contained image: its calls are patched in place and carry
            // no relocation to read.
            if !obj.relocatable {
                assert!(
                    *leg == "m4-default" && !fx.calls_an_import,
                    "{what}: unexpectedly self-contained"
                );
                assert!(obj.relocs.is_empty(), "{what}: relocations in an image");
                continue;
            }
            match check_binding(&obj, fx) {
                Ok(n) => sites += n,
                Err(b) => bad.extend(b.into_iter().map(|b| format!("{what}: {b}"))),
            }
        }
    }
    for b in &bad {
        eprintln!("  WRONG {b}");
    }
    assert!(
        bad.is_empty(),
        "{} call site(s) bound outside their module",
        bad.len()
    );
    // 12 call sites over the five fixtures (2, 2, 3, 4, 1) on the three
    // host-linked legs, and 11 on the default-flags leg, where the fixture
    // with no import call is a self-contained image.
    assert_eq!(
        (sites, objects),
        (47, 20),
        "call-site or object count moved"
    );
    eprintln!(
        "ORACLE wast-merge-1761 structure: {sites} call sites bound to their own module across {objects} objects"
    );
}

/// AArch64 lowers no import call on the `.wast` merge (the merge hands it no
/// import table) and refuses, loudly. The one fixture without an import call
/// compiles, and its call is bound to its own function.
#[test]
fn a64_refuses_an_import_call_and_binds_the_rest() {
    let (mut refused, mut bound) = (0, 0);
    for fx in FIXTURES {
        match build(fx.wast, "wast", A64) {
            Err(e) => {
                assert!(
                    fx.calls_an_import,
                    "{}: refused, though it calls no import: {e}",
                    fx.name
                );
                assert!(
                    e.contains("which this object does not place"),
                    "{}: refused for another reason: {e}",
                    fx.name
                );
                refused += 1;
            }
            Ok(obj) => {
                assert!(
                    !fx.calls_an_import,
                    "{}: an import call compiled on the A64 .wast merge",
                    fx.name
                );
                let n = check_binding(&obj, fx).unwrap_or_else(|b| {
                    panic!("{}: {}", fx.name, b.join("; "));
                });
                bound += n;
            }
        }
    }
    assert_eq!((refused, bound), (4, 1), "A64 outcome moved");
    eprintln!(
        "ORACLE wast-merge-1761 a64: {refused} fixtures with an import call refused, {bound} call site bound in the fixture without one"
    );
}

/// CONTROL: a single module has one index space, so the label rewrite is
/// right there by construction. Each union module, compiled alone, executes
/// like kiln and has the bindings its fixture expects.
#[test]
fn control_single_module_input_was_never_affected() {
    let (mut steps, mut sites) = (0, 0);
    for fx in FIXTURES.iter().filter(|f| f.calls_an_import) {
        let leg = &ARM_LEGS[0];
        let obj = build(fx.union, "wat", leg.flags).unwrap_or_else(|e| panic!("{}: {e}", fx.name));
        let (a, _, bad) = run_steps(fx.name, &obj, fx, leg.cpu);
        assert!(bad.is_empty(), "{}:\n{}", fx.name, bad.join("\n"));
        steps += a;
        // In the union module the internal callee of `internal-callee` is
        // function 4, not 1: check the import bindings only.
        for (func, want) in fx.binding {
            let got = call_sites(&obj, func).unwrap();
            assert_eq!(got.len(), want.len(), "{} `{func}`", fx.name);
            for (site, want) in got.iter().zip(want.iter()) {
                match want {
                    Callee::Import(field) => {
                        assert!(site.target.is_none() && site.symbol == *field, "{site:?}");
                        sites += 1;
                    }
                    Callee::Local(_) => assert!(site.target.is_some(), "{site:?}"),
                }
            }
        }
    }
    assert_eq!((steps, sites), (28, 5), "control count moved");
    eprintln!(
        "ORACLE wast-merge-1761 control: {steps} steps agree and {sites} import call sites are bound on single-module input"
    );
}

/// POTENCY: both checks see the defect. Take the issue's object as the fixed
/// compiler emits it and rebind the recursive call in `a` to the undefined
/// symbol `g0`, which is the relocation main 6641efec emitted.
#[test]
fn potency_a_call_rebound_to_the_import_is_judged_wrong() {
    let fx = &FIXTURES[0];
    let leg = &ARM_LEGS[0];
    let mut obj = build(fx.wast, "wast", leg.flags).expect("compiles");
    assert_eq!(check_binding(&obj, fx), Ok(2));
    let a = obj.func("a").unwrap().clone();
    let site = obj
        .relocs
        .iter_mut()
        .find(|r| r.offset >= a.offset && r.offset < a.offset + a.size)
        .expect("`a` has a call");
    site.symbol = "g0".to_string();
    site.target = None;

    let bad = check_binding(&obj, fx).unwrap_err();
    assert_eq!(bad.len(), 1, "{bad:?}");
    assert!(bad[0].contains("bound to `g0` (undefined)"), "{bad:?}");

    // a(0) makes no call and still agrees; a(n > 0) returns g0(n - 1).
    let (agree, _, wrong) = run_steps("rebound", &obj, fx, leg.cpu);
    assert_eq!((agree, wrong.len()), (4, 3), "{wrong:?}");
    assert!(wrong.iter().all(|w| w.contains(" a[")), "{wrong:?}");
    assert!(
        wrong[0].contains("field: \"g0\"") && wrong[0].contains("0x00000064"),
        "a(1) = g0(0) = 100: {}",
        wrong[0]
    );
}
