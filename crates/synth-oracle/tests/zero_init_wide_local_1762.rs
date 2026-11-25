//! Refs #1762: a local that is read and never written is as wide as its
//! DECLARATION says, on RV32 as on ARM.
//!
//! The RV32 selector learned a local's width only from a store into it. For
//! `(local i64) local.get 1` there is no store, so the local got a 4-byte
//! slot, `local.get` pushed one register, and the function returned with a1
//! (the high word of the result) never written: `f(5)` returned whatever a1
//! held at entry, shifted into the high word. Where an i64 operator consumed
//! the local, the same gap was a refusal ("expected i64, found i32").
//!
//! Every shape below runs on kiln (the reference) and, as the machine code
//! synth emitted, under unicorn on:
//!
//! - rv32imac `--relocatable` (the backend the issue is about);
//! - cortex-m4 and cortex-m3 `--relocatable` (the ARM direct selector);
//! - cortex-m4 default flags and `--no-optimize`.
//!
//! The ARM legs are the twin check: ARM reads the declared widths (#1214)
//! and was right on every shape here before the fix.
//!
//! The emulator poisons every argument register no argument occupies, so a
//! high word that nothing writes is `0xFEEDFACE`, never wasm's zero.
//!
//! An f64 local has the same 8-byte width and the same defect. No float
//! signature runs on the RV32 leg (the harness refuses them), so the f64
//! shape is pinned structurally: its code is byte-identical to the executed
//! i64 twin's.
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary; with a
//! pre-fix one the RV32 leg reds on 44 of its 60 cases: 7 shapes return
//! `0xFEEDFACE` in the high word (28 cases) and 4 shapes are refused (16).

#![cfg(feature = "exec")]

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use synth_oracle::compare::{EmuOutcome, RefOutcome, Verdict};
use synth_oracle::emulate::{Cpu, EmuConfig};
use synth_oracle::reference::Imports;
use synth_oracle::synth::{CompiledObject, FuncSym, Machine, compile};
use synth_oracle::value::WasmValue;
use synth_oracle::{Case, run_case};

const FUEL: u64 = 100_000;

/// One function `(param i32) (result <result>) <locals> <body>`. Local 0 is
/// the parameter; the declared locals start at index 1.
struct Shape {
    name: &'static str,
    result: &'static str,
    locals: &'static str,
    body: &'static str,
}

const fn s(
    name: &'static str,
    result: &'static str,
    locals: &'static str,
    body: &'static str,
) -> Shape {
    Shape {
        name,
        result,
        locals,
        body,
    }
}

const SHAPES: &[Shape] = &[
    // The issue.
    s("ret", "i64", "(local i64)", "local.get 1"),
    // Read after other code has run and written a neighbouring local.
    s(
        "after_code",
        "i64",
        "(local i32 i64)",
        "(local.set 1 (i32.mul (local.get 0) (i32.const 3)))
         (local.set 1 (i32.add (local.get 1) (i32.const 7)))
         local.get 2",
    ),
    // Both neighbours hold all-ones: the 8-byte slot must not share a word.
    s(
        "between_neighbours",
        "i64",
        "(local i32 i64 i32)",
        "(local.set 1 (i32.const -1)) (local.set 3 (i32.const -1)) local.get 2",
    ),
    // A never-written local copied into another, then read.
    s(
        "copy",
        "i64",
        "(local i64 i64)",
        "local.get 2 local.set 1 local.get 1",
    ),
    s(
        "tee",
        "i64",
        "(local i64 i64)",
        "local.get 2 local.tee 1 drop local.get 1",
    ),
    // Written on one path only.
    s(
        "cond_written",
        "i64",
        "(local i64)",
        "(if (local.get 0) (then (local.set 1 (i64.const 0x100000005)))) local.get 1",
    ),
    s(
        "drop_then_get",
        "i64",
        "(local i64)",
        "local.get 1 drop local.get 1",
    ),
    s(
        "block_result",
        "i64",
        "(local i64)",
        "(block (result i64) local.get 1)",
    ),
    s(
        "select_one_written",
        "i64",
        "(local i64 i64)",
        "(local.set 2 (i64.const 0x700000009))
         (select (local.get 1) (local.get 2) (local.get 0))",
    ),
    // An i64 operator consumes the never-written local. Pre-fix RV32 refused
    // these three ("stack type mismatch ... expected i64, found i32").
    s(
        "add",
        "i64",
        "(local i64)",
        "(i64.add (local.get 1) (i64.extend_i32_u (local.get 0)))",
    ),
    s("eqz", "i32", "(local i64)", "(i64.eqz (local.get 1))"),
    s(
        "high_word",
        "i32",
        "(local i64)",
        "(i32.wrap_i64 (i64.shr_u (local.get 1) (i64.const 32)))",
    ),
    // Read before written inside a loop, then written: the dataflow inference
    // already saw this one.
    s(
        "loop_accumulate",
        "i64",
        "(local i64 i32)",
        "(local.set 2 (i32.and (local.get 0) (i32.const 7)))
         (block (loop
           (br_if 1 (i32.eqz (local.get 2)))
           (local.set 1 (i64.add (local.get 1) (i64.const 0x100000001)))
           (local.set 2 (i32.sub (local.get 2) (i32.const 1)))
           (br 0)))
         local.get 1",
    ),
    // The i32 controls.
    s("i32_ret", "i32", "(local i32)", "local.get 1"),
    s(
        "i32_after_code",
        "i32",
        "(local i64 i32)",
        "(local.set 1 (i64.const -1)) local.get 2",
    ),
];

const ARGS: &[u32] = &[0, 1, 5, 0xFFFF_FFFF];

fn module_of(shapes: &[&Shape]) -> Vec<u8> {
    let mut wat = String::from("(module\n");
    for s in shapes {
        wat.push_str(&format!(
            "(func (export \"{}\") (param i32) (result {}) {}\n{})\n",
            s.name, s.result, s.locals, s.body
        ));
    }
    wat.push(')');
    wat::parse_str(&wat).unwrap_or_else(|e| panic!("WAT: {e}\n{wat}"))
}

fn module() -> Vec<u8> {
    module_of(&SHAPES.iter().collect::<Vec<_>>())
}

struct Leg {
    name: &'static str,
    cpu: Cpu,
    flags: &'static [&'static str],
    /// The leg #1762 was wrong on.
    rv32: bool,
}

const RV32: &[&str] = &[
    "-b",
    "riscv",
    "--target",
    "riscv32imac",
    "--relocatable",
    "--all-exports",
];

const LEGS: &[Leg] = &[
    Leg {
        name: "rv32imac",
        cpu: Cpu::Rv32Imac,
        flags: RV32,
        rv32: true,
    },
    Leg {
        name: "m4-relocatable",
        cpu: Cpu::CortexM4,
        flags: &["--target", "cortex-m4", "--relocatable", "--all-exports"],
        rv32: false,
    },
    Leg {
        name: "m3-relocatable",
        cpu: Cpu::CortexM3,
        flags: &["--target", "cortex-m3", "--relocatable", "--all-exports"],
        rv32: false,
    },
    Leg {
        name: "m4-default",
        cpu: Cpu::CortexM4,
        flags: &["--target", "cortex-m4", "--all-exports"],
        rv32: false,
    },
    Leg {
        name: "m4-no-optimize",
        cpu: Cpu::CortexM4,
        flags: &["--target", "cortex-m4", "--all-exports", "--no-optimize"],
        rv32: false,
    },
];

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("zero-init-1762-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// What one shape runs on: its module and the object compiled from it, or
/// synth's stderr when the compile was refused.
type Unit = Result<(Vec<u8>, CompiledObject), String>;

/// Compile `wasm`. `Err` carries synth's stderr when the compile is refused
/// or any of `names` has no code in the object.
fn build(wasm: &[u8], flags: &[&str], names: &[&str]) -> Result<CompiledObject, String> {
    let dir = scratch();
    let input = dir.join("m.wasm");
    std::fs::write(&input, wasm).unwrap();
    let run = compile(&input, flags, &dir.join("m.o")).expect("synth runs");
    if !run.status.success() {
        return Err(run.stderr);
    }
    let obj = run.object.expect("object parsed");
    for n in names {
        if obj.function_bytes(n).is_none_or(|b| b.is_empty()) {
            return Err(format!("no bytes for `{n}`: {}", run.stderr));
        }
    }
    Ok(obj)
}

fn show(v: &[WasmValue]) -> String {
    v.iter()
        .map(|x| match x {
            WasmValue::I32(a) => format!("{a:#x}"),
            WasmValue::I64(a) => format!("{a:#x}"),
            other => format!("{other:?}"),
        })
        .collect::<Vec<_>>()
        .join(",")
}

#[test]
fn a_never_written_local_reads_zero_at_its_declared_width() {
    let wasm = module();
    let names: Vec<&str> = SHAPES.iter().map(|s| s.name).collect();
    let imports = Imports::new();
    let mut total = 0;
    let mut bad_total = 0;
    let mut rv32_cases = 0;
    let mut report = String::new();
    for leg in LEGS {
        // One module for the whole leg. If synth refuses any function of it,
        // fall back to one module per shape, so a refusal of one shape does
        // not hide what the others compute.
        let units: Vec<(&Shape, Unit)> = match build(&wasm, leg.flags, &names) {
            Ok(obj) => SHAPES
                .iter()
                .map(|s| (s, Ok((wasm.clone(), obj.clone()))))
                .collect(),
            Err(_) => SHAPES
                .iter()
                .map(|s| {
                    let w = module_of(&[s]);
                    let r = build(&w, leg.flags, &[s.name]);
                    (s, r.map(|o| (w, o)))
                })
                .collect(),
        };
        let cfg = EmuConfig::new(leg.cpu);
        let mut cases: Vec<Case> = Vec::new();
        let mut refused: Vec<&str> = Vec::new();
        for (s, unit) in &units {
            let (w, obj) = match unit {
                Ok(u) => u,
                Err(e) => {
                    let why = e
                        .lines()
                        .find(|l| l.contains("skipping function"))
                        .unwrap_or("no reason on stderr");
                    report.push_str(&format!("  REFUSED {} {}: {why}\n", leg.name, s.name));
                    refused.push(s.name);
                    continue;
                }
            };
            for &a in ARGS {
                let args = [WasmValue::I32(a)];
                let c = run_case(w, obj, s.name, &args, FUEL, &imports, &cfg).unwrap_or_else(|e| {
                    panic!("{} {}({a:#x}): harness error {e:?}", leg.name, s.name)
                });
                cases.push(c);
            }
        }
        // Every case returned a VALUE on the reference: a sweep of traps
        // would agree without comparing one result.
        assert!(
            cases
                .iter()
                .all(|c| matches!(c.reference, RefOutcome::Values(_))),
            "{}: a reference run did not return a value",
            leg.name
        );
        let mut per: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
        for c in &cases {
            let e = per.entry(c.export.as_str()).or_default();
            e.1 += 1;
            if !c.verdict.is_agree() {
                e.0 += 1;
                let (r, m) = match (&c.reference, &c.emulator) {
                    (RefOutcome::Values(r), EmuOutcome::Values(m)) => (show(r), show(m)),
                    (r, m) => (format!("{r:?}"), format!("{m:?}")),
                };
                report.push_str(&format!(
                    "  WRONG {} {}({}) = {m}, reference {r}\n",
                    leg.name,
                    c.export,
                    show(&c.args)
                ));
            }
        }
        // A refused shape counts every one of its vectors as wrong.
        let n = cases.len() + refused.len() * ARGS.len();
        let bad: usize = per.values().map(|p| p.0).sum::<usize>() + refused.len() * ARGS.len();
        let wrong: Vec<String> = per
            .iter()
            .filter(|(_, p)| p.0 > 0)
            .map(|(n, p)| format!("{n} {}/{}", p.0, p.1))
            .collect();
        eprintln!(
            "ORACLE zero-init-1762 [{}]: {} of {} wrong; wrong values: [{}]; refused: [{}]",
            leg.name,
            bad,
            n,
            wrong.join(", "),
            refused.join(", ")
        );
        if leg.rv32 {
            rv32_cases += n;
        }
        total += n;
        bad_total += bad;
    }
    eprint!("{report}");
    // EXACT literals: shrinking the shapes, the vectors or the legs reds.
    assert_eq!(total, 300, "case count moved");
    assert_eq!(
        bad_total, 0,
        "{bad_total} of {total} cases disagree with kiln"
    );
    assert_eq!(rv32_cases, 60, "RV32 case count moved");
    eprintln!(
        "ORACLE zero-init-1762: {total} cases agree across {} legs",
        LEGS.len()
    );
}

/// The f64 twin on RV32. An f64 local is 8 bytes and returns in a0:a1 under
/// the soft-float ILP32 convention, exactly like an i64; no float signature
/// runs on this leg, so the pin is that its code EQUALS the i64 twin's,
/// which the sweep above executes. The f32 twin must equal the i32 one.
#[test]
fn rv32_float_locals_are_lowered_like_their_integer_twins() {
    let one = |result: &str, local: &str| -> Vec<u8> {
        let wat = format!(
            "(module (func (export \"f\") (param i32) (result {result}) (local {local}) local.get 1))"
        );
        let wasm = wat::parse_str(&wat).unwrap();
        let obj = build(&wasm, RV32, &["f"]).unwrap_or_else(|e| panic!("{result}: {e}"));
        obj.function_bytes("f").unwrap().to_vec()
    };
    let (l, d) = (one("i64", "i64"), one("f64", "f64"));
    let (i, f) = (one("i32", "i32"), one("f32", "f32"));
    assert_eq!(d, l, "the f64 local is not lowered like the i64 local");
    assert_eq!(f, i, "the f32 local is not lowered like the i32 local");
    assert_ne!(l, i, "the i64 and i32 twins are the same code");
    eprintln!("ORACLE zero-init-1762 rv32 float twins: 2 of 2 byte-identical to the integer twin");
}

/// The bytes main 6641efec emitted for the issue function on `-b riscv`:
/// `addi sp,sp,-16; sw zero,0(sp); lw t0,0(sp); mv a0,t0; addi sp,sp,16; ret`
/// (and the unreachable second epilogue). Frozen, so this stays red-capable.
const PRE_FIX_ISSUE_FN: &[u32] = &[
    0xff01_0113, // addi sp, sp, -16
    0x0001_2023, // sw zero, 0(sp)
    0x0001_2283, // lw t0, 0(sp)
    0x0002_8513, // mv a0, t0
    0x0101_0113, // addi sp, sp, 16
    0x0000_8067, // ret
    0x0002_8513,
    0x0101_0113,
    0x0000_8067,
];

/// POTENCY: the harness sees the defect. The frozen pre-fix bytes leave a1
/// as the emulator's poison, so the i64 result's high word is `0xFEEDFACE`.
#[test]
fn frozen_pre_fix_bytes_are_judged_wrong() {
    let wasm = module();
    let text: Vec<u8> = PRE_FIX_ISSUE_FN
        .iter()
        .flat_map(|w| w.to_le_bytes())
        .collect();
    let obj = CompiledObject {
        path: Path::new("frozen-pre-fix-1762").to_path_buf(),
        machine: Machine::RiscV32,
        funcs: BTreeMap::from([(
            "ret".to_string(),
            FuncSym {
                offset: 0,
                size: text.len() as u64,
                thumb: false,
                global: true,
            },
        )]),
        text,
        text_relocs: Vec::new(),
        relocs: Vec::new(),
        relocatable: true,
        e_flags: 0,
    };
    let cfg = EmuConfig::new(Cpu::Rv32Imac);
    let c = run_case(
        &wasm,
        &obj,
        "ret",
        &[WasmValue::I32(5)],
        FUEL,
        &Imports::new(),
        &cfg,
    )
    .expect("runs");
    assert_eq!(c.reference, RefOutcome::Values(vec![WasmValue::I64(0)]));
    assert_eq!(
        c.emulator,
        EmuOutcome::Values(vec![WasmValue::I64(0xFEED_FACE_0000_0000)])
    );
    assert!(matches!(c.verdict, Verdict::Disagree(_)), "{:?}", c.verdict);
}
