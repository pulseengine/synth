//! #1745: the published LIBRARY entry point, `Backend::compile_module`,
//! executed against kiln.
//!
//! No `synth` invocation reaches `compile_module`: the CLI decodes the module
//! itself and drives `compile_function` with each function's facts threaded
//! (declared param count, float-param masks, blocktype arity). A library
//! caller hands `compile_module` a decoded module and a config, and the
//! backend has to thread those facts from the MODULE. The AArch64 backend did
//! not: with a default config a value-carrying block returned the caller's
//! x0, a zero-initialised local returned the caller's x1, and a float param
//! did not compile.
//!
//! What runs here, each case on kiln and under unicorn:
//!
//! 1. the eight bodies of the issue through `AArch64Backend::compile_module`,
//!    under the default config and under the issue's config;
//! 2. the paired control: the same bodies through `compile_function` with the
//!    CLI's per-function config, which was already right;
//! 3. the same bodies with a caller config whose own tables are WRONG for the
//!    module: the module's facts must win;
//! 4. the twin: `ArmBackend` and `RiscVBackend::compile_module` over the
//!    facts those two read from the caller's config.
//!
//! Then the guards the AArch64 runner adds to the harness, each shown red.
//!
//! Needs `--features exec` (kiln + unicorn). No `synth` binary is used.

#![cfg(feature = "exec")]

use std::path::PathBuf;

use synth_backend::ArmBackend;
use synth_backend_aarch64::AArch64Backend;
use synth_backend_riscv::RiscVBackend;
use synth_core::backend::{Backend, CompileConfig, SafetyBounds};
use synth_core::target::TargetSpec;
use synth_core::wasm_decoder::{DecodedModule, decode_wasm_module};
use synth_oracle::compare::{EmuOutcome, RefOutcome};
use synth_oracle::emulate::{self, Cpu, EmuConfig, EmuError};
use synth_oracle::reference::Imports;
use synth_oracle::run_case;
use synth_oracle::synth::{CompiledObject, FuncSym, Machine};
use synth_oracle::value::{Signature, ValType, WasmValue};

const FUEL: u64 = 100_000;

fn i(v: u32) -> WasmValue {
    WasmValue::I32(v)
}
fn l(v: u64) -> WasmValue {
    WasmValue::I64(v)
}
fn f(v: f32) -> WasmValue {
    WasmValue::F32(v.to_bits())
}

/// One body: the module text, the argument vectors, and the value wasm gives
/// for each (a literal, checked against kiln, so the reference cannot drift).
struct Row {
    name: &'static str,
    wat: &'static str,
    cases: Vec<(Vec<WasmValue>, WasmValue)>,
}

fn i32_row(name: &'static str, body: &'static str, want: [u32; 3]) -> Row {
    Row {
        name,
        wat: body,
        cases: [0u32, 1, 5]
            .iter()
            .zip(want)
            .map(|(a, w)| (vec![i(*a)], i(w)))
            .collect(),
    }
}

/// The eight rows of #1745's table, in its order.
fn issue_rows() -> Vec<Row> {
    vec![
        i32_row(
            "block_result",
            r#"(module (func (export "f") (param i32) (result i32)
                 (block (result i32) (i32.const 7))))"#,
            [7, 7, 7],
        ),
        i32_row(
            "value_below_block",
            r#"(module (func (export "f") (param i32) (result i32)
                 i32.const 100 (block (result i32) (i32.const 7)) drop))"#,
            [100, 100, 100],
        ),
        i32_row(
            "if_result",
            r#"(module (func (export "f") (param i32) (result i32)
                 (if (result i32) (local.get 0) (then (i32.const 11)) (else (i32.const 22)))))"#,
            [22, 11, 11],
        ),
        i32_row(
            "br_if_value",
            r#"(module (func (export "f") (param i32) (result i32)
                 (block (result i32) (i32.const 5) (br_if 0 (local.get 0)) (drop) (i32.const 9))))"#,
            [9, 5, 5],
        ),
        i32_row(
            "loop_result",
            r#"(module (func (export "f") (param i32) (result i32)
                 i32.const 40 (loop (result i32) (i32.const 2)) i32.add))"#,
            [42, 42, 42],
        ),
        i32_row(
            "void_control",
            r#"(module (func (export "f") (param i32) (result i32)
                 (block (br_if 0 (local.get 0))) (i32.const 3)))"#,
            [3, 3, 3],
        ),
        i32_row(
            "zero_init_local",
            r#"(module (func (export "f") (param i32) (result i32) (local i32)
                 local.get 1))"#,
            [0, 0, 0],
        ),
        Row {
            name: "f32_param",
            wat: r#"(module (func (export "f") (param i32 f32) (result f32)
                      local.get 1 f32.neg))"#,
            cases: vec![
                (vec![i(0), f(1.5)], f(-1.5)),
                (vec![i(1), f(-2.25)], f(2.25)),
                (vec![i(5), f(0.0)], f(-0.0)),
            ],
        },
    ]
}

/// The issue's eight rows, and one more for the fact they leave out: the f64
/// param mask (without it `f64.neg` sees a GP operand and does not compile).
fn a64_rows() -> Vec<Row> {
    let d = |v: f64| WasmValue::F64(v.to_bits());
    let mut rows = issue_rows();
    rows.push(Row {
        name: "f64_param",
        wat: r#"(module (func (export "f") (param i32 f64) (result f64)
                  local.get 1 f64.neg))"#,
        cases: vec![
            (vec![i(0), d(1.5)], d(-1.5)),
            (vec![i(1), d(-2.25)], d(2.25)),
            (vec![i(5), d(0.0)], d(-0.0)),
        ],
    });
    rows
}

/// The config of the issue's measurement.
fn issue_cfg() -> CompileConfig {
    CompileConfig {
        target: TargetSpec::cortex_a53(),
        relocatable: true,
        safety_bounds: SafetyBounds::Software,
        ..CompileConfig::default()
    }
}

fn decode(wat: &str) -> (Vec<u8>, DecodedModule) {
    let wasm = wat::parse_str(wat).expect("WAT parses");
    let module = decode_wasm_module(&wasm).expect("decodes");
    (wasm, module)
}

/// A one-function object over the bytes a backend returned for `f`.
fn object_of(machine: Machine, code: &[u8], relocs: Vec<u64>) -> CompiledObject {
    CompiledObject {
        path: PathBuf::from("library.o"),
        machine,
        text: code.to_vec(),
        funcs: [(
            "f".to_string(),
            FuncSym {
                offset: 0,
                size: code.len() as u64,
                thumb: machine == Machine::Arm,
                global: true,
            },
        )]
        .into_iter()
        .collect(),
        text_relocs: relocs,
    }
}

/// Run a compile that may panic (a debug build asserts where a release build
/// emits wrong code) and flatten the three outcomes.
fn guarded<T>(
    compile: impl FnOnce() -> Result<T, synth_core::backend::BackendError>,
) -> Result<T, String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(compile)) {
        Ok(Ok(v)) => Ok(v),
        Ok(Err(e)) => Err(format!("Err: {e}")),
        Err(p) => Err(format!(
            "PANIC: {}",
            p.downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| p.downcast_ref::<&str>().copied())
                .unwrap_or("?")
        )),
    }
}

/// AArch64 through `compile_module`: the object is the ELF the backend
/// returned, read through the symbol table.
fn a64_module(module: &DecodedModule, cfg: &CompileConfig) -> Result<CompiledObject, String> {
    let r = guarded(|| AArch64Backend::new().compile_module(module, cfg))?;
    let elf = r.elf.ok_or("compile_module returned no ELF")?;
    CompiledObject::parse_bytes(&PathBuf::from("a64.o"), &elf)
}

/// AArch64 through `compile_function` with the per-function config the CLI
/// builds (`synth-cli/src/main.rs`, the per-function `fc`).
fn a64_function(module: &DecodedModule, cfg: &CompileConfig) -> Result<CompiledObject, String> {
    let func = &module.functions[0];
    let idx = func.index as usize;
    let fc = CompileConfig {
        func_arg_counts: module.func_arg_counts.clone(),
        current_func_param_count: module.func_arg_counts.get(idx).copied(),
        current_func_params_f32: module.func_params_f32.get(idx).cloned().unwrap_or_default(),
        current_func_params_f64: module.func_params_f64.get(idx).cloned().unwrap_or_default(),
        current_func_block_arity: func.block_arity.clone(),
        ..cfg.clone()
    };
    let c = guarded(|| AArch64Backend::new().compile_function("f", &func.ops, &fc))?;
    Ok(object_of(
        Machine::AArch64,
        &c.code,
        c.relocations.iter().map(|r| u64::from(r.offset)).collect(),
    ))
}

/// One row on one object: what each vector gave, and whether all agreed.
struct RowResult {
    line: String,
    agree: usize,
    total: usize,
}

fn run_row(
    leg: &str,
    row: &Row,
    wasm: &[u8],
    obj: &Result<CompiledObject, String>,
    cpu: Cpu,
) -> RowResult {
    let total = row.cases.len();
    let obj = match obj {
        Ok(o) => o,
        Err(e) => {
            return RowResult {
                line: format!("ROW {leg} {}: no code ({e})", row.name),
                agree: 0,
                total,
            };
        }
    };
    let (mut got, mut want, mut agree) = (Vec::new(), Vec::new(), 0);
    for (args, literal) in &row.cases {
        match run_case(
            wasm,
            obj,
            "f",
            args,
            FUEL,
            &Imports::new(),
            &EmuConfig::new(cpu),
        ) {
            Ok(c) => {
                // The reference is checked against the literal first: a kiln
                // that agreed with wrong code would otherwise pass.
                assert_eq!(
                    c.reference,
                    RefOutcome::Values(vec![*literal]),
                    "{leg} {}: kiln disagrees with the expected literal",
                    row.name
                );
                want.push(format!("{literal:?}"));
                got.push(match &c.emulator {
                    EmuOutcome::Values(v) if v.len() == 1 => format!("{:?}", v[0]),
                    other => format!("{other:?}"),
                });
                agree += usize::from(c.verdict.is_agree());
            }
            Err(e) => got.push(format!("HARNESS {e:?}")),
        }
    }
    RowResult {
        line: format!(
            "ROW {leg} {}: emu=[{}] wasm=[{}] {}",
            row.name,
            got.join(", "),
            want.join(", "),
            if agree == total { "agree" } else { "WRONG" }
        ),
        agree,
        total,
    }
}

/// Run every row on every leg, print every line, and return (agreeing cases,
/// total cases, the lines that did not agree).
fn sweep_a64(
    title: &str,
    legs: &[(&str, CompileConfig)],
    build: impl Fn(&DecodedModule, &CompileConfig) -> Result<CompiledObject, String>,
) -> (usize, usize, Vec<String>) {
    let (mut agree, mut total, mut bad) = (0, 0, Vec::new());
    for (leg, cfg) in legs {
        for row in a64_rows() {
            let (wasm, module) = decode(row.wat);
            let obj = build(&module, cfg);
            let r = run_row(&format!("{title}/{leg}"), &row, &wasm, &obj, Cpu::CortexA53);
            eprintln!("{}", r.line);
            agree += r.agree;
            total += r.total;
            if r.agree != r.total {
                bad.push(r.line);
            }
        }
    }
    (agree, total, bad)
}

fn a64_legs() -> Vec<(&'static str, CompileConfig)> {
    vec![
        ("default", CompileConfig::default()),
        ("issue-config", issue_cfg()),
    ]
}

#[test]
fn a64_compile_module_agrees_with_kiln_1745() {
    let (agree, total, bad) = sweep_a64("a64-compile_module", &a64_legs(), a64_module);
    eprintln!("ORACLE 1745 a64 compile_module: {agree} of {total} cases agree");
    assert!(
        bad.is_empty(),
        "compile_module disagrees with wasm:\n{}",
        bad.join("\n")
    );
    // EXACT: 9 rows x 3 vectors x 2 configs.
    assert_eq!((agree, total), (54, 54), "case count moved");
}

/// The paired control. `compile_function` with the CLI's per-function config
/// was right before the fix, so a red in the test above is `compile_module`'s
/// and not the harness's.
#[test]
fn a64_compile_function_cli_shape_agrees_with_kiln_1745() {
    let (agree, total, bad) = sweep_a64("a64-compile_function", &a64_legs(), a64_function);
    eprintln!("ORACLE 1745 a64 compile_function (control): {agree} of {total} cases agree");
    assert!(bad.is_empty(), "the control is red:\n{}", bad.join("\n"));
    assert_eq!((agree, total), (54, 54), "case count moved");
}

/// A caller whose config already carries per-function facts, for ANOTHER
/// function: `compile_module` must compile each function against the module
/// it was handed. Every table here is wrong for every row.
#[test]
fn a64_module_facts_win_over_the_callers_config_1745() {
    let stale = CompileConfig {
        func_arg_counts: vec![0, 0, 0],
        current_func_param_count: Some(0),
        current_func_params_f32: vec![true, false],
        current_func_params_f64: vec![false, true],
        current_func_block_arity: vec![(0, 0), (0, 0), (0, 0)],
        ..CompileConfig::default()
    };
    let (agree, total, bad) = sweep_a64("a64-stale-caller", &[("stale", stale)], a64_module);
    eprintln!("ORACLE 1745 a64 stale caller config: {agree} of {total} cases agree");
    assert!(
        bad.is_empty(),
        "a caller table overrode the module:\n{}",
        bad.join("\n")
    );
    assert_eq!((agree, total), (27, 27), "case count moved");
}

// ------------------------------------------------------- ARM / RV32 twin --

/// Bodies over the facts `ArmBackend` and `RiscVBackend::compile_module`
/// take per function: the declared param count, the i64-param mask and the
/// blocktype arity. Integer signatures only. The declared i64 locals are
/// covered by the two `declared_i64_local*` rows, on ARM (RV32 has no such
/// channel); `zero_init_i64_local` passes on width inference alone. The
/// float facts are in `arm_vfp_compile_module_twin_1745`.
fn twin_rows() -> Vec<Row> {
    let hi = 0x1111_2222_3333_4444u64;
    let mut rows: Vec<Row> = issue_rows().into_iter().take(7).collect();
    rows.extend([
        Row {
            name: "i64_param_after_i32",
            wat: r#"(module (func (export "f") (param i32 i64) (result i64) local.get 1))"#,
            cases: vec![
                (vec![i(7), l(hi)], l(hi)),
                (vec![i(0), l(1)], l(1)),
                (vec![i(1), l(u64::MAX)], l(u64::MAX)),
            ],
        },
        Row {
            name: "i32_param_after_i64",
            wat: r#"(module (func (export "f") (param i64 i32) (result i32) local.get 1))"#,
            cases: vec![
                (vec![l(hi), i(7)], i(7)),
                (vec![l(0), i(1)], i(1)),
                (vec![l(u64::MAX), i(0)], i(0)),
            ],
        },
        Row {
            name: "unused_i64_param",
            wat: r#"(module (func (export "f") (param i32 i64) (result i32) local.get 0))"#,
            cases: vec![
                (vec![i(7), l(hi)], i(7)),
                (vec![i(0), l(1)], i(0)),
                (vec![i(1), l(0)], i(1)),
            ],
        },
        Row {
            name: "zero_init_i64_local",
            wat: r#"(module (func (export "f") (param i32) (result i64) (local i64)
                      local.get 1))"#,
            cases: vec![(vec![i(0)], l(0)), (vec![i(1)], l(0)), (vec![i(5)], l(0))],
        },
        // The DECLARED width is the only source in these two: the locals
        // are never written, so nothing but the declaration says they are
        // 64-bit. With it ignored, `i64.eqz` answers 0 for 1 and the
        // `i64.or` returns a high word nothing zeroed.
        Row {
            name: "declared_i64_local_eqz",
            wat: r#"(module (func (export "f") (param i32) (result i32) (local i64)
                      local.get 1 i64.eqz))"#,
            cases: vec![(vec![i(0)], i(1)), (vec![i(1)], i(1)), (vec![i(5)], i(1))],
        },
        Row {
            name: "declared_i64_locals_or",
            wat: r#"(module (func (export "f") (param i32) (result i64) (local i64 i64)
                      local.get 1 local.get 2 i64.or))"#,
            cases: vec![(vec![i(0)], l(0)), (vec![i(1)], l(0)), (vec![i(5)], l(0))],
        },
        Row {
            name: "cond_written_param",
            wat: r#"(module (func (export "f") (param i32 i32) (result i32)
                      (if (local.get 0) (then (local.set 1 (i32.const 9))))
                      local.get 1))"#,
            cases: vec![
                (vec![i(0), i(42)], i(42)),
                (vec![i(1), i(42)], i(9)),
                (vec![i(5), i(0)], i(9)),
            ],
        },
        Row {
            name: "i64_add_params",
            wat: r#"(module (func (export "f") (param i64 i32) (result i64)
                      local.get 0 local.get 1 i64.extend_i32_u i64.add))"#,
            cases: vec![
                (vec![l(hi), i(1)], l(hi + 1)),
                (vec![l(0), i(0)], l(0)),
                (vec![l(u64::MAX), i(1)], l(0)),
            ],
        },
    ]);
    rows
}

fn twin_sweep(
    title: &str,
    machine: Machine,
    cpu: Cpu,
    rows: fn() -> Vec<Row>,
    legs: &[(&str, CompileConfig)],
    // Rows the backend must REFUSE, with the text the refusal carries. A loud
    // refusal is the right outcome where the backend cannot lower the shape;
    // `Ok` with any code for one of these is a failure.
    declines: &[(&str, &str)],
    // Rows left out, each with its reason at the call site.
    skip: &[&str],
    build: impl Fn(
        &DecodedModule,
        &CompileConfig,
    )
        -> Result<synth_core::backend::CompilationResult, synth_core::backend::BackendError>,
) -> (usize, usize, usize, Vec<String>) {
    let (mut agree, mut total, mut refused, mut bad) = (0, 0, 0, Vec::new());
    for (leg, cfg) in legs {
        for row in rows() {
            if skip.contains(&row.name) {
                continue;
            }
            let (wasm, module) = decode(row.wat);
            if let Some((_, needle)) = declines.iter().find(|(n, _)| *n == row.name) {
                let line = match guarded(|| build(&module, cfg)) {
                    Err(e) if e.starts_with("Err: ") && e.contains(needle) => {
                        eprintln!("ROW {title}/{leg} {}: declined ({e})", row.name);
                        refused += 1;
                        continue;
                    }
                    Err(e) => format!("ROW {title}/{leg} {}: wrong refusal ({e})", row.name),
                    Ok(_) => format!(
                        "ROW {title}/{leg} {}: compiled, expected a refusal",
                        row.name
                    ),
                };
                eprintln!("{line}");
                bad.push(line);
                continue;
            }
            let obj = guarded(|| build(&module, cfg)).map(|r| {
                let c = &r.functions[0];
                object_of(
                    machine,
                    &c.code,
                    c.relocations.iter().map(|r| u64::from(r.offset)).collect(),
                )
            });
            let r = run_row(&format!("{title}/{leg}"), &row, &wasm, &obj, cpu);
            eprintln!("{}", r.line);
            agree += r.agree;
            total += r.total;
            if r.agree != r.total {
                bad.push(r.line);
            }
        }
    }
    (agree, total, refused, bad)
}

#[test]
fn arm_compile_module_twin_1745() {
    let legs = [
        ("default", CompileConfig::default()),
        (
            "relocatable",
            CompileConfig {
                relocatable: true,
                ..CompileConfig::default()
            },
        ),
        (
            "no-optimize",
            CompileConfig {
                no_optimize: true,
                ..CompileConfig::default()
            },
        ),
    ];
    let (agree, total, _, bad) = twin_sweep(
        "arm-compile_module",
        Machine::Arm,
        Cpu::CortexM4,
        twin_rows,
        &legs,
        &[],
        &[],
        |m, c| ArmBackend::new().compile_module(m, c),
    );
    eprintln!("ORACLE 1745 arm compile_module: {agree} of {total} cases agree");
    assert!(bad.is_empty(), "ARM twin:\n{}", bad.join("\n"));
    // 15 rows x 3 vectors x 3 configs.
    assert_eq!((agree, total), (135, 135), "case count moved");
}

#[test]
fn rv32_compile_module_twin_1745() {
    // The RV32 backend refuses the default (Cortex-M4) target, so the target
    // is the one field set.
    let legs = [(
        "default+target",
        CompileConfig {
            target: TargetSpec::riscv32imac(),
            ..CompileConfig::default()
        },
    )];
    let (agree, total, refused, bad) = twin_sweep(
        "rv32-compile_module",
        Machine::RiscV32,
        Cpu::Rv32Imac,
        twin_rows,
        &legs,
        // The RV32 selector does not lower a READ of an i64 param; with the
        // module's i64-param mask threaded it says so. Before #1745 the mask
        // was never set here, and these two compiled to wrong code (the
        // first) or failed on a later op for a reason that named nothing.
        &[
            (
                "i64_param_after_i32",
                "unsupported wasm op for RV32 skeleton: LocalGet(1)",
            ),
            (
                "i64_add_params",
                "unsupported wasm op for RV32 skeleton: LocalGet(0)",
            ),
            // The RV32 selector has no declared-i64-local channel, so a
            // never-written i64 local reads as an i32. Where an i64 operator
            // consumes it the selector refuses, on the CLI too (same
            // message, main 6641efec).
            (
                "declared_i64_local_eqz",
                "stack type mismatch at op I64Eqz: expected i64, found i32",
            ),
            (
                "declared_i64_locals_or",
                "stack type mismatch at op I64Or: expected i64, found i32",
            ),
        ],
        // NOT a `compile_module` difference, so not judged here: where no
        // operator consumes it, the same gap is silent. `synth compile -b
        // riscv` emits the same code for this body (a0 loaded from the
        // zeroed slot, a1 never written), measured on main 6641efec.
        &["zero_init_i64_local"],
        |m, c| RiscVBackend::new().compile_module(m, c),
    );
    eprintln!("ORACLE 1745 rv32 compile_module: {agree} of {total} cases agree, {refused} refused");
    assert!(bad.is_empty(), "RV32 twin:\n{}", bad.join("\n"));
    // 15 rows, less 1 skipped and 4 refused, x 3 vectors.
    assert_eq!((agree, total, refused), (30, 30, 4), "case count moved");
}

/// The facts only ARM's hard-float targets read. Integer PARAMETERS only
/// (the harness sets up no float argument on ARM); a float result is read
/// from s0/d0.
///
/// What these rows DO pin is the declared float locals: with that table
/// ignored, the three zero-init rows return POISON. What they do NOT pin is
/// the f32/f64 RETURN FLAGS: with the flags ignored every row here still
/// agrees, and so did five more float-result shapes on three configs. The
/// flags only arm the epilogue's refusal of a float result that arrives
/// integer-tagged, which takes a `call` to a float-returning function, and a
/// function with a call carries a relocation this harness does not run. The
/// flags are pinned by the `for_function` unit test in `synth-core` only.
fn vfp_rows_m4f() -> Vec<Row> {
    vec![
        Row {
            name: "ret_f32",
            wat: r#"(module (func (export "f") (param i32) (result f32)
                      local.get 0 f32.convert_i32_s))"#,
            cases: vec![
                (vec![i(0)], f(0.0)),
                (vec![i(1)], f(1.0)),
                (vec![i(5)], f(5.0)),
            ],
        },
        Row {
            name: "zero_init_f32_local",
            wat: r#"(module (func (export "f") (param i32) (result i32) (local f32)
                      local.get 1 i32.reinterpret_f32))"#,
            cases: vec![(vec![i(0)], i(0)), (vec![i(1)], i(0)), (vec![i(5)], i(0))],
        },
        Row {
            name: "zero_init_f32_local_returned",
            wat: r#"(module (func (export "f") (param i32) (result f32) (local f32)
                      local.get 1))"#,
            cases: vec![
                (vec![i(0)], f(0.0)),
                (vec![i(1)], f(0.0)),
                (vec![i(5)], f(0.0)),
            ],
        },
    ]
}

fn vfp_rows_m7dp() -> Vec<Row> {
    let d = |v: f64| WasmValue::F64(v.to_bits());
    vec![
        Row {
            name: "ret_f64",
            wat: r#"(module (func (export "f") (param i32) (result f64)
                      local.get 0 f64.convert_i32_s))"#,
            cases: vec![
                (vec![i(0)], d(0.0)),
                (vec![i(1)], d(1.0)),
                (vec![i(5)], d(5.0)),
            ],
        },
        Row {
            name: "zero_init_f64_local_returned",
            wat: r#"(module (func (export "f") (param i32) (result f64) (local f64)
                      local.get 1))"#,
            cases: vec![
                (vec![i(0)], d(0.0)),
                (vec![i(1)], d(0.0)),
                (vec![i(5)], d(0.0)),
            ],
        },
    ]
}

#[test]
fn arm_vfp_compile_module_twin_1745() {
    let leg = |target: TargetSpec| CompileConfig {
        target,
        ..CompileConfig::default()
    };
    let (a4, t4, _, mut bad) = twin_sweep(
        "arm-m4f-compile_module",
        Machine::Arm,
        Cpu::CortexM4F,
        vfp_rows_m4f,
        &[("m4f", leg(TargetSpec::cortex_m4f()))],
        &[],
        &[],
        |m, c| ArmBackend::new().compile_module(m, c),
    );
    let (a7, t7, _, bad7) = twin_sweep(
        "arm-m7dp-compile_module",
        Machine::Arm,
        Cpu::CortexM7F,
        vfp_rows_m7dp,
        &[("m7dp", leg(TargetSpec::cortex_m7dp()))],
        &[],
        &[],
        |m, c| ArmBackend::new().compile_module(m, c),
    );
    bad.extend(bad7);
    let (agree, total) = (a4 + a7, t4 + t7);
    eprintln!("ORACLE 1745 arm vfp compile_module: {agree} of {total} cases agree");
    assert!(bad.is_empty(), "ARM VFP twin:\n{}", bad.join("\n"));
    assert_eq!((agree, total), (15, 15), "case count moved");
}

// ------------------------------------------- the AArch64 runner's guards --

fn a64(words: &[u32]) -> CompiledObject {
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    object_of(Machine::AArch64, &code, vec![])
}

fn sig(params: &[ValType], result: ValType) -> Signature {
    Signature {
        params: params.to_vec(),
        results: vec![result],
    }
}

fn emu(obj: &CompiledObject, s: &Signature, args: &[WasmValue]) -> EmuOutcome {
    emulate::run(obj, "f", s, args, &EmuConfig::new(Cpu::CortexA53))
        .expect("emulates")
        .outcome
}

const RET: u32 = 0xD65F_03C0;

#[test]
fn a64_guard_cpu_model_is_read_back() {
    let r = emulate::run(
        &a64(&[0x5280_00A0, RET]), // mov w0, #5
        "f",
        &sig(&[], ValType::I32),
        &[],
        &EmuConfig::new(Cpu::CortexA53),
    )
    .expect("emulates");
    assert_eq!(r.cpu_model_readback, Cpu::CortexA53.model_id());
    assert_eq!(r.outcome, EmuOutcome::Values(vec![i(5)]));
    // An A64 object is refused on a 32-bit core, and the reverse.
    assert!(matches!(
        emulate::run(
            &a64(&[RET]),
            "f",
            &sig(&[], ValType::I32),
            &[],
            &EmuConfig::new(Cpu::CortexM4)
        ),
        Err(EmuError::WrongMachine { .. })
    ));
}

#[test]
fn a64_guard_arguments_follow_aapcs64() {
    // An i32 argument's upper half is POISON, not zero: `ret` alone hands x0
    // back, read here as an i64.
    assert_eq!(
        emu(&a64(&[RET]), &sig(&[ValType::I32], ValType::I64), &[i(7)]),
        EmuOutcome::Values(vec![l(0xFEED_FACE_0000_0007)])
    );
    // ... and the same register read as an i32 result is its low half.
    assert_eq!(
        emu(&a64(&[RET]), &sig(&[ValType::I32], ValType::I32), &[i(7)]),
        EmuOutcome::Values(vec![i(7)])
    );
    // An unused argument register is POISON: `mov x0, x1`.
    assert_eq!(
        emu(
            &a64(&[0xAA01_03E0, RET]),
            &sig(&[ValType::I32], ValType::I64),
            &[i(7)]
        ),
        EmuOutcome::Values(vec![l(0xFEED_FACE_FEED_FACE)])
    );
    // The second integer argument is x1, whole: `mov x0, x1`.
    assert_eq!(
        emu(
            &a64(&[0xAA01_03E0, RET]),
            &sig(&[ValType::I32, ValType::I64], ValType::I64),
            &[i(7), l(0x1111_2222_3333_4444)]
        ),
        EmuOutcome::Values(vec![l(0x1111_2222_3333_4444)])
    );
    // Floats count separately from integers: with (i32, f32) the float is
    // v0. `fneg s0, s0` negates it; `fneg s0, s1` would negate POISON.
    let s = sig(&[ValType::I32, ValType::F32], ValType::F32);
    assert_eq!(
        emu(&a64(&[0x1E21_4000, RET]), &s, &[i(7), f(1.5)]),
        EmuOutcome::Values(vec![f(-1.5)])
    );
    assert_eq!(
        emu(&a64(&[0x1E21_4020, RET]), &s, &[i(7), f(1.5)]),
        EmuOutcome::Values(vec![WasmValue::F32(0xFEED_FACE ^ 0x8000_0000)])
    );
    // A float result is read from v0, not x0: `fmov w0, s0` alone leaves the
    // argument in v0, so the negation done in x0 is not seen.
    // (`eor w0, w0, #0x80000000` then `ret`.)
    assert_eq!(
        emu(
            &a64(&[0x1E26_0000, 0x5201_0000, RET]),
            &sig(&[ValType::F32], ValType::F32),
            &[f(1.5)]
        ),
        EmuOutcome::Values(vec![f(1.5)])
    );
    // f64: `fneg d0, d0`.
    assert_eq!(
        emu(
            &a64(&[0x1E61_4000, RET]),
            &sig(&[ValType::F64], ValType::F64),
            &[WasmValue::F64(2.5f64.to_bits())]
        ),
        EmuOutcome::Values(vec![WasmValue::F64((-2.5f64).to_bits())])
    );
    // Nine integer arguments do not fit x0-x7.
    assert!(matches!(
        emulate::run(
            &a64(&[RET]),
            "f",
            &sig(&[ValType::I32; 9], ValType::I32),
            &[i(0); 9],
            &EmuConfig::new(Cpu::CortexA53)
        ),
        Err(EmuError::Abi(_))
    ));
}

#[test]
fn a64_guard_callee_saved_and_sp_are_checked() {
    let s = sig(&[], ValType::I32);
    let illegal = |words: &[u32], what: &str| match emu(&a64(words), &s, &[]) {
        EmuOutcome::Illegal { reason, .. } => {
            assert!(reason.contains(what), "{what}: {reason}")
        }
        other => panic!("{what}: {other:?}"),
    };
    // mov x19, #0 / mov x28, #0 / mov x29, #0
    illegal(&[0xD280_0013, RET], "x19 clobbered");
    illegal(&[0xD280_001C, RET], "x28 clobbered");
    illegal(&[0xD280_001D, RET], "x29 clobbered");
    // Only the UPPER half of x19 changed: `mov w19, w19` zero-extends.
    illegal(&[0x2A13_03F3, RET], "x19 clobbered");
    // fmov d8, xzr / fmov d15, xzr
    illegal(&[0x9E67_03E8, RET], "d8 clobbered");
    illegal(&[0x9E67_03EF, RET], "d15 clobbered");
    // sub sp, sp, #16
    illegal(&[0xD100_43FF, RET], "SP imbalance");
    // The caller-saved neighbours are free: mov x18, #0 ; fmov d16, xzr ;
    // fmov d7, xzr ; mov w0, #5.
    assert_eq!(
        emu(
            &a64(&[0xD280_0012, 0x9E67_03F0, 0x9E67_03E7, 0x5280_00A0, RET]),
            &s,
            &[]
        ),
        EmuOutcome::Values(vec![i(5)])
    );
}

#[test]
fn a64_guard_trap_is_brk_inside_the_function_only() {
    let s = sig(&[], ValType::I32);
    // `brk #0`, what synth emits for a trap.
    assert!(matches!(
        emu(&a64(&[0xD420_0000]), &s, &[]),
        EmuOutcome::Trap { pc, ref insn } if pc == emulate::TEXT_BASE && insn == "brk"
    ));
    // `brk #1` too (the immediate is free).
    assert!(matches!(
        emu(&a64(&[0xD420_0020]), &s, &[]),
        EmuOutcome::Trap { .. }
    ));
    // Not traps: udf #0 (what zero padding decodes as), svc #0, hlt #0, an
    // unallocated encoding.
    for w in [0x0000_0000u32, 0xD400_0001, 0xD440_0000, 0xFFFF_FFFF] {
        assert!(
            matches!(emu(&a64(&[w]), &s, &[]), EmuOutcome::Illegal { .. }),
            "{w:08x}"
        );
    }
    // A real `brk` OUTSIDE the function: `b +8` over the function's end.
    let mut obj = a64(&[0x1400_0002, RET, 0xD420_0000]);
    obj.funcs.get_mut("f").unwrap().size = 8;
    assert!(matches!(emu(&obj, &s, &[]), EmuOutcome::Illegal { .. }));
    // Running out of instructions is never a trap: `b .`.
    assert_eq!(emu(&a64(&[0x1400_0000]), &s, &[]), EmuOutcome::Budget);
    // A function carrying a relocation is refused.
    let mut obj = a64(&[RET]);
    obj.text_relocs = vec![0];
    assert!(matches!(
        emulate::run(&obj, "f", &s, &[], &EmuConfig::new(Cpu::CortexA53)),
        Err(EmuError::NeedsLink { relocs: 1, .. })
    ));
}

/// The ELF64 reader: the object `compile_module` returns is read through its
/// symbol table, and a machine is accepted only in the class synth emits it.
#[test]
fn a64_guard_elf64_is_read_through_the_symtab() {
    let (_, module) = decode(
        r#"(module
             (func (export "a") (result i32) i32.const 1)
             (func (export "b") (result i32) i32.const 2 i32.const 3 i32.add))"#,
    );
    let r = AArch64Backend::new()
        .compile_module(&module, &CompileConfig::default())
        .expect("compiles");
    let elf = r.elf.expect("an ELF");
    let obj = CompiledObject::parse_bytes(&PathBuf::from("two.o"), &elf).expect("parses");
    assert_eq!(obj.machine, Machine::AArch64);
    for (k, name) in ["a", "b"].iter().enumerate() {
        assert_eq!(
            obj.function_bytes(name).expect("in the symtab"),
            &r.functions[k].code[..],
            "`{name}` bytes are the function's own"
        );
    }
    assert!(obj.func("b").unwrap().offset > 0);
    assert!(!obj.func("a").unwrap().thumb);
    // e_machine (offset 18) rewritten to EM_RISCV: an ELF64 RISC-V object is
    // RV64, which this harness does not run, so it is refused.
    let mut rv = elf.clone();
    rv[18..20].copy_from_slice(&object::elf::EM_RISCV.0.to_le_bytes());
    let e = CompiledObject::parse_bytes(&PathBuf::from("rv64.o"), &rv).unwrap_err();
    assert!(e.contains("ELF64"), "{e}");
    // ... and EM_AARCH64 in an ELF32 header is refused the same way.
    let mut bad = elf.clone();
    bad[4] = 1; // EI_CLASS = ELFCLASS32
    assert!(CompiledObject::parse_bytes(&PathBuf::from("a32.o"), &bad).is_err());
}

/// What a run starts from is POISON wherever wasm would have a zero, so a
/// lowering that drops a zero-initialisation cannot agree: the stack on
/// every core, x8-x18 and d16-d31 on AArch64, d0-d15 on the VFP cores.
#[test]
fn guard_uninitialised_state_is_poison() {
    let p32 = i(0xFEED_FACE);
    let p64 = l(0xFEED_FACE_FEED_FACE);
    let s64 = sig(&[], ValType::I64);
    let s32 = sig(&[], ValType::I32);
    // AArch64, below SP: `ldur w0, [sp, #-16]`.
    assert_eq!(
        emu(&a64(&[0xB85F_03E0, RET]), &s32, &[]),
        EmuOutcome::Values(vec![p32])
    );
    // ... and inside a frame the function made: `sub sp, sp, #32 ; ldr x0,
    // [sp, #8] ; add sp, sp, #32`.
    assert_eq!(
        emu(
            &a64(&[0xD100_83FF, 0xF940_07E0, 0x9100_83FF, RET]),
            &s64,
            &[]
        ),
        EmuOutcome::Values(vec![p64])
    );
    // AArch64 scratch registers: `mov x0, xN` for x8, x9, x17, x18.
    for n in [8u32, 9, 17, 18] {
        assert_eq!(
            emu(&a64(&[0xAA00_03E0 | (n << 16), RET]), &s64, &[]),
            EmuOutcome::Values(vec![p64]),
            "x{n}"
        );
    }
    // `fmov x0, dN` for d16 and d31.
    for n in [16u32, 31] {
        assert_eq!(
            emu(&a64(&[0x9E66_0000 | (n << 5), RET]), &s64, &[]),
            EmuOutcome::Values(vec![p64]),
            "d{n}"
        );
    }
    // Thumb: `sub sp, #8 ; ldr r0, [sp] ; add sp, #8 ; bx lr`.
    let thumb = |hs: &[u16]| {
        let code: Vec<u8> = hs.iter().flat_map(|h| h.to_le_bytes()).collect();
        object_of(Machine::Arm, &code, vec![])
    };
    let run = |obj: &CompiledObject, s: &Signature, cpu: Cpu| {
        emulate::run(obj, "f", s, &[], &EmuConfig::new(cpu))
            .expect("emulates")
            .outcome
    };
    let frame_read = thumb(&[0xB082, 0x9800, 0xB002, 0x4770]);
    for cpu in [Cpu::CortexM0, Cpu::CortexM3, Cpu::CortexM4, Cpu::CortexM4F] {
        assert_eq!(
            run(&frame_read, &s32, cpu),
            EmuOutcome::Values(vec![p32]),
            "{cpu:?}"
        );
    }
    // RV32: `lw a0, -16(sp) ; ret`.
    let rv = object_of(
        Machine::RiscV32,
        &[0xFF01_2503u32, 0x0000_8067]
            .iter()
            .flat_map(|w| w.to_le_bytes())
            .collect::<Vec<u8>>(),
        vec![],
    );
    assert_eq!(run(&rv, &s32, Cpu::Rv32Imac), EmuOutcome::Values(vec![p32]));
}

/// The two VFP cores: a VFP instruction runs, an untouched s/d register is
/// POISON, a float result is read from s0/d0, and a float PARAMETER is still
/// refused.
#[test]
fn guard_vfp_cores_enable_the_fpu_and_read_s0() {
    let thumb = |hs: &[u16]| {
        let code: Vec<u8> = hs.iter().flat_map(|h| h.to_le_bytes()).collect();
        object_of(Machine::Arm, &code, vec![])
    };
    let run = |obj: &CompiledObject, s: &Signature, cpu: Cpu| {
        emulate::run(obj, "f", s, &[], &EmuConfig::new(cpu)).map(|r| r.outcome)
    };
    // `vmov r0, s5 ; bx lr` (EE12 0A90): an untouched VFP register.
    let read_s5 = thumb(&[0xEE12, 0x0A90, 0x4770]);
    for cpu in [Cpu::CortexM4F, Cpu::CortexM7F] {
        let r = emulate::run(
            &read_s5,
            "f",
            &sig(&[], ValType::I32),
            &[],
            &EmuConfig::new(cpu),
        )
        .expect("emulates");
        assert_eq!(r.cpu_model_readback, cpu.model_id(), "{cpu:?}");
        assert_eq!(
            r.outcome,
            EmuOutcome::Values(vec![i(0xFEED_FACE)]),
            "{cpu:?}"
        );
    }
    // The plain M4 leaves the VFP registers as unicorn made them, zero.
    // (unicorn 2.1.5 runs a VFP instruction on its M4 model whether or not
    // CPACR was written, so this is the poisoning that is shown here, not an
    // FPU-off fault.)
    assert_eq!(
        run(&read_s5, &sig(&[], ValType::I32), Cpu::CortexM4),
        Ok(EmuOutcome::Values(vec![i(0)]))
    );
    // `vmov s0, r0 ; bx lr` (EE00 0A10): r0 holds the i32 argument, and the
    // f32 result is read from s0, not r0.
    let to_s0 = thumb(&[0xEE00, 0x0A10, 0x4770]);
    let r = emulate::run(
        &to_s0,
        "f",
        &sig(&[ValType::I32], ValType::F32),
        &[i(1.5f32.to_bits())],
        &EmuConfig::new(Cpu::CortexM4F),
    )
    .expect("emulates");
    assert_eq!(r.outcome, EmuOutcome::Values(vec![f(1.5)]));
    // `bx lr` alone: the result is whatever s0 held (POISON), not r0.
    let r = emulate::run(
        &thumb(&[0x4770]),
        "f",
        &sig(&[ValType::I32], ValType::F32),
        &[i(1.5f32.to_bits())],
        &EmuConfig::new(Cpu::CortexM4F),
    )
    .expect("emulates");
    assert_eq!(
        r.outcome,
        EmuOutcome::Values(vec![WasmValue::F32(0xFEED_FACE)])
    );
    // An f64 result is all of d0: `bx lr` alone.
    assert_eq!(
        run(&thumb(&[0x4770]), &sig(&[], ValType::F64), Cpu::CortexM7F),
        Ok(EmuOutcome::Values(vec![WasmValue::F64(
            0xFEED_FACE_FEED_FACE
        )]))
    );
    // A float parameter is refused on the VFP cores, and a float result on
    // the plain M4.
    assert!(matches!(
        emulate::run(
            &thumb(&[0x4770]),
            "f",
            &sig(&[ValType::F32], ValType::I32),
            &[f(1.0)],
            &EmuConfig::new(Cpu::CortexM4F)
        ),
        Err(EmuError::FloatAbi { .. })
    ));
    assert!(matches!(
        run(&thumb(&[0x4770]), &sig(&[], ValType::F32), Cpu::CortexM4),
        Err(EmuError::FloatAbi { .. })
    ));
}
