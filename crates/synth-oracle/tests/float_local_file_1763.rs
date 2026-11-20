//! Refs #1763: on AArch64 a float local lives in the FP register file.
//!
//! The A64 selector keeps every non-param local in an 8-byte stack slot and
//! used to read each one into a GP temp, whatever its type. A value-stack
//! entry carries its register file, and the epilogue picks the result
//! register from it, so `(result f64) (local f64) local.get 1` wrote x0 and
//! never v0: the caller read whatever d0 held, often the first float
//! parameter. `f(2.5)` returned 2.5 where wasm returns 0.
//!
//! The same GP entry reached a `call` as an INTEGER argument (the callee
//! reads v0), and it made every other use of a float local a refusal: a
//! float operator refused the GP operand, `local.set` refused the FP one.
//!
//! Every shape below runs on kiln (the reference) and, as the machine code
//! synth emitted, under unicorn on:
//!
//! - cortex-a53, `-b aarch64 --relocatable` (the backend the issue is about):
//!   all shapes, float parameters included;
//! - cortex-m7dp (double-precision VFP): the shapes without a float
//!   parameter;
//! - cortex-m4f (single-precision VFP): the f32 shapes without a float
//!   parameter.
//!
//! The two ARM legs are the twin check (the harness sets up no float
//! ARGUMENT on ARM, so the float-parameter shapes are A64-only). ARM reads
//! the declared float locals (#1594) and was right on every shape here
//! before the fix.
//!
//! The emulator poisons d0-d7 where no argument occupies them, x8-x18 and
//! d16-d31, so a result register nothing writes is never wasm's zero.
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary; with a
//! pre-fix one the A64 leg reds on 87 of its 94 cases (30 wrong values over
//! 9 shapes; 15 shapes refused, 57 cases) and the float call argument
//! compiles. The 7 that agree are the i64 control (4 vectors) and the three
//! vectors whose first float parameter is 0.0, which is what v0 was left
//! holding.

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

/// What a shape needs from the core it runs on.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Need {
    /// f32 only, integer parameters.
    Single,
    /// f64 (possibly f32 too), integer parameters.
    Double,
    /// A float parameter: AArch64 only.
    FloatParam,
}

/// Parameter lists, which select the argument vectors.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Params {
    I,
    D,
    S,
    SD,
}

impl Params {
    fn wat(self) -> &'static str {
        match self {
            Params::I => "i32",
            Params::D => "f64",
            Params::S => "f32",
            Params::SD => "f32 f64",
        }
    }
}

struct Shape {
    name: &'static str,
    need: Need,
    params: Params,
    result: &'static str,
    /// Declared locals; indices start after the parameters.
    locals: &'static str,
    body: &'static str,
}

const fn s(
    name: &'static str,
    need: Need,
    params: Params,
    result: &'static str,
    locals: &'static str,
    body: &'static str,
) -> Shape {
    Shape {
        name,
        need,
        params,
        result,
        locals,
        body,
    }
}

use Need::{Double, FloatParam, Single};
use Params::{D, I, S, SD};

const SHAPES: &[Shape] = &[
    // ---- never written, returned (the defect) ----
    s("ret_f64", Double, I, "f64", "(local f64)", "local.get 1"),
    s("ret_f32", Single, I, "f32", "(local f32)", "local.get 1"),
    // The issue's two modules: a float parameter is left in d0/s0.
    s(
        "issue_f64",
        FloatParam,
        D,
        "f64",
        "(local f64)",
        "local.get 1",
    ),
    s(
        "issue_f32",
        FloatParam,
        S,
        "f32",
        "(local f32)",
        "local.get 1",
    ),
    // Read after other code wrote the neighbouring locals.
    s(
        "after_code_f64",
        Double,
        I,
        "f64",
        "(local i32 f64 i64)",
        "(local.set 1 (i32.mul (local.get 0) (i32.const 3)))
         (local.set 3 (i64.const -1))
         local.get 2",
    ),
    // ---- never written, consumed by an operator (refused before) ----
    s(
        "add_zero_f64",
        Double,
        I,
        "f64",
        "(local f64)",
        "(f64.add (local.get 1) (f64.convert_i32_u (local.get 0)))",
    ),
    s(
        "bits_f64",
        Double,
        I,
        "i64",
        "(local f64)",
        "(i64.reinterpret_f64 (local.get 1))",
    ),
    s(
        "bits_f32",
        Single,
        I,
        "i32",
        "(local f32)",
        "(i32.reinterpret_f32 (local.get 1))",
    ),
    s(
        "eq_zero_f32",
        Single,
        I,
        "i32",
        "(local f32)",
        "(f32.eq (local.get 1) (f32.const 0))",
    ),
    // ---- copied and teed between float locals ----
    s(
        "copy_f64",
        Double,
        I,
        "f64",
        "(local f64 f64)",
        "local.get 2 local.set 1 local.get 1",
    ),
    s(
        "tee_f32",
        Single,
        I,
        "f32",
        "(local f32 f32)",
        "local.get 2 local.tee 1 drop local.get 1",
    ),
    // ---- written, then read (refused before: local.set of an FP operand) ----
    s(
        "written_f64",
        Double,
        I,
        "f64",
        "(local f64)",
        "(local.set 1 (f64.convert_i32_s (local.get 0)))
         (f64.add (local.get 1) (f64.const 0.5))",
    ),
    s(
        "written_f32",
        Single,
        I,
        "f32",
        "(local f32)",
        "(local.set 1 (f32.convert_i32_s (local.get 0)))
         (f32.mul (local.get 1) (f32.const 2))",
    ),
    s(
        "tee_written_f64",
        Double,
        I,
        "f64",
        "(local f64)",
        "(f64.mul (local.tee 1 (f64.convert_i32_u (local.get 0))) (local.get 1))",
    ),
    s(
        "cond_written_f64",
        Double,
        I,
        "f64",
        "(local f64)",
        "(if (local.get 0) (then (local.set 1 (f64.const 2.5)))) local.get 1",
    ),
    s(
        "select_f64",
        Double,
        I,
        "f64",
        "(local f64 f64)",
        "(local.set 2 (f64.const 7.25))
         (select (local.get 1) (local.get 2) (local.get 0))",
    ),
    s(
        "block_result_f32",
        Single,
        I,
        "f32",
        "(local f32)",
        "(block (result f32) local.get 1)",
    ),
    // An f32 written into a slot, an f64 read from its neighbour: the f32
    // store must not reach the f64 slot, nor the reverse.
    s(
        "mixed_widths",
        Double,
        I,
        "f64",
        "(local f32 f64 f32)",
        "(local.set 1 (f32.const -1.5)) (local.set 3 (f32.const -2.5))
         (local.set 2 (f64.convert_i32_s (local.get 0)))
         (f64.add (local.get 2)
           (f64.promote_f32 (f32.add (local.get 1) (local.get 3))))",
    ),
    s(
        "loop_accumulate_f64",
        Double,
        I,
        "f64",
        "(local f64 i32)",
        "(local.set 2 (i32.and (local.get 0) (i32.const 7)))
         (block (loop
           (br_if 1 (i32.eqz (local.get 2)))
           (local.set 1 (f64.add (local.get 1) (f64.const 1.5)))
           (local.set 2 (i32.sub (local.get 2) (i32.const 1)))
           (br 0)))
         local.get 1",
    ),
    // ---- float parameters beside float locals (AArch64 only) ----
    s(
        "param_times_local_f64",
        FloatParam,
        D,
        "f64",
        "(local f64)",
        "(local.set 1 (f64.mul (local.get 0) (f64.const 2)))
         (f64.add (local.get 1) (local.get 0))",
    ),
    s(
        "param_plus_zero_f32",
        FloatParam,
        S,
        "f32",
        "(local f32)",
        "(f32.add (local.get 0) (local.get 1))",
    ),
    s(
        "two_params_two_locals",
        FloatParam,
        SD,
        "f64",
        "(local f32 f64)",
        "(local.set 2 (local.get 0)) (local.set 3 (local.get 1))
         (f64.sub (local.get 3) (f64.promote_f32 (local.get 2)))",
    ),
    s(
        "unwritten_beside_params",
        FloatParam,
        SD,
        "f32",
        "(local f64 f32)",
        "local.get 3",
    ),
    // ---- integer controls ----
    s("i64_ret", Single, I, "i64", "(local i64)", "local.get 1"),
    s(
        "i32_beside_float",
        Single,
        I,
        "i32",
        "(local f32 i32)",
        "(local.set 1 (f32.const -1)) local.get 2",
    ),
];

fn vectors(p: Params) -> Vec<Vec<WasmValue>> {
    let i = WasmValue::I32;
    let d = |v: f64| WasmValue::F64(v.to_bits());
    let f = |v: f32| WasmValue::F32(v.to_bits());
    match p {
        Params::I => [0u32, 1, 5, 0xFFFF_FFFF]
            .iter()
            .map(|&a| vec![i(a)])
            .collect(),
        Params::D => [2.5f64, 0.0, -7.75].iter().map(|&a| vec![d(a)]).collect(),
        Params::S => [2.5f32, 0.0, -7.75].iter().map(|&a| vec![f(a)]).collect(),
        Params::SD => [(2.5f32, 10.0f64), (0.0, 0.0), (-7.75, 1e300)]
            .iter()
            .map(|&(a, b)| vec![f(a), d(b)])
            .collect(),
    }
}

fn module_of(shapes: &[&Shape]) -> Vec<u8> {
    let mut wat = String::from("(module\n");
    for s in shapes {
        wat.push_str(&format!(
            "(func (export \"{}\") (param {}) (result {}) {}\n{})\n",
            s.name,
            s.params.wat(),
            s.result,
            s.locals,
            s.body
        ));
    }
    wat.push(')');
    wat::parse_str(&wat).unwrap_or_else(|e| panic!("WAT: {e}\n{wat}"))
}

struct Leg {
    name: &'static str,
    cpu: Cpu,
    flags: &'static [&'static str],
    runs: &'static [Need],
    /// The leg #1763 was wrong on.
    a64: bool,
}

const A64: &[&str] = &["-b", "aarch64", "--relocatable", "--all-exports"];

const LEGS: &[Leg] = &[
    Leg {
        name: "a64",
        cpu: Cpu::CortexA53,
        flags: A64,
        runs: &[Single, Double, FloatParam],
        a64: true,
    },
    Leg {
        name: "m7dp-relocatable",
        cpu: Cpu::CortexM7F,
        flags: &["--target", "cortex-m7dp", "--relocatable", "--all-exports"],
        runs: &[Single, Double],
        a64: false,
    },
    Leg {
        name: "m4f-relocatable",
        cpu: Cpu::CortexM4F,
        flags: &["--target", "cortex-m4f", "--relocatable", "--all-exports"],
        runs: &[Single],
        a64: false,
    },
];

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("float-local-1763-{}-{n}", std::process::id()));
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
            WasmValue::F32(a) => format!("{:e}f32", f32::from_bits(*a)),
            WasmValue::F64(a) => format!("{:e}f64", f64::from_bits(*a)),
        })
        .collect::<Vec<_>>()
        .join(",")
}

#[test]
fn a_float_local_is_read_and_written_in_the_fp_file() {
    let imports = Imports::new();
    let mut total = 0;
    let mut bad_total = 0;
    let mut a64_cases = 0;
    let mut report = String::new();
    for leg in LEGS {
        let shapes: Vec<&Shape> = SHAPES
            .iter()
            .filter(|s| leg.runs.contains(&s.need))
            .collect();
        let names: Vec<&str> = shapes.iter().map(|s| s.name).collect();
        let wasm = module_of(&shapes);
        // One module for the whole leg. If synth refuses any function of it,
        // fall back to one module per shape, so a refusal of one shape does
        // not hide what the others compute.
        let units: Vec<(&Shape, Unit)> = match build(&wasm, leg.flags, &names) {
            Ok(obj) => shapes
                .iter()
                .map(|s| (*s, Ok((wasm.clone(), obj.clone()))))
                .collect(),
            Err(_) => shapes
                .iter()
                .map(|s| {
                    let w = module_of(&[s]);
                    let r = build(&w, leg.flags, &[s.name]);
                    (*s, r.map(|o| (w, o)))
                })
                .collect(),
        };
        let cfg = EmuConfig::new(leg.cpu);
        let mut cases: Vec<Case> = Vec::new();
        let mut refused: Vec<&str> = Vec::new();
        let mut refused_cases = 0;
        for (s, unit) in &units {
            let vs = vectors(s.params);
            let (w, obj) = match unit {
                Ok(u) => u,
                Err(e) => {
                    let why = e
                        .lines()
                        .find(|l| l.contains("skipping function"))
                        .unwrap_or("no reason on stderr");
                    report.push_str(&format!("  REFUSED {} {}: {why}\n", leg.name, s.name));
                    refused.push(s.name);
                    refused_cases += vs.len();
                    continue;
                }
            };
            for args in vs {
                let c = run_case(w, obj, s.name, &args, FUEL, &imports, &cfg).unwrap_or_else(|e| {
                    panic!("{} {}{args:?}: harness error {e:?}", leg.name, s.name)
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
        let n = cases.len() + refused_cases;
        let bad: usize = per.values().map(|p| p.0).sum::<usize>() + refused_cases;
        let wrong: Vec<String> = per
            .iter()
            .filter(|(_, p)| p.0 > 0)
            .map(|(n, p)| format!("{n} {}/{}", p.0, p.1))
            .collect();
        eprintln!(
            "ORACLE float-local-1763 [{}]: {} of {} wrong; wrong values: [{}]; refused: [{}]",
            leg.name,
            bad,
            n,
            wrong.join(", "),
            refused.join(", ")
        );
        if leg.a64 {
            a64_cases += n;
        }
        total += n;
        bad_total += bad;
    }
    eprint!("{report}");
    // EXACT literals: shrinking the shapes, the vectors or the legs reds.
    assert_eq!(total, 202, "case count moved");
    assert_eq!(a64_cases, 94, "A64 case count moved");
    assert_eq!(
        bad_total, 0,
        "{bad_total} of {total} cases disagree with kiln"
    );
    eprintln!(
        "ORACLE float-local-1763: {total} cases agree across {} legs",
        LEGS.len()
    );
}

/// A float local passed to a `call`. AArch64 does not marshal FP arguments
/// and says so. Before the fix the local was a GP entry, so the check that
/// refuses an FP argument did not see one: the call compiled, with the
/// local's bits in x0 for a callee that reads v0. A function with a call
/// carries a relocation this harness does not run, so the pin is the
/// refusal itself.
#[test]
fn a64_refuses_a_float_local_as_a_call_argument() {
    let wat = r#"(module
        (func $g (param f64) (result i32) (i32.trunc_sat_f64_s (local.get 0)))
        (func (export "f") (param i32) (result i32) (local f64)
          (call $g (local.get 1))))"#;
    let wasm = wat::parse_str(wat).unwrap();
    let dir = scratch();
    let input = dir.join("m.wasm");
    std::fs::write(&input, &wasm).unwrap();
    let run = compile(&input, A64, &dir.join("m.o")).expect("synth runs");
    assert!(
        !run.status.success(),
        "a float local reached a call as an integer argument (compiled, exit 0)"
    );
    assert!(
        run.stderr.contains("argument 0 is a float"),
        "refused for another reason: {}",
        run.stderr
    );
    eprintln!("ORACLE float-local-1763 a64 call argument: refused (argument 0 is a float)");
}

/// The words main 6641efec emitted for the issue function on `-b aarch64`.
/// Frozen, so this stays red-capable after the fix.
const PRE_FIX_ISSUE_FN: &[u32] = &[
    0xd100_43ff, // sub sp, sp, #0x10
    0xf900_03ff, // str xzr, [sp]
    0xf940_03e9, // ldr x9, [sp]
    0xaa09_03e0, // mov x0, x9
    0x9100_43ff, // add sp, sp, #0x10
    0xd65f_03c0, // ret
];

/// POTENCY: the harness sees the defect. The frozen pre-fix words never
/// write v0, so the f64 parameter comes back as the result, and with an
/// integer parameter the result is the poison d0 was given.
#[test]
fn frozen_pre_fix_words_are_judged_wrong() {
    let text: Vec<u8> = PRE_FIX_ISSUE_FN
        .iter()
        .flat_map(|w| w.to_le_bytes())
        .collect();
    let obj = |name: &str| CompiledObject {
        path: Path::new("frozen-pre-fix-1763").to_path_buf(),
        machine: Machine::AArch64,
        funcs: BTreeMap::from([(
            name.to_string(),
            FuncSym {
                offset: 0,
                size: text.len() as u64,
                thumb: false,
                global: true,
            },
        )]),
        text: text.clone(),
        text_relocs: Vec::new(),
        relocs: Vec::new(),
        relocatable: true,
    };
    let find = |n: &str| SHAPES.iter().find(|s| s.name == n).unwrap();
    let cfg = EmuConfig::new(Cpu::CortexA53);
    let d = |v: f64| WasmValue::F64(v.to_bits());

    let wasm = module_of(&[find("issue_f64")]);
    let c = run_case(
        &wasm,
        &obj("issue_f64"),
        "issue_f64",
        &[d(2.5)],
        FUEL,
        &Imports::new(),
        &cfg,
    )
    .expect("runs");
    assert_eq!(c.reference, RefOutcome::Values(vec![d(0.0)]));
    assert_eq!(c.emulator, EmuOutcome::Values(vec![d(2.5)]));
    assert!(matches!(c.verdict, Verdict::Disagree(_)), "{:?}", c.verdict);

    let wasm = module_of(&[find("ret_f64")]);
    let c = run_case(
        &wasm,
        &obj("ret_f64"),
        "ret_f64",
        &[WasmValue::I32(5)],
        FUEL,
        &Imports::new(),
        &cfg,
    )
    .expect("runs");
    assert_eq!(c.reference, RefOutcome::Values(vec![d(0.0)]));
    assert_eq!(
        c.emulator,
        EmuOutcome::Values(vec![WasmValue::F64(0xFEED_FACE_FEED_FACE)])
    );
    assert!(!c.verdict.is_agree());
}
