//! Refs #1754: `select` on the ARM direct selector must not write its result
//! into a register that still holds a live operand-stack value.
//!
//! `local.get` of a register-homed parameter pushes the HOME REGISTER. The
//! in-place form of the i32 `select` reuses the register of its second value
//! (`val2`) as the destination. Before the fix the only liveness it asked
//! about was "is there a later `local.get` of this parameter", so with
//! `p0 + select(p2, p0, p1)` the select overwrote r0 while the first operand
//! of the `add` was still r0 on the stack: `f(5, 1, 7)` returned 14, not 12.
//!
//! Every shape below runs on kiln (the reference) and, as the machine code
//! synth emitted, under unicorn on:
//!
//! - cortex-m4 and cortex-m3 `--relocatable` (always the direct selector);
//! - cortex-m4 DEFAULT flags, with a written i64 local in every function,
//!   which routes the function to the direct selector;
//! - cortex-m4 `--no-optimize` (the direct selector, self-contained image);
//! - cortex-m4 default flags WITHOUT the i64 local: the optimized path, the
//!   paired control, which was never wrong.
//!
//! The routing of the default-flags leg is witnessed, not assumed: see
//! `default_flags_leg_routes_to_the_direct_selector`.
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary; run it with
//! a pre-fix binary to see the red half (128 of 880 cases disagree).

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

/// One function shape: its name, parameter list, result type and body. The
/// body may use local index `params.len()` only through `ROUTE` below.
struct Shape {
    name: &'static str,
    params: &'static str,
    result: &'static str,
    /// Extra locals the body itself declares (before the routing local).
    locals: &'static str,
    body: &'static str,
    kind: Kind,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    /// `(i32, i32, i32) -> i32`.
    I3,
    /// `(i32, i32) -> i32`.
    I2,
    /// `(i64, i32) -> i64`.
    L1I1,
    /// `(i32, i64) -> i64`.
    I1L1,
    /// `(i64, i64) -> i64`.
    L2,
}

const fn s3(name: &'static str, body: &'static str) -> Shape {
    Shape {
        name,
        params: "i32 i32 i32",
        result: "i32",
        locals: "",
        body,
        kind: Kind::I3,
    }
}

/// The issue module, then the triage's sibling shapes (`a b c d k`: 5 shapes
/// x 3 vectors are "the 15 sibling vectors"), its three not-affected shapes
/// (`e g h`), further aliasing shapes, and the i64-select siblings.
const SHAPES: &[Shape] = &[
    // The issue: val2 = p0, and p0 is still stacked under the select.
    s3(
        "f",
        "(i32.add (local.get 0) (select (local.get 2) (local.get 0) (local.get 1)))",
    ),
    s3(
        "a",
        "(i32.sub (local.get 0) (select (local.get 2) (local.get 0) (local.get 1)))",
    ),
    s3(
        "b",
        "(i32.sub (local.get 1) (select (local.get 0) (local.get 1) (local.get 2)))",
    ),
    // The stacked parameter is val1, not val2: never wrong.
    s3(
        "c",
        "(i32.sub (local.get 0) (select (local.get 0) (local.get 2) (local.get 1)))",
    ),
    s3(
        "d",
        "(i32.sub (local.get 0) (i32.sub (local.get 1)
           (select (local.get 2) (local.get 0) (local.get 1))))",
    ),
    s3(
        "k",
        "(i32.sub (local.get 0) (select (i32.const 9) (local.get 0) (local.get 1)))",
    ),
    Shape {
        name: "e",
        params: "i32 i32",
        result: "i32",
        locals: "",
        body: "(i32.sub (local.get 0)
                 (i32.wrap_i64 (i64.extend8_s (i64.extend_i32_u (local.get 0)))))",
        kind: Kind::I2,
    },
    Shape {
        name: "g",
        params: "i32 i32",
        result: "i32",
        locals: "",
        body: "(i32.sub (local.get 0) (i32.extend8_s (local.get 0)))",
        kind: Kind::I2,
    },
    Shape {
        name: "h",
        params: "i32 i32",
        result: "i32",
        locals: "",
        body: "(i32.sub (local.get 0) (i32.clz (local.get 0)))",
        kind: Kind::I2,
    },
    // Two selects, each with val2 = p0, under two stacked copies of p0.
    s3(
        "u",
        "(i32.sub (local.get 0) (i32.xor (local.get 0)
           (select (select (local.get 2) (local.get 0) (local.get 1))
                   (local.get 0) (local.get 2))))",
    ),
    // val2 is the stacked parameter AND the condition.
    s3(
        "v",
        "(i32.sub (local.get 1) (select (local.get 2) (local.get 1) (local.get 1)))",
    ),
    // The alias is a non-parameter local.
    Shape {
        name: "t",
        params: "i32 i32 i32",
        result: "i32",
        locals: "(local i32)",
        body: "(local.set 3 (i32.mul (local.get 0) (i32.const 3)))
               (i32.sub (local.get 3) (select (local.get 2) (local.get 3) (local.get 1)))",
        kind: Kind::I3,
    },
    // The #209 clamp, `(x > k) ? k : x`: no alias remains, in-place is right.
    s3(
        "clamp",
        "(select (i32.const 100) (local.get 0) (i32.gt_s (local.get 0) (i32.const 100)))",
    ),
    // i64 select with the i64 parameter (val2) still stacked.
    Shape {
        name: "s64a",
        params: "i64 i32",
        result: "i64",
        locals: "",
        body: "(i64.sub (local.get 0) (select (i64.const 9) (local.get 0) (local.get 1)))",
        kind: Kind::L1I1,
    },
    Shape {
        name: "s64b",
        params: "i32 i64",
        result: "i64",
        locals: "",
        body: "(i64.sub (local.get 1)
                 (select (i64.extend_i32_u (local.get 0)) (local.get 1) (local.get 0)))",
        kind: Kind::I1L1,
    },
    Shape {
        name: "s64c",
        params: "i64 i64",
        result: "i64",
        locals: "",
        body: "(i64.sub (local.get 0)
                 (select (local.get 1) (local.get 0) (i64.eqz (local.get 1))))",
        kind: Kind::L2,
    },
    // The i64 parameter is val1.
    Shape {
        name: "s64d",
        params: "i64 i32",
        result: "i64",
        locals: "",
        body: "(i64.sub (local.get 0) (select (local.get 0) (i64.const 9) (local.get 1)))",
        kind: Kind::L1I1,
    },
];

/// The triage's three vectors first (so "the 15 sibling vectors" are
/// `a b c d k` x `V3[..3]`), then edge values.
const V3: &[[u32; 3]] = &[
    [5, 1, 7],
    [5, 0, 7],
    [1, 2, 3],
    [0, 0, 0],
    [0xFFFF_FFFF, 1, 0x8000_0000],
    [7, 0x8000_0000, 5],
    [0xDEAD_BEEF, 0, 1],
    [3, 5, 0],
];

const V64: &[u64] = &[
    0,
    5,
    0xFFFF_FFFF,
    0x1_0000_0000,
    0x8000_0000_0000_0000,
    0xDEAD_BEEF_0BAD_F00D,
];

fn vectors(kind: Kind) -> Vec<Vec<WasmValue>> {
    let i = WasmValue::I32;
    let l = WasmValue::I64;
    match kind {
        Kind::I3 => V3.iter().map(|v| vec![i(v[0]), i(v[1]), i(v[2])]).collect(),
        Kind::I2 => V3.iter().map(|v| vec![i(v[0]), i(v[2])]).collect(),
        Kind::L1I1 => V64
            .iter()
            .flat_map(|&a| [0u32, 1, 0x8000_0000].map(|c| vec![l(a), i(c)]))
            .collect(),
        Kind::I1L1 => V64
            .iter()
            .flat_map(|&a| [0u32, 1, 0x8000_0000].map(|c| vec![i(c), l(a)]))
            .collect(),
        Kind::L2 => V64
            .iter()
            .flat_map(|&a| [0u64, 7, 0x1_0000_0000].map(|b| vec![l(a), l(b)]))
            .collect(),
    }
}

/// The module. With `routed`, every function also declares an i64 local and
/// WRITES it: a written i64 local is what sends a function to the direct
/// selector on default flags (an unused one does not).
fn module(routed: bool) -> Vec<u8> {
    let mut wat = String::from("(module\n");
    for s in SHAPES {
        let n_params = s.params.split_whitespace().count();
        let n_locals = s.locals.matches("(local").count();
        let (decl, set) = if routed {
            (
                " (local i64)".to_string(),
                format!("(local.set {} (i64.const 1))\n", n_params + n_locals),
            )
        } else {
            (String::new(), String::new())
        };
        wat.push_str(&format!(
            "(func (export \"{}\") (param {}) (result {}) {}{}\n{}{})\n",
            s.name, s.params, s.result, s.locals, decl, set, s.body
        ));
    }
    wat.push(')');
    wat::parse_str(&wat).unwrap_or_else(|e| panic!("WAT: {e}\n{wat}"))
}

struct Leg {
    name: &'static str,
    cpu: Cpu,
    flags: &'static [&'static str],
    routed: bool,
    /// The direct selector lowers this leg (the legs #1754 was wrong on).
    direct: bool,
}

const M4_DEFAULT: &[&str] = &["--target", "cortex-m4", "--all-exports"];
const M4_NO_OPT: &[&str] = &["--target", "cortex-m4", "--all-exports", "--no-optimize"];

const LEGS: &[Leg] = &[
    Leg {
        name: "m4-relocatable",
        cpu: Cpu::CortexM4,
        flags: &["--target", "cortex-m4", "--relocatable", "--all-exports"],
        routed: false,
        direct: true,
    },
    Leg {
        name: "m3-relocatable",
        cpu: Cpu::CortexM3,
        flags: &["--target", "cortex-m3", "--relocatable", "--all-exports"],
        routed: false,
        direct: true,
    },
    Leg {
        name: "m4-default-routed",
        cpu: Cpu::CortexM4,
        flags: M4_DEFAULT,
        routed: true,
        direct: true,
    },
    Leg {
        name: "m4-no-optimize",
        cpu: Cpu::CortexM4,
        flags: M4_NO_OPT,
        routed: false,
        direct: true,
    },
    Leg {
        name: "m4-default-optimized (control)",
        cpu: Cpu::CortexM4,
        flags: M4_DEFAULT,
        routed: false,
        direct: false,
    },
];

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("select-1754-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn build(wasm: &[u8], flags: &[&str], what: &str) -> CompiledObject {
    let dir = scratch();
    let input = dir.join("m.wasm");
    std::fs::write(&input, wasm).unwrap();
    let run = compile(&input, flags, &dir.join("m.o")).expect("synth runs");
    assert!(run.status.success(), "{what}: synth: {}", run.stderr);
    let obj = run.object.expect("object parsed");
    for s in SHAPES {
        assert!(
            obj.function_bytes(s.name).is_some_and(|b| !b.is_empty()),
            "{what}: no bytes for `{}`",
            s.name
        );
    }
    obj
}

fn run_leg(leg: &Leg) -> Vec<Case> {
    let wasm = module(leg.routed);
    let obj = build(&wasm, leg.flags, leg.name);
    let cfg = EmuConfig::new(leg.cpu);
    let imports = Imports::new();
    let mut cases = Vec::new();
    for s in SHAPES {
        for args in vectors(s.kind) {
            let c = run_case(&wasm, &obj, s.name, &args, FUEL, &imports, &cfg)
                .unwrap_or_else(|e| panic!("{} {}{args:?}: harness error {e:?}", leg.name, s.name));
            cases.push(c);
        }
    }
    cases
}

fn show(v: &[WasmValue]) -> String {
    v.iter()
        .map(|x| match x {
            WasmValue::I32(a) => format!("{}", *a as i32),
            WasmValue::I64(a) => format!("{}", *a as i64),
            other => format!("{other:?}"),
        })
        .collect::<Vec<_>>()
        .join(",")
}

#[test]
fn select_never_overwrites_a_stacked_alias() {
    let mut total = 0;
    let mut bad_total = 0;
    let mut direct_cases = 0;
    let mut report = String::new();
    for leg in LEGS {
        let cases = run_leg(leg);
        // Every case returned a VALUE on the reference: a sweep of traps
        // would agree without comparing a single select result.
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
        let bad: usize = per.values().map(|p| p.0).sum();
        // The triage's 15: shapes a b c d k on the first three vectors.
        let sib15 = cases
            .iter()
            .filter(|c| ["a", "b", "c", "d", "k"].contains(&c.export.as_str()))
            .filter(|c| {
                V3[..3]
                    .iter()
                    .any(|v| c.args == [0, 1, 2].map(|j| WasmValue::I32(v[j])))
            })
            .collect::<Vec<_>>();
        assert_eq!(sib15.len(), 15, "{}: the 15 sibling vectors", leg.name);
        let sib_bad = sib15.iter().filter(|c| !c.verdict.is_agree()).count();
        let wrong: Vec<String> = per
            .iter()
            .filter(|(_, p)| p.0 > 0)
            .map(|(n, p)| format!("{n} {}/{}", p.0, p.1))
            .collect();
        eprintln!(
            "ORACLE select-1754 [{}]: {} of {} wrong; sibling vectors {} of 15 wrong; shapes: [{}]",
            leg.name,
            bad,
            cases.len(),
            sib_bad,
            wrong.join(", ")
        );
        if !leg.direct {
            assert_eq!(bad, 0, "{}: the optimized-path control is wrong", leg.name);
        } else {
            direct_cases += cases.len();
        }
        total += cases.len();
        bad_total += bad;
    }
    eprint!("{report}");
    // EXACT literals: shrinking the shapes, the vectors or the legs reds.
    assert_eq!(total, 880, "case count moved");
    assert_eq!(direct_cases, 704, "direct-selector case count moved");
    assert_eq!(
        bad_total, 0,
        "{bad_total} of {total} cases disagree with kiln"
    );
    eprintln!(
        "ORACLE select-1754: {total} cases agree across {} legs",
        LEGS.len()
    );
}

/// The default-flags leg is only evidence about the direct selector if the
/// written i64 local really routes each function there. Witness: on default
/// flags the routed module's function bytes EQUAL the `--no-optimize` bytes
/// (the direct selector by construction), while the un-routed issue function
/// DIFFERS between the two (so the equality is not "the flags do nothing").
#[test]
fn default_flags_leg_routes_to_the_direct_selector() {
    let routed = module(true);
    let d = build(&routed, M4_DEFAULT, "routed default");
    let n = build(&routed, M4_NO_OPT, "routed no-optimize");
    for s in SHAPES {
        assert_eq!(
            d.function_bytes(s.name),
            n.function_bytes(s.name),
            "`{}`: default flags did not route to the direct selector",
            s.name
        );
    }
    let plain = module(false);
    let d = build(&plain, M4_DEFAULT, "plain default");
    let n = build(&plain, M4_NO_OPT, "plain no-optimize");
    assert_ne!(
        d.function_bytes("f"),
        n.function_bytes("f"),
        "`f` without the i64 local is no longer lowered differently by the \
         optimized path: the routing witness above proves nothing"
    );
}

/// The bytes main 6641efec emitted for the issue function on
/// `--target cortex-m4 --relocatable`: `cmp r1,#0; it ne; movne r0,r2;
/// adds r3,r0,r0; mov r0,r3`. Frozen, so this stays red-capable after the fix.
const PRE_FIX_ISSUE_FN: &[u8] = &[
    0x10, 0xb5, // push {r4, lr}
    0x00, 0x29, // cmp r1, #0
    0x18, 0xbf, // it ne
    0x10, 0x46, // movne r0, r2
    0x03, 0x18, // adds r3, r0, r0
    0x18, 0x46, // mov r0, r3
    0x10, 0xbd, // pop {r4, pc}
];

/// POTENCY: the harness sees the defect. The frozen pre-fix bytes return 14
/// for `f(5, 1, 7)` where kiln returns 12, and agree when the condition is 0.
#[test]
fn frozen_pre_fix_bytes_are_judged_wrong() {
    let wasm = module(false);
    let obj = CompiledObject {
        path: Path::new("frozen-pre-fix-1754").to_path_buf(),
        machine: Machine::Arm,
        text: PRE_FIX_ISSUE_FN.to_vec(),
        funcs: BTreeMap::from([(
            "f".to_string(),
            FuncSym {
                offset: 0,
                size: PRE_FIX_ISSUE_FN.len() as u64,
                thumb: true,
                global: true,
            },
        )]),
        text_relocs: Vec::new(),
    };
    let cfg = EmuConfig::new(Cpu::CortexM4);
    let i = WasmValue::I32;
    let run = |args: [u32; 3]| {
        run_case(&wasm, &obj, "f", &args.map(i), FUEL, &Imports::new(), &cfg).expect("runs")
    };
    let c = run([5, 1, 7]);
    assert_eq!(c.reference, RefOutcome::Values(vec![i(12)]));
    assert_eq!(c.emulator, EmuOutcome::Values(vec![i(14)]));
    assert!(matches!(c.verdict, Verdict::Disagree(_)), "{:?}", c.verdict);
    let c = run([1, 2, 3]);
    assert_eq!(c.reference, RefOutcome::Values(vec![i(4)]));
    assert_eq!(c.emulator, EmuOutcome::Values(vec![i(6)]));
    assert!(!c.verdict.is_agree());
    let c = run([5, 0, 7]);
    assert_eq!(c.emulator, EmuOutcome::Values(vec![i(10)]));
    assert!(c.verdict.is_agree());
}
