//! RQ-91-ORACLEKILN (Refs #1741): the first oracle on the Rust harness.
//!
//! A small embedded probe set (i32 arithmetic, compares, control flow, i64
//! results, traps) is compiled by synth for cortex-m3 AND rv32imac
//! (`--relocatable`), and every probe × vector runs on kiln and on unicorn.
//! Every case is required to AGREE. Then four potency legs show the gate can fail:
//!
//! 1. a planted wrong REFERENCE (kiln runs `i32.sub` where synth compiled
//!    `i32.add`) reds;
//! 2. a planted illegal INSTRUCTION in the compiled bytes reds;
//! 3. dropping the HIGH WORD of an i64 result reds;
//! 4. a budget overrun is never a trap: kiln out of fuel and unicorn out of
//!    instructions are each `Budget`, and no pairing with a trap agrees.
//!
//! Needs `--features exec` (kiln + unicorn). `SYNTH` may name a prebuilt
//! binary; otherwise the test builds `synth-cli`.

#![cfg(feature = "exec")]

use std::path::PathBuf;

use synth_oracle::compare::{EmuOutcome, RefOutcome, TrapClass, Verdict, verdict};
use synth_oracle::emulate::{self, Cpu, EmuConfig};
use synth_oracle::reference::{self, Imports};
use synth_oracle::synth::{CompiledObject, compile};
use synth_oracle::value::{Signature, ValType, WasmValue, export_signature};
use synth_oracle::{Case, run_case};

const FUEL: u64 = 1_000_000;

/// Every probe is call-free (no relocations), takes only i32 params (the RV32
/// selector's i64-PARAM homing is a separate, known defect — see
/// i64_local_roundtrip_1713_differential.py's RV_LEGS note) and returns at
/// most one value.
const PROBES_WAT: &str = r#"
(module
  (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (func (export "sub") (param i32 i32) (result i32) local.get 0 local.get 1 i32.sub)
  (func (export "mul") (param i32 i32) (result i32) local.get 0 local.get 1 i32.mul)
  (func (export "and_or_xor") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.and local.get 0 local.get 1 i32.or i32.xor)
  (func (export "shr_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.shr_s)
  (func (export "shr_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.shr_u)
  (func (export "ne") (param i32 i32) (result i32) local.get 0 local.get 1 i32.ne)
  (func (export "lt_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.lt_s)
  (func (export "ge_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.ge_u)
  (func (export "eqz") (param i32 i32) (result i32) local.get 0 i32.eqz)
  (func (export "select_max") (param i32 i32) (result i32)
    local.get 0 local.get 1 local.get 0 local.get 1 i32.gt_s select)
  (func (export "if_else") (param i32 i32) (result i32)
    local.get 0 if (result i32) local.get 1 i32.const 3 i32.mul
    else local.get 1 i32.const 5 i32.sub end)
  (func (export "loop_sum") (param i32 i32) (result i32) (local i32)
    local.get 0 i32.const 15 i32.and local.set 0
    block loop
      local.get 0 i32.eqz br_if 1
      local.get 2 local.get 0 i32.add local.get 1 i32.xor local.set 2
      local.get 0 i32.const 1 i32.sub local.set 0
      br 0
    end end
    local.get 2)
  (func (export "br_table") (param i32 i32) (result i32)
    block block block
      local.get 0 br_table 0 1 2
    end local.get 1 i32.const 100 i32.add return
    end local.get 1 i32.const 200 i32.add return
    end local.get 1 i32.const 300 i32.add)
  (func (export "i64_mul_wide") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_u local.get 1 i64.extend_i32_u i64.mul)
  (func (export "i64_shl") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_s local.get 1 i64.extend_i32_u i64.shl)
  (func (export "i64_add_sub") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_u i64.const 32 i64.shl local.get 1 i64.extend_i32_s i64.add
    i64.const 0x123456789 i64.sub)
  (func (export "i64_lt_s") (param i32 i32) (result i32)
    local.get 0 i64.extend_i32_s i64.const 32 i64.shl
    local.get 1 i64.extend_i32_s i64.const 32 i64.shl i64.lt_s)
  (func (export "div_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.div_u)
  (func (export "rem_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.rem_u)
  (func (export "trap_if") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.eq if unreachable end local.get 0 local.get 1 i32.sub)
  (func (export "spin") (param i32 i32) (result i32) loop br 0 end i32.const 0)
)
"#;

/// The probes required to agree on every vector. `spin` is the budget probe
/// and is judged separately.
const AGREE_PROBES: &[&str] = &[
    "add",
    "sub",
    "mul",
    "and_or_xor",
    "shr_s",
    "shr_u",
    "ne",
    "lt_s",
    "ge_u",
    "eqz",
    "select_max",
    "if_else",
    "loop_sum",
    "br_table",
    "i64_mul_wide",
    "i64_shl",
    "i64_add_sub",
    "i64_lt_s",
    "div_u",
    "rem_u",
    "trap_if",
];

const VECTORS: &[u32] = &[
    0,
    1,
    2,
    7,
    31,
    32,
    0x7F,
    0x8000,
    0x7FFF_FFFF,
    0x8000_0000,
    0xFFFF_FFFF,
    0xDEAD_BEEF,
];

struct Leg {
    name: &'static str,
    cpu: Cpu,
    flags: &'static [&'static str],
}

const LEGS: &[Leg] = &[
    Leg {
        name: "cortex-m3",
        cpu: Cpu::CortexM3,
        flags: &["--target", "cortex-m3", "--relocatable", "--all-exports"],
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

/// A fresh directory per call, under cargo's per-target scratch space (so it
/// goes with `target/`). Per call, not per process: the tests run in parallel
/// threads and must not write the same input or object file.
fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-oracle-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn wasm() -> Vec<u8> {
    wat::parse_str(PROBES_WAT).expect("probe WAT parses")
}

fn compile_leg(leg: &Leg) -> CompiledObject {
    let dir = scratch();
    let input = dir.join("probes.wasm");
    std::fs::write(&input, wasm()).unwrap();
    let out = dir.join(format!("probes-{}.o", leg.name));
    let run = compile(&input, leg.flags, &out).expect("synth runs");
    assert!(
        run.status.success(),
        "{}: synth compile failed: {}",
        leg.name,
        run.stderr
    );
    let obj = run.object.expect("object parsed");
    for p in AGREE_PROBES.iter().chain(["spin"].iter()) {
        assert!(
            obj.function_bytes(p).is_some_and(|b| !b.is_empty()),
            "{}: no bytes for `{p}` in the symtab",
            leg.name
        );
        assert_eq!(
            obj.relocs_in(p),
            0,
            "{}: `{p}` carries relocations",
            leg.name
        );
    }
    obj
}

fn pairs() -> impl Iterator<Item = [WasmValue; 2]> {
    VECTORS.iter().flat_map(|&a| {
        VECTORS
            .iter()
            .map(move |&b| [WasmValue::I32(a), WasmValue::I32(b)])
    })
}

/// Run every AGREE probe × vector on one leg; return the cases.
fn sweep(wasm_ref: &[u8], obj: &CompiledObject, cpu: Cpu) -> Vec<Case> {
    let cfg = EmuConfig::new(cpu);
    let imports = Imports::new();
    let mut cases = Vec::new();
    for p in AGREE_PROBES {
        for args in pairs() {
            let c = run_case(wasm_ref, obj, p, &args, FUEL, &imports, &cfg)
                .unwrap_or_else(|e| panic!("{p}{args:?}: harness error {e:?}"));
            cases.push(c);
        }
    }
    cases
}

#[test]
fn probes_agree_with_kiln_on_m3_and_rv32() {
    let w = wasm();
    let mut total = 0;
    let mut traps = 0;
    for leg in LEGS {
        let obj = compile_leg(leg);
        let cases = sweep(&w, &obj, leg.cpu);
        let bad: Vec<_> = cases.iter().filter(|c| !c.verdict.is_agree()).collect();
        for c in bad.iter().take(20) {
            eprintln!(
                "{} {}{:?}: {:?}  (ref {:?}, emu {:?})",
                leg.name, c.export, c.args, c.verdict, c.reference, c.emulator
            );
        }
        assert!(
            bad.is_empty(),
            "{}: {} of {} cases do not agree",
            leg.name,
            bad.len(),
            cases.len()
        );
        // NON-VACUITY: every probe ran every vector, and the trap probes
        // trapped on BOTH sides somewhere (an all-values sweep would agree
        // without ever exercising the trap row of the matrix).
        assert_eq!(
            cases.len(),
            AGREE_PROBES.len() * VECTORS.len() * VECTORS.len()
        );
        let leg_traps = cases
            .iter()
            .filter(|c| {
                matches!(c.reference, RefOutcome::Trap { .. })
                    && matches!(c.emulator, EmuOutcome::Trap { .. })
            })
            .count();
        let classes: std::collections::BTreeSet<_> = cases
            .iter()
            .filter_map(|c| match &c.reference {
                RefOutcome::Trap { class, .. } => Some(format!("{class:?}")),
                _ => None,
            })
            .collect();
        eprintln!(
            "{}: {} cases agree ({} trap/trap; kiln trap classes {:?})",
            leg.name,
            cases.len(),
            leg_traps,
            classes
        );
        assert!(classes.contains("IntegerDivideByZero") && classes.contains("Unreachable"));
        // Optional: the reference outcomes as text, for a one-off comparison
        // of kiln against another engine. Not part of the gate.
        if let Some(path) = std::env::var_os("SYNTH_ORACLE_DUMP") {
            use std::fmt::Write as _;
            let mut s = String::new();
            for c in &cases {
                let [WasmValue::I32(a), WasmValue::I32(b)] = c.args[..] else {
                    unreachable!()
                };
                let r = match &c.reference {
                    RefOutcome::Values(v) => format!("{v:?}"),
                    RefOutcome::Trap { class, .. } => format!("trap:{class:?}"),
                    other => format!("{other:?}"),
                };
                writeln!(s, "{} {a} {b} {r}", c.export).unwrap();
            }
            let p = PathBuf::from(path).with_extension(leg.name);
            std::fs::write(p, s).unwrap();
        }
        total += cases.len();
        traps += leg_traps;
    }
    eprintln!(
        "ORACLE kiln-probe: {total} cases agree across {} legs, {traps} trap/trap",
        LEGS.len()
    );
}

#[test]
fn cpu_model_is_read_back() {
    // Every core this harness offers really is the one emulated: the readback
    // equals the request (EmuError::CpuModelMismatch otherwise).
    let w = wasm();
    for leg in LEGS {
        let obj = compile_leg(leg);
        let sig = export_signature(&w, "add").unwrap();
        let r = emulate::run(
            &obj,
            "add",
            &sig,
            &[WasmValue::I32(2), WasmValue::I32(3)],
            &EmuConfig::new(leg.cpu),
        )
        .expect("emulates");
        assert_eq!(r.cpu_model_readback, leg.cpu.model_id());
        assert_eq!(r.outcome, EmuOutcome::Values(vec![WasmValue::I32(5)]));
    }
    // The M-class models: M0 and M4 also read back (ARM object needed).
    let obj = compile_leg(&LEGS[0]);
    let sig = export_signature(&w, "add").unwrap();
    for cpu in [Cpu::CortexM0, Cpu::CortexM4] {
        let r = emulate::run(
            &obj,
            "add",
            &sig,
            &[WasmValue::I32(2), WasmValue::I32(3)],
            &EmuConfig::new(cpu),
        )
        .expect("emulates");
        assert_eq!(r.cpu_model_readback, cpu.model_id(), "{cpu:?}");
    }
}

// ---------------------------------------------------------------- potency --

#[test]
fn potency_planted_wrong_reference_reds() {
    // kiln runs `add` as SUB; synth compiled the real `add`.
    let planted = PROBES_WAT.replacen(
        "(func (export \"add\") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)",
        "(func (export \"add\") (param i32 i32) (result i32) local.get 0 local.get 1 i32.sub)",
        1,
    );
    assert_ne!(planted, PROBES_WAT, "the plant must change the module");
    let w = wat::parse_str(&planted).unwrap();
    for leg in LEGS {
        let obj = compile_leg(leg);
        let cfg = EmuConfig::new(leg.cpu);
        let disagree = pairs()
            .filter(|args| {
                matches!(
                    run_case(&w, &obj, "add", args, FUEL, &Imports::new(), &cfg)
                        .unwrap()
                        .verdict,
                    Verdict::Disagree(_)
                )
            })
            .count();
        eprintln!(
            "{}: planted sub-for-add: {disagree} disagreements",
            leg.name
        );
        // add == sub exactly when b is 0 or 0x80000000.
        let expected = VECTORS.len() * (VECTORS.len() - 2);
        assert_eq!(disagree, expected, "{}", leg.name);
    }
}

#[test]
fn potency_planted_illegal_instruction_reds() {
    let w = wasm();
    let sig = export_signature(&w, "add").unwrap();
    let args = [WasmValue::I32(2), WasmValue::I32(3)];
    // ARM: 0xFFFF 0xFFFF is a 32-bit Thumb encoding in the undefined space,
    // not UDF. RV32: 0xFFFFFFFF is a reserved (>32-bit-length) encoding, not
    // ebreak/unimp. Also a NON-trap fault: BKPT on ARM, ecall on RV32.
    for leg in LEGS {
        let obj = compile_leg(leg);
        let off = obj.func("add").unwrap().offset as usize;
        let plants: Vec<(&str, Vec<u8>)> = match leg.cpu {
            Cpu::Rv32Imac => vec![
                ("reserved", vec![0xFF, 0xFF, 0xFF, 0xFF]),
                ("ecall", 0x0000_0073u32.to_le_bytes().to_vec()),
                (
                    "fadd.s (no F on E31)",
                    0x0000_0053u32.to_le_bytes().to_vec(),
                ),
            ],
            _ => vec![
                ("undefined", vec![0xFF, 0xFF, 0xFF, 0xFF]),
                ("bkpt", vec![0x00, 0xBE, 0x00, 0xBE]),
                ("vadd.f32 (no FPU on M3)", vec![0x30, 0xEE, 0x00, 0x0A]),
            ],
        };
        for (what, bytes) in plants {
            let mut bad = obj.clone();
            bad.text[off..off + bytes.len()].copy_from_slice(&bytes);
            let e = emulate::run(&bad, "add", &sig, &args, &EmuConfig::new(leg.cpu)).unwrap();
            let r = reference::run(&w, "add", &args, FUEL, &Imports::new()).unwrap();
            let v = verdict(&r.outcome, &e.outcome);
            eprintln!("{}: planted {what}: {:?} -> {v:?}", leg.name, e.outcome);
            assert!(
                matches!(e.outcome, EmuOutcome::Illegal { .. }),
                "{}: planted {what} is not ILLEGAL: {:?}",
                leg.name,
                e.outcome
            );
            assert!(matches!(v, Verdict::Disagree(_)));
        }
        // CONTROL: every trap idiom IS a trap, at the first instruction and at
        // a later one (so the leg above is not ILLEGAL for every fault, and the
        // reported fault PC is the idiom's own on each stop path).
        let idioms: Vec<(&str, Vec<u8>)> = match leg.cpu {
            Cpu::Rv32Imac => vec![
                ("ebreak", 0x0010_0073u32.to_le_bytes().to_vec()),
                ("c.ebreak", vec![0x02, 0x90]),
                ("unimp", 0xC000_1073u32.to_le_bytes().to_vec()),
                ("c.unimp", vec![0x00, 0x00]),
            ],
            _ => vec![
                ("udf", vec![0x00, 0xDE]),
                ("udf.w", vec![0xF0, 0xF7, 0x00, 0xA0]),
            ],
        };
        for (what, idiom) in idioms {
            for at in [0usize, 4] {
                let mut t = obj.clone();
                let o = off + at;
                t.text[o..o + idiom.len()].copy_from_slice(&idiom);
                let e = emulate::run(&t, "add", &sig, &args, &EmuConfig::new(leg.cpu)).unwrap();
                let want = emulate::TEXT_BASE + o as u64;
                assert!(
                    matches!(e.outcome, EmuOutcome::Trap { pc, .. } if pc == want),
                    "{}: control {what}@+{at}: {:?} (want a trap at 0x{want:x})",
                    leg.name,
                    e.outcome
                );
            }
        }
    }
}

#[test]
fn potency_dropped_i64_high_word_reds() {
    let w = wasm();
    let i64_probes = ["i64_mul_wide", "i64_shl", "i64_add_sub"];
    for leg in LEGS {
        let obj = compile_leg(leg);
        let cfg = EmuConfig::new(leg.cpu);
        let (mut agree_full, mut red_dropped, mut nonzero_hi) = (0, 0, 0);
        for p in i64_probes {
            let sig: Signature = export_signature(&w, p).unwrap();
            assert_eq!(sig.results, vec![ValType::I64]);
            for args in pairs() {
                let c = run_case(&w, &obj, p, &args, FUEL, &Imports::new(), &cfg).unwrap();
                assert!(c.verdict.is_agree(), "{p}{args:?}: {:?}", c.verdict);
                agree_full += 1;
                let EmuOutcome::Values(v) = &c.emulator else {
                    panic!("{p}: not a value")
                };
                let WasmValue::I64(full) = v[0] else {
                    panic!("{p}: not i64")
                };
                // The planted defect: a harness (or a selector) that keeps
                // only the low word.
                let dropped = EmuOutcome::Values(vec![WasmValue::I64(full & 0xFFFF_FFFF)]);
                if full >> 32 != 0 {
                    nonzero_hi += 1;
                    assert!(
                        matches!(verdict(&c.reference, &dropped), Verdict::Disagree(_)),
                        "{p}{args:?}: dropping the high word of 0x{full:x} still agrees"
                    );
                    red_dropped += 1;
                }
            }
        }
        eprintln!(
            "{}: i64 high word: {agree_full} agree in full, {red_dropped} of {nonzero_hi} \
             nonzero-high results red when the high word is dropped",
            leg.name
        );
        assert!(nonzero_hi > 100, "{}: too few nonzero high words", leg.name);
    }
}

#[test]
fn potency_budget_is_never_a_trap() {
    let w = wasm();
    let args = [WasmValue::I32(1), WasmValue::I32(2)];
    // kiln: `spin` exhausts fuel -> Budget, not Trap.
    let r = reference::run(&w, "spin", &args, 10_000, &Imports::new()).unwrap();
    assert_eq!(r.outcome, RefOutcome::Budget, "kiln spin: {:?}", r.outcome);
    // kiln: a TRAPPING probe with too little fuel to reach its trap is Budget.
    let r = reference::run(
        &w,
        "trap_if",
        &[WasmValue::I32(4), WasmValue::I32(4)],
        2,
        &Imports::new(),
    )
    .unwrap();
    assert_eq!(
        r.outcome,
        RefOutcome::Budget,
        "kiln trap_if@2: {:?}",
        r.outcome
    );
    // ... and with enough fuel it is the trap (control).
    let r = reference::run(
        &w,
        "trap_if",
        &[WasmValue::I32(4), WasmValue::I32(4)],
        FUEL,
        &Imports::new(),
    )
    .unwrap();
    assert!(
        matches!(
            r.outcome,
            RefOutcome::Trap {
                class: TrapClass::Unreachable,
                ..
            }
        ),
        "{:?}",
        r.outcome
    );
    for leg in LEGS {
        let obj = compile_leg(leg);
        let sig = export_signature(&w, "spin").unwrap();
        let e = emulate::run(&obj, "spin", &sig, &args, &EmuConfig::new(leg.cpu)).unwrap();
        assert_eq!(
            e.outcome,
            EmuOutcome::Budget,
            "{} spin: {:?}",
            leg.name,
            e.outcome
        );
        let r = reference::run(&w, "spin", &args, 10_000, &Imports::new()).unwrap();
        assert!(matches!(
            verdict(&r.outcome, &e.outcome),
            Verdict::Inconclusive(_)
        ));
        // unicorn: the trapping probe with a 1-instruction budget stops on
        // the budget, not the trap ...
        let tsig = export_signature(&w, "trap_if").unwrap();
        let targs = [WasmValue::I32(4), WasmValue::I32(4)];
        let mut cfg = EmuConfig::new(leg.cpu);
        cfg.budget = 1;
        let e = emulate::run(&obj, "trap_if", &tsig, &targs, &cfg).unwrap();
        assert_eq!(
            e.outcome,
            EmuOutcome::Budget,
            "{} trap_if@1: {:?}",
            leg.name,
            e.outcome
        );
        // ... and a Budget never agrees with the reference's trap.
        let r = reference::run(&w, "trap_if", &targs, FUEL, &Imports::new()).unwrap();
        assert!(!verdict(&r.outcome, &e.outcome).is_agree());
        // Control: with the default budget it IS a trap on both sides.
        let e = emulate::run(&obj, "trap_if", &tsig, &targs, &EmuConfig::new(leg.cpu)).unwrap();
        assert!(
            matches!(e.outcome, EmuOutcome::Trap { .. }),
            "{}: {:?}",
            leg.name,
            e.outcome
        );
        assert!(verdict(&r.outcome, &e.outcome).is_agree());
    }
}

#[test]
fn host_imports_resolve_exactly_and_log() {
    let w = wat::parse_str(
        r#"(module
             (import "mmio" "write32" (func $w (param i32 i32)))
             (import "mmio" "read32" (func $r (param i32) (result i32)))
             (func (export "poke") (param i32) (result i32)
               i32.const 0x40000000 local.get 0 call $w
               i32.const 0x40000004 call $r i32.const 1 i32.add))"#,
    )
    .unwrap();
    let imports =
        Imports::new()
            .trace("mmio", "write32", vec![])
            .func("mmio", "read32", |a| match a {
                [WasmValue::I32(addr)] => Ok(vec![WasmValue::I32(addr ^ 0xFF)]),
                _ => Err("bad args".into()),
            });
    let r = reference::run(&w, "poke", &[WasmValue::I32(0x55)], FUEL, &imports).unwrap();
    assert_eq!(
        r.outcome,
        RefOutcome::Values(vec![WasmValue::I32(0x4000_00FC)])
    );
    let trace: Vec<_> = r
        .calls
        .iter()
        .map(|c| (c.module.as_str(), c.field.as_str(), c.args.clone()))
        .collect();
    assert_eq!(
        trace,
        vec![
            (
                "mmio",
                "write32",
                vec![WasmValue::I32(0x4000_0000), WasmValue::I32(0x55)]
            ),
            ("mmio", "read32", vec![WasmValue::I32(0x4000_0004)]),
        ]
    );
    // A host error is a trap.
    let failing = Imports::new()
        .trace("mmio", "write32", vec![])
        .func("mmio", "read32", |_| Err("bus fault".into()));
    let r = reference::run(&w, "poke", &[WasmValue::I32(1)], FUEL, &failing).unwrap();
    assert!(
        matches!(
            r.outcome,
            RefOutcome::Trap {
                class: TrapClass::HostTrap,
                ..
            }
        ),
        "{:?}",
        r.outcome
    );
    // EXACT resolution: a missing import refuses the module, a near-miss
    // name does not resolve.
    let near = Imports::new().trace("mmio", "write32", vec![]).trace(
        "mmio",
        "read",
        vec![WasmValue::I32(0)],
    );
    let e = reference::run(&w, "poke", &[WasmValue::I32(1)], FUEL, &near).unwrap_err();
    assert_eq!(
        e,
        reference::RefError::UnresolvedImport {
            module: "mmio".into(),
            field: "read32".into()
        }
    );
}
