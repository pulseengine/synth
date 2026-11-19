//! RQ-91-RV32ISA (Refs #1744, #1741): the RV32 `--target` profile oracle.
//!
//! Before #1744, `--target` did not constrain RV32 instruction selection:
//! `rv32i` emitted `mul`/`remu` and every object claimed RVC. This oracle
//! holds, for each named profile (rv32i, rv32im, rv32imc, esp32c3, rv32imac):
//!
//! 1. every instruction of every emitted function DECODES inside the
//!    profile's extension set ([`synth_oracle::rv32_isa`], a decoder written
//!    from the ISA manual's opcode map, independent of synth's encoder), and
//!    the object's `e_flags` are the profile's (RVC iff C);
//! 2. every accepted function EXECUTES equal to kiln. unicorn cannot emulate
//!    a restricted RV32 core (see `rv32_isa`'s module doc), so the run is on
//!    the SiFive E31 (RV32IMAC); (1) proved the code stays inside the
//!    profile, so the E31's result is the profile core's;
//! 3. `rv32i` REFUSES, loudly and per function, every lowering that needs M
//!    (`i32.mul`, `i32.div_*`/`rem_*`, `i64.mul`, `i64.popcnt`), while
//!    `rv32im` accepts each and emits at least one M instruction for it;
//! 4. atomics are refused on every profile (synth emits no A instruction).
//!
//! Potency: the decode gate reds on a REAL rv32imac object judged as rv32i
//! (its `mul`/`remu`), and on the stack base `rv32i_refuses_each_m_lowering`
//! reds because rv32i exits 0 with `mul` in the object.
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary.

#![cfg(feature = "exec")]

use std::collections::BTreeMap;
use std::path::PathBuf;

use synth_oracle::emulate::{Cpu, EmuConfig};
use synth_oracle::reference::Imports;
use synth_oracle::run_case;
use synth_oracle::rv32_isa::{self, Ext, Profile};
use synth_oracle::synth::{CompileRun, CompiledObject, compile};
use synth_oracle::value::WasmValue;

const FUEL: u64 = 1_000_000;

/// Memory-free, call-free, i32-param probes. The `M_PROBES` need the M
/// extension on RV32; the rest are base-ISA.
const PROBES_WAT: &str = r#"
(module
  (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (func (export "sub_shift") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.shl local.get 1 local.get 0 i32.shr_s i32.sub)
  (func (export "lt_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.lt_u)
  (func (export "select_min") (param i32 i32) (result i32)
    local.get 0 local.get 1 local.get 0 local.get 1 i32.lt_s select)
  (func (export "loop_xor") (param i32 i32) (result i32) (local i32)
    local.get 0 i32.const 15 i32.and local.set 0
    block loop
      local.get 0 i32.eqz br_if 1
      local.get 2 local.get 1 i32.add local.get 0 i32.xor local.set 2
      local.get 0 i32.const 1 i32.sub local.set 0
      br 0
    end end
    local.get 2)
  (func (export "trap_if_eq") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.eq if unreachable end local.get 0)
  (func (export "i64_add") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_u local.get 1 i64.extend_i32_s i64.add)
  (func (export "mul") (param i32 i32) (result i32) local.get 0 local.get 1 i32.mul)
  (func (export "div_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.div_s)
  (func (export "div_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.div_u)
  (func (export "rem_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.rem_s)
  (func (export "rem_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.rem_u)
  (func (export "i64_mul") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_u local.get 1 i64.extend_i32_s i64.mul)
  (func (export "i64_popcnt") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_u i64.const 32 i64.shl local.get 1 i64.extend_i32_u i64.or
    i64.popcnt)
)
"#;

const BASE_PROBES: &[&str] = &[
    "add",
    "sub_shift",
    "lt_u",
    "select_min",
    "loop_xor",
    "trap_if_eq",
    "i64_add",
];
const M_PROBES: &[&str] = &[
    "mul",
    "div_s",
    "div_u",
    "rem_s",
    "rem_u",
    "i64_mul",
    "i64_popcnt",
];

const PROFILES: &[Profile] = &[
    Profile::new("rv32i", false, false, false),
    Profile::new("rv32im", true, false, false),
    Profile::new("rv32imc", true, false, true),
    Profile::new("esp32c3", true, false, true),
    Profile::new("rv32imac", true, true, true),
];

const VECTORS: &[u32] = &[
    0,
    1,
    2,
    3,
    7,
    0x7FFF_FFFF,
    0x8000_0000,
    0xFFFF_FFFE,
    0xFFFF_FFFF,
    0xDEAD_BEEF,
];

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-rv32isa-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn compile_wasm(wasm: &[u8], target: &str, extra: &[&str]) -> CompileRun {
    let dir = scratch();
    let input = dir.join("m.wasm");
    std::fs::write(&input, wasm).unwrap();
    let mut flags = vec!["-b", "riscv", "--target", target, "--relocatable"];
    flags.extend_from_slice(extra);
    compile(&input, &flags, &dir.join(format!("m-{target}.o"))).expect("synth runs")
}

/// Every instruction of `.text` decoded under `p`, and per-extension counts.
/// Panics naming the first out-of-profile instruction.
fn assert_decodes_within(p: &Profile, obj: &CompiledObject) -> BTreeMap<Ext, usize> {
    assert_eq!(
        obj.e_flags,
        p.e_flags(),
        "{}: e_flags {:#x}, the profile's are {:#x}",
        p.name,
        obj.e_flags,
        p.e_flags()
    );
    let bad = rv32_isa::violations(p, &obj.text);
    assert!(
        bad.is_empty(),
        "{}: {} instruction(s) outside the profile, first {:?}",
        p.name,
        bad.len(),
        bad[0]
    );
    let mut hist = BTreeMap::new();
    for i in rv32_isa::decode(&obj.text) {
        *hist.entry(i.ext).or_insert(0) += 1;
    }
    hist
}

#[test]
fn profiles_decode_within_their_isa_and_execute_equal_to_kiln() {
    let wasm = wat::parse_str(PROBES_WAT).unwrap();
    let cfg = EmuConfig::new(Cpu::Rv32Imac);
    let imports = Imports::new();
    let mut agree = 0usize;
    let mut refused = 0usize;
    for p in PROFILES {
        let run = compile_wasm(&wasm, p.name, &["--all-exports", "--allow-skipped-exports"]);
        assert!(run.status.success(), "{}: {}", p.name, run.stderr);
        let obj = run.object.expect("object");
        let hist = assert_decodes_within(p, &obj);
        assert_eq!(
            hist.get(&Ext::A),
            None,
            "{}: synth emits no A instruction",
            p.name
        );
        assert_eq!(
            hist.get(&Ext::C),
            None,
            "{}: synth emits no RVC form",
            p.name
        );
        // Which probes the profile accepted.
        for f in BASE_PROBES {
            assert!(
                obj.func(f).is_some(),
                "{}: base probe `{f}` missing",
                p.name
            );
        }
        for f in M_PROBES {
            if p.m {
                assert!(obj.func(f).is_some(), "{}: `{f}` missing", p.name);
            } else {
                assert!(obj.func(f).is_none(), "{}: `{f}` was emitted", p.name);
                assert!(
                    run.stderr.contains(&format!("function '{f}' lowers to"))
                        && run.stderr.contains("#1744"),
                    "{}: no loud refusal of `{f}`:\n{}",
                    p.name,
                    run.stderr
                );
                refused += 1;
            }
        }
        // NON-VACUITY: a profile with M actually emits M instructions here.
        assert_eq!(
            hist.get(&Ext::M).copied().unwrap_or(0) > 0,
            p.m,
            "{}: M histogram {hist:?}",
            p.name
        );
        for f in BASE_PROBES
            .iter()
            .chain(M_PROBES)
            .filter(|f| obj.func(f).is_some())
        {
            assert_eq!(obj.relocs_in(f), 0, "{}: `{f}` carries relocations", p.name);
            for &a in VECTORS {
                for &b in VECTORS {
                    let args = [WasmValue::I32(a), WasmValue::I32(b)];
                    let c = run_case(&wasm, &obj, f, &args, FUEL, &imports, &cfg)
                        .unwrap_or_else(|e| panic!("{}: {f}{args:?}: {e:?}", p.name));
                    assert!(
                        c.verdict.is_agree(),
                        "{}: {f}{args:?}: kiln {:?} vs synth {:?}",
                        p.name,
                        c.reference,
                        c.emulator
                    );
                    agree += 1;
                }
            }
        }
    }
    println!(
        "ORACLE rv32-isa: {agree} cases agree across {} profiles, {refused} M functions refused",
        PROFILES.len()
    );
    // 4 M profiles x 14 probes + rv32i x 7 base probes, x 100 vectors.
    assert_eq!(agree, (4 * 14 + 7) * VECTORS.len() * VECTORS.len());
    assert_eq!(refused, M_PROBES.len());
}

/// RED on the stack base (rv32i exited 0 with `mul` in the object).
#[test]
fn rv32i_refuses_each_m_lowering() {
    let sig = |res: &str| format!("(param i32 i32) (result {res})");
    let bodies = [
        ("i32.mul", sig("i32"), "local.get 0 local.get 1 i32.mul"),
        ("i32.div_s", sig("i32"), "local.get 0 local.get 1 i32.div_s"),
        ("i32.div_u", sig("i32"), "local.get 0 local.get 1 i32.div_u"),
        ("i32.rem_s", sig("i32"), "local.get 0 local.get 1 i32.rem_s"),
        ("i32.rem_u", sig("i32"), "local.get 0 local.get 1 i32.rem_u"),
        (
            "i64.mul",
            sig("i64"),
            "local.get 0 i64.extend_i32_u local.get 1 i64.extend_i32_u i64.mul",
        ),
        (
            "i64.popcnt",
            sig("i64"),
            "local.get 0 i64.extend_i32_u i64.popcnt",
        ),
    ];
    let rv32i = PROFILES[0];
    let rv32im = PROFILES[1];
    for (what, sig, body) in bodies {
        let wasm = wat::parse_str(format!("(module (func (export \"f\") {sig} {body}))")).unwrap();
        let run = compile_wasm(&wasm, "rv32i", &[]);
        if let Some(obj) = &run.object {
            panic!(
                "{what}: rv32i ACCEPTED it; out-of-profile instructions: {:?}",
                rv32_isa::violations(&rv32i, &obj.text)
            );
        }
        assert!(
            run.stderr.contains("has no `m` extension") && run.stderr.contains("#1744"),
            "{what}: rv32i refused, but not for the profile:\n{}",
            run.stderr
        );
        let run = compile_wasm(&wasm, "rv32im", &[]);
        let obj = run
            .object
            .unwrap_or_else(|| panic!("{what}: rv32im refused: {}", run.stderr));
        let hist = assert_decodes_within(&rv32im, &obj);
        assert!(
            hist.get(&Ext::M).copied().unwrap_or(0) > 0,
            "{what}: {hist:?}"
        );
    }
}

#[test]
fn atomics_are_refused_on_every_profile() {
    let mods = [
        "(module (memory 1) (func (export \"f\") (param i32 i32) (result i32) \
         local.get 0 local.get 1 i32.atomic.rmw.add))",
        "(module (memory 1) (func (export \"f\") (param i32) (result i32) \
         local.get 0 i32.atomic.load))",
        "(module (func (export \"f\") (param i32) (result i32) atomic.fence local.get 0))",
    ];
    for m in mods {
        let wasm = wat::parse_str(m).unwrap();
        for p in PROFILES {
            let run = compile_wasm(&wasm, p.name, &[]);
            assert!(
                !run.status.success() && run.object.is_none(),
                "{}: accepted an atomic: {m}",
                p.name
            );
        }
    }
}

/// POTENCY on real bytes: an rv32imac object judged as rv32i reds on its M
/// instructions and on its RVC flag.
#[test]
fn potency_rv32imac_object_fails_the_rv32i_gate() {
    let wasm = wat::parse_str(PROBES_WAT).unwrap();
    let run = compile_wasm(&wasm, "rv32imac", &["--all-exports"]);
    let obj = run.object.expect("rv32imac compiles every probe");
    let rv32i = PROFILES[0];
    let bad = rv32_isa::violations(&rv32i, &obj.text);
    assert!(
        !bad.is_empty() && bad.iter().all(|i| i.ext == Ext::M),
        "{bad:?}"
    );
    assert_ne!(obj.e_flags, rv32i.e_flags());
    let r = std::panic::catch_unwind(|| assert_decodes_within(&rv32i, &obj));
    assert!(r.is_err(), "the rv32i gate passed an rv32imac object");
}

/// The acceptance corpus (gale's drivers), when `SYNTH_RV32ISA_CORPUS` names a
/// directory of `.wasm` files: for each profile, an accepted object decodes
/// inside it. Reports per-profile accepted/refused counts. Not set: prints
/// that, and asserts nothing (the corpus is not vendored).
#[test]
fn corpus_decodes_within_each_profile() {
    let Some(dir) = std::env::var_os("SYNTH_RV32ISA_CORPUS") else {
        println!("rv32-isa corpus: SYNTH_RV32ISA_CORPUS not set, leg not run");
        return;
    };
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "wasm"))
        .collect();
    files.sort();
    assert!(!files.is_empty(), "no .wasm in {dir:?}");
    for f in &files {
        let wasm = std::fs::read(f).unwrap();
        for p in PROFILES {
            let run = compile_wasm(&wasm, p.name, &["--all-exports"]);
            let verdict = match &run.object {
                Some(obj) => {
                    let hist = assert_decodes_within(p, obj);
                    format!("ACCEPTED {} funcs, insns {hist:?}", obj.funcs.len())
                }
                None => {
                    let why = run
                        .stderr
                        .lines()
                        .filter(|l| l.contains("#1744") || l.starts_with("Error"))
                        .collect::<Vec<_>>()
                        .join(" | ");
                    format!("REFUSED: {why}")
                }
            };
            println!("rv32-isa corpus {}: {}: {verdict}", f.display(), p.name);
        }
    }
}
