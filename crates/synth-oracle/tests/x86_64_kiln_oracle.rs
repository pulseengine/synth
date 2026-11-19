//! RQ-91-X86SKEL (Refs #1741): the x86-64 skeleton against kiln.
//!
//! An embedded probe module (the ops lane X1 lowers: `local.get` of a
//! parameter, `i32.add`, `return`, `end`, over one to six i32 parameters) is
//! compiled by synth with `-b x86_64 --relocatable`, and every probe × vector
//! runs on kiln and, as the bytes synth emitted, on unicorn x86-64 with the CPU
//! model PINNED to QEMU64 (the baseline), SysV argument passing with POISONED
//! upper halves, and rbx/rbp/r12–r15/rsp checked preserved. Every case must
//! AGREE.
//!
//! The probes are embedded, not files under `scripts/repro/` (REVIEW_2 X7: a
//! fixture there would move the ARM corpus sweeps' pinned figures).
//!
//! Potency, each its own test: a planted wrong reference; the emitted image
//! mutated (`add` → `sub`); a planted `ud2` (a trap where kiln returns) and
//! planted non-`ud2` faults; each callee-saved register and `rsp`; the poisoned
//! upper half; and the pinned CPU model (`lzcnt` runs as `bsr`, `popcnt`
//! faults), shown against unicorn's unpinned default.
//!
//! RED ON THE STACK BASE: there `-b x86_64` is "Unknown backend", so
//! `compile_x86` fails before any case runs.
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary.

#![cfg(feature = "exec")]

use std::path::PathBuf;

use synth_oracle::compare::{EmuOutcome, Verdict};
use synth_oracle::emulate::{self, Cpu, EmuConfig};
use synth_oracle::reference::Imports;
use synth_oracle::synth::{CompiledObject, FuncSym, Machine, compile};
use synth_oracle::value::{Signature, ValType, WasmValue, export_signature};
use synth_oracle::{Case, run_case};

const FUEL: u64 = 1_000_000;

const PROBES_WAT: &str = r#"
(module
  (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (func (export "add3") (param i32 i32 i32) (result i32)
    local.get 0 local.get 1 i32.add local.get 2 i32.add)
  (func (export "ret_early") (param i32 i32) (result i32)
    local.get 1 local.get 0 i32.add return)
  (func (export "id") (param i32) (result i32) local.get 0)
  (func (export "second") (param i32 i32) (result i32) local.get 1)
  (func (export "sum6") (param i32 i32 i32 i32 i32 i32) (result i32)
    local.get 0 local.get 1 i32.add
    local.get 2 local.get 3 i32.add
    local.get 4 local.get 5 i32.add
    i32.add i32.add)
  (func (export "rsum") (param i32 i32 i32 i32 i32 i32) (result i32)
    local.get 5 local.get 4 local.get 3 i32.add i32.add
    local.get 2 i32.add local.get 1 i32.add local.get 0 i32.add)
  (func (export "void"))
)
"#;

/// `(export, parameter count)`.
const PROBES: &[(&str, usize)] = &[
    ("add", 2),
    ("add3", 3),
    ("ret_early", 2),
    ("id", 1),
    ("second", 2),
    ("sum6", 6),
    ("rsum", 6),
    ("void", 0),
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

const FLAGS: &[&str] = &["-b", "x86_64", "--relocatable", "--all-exports"];

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-oracle-x86-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn wasm() -> Vec<u8> {
    wat::parse_str(PROBES_WAT).expect("probe WAT parses")
}

fn compile_x86() -> CompiledObject {
    let dir = scratch();
    let input = dir.join("probes.wasm");
    std::fs::write(&input, wasm()).unwrap();
    let out = dir.join("probes-x86_64.o");
    let run = compile(&input, FLAGS, &out).expect("synth runs");
    assert!(
        run.status.success(),
        "x86_64: synth compile failed: {}",
        run.stderr
    );
    let obj = run.object.expect("object parsed");
    assert_eq!(obj.machine, Machine::X86_64);
    for (p, _) in PROBES {
        assert!(
            obj.function_bytes(p).is_some_and(|b| !b.is_empty()),
            "no bytes for `{p}` in the symtab"
        );
        assert_eq!(obj.relocs_in(p), 0, "`{p}` carries relocations");
    }
    obj
}

/// The argument vectors for an `n`-parameter probe: every pair of VECTORS for
/// `n >= 2` (the remaining slots filled by rotation, so every slot sees every
/// vector), every vector for `n == 1`, one empty call for `n == 0`.
fn args_for(n: usize) -> Vec<Vec<WasmValue>> {
    match n {
        0 => vec![vec![]],
        1 => VECTORS.iter().map(|&a| vec![WasmValue::I32(a)]).collect(),
        _ => {
            let k = VECTORS.len();
            let mut v = Vec::new();
            for i in 0..k {
                for j in 0..k {
                    v.push(
                        (0..n)
                            .map(|s| match s {
                                0 => VECTORS[i],
                                1 => VECTORS[j],
                                _ => VECTORS[(i + j * s + s) % k],
                            })
                            .map(WasmValue::I32)
                            .collect(),
                    );
                }
            }
            v
        }
    }
}

fn cfg() -> EmuConfig {
    EmuConfig::new(Cpu::X86_64Baseline)
}

fn sweep(wasm_ref: &[u8], obj: &CompiledObject) -> Vec<Case> {
    let mut cases = Vec::new();
    for (p, n) in PROBES {
        for args in args_for(*n) {
            cases.push(
                run_case(wasm_ref, obj, p, &args, FUEL, &Imports::new(), &cfg())
                    .unwrap_or_else(|e| panic!("{p}{args:?}: harness error {e:?}")),
            );
        }
    }
    cases
}

#[test]
fn probes_agree_with_kiln_on_x86_64() {
    let w = wasm();
    let obj = compile_x86();
    let cases = sweep(&w, &obj);
    let bad: Vec<_> = cases.iter().filter(|c| !c.verdict.is_agree()).collect();
    for c in bad.iter().take(20) {
        eprintln!(
            "x86_64 {}{:?}: {:?}  (ref {:?}, emu {:?})",
            c.export, c.args, c.verdict, c.reference, c.emulator
        );
    }
    assert!(
        bad.is_empty(),
        "x86_64: {} of {} cases do not agree",
        bad.len(),
        cases.len()
    );
    // Non-vacuity: every case returned VALUES on both sides (this lane has no
    // trap), and the count is EXACT as a literal.
    assert!(
        cases
            .iter()
            .all(|c| matches!(c.emulator, EmuOutcome::Values(_)))
    );
    assert_eq!(cases.len(), 877, "case count moved");
    eprintln!("ORACLE x86_64-kiln: {} cases agree", cases.len());
}

#[test]
fn cpu_model_is_pinned_and_read_back() {
    let w = wasm();
    let obj = compile_x86();
    let sig = export_signature(&w, "add").unwrap();
    let r = emulate::run(
        &obj,
        "add",
        &sig,
        &[WasmValue::I32(2), WasmValue::I32(3)],
        &cfg(),
    )
    .expect("emulates");
    assert_eq!(r.cpu_model_readback, Cpu::X86_64Baseline.model_id());
    assert_eq!(
        Cpu::X86_64Baseline.model_id(),
        unicorn_engine::X86CpuModel::QEMU64 as i32
    );
    assert_eq!(r.outcome, EmuOutcome::Values(vec![WasmValue::I32(5)]));
}

// ---------------------------------------------------------------- potency --

#[test]
fn potency_planted_wrong_reference_reds() {
    let planted = PROBES_WAT.replacen(
        "(func (export \"add\") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)",
        "(func (export \"add\") (param i32 i32) (result i32) local.get 0 local.get 1 i32.sub)",
        1,
    );
    assert_ne!(planted, PROBES_WAT);
    let w = wat::parse_str(&planted).unwrap();
    let obj = compile_x86();
    let disagree = args_for(2)
        .iter()
        .filter(|a| {
            matches!(
                run_case(&w, &obj, "add", a, FUEL, &Imports::new(), &cfg())
                    .unwrap()
                    .verdict,
                Verdict::Disagree(_)
            )
        })
        .count();
    // add == sub exactly when b is 0 or 0x80000000.
    assert_eq!(disagree, VECTORS.len() * (VECTORS.len() - 2));
}

/// The emitted image itself mutated: `add` (`01 /r`) becomes `sub` (`29 /r`)
/// in the bytes synth wrote. The sweep must red on the same vectors.
#[test]
fn potency_mutated_image_reds() {
    let w = wasm();
    let obj = compile_x86();
    let f = obj.func("add").unwrap().clone();
    let body = &obj.text[f.offset as usize..(f.offset + f.size) as usize];
    let at = body
        .iter()
        .position(|&b| b == 0x01)
        .expect("an `add r/m32, r32` opcode in `add`");
    let mut bad = obj.clone();
    bad.text[f.offset as usize + at] = 0x29;
    let disagree = args_for(2)
        .iter()
        .filter(|a| {
            !run_case(&w, &bad, "add", a, FUEL, &Imports::new(), &cfg())
                .unwrap()
                .verdict
                .is_agree()
        })
        .count();
    assert_eq!(disagree, VECTORS.len() * (VECTORS.len() - 2));
}

/// A one-function x86-64 object built by hand.
fn hand(text: &[u8]) -> CompiledObject {
    CompiledObject {
        path: PathBuf::from("hand.o"),
        machine: Machine::X86_64,
        text: text.to_vec(),
        funcs: [(
            "f".to_string(),
            FuncSym {
                offset: 0,
                size: text.len() as u64,
                thumb: false,
                global: true,
            },
        )]
        .into_iter()
        .collect(),
        text_relocs: vec![],
    }
}

fn sig(params: &[ValType], results: &[ValType]) -> Signature {
    Signature {
        params: params.to_vec(),
        results: results.to_vec(),
    }
}

fn run_hand(text: &[u8], s: &Signature, args: &[WasmValue]) -> EmuOutcome {
    emulate::run(&hand(text), "f", s, args, &cfg())
        .expect("emulates")
        .outcome
}

const MOV_EAX_EDI_RET: &[u8] = &[0x89, 0xF8, 0xC3];

#[test]
fn potency_trap_only_on_ud2_inside_the_function() {
    let s = sig(&[ValType::I32], &[ValType::I32]);
    let a = [WasmValue::I32(5)];
    assert_eq!(
        run_hand(MOV_EAX_EDI_RET, &s, &a),
        EmuOutcome::Values(vec![WasmValue::I32(5)])
    );
    // `ud2` at offset 2: a trap, at that RIP.
    match run_hand(&[0x89, 0xF8, 0x0F, 0x0B, 0xC3], &s, &a) {
        EmuOutcome::Trap { pc, insn } => {
            assert_eq!(insn, "ud2");
            assert_eq!(pc, emulate::TEXT_BASE + 2);
        }
        o => panic!("ud2 is not a trap: {o:?}"),
    }
    // Faults that are NOT ud2: ILLEGAL, never a trap (REVIEW_2 X3). `06` is
    // invalid in 64-bit mode; `0F 0F FF` is a 3DNow! form QEMU64 lacks; `0F
    // FF` is ud0; `div ecx` with ecx = 0 is a CPU #DE.
    for (what, bytes) in [
        ("06", &[0x06u8, 0xC3][..]),
        ("0f 0f ff", &[0x0F, 0x0F, 0xFF, 0xC3][..]),
        ("ud0", &[0x0F, 0xFF, 0xC0, 0xC3][..]),
        ("ud1", &[0x0F, 0xB9, 0xC0, 0xC3][..]),
        ("div by zero", &[0x31, 0xC9, 0xF7, 0xF1, 0xC3][..]),
    ] {
        let o = run_hand(bytes, &s, &a);
        assert!(
            matches!(o, EmuOutcome::Illegal { .. }),
            "{what}: {o:?} is not ILLEGAL"
        );
    }
}

#[test]
fn potency_callee_saved_registers_and_rsp() {
    let s = sig(&[ValType::I32], &[ValType::I32]);
    let a = [WasmValue::I32(5)];
    // `xor reg, reg` (32-bit: also zeroes the upper half), then the control body.
    for (reg, xor) in [
        ("rbx", &[0x31u8, 0xDB][..]),
        ("rbp", &[0x31, 0xED][..]),
        ("r12", &[0x45, 0x31, 0xE4][..]),
        ("r13", &[0x45, 0x31, 0xED][..]),
        ("r14", &[0x45, 0x31, 0xF6][..]),
        ("r15", &[0x45, 0x31, 0xFF][..]),
    ] {
        let mut t = xor.to_vec();
        t.extend_from_slice(MOV_EAX_EDI_RET);
        match run_hand(&t, &s, &a) {
            EmuOutcome::Illegal { reason, .. } => {
                assert!(reason.contains(&format!("{reg} clobbered")), "{reason}");
            }
            o => panic!("{reg} clobber not caught: {o:?}"),
        }
    }
    // Writing ONLY the upper half of rbx (a 32-bit-clean value would hide it):
    // `ror rbx, 32` twice is the identity; once is not.
    let mut t = vec![0x48, 0xC1, 0xCB, 0x20];
    t.extend_from_slice(MOV_EAX_EDI_RET);
    assert!(matches!(run_hand(&t, &s, &a), EmuOutcome::Illegal { .. }));
    // rsp: `pop rcx; sub rsp, 8; jmp rcx` reaches the sentinel with rsp 8 low.
    let t = [0x59, 0x48, 0x83, 0xEC, 0x08, 0xFF, 0xE1];
    match run_hand(&t, &s, &a) {
        EmuOutcome::Illegal { reason, .. } => assert!(reason.contains("SP imbalance"), "{reason}"),
        o => panic!("rsp imbalance not caught: {o:?}"),
    }
    // Caller-saved scratch is NOT callee-saved: clobbering r10/r11 is fine.
    let mut t = vec![0x45, 0x31, 0xD2, 0x45, 0x31, 0xDB];
    t.extend_from_slice(MOV_EAX_EDI_RET);
    assert_eq!(
        run_hand(&t, &s, &a),
        EmuOutcome::Values(vec![WasmValue::I32(5)])
    );
}

/// The upper half of an i32 argument register is POISONED: a 64-bit move that
/// carries it into an i64 result is visible.
#[test]
fn potency_upper_half_of_i32_args_is_poisoned() {
    let s = sig(&[ValType::I32], &[ValType::I64]);
    let a = [WasmValue::I32(5)];
    // `movl %edi, %eax` zero-extends: the i64 is 5.
    assert_eq!(
        run_hand(MOV_EAX_EDI_RET, &s, &a),
        EmuOutcome::Values(vec![WasmValue::I64(5)])
    );
    // `movq %rdi, %rax` carries the poison.
    match run_hand(&[0x48, 0x89, 0xF8, 0xC3], &s, &a) {
        EmuOutcome::Values(v) => assert_ne!(v, vec![WasmValue::I64(5)]),
        o => panic!("{o:?}"),
    }
    // rax is poisoned at entry: a function that never writes it does not
    // return a fixed value by accident.
    match run_hand(&[0xC3], &sig(&[], &[ValType::I32]), &[]) {
        EmuOutcome::Values(v) => assert_ne!(v, vec![WasmValue::I32(0)]),
        o => panic!("{o:?}"),
    }
}

/// `F3 0F BD C7` is `lzcnt eax, edi` on a CPU with LZCNT and `bsr eax, edi`
/// without it. On the PINNED baseline model it runs as `bsr` (1 -> 0), and
/// `popcnt` faults; unicorn's DEFAULT x86-64 model runs `lzcnt` (1 -> 31). So
/// the pin is load-bearing: without it the oracle could not see an
/// above-baseline instruction (REVIEW_2 X2).
#[test]
fn potency_the_cpu_model_pin_is_load_bearing() {
    let lzcnt = [0xF3, 0x0F, 0xBD, 0xC7, 0xC3];
    let s = sig(&[ValType::I32], &[ValType::I32]);
    assert_eq!(
        run_hand(&lzcnt, &s, &[WasmValue::I32(1)]),
        EmuOutcome::Values(vec![WasmValue::I32(0)])
    );
    assert!(matches!(
        run_hand(&[0xF3, 0x0F, 0xB8, 0xC7, 0xC3], &s, &[WasmValue::I32(1)]),
        EmuOutcome::Illegal { .. }
    ));
    // The same bytes on unicorn's default model: lzcnt semantics.
    use unicorn_engine::{Arch, Mode, Prot, RegisterX86, Unicorn};
    let mut u = Unicorn::new(Arch::X86, Mode::MODE_64).unwrap();
    u.mem_map(0x1000, 0x1000, Prot::ALL).unwrap();
    u.mem_write(0x1000, &lzcnt[..4]).unwrap();
    u.reg_write(RegisterX86::RDI as i32, 1).unwrap();
    u.emu_start(0x1000, 0x1004, 0, 1).unwrap();
    assert_eq!(u.reg_read(RegisterX86::RAX as i32).unwrap() as u32, 31);
}
