//! Refs #1785, #929: a 64-bit (i64) CALL ARGUMENT on ARM Cortex-M is passed
//! where base AAPCS puts it, and synth's caller and synth's callee agree.
//!
//! Before this, the ARM selector refused every call with an i64 argument
//! (`#929: call arg 0 is 64-bit and would be passed in a register ...
//! Declining`, and `#503` for one on the stack), so a function making such a
//! call was skipped and the whole module failed (#952, or #1102 once another
//! retained function called the skipped one).
//!
//! AAPCS, core registers: an i64 takes the next EVEN pair (R0:R1 or R2:R3),
//! skipping an odd NCRN, and the skipped register is NOT back-filled; the low
//! word is in the lower register. One that does not fit sets NCRN to 4 and
//! goes on the stack at an 8-byte-aligned NSAA; every later argument is
//! stacked too.
//!
//! For each signature in [`SIGS`] the module has a LOCAL callee and an IMPORT
//! of the same signature. Both fold every argument word into one i64 so a
//! misplaced, dropped or swapped word changes the result. Four exports call
//! them: with constant arguments and with arguments taken from the export's
//! own two i64 params (so sources sit in R0-R3 and the marshal is a parallel
//! move with cycles, e.g. an i64 in R0:R1 bound for R2:R3 while an i32 in R2
//! is bound for R0). kiln is the reference. For the import, the host stub
//! (`synth_oracle::hosted`) reads the arguments per AAPCS from R0-R3 and the
//! stack, so the logged host call is the C-ABI check, word for word, and SP
//! must be 8-byte aligned at the call.
//!
//! Legs: cortex-m4, cortex-m3 and cortex-m7 `--relocatable` (the direct
//! selector, #197), cortex-m4 default flags (an import makes it host-linked),
//! and the self-contained `--cortex-m` image of the local-only twin, booted
//! through its own startup on cortex-m4.
//!
//! A third test, `i64_operand_live_across_call_1785`, pins a defect the
//! spec-execution oracle found once `call.wast`'s `fac` compiled: a spilled
//! i64 operand reloaded over the call's i64 result. Its i32-argument twin was
//! a silent miscompile on d6fff037 already (`mulcall(5)` gave 0x19, wasm
//! 0x500000014); the fix is in `pop_operand`, not in the marshalling.
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary; with a
//! pre-fix one every leg reds at compile time (the test asserts acceptance:
//! a decline is a failure here, not a skip).

#![cfg(feature = "exec")]

use std::path::PathBuf;

use synth_oracle::compare::{Verdict, verdict};
use synth_oracle::emulate::Cpu;
use synth_oracle::hosted::HostConfig;
use synth_oracle::image::BootedImage;
use synth_oracle::reference::{self, Imports};
use synth_oracle::run_hosted;
use synth_oracle::synth::compile;
use synth_oracle::value::{WasmValue, export_signature};

const FUEL: u64 = 1_000_000;
const LINMEM: u32 = 0x2001_0000;

/// Parameter lists, `true` = i64. Every shape the issue's AAPCS rules
/// distinguish: pair at R0:R1, pair after a skipped R1, pair at R2:R3, two
/// pairs, a skip with an i32 after it (no back-fill), an i64 to the stack at
/// an 8-aligned NSAA, a second i64 to the stack, i32s after a pair spilling
/// to the stack, and three i64s.
const SIGS: &[(&str, &[bool])] = &[
    ("s_i64_i32", &[true, false]),
    ("s_i32_i64", &[false, true]),
    ("s_i32_i32_i64", &[false, false, true]),
    ("s_i64_i64", &[true, true]),
    ("s_i32_i64_i32", &[false, true, false]),
    ("s_i32_i32_i32_i64", &[false, false, false, true]),
    ("s_i64_i32_i64", &[true, false, true]),
    ("s_i64_i32_i32_i32_i32", &[true, false, false, false, false]),
    ("s_i32_i64_i64", &[false, true, true]),
    ("s_i64_i64_i64", &[true, true, true]),
];

/// The fold both callees compute: `acc = acc * P + x_k` over the argument
/// words in order (an i32 zero-extended), with distinct per-position mixing.
fn fold(args: &[WasmValue]) -> u64 {
    const P: u64 = 0x0000_0100_0000_01B3;
    let mut acc: u64 = 0xCBF2_9CE4_8422_2325;
    for (k, a) in args.iter().enumerate() {
        let x = match a {
            WasmValue::I32(v) => u64::from(*v),
            WasmValue::I64(v) => *v,
            _ => unreachable!("integer signatures only"),
        };
        acc = acc.wrapping_mul(P).wrapping_add(x ^ (k as u64 + 1));
    }
    acc
}

fn wat_ty(w: bool) -> &'static str {
    if w { "i64" } else { "i32" }
}

/// The callee body: the same fold, in wasm.
fn fold_body(params: &[bool]) -> String {
    let mut b = String::from("i64.const 0xCBF29CE484222325\n");
    for (k, &w) in params.iter().enumerate() {
        b += "i64.const 0x00000100000001B3 i64.mul\n";
        b += &format!("local.get {k}\n");
        if !w {
            b += "i64.extend_i32_u\n";
        }
        b += &format!("i64.const {} i64.xor i64.add\n", k + 1);
    }
    b
}

/// Constant arguments: distinct high and low words, negative values.
fn const_arg(k: usize, w: bool) -> String {
    if w {
        let v: [i64; 3] = [
            0x1122_3344_5566_7788,
            -2,
            0x7EDC_BA98_7654_3210_u64 as i64 ^ i64::MIN,
        ];
        format!("i64.const {}", v[k % 3])
    } else {
        let v: [i32; 5] = [-3, 0x5A5A_0001, 0x7FFF_FFFF, 42, -0x8000_0000];
        format!("i32.const {}", v[k % 5])
    }
}

/// Arguments from the export's params `a` (local 0) and `b` (local 1), both
/// i64: the i64s alternate b, a, a^b (so sources are crossed), the i32s are
/// the low words of b and a and the high word of a, plus a constant.
fn param_arg(k: usize, w: bool) -> String {
    if w {
        [
            "local.get 1",
            "local.get 0",
            "local.get 0 local.get 1 i64.xor",
        ][k % 3]
            .to_string()
    } else {
        [
            "local.get 1 i32.wrap_i64",
            "local.get 0 i32.wrap_i64",
            "local.get 0 i64.const 32 i64.shr_u i32.wrap_i64",
            "i32.const 0x13572468",
        ][k % 4]
            .to_string()
    }
}

/// The module for one signature. `with_import` adds the import callee and
/// its two exports (the self-contained leg cannot link an import).
fn module(params: &[bool], with_import: bool) -> String {
    let ps: Vec<&str> = params.iter().map(|&w| wat_ty(w)).collect();
    let ps = ps.join(" ");
    let call = |target: &str, arg: &dyn Fn(usize, bool) -> String| {
        let args: Vec<String> = params.iter().enumerate().map(|(k, &w)| arg(k, w)).collect();
        format!("{}\ncall {target}", args.join("\n"))
    };
    let mut m = String::from("(module\n");
    if with_import {
        m += &format!("  (import \"env\" \"imp\" (func $imp (param {ps}) (result i64)))\n");
    }
    // `call $nop` first: the callee then frame-backs its params (#837). A
    // CALL-FREE callee with an i64 param in a register and i64 arithmetic in
    // its body is refused by its own prologue today (#518/#837: the
    // pair-exhaustion retry), independent of how the caller passes them.
    m += "  (func $nop)\n";
    m += &format!(
        "  (func $loc (param {ps}) (result i64)\ncall $nop\n{})\n",
        fold_body(params)
    );
    m += &format!(
        "  (func (export \"k_loc\") (result i64)\n{})\n",
        call("$loc", &const_arg)
    );
    m += &format!(
        "  (func (export \"p_loc\") (param i64 i64) (result i64)\n{})\n",
        call("$loc", &param_arg)
    );
    if with_import {
        m += &format!(
            "  (func (export \"k_imp\") (result i64)\n{})\n",
            call("$imp", &const_arg)
        );
        m += &format!(
            "  (func (export \"p_imp\") (param i64 i64) (result i64)\n{})\n",
            call("$imp", &param_arg)
        );
    }
    m + ")\n"
}

fn imports() -> Imports {
    Imports::new().func("env", "imp", |a: &[WasmValue]| {
        Ok(vec![WasmValue::I64(fold(a))])
    })
}

fn l(v: u64) -> WasmValue {
    WasmValue::I64(v)
}

/// The export-param vectors: distinct words, all-ones, sign boundaries.
fn vectors() -> Vec<[WasmValue; 2]> {
    vec![
        [l(0x1122_3344_5566_7788), l(0x99AA_BBCC_DDEE_FF00)],
        [l(u64::MAX), l(0)],
        [l(0x8000_0000_0000_0000), l(0x7FFF_FFFF_FFFF_FFFF)],
        [l((-0x1_2345_6789_i64) as u64), l(42)],
    ]
}

/// Every step of one module: the constant exports once, the param exports
/// on every vector.
fn steps(with_import: bool) -> Vec<(&'static str, Vec<WasmValue>)> {
    let mut s: Vec<(&'static str, Vec<WasmValue>)> = vec![("k_loc", vec![])];
    if with_import {
        s.push(("k_imp", vec![]));
    }
    for v in vectors() {
        s.push(("p_loc", v.to_vec()));
        if with_import {
            s.push(("p_imp", v.to_vec()));
        }
    }
    s
}

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-i64args-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// Compile `wat` with `flags`; Err is the compiler's refusal (red).
fn build(wat: &str, flags: &[&str]) -> Result<(Vec<u8>, PathBuf), String> {
    let wasm = wat::parse_str(wat).map_err(|e| format!("WAT: {e}"))?;
    let dir = scratch();
    let input = dir.join("m.wasm");
    std::fs::write(&input, &wasm).unwrap();
    let out = dir.join("m.out");
    let mut f = flags.to_vec();
    f.push("--all-exports");
    let run = compile(&input, &f, &out)?;
    if !run.status.success() {
        let why = run
            .stderr
            .lines()
            .find(|l| l.contains("#929") || l.contains("#503") || l.contains("Error"))
            .unwrap_or("synth failed")
            .to_string();
        return Err(format!("{flags:?} REFUSED: {why}"));
    }
    Ok((wasm, out))
}

struct HostedLeg {
    name: &'static str,
    flags: &'static [&'static str],
    cpu: Cpu,
}

const HOSTED: &[HostedLeg] = &[
    HostedLeg {
        name: "cortex-m4 --relocatable",
        flags: &["--target", "cortex-m4", "--relocatable"],
        cpu: Cpu::CortexM4,
    },
    HostedLeg {
        name: "cortex-m3 --relocatable",
        flags: &["--target", "cortex-m3", "--relocatable"],
        cpu: Cpu::CortexM3,
    },
    HostedLeg {
        name: "cortex-m7 --relocatable",
        flags: &["--target", "cortex-m7", "--relocatable"],
        cpu: Cpu::CortexM7,
    },
    HostedLeg {
        name: "cortex-m4 default flags",
        flags: &["--target", "cortex-m4"],
        cpu: Cpu::CortexM4,
    },
];

fn show_case(c: &synth_oracle::HostedCase) -> String {
    format!(
        "{}{:?}: kiln {:?} calls {:?} | machine code {:?} calls {:?} | {:?}",
        c.export, c.args, c.reference, c.ref_calls, c.emulator, c.emu_calls, c.verdict
    )
}

/// Local and import callees, linked against the AAPCS host stub, on every
/// host-linked leg.
#[test]
fn i64_call_args_hosted_1785() {
    let (mut agree, mut calls, mut red) = (0usize, 0usize, Vec::new());
    for leg in HOSTED {
        for (sig, params) in SIGS {
            let what = format!("{} {sig}", leg.name);
            let (wasm, out) = match build(&module(params, true), leg.flags) {
                Ok(b) => b,
                Err(e) => {
                    red.push(format!("{what}: {e}"));
                    continue;
                }
            };
            let obj = synth_oracle::synth::CompiledObject::parse(&out).expect("object parses");
            let cfg = HostConfig::new(leg.cpu, LINMEM);
            for (e, a) in steps(true) {
                match run_hosted(&wasm, &obj, &[(e, &a[..])], FUEL, &imports(), &cfg) {
                    Ok(cases) if cases.len() == 1 && cases[0].verdict.is_agree() => {
                        agree += 1;
                        calls += cases[0].emu_calls.len();
                    }
                    Ok(cases) => {
                        red.extend(cases.iter().map(|c| format!("{what}: {}", show_case(c))))
                    }
                    Err(err) => red.push(format!("{what}: {e}{a:?}: harness error {err:?}")),
                }
            }
        }
    }
    assert!(red.is_empty(), "\n{}", red.join("\n"));
    println!(
        "ORACLE i64-call-args-1785 hosted: {agree} steps agree across {} legs x {} signatures, {calls} host calls matched",
        HOSTED.len(),
        SIGS.len()
    );
    assert_eq!(
        (agree, calls),
        (
            HOSTED.len() * SIGS.len() * 10,
            HOSTED.len() * SIGS.len() * 5
        )
    );
}

/// The self-contained `--cortex-m` image of the local-only twin, booted
/// through its own startup.
#[test]
fn i64_call_args_self_contained_1785() {
    let (mut agree, mut red) = (0usize, Vec::new());
    for (sig, params) in SIGS {
        let what = format!("cortex-m4 --cortex-m {sig}");
        let (wasm, out) = match build(
            &module(params, false),
            &["--target", "cortex-m4", "--cortex-m"],
        ) {
            Ok(b) => b,
            Err(e) => {
                red.push(format!("{what}: {e}"));
                continue;
            }
        };
        let mut img = match BootedImage::boot(&out, Cpu::CortexM4, false) {
            Ok(i) => i,
            Err(e) => {
                red.push(format!("{what}: boot {e:?}"));
                continue;
            }
        };
        for (e, a) in steps(false) {
            let r = reference::run(&wasm, e, &a, FUEL, &Imports::new()).expect("kiln runs");
            let sigt = export_signature(&wasm, e).unwrap();
            match img.call(e, &sigt, &a, 1_000_000) {
                Ok(run) => match verdict(&r.outcome, &run.outcome) {
                    Verdict::Agree => agree += 1,
                    v => red.push(format!(
                        "{what}: {e}{a:?}: kiln {:?} | machine code {:?} | {v:?}",
                        r.outcome, run.outcome
                    )),
                },
                Err(err) => red.push(format!("{what}: {e}{a:?}: {err:?}")),
            }
        }
    }
    assert!(red.is_empty(), "\n{}", red.join("\n"));
    println!(
        "ORACLE i64-call-args-1785 self-contained: {agree} steps agree across {} signatures",
        SIGS.len()
    );
    assert_eq!(agree, SIGS.len() * 5);
}

/// Found by the spec suite once `call.wast`'s `fac` compiled: an i64 operand
/// live across a call, SPILLED while the argument was computed, was reloaded
/// by the consuming `i64.mul` into R0:R1 — over the call's own i64 result —
/// so `fac(5)` returned 25. `mulcall` is the same shape with an i32 argument;
/// it compiled before #1785 too, with the same wrong code (a pre-existing
/// silent miscompile on d6fff037, not one this lane introduced).
const LIVE_ACROSS_WAT: &str = r#"
(module
  (func $g (param i32) (result i64)
    (i64.add (i64.extend_i32_u (local.get 0)) (i64.const 0x100000000)))
  (func $fac (export "fac") (param i64) (result i64)
    (if (result i64) (i64.eqz (local.get 0))
      (then (i64.const 1))
      (else (i64.mul (local.get 0) (call $fac (i64.sub (local.get 0) (i64.const 1)))))))
  (func (export "mulcall") (param i64) (result i64)
    (if (result i64) (i64.eqz (local.get 0))
      (then (i64.const 1))
      (else (i64.mul (local.get 0)
        (call $g (i32.wrap_i64 (i64.sub (local.get 0) (i64.const 1)))))))))
"#;

#[test]
fn i64_operand_live_across_call_1785() {
    let mut steps: Vec<(&str, Vec<WasmValue>)> = Vec::new();
    for n in [0u64, 1, 5, 20, 25] {
        steps.push(("fac", vec![l(n)]));
    }
    for n in [0u64, 1, 5, 0x1_0000_0007, u64::MAX] {
        steps.push(("mulcall", vec![l(n)]));
    }
    let (mut agree, mut red) = (0usize, Vec::new());
    for leg in &HOSTED[..3] {
        let (wasm, out) = match build(LIVE_ACROSS_WAT, leg.flags) {
            Ok(b) => b,
            Err(e) => {
                red.push(format!("{}: {e}", leg.name));
                continue;
            }
        };
        let obj = synth_oracle::synth::CompiledObject::parse(&out).expect("object parses");
        let cfg = HostConfig::new(leg.cpu, LINMEM);
        for (e, a) in &steps {
            match run_hosted(&wasm, &obj, &[(e, &a[..])], FUEL, &Imports::new(), &cfg) {
                Ok(c) if c.len() == 1 && c[0].verdict.is_agree() => agree += 1,
                Ok(c) => red.extend(c.iter().map(|c| format!("{}: {}", leg.name, show_case(c)))),
                Err(err) => red.push(format!("{}: {e}{a:?}: {err:?}", leg.name)),
            }
        }
    }
    match build(LIVE_ACROSS_WAT, &["--target", "cortex-m4", "--cortex-m"]) {
        Ok((wasm, out)) => match BootedImage::boot(&out, Cpu::CortexM4, false) {
            Ok(mut img) => {
                for (e, a) in &steps {
                    let r = reference::run(&wasm, e, a, FUEL, &Imports::new()).expect("kiln");
                    let sigt = export_signature(&wasm, e).unwrap();
                    match img.call(e, &sigt, a, 1_000_000) {
                        Ok(run) if verdict(&r.outcome, &run.outcome).is_agree() => agree += 1,
                        Ok(run) => red.push(format!(
                            "--cortex-m: {e}{a:?}: kiln {:?} | machine code {:?}",
                            r.outcome, run.outcome
                        )),
                        Err(err) => red.push(format!("--cortex-m: {e}{a:?}: {err:?}")),
                    }
                }
            }
            Err(e) => red.push(format!("--cortex-m: boot {e:?}")),
        },
        Err(e) => red.push(format!("--cortex-m: {e}")),
    }
    assert!(red.is_empty(), "\n{}", red.join("\n"));
    println!("ORACLE i64-call-args-1785 live-across-call: {agree} steps agree across 4 legs");
    assert_eq!(agree, 4 * steps.len());
}
