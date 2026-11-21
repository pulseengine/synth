//! RQ-92-WDGTHIN (Refs #1741, #1301): direct calls on ARMv6-M (Cortex-M0/M0+) —
//! calls to functions of the module and to function imports — executed on
//! unicorn's Cortex-M0 model against kiln.
//!
//! This is the second execution differential of the ARMv6-M leg (the first,
//! `armv6m_i32_oracle.rs`, covers the call-free i32 core). What gale v0.12.0
//! needs from synth on NUCLEO-G031K8 is "i32 lowering plus gust:hal import
//! calls": a dissolved driver is i32 arithmetic around calls into the HAL.
//! [`DRIVER_WAT`] is that shape (a watchdog driver over `gust:hal` MMIO
//! imports), and [`CALLS_WAT`] is one probe per call shape.
//!
//! Each module is compiled for `cortex-m0` and `cortex-m0plus` on DEFAULT
//! flags. A module that calls a function import is a relocatable object
//! without `--relocatable` (the v0.92 import-ABI rule), and ARMv6-M follows it:
//! the default-flags object is the `--relocatable` object, byte for byte.
//!
//! 1. ACCEPTANCE, EXACT both ways: every export of the two modules compiles,
//!    and [`DECLINE_WAT`]'s shapes (an outgoing stack argument, an indirect
//!    call, a 64-bit argument, a 64-bit value live across a call) decline,
//!    each for its named cause. RED on the
//!    previous base, where every function containing a call declined ("no
//!    ARMv6-M rule for `Bl`") and the default-flags compile was refused.
//! 2. ARMv6-M, DECODED: every halfword of `.text` is in the frozen
//!    LLVM-derived ARMv6-M table, and the only 32-bit encodings are `BL`, one
//!    per `R_ARM_THM_CALL` relocation. No write to R8-R12.
//! 3. EXECUTION: the object is linked the way an embedder links it
//!    (`synth_oracle::hosted`: a host stub per import symbol, AAPCS arguments,
//!    every caller-saved register clobbered when a host call returns; R4-R11
//!    and SP checked when the export returns) and every step is required to
//!    agree with kiln — the same result AND the same host calls with the same
//!    arguments in the same order. Calls BETWEEN functions of the object are
//!    held to AAPCS as well: R4-R11 are compared across every internal call,
//!    and R2, R3 and R12 are clobbered when it returns
//!    (`internal_callee_that_loses_r4_is_caught`).
//!
//! WHAT "ON THE CORTEX-M0 MODEL" PROVES, MEASURED HERE. unicorn's Cortex-M0
//! model raises an illegal-instruction fault on a 32-bit Thumb-2 encoding
//! other than `BL` (`v7m_code_faults_on_the_m0_model`: the same module
//! compiled for cortex-m3 faults on its `push.w`). It does NOT fault on the
//! two 16-bit ARMv7-M additions, IT and CBZ/CBNZ: it executes them
//! (`m0_model_executes_cbz_and_it`, pinned so the statement stays measured).
//! Those two are what the decode leg is for; execution and decode together
//! are the ARMv6-M check, neither alone.
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary.

#![cfg(feature = "exec")]

use std::collections::BTreeSet;
use std::path::PathBuf;

use synth_oracle::armv6m::{is_prefix, legal16_table, v6m_violations};
use synth_oracle::compare::{EmuOutcome, Verdict};
use synth_oracle::emulate::Cpu;
use synth_oracle::hosted::{HostConfig, Hosted};
use synth_oracle::reference::Imports;
use synth_oracle::synth::{CompiledObject, FuncSym, Machine, R_ARM_THM_CALL, compile};
use synth_oracle::value::WasmValue;
use synth_oracle::{HostedCase, run_hosted};

const FUEL: u64 = 1_000_000;
/// The modules have no linear memory; R11 is set here and must come back
/// unchanged.
const LINMEM: u32 = 0x2001_0000;
const TARGETS: &[&str] = &["cortex-m0", "cortex-m0plus"];

/// A dissolved watchdog driver: i32 arithmetic and control flow around
/// `gust:hal` MMIO imports. Register offsets are the STM32G0 IWDG's.
const DRIVER_WAT: &str = r#"
(module
  (import "gust:hal/mmio" "read32" (func $rd (param i32) (result i32)))
  (import "gust:hal/mmio" "write32" (func $wr (param i32 i32)))
  (import "gust:hal/clock" "ticks" (func $ticks (result i32)))
  ;; IWDG_KR = base + 0, IWDG_PR = base + 4, IWDG_RLR = base + 8, IWDG_SR = base + 12
  (func $reg (param i32) (result i32) i32.const 0x40003000 local.get 0 i32.add)
  (func $busy (result i32) i32.const 12 call $reg call $rd i32.const 7 i32.and)
  (func (export "wdg_kick")
    i32.const 0 call $reg i32.const 0xAAAA call $wr)
  (func (export "wdg_status") (result i32) call $busy)
  ;; Unlock, program prescaler and reload, start; return the status after.
  (func (export "wdg_start") (param $pr i32) (param $reload i32) (result i32)
    i32.const 0 call $reg i32.const 0x5555 call $wr
    i32.const 4 call $reg local.get $pr i32.const 7 i32.and call $wr
    i32.const 8 call $reg local.get $reload i32.const 0xFFF i32.and call $wr
    i32.const 0 call $reg i32.const 0xCCCC call $wr
    call $busy)
  ;; Poll the status register at most (n & 7) times; return the polls left.
  (func (export "wdg_wait") (param $n i32) (result i32)
    local.get $n i32.const 7 i32.and local.set $n
    block
      loop
        local.get $n i32.eqz br_if 1
        call $busy i32.eqz br_if 1
        local.get $n i32.const 1 i32.sub local.set $n
        br 0
      end
    end
    local.get $n)
  ;; Time left until a deadline: a result used in a compare and a select.
  (func (export "wdg_remaining") (param $deadline i32) (result i32) (local $now i32)
    call $ticks local.set $now
    i32.const 0
    local.get $deadline local.get $now i32.sub
    local.get $now local.get $deadline i32.ge_u
    select)
  ;; Read-modify-write of the prescaler: the read's result feeds the write.
  (func (export "wdg_set_prescaler") (param $pr i32) (result i32) (local $old i32)
    i32.const 4 call $reg call $rd local.set $old
    i32.const 4 call $reg
    local.get $old i32.const -8 i32.and local.get $pr i32.const 7 i32.and i32.or
    call $wr
    local.get $old)
)
"#;

/// One probe per call shape.
const CALLS_WAT: &str = r#"
(module
  (import "env" "log" (func $log (param i32)))
  (import "env" "rd" (func $rd (param i32) (result i32)))
  (import "env" "sub2" (func $sub2 (param i32 i32) (result i32)))
  (import "env" "mix3" (func $mix3 (param i32 i32 i32) (result i32)))
  (import "env" "mix4" (func $mix4 (param i32 i32 i32 i32) (result i32)))
  (import "env" "seven" (func $seven (result i32)))
  (import "env" "wide" (func $wide (param i32) (result i64)))
  (func $widen (param i32) (result i64) local.get 0 i64.extend_i32_u)
  (func $inc (param i32) (result i32) local.get 0 i32.const 1 i32.add)
  (func $sub (param i32 i32) (result i32) local.get 0 local.get 1 i32.sub)
  (func $viaimp (param i32) (result i32) local.get 0 call $rd i32.const 3 i32.add)
  (func $nop)
  ;; --- calls to functions of the module ---
  (func (export "local_call") (param i32) (result i32) local.get 0 call $inc)
  (func (export "local_chain") (param i32) (result i32)
    local.get 0 call $inc call $inc local.get 0 i32.add)
  (func (export "local_order") (param i32 i32) (result i32)
    local.get 1 local.get 0 call $sub)
  (func (export "local_void") (param i32) (result i32) call $nop local.get 0)
  (func (export "local_then_import") (param i32) (result i32) local.get 0 call $viaimp)
  ;; --- import calls: results, arguments, order ---
  (func (export "imp_result") (param i32) (result i32) local.get 0 call $rd)
  (func (export "imp_noarg") (result i32) call $seven)
  (func (export "imp_const_args") (result i32) i32.const 3 i32.const 11 call $sub2)
  (func (export "imp_ordered") (param i32 i32) (result i32)
    local.get 0 local.get 1 call $sub2)
  (func (export "imp_swapped") (param i32 i32) (result i32)
    local.get 1 local.get 0 call $sub2)
  (func (export "imp_computed") (param i32 i32) (result i32)
    local.get 0 i32.const 300 i32.add local.get 1 i32.const 7 i32.shl call $sub2)
  (func (export "imp_three") (param i32 i32 i32) (result i32)
    local.get 2 local.get 0 local.get 1 call $mix3)
  (func (export "imp_four") (param i32 i32 i32 i32) (result i32)
    local.get 3 local.get 2 local.get 1 local.get 0 call $mix4)
  ;; --- values live across a call ---
  (func (export "param_across") (param i32) (result i32)
    local.get 0 call $log local.get 0)
  (func (export "temp_across") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.mul local.get 0 call $log local.get 1 i32.add)
  (func (export "phantom") (param i32) (result i32)
    i32.const 5 local.get 0 call $log)
  (func (export "result_across") (param i32 i32) (result i32)
    local.get 0 call $rd local.get 1 call $rd i32.sub)
  (func (export "two_calls") (param i32 i32) (result i32)
    local.get 0 local.get 1 call $sub2
    local.get 1 local.get 0 call $sub2
    i32.mul)
  ;; --- calls under control flow ---
  (func (export "call_in_if") (param i32 i32) (result i32)
    local.get 0 if (result i32) local.get 1 call $rd
    else local.get 0 local.get 1 call $sub2 end)
  (func (export "cond_on_result") (param i32) (result i32)
    local.get 0 call $rd i32.const 1 i32.and if (result i32) i32.const 100
    else i32.const 200 end)
  (func (export "call_in_loop") (param i32) (result i32) (local i32)
    local.get 0 i32.const 7 i32.and local.set 0
    block loop
      local.get 0 i32.eqz br_if 1
      local.get 1 local.get 0 call $rd i32.xor local.set 1
      local.get 0 call $log
      local.get 0 i32.const 1 i32.sub local.set 0
      br 0
    end end
    local.get 1)
  (func (export "select_of_results") (param i32 i32 i32) (result i32)
    local.get 0 call $rd local.get 1 call $rd local.get 2 select)
  (func (export "call_in_br_table") (param i32 i32) (result i32)
    block block block
      local.get 0 br_table 0 1 2
    end local.get 1 call $rd return
    end local.get 1 i32.const 1 i32.add call $rd return
    end local.get 1)
  ;; --- results: dropped, and 64-bit (R0:R1) ---
  (func (export "drop_result") (param i32) (result i32)
    local.get 0 call $rd drop local.get 0)
  (func (export "imp_i64_result") (param i32) (result i64) local.get 0 call $wide)
  (func (export "local_i64_result") (param i32) (result i64) local.get 0 call $widen)
)
"#;

/// Call shapes ARMv6-M does not lower. Compiled only for the decline pin.
const DECLINE_WAT: &str = r#"
(module
  (import "env" "five" (func $five (param i32 i32 i32 i32 i32) (result i32)))
  (import "env" "wide_arg" (func $wide_arg (param i64) (result i32)))
  (import "env" "one" (func $one (param i32) (result i32)))
  (type $t (func (param i32) (result i32)))
  (table 1 funcref)
  (func $six (param i32 i32 i32 i32 i32 i32) (result i32) local.get 0)
  (func (export "d_stack_arg_import") (param i32) (result i32)
    local.get 0 local.get 0 local.get 0 local.get 0 local.get 0 call $five)
  (func (export "d_stack_arg_local") (param i32) (result i32)
    local.get 0 local.get 0 local.get 0 local.get 0 local.get 0 local.get 0 call $six)
  (func (export "d_call_indirect") (param i32) (result i32)
    local.get 0 i32.const 0 call_indirect (type $t))
  (func (export "d_i64_arg") (param i64) (result i32) local.get 0 call $wide_arg)
  ;; A 64-bit value live across a call is kept in a frame slot pair.
  (func (export "d_i64_across") (param i64 i32) (result i64)
    local.get 1 call $one drop local.get 0)
)
"#;

/// The decline probes and the cause each diagnostic must name.
const DECLINED: &[(&str, &str)] = &[
    (
        "d_stack_arg_import",
        "ARMv6-M lowering, RQ-91-M0I32 (#1301): the call to function 0 passes 5 arguments",
    ),
    (
        "d_stack_arg_local",
        "ARMv6-M lowering, RQ-91-M0I32 (#1301): the call to function 3 passes 6 arguments",
    ),
    ("d_call_indirect", "no ARMv6-M rule for `CallIndirect"),
    // #1785 lowers i64 call arguments on v7-M; the i64 store has no ARMv6-M
    // rule, so ARMv6-M still refuses the function, by name.
    ("d_i64_arg", "no ARMv6-M rule for `I64Str"),
    ("d_i64_across", "no ARMv6-M rule for `I64Str"),
];

fn imports() -> Imports {
    let one = |f: fn(u32) -> u32| {
        move |a: &[WasmValue]| match a {
            [WasmValue::I32(x)] => Ok(vec![WasmValue::I32(f(*x))]),
            _ => Err(format!("bad args {a:?}")),
        }
    };
    let two = |f: fn(u32, u32) -> u32| {
        move |a: &[WasmValue]| match a {
            [WasmValue::I32(x), WasmValue::I32(y)] => Ok(vec![WasmValue::I32(f(*x, *y))]),
            _ => Err(format!("bad args {a:?}")),
        }
    };
    // A register bank as a pure function of the address, so both engines read
    // the same thing without shared state. Order-sensitive mixes for the
    // multi-argument imports: a swapped argument changes the result.
    let reg = |a: u32| a.rotate_left(5) ^ 0x5A5A_A5A5;
    Imports::new()
        .func("gust:hal/mmio", "read32", one(reg))
        .trace("gust:hal/mmio", "write32", vec![])
        .trace("gust:hal/clock", "ticks", vec![WasmValue::I32(1_000)])
        .trace("env", "log", vec![])
        .func("env", "rd", one(reg))
        .func("env", "sub2", two(u32::wrapping_sub))
        .func("env", "mix3", |a: &[WasmValue]| match a {
            [WasmValue::I32(x), WasmValue::I32(y), WasmValue::I32(z)] => Ok(vec![WasmValue::I32(
                x.wrapping_mul(3)
                    .wrapping_add(y.wrapping_mul(5))
                    .wrapping_add(z.wrapping_mul(7)),
            )]),
            _ => Err(format!("bad args {a:?}")),
        })
        .func("env", "mix4", |a: &[WasmValue]| match a {
            [
                WasmValue::I32(w),
                WasmValue::I32(x),
                WasmValue::I32(y),
                WasmValue::I32(z),
            ] => Ok(vec![WasmValue::I32(
                w.wrapping_mul(3)
                    .wrapping_add(x.wrapping_mul(5))
                    .wrapping_add(y.wrapping_mul(7))
                    .wrapping_add(z.wrapping_mul(11)),
            )]),
            _ => Err(format!("bad args {a:?}")),
        })
        .trace("env", "seven", vec![WasmValue::I32(7)])
        .func("env", "wide", |a: &[WasmValue]| match a {
            [WasmValue::I32(x)] => Ok(vec![WasmValue::I64(
                (u64::from(!*x) << 32) | u64::from(x.rotate_left(9)),
            )]),
            _ => Err(format!("bad args {a:?}")),
        })
}

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-oracle-m0call-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

struct Built {
    wasm: Vec<u8>,
    object: Option<CompiledObject>,
    file: Vec<u8>,
    ok: bool,
    stderr: String,
}

/// Compile `wat` for `target` with `--all-exports` plus `extra`.
fn compile_with(wat: &str, target: &str, extra: &[&str]) -> Built {
    let wasm = wat::parse_str(wat).expect("WAT parses");
    let dir = scratch();
    let input = dir.join("m.wasm");
    std::fs::write(&input, &wasm).unwrap();
    let out = dir.join("m.o");
    let mut flags = vec!["--target", target, "--all-exports"];
    flags.extend_from_slice(extra);
    let run = compile(&input, &flags, &out).expect("synth runs");
    Built {
        wasm,
        file: std::fs::read(&out).unwrap_or_default(),
        ok: run.status.success(),
        object: run.object,
        stderr: run.stderr,
    }
}

/// The default-flags object of `wat`, which must compile completely.
fn compile_default(wat: &str, target: &str) -> (Vec<u8>, CompiledObject) {
    let b = compile_with(wat, target, &[]);
    assert!(b.ok, "{target}: synth compile failed: {}", b.stderr);
    (b.wasm, b.object.expect("object parsed"))
}

fn exports(wat_src: &str) -> Vec<String> {
    let w = wat::parse_str(wat_src).unwrap();
    let mut v = Vec::new();
    for p in wasmparser::Parser::new(0).parse_all(&w) {
        if let Ok(wasmparser::Payload::ExportSection(s)) = p {
            for e in s {
                let e = e.unwrap();
                if e.kind == wasmparser::ExternalKind::Func {
                    v.push(e.name.to_string());
                }
            }
        }
    }
    v
}

fn i(v: u32) -> WasmValue {
    WasmValue::I32(v)
}

type Step = (&'static str, Vec<WasmValue>);

const VALS: &[u32] = &[0, 1, 7, 0xFF, 0x100, 0x7FFF_FFFF, 0x8000_0000, 0xDEAD_BEEF];

fn pairs() -> Vec<(u32, u32)> {
    vec![
        (10, 20),
        (0, 0),
        (1, 0xFFFF_FFFF),
        (0x8000_0000, 3),
        (30, 10),
        (0xDEAD_BEEF, 0x1234_5678),
    ]
}

fn driver_steps() -> Vec<Step> {
    let mut s: Vec<Step> = vec![("wdg_kick", vec![]), ("wdg_status", vec![])];
    for (a, b) in pairs() {
        s.push(("wdg_start", vec![i(a), i(b)]));
    }
    for &v in VALS {
        s.push(("wdg_wait", vec![i(v)]));
        s.push(("wdg_remaining", vec![i(v)]));
        s.push(("wdg_set_prescaler", vec![i(v)]));
    }
    // The deadline on both sides of the clock's 1000 ticks.
    for v in [999, 1_000, 1_001, 5_000] {
        s.push(("wdg_remaining", vec![i(v)]));
    }
    s
}

fn call_steps() -> Vec<Step> {
    let mut s: Vec<Step> = vec![("imp_noarg", vec![]), ("imp_const_args", vec![])];
    for &v in VALS {
        for e in [
            "local_call",
            "local_chain",
            "local_void",
            "local_then_import",
            "imp_result",
            "param_across",
            "phantom",
            "cond_on_result",
            "call_in_loop",
            "drop_result",
            "imp_i64_result",
            "local_i64_result",
        ] {
            s.push((e, vec![i(v)]));
        }
    }
    for (a, b) in pairs() {
        for e in [
            "local_order",
            "imp_ordered",
            "imp_swapped",
            "imp_computed",
            "temp_across",
            "result_across",
            "two_calls",
            "call_in_if",
        ] {
            s.push((e, vec![i(a), i(b)]));
        }
        s.push(("call_in_if", vec![i(0), i(b)]));
        for sel in [0, 1, 2, 3] {
            s.push(("call_in_br_table", vec![i(sel), i(a)]));
        }
        for c in [0, 1] {
            s.push(("imp_three", vec![i(a), i(b), i(c)]));
            s.push(("select_of_results", vec![i(a), i(b), i(c)]));
        }
        s.push(("imp_four", vec![i(a), i(b), i(a ^ 0x55), i(b ^ 0xAA)]));
    }
    s
}

fn show(c: &HostedCase) -> String {
    format!(
        "{}{:?}: kiln {:?} calls {:?} | machine code {:?} calls {:?} | {:?}",
        c.export, c.args, c.reference, c.ref_calls, c.emulator, c.emu_calls, c.verdict
    )
}

/// Every step on its own image and kiln instance (the modules hold no state),
/// so one wrong step does not hide the next. Returns (steps, host calls).
fn run_steps(
    what: &str,
    wasm: &[u8],
    obj: &CompiledObject,
    steps: &[Step],
    cpu: Cpu,
    red: &mut Vec<String>,
) -> (usize, usize) {
    let cfg = HostConfig::new(cpu, LINMEM);
    let mut calls = 0;
    for (e, a) in steps {
        match run_hosted(wasm, obj, &[(*e, &a[..])], FUEL, &imports(), &cfg) {
            Ok(cases) => {
                if cases.len() != 1 {
                    red.push(format!("{what}: {e}{a:?} did not run"));
                }
                for c in &cases {
                    calls += c.emu_calls.len();
                    if !c.verdict.is_agree() {
                        red.push(format!("{what}: {}", show(c)));
                    }
                }
            }
            Err(err) => red.push(format!("{what}: {e}{a:?}: harness error {err:?}")),
        }
    }
    (steps.len(), calls)
}

// ---------------------------------------------------------------- gates --

#[test]
fn every_call_shape_compiles_and_the_refused_ones_say_why() {
    let mut accepted = 0;
    for target in TARGETS {
        for (name, wat) in [("driver", DRIVER_WAT), ("calls", CALLS_WAT)] {
            let (_w, obj) = compile_default(wat, target);
            let all = exports(wat);
            let missing: Vec<&String> = all.iter().filter(|e| obj.func(e).is_none()).collect();
            assert!(
                missing.is_empty(),
                "{target} {name}: exports that did not compile: {missing:?}"
            );
            accepted += all.len();
        }
        let d = compile_with(DECLINE_WAT, target, &["--allow-skipped-exports"]);
        let all = exports(DECLINE_WAT);
        let declined: BTreeSet<&str> = all
            .iter()
            .filter(|e| d.object.as_ref().is_none_or(|o| o.func(e).is_none()))
            .map(|s| s.as_str())
            .collect();
        let want: BTreeSet<&str> = DECLINED.iter().map(|(n, _)| *n).collect();
        assert_eq!(declined, want, "{target}: declined set moved: {}", d.stderr);
        for (n, cause) in DECLINED {
            let line = d
                .stderr
                .lines()
                .find(|l| l.contains(&format!("skipping function '{n}'")))
                .unwrap_or_else(|| panic!("{target}: no skip diagnostic for {n}:\n{}", d.stderr));
            assert!(
                line.contains(cause),
                "{target}: {n} declined, but not for `{cause}`: {line}"
            );
        }
        // Without the escape hatch a declined export is a hard refusal.
        assert!(
            !compile_with(DECLINE_WAT, target, &[]).ok,
            "{target}: a module with declined exports compiled at exit 0"
        );
    }
    eprintln!(
        "ORACLE armv6m-call: {} of {} call probes accepted, {} of {} decline probes declined, on {} targets",
        accepted / TARGETS.len(),
        exports(DRIVER_WAT).len() + exports(CALLS_WAT).len(),
        DECLINED.len(),
        exports(DECLINE_WAT).len(),
        TARGETS.len()
    );
}

/// The v0.92 import-ABI rule on ARMv6-M: a module that calls a function
/// import is the `--relocatable` object without the flag, and a module that
/// calls none is still refused as a self-contained image.
#[test]
fn default_flags_object_is_the_relocatable_object() {
    let mut same = 0;
    for target in TARGETS {
        for wat in [DRIVER_WAT, CALLS_WAT] {
            let default = compile_with(wat, target, &[]);
            let reloc = compile_with(wat, target, &["--relocatable"]);
            assert!(default.ok && reloc.ok, "{target}: {}", default.stderr);
            assert!(!default.file.is_empty());
            assert_eq!(
                default.file, reloc.file,
                "{target}: the default-flags object differs from --relocatable"
            );
            // ET_REL (e_type at offset 16 == 1).
            assert_eq!(u16::from_le_bytes([default.file[16], default.file[17]]), 1);
            assert!(default.object.as_ref().is_some_and(|o| o.relocatable));
            same += 1;
        }
        // CONTROL: no import call, so no host-link rule, so the ARMv6-M
        // self-contained-image refusal still fires.
        let leaf = "(module (func (export \"f\") (param i32) (result i32) local.get 0))";
        let b = compile_with(leaf, target, &[]);
        assert!(!b.ok, "{target}: a self-contained ARMv6-M image compiled");
        assert!(
            b.stderr.contains("supports only `--relocatable` objects"),
            "{target}: {}",
            b.stderr
        );
        assert!(compile_with(leaf, target, &["--relocatable"]).ok);
    }
    eprintln!(
        "ORACLE armv6m-call structural: {same} default-flags objects are byte-identical to --relocatable"
    );
}

#[test]
fn call_code_decodes_as_armv6m_and_every_wide_instruction_is_a_bl() {
    let table = legal16_table();
    let (mut halfwords, mut bls) = (0usize, 0usize);
    for wat in [DRIVER_WAT, CALLS_WAT] {
        let (_w, m0) = compile_default(wat, "cortex-m0");
        let (_w, m0p) = compile_default(wat, "cortex-m0plus");
        assert_eq!(
            m0.text, m0p.text,
            "cortex-m0plus .text differs from cortex-m0"
        );
        let bad = v6m_violations(&m0.text, &table);
        assert!(bad.is_empty(), "not ARMv6-M: {bad:?}");
        // Every 32-bit encoding is a BL, and each BL carries the one kind of
        // relocation the object has.
        let hw = |k: usize| u16::from_le_bytes([m0.text[k], m0.text[k + 1]]);
        let mut wide = BTreeSet::new();
        let mut k = 0;
        while k + 1 < m0.text.len() {
            if is_prefix(hw(k)) {
                assert!(
                    hw(k) >> 11 == 0b11110 && hw(k + 2) & 0xD000 == 0xD000,
                    "+{k:x}: a 32-bit instruction that is not BL"
                );
                wide.insert(k as u64);
                k += 4;
            } else {
                k += 2;
            }
        }
        assert!(m0.relocs.iter().all(|r| r.r_type == R_ARM_THM_CALL));
        let sites: BTreeSet<u64> = m0.relocs.iter().map(|r| r.offset).collect();
        assert_eq!(wide, sites, "BL sites and relocation sites differ");
        halfwords += m0.text.len() / 2;
        bls += wide.len();
    }
    eprintln!("ORACLE armv6m-call decode: {halfwords} halfwords, all ARMv6-M, {bls} BL");
    assert_eq!(bls, 54, "BL count moved");
}

#[test]
fn calls_agree_with_kiln_on_the_m0_model() {
    let mut red = Vec::new();
    let (mut steps, mut calls) = (0, 0);
    for target in TARGETS {
        for (name, wat, st) in [
            ("driver", DRIVER_WAT, driver_steps()),
            ("calls", CALLS_WAT, call_steps()),
        ] {
            let (wasm, obj) = compile_default(wat, target);
            let (s, c) = run_steps(
                &format!("{target} {name}"),
                &wasm,
                &obj,
                &st,
                Cpu::CortexM0,
                &mut red,
            );
            steps += s;
            calls += c;
        }
    }
    assert!(
        red.is_empty(),
        "{} disagreement(s):\n{}",
        red.len(),
        red.join("\n")
    );
    eprintln!(
        "ORACLE armv6m-call: {steps} steps agree on the Cortex-M0 model across {} targets, {calls} host calls matched",
        TARGETS.len()
    );
    // EXACT literals: a shrunk probe set or step list reds here.
    assert_eq!(steps, 484, "step count moved");
    assert_eq!(calls, 638, "host-call count moved");
}

// --------------------------------------------------------------- potency --

/// The execution leg is an ARMv6-M check for 32-bit encodings: the SAME
/// module compiled for cortex-m3 faults as ILLEGAL on the Cortex-M0 model
/// (its prologue is `push.w`), and runs correctly on the Cortex-M3 model.
#[test]
fn v7m_code_faults_on_the_m0_model() {
    let b = compile_with(CALLS_WAT, "cortex-m3", &[]);
    assert!(b.ok, "cortex-m3: {}", b.stderr);
    let obj = b.object.unwrap();
    let step: [(&str, &[WasmValue]); 1] = [("imp_result", &[i(7)])];
    let on = |cpu: Cpu| {
        run_hosted(
            &b.wasm,
            &obj,
            &step,
            FUEL,
            &imports(),
            &HostConfig::new(cpu, LINMEM),
        )
        .unwrap()
        .remove(0)
    };
    let m0 = on(Cpu::CortexM0);
    assert!(
        matches!(m0.emulator, EmuOutcome::Illegal { .. }),
        "v7-M code on the M0 model: {:?}",
        m0.emulator
    );
    assert!(!m0.verdict.is_agree());
    let m3 = on(Cpu::CortexM3);
    assert!(m3.verdict.is_agree(), "control: {}", show(&m3));
}

fn hand(funcs: &[(&str, &[u16])]) -> CompiledObject {
    let mut text = Vec::new();
    let mut map = std::collections::BTreeMap::new();
    for (name, halfwords) in funcs {
        let offset = text.len() as u64;
        for h in *halfwords {
            text.extend_from_slice(&h.to_le_bytes());
        }
        map.insert(
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
        path: PathBuf::from("<hand-written>"),
        machine: Machine::Arm,
        text,
        funcs: map,
        text_relocs: Vec::new(),
        relocs: Vec::new(),
        relocatable: true,
        e_flags: 0,
    }
}

/// MEASURED, so the module doc's statement stays true: unicorn's Cortex-M0
/// model executes CBZ and IT, the two 16-bit ARMv7-M additions. The decode
/// leg refuses both. If this test turns red the model started faulting on
/// them, and the doc's "execution and decode together" can be tightened.
#[test]
fn m0_model_executes_cbz_and_it() {
    let table = legal16_table();
    let wasm =
        wat::parse_str("(module (func (export \"f\") (param i32) (result i32) local.get 0))")
            .unwrap();
    for (what, code, want) in [
        // cbz r0, +0 (to the bx); movs r0, #9; bx lr
        ("CBZ", &[0xB100u16, 0x2009, 0x4770][..], [0u32, 9]),
        // cmp r0, #0; it eq; moveq r0, #5; bx lr
        ("IT", &[0x2800, 0xBF08, 0x2005, 0x4770][..], [5, 1]),
    ] {
        let obj = hand(&[("f", code)]);
        assert!(
            !v6m_violations(&obj.text, &table).is_empty(),
            "{what}: the decode leg missed it"
        );
        let mut image = Hosted::link(
            &obj,
            &wasm,
            &Imports::new(),
            &HostConfig::new(Cpu::CortexM0, LINMEM),
        )
        .unwrap();
        for (arg, want) in [0u32, 1].into_iter().zip(want) {
            let run = image.call("f", &[i(arg)]).unwrap();
            assert_eq!(
                run.outcome,
                EmuOutcome::Values(vec![i(want)]),
                "{what}: the Cortex-M0 model did not execute it for f({arg})"
            );
        }
    }
}

/// Internal callees that save R4, from the cold review's probe module: a
/// caller that keeps nothing in R4 across the call hides a callee that loses
/// it, unless internal calls are checked themselves.
const INTERNAL_WAT: &str = r#"
(module
  (import "env" "rd" (func $rd (param i32) (result i32)))
  (func $f (param i32) (result i32) local.get 0 i32.const 3 i32.mul)
  (func $g (param i32 i32) (result i32) local.get 0 call $f local.get 1 call $f i32.add)
  (func $rec (param i32) (result i32)
    local.get 0 i32.const 15 i32.and local.tee 0 i32.eqz if (result i32) i32.const 1
    else local.get 0 local.get 0 i32.const 1 i32.sub call $rec i32.add end)
  (func $fib (param i32) (result i32)
    local.get 0 i32.const 2 i32.lt_u if (result i32) local.get 0
    else local.get 0 i32.const 1 i32.sub call $fib local.get 0 i32.const 2 i32.sub call $fib i32.add end)
  (func $heavy (param i32 i32) (result i32) (local i32 i32 i32 i32)
    local.get 0 local.get 1 i32.xor local.set 2
    local.get 0 local.get 1 i32.add local.set 3
    local.get 2 local.get 3 i32.mul local.set 4
    local.get 4 local.get 0 i32.sub local.set 5
    local.get 2 local.get 3 i32.add local.get 4 i32.add local.get 5 i32.xor)
  (func (export "nested") (param i32 i32) (result i32) local.get 0 local.get 1 call $g call $rd)
  (func (export "rec") (param i32) (result i32) local.get 0 call $rec)
  (func (export "fib") (param i32) (result i32) local.get 0 i32.const 15 i32.and call $fib)
  (func (export "across_heavy") (param i32 i32 i32) (result i32) (local i32 i32)
    local.get 0 local.get 1 i32.add local.set 3
    local.get 1 local.get 2 i32.sub local.set 4
    local.get 0 local.get 2 call $heavy
    local.get 3 i32.xor local.get 4 i32.add local.get 0 i32.add local.get 1 i32.mul local.get 2 i32.sub)
)
"#;

/// Cold review F4. Dropping R4 from the push and pop of ONE internal function
/// is caught, by the internal-call check itself, for each of the three whose
/// body WRITES R4 ($g, $rec, $fib): the caller's epilogue restores R4, so the
/// export-level check and the returned value miss it. The unmutated object
/// agrees, and its internal calls are counted, so the check is known to have
/// run.
///
/// The fourth, $heavy, is pinned as what it is in the code synth emits: an
/// EQUIVALENT mutant. R4 is in its push only as padding (`push {r2, r3, r4,
/// r5, r6, lr}`, keeping the selector's frame size) and no instruction of its
/// body writes R4, so with or without the save R4 comes back unchanged and
/// every step still agrees with kiln. No register check can red it. The sets
/// are exact both ways: if $heavy starts using R4, this test reds and the
/// mutant moves to the caught set.
#[test]
fn internal_callee_that_loses_r4_is_caught() {
    let (wasm, obj) = compile_default(INTERNAL_WAT, "cortex-m0");
    let cfg = HostConfig::new(Cpu::CortexM0, LINMEM);
    let steps: Vec<Step> = vec![
        ("nested", vec![i(3), i(80)]),
        ("rec", vec![i(6)]),
        ("fib", vec![i(7)]),
        ("across_heavy", vec![i(3), i(80), i(157)]),
        ("across_heavy", vec![i(0xDEAD_BEEF), i(1), i(2)]),
    ];
    // CONTROL: every step agrees, and internal calls returned and were checked.
    let mut image = Hosted::link(&obj, &wasm, &imports(), &cfg).unwrap();
    for (e, a) in &steps {
        let run = image.call(e, a).unwrap();
        assert!(
            matches!(run.outcome, EmuOutcome::Values(_)),
            "{e}{a:?}: {:?}",
            run.outcome
        );
    }
    let checked = image.internal_returns();
    let mut red = Vec::new();
    run_steps("internal", &wasm, &obj, &steps, Cpu::CortexM0, &mut red);
    assert!(red.is_empty(), "{red:?}");

    // Internal functions only: an export also carries a local `func_N` alias
    // at the same offset.
    let exported: BTreeSet<u64> = exports(INTERNAL_WAT)
        .iter()
        .map(|e| obj.func(e).expect("export compiled").offset)
        .collect();
    let mut mutants = Vec::new();
    for (name, f) in obj
        .funcs
        .iter()
        .filter(|(_, f)| !exported.contains(&f.offset))
    {
        let mut m = obj.clone();
        let (lo, hi) = (f.offset as usize, (f.offset + f.size) as usize);
        let mut changed = false;
        for k in (lo..hi.saturating_sub(1)).step_by(2) {
            let h = u16::from_le_bytes([m.text[k], m.text[k + 1]]);
            // push {.., r4, .., lr} / pop {.., r4, .., pc}
            if matches!(h & 0xFF00, 0xB500 | 0xBD00) && h & 0x10 != 0 {
                m.text[k..k + 2].copy_from_slice(&(h & !0x10).to_le_bytes());
                changed = true;
            }
        }
        if !changed {
            continue;
        }
        let mut by_internal_check = 0;
        let mut caught = 0;
        for (e, a) in &steps {
            let step: [(&str, &[WasmValue]); 1] = [(e, &a[..])];
            let c = run_hosted(&wasm, &m, &step, FUEL, &imports(), &cfg)
                .unwrap()
                .remove(0);
            if !c.verdict.is_agree() {
                caught += 1;
            }
            if matches!(&c.emulator, EmuOutcome::Illegal { reason, .. }
                if reason.contains(&format!("internal call to `{name}` returned with R4 clobbered")))
            {
                by_internal_check += 1;
            }
        }
        mutants.push((name.clone(), by_internal_check, caught));
    }
    let caught: Vec<&str> = mutants
        .iter()
        .filter(|(_, by_check, _)| *by_check > 0)
        .map(|(n, _, _)| n.as_str())
        .collect();
    let equivalent: Vec<&str> = mutants
        .iter()
        .filter(|(_, _, any)| *any == 0)
        .map(|(n, _, _)| n.as_str())
        .collect();
    eprintln!(
        "ORACLE armv6m-call internal: {} of {} callees that lose R4 are caught by the internal-call check, {} equivalent, {checked} internal returns checked",
        caught.len(),
        mutants.len(),
        equivalent.len()
    );
    // func_1 is $f (no R4 in its push); func_2..func_4 are $g, $rec, $fib;
    // func_5 is $heavy.
    assert_eq!(caught, ["func_2", "func_3", "func_4"], "{mutants:?}");
    assert_eq!(equivalent, ["func_5"], "{mutants:?}");
    assert_eq!(checked, 53, "internal returns on the unmutated object");
}

/// The other half of F4, on hand-written ARMv6-M code: a value kept in R2
/// across a call to a leaf that does not touch R2 reads back the clobber, not
/// the value, and a leaf that writes R5 without saving it is named.
#[test]
fn internal_call_clobbers_r2_and_checks_callee_saved() {
    use synth_oracle::hosted::CLOBBER;
    use synth_oracle::synth::TextReloc;
    let wasm =
        wat::parse_str("(module (func (export \"f\") (param i32) (result i32) local.get 0))")
            .unwrap();
    let cfg = HostConfig::new(Cpu::CortexM0, LINMEM);
    // f: push {r4, lr}; mov r2, r0; bl leaf; mov r0, r2; pop {r4, pc}
    let f: &[u16] = &[0xB510, 0x4602, 0xF7FF, 0xFFFE, 0x4610, 0xBD10];
    for (what, leaf, want) in [
        // leaf: bx lr
        (
            "R2 across a call",
            &[0x4770u16, 0x46C0][..],
            Ok(CLOBBER | 2),
        ),
        // leaf: movs r5, #9; bx lr
        (
            "a callee that loses R5",
            &[0x2509, 0x4770][..],
            Err("internal call to `leaf` returned with R5 clobbered"),
        ),
    ] {
        let mut obj = hand(&[("f", f), ("leaf", leaf)]);
        let target = obj.funcs["leaf"].offset;
        obj.relocs = vec![TextReloc {
            offset: 4,
            r_type: R_ARM_THM_CALL,
            addend: 0,
            symbol: "leaf".into(),
            target: Some(target),
            undefined: false,
        }];
        obj.text_relocs = vec![4];
        let mut image = Hosted::link(&obj, &wasm, &Imports::new(), &cfg).unwrap();
        let run = image.call("f", &[i(41)]).unwrap();
        match want {
            Ok(v) => assert_eq!(run.outcome, EmuOutcome::Values(vec![i(v)]), "{what}"),
            Err(reason) => assert!(
                matches!(&run.outcome, EmuOutcome::Illegal { reason: r, .. } if r.contains(reason)),
                "{what}: {:?}",
                run.outcome
            ),
        }
        assert_eq!(image.internal_returns(), 1, "{what}");
    }
}

/// A planted wrong reference reds, and on host-call ARGUMENTS where the
/// result happens to be equal: kiln is given `imp_swapped`'s body for
/// `imp_ordered`. For (0x8000_0000, 0) both orders return 0x8000_0000, so
/// only the logged arguments tell them apart.
#[test]
fn potency_planted_wrong_reference_reds() {
    let planted = CALLS_WAT.replacen(
        "(func (export \"imp_ordered\") (param i32 i32) (result i32)\n    local.get 0 local.get 1 call $sub2)",
        "(func (export \"imp_ordered\") (param i32 i32) (result i32)\n    local.get 1 local.get 0 call $sub2)",
        1,
    );
    assert_ne!(planted, CALLS_WAT);
    let wasm = wat::parse_str(&planted).unwrap();
    let (_w, obj) = compile_default(CALLS_WAT, "cortex-m0");
    let cfg = HostConfig::new(Cpu::CortexM0, LINMEM);
    let (mut by_value, mut by_calls) = (0, 0);
    for (a, b) in [(10u32, 20u32), (0, 1), (0x8000_0000, 0)] {
        let args = [i(a), i(b)];
        let step: [(&str, &[WasmValue]); 1] = [("imp_ordered", &args)];
        let c = run_hosted(&wasm, &obj, &step, FUEL, &imports(), &cfg)
            .unwrap()
            .remove(0);
        match &c.verdict {
            Verdict::Disagree(why) if why.contains("host calls differ") => by_calls += 1,
            Verdict::Disagree(_) => by_value += 1,
            v => panic!("planted swap agreed for ({a}, {b}): {v:?}"),
        }
    }
    assert_eq!((by_value, by_calls), (2, 1));
}
