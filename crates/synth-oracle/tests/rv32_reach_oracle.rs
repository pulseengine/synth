//! RV32 reach oracles (Refs #1254, #1724): kiln against unicorn RV32, with
//! linear memory compared BYTE FOR BYTE and host calls compared as a trace
//! (`synth_oracle::run_case_env`).
//!
//! - **#1254**: a linear-memory access whose memarg offset leaves the signed
//!   12-bit load/store immediate (above 2047, or 2043 for an i64's high word)
//!   was DECLINED (`immediate N too large for memory offset`). Every load and
//!   store width the RV32 selector lowers (`i32.load`, `load8_s/u`,
//!   `load16_s/u`, `i64.load`, `i32.store`, `store8`, `store16`,
//!   `i64.store`) is compiled at offsets 0, 2040, 2044, 2047, 2048, 4092,
//!   4095, 4096, 0x10000C (the issue's number) and two near the end of a
//!   2 MiB memory, under `--safety-bounds none`, `software` and `mask`, and
//!   run at in-bounds addresses up to the last byte. Under `software` it is
//!   also run OUT of bounds (one past the end, at the memory size, at
//!   0x80000000 and at an address whose sum with the offset wraps 2^32), and
//!   at two offsets no address can make in-bounds (the memory size and
//!   0xFFFFFFF0): each must trap, with memory unchanged. The issue's own
//!   constant-address shape (`i32.const 0; i32.load offset=1048588`) is run
//!   too.
//! - **#1724**: a call inside a control frame with a value pending BENEATH
//!   its arguments was declined (`Call(0)`). The issue's own module plus
//!   survivor {i32, i64, two i32} x frame {block, block in block, if-then,
//!   if-else, if in if, loop, loop in block} and the same survivors at
//!   depth 0 (the path that was already accepted, as a control). The host
//!   stubs clobber every caller-saved register, so a survivor left in one is
//!   caught.
//!
//! - **#1724, the cold review's 19 shapes** (`rv32_call_shapes_from_review_1724`):
//!   a value below the frame holding the call, loops, branch-result
//!   registers, a defined callee, six pending values, the #1717 slot area
//!   shared with an i64 `div_u`, frame locals, a void call, the `else` arm.
//!
//! Every object is also decoded under the `esp32c3` profile (RV32IMC, no A):
//! the new address materialization and the frame saves stay inside it.
//!
//! RED on the base (72bae955): every function above 2047 / in a frame is
//! missing from the object, which fails the presence check before anything
//! runs. Needs `--features exec`. `SYNTH` may name a prebuilt binary.

#![cfg(feature = "exec")]

use std::fmt::Write as _;
use std::path::PathBuf;

use synth_oracle::compare::{EmuOutcome, RefOutcome};
use synth_oracle::emulate::{Cpu, EmuConfig};
use synth_oracle::reference::Imports;
use synth_oracle::rv32_isa::{self, Profile};
use synth_oracle::synth::{CompileRun, CompiledObject, compile};
use synth_oracle::value::WasmValue;
use synth_oracle::{env_for, run_case_env};

const FUEL: u64 = 1_000_000;
const ESP32C3: Profile = Profile::new("esp32c3", true, false, true);

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-rv32reach-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn compile_rv32(wasm: &[u8], bounds: &str) -> CompileRun {
    let dir = scratch();
    let input = dir.join("m.wasm");
    std::fs::write(&input, wasm).unwrap();
    let flags = [
        "-b",
        "riscv",
        "--target",
        "esp32c3",
        "--relocatable",
        "--all-exports",
        "--allow-skipped-exports",
        "--safety-bounds",
        bounds,
    ];
    compile(&input, &flags, &dir.join(format!("m-{bounds}.o"))).expect("synth runs")
}

/// Every named export is in the object (the RED half: the base declines
/// them), and the object decodes inside RV32IMC.
fn assert_complete(run: &CompileRun, exports: &[String], what: &str) -> CompiledObject {
    assert!(run.status.success(), "{what}: {}", run.stderr);
    let obj = run.object.clone().expect("object");
    let missing: Vec<&String> = exports.iter().filter(|e| obj.func(e).is_none()).collect();
    assert!(
        missing.is_empty(),
        "{what}: {} of {} functions DECLINED, first {:?}\n{}",
        missing.len(),
        exports.len(),
        &missing[..missing.len().min(8)],
        run.stderr
            .lines()
            .filter(|l| l.contains("skipping"))
            .take(4)
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert_eq!(obj.e_flags, ESP32C3.e_flags(), "{what}: e_flags");
    let bad = rv32_isa::violations(&ESP32C3, &obj.text);
    assert!(bad.is_empty(), "{what}: outside RV32IMC: {:?}", &bad[..1]);
    obj
}

// ─── #1254 ────────────────────────────────────────────────────────────────

const PAGES: u32 = 32;
const MEM: u32 = PAGES * 65536; // 2 MiB: a power of two, so `mask` applies

#[derive(Clone, Copy)]
struct MemOp {
    wat: &'static str,
    tag: &'static str,
    size: u32,
    store: bool,
    i64: bool,
}

const fn ld(wat: &'static str, tag: &'static str, size: u32, i64: bool) -> MemOp {
    MemOp {
        wat,
        tag,
        size,
        store: false,
        i64,
    }
}
const fn st(wat: &'static str, tag: &'static str, size: u32, i64: bool) -> MemOp {
    MemOp {
        wat,
        tag,
        size,
        store: true,
        i64,
    }
}

const OPS: &[MemOp] = &[
    ld("i32.load", "ld32", 4, false),
    ld("i32.load8_s", "ld8s", 1, false),
    ld("i32.load8_u", "ld8u", 1, false),
    ld("i32.load16_s", "ld16s", 2, false),
    ld("i32.load16_u", "ld16u", 2, false),
    ld("i64.load", "ld64", 8, true),
    st("i32.store", "st32", 4, false),
    st("i32.store8", "st8", 1, false),
    st("i32.store16", "st16", 2, false),
    st("i64.store", "st64", 8, true),
];

/// Offsets some address makes in-bounds for every width.
const OFFSETS: &[u32] = &[
    0,
    2040,
    2044,
    2047,
    2048,
    4092,
    4095,
    4096,
    0x0010_000C,
    MEM - 64,
    MEM - 8,
];
/// Offsets NO address makes in-bounds (offset + size > memory): run under
/// `software` only, where every access must trap.
const OOB_OFFSETS: &[u32] = &[MEM, 0xFFFF_FFF0];

fn fname(op: &MemOp, off: u32) -> String {
    format!("{}_{off:x}", op.tag)
}

/// One module per access op (and one for the constant-address shapes):
/// kiln converts a module with a memory afresh on every reference run, at a
/// cost that grows with the module, so one 133-function module made each case
/// several times dearer than thirteen small ones.
fn mem_module(ops: &[MemOp], consts: bool) -> (Vec<u8>, Vec<String>) {
    let mut w = format!("(module (memory {PAGES})\n");
    // Deterministic, non-zero bytes in every window the loads read.
    for (start, len) in [(0u32, 8192u32), (0x0010_0000, 256), (MEM - 256, 256)] {
        let _ = write!(w, "  (data (i32.const {start}) \"");
        for i in start..start + len {
            let b = (i.wrapping_mul(0x9E37_79B1) >> 13) as u8 ^ (i as u8);
            let _ = write!(w, "\\{b:02x}");
        }
        w.push_str("\")\n");
    }
    let mut names = Vec::new();
    for op in ops {
        for &off in OFFSETS.iter().chain(OOB_OFFSETS) {
            let name = fname(op, off);
            let body = match (op.store, op.i64) {
                (false, false) => format!(
                    "(param i32) (result i32) local.get 0 {} offset={off}",
                    op.wat
                ),
                (false, true) => format!(
                    "(param i32) (result i64) local.get 0 {} offset={off}",
                    op.wat
                ),
                (true, false) => format!(
                    "(param i32 i32) local.get 0 local.get 1 {} offset={off}",
                    op.wat
                ),
                // RV32 declines a function that READS an i64 parameter, so
                // the value is built from two i32 halves.
                (true, true) => format!(
                    "(param i32 i32 i32) local.get 0 local.get 1 i64.extend_i32_u \
                     i64.const 32 i64.shl local.get 2 i64.extend_i32_u i64.or {} offset={off}",
                    op.wat
                ),
            };
            let _ = writeln!(w, "  (func (export \"{name}\") {body})");
            names.push(name);
        }
    }
    // The issue's shape: a CONSTANT address, the offset folded into the
    // access (`i32.const 0; i32.load offset=1048588`).
    for (name, body, _) in CONST_ADDR.iter().filter(|_| consts) {
        let _ = writeln!(w, "  (func (export \"{name}\") {body})");
        names.push(name.to_string());
    }
    w.push(')');
    (wat::parse_str(&w).unwrap(), names)
}

/// Constant-address functions: (export, body, argument).
const CONST_ADDR: &[(&str, &str, Option<u32>)] = &[
    (
        "cst_ld32",
        "(result i32) i32.const 0 i32.load offset=1048588",
        None,
    ),
    (
        "cst_st8",
        "(param i32) i32.const 4 local.get 0 i32.store8 offset=1048588",
        Some(0x5A),
    ),
    (
        "cst_ld64",
        "(result i64) i32.const 8 i64.load offset=4092",
        None,
    ),
];

/// In-bounds addresses for `op` at `off`, naturally aligned effective
/// addresses, up to the last access that ends at the memory's last byte.
fn in_bounds_addrs(op: &MemOp, off: u32) -> Vec<u32> {
    let s = op.size;
    let a0 = (s - off % s) % s;
    let last = MEM - off - s;
    let mut v = Vec::new();
    for a in [a0, a0 + s, a0 + 64, last] {
        if u64::from(a) + u64::from(off) + u64::from(s) <= u64::from(MEM) && !v.contains(&a) {
            v.push(a);
        }
    }
    v
}

/// Out-of-bounds addresses (wasm traps on each).
fn oob_addrs(op: &MemOp, off: u32) -> Vec<u32> {
    let s = op.size;
    // `addr + off` wraps 2^32 to a small, in-bounds-looking address.
    let wrap = if off >= 8 {
        0u32.wrapping_sub(off).wrapping_add(4)
    } else {
        0xFFFF_FFFC
    };
    let mut v = vec![MEM, 0x8000_0000, wrap];
    if u64::from(off) + u64::from(s) <= u64::from(MEM) {
        v.insert(0, MEM - off - s + 1);
    } else {
        v.insert(0, 0);
    }
    v
}

fn mem_args(op: &MemOp, addr: u32, k: u32) -> Vec<WasmValue> {
    let v = 0xA5C3_E187u32.wrapping_mul(k.wrapping_add(1)) ^ addr;
    match (op.store, op.i64) {
        (false, _) => vec![WasmValue::I32(addr)],
        (true, false) => vec![WasmValue::I32(addr), WasmValue::I32(v)],
        (true, true) => vec![
            WasmValue::I32(addr),
            WasmValue::I32(v.rotate_left(7)),
            WasmValue::I32(v),
        ],
    }
}

#[test]
fn rv32_memarg_offsets_past_imm12_1254() {
    let cfg = EmuConfig::new(Cpu::Rv32Imac);
    let imports = Imports::new();
    let mut groups: Vec<(Vec<MemOp>, bool)> = OPS.iter().map(|op| (vec![*op], false)).collect();
    groups.push((Vec::new(), true));
    let modules: Vec<_> = groups
        .iter()
        .map(|(ops, consts)| {
            let (wasm, names) = mem_module(ops, *consts);
            let env = env_for(&wasm, &imports).unwrap();
            assert_eq!(env.memory.as_ref().map(Vec::len), Some(MEM as usize));
            (ops.clone(), *consts, wasm, names, env)
        })
        .collect();
    let n_funcs: usize = modules.iter().map(|m| m.3.len()).sum();
    let mut summary = String::new();
    let mut total = 0usize;
    for bounds in ["none", "software", "mask"] {
        let (mut values, mut traps) = (0usize, 0usize);
        for (ops, consts, wasm, names, env) in &modules {
            let run = compile_rv32(wasm, bounds);
            let obj = assert_complete(&run, names, bounds);
            for op in ops {
                for &off in OFFSETS.iter().chain(OOB_OFFSETS) {
                    let f = fname(op, off);
                    let mut cases: Vec<(u32, bool)> = Vec::new();
                    if OFFSETS.contains(&off) {
                        cases.extend(in_bounds_addrs(op, off).into_iter().map(|a| (a, false)));
                    }
                    // Out of bounds is wasm's trap only under `software`; `none`
                    // leaves it outside the envelope and `mask` wraps it.
                    if bounds == "software" {
                        cases.extend(oob_addrs(op, off).into_iter().map(|a| (a, true)));
                    }
                    for (k, (addr, oob)) in cases.into_iter().enumerate() {
                        let args = mem_args(op, addr, k as u32);
                        let c = run_case_env(wasm, &obj, &f, &args, FUEL, &imports, &cfg, env)
                            .unwrap_or_else(|e| panic!("{bounds}: {f}{args:?}: {e:?}"));
                        assert!(
                            c.verdict.is_agree(),
                            "{bounds}: {f}{args:?}: {:?}\n kiln {:?}\n synth {:?}",
                            c.verdict,
                            c.reference,
                            c.emulator
                        );
                        match (&c.reference, &c.emulator, oob) {
                            (RefOutcome::Values(_), EmuOutcome::Values(_), false) => values += 1,
                            (RefOutcome::Trap { .. }, EmuOutcome::Trap { .. }, true) => traps += 1,
                            other => panic!("{bounds}: {f}{args:?}: unexpected {other:?}"),
                        }
                    }
                }
            }
            for (f, _, arg) in CONST_ADDR.iter().filter(|_| *consts) {
                let args: Vec<WasmValue> = arg.iter().map(|a| WasmValue::I32(*a)).collect();
                let c = run_case_env(wasm, &obj, f, &args, FUEL, &imports, &cfg, env)
                    .unwrap_or_else(|e| panic!("{bounds}: {f}: {e:?}"));
                assert!(
                    c.verdict.is_agree() && matches!(c.reference, RefOutcome::Values(_)),
                    "{bounds}: {f}: {:?}\n kiln {:?}\n synth {:?}",
                    c.verdict,
                    c.reference,
                    c.emulator
                );
                values += 1;
            }
        }
        let _ = writeln!(
            summary,
            "ORACLE rv32-reach-1254 {bounds}: {n_funcs} functions, {values} in-bounds agree, {traps} trap/trap"
        );
        total += values + traps;
    }
    print!("{summary}");
    println!("ORACLE rv32-reach-1254: {total} cases agree across 3 bounds modes");
    // 10 ops x 11 offsets, in-bounds addresses per (op, offset) as
    // `in_bounds_addrs` derives them (414), in each of the 3 modes; plus
    // under `software` 4 out-of-bounds addresses x 10 ops x 13 offsets; plus
    // the 3 constant-address functions in each mode.
    let inb: usize = OPS
        .iter()
        .flat_map(|op| OFFSETS.iter().map(move |&o| in_bounds_addrs(op, o).len()))
        .sum();
    assert_eq!(inb, 414);
    assert_eq!(
        total,
        3 * (inb + CONST_ADDR.len()) + 4 * OPS.len() * (OFFSETS.len() + OOB_OFFSETS.len())
    );
    assert_eq!(total, 1771);
}

// ─── #1724 ────────────────────────────────────────────────────────────────

const S32: &str = "local.get 0 i32.const 0x1234 i32.xor";
const S64: &str = "local.get 0 i64.extend_i32_u i64.const 32 i64.shl \
                   local.get 0 i32.const 0x55 i32.xor i64.extend_i32_u i64.or";

/// The value kept across the call, the call, and the use, writing the
/// function's result local.
fn survivor_body(kind: &str) -> String {
    match kind {
        "i32" => format!("{S32} local.get 0 call $rd i32.add local.set 1"),
        "i64" => format!("{S64} local.get 0 call $rd i64.extend_i32_u i64.add local.set 2"),
        // Two values beneath a two-argument call.
        "two" => format!(
            "{S32} local.get 0 i32.const 7 i32.add \
             local.get 0 local.get 0 i32.const 1 i32.shl call $mix i32.add i32.sub local.set 1"
        ),
        _ => unreachable!(),
    }
}

fn framed(frame: &str, body: &str) -> String {
    let b1 = "local.get 0 i32.const 1 i32.and";
    let b2 = "local.get 0 i32.const 2 i32.and";
    match frame {
        "top" => body.to_string(),
        "block" => format!("block {b1} br_if 0 {body} end"),
        "block2" => format!("block block {b1} br_if 1 {b2} br_if 0 {body} end end"),
        "if" => format!("{b1} if {body} end"),
        "ifelse" => format!("{b1} if nop else {body} end"),
        "if2" => format!("{b1} if {b2} if {body} end end"),
        // Two iterations, so the call runs twice.
        "loop" => format!(
            "i32.const 2 local.set 3 loop {body} \
             local.get 3 i32.const 1 i32.sub local.tee 3 br_if 0 end"
        ),
        "loop2" => format!(
            "i32.const 2 local.set 3 block loop {body} {b2} br_if 1 \
             local.get 3 i32.const 1 i32.sub local.tee 3 br_if 0 end end"
        ),
        _ => unreachable!(),
    }
}

const FRAMES: &[&str] = &[
    "top", "block", "block2", "if", "ifelse", "if2", "loop", "loop2",
];
const KINDS: &[&str] = &["i32", "i64", "two"];

fn call_module() -> (Vec<u8>, Vec<String>) {
    let mut w = String::from(
        "(module\n  (import \"m\" \"rd\" (func $rd (param i32) (result i32)))\n  \
         (import \"m\" \"wr\" (func $wr (param i32 i32)))\n  \
         (import \"m\" \"mix\" (func $mix (param i32 i32) (result i32)))\n",
    );
    // The issue's module, verbatim but for a name.
    w.push_str(
        "  (func (export \"issue\") (param i32)\n    block local.get 0 br_if 0 \
         i32.const 64 i32.const 64 call $rd call $wr end)\n",
    );
    let mut names = vec!["issue".to_string()];
    for frame in FRAMES {
        for kind in KINDS {
            let name = format!("{frame}_{kind}");
            let (res, out) = if *kind == "i64" {
                ("i64", "local.get 2")
            } else {
                ("i32", "local.get 1")
            };
            let _ = writeln!(
                w,
                "  (func (export \"{name}\") (param i32) (result {res}) (local i32 i64 i32)\n    \
                 i32.const 99 local.set 1 i64.const 0x99 local.set 2\n    {}\n    {out})",
                framed(frame, &survivor_body(kind))
            );
            names.push(name);
        }
    }
    w.push(')');
    (wat::parse_str(&w).unwrap(), names)
}

fn call_imports() -> Imports {
    let i32_of = |v: &WasmValue| match v {
        WasmValue::I32(x) => *x,
        other => panic!("not i32: {other:?}"),
    };
    Imports::new()
        .func("m", "rd", move |a| {
            Ok(vec![WasmValue::I32(
                i32_of(&a[0]).wrapping_mul(3).wrapping_add(0x101),
            )])
        })
        .func("m", "mix", move |a| {
            Ok(vec![WasmValue::I32(
                i32_of(&a[0]).rotate_left(5) ^ i32_of(&a[1]).wrapping_add(0x77),
            )])
        })
        .trace("m", "wr", vec![])
}

const CALL_VECTORS: &[u32] = &[
    0,
    1,
    2,
    3,
    0x7FFF_FFFF,
    0x8000_0000,
    0xFFFF_FFFF,
    0xDEAD_BEEF,
];

#[test]
fn rv32_call_in_frame_with_survivors_1724() {
    let (wasm, names) = call_module();
    let cfg = EmuConfig::new(Cpu::Rv32Imac);
    let imports = call_imports();
    let env = env_for(&wasm, &imports).unwrap();
    let run = compile_rv32(&wasm, "none");
    let obj = assert_complete(&run, &names, "calls");
    let mut agree = 0usize;
    let mut host_calls = 0usize;
    for f in &names {
        for &x in CALL_VECTORS {
            let args = [WasmValue::I32(x)];
            let c = run_case_env(&wasm, &obj, f, &args, FUEL, &imports, &cfg, &env)
                .unwrap_or_else(|e| panic!("{f}({x:#x}): {e:?}"));
            assert!(
                c.verdict.is_agree(),
                "{f}({x:#x}): {:?}\n kiln {:?}\n synth {:?}",
                c.verdict,
                c.reference,
                c.emulator
            );
            assert!(matches!(c.reference, RefOutcome::Values(_)), "{f}: {c:?}");
            host_calls += c.host_calls.len();
            agree += 1;
        }
    }
    // The issue's own observation: `wr` receives (64, rd(64)).
    let c = run_case_env(
        &wasm,
        &obj,
        "issue",
        &[WasmValue::I32(0)],
        FUEL,
        &imports,
        &cfg,
        &env,
    )
    .unwrap();
    let wr: Vec<_> = c.host_calls.iter().filter(|h| h.field == "wr").collect();
    assert_eq!(wr.len(), 1);
    assert_eq!(
        wr[0].args,
        vec![WasmValue::I32(64), WasmValue::I32(64 * 3 + 0x101)]
    );
    println!(
        "ORACLE rv32-reach-1724: {agree} cases agree over {} functions, {host_calls} host calls matched",
        names.len()
    );
    assert_eq!(names.len(), 1 + FRAMES.len() * KINDS.len());
    assert_eq!(agree, names.len() * CALL_VECTORS.len());
    // Measured: the calls the taken paths make (a vector with bit 0 or 1 set
    // skips the framed call), identical on both engines by the trace check.
    assert_eq!(host_calls, 158);
}

/// The 19 extra #1724 shapes from the cold review of 150d33b1 (its
/// `probe.rs`), where the call sits in a frame and the pending value lies
/// BELOW that frame, or is carried in other ways the shapes above do not
/// reach: a value beneath an `if (result ...)` holding the call (i32, i64);
/// an outer value live across a loop that calls on every iteration; a
/// frame's `br_if` result register live at the call; nested frames and a
/// call feeding an `if` condition; a DEFINED callee with high register
/// pressure that itself calls out; six pending values; an i64 `div_u` and an
/// in-frame call in one function (the shared #1717 slot area); i32 and i64
/// frame locals live across the call; a void call; a call in the `else`
/// arm. The base declines 17 of the 19.
fn review_shapes() -> Vec<(&'static str, &'static str, String)> {
    const C1: &str = "local.get 0 i32.const 1 i32.and";
    let s6: String = (1..=6)
        .map(|k| format!("local.get 0 i32.const {k} i32.shl "))
        .collect();
    let adds6: String = (0..6).map(|_| "i32.add ").collect();
    vec![
        (
            "under_ifres",
            "i32",
            format!("{S32} {C1} if (result i32) local.get 0 call $rd else i32.const 5 end i32.add"),
        ),
        (
            "under_ifres_i64",
            "i64",
            format!(
                "{S64} {C1} if (result i32) local.get 0 call $rd else i32.const 5 end i64.extend_i32_u i64.add"
            ),
        ),
        (
            "under_loop",
            "i32",
            format!(
                "{S32} i32.const 3 local.set 1 loop local.get 0 call $rd drop local.get 1 i32.const 1 i32.sub local.tee 1 br_if 0 end i32.const 9 i32.add"
            ),
        ),
        (
            "under_loop_i64",
            "i64",
            format!(
                "{S64} i32.const 3 local.set 1 loop local.get 0 local.get 1 i32.add call $rd local.set 3 local.get 1 i32.const 1 i32.sub local.tee 1 br_if 0 end local.get 3 i64.extend_i32_u i64.add"
            ),
        ),
        (
            "brres",
            "i32",
            format!("block (result i32) {S32} {C1} br_if 0 drop local.get 0 call $rd end"),
        ),
        (
            "brres_nested",
            "i32",
            format!(
                "block (result i32) {S32} {C1} br_if 0 drop block local.get 0 call $rd drop end i32.const 7 end"
            ),
        ),
        (
            "brres_value_under",
            "i32",
            format!(
                "local.get 0 block (result i32) {S32} {C1} br_if 0 drop local.get 0 call $rd end i32.add"
            ),
        ),
        (
            "nested_args",
            "i32",
            format!(
                "{S32} local.get 0 call $rd {C1} if (result i32) local.get 0 call $rd call $rd else i32.const 1 end call $mix i32.add"
            ),
        ),
        (
            "heavy_local",
            "i32",
            format!(
                "{S32} {S32} i32.const 3 i32.shl {C1} if (result i32) local.get 0 call $heavy else i32.const 3 end i32.add i32.add"
            ),
        ),
        (
            "heavy_local_i64",
            "i64",
            format!(
                "{S64} {C1} if (result i32) local.get 0 call $heavy else i32.const 3 end i64.extend_i32_u i64.add"
            ),
        ),
        (
            "many6",
            "i32",
            format!("{s6} {C1} if (result i32) local.get 0 call $rd else i32.const 0 end {adds6}"),
        ),
        (
            "with_div",
            "i32",
            format!(
                "{S32} {C1} if (result i32) local.get 0 call $rd else i32.const 1 end {S64} i64.const 3 i64.div_u i32.wrap_i64 i32.add i32.add"
            ),
        ),
        (
            "div_then_call_in_if",
            "i32",
            format!(
                "{S32} {S64} {C1} if (result i64) local.get 0 call $rd i64.extend_i32_u else i64.const 1 end i64.div_u i32.wrap_i64 i32.add"
            ),
        ),
        (
            "locals_survive",
            "i32",
            format!(
                "local.get 0 i32.const 77 i32.mul local.set 1 local.get 0 i64.extend_i32_s i64.const 1000 i64.mul local.set 2 {S32} {C1} if (result i32) local.get 0 call $rd local.set 3 local.get 3 else i32.const 2 end local.get 1 i32.add local.get 2 i32.wrap_i64 i32.add local.get 2 i64.const 32 i64.shr_u i32.wrap_i64 i32.add i32.add"
            ),
        ),
        (
            "void_under",
            "i32",
            format!("{S32} {C1} if local.get 0 local.get 0 call $rd call $wr end"),
        ),
        (
            "promoted_alias",
            "i32",
            format!(
                "local.get 0 local.set 1 local.get 1 {C1} if local.get 0 call $rd local.set 1 end local.get 1 i32.add"
            ),
        ),
        (
            "call_in_else_arm",
            "i32",
            format!("{S32} {C1} if (result i32) i32.const 4 else local.get 0 call $rd end i32.add"),
        ),
        (
            "deep_nest",
            "i32",
            format!(
                "i32.const 5 local.set 1 {S32} block {S32} block {S32} {C1} br_if 1 local.get 0 call $rd i32.add local.set 1 end local.get 1 i32.add local.set 1 end local.get 1 i32.add"
            ),
        ),
        (
            "call_as_condition",
            "i32",
            format!(
                "{S32} block (result i32) local.get 0 call $rd i32.const 1 i32.and if (result i32) local.get 0 call $rd else i32.const 3 end end i32.add"
            ),
        ),
    ]
}

fn review_module() -> (Vec<u8>, Vec<String>) {
    let mut w = String::from(
        "(module\n  (import \"m\" \"rd\" (func $rd (param i32) (result i32)))\n  \
         (import \"m\" \"wr\" (func $wr (param i32 i32)))\n  \
         (import \"m\" \"mix\" (func $mix (param i32 i32) (result i32)))\n",
    );
    // A defined callee using many registers and itself calling out.
    let mut heavy = String::from("local.get 0 call $rd ");
    for k in 1..=9 {
        let _ = write!(
            heavy,
            "local.get 0 i32.const {k} i32.shr_u i32.const {} i32.mul ",
            2 * k + 1
        );
    }
    heavy.push_str(&"i32.xor ".repeat(9));
    let _ = writeln!(w, "  (func $heavy (param i32) (result i32) {heavy})");
    let mut names = Vec::new();
    for (name, res, body) in review_shapes() {
        let _ = writeln!(
            w,
            "  (func (export \"{name}\") (param i32) (result {res}) (local i32 i64 i32)\n    {body})"
        );
        names.push(name.to_string());
    }
    w.push(')');
    (wat::parse_str(&w).unwrap(), names)
}

const REVIEW_VECTORS: &[u32] = &[
    0,
    1,
    2,
    3,
    0x7FFF_FFFF,
    0x8000_0000,
    0xFFFF_FFFF,
    0xDEAD_BEEF,
    0x1234_5679,
];

#[test]
fn rv32_call_shapes_from_review_1724() {
    let (wasm, names) = review_module();
    let cfg = EmuConfig::new(Cpu::Rv32Imac);
    let imports = call_imports();
    let env = env_for(&wasm, &imports).unwrap();
    let run = compile_rv32(&wasm, "none");
    let obj = assert_complete(&run, &names, "review shapes");
    let mut agree = 0usize;
    let mut host_calls = 0usize;
    for f in &names {
        for &x in REVIEW_VECTORS {
            let args = [WasmValue::I32(x)];
            let c = run_case_env(&wasm, &obj, f, &args, FUEL, &imports, &cfg, &env)
                .unwrap_or_else(|e| panic!("{f}({x:#x}): {e:?}"));
            assert!(
                c.verdict.is_agree() && matches!(c.reference, RefOutcome::Values(_)),
                "{f}({x:#x}): {:?}\n kiln {:?}\n synth {:?}",
                c.verdict,
                c.reference,
                c.emulator
            );
            host_calls += c.host_calls.len();
            agree += 1;
        }
    }
    println!(
        "ORACLE rv32-reach-1724-review: {agree} cases agree over {} functions, {host_calls} host calls matched",
        names.len()
    );
    assert_eq!(names.len(), 19);
    assert_eq!(agree, names.len() * REVIEW_VECTORS.len());
    // Measured: the calls the taken paths make (`$heavy` is a synth callee,
    // so its own `rd` call is counted), identical on both engines.
    assert_eq!(host_calls, 177);
}

/// POTENCY of the harness on REAL synth output: the memory comparison and
/// the call-trace comparison each catch a planted defect in an object that
/// otherwise agrees.
#[test]
fn potency_memory_and_call_trace_are_compared() {
    // Memory: a store whose emitted `sb` is redirected one byte up.
    let wasm = wat::parse_str(
        "(module (memory 1) (func (export \"s\") (param i32 i32) \
         local.get 0 local.get 1 i32.store8 offset=4096))",
    )
    .unwrap();
    let imports = Imports::new();
    let env = env_for(&wasm, &imports).unwrap();
    let cfg = EmuConfig::new(Cpu::Rv32Imac);
    let run = compile_rv32(&wasm, "none");
    let obj = assert_complete(&run, &["s".into()], "potency-mem");
    let args = [WasmValue::I32(8), WasmValue::I32(0x5A)];
    let good = run_case_env(&wasm, &obj, "s", &args, FUEL, &imports, &cfg, &env).unwrap();
    assert!(good.verdict.is_agree(), "{good:?}");
    let mut bad = obj.clone();
    let sb = (0..bad.text.len())
        .step_by(4)
        .find(|&i| {
            let w = u32::from_le_bytes(bad.text[i..i + 4].try_into().unwrap());
            w & 0x707F == 0x0023 // sb
        })
        .expect("an sb");
    let w = u32::from_le_bytes(bad.text[sb..sb + 4].try_into().unwrap());
    let imm = ((w >> 25) << 5) | ((w >> 7) & 0x1F);
    let imm = imm + 1;
    let w = (w & !(0x7F << 25) & !(0x1F << 7)) | ((imm >> 5) << 25) | ((imm & 0x1F) << 7);
    bad.text[sb..sb + 4].copy_from_slice(&w.to_le_bytes());
    let c = run_case_env(&wasm, &bad, "s", &args, FUEL, &imports, &cfg, &env).unwrap();
    assert!(
        format!("{:?}", c.verdict).contains("memory differs"),
        "a misplaced store passed: {:?}",
        c.verdict
    );

    // Calls: the planted host disagrees with kiln's only in what `rd` returns.
    let (cw, names) = call_module();
    let cimports = call_imports();
    let run = compile_rv32(&cw, "none");
    let cobj = assert_complete(&run, &names, "potency-calls");
    let mut env = env_for(&cw, &cimports).unwrap();
    for (n, _, f) in env.imports.iter_mut() {
        if n == "wr" {
            *f = std::sync::Arc::new(|_: &[WasmValue]| Ok(vec![]));
        }
        if n == "rd" {
            *f = std::sync::Arc::new(|a: &[WasmValue]| match a[0] {
                WasmValue::I32(x) => {
                    Ok(vec![WasmValue::I32(x.wrapping_mul(3).wrapping_add(0x102))])
                }
                _ => Err("type".into()),
            });
        }
    }
    let c = run_case_env(
        &cw,
        &cobj,
        "issue",
        &[WasmValue::I32(0)],
        FUEL,
        &cimports,
        &cfg,
        &env,
    )
    .unwrap();
    assert!(
        format!("{:?}", c.verdict).contains("host calls"),
        "a different host trace passed: {:?}",
        c.verdict
    );
}
