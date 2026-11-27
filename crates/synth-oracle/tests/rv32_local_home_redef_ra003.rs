//! VCR-RA-003 (RV32) refused correct functions that redefine a frame-resident
//! wasm local before reading it; this runs the functions it now accepts
//! against kiln (unicorn RV32, linear memory compared byte for byte, host
//! calls compared as a trace — `synth_oracle::run_case_env`).
//!
//! The RV32 validator's spill-slot rule policed EVERY `sp` offset, including
//! a wasm local's permanent frame home, which the selector writes at every
//! `local.set`/`local.tee` (and the #457/#990 entry zero-init). The fix
//! exempts the homes (and checks them for overlap instead); it changes no
//! emitted byte, so what this oracle adds is that the bytes the validator
//! used to refuse are RIGHT:
//!
//! - `redefine`: `local.set 1; local.set 1; local.get 1`;
//! - `zero_init_then_tee`: the entry zero-init of a local followed, in the
//!   same straight-line segment, by its `local.tee` and `local.get`;
//! - `redefine_call`: the same with a call, so the param has a frame home too;
//! - `redefine_loop`: two writes per iteration, read back each time;
//! - `display_fmt`: `core::fmt::num::<impl Display for i32>::fmt`, function
//!   218 of a Rust `wasm32-wasip1` hello world (opt-level s), where this was
//!   found. Verbatim but for `__stack_pointer`, which the RV32 harness does
//!   not link (`global.get` -> `i32.const 4096`, `global.set` -> `drop`), and
//!   `Formatter::pad_integral`, served by a host function so its six
//!   arguments are compared as a trace. The variant is refused on 56ccaa34
//!   exactly as the original (`SpillSlotAliased { slot: 8, .. }`).
//!   `display` stores its argument and calls it, as Rust would.
//!
//! RED on 56ccaa34: every function above but `display` is missing from the
//! object, which fails the presence check before anything runs.
//! POTENCY: the same comparison rejects the objects with the SECOND write of
//! the local moved off its home, so the reload reads the first value — the
//! stale-reload the validator was guarding against.
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary.

#![cfg(feature = "exec")]

use std::fmt::Write as _;
use std::path::PathBuf;

use synth_oracle::compare::RefOutcome;
use synth_oracle::emulate::{Cpu, EmuConfig};
use synth_oracle::reference::Imports;
use synth_oracle::synth::{CompiledObject, compile};
use synth_oracle::value::WasmValue;
use synth_oracle::{env_for, run_case_env};

const FUEL: u64 = 1_000_000;

/// func 218 of the hello world, `__stack_pointer` replaced (see the doc).
const DISPLAY_FMT_BODY: &str = r#"
    (local i32 i32 i32 i32 i32 i32 i32)
    i32.const 4096
    i32.const 16
    i32.sub
    local.tee 2
    drop
    i32.const 10
    local.set 3
    block ;; label = @1
      local.get 0
      i32.load
      local.tee 4
      local.get 4
      i32.const 31
      i32.shr_s
      local.tee 0
      i32.xor
      local.get 0
      i32.sub
      local.tee 5
      i32.const 1000
      i32.lt_u
      br_if 0 (;@1;)
      i32.const 10
      local.set 3
      loop ;; label = @2
        local.get 2
        i32.const 6
        i32.add
        local.get 3
        i32.add
        local.tee 6
        i32.const -4
        i32.add
        local.get 5
        local.tee 0
        local.get 0
        i32.const 10000
        i32.div_u
        local.tee 5
        i32.const 10000
        i32.mul
        i32.sub
        local.tee 7
        i32.const 65535
        i32.and
        i32.const 100
        i32.div_u
        local.tee 8
        i32.const 1
        i32.shl
        i32.load16_u offset=1056622 align=1
        i32.store16 align=1
        local.get 6
        i32.const -2
        i32.add
        local.get 7
        local.get 8
        i32.const 100
        i32.mul
        i32.sub
        i32.const 65535
        i32.and
        i32.const 1
        i32.shl
        i32.load16_u offset=1056622 align=1
        i32.store16 align=1
        local.get 3
        i32.const -4
        i32.add
        local.set 3
        local.get 0
        i32.const 9999999
        i32.gt_u
        br_if 0 (;@2;)
      end
    end
    block ;; label = @1
      block ;; label = @2
        local.get 5
        i32.const 9
        i32.gt_u
        br_if 0 (;@2;)
        local.get 5
        local.set 0
        br 1 (;@1;)
      end
      local.get 2
      i32.const 6
      i32.add
      local.get 3
      i32.const -2
      i32.add
      local.tee 3
      i32.add
      local.get 5
      local.get 5
      i32.const 65535
      i32.and
      i32.const 100
      i32.div_u
      local.tee 0
      i32.const 100
      i32.mul
      i32.sub
      i32.const 65535
      i32.and
      i32.const 1
      i32.shl
      i32.load16_u offset=1056622 align=1
      i32.store16 align=1
    end
    block ;; label = @1
      block ;; label = @2
        local.get 4
        i32.eqz
        br_if 0 (;@2;)
        local.get 0
        i32.eqz
        br_if 1 (;@1;)
      end
      local.get 2
      i32.const 6
      i32.add
      local.get 3
      i32.const -1
      i32.add
      local.tee 3
      i32.add
      local.get 0
      i32.const 1
      i32.shl
      i32.load8_u offset=1056623
      i32.store8
    end
    local.get 1
    local.get 4
    i32.const -1
    i32.xor
    i32.const 31
    i32.shr_u
    i32.const 1
    i32.const 0
    local.get 2
    i32.const 6
    i32.add
    local.get 3
    i32.add
    i32.const 10
    local.get 3
    i32.sub
    call $pad
    local.set 3
    local.get 2
    i32.const 16
    i32.add
    drop
    local.get 3
"#;

const SMALL: &[&str] = &[
    "redefine",
    "zero_init_then_tee",
    "redefine_call",
    "redefine_loop",
];

fn module() -> Vec<u8> {
    let mut w = String::from(
        "(module\n  (import \"m\" \"pad\" (func $pad (param i32 i32 i32 i32 i32 i32) (result i32)))\n  \
         (import \"m\" \"g\" (func $g (param i32) (result i32)))\n  (memory 17)\n",
    );
    // The two-digit table `pad_integral`'s caller indexes, where the hello
    // world's rodata has it.
    w.push_str("  (data (i32.const 1056622) \"");
    for i in 0..100 {
        let _ = write!(w, "{i:02}");
    }
    w.push_str("\")\n");
    // Values `display_fmt` is pointed at directly.
    w.push_str("  (data (i32.const 256) \"");
    for v in DIRECT {
        for b in v.to_le_bytes() {
            let _ = write!(w, "\\{b:02x}");
        }
    }
    w.push_str("\")\n");
    w.push_str(
        "  (func (export \"redefine\") (param i32) (result i32) (local i32)\n    \
         local.get 0 local.set 1\n    \
         local.get 0 i32.const 1 i32.add local.set 1\n    \
         local.get 1)\n  \
         (func (export \"zero_init_then_tee\") (param i32) (result i32) (local i32)\n    \
         block local.get 0 local.tee 1 local.get 1 i32.xor br_if 0 end\n    \
         local.get 1)\n  \
         (func (export \"redefine_call\") (param i32) (result i32) (local i32)\n    \
         local.get 0 local.set 1\n    \
         local.get 0 i32.const 3 i32.mul local.set 1\n    \
         local.get 1 call $g local.get 1 i32.add)\n  \
         (func (export \"redefine_loop\") (param i32) (result i32) (local i32 i32)\n    \
         i32.const 4 local.set 2\n    \
         loop\n      \
         local.get 0 local.set 1\n      \
         local.get 1 i32.const 7 i32.mul local.get 2 i32.add local.set 1\n      \
         local.get 1 local.set 0\n      \
         local.get 2 i32.const 1 i32.sub local.tee 2 br_if 0\n    \
         end\n    \
         local.get 0)\n",
    );
    let _ = writeln!(
        w,
        "  (func $fmt (export \"display_fmt\") (param i32 i32) (result i32){DISPLAY_FMT_BODY}  )"
    );
    w.push_str(
        "  (func (export \"display\") (param i32) (result i32)\n    \
         i32.const 64 local.get 0 i32.store\n    \
         i32.const 64 i32.const 128 call $fmt)\n)",
    );
    wat::parse_str(&w).unwrap()
}

const DIRECT: &[u32] = &[0, 7, 1000, 0xFFFF_FC18, 0x7FFF_FFFF, 0x8000_0000];

const VECTORS: &[u32] = &[
    0,
    1,
    9,
    10,
    99,
    100,
    999,
    1000,
    9999,
    10000,
    12_345_678,
    99_999_999,
    100_000_000,
    0x7FFF_FFFF,
    0x8000_0000,
    0xFFFF_FFFF,
    0xFFFF_FC18, // -1000
    0xDEAD_BEEF,
];

fn imports() -> Imports {
    let w = |v: &WasmValue| match v {
        WasmValue::I32(x) => *x,
        other => panic!("not i32: {other:?}"),
    };
    Imports::new()
        .func("m", "pad", move |a| {
            let mut h = 0x9E37_79B9u32;
            for (k, v) in a.iter().enumerate() {
                h = (h ^ w(v))
                    .rotate_left(5 + k as u32)
                    .wrapping_mul(0x0100_0193);
            }
            Ok(vec![WasmValue::I32(h)])
        })
        .func("m", "g", move |a| {
            Ok(vec![WasmValue::I32(w(&a[0]).wrapping_mul(5) ^ 0x5A5A)])
        })
}

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-ra003home-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn compile_rv32(wasm: &[u8]) -> CompiledObject {
    let dir = scratch();
    let input = dir.join("m.wasm");
    std::fs::write(&input, wasm).unwrap();
    let run = compile(
        &input,
        &[
            "-b",
            "riscv",
            "--relocatable",
            "--all-exports",
            "--allow-skipped-exports",
        ],
        &dir.join("m.o"),
    )
    .expect("synth runs");
    assert!(run.status.success(), "{}", run.stderr);
    let obj = run.object.clone().expect("object");
    let missing: Vec<&str> = SMALL
        .iter()
        .copied()
        .chain(["display_fmt", "display"])
        .filter(|f| obj.func(f).is_none())
        .collect();
    assert!(
        missing.is_empty(),
        "DECLINED: {missing:?}\n{}",
        run.stderr
            .lines()
            .filter(|l| l.contains("skipping"))
            .collect::<Vec<_>>()
            .join("\n")
    );
    obj
}

/// Every case: (function, arguments).
fn cases() -> Vec<(&'static str, Vec<WasmValue>)> {
    let mut c = Vec::new();
    for f in SMALL.iter().copied().chain(["display"]) {
        for &x in VECTORS {
            c.push((f, vec![WasmValue::I32(x)]));
        }
    }
    for k in 0..DIRECT.len() as u32 {
        c.push((
            "display_fmt",
            vec![WasmValue::I32(256 + 4 * k), WasmValue::I32(512)],
        ));
    }
    c
}

#[test]
fn rv32_local_home_redefinition_matches_kiln_ra003() {
    let wasm = module();
    let imports = imports();
    let env = env_for(&wasm, &imports).unwrap();
    let cfg = EmuConfig::new(Cpu::Rv32Imac);
    let obj = compile_rv32(&wasm);
    let mut agree = 0usize;
    let mut host_calls = 0usize;
    for (f, args) in cases() {
        let c = run_case_env(&wasm, &obj, f, &args, FUEL, &imports, &cfg, &env)
            .unwrap_or_else(|e| panic!("{f}({args:?}): {e:?}"));
        assert!(
            c.verdict.is_agree(),
            "{f}({args:?}): {:?}\n kiln {:?}\n synth {:?}",
            c.verdict,
            c.reference,
            c.emulator
        );
        assert!(matches!(c.reference, RefOutcome::Values(_)), "{f}: {c:?}");
        host_calls += c.host_calls.len();
        agree += 1;
    }
    println!(
        "ORACLE rv32-local-home-ra003: {agree} cases agree over {} functions, {host_calls} host calls matched",
        SMALL.len() + 2
    );
    assert_eq!(agree, (SMALL.len() + 1) * VECTORS.len() + DIRECT.len());
    // One `g` per `redefine_call`, one `pad` per `display`/`display_fmt`.
    assert_eq!(host_calls, 2 * VECTORS.len() + DIRECT.len());
}

/// `sw` with base `sp`: (rs2, imm).
fn sp_store(w: u32) -> Option<(u32, i32)> {
    if w & 0x707F != 0x2023 || (w >> 15) & 0x1F != 2 {
        return None;
    }
    let imm = (((w >> 25) << 5) | ((w >> 7) & 0x1F)) as i32;
    Some(((w >> 20) & 0x1F, (imm << 20) >> 20))
}

/// `obj` with the `nth` (0-based) `sw _, slot(sp)` of `func` moved to `to`.
fn move_store(obj: &CompiledObject, func: &str, slot: i32, nth: usize, to: i32) -> CompiledObject {
    let f = obj.func(func).expect("func").clone();
    let mut bad = obj.clone();
    let at = (f.offset as usize..(f.offset + f.size) as usize)
        .step_by(4)
        .filter(|&i| {
            let w = u32::from_le_bytes(bad.text[i..i + 4].try_into().unwrap());
            sp_store(w).is_some_and(|(_, imm)| imm == slot)
        })
        .nth(nth)
        .unwrap_or_else(|| panic!("{func}: no store #{nth} to {slot}(sp)"));
    let w = u32::from_le_bytes(bad.text[at..at + 4].try_into().unwrap());
    let imm = to as u32 & 0xFFF;
    let w = (w & !(0x7F << 25) & !(0x1F << 7)) | ((imm >> 5) << 25) | ((imm & 0x1F) << 7);
    bad.text[at..at + 4].copy_from_slice(&w.to_le_bytes());
    bad
}

/// POTENCY on the real objects: the second write of the local (the store the
/// validator called "overwriting") is moved to an unused frame word, so the
/// reload reads the FIRST value — the stale reload the rule exists for. The
/// comparison must reject it, or agreeing above proved nothing.
#[test]
fn potency_a_stale_reload_of_the_home_disagrees_ra003() {
    let wasm = module();
    let imports = imports();
    let env = env_for(&wasm, &imports).unwrap();
    let cfg = EmuConfig::new(Cpu::Rv32Imac);
    let obj = compile_rv32(&wasm);
    // Local 1 is the only frame local of both: home 0. Offset 12 is inside
    // the 16-byte frame and unused by either (no saved register, no ra).
    for f in ["redefine", "zero_init_then_tee"] {
        let bad = move_store(&obj, f, 0, 1, 12);
        let mut caught = 0;
        for &x in VECTORS {
            let args = [WasmValue::I32(x)];
            let good = run_case_env(&wasm, &obj, f, &args, FUEL, &imports, &cfg, &env).unwrap();
            assert!(good.verdict.is_agree(), "{f}({x:#x}) good: {good:?}");
            let c = run_case_env(&wasm, &bad, f, &args, FUEL, &imports, &cfg, &env).unwrap();
            if !c.verdict.is_agree() {
                caught += 1;
            }
        }
        // `redefine` returns x where x+1 is right: every vector differs.
        // `zero_init_then_tee` returns 0 where x is right: all but x = 0.
        let want = if f == "redefine" {
            VECTORS.len()
        } else {
            VECTORS.len() - 1
        };
        assert_eq!(caught, want, "{f}: the stale reload passed the oracle");
    }
}
