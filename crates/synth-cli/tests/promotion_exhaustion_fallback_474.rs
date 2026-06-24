//! #474 regression guard — local promotion must never CAUSE a compile failure.
//!
//! v0.14.0 made i32 local promotion default-on. Promotion pins eligible locals
//! into callee-saved r4-r8, which halves the operand-stack temp pool. On a dense
//! function that tips register allocation past what it can recover, turning a
//! working compile into a hard "register exhaustion" skip — a regression from
//! v0.12.0 (observed on a real engine-control function; reproduced generically by
//! `scripts/repro/promotion_exhaustion_fallback.wat`).
//!
//! The fix (arm_backend.rs `select_direct`): run the promotion-on recovery ladder
//! first — so every function that compiles today is bit-identical (the frozen byte
//! gate proves it) — and, only if it still ends in register exhaustion, fall back
//! to the promotion-off ladder automatically (exactly what `SYNTH_NO_LOCAL_PROMOTE=1`
//! does by hand). Promotion is an optimization; it must never be the *reason* a
//! function fails to compile.
//!
//! This test is the executable proof the fallback is load-bearing AND lands on the
//! frame-slot path: the fixture compiles with promotion default-on, and its `.text`
//! is byte-identical to the `SYNTH_NO_LOCAL_PROMOTE=1` build.

use std::process::Command;

use object::{Object, ObjectSection};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/promotion_exhaustion_fallback.wat")
}

/// Compile the fixture (cortex-m4, relocatable) with promotion either default-on
/// or forced off, and return the `.text` bytes. Panics if the compile fails — a
/// FAILED promotion-on compile is exactly the #474 regression this guards.
fn text_bytes(promotion_off: bool) -> Vec<u8> {
    let elf = format!(
        "/tmp/pef_474_{}.elf",
        if promotion_off { "off" } else { "on" }
    );
    let mut cmd = Command::new(synth());
    if promotion_off {
        cmd.env("SYNTH_NO_LOCAL_PROMOTE", "1");
    } else {
        cmd.env_remove("SYNTH_NO_LOCAL_PROMOTE");
    }
    let out = cmd
        .args([
            "compile",
            fixture().to_str().unwrap(),
            "-o",
            &elf,
            "--target",
            "cortex-m4",
            "--relocatable",
            "--all-exports",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "#474 REGRESSION: promotion-{} compile FAILED — promotion turned a \
         compilable function into a skipped one. stderr:\n{}",
        if promotion_off { "off" } else { "on" },
        String::from_utf8_lossy(&out.stderr)
    );
    let bytes = std::fs::read(&elf).expect("read elf");
    let obj = object::File::parse(&*bytes).expect("parse elf");
    obj.section_by_name(".text")
        .expect(".text section")
        .data()
        .expect("read .text")
        .to_vec()
}

/// The dense fixture compiles with promotion DEFAULT-ON (the v0.14.0 setting that
/// regressed it), and the rescued `.text` is byte-identical to the promotion-off
/// build — proving the fallback fired and used the frame-slot lowering.
#[test]
fn promotion_never_causes_compile_failure_474() {
    let on = text_bytes(false);
    let off = text_bytes(true);
    assert_eq!(
        on, off,
        "#474: promotion-on .text should equal the promotion-off (frame-slot) \
         lowering for an exhausting function — the fallback must land on that path"
    );
}
