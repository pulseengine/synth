//! #1013 — the aarch64 ELF builder must REFUSE, not PANIC, when a retained
//! function holds a relocation against a function the backend declined.
//!
//! Measured on v0.58.0 (gale's 805-module real-world corpus; the only panic —
//! the other 787 aarch64 refusals were clean). The named repro is a 4.7 KB
//! `httparse` fixture whose `func_0` carries a 95-target `br_table`:
//!
//! ```text
//! $ synth compile httparse.wasm -b aarch64 --all-exports --relocatable -o out.o
//! warning: skipping function 'func_0': ... br_table with 95 targets exceeds the
//!          aarch64 compare-chain threshold (16) ... loud-declining (VCR-A64-CF-001)
//! warning: 1 of 5 functions were skipped (not in output): func_0
//! thread 'main' panicked at crates/synth-backend-aarch64/src/elf.rs:189:17:
//! aarch64 ELF builder: relocation at .text+96 targets symbol 'func_0', which
//! this object does not place — refusing to ship an unrelocated placeholder (#851)
//! $ echo $?
//! 101
//! ```
//!
//! The DECISION is right — an unrelocated `bl #0` placeholder is the
//! silent-miscompile class and must not ship. The MECHANISM is wrong: a panic
//! is not a decline. Exit 101 + a `RUST_BACKTRACE` note tells the user "synth
//! has a bug", not "synth found a real problem and refused"; #952 established
//! that a refusal exits non-zero CLEANLY with a named error.
//!
//! # What this test asserts (and why not merely "does not crash")
//!
//! A test that only asserts the absence of a panic starts passing for the
//! wrong reasons the moment the code path moves. This test asserts the full
//! refusal contract: exit code exactly 1 (the clean-error path — NOT Rust's
//! panic code 101), no panic markers on stderr, and a machine-readable reason
//! that names the declined symbol (`func_0`) and the class (#851).
//!
//! # Sibling behaviour, measured (a finding vs. #1013's table)
//!
//! #1013 reports arm/riscv exiting 1 on the identical module. Measured on
//! main @ d149f2ec (= v0.58.0 for these paths), both actually exit 0: ARM
//! COMPILES the 95-target `br_table` outright, and RISC-V declines `func_0`
//! but emits the object with `synth_func_0` as an UNDEFINED symbol and the
//! relocations retained — loud at link time, never a silent hole
//! (`build_multi_func_riscv_elf`, #871). Full undefined-external parity for
//! aarch64 is deliberately NOT this fix — it is adjacent to the #1017 import
//! -dispatch capability push (v0.60). This fix only converts the existing
//! refusal from a panic into the #952-style clean error.
//!
//! Fixtures are generated WAT (not the loom-repo corpus file, which is not
//! vendored here); both shapes were verified against the UNFIXED v0.58.0
//! binary before this test was written: repro exits 101 with the panic,
//! control exits 0 with no panic.

use std::path::PathBuf;
use std::process::{Command, Output};

fn synth() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_synth"))
}

fn workdir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("synth-1013-{tag}"));
    std::fs::create_dir_all(&d).expect("temp dir");
    d
}

/// A function body whose `br_table` has `n` targets — above the aarch64
/// compare-chain threshold (16) it is loud-declined (VCR-A64-CF-001).
fn br_table_body(n: usize) -> String {
    let targets = (0..n)
        .map(|k| format!("$b{k}"))
        .collect::<Vec<_>>()
        .join(" ");
    let opens = (0..n)
        .rev()
        .map(|k| format!("(block $b{k}"))
        .collect::<Vec<_>>()
        .join(" ");
    let closes = (0..n)
        .map(|k| format!(") (return (i32.const {k}))"))
        .collect::<Vec<_>>()
        .join("\n    ");
    format!("{opens}\n      (br_table {targets} (local.get 0))\n    {closes}\n    (i32.const 99)")
}

/// gale's #1013 shape, minimized: `$jump` (wasm index 0, so symbol `func_0`)
/// is an internal, NON-exported helper pulled in only by #235 reachability;
/// aarch64 declines it (20-target `br_table` > threshold 16), and the
/// retained export `run` holds a `bl func_0` relocation against it.
fn dangling_reloc_wat() -> String {
    format!(
        "(module\n  (func $jump (param i32) (result i32)\n    {})\n  \
         (func (export \"run\") (param i32) (result i32)\n    \
         (call $jump (local.get 0))))\n",
        br_table_body(20)
    )
}

/// Same decline, NO dangling relocation: the `br_table` function is exported
/// (declined under `--allow-skipped-exports`, the corpus-sweep shape) and
/// nothing retained calls it, so the object must still be emitted with exit 0.
fn decline_without_reloc_wat() -> String {
    format!(
        "(module\n  (func (export \"jump\") (param i32) (result i32)\n    {})\n  \
         (func (export \"run\") (param i32) (result i32)\n    \
         (i32.add (local.get 0) (i32.const 1))))\n",
        br_table_body(20)
    )
}

fn compile(dir: &std::path::Path, wat: &str, out_name: &str, extra: &[&str]) -> Output {
    let src = dir.join("m.wat");
    std::fs::write(&src, wat).expect("write wat");
    let obj = dir.join(out_name);
    // The temp workdir persists across runs — a stale object from an earlier
    // run would make the "no partial object left behind" assertion vacuous.
    let _ = std::fs::remove_file(&obj);
    let mut c = Command::new(synth());
    c.args([
        "compile",
        src.to_str().unwrap(),
        "-b",
        "aarch64",
        "--all-exports",
        "--relocatable",
        "-o",
        obj.to_str().unwrap(),
    ]);
    c.args(extra);
    c.output().expect("run synth compile")
}

fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// RED (fails on the unfixed builder with exit 101 + panic): a dangling
/// relocation against a declined function must be a CLEAN refusal — exit 1,
/// no panic, machine-readable reason naming the declined symbol.
#[test]
fn dangling_reloc_against_declined_function_refuses_cleanly() {
    let dir = workdir("refusal");
    let out = compile(&dir, &dangling_reloc_wat(), "out.o", &[]);
    let err = stderr(&out);

    // Anchor: the decline this test depends on must actually have happened —
    // otherwise the assertions below would be judging some unrelated failure.
    assert!(
        err.contains("VCR-A64-CF-001")
            && err.contains("br_table with")
            && err.contains("exceeds the aarch64 compare-chain threshold"),
        "fixture no longer trips the VCR-A64-CF-001 br_table decline — the \
         test premise is gone, revisit rather than let it pass on some other \
         error.\nstderr:\n{err}"
    );

    // The refusal must be the CLEAN error path (#952 contract): exit code
    // exactly 1 — not 101, which is Rust's panic code and the #1013 bug.
    assert_eq!(
        out.status.code(),
        Some(1),
        "expected the clean-error exit (1); 101 means the ELF builder still \
         panics (#1013), 0 means an object with a dangling relocation was \
         shipped.\nstderr:\n{err}"
    );

    // A panic is not a decline: no panic markers on stderr.
    assert!(
        !err.contains("panicked at") && !err.contains("RUST_BACKTRACE"),
        "refusal was delivered via panic, not a clean error (#1013).\nstderr:\n{err}"
    );

    // Machine-readable reason: names the declined symbol and the class.
    assert!(
        err.contains("targets symbol 'func_0'")
            && err.contains("does not place")
            && err.contains("#851"),
        "refusal reason must name the declined symbol (func_0) and the #851 \
         unrelocated-placeholder class.\nstderr:\n{err}"
    );

    // A refused compile must not leave a partial object behind.
    assert!(
        !dir.join("out.o").exists(),
        "refused compile still wrote an output object"
    );
}

/// NEGATIVE CONTROL: the same decline with NO dangling relocation stays a
/// routine skip — object emitted, exit 0. Protects against the inverse
/// failure of the fix: refusing every module that merely contains a decline.
#[test]
fn decline_without_dangling_reloc_still_exits_zero() {
    let dir = workdir("control");
    let out = compile(
        &dir,
        &decline_without_reloc_wat(),
        "ctrl.o",
        &["--allow-skipped-exports"],
    );
    let err = stderr(&out);

    // The decline must still have happened (true control, not a compile that
    // silently started supporting 20-target br_table).
    assert!(
        err.contains("VCR-A64-CF-001"),
        "control fixture no longer declines — premise gone.\nstderr:\n{err}"
    );
    assert_eq!(
        out.status.code(),
        Some(0),
        "a decline with no dangling relocation must stay a routine exit-0 \
         skip.\nstderr:\n{err}"
    );
    assert!(
        !err.contains("panicked at"),
        "control compile panicked.\nstderr:\n{err}"
    );
    assert!(
        dir.join("ctrl.o").exists(),
        "control object was not emitted"
    );
}
