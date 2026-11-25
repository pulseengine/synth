//! RQ-91-RV32ISA (Refs #1744): the SHIPPED CLI honours the RV32 profile.
//!
//! The backend's profile check and `RiscVElfBuilder::with_profile` are
//! unit-tested in `synth-backend-riscv`, but the `synth` binary builds RV32
//! objects through its OWN two ELF paths (`build_riscv_elf`,
//! `build_multi_func_riscv_elf` in `main.rs`), and cold review 12 (F1) showed
//! dropping both `.with_profile(...)` calls left every required test green.
//! This file is in the required Test job and pins, on the binary:
//!
//!   * `e_flags` 0 under `rv32i` and `rv32im`, `0x1` (RVC) under `rv32imc`,
//!     `esp32c3` and `rv32imac`, on every compile shape that reaches either
//!     CLI path (module `--all-exports`, single function `-n`, with and
//!     without `--relocatable`);
//!   * the refusal: `rv32i` exits non-zero on `i32.mul`, naming #1744;
//!   * `synth riscv-runtime` (F2) accepts the same profile names `compile`
//!     does and prints the profile's own `-march` — `rv32imc` for the
//!     ESP32-C3, never `rv32imac` (the C3 has no A extension).

#![cfg(feature = "riscv")]

use std::path::{Path, PathBuf};
use std::process::Command;

const ADD: &str = r#"(module
  (func (export "f") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (func (export "g") (param i32) (result i32) local.get 0 i32.const 1 i32.sub))
"#;
const MUL: &str = r#"(module
  (func (export "f") (param i32 i32) (result i32) local.get 0 local.get 1 i32.mul))
"#;

fn workdir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("synth-1744-{}-{tag}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn synth() -> Command {
    Command::new(env!("CARGO_BIN_EXE_synth"))
}

fn compile(dir: &Path, wat: &str, target: &str, flags: &[&str]) -> (bool, String, Option<u32>) {
    let input = dir.join("m.wat");
    std::fs::write(&input, wat).unwrap();
    let out = dir.join(format!("m-{target}.o"));
    let _ = std::fs::remove_file(&out);
    let o = synth()
        .arg("compile")
        .arg(&input)
        .args(["-b", "riscv", "--target", target])
        .args(flags)
        .arg("-o")
        .arg(&out)
        .output()
        .unwrap();
    let flags = std::fs::read(&out).ok().map(|b| {
        assert_eq!(&b[..4], b"\x7fELF");
        assert_eq!(u16::from_le_bytes([b[18], b[19]]), 0xF3, "EM_RISCV");
        u32::from_le_bytes([b[36], b[37], b[38], b[39]])
    });
    (
        o.status.success(),
        String::from_utf8_lossy(&o.stderr).into_owned(),
        flags,
    )
}

const SHAPES: &[&[&str]] = &[
    &["--all-exports", "--relocatable"],
    &["--all-exports"],
    &["-n", "f", "--relocatable"],
    &["-n", "f"],
];

#[test]
fn e_flags_follow_the_profile_on_every_cli_path() {
    let dir = workdir("eflags");
    for (target, want) in [
        ("rv32i", 0u32),
        ("rv32im", 0),
        ("rv32imc", 1),
        ("esp32c3", 1),
        ("rv32imac", 1),
    ] {
        for shape in SHAPES {
            let (ok, err, flags) = compile(&dir, ADD, target, shape);
            assert!(ok, "{target} {shape:?}: {err}");
            assert_eq!(flags, Some(want), "{target} {shape:?}: e_flags");
        }
    }
}

#[test]
fn rv32i_refuses_mul_and_rv32im_accepts_it() {
    let dir = workdir("mul");
    for shape in SHAPES {
        let (ok, err, flags) = compile(&dir, MUL, "rv32i", shape);
        assert!(!ok && flags.is_none(), "rv32i {shape:?} accepted i32.mul");
        assert!(
            err.contains("has no `m` extension") && err.contains("#1744"),
            "rv32i {shape:?}: {err}"
        );
        let (ok, err, flags) = compile(&dir, MUL, "rv32im", shape);
        assert!(ok, "rv32im {shape:?}: {err}");
        assert_eq!(flags, Some(0));
    }
}

fn runtime(target: &str) -> (bool, String, String) {
    let dir = workdir(&format!("rt-{target}"));
    let o = synth()
        .args(["riscv-runtime", "--target", target, "-o"])
        .arg(&dir)
        .output()
        .unwrap();
    let startup = std::fs::read_to_string(dir.join("startup.c")).unwrap_or_default();
    (
        o.status.success(),
        String::from_utf8_lossy(&o.stdout).into_owned() + &String::from_utf8_lossy(&o.stderr),
        startup,
    )
}

#[test]
fn riscv_runtime_takes_compile_profile_names_and_prints_their_march() {
    for (target, march, summary) in [
        ("rv32i", "rv32i", "RV32I"),
        ("rv32im", "rv32im", "RV32IM"),
        ("rv32imc", "rv32imc", "RV32IMC"),
        ("esp32c3", "rv32imc", "RV32IMC"),
        ("rv32imac", "rv32imac", "RV32IMAC"),
        ("riscv32", "rv32imac", "RV32IMAC"),
        ("rv32gc", "rv32gc", "RV32GC"),
    ] {
        let (ok, out, startup) = runtime(target);
        assert!(ok, "{target}: {out}");
        assert!(
            out.contains(&format!("-march={march} ")),
            "{target}: expected -march={march}:\n{out}"
        );
        assert!(
            startup.contains(&format!("Target: {summary} (")),
            "{target}: startup.c does not name {summary}"
        );
    }
    let (ok, out, _) = runtime("bogus-rv");
    assert!(!ok, "bogus target accepted: {out}");
}
