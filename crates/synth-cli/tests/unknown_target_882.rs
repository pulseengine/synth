//! #882 — the `--target` seam must never silently select a wrong-ISA build.
//!
//! gale's papercut: `synth compile … --target riscv32` (no `-b`) printed
//! "Using backend: arm" and produced Thumb code in a RISC-V ELF container,
//! failing only deep in the emitter ("non-CALL_PLT relocation ThmCall
//! reached the RISC-V ELF emitter"). This gate pins the CLI behavior:
//!
//! 1. an UNKNOWN `--target` exits non-zero naming the valid set;
//! 2. a KNOWN target whose ISA family mismatches the (defaulted or explicit)
//!    single-ISA backend exits non-zero pointing at the right `-b`;
//! 3. every currently-valid target/backend pairing still compiles (no
//!    behavior change for good input).

use std::path::PathBuf;
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/rv32_br_table_882.wat")
}

fn run(args: &[&str]) -> (bool, String) {
    use std::sync::atomic::{AtomicU32, Ordering};
    static N: AtomicU32 = AtomicU32::new(0);
    let out_path = std::env::temp_dir().join(format!(
        "synth_882_{}_{}.o",
        std::process::id(),
        N.fetch_add(1, Ordering::Relaxed)
    ));
    let out = Command::new(synth())
        .arg("compile")
        .arg(fixture())
        .args(args)
        .arg("-o")
        .arg(&out_path)
        .output()
        .expect("spawn synth");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (out.status.success(), text)
}

/// #882 (1): unknown --target → non-zero, message names the valid set.
#[test]
fn unknown_target_hard_errors_with_valid_set() {
    let (ok, text) = run(&["--target", "riscv32xyz"]);
    assert!(!ok, "unknown target must exit non-zero, got:\n{text}");
    assert!(
        text.contains("unknown target triple: riscv32xyz"),
        "must name the bad target:\n{text}"
    );
    for name in ["cortex-m3", "rv32imac", "esp32c3", "cortex-a53"] {
        assert!(text.contains(name), "valid set must include {name}:\n{text}");
    }
    // And it must never have reached backend selection.
    assert!(
        !text.contains("Using backend"),
        "must fail BEFORE backend selection:\n{text}"
    );
}

/// #882 (1b): unknown --target with an EXPLICIT backend additionally lists
/// that backend's accepted targets.
#[test]
fn unknown_target_with_explicit_backend_lists_its_targets() {
    let (ok, text) = run(&["--target", "riscv32xyz", "-b", "riscv"]);
    assert!(!ok, "unknown target must exit non-zero, got:\n{text}");
    assert!(
        text.contains("targets accepted by backend 'riscv'"),
        "explicit -b must list its accepted set:\n{text}"
    );
}

/// #882 (2) — gale's exact shape: `--target riscv32` with NO `-b` must
/// hard-error pointing at `-b riscv`, not print "Using backend: arm".
#[test]
fn riscv_target_with_defaulted_arm_backend_hard_errors() {
    let (ok, text) = run(&["--target", "riscv32", "--all-exports", "--relocatable"]);
    assert!(
        !ok,
        "--target riscv32 without -b riscv must exit non-zero, got:\n{text}"
    );
    assert!(text.contains("RISC-V"), "{text}");
    assert!(text.contains("-b riscv"), "must point at -b riscv:\n{text}");
    assert!(
        !text.contains("Using backend"),
        "must fail BEFORE backend selection:\n{text}"
    );
}

/// #882 (2b): explicit mismatched backend errors naming its accepted targets.
#[test]
fn explicit_backend_target_mismatch_hard_errors() {
    let (ok, text) = run(&["--target", "cortex-m3", "-b", "riscv"]);
    assert!(!ok, "cortex-m3 on -b riscv must exit non-zero, got:\n{text}");
    assert!(
        text.contains("does not accept --target cortex-m3"),
        "{text}"
    );
    assert!(text.contains("rv32imac"), "{text}");
}

/// #882 (3): good input unchanged — the matched pairings still compile.
#[test]
fn good_target_backend_pairings_still_compile() {
    for args in [
        &["--target", "cortex-m3", "--all-exports"][..],
        &["--target", "rv32imac", "-b", "riscv", "--all-exports", "--relocatable"][..],
        &["--target", "esp32c3", "-b", "riscv", "--all-exports", "--relocatable"][..],
    ] {
        let (ok, text) = run(args);
        assert!(ok, "good input {args:?} must still compile:\n{text}");
    }
}
