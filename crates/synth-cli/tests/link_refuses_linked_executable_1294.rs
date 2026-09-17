//! RQ-68-CLAIMSDRIFT (#1294) — `--link` on an already-linked image.
//!
//! `--link` links a RELOCATABLE object. The self-contained outputs are already
//! a linked ELF `ET_EXEC`, which a linker refuses as input, so `--cortex-m
//! --link` failed every time with a raw toolchain error while the README listed
//! `--link` as Implemented. Measured before the fix: `--relocatable --link`
//! produced firmware; `--cortex-m --link` and `--all-exports --link` failed.
//!
//! The refusal is decided from the artifact's own ELF header and happens BEFORE
//! any toolchain lookup, so this test needs no ARM cross toolchain and runs in
//! CI. It is red against the pre-fix binary, which reports either "Linker
//! failed" or "arm-none-eabi-gcc not found" depending on the machine — neither
//! names #1294.

use std::path::Path;
use std::process::Command;

fn fixture() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/repro/i64_high_reg_zero_fill_916.wat")
}

fn run(name: &str, flags: &[&str]) -> (bool, String) {
    let dir = std::env::temp_dir().join(format!("synth-link-1294-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let out = Command::new(env!("CARGO_BIN_EXE_synth"))
        .arg("compile")
        .arg(fixture())
        .arg("-o")
        // One output per test: the two tests run in parallel threads of one
        // process, and a shared path let one compile truncate the ELF the
        // other was reading the header of.
        .arg(dir.join(format!("{name}.elf")))
        .args(flags)
        .output()
        .expect("run synth");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stderr).into_owned() + &String::from_utf8_lossy(&out.stdout),
    )
}

#[test]
fn link_on_a_self_contained_cortex_m_image_is_refused_with_a_diagnostic_1294() {
    let (ok, text) = run("cortex_m", &["--cortex-m", "--link"]);
    assert!(
        !ok,
        "--cortex-m --link must fail: the image is already linked"
    );
    assert!(
        text.contains("#1294") && text.contains("already a LINKED executable"),
        "#1294: expected the explicit refusal, got: {text}"
    );
    assert!(
        !text.contains("Linker failed"),
        "#1294: the linker must not be invoked on an ET_EXEC: {text}"
    );
}

#[test]
fn link_on_an_all_exports_image_is_refused_too_1294() {
    let (ok, text) = run(
        "all_exports",
        &["--target", "cortex-m4", "--all-exports", "--link"],
    );
    assert!(!ok);
    assert!(text.contains("#1294"), "#1294: {text}");
}

/// Negative control: the refusal is decided from the ELF header, so the one
/// combination `--link` supports must never reach it. Whether the link then
/// succeeds depends on a cross toolchain being installed, so only the absence
/// of the #1294 refusal is asserted.
#[test]
fn link_on_a_relocatable_object_is_not_refused_1294() {
    let (_ok, text) = run("relocatable", &["--relocatable", "--link"]);
    assert!(
        !text.contains("already a LINKED executable"),
        "#1294: a relocatable object (ET_REL) must reach the linker: {text}"
    );
}
