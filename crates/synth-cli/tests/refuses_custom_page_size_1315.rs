//! RQ-69-PAGESIZE (#1315) — a declared custom page size is refused, not ignored.
//!
//! gale reported that `(memory 1 1 (pagesize 1))` compiled with rc=0 and no
//! diagnostic, while `__synth_mem_size_0` reported 65536 for a memory the
//! module declares as one byte. That symbol is what an embedder programs one
//! MPU region from (#1145), so the region over-granted by the page-size ratio.
//!
//! Measured on v0.68.0 across four paths — self-contained, single-memory
//! relocatable, multi-memory relocatable and RV32 — all rc=0. The refusal is
//! decided at decode time, so these tests need no cross toolchain.
//!
//! RED-FIRST: with the `refuse_custom_page_size` calls removed, every
//! `refused_*` test below fails (the compile succeeds) while
//! `default_page_size_still_compiles` keeps passing — the negative control that
//! stops this from becoming "refuse memories".

use std::path::Path;
use std::process::Command;

fn fixture(name: &str) -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../scripts/repro")
        .join(name)
}

fn run(tag: &str, wat: &str, flags: &[&str]) -> (bool, String) {
    let dir = std::env::temp_dir().join(format!("synth-pagesize-1315-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let out = Command::new(env!("CARGO_BIN_EXE_synth"))
        .arg("compile")
        .arg(fixture(wat))
        .arg("-o")
        .arg(dir.join(format!("{tag}.o")))
        .args(flags)
        .output()
        .expect("synth runs");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (out.status.success(), text)
}

/// The diagnostic must name the issue AND the two numbers that make it matter:
/// what the module declares, and what synth would otherwise have reported.
fn assert_refused(tag: &str, flags: &[&str]) {
    let (ok, text) = run(tag, "custom_page_size_1315.wat", flags);
    assert!(
        !ok,
        "{tag}: custom page size compiled instead of being refused:\n{text}"
    );
    assert!(
        text.contains("#1315"),
        "{tag}: refusal does not name #1315:\n{text}"
    );
    assert!(
        text.contains("custom page size"),
        "{tag}: refusal does not say what was declared:\n{text}"
    );
    assert!(
        text.contains("65536"),
        "{tag}: refusal does not state the size synth would have reported:\n{text}"
    );
}

#[test]
fn refused_on_self_contained_image_1315() {
    assert_refused("self", &["--cortex-m"]);
}

#[test]
fn refused_on_relocatable_object_1315() {
    assert_refused(
        "reloc",
        &["--target", "cortex-m3", "--all-exports", "--relocatable"],
    );
}

#[test]
fn refused_on_rv32_1315() {
    assert_refused("rv32", &["-b", "riscv", "--all-exports"]);
}

/// The negative control. A memory with the DEFAULT page size must still
/// compile — the refusal is about an ignored declaration, not about memories.
#[test]
fn default_page_size_still_compiles_1315() {
    let (ok, text) = run("default", "i64_high_reg_zero_fill_916.wat", &["--cortex-m"]);
    assert!(ok, "default page size stopped compiling:\n{text}");
}

/// The sweep's second member (#1315): a shared memory is refused too. Zero
/// `(memory ... shared)` declarations exist in synth's own fixtures and zero
/// across the org's consumer repositories — measured before refusing, as a
/// behaviour change requires.
#[test]
fn refused_shared_memory_1315() {
    let (ok, text) = run("shared", "shared_memory_1315.wat", &["--cortex-m"]);
    assert!(
        !ok,
        "shared memory compiled instead of being refused:\n{text}"
    );
    assert!(
        text.contains("#1315"),
        "refusal does not name #1315:\n{text}"
    );
    assert!(
        text.contains("SHARED"),
        "refusal does not say what was declared:\n{text}"
    );
}
