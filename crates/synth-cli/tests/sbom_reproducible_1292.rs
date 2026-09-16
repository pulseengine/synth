//! RQ-68-REPRO (#1292, #1293) — driven through the SHIPPED binary.
//!
//! relay built drone software to wasm and through synth twice and got two
//! different files. Measured before this test existed: the ELF was
//! byte-identical and the `--sbom` document differed in exactly one field, a
//! wall-clock timestamp, which ignored `SOURCE_DATE_EPOCH`. And the SBOM said
//! nothing about the `SYNTH_*` levers the build ran under, although a census
//! found 14 of the 36 variables non-test source reads change emitted bytes.
//!
//! Both halves are red against the pre-#1292 binary: its SBOMs differ with
//! `SOURCE_DATE_EPOCH` set, and never name a lever.

use std::path::{Path, PathBuf};
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/repro/i64_high_reg_zero_fill_916.wat")
}

/// Compile once into `dir`, with `envs` applied on top of an environment
/// scrubbed of every ambient `SYNTH_*` variable and of `SOURCE_DATE_EPOCH`, so
/// the developer's own shell cannot make this test pass or fail.
fn build(dir: &Path, tag: &str, envs: &[(&str, &str)]) -> (Vec<u8>, String) {
    let elf = dir.join(format!("{tag}.elf"));
    let sbom = dir.join(format!("{tag}.cdx.json"));
    let mut cmd = Command::new(synth());
    for (k, _) in std::env::vars() {
        if k.starts_with("SYNTH_") || k == "SOURCE_DATE_EPOCH" {
            cmd.env_remove(k);
        }
    }
    cmd.envs(envs.iter().copied())
        .arg("compile")
        .arg(fixture())
        .arg("-o")
        .arg(&elf)
        .args(["--target", "cortex-m4", "--all-exports", "--sbom"])
        .arg(&sbom);
    let out = cmd.output().expect("run synth");
    assert!(
        out.status.success(),
        "synth compile failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    (
        std::fs::read(&elf).expect("elf"),
        std::fs::read_to_string(&sbom).expect("sbom"),
    )
}

fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("synth-repro-1292-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

#[test]
fn two_builds_under_source_date_epoch_give_identical_elf_and_sbom_1292() {
    let d = scratch("sde");
    let epoch = [("SOURCE_DATE_EPOCH", "1700000000")];
    let (elf_a, sbom_a) = build(&d, "a", &epoch);
    std::thread::sleep(std::time::Duration::from_millis(1100)); // cross a wall-clock second
    let (elf_b, sbom_b) = build(&d, "b", &epoch);
    assert_eq!(
        elf_a, elf_b,
        "codegen was not deterministic for identical input"
    );
    // The output file NAME is recorded in the SBOM; normalise it, nothing else.
    let norm = |s: &str, tag: &str| s.replace(&format!("{tag}.elf"), "OUT.elf");
    assert_eq!(
        norm(&sbom_a, "a"),
        norm(&sbom_b, "b"),
        "#1292: with SOURCE_DATE_EPOCH set, two builds of the same source must \
         produce the same SBOM"
    );
    assert!(
        sbom_a.contains("2023-11-14T22:13:20Z"),
        "timestamp not pinned: {sbom_a}"
    );
}

#[test]
fn malformed_source_date_epoch_fails_the_build_1292() {
    let d = scratch("bad");
    let out = Command::new(synth())
        .env("SOURCE_DATE_EPOCH", "yesterday")
        .arg("compile")
        .arg(fixture())
        .arg("-o")
        .arg(d.join("x.elf"))
        .args(["--target", "cortex-m4", "--all-exports", "--sbom"])
        .arg(d.join("x.cdx.json"))
        .output()
        .expect("run synth");
    assert!(
        !out.status.success(),
        "#1292: a malformed SOURCE_DATE_EPOCH must fail rather than fall back to the clock"
    );
}

#[test]
fn sbom_names_the_byte_changing_lever_the_build_ran_under_1293() {
    let d = scratch("lever");
    let epoch = ("SOURCE_DATE_EPOCH", "1700000000");
    let (elf_default, sbom_default) = build(&d, "default", &[epoch]);
    let (elf_lever, sbom_lever) = build(&d, "lever", &[epoch, ("SYNTH_RANGE_REALLOC", "0")]);
    assert!(
        sbom_lever.contains("synth:build-env:SYNTH_RANGE_REALLOC"),
        "#1293: the SBOM must name the SYNTH_* lever this build ran under: {sbom_lever}"
    );
    assert!(
        !sbom_default.contains("synth:build-env:"),
        "a build with no SYNTH_* lever set must record none"
    );
    // The lever's effect is what makes recording it matter; say so if this
    // fixture happens not to exercise it, rather than asserting a difference.
    if elf_default == elf_lever {
        eprintln!("note: SYNTH_RANGE_REALLOC=0 did not move this fixture's bytes");
    }
}
