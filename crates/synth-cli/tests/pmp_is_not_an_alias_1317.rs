//! RQ-69-PMPLIB (#1317) — `pmp` is refused identically on every backend.
//!
//! v0.68 (#1284) made the CLI refuse `--safety-bounds pmp`, but two residuals
//! survived, both found by that release's clean-room review:
//!
//!  1. `synth-core`'s `SafetyBounds::parse` still mapped `pmp` to `Mpu`, with a
//!     unit test PINNING the alias — and `synth-core` is PUBLISHED, so a
//!     library caller got exactly the alias the CLI rejects.
//!  2. On AArch64 the refusal came from the older #865 check, whose message
//!     talks about `mpu` — one backend answering a `pmp` request by discussing
//!     a different mode.
//!
//! Refusing in the parse fixes both at once: nothing reaches a per-backend
//! check, so all three backends emit one message that names what was typed.

use std::path::Path;
use std::process::Command;

fn run(tag: &str, flags: &[&str]) -> (bool, String) {
    let dir = std::env::temp_dir().join(format!("synth-pmp-1317-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../scripts/repro/i64_high_reg_zero_fill_916.wat");
    let out = Command::new(env!("CARGO_BIN_EXE_synth"))
        .arg("compile")
        .arg(fixture)
        .arg("-o")
        .arg(dir.join(format!("{tag}.o")))
        .args(flags)
        .output()
        .expect("synth runs");
    (
        out.status.success(),
        format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        ),
    )
}

fn assert_refused_naming_pmp(tag: &str, flags: &[&str]) {
    let (ok, text) = run(tag, flags);
    assert!(!ok, "{tag}: pmp was accepted:\n{text}");
    assert!(
        text.contains("pmp"),
        "{tag}: the refusal must name what was typed:\n{text}"
    );
    assert!(
        text.contains("never a silent alias"),
        "{tag}: the refusal must say pmp is never an alias (#1284's wording):\n{text}"
    );
}

#[test]
fn pmp_refused_on_self_contained_arm_1317() {
    assert_refused_naming_pmp("arm", &["--cortex-m", "--safety-bounds", "pmp"]);
}

#[test]
fn pmp_refused_on_rv32_1317() {
    assert_refused_naming_pmp(
        "rv32",
        &["-b", "riscv", "--all-exports", "--safety-bounds", "pmp"],
    );
}

/// The residual the v0.68 review named: AArch64 refused `pmp` through the #865
/// mask/mpu check, whose message said "mpu". It must now name `pmp` like the
/// others.
#[test]
fn pmp_refused_on_aarch64_naming_pmp_not_mpu_1317() {
    assert_refused_naming_pmp(
        "a64",
        &["-b", "aarch64", "--all-exports", "--safety-bounds", "pmp"],
    );
}

/// The negative control: `mpu` itself is NOT collateral damage. It still
/// reaches its own per-backend diagnostic (refused on a self-contained image,
/// accepted only on ARM relocatable with `--embedder-mpu`, per #1284).
#[test]
fn mpu_still_reaches_its_own_diagnostic_1317() {
    let (ok, text) = run("mpu", &["--cortex-m", "--safety-bounds", "mpu"]);
    assert!(!ok, "mpu on a self-contained image must still be refused");
    assert!(
        text.contains("#1145") || text.contains("#1284"),
        "mpu must keep its OWN diagnostic, not inherit the pmp one:\n{text}"
    );
    assert!(
        !text.contains("never a silent alias"),
        "mpu must not be answered with the pmp message:\n{text}"
    );
}
