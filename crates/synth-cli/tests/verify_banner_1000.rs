//! #1000 (RQ-58-SHIPVERIFY) — `synth verify` capability check runs BEFORE the
//! banner, and a verify-capable binary reports a real verdict.
//!
//! Two halves, selected by how the test binary was built (deliberately NO
//! `required-features`, so the plain workspace test run exercises the
//! missing-capability half):
//!
//! - WITHOUT `verify` (the plain `cargo test --workspace` build): `synth
//!   verify` must fail (exit != 0) WITHOUT printing any of the
//!   `Translation validation:` banner lines — in particular not
//!   `Strategy: Per-rule SMT verification (ASIL D path)`. Before #1000 the
//!   banner printed first and the capability check ran after it, so a
//!   log-scraper grepping for the ASIL-D strategy line found it in a run
//!   that verified nothing (the exit code was already correct, #124).
//!   RED-FIRST: under the pre-#1000 ordering this half fails.
//!
//! - WITH `verify` (`cargo test -p synth-cli --features verify --test
//!   verify_banner_1000`, wired into the fact-spec-oracle CI job): the
//!   banner including the strategy line must still print, and the run must
//!   end in a REAL verdict on a module synth itself just compiled — not the
//!   capability-missing error. This is the in-tree twin of
//!   `scripts/release_verify_smoke.sh`, the released-artifact gate release.yml
//!   runs against the packaged tarballs.

use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

/// Small module with an exported function whose ops are all on the verified
/// ARM path (and/add) — the same shape the release smoke script compiles.
const FIXTURE_WAT: &str = r#"(module
  (func (export "mix") (param i32 i32) (result i32)
    local.get 0
    i32.const 255
    i32.and
    local.get 1
    i32.add))
"#;

/// Compile the fixture with the binary under test; returns (wat, elf) paths.
fn compile_fixture(tag: &str) -> (std::path::PathBuf, std::path::PathBuf, std::path::PathBuf) {
    let dir = std::env::temp_dir().join(format!(
        "synth_verify_banner_1000_{}_{}",
        tag,
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let wat = dir.join("mix.wat");
    let elf = dir.join("mix.elf");
    std::fs::write(&wat, FIXTURE_WAT).expect("write fixture wat");
    let compile = Command::new(synth())
        .args([
            "compile",
            wat.to_str().unwrap(),
            "-o",
            elf.to_str().unwrap(),
            "--all-exports",
        ])
        .output()
        .expect("run synth compile");
    assert!(
        compile.status.success(),
        "fixture compile failed:\n{}\n{}",
        String::from_utf8_lossy(&compile.stdout),
        String::from_utf8_lossy(&compile.stderr)
    );
    (dir, wat, elf)
}

fn run_verify(wat: &std::path::Path, elf: &std::path::Path) -> std::process::Output {
    Command::new(synth())
        .args(["verify", wat.to_str().unwrap(), elf.to_str().unwrap()])
        .output()
        .expect("run synth verify")
}

/// The missing-capability half: fail loudly BEFORE anything
/// verification-shaped is printed.
#[cfg(not(feature = "verify"))]
#[test]
fn verify_without_feature_fails_before_banner() {
    let (dir, wat, elf) = compile_fixture("nofeat");
    let out = run_verify(&wat, &elf);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);

    // #124 contract, unchanged: non-zero exit, loud capability error.
    assert!(
        !out.status.success(),
        "`synth verify` must fail on a build without the `verify` feature\nstdout:\n{stdout}"
    );
    assert!(
        stderr.contains("built without the `verify` feature"),
        "capability error must name the missing feature\nstderr:\n{stderr}"
    );

    // #1000 contract, new: the check runs BEFORE the banner, so none of the
    // four `Translation validation:` lines — above all the ASIL-D strategy
    // line — may appear in a run that verified nothing.
    assert!(
        !stdout.contains("Strategy: Per-rule SMT verification"),
        "ASIL-D strategy line printed by a binary that cannot verify:\n{stdout}"
    );
    assert!(
        !stdout.contains("Translation validation:"),
        "verification banner printed by a binary that cannot verify:\n{stdout}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// The capable half: banner still prints, and the run ends in a real verdict.
#[cfg(feature = "verify")]
#[test]
fn verify_with_feature_reports_real_verdict() {
    let (dir, wat, elf) = compile_fixture("feat");
    let out = run_verify(&wat, &elf);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);

    assert!(
        out.status.success(),
        "`synth verify` must succeed on a verify-capable build\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    // The #1000 reorder must NOT cost the capable binary its banner.
    assert!(
        stdout.contains("Strategy: Per-rule SMT verification (ASIL D path)"),
        "strategy banner missing on a verify-capable build:\n{stdout}"
    );
    // A real verdict, not the capability-missing error.
    assert!(
        stdout.contains("All functions verified successfully."),
        "expected a real verification verdict:\n{stdout}"
    );
    assert!(
        !stderr.contains("built without the `verify` feature"),
        "capability error on a build that HAS the feature:\n{stderr}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
