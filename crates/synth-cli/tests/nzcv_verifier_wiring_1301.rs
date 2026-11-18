//! RQ-91-M0FLAGS (#1301): the NZCV-liveness verifier is WIRED into the ARM
//! emit path, by default, on ARMv7-M — and its opt-out is loud.
//!
//! The verifier never rejects anything synth emits today (that is the point:
//! the bytes are byte-identical to before it existed), so a plain compile
//! cannot show that it runs. The debug-build self-test lever
//! `SYNTH_NZCV_SELFTEST_PLANT` re-labels every `Cmp` op as flag-PRESERVING
//! without changing a byte; a compare whose flags reach a branch is then a
//! violation the verifier MUST report. If the call site in `arm_backend.rs`
//! is unplugged (or gated off by default), the planted compile succeeds and
//! this test is red. The opt-out `SYNTH_NO_NZCV_VERIFY` must turn the planted
//! compile green again AND say so on stderr, and the plant must never move an
//! emitted byte.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const WAT: &str = r#"(module
  (func (export "f") (param i32 i32) (result i32)
    (block
      (br_if 0 (i32.lt_s (local.get 0) (local.get 1)))
      (return (i32.const 7)))
    (i32.const 9)))
"#;

/// A per-test scratch directory (tests run in parallel and each removes its
/// own directory when done).
fn dir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!(
        "synth_nzcv_wiring_1301_{}_{tag}",
        std::process::id()
    ));
    std::fs::create_dir_all(&d).expect("mkdir");
    d
}

fn compile(wat: &Path, out: &Path, flags: &[&str], env: &[(&str, &str)]) -> Output {
    let mut c = Command::new(env!("CARGO_BIN_EXE_synth"));
    c.args([
        "compile",
        wat.to_str().unwrap(),
        "-o",
        out.to_str().unwrap(),
    ])
    .args(flags)
    .env_remove("SYNTH_NO_NZCV_VERIFY")
    .env_remove("SYNTH_NZCV_SELFTEST_PLANT");
    for (k, v) in env {
        c.env(k, v);
    }
    c.output().expect("run synth")
}

#[test]
fn nzcv_verifier_runs_by_default_and_its_opt_out_is_loud() {
    // The plant is honoured by debug builds only (never a release binary);
    // the test binary and `synth` share the profile.
    if !cfg!(debug_assertions) {
        return;
    }
    let d = dir("wiring");
    let wat = d.join("cmp_branch.wat");
    std::fs::write(&wat, WAT).unwrap();
    for (name, flags) in [
        (
            "m4-reloc",
            &["--target", "cortex-m4", "--relocatable", "--all-exports"][..],
        ),
        ("m4-self", &["--target", "cortex-m4", "--all-exports"][..]),
    ] {
        let base = d.join(format!("{name}-base.o"));
        let planted = d.join(format!("{name}-planted.o"));
        let opted = d.join(format!("{name}-opted.o"));
        // 1. control: compiles, no notice.
        let o = compile(&wat, &base, flags, &[]);
        let err = String::from_utf8_lossy(&o.stderr);
        assert!(o.status.success(), "{name}: control failed: {err}");
        assert!(!err.contains("SYNTH_NO_NZCV_VERIFY"), "{name}: {err}");
        // 2. planted: the verifier must refuse (a compare feeds a branch).
        let o = compile(&wat, &planted, flags, &[("SYNTH_NZCV_SELFTEST_PLANT", "1")]);
        let err = String::from_utf8_lossy(&o.stderr);
        assert!(
            !o.status.success() && err.contains("NZCV live across a clobber"),
            "{name}: the planted compile was NOT refused — the NZCV verifier is not \
             wired at its call site (or not on by default). stderr: {err}"
        );
        // 3. planted + opt-out: compiles, says so, same bytes as the control.
        let o = compile(
            &wat,
            &opted,
            flags,
            &[
                ("SYNTH_NZCV_SELFTEST_PLANT", "1"),
                ("SYNTH_NO_NZCV_VERIFY", "1"),
            ],
        );
        let err = String::from_utf8_lossy(&o.stderr);
        assert!(o.status.success(), "{name}: opt-out did not disable: {err}");
        assert!(
            err.contains("SYNTH_NO_NZCV_VERIFY is set") && err.contains("DISABLED"),
            "{name}: the opt-out must be loud on stderr: {err}"
        );
        assert_eq!(
            std::fs::read(&base).unwrap(),
            std::fs::read(&opted).unwrap(),
            "{name}: the plant or the opt-out moved emitted bytes"
        );
    }
    let _ = std::fs::remove_dir_all(&d);
}

/// ARMv6-M ignores the opt-out: the check cannot be switched off there.
#[test]
fn nzcv_opt_out_does_not_apply_to_armv6m() {
    if !cfg!(debug_assertions) {
        return;
    }
    let d = dir("v6m");
    // `inc` is accepted on cortex-m0 today (armv6m_1301 fixture shape).
    let wat = d.join("inc.wat");
    std::fs::write(
        &wat,
        r#"(module (func (export "f") (param i32) (result i32) (i32.add (local.get 0) (i32.const 1))))"#,
    )
    .unwrap();
    let o = compile(
        &wat,
        &d.join("inc.o"),
        &["--target", "cortex-m0", "--relocatable", "--all-exports"],
        &[("SYNTH_NO_NZCV_VERIFY", "1")],
    );
    let err = String::from_utf8_lossy(&o.stderr);
    assert!(o.status.success(), "{err}");
    assert!(
        !err.contains("SYNTH_NO_NZCV_VERIFY is set"),
        "the opt-out must not be honoured (or announced) on ARMv6-M: {err}"
    );
    let _ = std::fs::remove_dir_all(&d);
}

/// Review 10 N2: the island segment push is pinned in Rust, not only by the
/// Python island oracles in ci.yml. Every committed island fixture compiles
/// under `--native-pointer-abi` (the only route that emits mid-stream
/// literal islands). If the island's branch-over is not recorded as a
/// segment, the instruction before it "falls into a gap", all flags look
/// live, and these compiles are refused with `NZCV live across a clobber`.
#[test]
fn nzcv_accepts_mid_stream_literal_islands() {
    let repro = concat!(env!("CARGO_MANIFEST_DIR"), "/../../scripts/repro");
    let d = dir("islands");
    for f in [
        "litpool_islands_345",
        "islandpass_1331_backspan",
        "islandpass_1331_nested",
        "islandpass_1331_spanning",
    ] {
        for target in ["cortex-m7", "cortex-m4f"] {
            let o = compile(
                Path::new(&format!("{repro}/{f}.wat")),
                &d.join(format!("{f}-{target}.o")),
                &[
                    "--target",
                    target,
                    "--relocatable",
                    "--all-exports",
                    "--native-pointer-abi",
                ],
                &[],
            );
            let err = String::from_utf8_lossy(&o.stderr);
            assert!(
                o.status.success() && !err.contains("NZCV"),
                "{f} on {target}: an island function was refused — is the island's \
                 branch-over still recorded as an NZCV segment? stderr: {err}"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&d);
}
