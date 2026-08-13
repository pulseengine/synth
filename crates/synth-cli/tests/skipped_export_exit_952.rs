//! #952 — a declined REQUESTED export must exit non-zero, not 0.
//!
//! Measured on v0.56.0:
//!
//! ```wat
//! (module
//!   (func $g (param i32 i64) (result i32) (local.get 0))
//!   (func (export "f") (result i32) (call $g (i32.const 7) (i64.const 9))))
//! ```
//!
//! ```text
//! $ synth compile ctrl.wat -b arm -t cortex-m3 --all-exports --relocatable -o ctrl.o
//! warning: skipping function 'f': ... #929: call arg 1 is 64-bit ... Declining
//!          rather than emitting a silent miscompile
//! warning: 1 of 2 functions were skipped (not in output): f
//! $ echo $?
//! 0
//! $ llvm-objdump -t ctrl.o | grep 'F .text'
//! 00000000 l     F .text 00000004 func_0        # only the callee — 'f' is gone
//! ```
//!
//! `f` is the module's sole export. The compile that declined it exited 0, so
//! any build gating on `$?` — which is every build — ships the object missing
//! its one public entry point.
//!
//! # Why this test reads synth's own stdout/stderr, not `synth disasm`
//!
//! `proven_safe_imported_memory_932.rs` already hit this: the first version of
//! that test counted mnemonics in `synth disasm` output and passed on macOS
//! while returning ZERO on the ubuntu runner, because disassembly TEXT is
//! host-dependent (register-name spelling, mnemonic width suffixes, and so
//! on). This test reads the exit code (`ExitStatus`, not text) and synth's own
//! diagnostic text on stderr — both identical on every host — never
//! disassembly.
//!
//! # The asymmetry this test protects
//!
//! Declining a non-exported internal helper (pulled in only for #235
//! reachability) is routine and must keep exiting 0 — that is the
//! NEGATIVE CONTROL below. Only a decline of a function the module actually
//! `(export ...)`s must flip the exit code. Getting this backwards (failing
//! the build on every skip) would break the `--all-exports` corpus-sweep
//! callers this repo already has (`wast_conformance_928_differential.py` and
//! others) that intentionally compile many modules expecting some functions
//! to decline — hence `--allow-skipped-exports`, tested last.

use std::path::PathBuf;
use std::process::{Command, Output};

fn synth() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_synth"))
}

fn workdir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("synth-952-{tag}"));
    std::fs::create_dir_all(&d).expect("temp dir");
    d
}

fn compile(dir: &std::path::Path, wat: &str, out_name: &str, extra: &[&str]) -> Output {
    let src = dir.join("m.wat");
    std::fs::write(&src, wat).expect("write wat");
    let obj = dir.join(out_name);
    let mut c = Command::new(synth());
    c.args([
        "compile",
        src.to_str().unwrap(),
        "-b",
        "arm",
        "-t",
        "cortex-m3",
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

/// gale's exact repro (via #929): `f` is the module's SOLE export, and it is
/// the function that gets declined (the callee's i64 param forces the i64
/// register-pair marshalling #929 refuses on the CALLER, `f`).
const REQUESTED_EXPORT_DECLINED: &str = r#"(module
  (func $g (param i32 i64) (result i32) (local.get 0))
  (func (export "f") (result i32) (call $g (i32.const 7) (i64.const 9))))
"#;

/// `f` is exported and compiles fine; `$hard` is an internal, NON-exported
/// helper pulled in only because `f` calls it (#235 reachability). `$hard`'s
/// f64 result makes IT decline on a soft-float target — but nothing asked for
/// `$hard` by name, so its absence is routine, not a build failure.
///
/// Verified empirically before writing this test (against the unmodified
/// v0.56.1 binary) that this fixture actually PRODUCES a skip of a
/// non-exported function: `$hard` unreachable-but-uncalled produces no skip
/// at all (it is simply never compiled), so the helper MUST be called from
/// the export for `reachable_from_exports` to pull it in and then decline it.
const ONLY_HELPER_DECLINED: &str = r#"(module
  (func $hard (result f64) (f64.sqrt (f64.const 2.0)))
  (func $helper (result i32) (call $hard) (drop) (i32.const 1))
  (func (export "f") (result i32) (call $helper)))
"#;

/// RED (must pass only after the fix): a compile that declines a REQUESTED
/// export exits non-zero. Before the #952 fix this test fails — the process
/// exits 0 with the export silently absent from the object.
#[test]
fn declined_requested_export_exits_nonzero() {
    let dir = workdir("red");
    let out = compile(&dir, REQUESTED_EXPORT_DECLINED, "ctrl.o", &[]);

    // Anchor: the skip must actually have happened, not just an unrelated
    // failure. If this assertion stops matching (e.g. #929's message text
    // changes upstream), the test below is meaningless and must be revisited
    // rather than silently passing on some other error.
    let err = stderr(&out);
    assert!(
        err.contains("skipping function 'f'"),
        "fixture must decline 'f' specifically (the anchor this test relies \
         on) — got:\n{err}"
    );

    assert!(
        !out.status.success(),
        "#952: a compile that declines a REQUESTED export ('f', the module's \
         sole export) must exit non-zero — a build gating on `$?` must not \
         accept an object silently missing its public entry point. \
         stderr:\n{err}"
    );
}

/// NEGATIVE CONTROL, both before and after the fix: skipping only a
/// non-exported internal helper must still exit 0. This is the asymmetry
/// #952 explicitly preserves — routine helper skips are not build failures.
/// If this test ever starts failing, the fix over-broadened the gate to fail
/// the build on ANY skip, not just a skipped export.
#[test]
fn skipped_nonexported_helper_still_exits_zero() {
    let dir = workdir("negctrl");
    let out = compile(&dir, ONLY_HELPER_DECLINED, "ctrl.o", &[]);
    let err = stderr(&out);

    // Non-vacuity: a control that never exercises a skip proves nothing (the
    // #275/A32 lesson — see call_indirect_275_selfcontained.rs). Anchor on
    // BOTH the per-function warning naming the skipped helper AND the
    // aggregate count, so a future refactor that stops skipping `$hard`
    // (e.g. broadens f64 support) fails this test loudly rather than leaving
    // it passing for the wrong reason.
    assert!(
        err.contains("skipping function") && err.contains("were skipped"),
        "fixture must actually skip the non-exported helper for this control \
         to mean anything — got:\n{err}"
    );
    assert!(
        !err.contains("skipping function 'f'"),
        "the EXPORT 'f' must not be the one skipped — this fixture is meant \
         to isolate a helper-only skip. stderr:\n{err}"
    );

    assert!(
        out.status.success(),
        "#952 negative control: skipping only a non-exported internal helper \
         (never asked for by name) must still exit 0 — only a declined \
         REQUESTED export may fail the build. stderr:\n{err}"
    );
}

/// `--allow-skipped-exports` restores the pre-#952 exit-0 behavior for
/// callers who genuinely want the partial object (the `--all-exports`
/// corpus-sweep shape).
#[test]
fn allow_skipped_exports_restores_exit_zero() {
    let dir = workdir("allow");
    let out = compile(
        &dir,
        REQUESTED_EXPORT_DECLINED,
        "ctrl.o",
        &["--allow-skipped-exports"],
    );
    let err = stderr(&out);
    assert!(
        err.contains("skipping function 'f'"),
        "the decline must still happen (and still warn) under the opt-out — \
         only the EXIT CODE changes. stderr:\n{err}"
    );
    assert!(
        out.status.success(),
        "--allow-skipped-exports must restore exit 0 on a declined requested \
         export. stderr:\n{err}"
    );
}
