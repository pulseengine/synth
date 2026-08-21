//! RQ-58-FLAKE (#977) — the compile-then-parse guard the integration tests owe.
//!
//! Every byte-gate in `crates/synth-cli/tests/` has the same shape: run
//! `synth compile -o <path>`, then read `<path>` back and parse it as an ELF.
//! Two things go wrong with that shape, and only one of them is loud.
//!
//! **Loud.** The read lands on something that is not an ELF and `object`
//! reports `Could not read file magic` (#960, #974, #977). It looks like an
//! assertion failure in a file the PR never touched, so it reads as noise.
//!
//! **Silent, and the reason this module exists.** The read lands on a
//! *previous run's* ELF. `synth compile` opens the output with
//! `File::create` — truncate-then-write — so a failed or half-finished
//! compile leaves either nothing, a zero-length file, or the bytes that were
//! already there. Parse those and the gate passes on evidence it did not
//! produce. v0.56 lived through exactly this with the opposite sign: a
//! compile failed, `-o` wrote nothing, the previous run's `.o` was still on
//! disk, and executing it looked like a fresh miscompile.
//!
//! So the contract here is: **nothing parses an artifact until the artifact is
//! proven to be this invocation's output.** In order —
//!
//! 1. the output path is removed before the compile runs,
//! 2. the compile's exit status is asserted, carrying synth's own stderr,
//! 3. the file is asserted to exist,
//! 4. the file is asserted non-empty,
//!
//! and only then are the bytes handed back. A bad compile reports as a bad
//! compile, at the compile, with the compiler's message — not as a parse error
//! twenty lines later, and never as a pass.
//!
//! Freshness is additionally guaranteed *by construction*: [`unique_artifact`]
//! hands out a path that is unique per call (pid + a process-wide counter), so
//! no two compiles — in different libtest threads of one binary, or in two
//! binaries/CI runs sharing one `/tmp` — can ever name the same file. That is
//! the collision that produced #977: `shift_mask_elide_686.rs` derived its
//! output name from `(fixture, relocatable, flag)` only, and its two `#[test]`
//! fns walk the *same* corpus with the *same* flag values on parallel libtest
//! threads, so both wrote and read one path. Under concurrency this
//! reproduced `Could not read file magic` in 10 of 48 runs.
//!
//! Deliberately NOT checked: mtime. Filesystem timestamp granularity is coarse
//! enough that an mtime freshness test would become its own flake source.
//! Remove-first plus a unique path is stronger and has no clock in it.
//!
//! The guards are observed firing by the `artifact_guard_*` tests in
//! `shift_mask_elide_686.rs` — a guard nobody watched fire is not a guard.

#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

/// Process-wide, so two calls in two libtest threads cannot collide.
static SEQ: AtomicU64 = AtomicU64::new(0);

/// A path no other call — in this process or any other — will produce.
///
/// `tag` is a human-readable hint (test/fixture name); it only has to be
/// filesystem-safe, uniqueness comes from the pid and the counter.
pub fn unique_artifact(tag: &str, ext: &str) -> PathBuf {
    let safe: String = tag
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    let n = SEQ.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join("synth-test-artifacts");
    // Best-effort: a pre-existing dir is fine, and a failure here surfaces as
    // the "was not created" guard below rather than as a silent stale read.
    let _ = std::fs::create_dir_all(&dir);
    dir.join(format!("{safe}-{}-{n}.{ext}", std::process::id()))
}

/// Prove `path` is a readable, non-empty file and return its bytes.
///
/// Split out from [`compile_artifact`] so the empty/missing guards can be
/// exercised directly, without having to persuade a compiler to emit a
/// zero-byte object.
pub fn read_artifact(path: &Path) -> Result<Vec<u8>, String> {
    let meta = std::fs::metadata(path).map_err(|e| {
        format!(
            "output artifact {} was NOT created by this invocation ({e}) — \
             refusing to parse anything else that may be at that path",
            path.display()
        )
    })?;
    if meta.len() == 0 {
        return Err(format!(
            "output artifact {} is EMPTY (0 bytes) — the compile produced no \
             object; refusing to parse it",
            path.display()
        ));
    }
    std::fs::read(path).map_err(|e| format!("could not read {}: {e}", path.display()))
}

/// Run a `synth compile` (or any producer) that writes to `out`, and return the
/// artifact's bytes only if this invocation actually produced them.
///
/// `cmd` must already carry `-o <out>`. The path is removed first, so a stale
/// artifact from an earlier run can never be mistaken for this one's output.
pub fn compile_artifact(cmd: &mut Command, out: &Path) -> Result<Vec<u8>, String> {
    compile_artifact_with_output(cmd, out).map(|(bytes, _)| bytes)
}

/// [`compile_artifact`], additionally handing back the process
/// [`std::process::Output`] for gates that assert on the compiler's own
/// stderr (e.g. `SYNTH_SPILL_REPORT` stats). Same guard, same order — this is
/// the one implementation; [`compile_artifact`] delegates here.
pub fn compile_artifact_with_output(
    cmd: &mut Command,
    out: &Path,
) -> Result<(Vec<u8>, std::process::Output), String> {
    // (0) Freshness: whatever is there now is not ours.
    let _ = std::fs::remove_file(out);

    // (1) The compile must succeed, and its own stderr is the diagnostic.
    let output = cmd
        .output()
        .map_err(|e| format!("could not spawn {:?}: {e}", cmd.get_program()))?;
    if !output.status.success() {
        return Err(format!(
            "synth compile FAILED ({}) — refusing to parse {}\n--- stderr ---\n{}\n--- stdout ---\n{}",
            output.status,
            out.display(),
            String::from_utf8_lossy(&output.stderr).trim(),
            String::from_utf8_lossy(&output.stdout).trim(),
        ));
    }

    // (2)+(3) It must exist and be non-empty before anything parses it.
    read_artifact(out).map(|bytes| (bytes, output))
}

/// [`compile_artifact`], panicking with `ctx` prefixed — the ergonomic form for
/// a byte gate whose only sane response to a failed compile is to stop. Leaves
/// the artifact in place for callers that need the path afterwards.
pub fn compile_artifact_or_panic(cmd: &mut Command, out: &Path, ctx: &str) -> Vec<u8> {
    match compile_artifact(cmd, out) {
        Ok(bytes) => bytes,
        Err(e) => panic!("{ctx}: {e}"),
    }
}

/// [`compile_artifact_or_panic`] for gates that only want the bytes: the
/// artifact is deleted once read. Per-call unique paths mean nothing is ever
/// reused, so without this the temp dir would grow by one file per compile on a
/// long-lived (self-hosted) runner.
pub fn compile_bytes_or_panic(cmd: &mut Command, out: &Path, ctx: &str) -> Vec<u8> {
    let bytes = compile_artifact_or_panic(cmd, out, ctx);
    let _ = std::fs::remove_file(out);
    bytes
}
