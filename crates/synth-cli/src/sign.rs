//! Sigil/`wsc` integration: sign the ELF binaries `synth compile` emits.
//!
//! When `synth compile --sign-output` is used, after the ELF is written this
//! module invokes the external `wsc` (WebAssembly Signatures) CLI from the
//! [`pulseengine/sigil`](https://github.com/pulseengine/sigil) project to
//! attach a Sigstore keyless signature to the ELF.
//!
//! # The `wsc` contract this module assumes
//!
//! As of `wsc-cli` v0.9.x (sigil main, October 2025) the signing invocation is:
//!
//! ```text
//! wsc sign --keyless --format elf -i <input.elf> -o <signed.elf>
//! ```
//!
//! - `--keyless` — use Sigstore (Fulcio + Rekor) ephemeral keys; no long-lived
//!   private key on disk. Requires an OIDC token in the environment (set by
//!   GitHub Actions when `id-token: write` is granted).
//! - `--format elf` — the ELF signing format. Auto-detected when omitted, but
//!   we pass it explicitly so a misconfigured wsc fails loudly rather than
//!   silently treating the ELF as a WASM module.
//! - `-i` / `-o` — wsc writes a *new* file; it does not modify in place. We
//!   sign into a sibling temp file and rename atomically over the original so
//!   the user-facing contract ("the path I passed `-o` to is the signed ELF")
//!   holds.
//!
//! If `wsc`'s flags change in a future release (e.g. `--sign-elf` instead of
//! `sign --format elf`), the subprocess will fail and the user will see the
//! `wsc` error verbatim plus the "sigil interface assumption broken" hint
//! emitted by [`sign_elf`]. A silent no-op is impossible: we check the exit
//! status and the renamed file's existence.
//!
//! # What signing proves
//!
//! A keyless signature embedded in the ELF lets a downstream consumer of the
//! firmware verify, via `wsc verify --keyless`, that the ELF was produced by
//! a specific GitHub identity (via Fulcio cert) at a specific time (via the
//! Rekor transparency log) without any pre-shared key. See
//! [`docs/sigil-integration.md`](../../../docs/sigil-integration.md).

use anyhow::{Context, Result};
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The external CLI binary we shell out to. Comes from the
/// [`pulseengine/sigil`](https://github.com/pulseengine/sigil) project; the
/// `wsc-cli` crate ships both `wsc` and `sigil` bins pointing at the same
/// main. We pick `wsc` because that is the canonical PulseEngine name.
pub const WSC_BIN: &str = "wsc";

/// Build the argv `synth` will invoke on `wsc` to sign `elf` in place.
///
/// Returns `(program, args)`. `signed_tmp` is the temporary path wsc writes
/// to before the rename; on success it will be `rename`d over `elf`.
///
/// Extracted from [`sign_elf`] so a unit test can pin the exact argv shape
/// without needing `wsc` installed.
pub fn build_sign_argv(elf: &Path, signed_tmp: &Path) -> (PathBuf, Vec<PathBuf>) {
    (
        PathBuf::from(WSC_BIN),
        vec![
            PathBuf::from("sign"),
            PathBuf::from("--keyless"),
            PathBuf::from("--format"),
            PathBuf::from("elf"),
            PathBuf::from("-i"),
            elf.to_path_buf(),
            PathBuf::from("-o"),
            signed_tmp.to_path_buf(),
        ],
    )
}

/// Compute the sibling temp path wsc writes the signed ELF to before we
/// atomic-rename it over the original. Kept deterministic so a failed
/// signing leaves a discoverable `<output>.signing.tmp` next to the ELF.
pub fn signing_tmp_path(elf: &Path) -> PathBuf {
    let mut p = elf.as_os_str().to_owned();
    p.push(".signing.tmp");
    PathBuf::from(p)
}

/// Sign `elf` in place via `wsc sign --keyless --format elf`.
///
/// On success the file at `elf` has been replaced with the signed ELF (the
/// signature is embedded in a dedicated ELF section by wsc — the original
/// program headers, sections, and entry point are preserved).
///
/// On failure, this returns an `anyhow::Error` whose context includes the
/// wsc stderr and a hint that the sigil interface contract may have changed.
pub fn sign_elf(elf: &Path) -> Result<()> {
    // Sanity-check that wsc is reachable. We do not run `wsc --version` first
    // (extra latency on the happy path) — instead, when `Command::status` /
    // `Command::output` returns `ErrorKind::NotFound`, we translate it into a
    // user-friendly error.
    let tmp = signing_tmp_path(elf);
    let (program, args) = build_sign_argv(elf, &tmp);

    let output = Command::new(&program)
        .args(args.iter().map(|p| p.as_os_str()).collect::<Vec<&OsStr>>())
        .output()
        .map_err(|e| match e.kind() {
            std::io::ErrorKind::NotFound => anyhow::anyhow!(
                "`wsc` (sigil signing CLI) not found on PATH. \
                 `synth compile --sign-output` requires sigil's `wsc` binary; \
                 install it from https://github.com/pulseengine/sigil and \
                 ensure it is on PATH. Original error: {e}"
            ),
            _ => anyhow::Error::new(e).context(format!(
                "failed to invoke `{}` to sign {}",
                program.display(),
                elf.display()
            )),
        })?;

    if !output.status.success() {
        // Clean up the temp file if wsc partially wrote it.
        let _ = std::fs::remove_file(&tmp);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        anyhow::bail!(
            "wsc signing failed (exit {}). \
             If `wsc`'s CLI surface has changed (e.g. the `sign --format elf` \
             shape we depend on), update crates/synth-cli/src/sign.rs. \
             wsc stderr: {}\nwsc stdout: {}",
            output.status,
            stderr.trim(),
            stdout.trim(),
        );
    }

    // wsc reported success — the signed ELF should now live at `tmp`. If it
    // does not, the wsc contract has broken silently; refuse to claim the
    // original ELF is signed.
    if !tmp.exists() {
        anyhow::bail!(
            "wsc reported success but did not produce a signed file at {}. \
             The sigil interface contract may have changed.",
            tmp.display()
        );
    }

    std::fs::rename(&tmp, elf).with_context(|| {
        format!(
            "wsc produced signed ELF {} but renaming it over {} failed",
            tmp.display(),
            elf.display()
        )
    })?;

    println!("signed: {}", elf.display());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    #[test]
    fn argv_shape_matches_wsc_contract() {
        // Pins the wsc invocation shape this module assumes. If any of these
        // change, a downstream wsc-version bump may have broken the contract
        // — see the module-level doc-comment.
        let elf = Path::new("/tmp/example.elf");
        let tmp = signing_tmp_path(elf);
        let (program, args) = build_sign_argv(elf, &tmp);

        assert_eq!(program, PathBuf::from("wsc"));
        let arg_strs: Vec<&str> = args.iter().map(|p| p.to_str().unwrap()).collect();
        assert_eq!(
            arg_strs,
            vec![
                "sign",
                "--keyless",
                "--format",
                "elf",
                "-i",
                "/tmp/example.elf",
                "-o",
                "/tmp/example.elf.signing.tmp",
            ]
        );
    }

    #[test]
    fn signing_tmp_path_is_deterministic_sibling() {
        let elf = Path::new("/some/dir/firmware.elf");
        assert_eq!(
            signing_tmp_path(elf),
            PathBuf::from("/some/dir/firmware.elf.signing.tmp")
        );
    }

    /// If wsc is not on PATH, `sign_elf` must return a clear error that
    /// names the missing binary and points at sigil. The check is only run
    /// when wsc is genuinely absent — when a developer happens to have it
    /// installed, we skip rather than fabricate an end-to-end test.
    #[test]
    fn missing_wsc_produces_actionable_error() {
        if which_wsc().is_some() {
            eprintln!("skipping: `wsc` is on PATH in this environment");
            return;
        }
        // Use a nonexistent ELF path — we never get far enough for that to
        // matter because the Command::new("wsc").output() fails first.
        let err = sign_elf(Path::new("/tmp/nonexistent-synth-sign-test.elf"))
            .expect_err("sign_elf must fail when wsc is missing");
        let msg = format!("{:#}", err);
        assert!(
            msg.contains("wsc") && msg.contains("sigil"),
            "error should mention wsc and sigil; got: {msg}"
        );
    }

    /// Tiny helper used only by the smoke test above. Avoids depending on
    /// the `which` crate for a one-off PATH lookup.
    fn which_wsc() -> Option<PathBuf> {
        let path_var = std::env::var_os("PATH")?;
        for dir in std::env::split_paths(&path_var) {
            let candidate = dir.join(WSC_BIN);
            if candidate.is_file() {
                return Some(candidate);
            }
        }
        None
    }
}
