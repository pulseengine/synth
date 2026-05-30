//! Helper script for publishing the synth workspace to crates.io.
//!
//! Modes:
//!   ./publish verify   — `cargo package` every publishable crate (#146)
//!                        in dependency order, fail on first error.
//!   ./publish publish  — `cargo publish` every publishable crate in
//!                        dependency order; retries up to 10 times to
//!                        ride out crates.io index-propagation lag.
//!
//! Modelled on `pulseengine/sigil`'s scripts/publish.rs; the same
//! "try, sleep 40s, try again" loop covers the index-propagation
//! window between publishing a dep and publishing its dependent.
//!
//! Publish order is curated (not auto-derived): leaf crates first so
//! the index is up to date when the next layer publishes. Internal-only
//! crates (`publish = false` in their Cargo.toml) are not listed here
//! and are filtered out by `cargo publish -p` regardless.
//!
//! Run from the workspace root.

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::thread;
use std::time::Duration;

/// Publish order: leaves first, then their consumers, then the CLI.
/// Hand-curated to match the dependency graph documented in
/// `docs/release-process.md`. Internal-only crates (publish = false)
/// are intentionally absent.
const CRATES_TO_PUBLISH: &[&str] = &[
    // Leaves (no internal deps).
    "synth-cfg",
    "synth-core",
    // Direct consumers of the leaves.
    "synth-opt",
    "synth-frontend",
    // Depend on synth-{core,cfg,opt}.
    "synth-synthesis",
    // Depend on the above.
    "synth-backend",
    "synth-backend-awsm",
    "synth-backend-wasker",
    "synth-backend-riscv",
    "synth-verify",
    // Top of the tree.
    "synth-cli",
];

struct Krate {
    name: String,
    version: String,
}

fn main() {
    let mode = env::args().nth(1).expect("usage: publish {verify|publish}");

    let ws_version = read_workspace_version();
    let crates: Vec<Krate> = CRATES_TO_PUBLISH
        .iter()
        .map(|name| {
            let manifest = PathBuf::from(format!("crates/{name}/Cargo.toml"));
            assert!(
                manifest.exists(),
                "missing {}: publish order out of sync with crates/",
                manifest.display()
            );
            Krate {
                name: (*name).to_string(),
                version: ws_version.clone(),
            }
        })
        .collect();

    match mode.as_str() {
        "verify" => verify(&crates),
        "publish" => publish_all(crates),
        other => panic!("unknown command: {other}; expected verify|publish"),
    }
}

fn read_workspace_version() -> String {
    let toml = fs::read_to_string("Cargo.toml").expect("read workspace Cargo.toml");
    // Parse the version line inside [workspace.package].
    let mut in_pkg = false;
    for line in toml.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('[') {
            in_pkg = trimmed == "[workspace.package]";
            continue;
        }
        if in_pkg
            && let Some(rest) = trimmed.strip_prefix("version")
            && let Some(eq) = rest.find('=')
        {
            let v = rest[eq + 1..].trim();
            return v.trim_matches('"').to_string();
        }
    }
    panic!("could not find [workspace.package] version in Cargo.toml");
}

fn verify(crates: &[Krate]) {
    // #146: use `cargo package` rather than `cargo publish --dry-run`.
    // `--dry-run` resolves every workspace dep against crates.io, so for a
    // first publish of any new version the dependents always fail with the
    // chicken-and-egg "dep not yet published" error (this sank the v0.7.0
    // verify step, dropped in PR #144). `cargo package` resolves through the
    // local path deps, builds the `.crate` end-to-end, and still catches the
    // surface a pre-flight check should: missing README/license, bad
    // include/exclude, broken metadata, and code that doesn't compile.
    let mut failed = Vec::new();
    for k in crates {
        println!("--- cargo package -p {} ---", k.name);
        let status = Command::new("cargo")
            .args(["package", "-p", &k.name])
            .status()
            .expect("invoke cargo");
        if !status.success() {
            println!("FAIL: {} package failed: {status}", k.name);
            failed.push(k.name.clone());
        }
    }
    if !failed.is_empty() {
        eprintln!("\nverify failed for: {}", failed.join(", "));
        std::process::exit(1);
    }
    println!("\nAll {} crates passed cargo package.", crates.len());
}

fn publish_all(mut crates: Vec<Krate>) {
    for attempt in 1..=10 {
        crates.retain(|k| !try_publish(k));
        if crates.is_empty() {
            println!("\nAll crates published.");
            return;
        }
        println!(
            "\nattempt {attempt}: {} crates still pending; sleeping 40s for index propagation",
            crates.len()
        );
        thread::sleep(Duration::from_secs(40));
    }
    eprintln!(
        "\nstill failing after 10 attempts: {}",
        crates
            .iter()
            .map(|k| k.name.as_str())
            .collect::<Vec<_>>()
            .join(", ")
    );
    std::process::exit(1);
}

/// Returns true if the crate is now published (or was already published
/// at this version). Returns false if it failed and should be retried.
fn try_publish(k: &Krate) -> bool {
    if already_published(&k.name, &k.version) {
        println!("skip {}@{}: already on crates.io", k.name, k.version);
        return true;
    }
    println!("--- cargo publish -p {} ---", k.name);
    let status = Command::new("cargo")
        .args(["publish", "-p", &k.name])
        .status()
        .expect("invoke cargo");
    if status.success() {
        println!("published {}@{}", k.name, k.version);
        return true;
    }
    println!("FAIL: {}@{} ({status}) — will retry", k.name, k.version);
    false
}

fn already_published(name: &str, version: &str) -> bool {
    // crates.io API is rate-limited; treat any failure as "not
    // published" and let cargo publish itself be the authority.
    let out = Command::new("curl")
        .args([
            "-sf",
            "-A",
            "synth-publish-script (https://github.com/pulseengine/synth)",
            &format!("https://crates.io/api/v1/crates/{name}/{version}"),
        ])
        .output();
    match out {
        Ok(o) if o.status.success() => {
            // Body parses to JSON when the version exists; a 404 fails -sf above.
            !o.stdout.is_empty()
        }
        _ => false,
    }
}
