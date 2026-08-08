//! #932 (CRITICAL/SECURITY) — `--proven-safe` must never elide against a floor
//! it invented.
//!
//! For a module whose memory is IMPORTED, the derived floor was
//! `all_memories.first().map(..).unwrap_or(0)` = **0**, because imported
//! memories live in `imports`, not `memories`. Measured on v0.55.0:
//!
//! | claimed `memory_min_bytes` | verdict  | bounds guards |
//! |---|---|---|
//! | baseline, no `--proven-safe` | —        | present |
//! | `0`     (vacuous)            | ACCEPTED | **STRIPPED** |
//! | `65536` (the truth)          | REFUSED  | present |
//!
//! The fail-closed contract inverted: the honest document rejected, the vacuous
//! one stripping real guards, while synth printed "proved 1 access site
//! in-bounds against the 0 B floor" — self-refuting, since no access is in
//! bounds of a zero-byte memory. An imported memory is real at run time, so
//! that is an unguarded access at an attacker-controlled offset.
//!
//! # Why this test exists in this shape
//!
//! The #901 differential that gated the original feature used a module with a
//! **declared** memory, so the imported shape was never exercised and the
//! validator only ever saw the case it was written against — the v0.53 lesson
//! that a validator tests the shape it was written against. This pins the
//! SHAPE, not just the symptom.

use std::path::{Path, PathBuf};
use std::process::Command;

fn synth() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_synth"))
}

fn workdir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("synth-932-{tag}"));
    std::fs::create_dir_all(&d).expect("temp dir");
    d
}

/// Bytes of machine code, from synth's OWN stdout (`Total code size: N bytes`).
///
/// NOT from disassembly. The first version counted `udf` mnemonics in
/// `synth disasm` output; it passed on macOS and returned ZERO on the ubuntu
/// runner, failing both tests with "fixture must emit guards, got 0". That is a
/// lesson already recorded in this repo and violated anyway: **disassembly TEXT
/// is host-dependent — read structure, not rendering.** It also traded an
/// `llvm-objdump` host dependency for a worse one.
///
/// Code size is synth's own number, identical on every host, and it moves for
/// exactly the reason under test: eliding a bounds guard REMOVES instructions
/// (measured on the declared-memory fixture: 24 B guarded, 8 B elided).
fn code_size(stdout: &str) -> usize {
    stdout
        .split("Total code size:")
        .nth(1)
        .and_then(|s| s.split_whitespace().next())
        .and_then(|n| n.parse().ok())
        .unwrap_or_else(|| panic!("no 'Total code size:' in synth stdout:\n{stdout}"))
}

/// Compile and return `(code_size_bytes, stderr)`.
fn compile(dir: &Path, wasm: &Path, out: &str, verdicts: Option<&Path>) -> (usize, String) {
    let obj = dir.join(out);
    let mut c = Command::new(synth());
    c.args([
        "compile",
        wasm.to_str().unwrap(),
        "-b",
        "arm",
        "--target",
        "cortex-m4",
        "--safety-bounds",
        "software",
        "--all-exports",
        "--relocatable",
        "-o",
        obj.to_str().unwrap(),
    ]);
    if let Some(v) = verdicts {
        c.args(["--proven-safe", v.to_str().unwrap()]);
    }
    let o = c.output().expect("run synth compile");
    assert!(
        o.status.success(),
        "compile failed: {}",
        String::from_utf8_lossy(&o.stderr)
    );
    (
        code_size(&String::from_utf8_lossy(&o.stdout)),
        String::from_utf8_lossy(&o.stderr).to_string(),
    )
}

/// The sha256 synth computes over the bytes it hands to the DECODER, scraped
/// from synth's own diagnostic.
///
/// This matters more than it looks. The first version of this test used a dummy
/// hash, so every compile was refused at the HASH gate and the guards survived
/// for a reason unrelated to #932 — mutating the fix away did NOT fail the
/// test. Making the hash CORRECT is what leaves the floor check as the only
/// thing that can refuse.
fn actual_module_sha256(dir: &Path, wat: &Path) -> String {
    let probe = dir.join("probe_hash.json");
    std::fs::write(
        &probe,
        format!(
            r#"{{"schema":"scry/safe-accesses/v1","module_sha256":"{}",
                 "memory_min_bytes":65536,"proven_safe":[]}}"#,
            "0".repeat(64)
        ),
    )
    .expect("write probe");
    let (_sz, stderr) = compile(dir, wat, "probe.o", Some(&probe));
    stderr
        .split("hashes to ")
        .nth(1)
        .and_then(|s| s.split(['.', ' ', '\n']).next())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| panic!("could not scrape the module hash from:\n{stderr}"))
}

fn verdict_doc(dir: &Path, name: &str, sha: &str, claimed: u64) -> PathBuf {
    let v = dir.join(name);
    std::fs::write(
        &v,
        format!(
            r#"{{"schema":"scry/safe-accesses/v1","module_sha256":"{sha}",
                 "memory_min_bytes":{claimed},
                 "proven_safe":[{{"func":0,"pc":1,"op":"i32.load","width":4}}]}}"#
        ),
    )
    .expect("write verdicts");
    v
}

const IMPORTED: &str = r#"(module
  (import "env" "memory" (memory 1))
  (func (export "probe") (param $a i32) (result i32) (i32.load (local.get $a))))
"#;

const DECLARED: &str = r#"(module
  (memory 1)
  (func (export "probe") (param $a i32) (result i32) (i32.load (local.get $a))))
"#;

/// THE SECURITY PROPERTY. A module whose floor synth cannot establish must keep
/// every guard — whatever the document claims.
#[test]
fn imported_memory_never_elides_against_an_invented_floor() {
    let dir = workdir("imported");
    let wat = dir.join("imp.wat");
    std::fs::write(&wat, IMPORTED).expect("write wat");

    let (baseline, _) = compile(&dir, &wat, "base.o", None);
    // Non-vacuity: with no code there is nothing to elide and the comparisons
    // below would pass over an empty set forever.
    assert!(
        baseline > 0,
        "fixture must emit code without --proven-safe, got {baseline} bytes"
    );
    let sha = actual_module_sha256(&dir, &wat);

    // The VACUOUS claim (0) and the TRUTHFUL one (65536) must BOTH leave the
    // code untouched: synth cannot establish this module's floor, and absence
    // of evidence is not evidence of safety.
    for claimed in [0u64, 65536] {
        let v = verdict_doc(&dir, &format!("verdicts_{claimed}.json"), &sha, claimed);
        let (size, stderr) = compile(&dir, &wat, &format!("out_{claimed}.o"), Some(&v));
        assert_eq!(
            size, baseline,
            "claimed floor {claimed}: code SHRANK {baseline} -> {size} bytes, i.e. \
             guards were elided for a module whose floor synth cannot establish. \
             That is #932 — an unguarded access at an attacker-controlled \
             offset. stderr:\n{stderr}"
        );
        assert!(
            !stderr.contains("0 B floor"),
            "synth must never report proving anything 'against the 0 B floor' — \
             no access is in bounds of a zero-byte memory. stderr:\n{stderr}"
        );
    }
}

/// The feature must still WORK where a floor genuinely exists, or the fix above
/// is indistinguishable from deleting it.
#[test]
fn declared_memory_still_elides_on_a_truthful_document() {
    let dir = workdir("declared");
    let wat = dir.join("decl.wat");
    std::fs::write(&wat, DECLARED).expect("write wat");

    let (baseline, _) = compile(&dir, &wat, "base.o", None);
    assert!(baseline > 0, "fixture must emit code, got {baseline} bytes");
    let sha = actual_module_sha256(&dir, &wat);

    let v = verdict_doc(&dir, "v.json", &sha, 65536);
    let (size, stderr) = compile(&dir, &wat, "out.o", Some(&v));

    assert!(
        !stderr.contains("no linear memory"),
        "a DECLARED memory establishes a floor — the #932 refusal must not fire \
         here. stderr:\n{stderr}"
    );
    assert!(
        size < baseline,
        "the feature must still ELIDE where a floor genuinely exists, else the \
         #932 fix is indistinguishable from deleting it: baseline {baseline}, \
         got {size}. stderr:\n{stderr}"
    );
}
