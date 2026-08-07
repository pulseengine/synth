//! #932 (CRITICAL/SECURITY) — `--proven-safe` must never elide against a floor
//! it invented.
//!
//! For a module whose memory is IMPORTED, the derived floor was
//! `all_memories.first().map(..).unwrap_or(0)` = **0**, because imported
//! memories are not in `all_memories`. The consequences, measured on v0.55.0:
//!
//! | claimed `memory_min_bytes` | verdict  | `udf` guards |
//! |---|---|---|
//! | baseline, no `--proven-safe` | —        | 2 |
//! | `0`     (vacuous)            | ACCEPTED | **0** — guards STRIPPED |
//! | `65536` (the truth)          | REFUSED  | 2 |
//!
//! The fail-closed contract inverted: the honest document was rejected and the
//! vacuous one stripped real guards, while synth printed "proved 1 access site
//! in-bounds against the 0 B floor" — self-refuting, since no access is in
//! bounds of a zero-byte memory. An imported memory is real at run time, so
//! that is an unguarded access at an attacker-controlled offset.
//!
//! # Why this test exists in this shape
//!
//! The #901 differential that gated the original feature used a module with a
//! **declared** memory, so the imported shape was never exercised and the
//! validator only ever saw the case it was written against. That is the blind
//! spot recorded after v0.53 — *two validators can share one blind spot; only
//! exercising the other shape catches it*. So this test pins the SHAPE, not
//! just the symptom.

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

/// Count the inline bounds-guard traps (`udf`) in the emitted object.
///
/// Read from synth's own disassembler so the test does not depend on
/// llvm-objdump being installed on the runner (the #850 host-dependency
/// lesson: a differential that needs a host tool is a differential that
/// silently stops running).
fn guard_count(obj: &Path) -> usize {
    let out = Command::new(synth())
        .args(["disasm", obj.to_str().unwrap()])
        .output()
        .expect("run synth disasm");
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .filter(|l| l.to_ascii_lowercase().contains("udf"))
        .count()
}

fn compile(dir: &Path, wasm: &Path, out: &str, verdicts: Option<&Path>) -> (PathBuf, String) {
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
    (obj, String::from_utf8_lossy(&o.stderr).to_string())
}

/// The sha256 synth computes over the bytes it hands to the DECODER.
///
/// Scraped from synth's own mismatch diagnostic rather than recomputed here:
/// the hash covers post-`.wat`-parse, post-loom, post-arena-bind bytes, so
/// hashing the source file would be a DIFFERENT number and the test would once
/// again pass for the wrong reason.
///
/// This matters more than it looks. The first version of this test used a dummy
/// hash, so every compile was refused at the HASH gate and the guards survived
/// for a reason unrelated to #932 — mutating the fix away did NOT make the test
/// fail. Getting the hash right is what makes the floor check the only thing
/// left that can refuse.
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
    let (_o, stderr) = compile(dir, wat, "probe.o", Some(&probe));
    let re_hash = stderr
        .split("hashes to ")
        .nth(1)
        .and_then(|s| s.split(['.', ' ', '\n']).next())
        .map(|s| s.trim().to_string());
    re_hash.unwrap_or_else(|| panic!("could not scrape the module hash from:\n{stderr}"))
}

const IMPORTED: &str = r#"(module
  (import "env" "memory" (memory 1))
  (func (export "probe") (param $a i32) (result i32) (i32.load (local.get $a))))
"#;

/// THE SECURITY PROPERTY. A module with no floor synth can establish must not
/// have a single guard elided — whatever the document claims.
#[test]
fn imported_memory_never_elides_against_an_invented_floor() {
    let dir = workdir("imported");
    let wat = dir.join("imp.wat");
    std::fs::write(&wat, IMPORTED).expect("write wat");

    let (_base, _) = compile(&dir, &wat, "base.o", None);
    let baseline = guard_count(&_base);
    let sha = actual_module_sha256(&dir, &wat);
    // Non-vacuity: if the baseline emits no guards the comparison below proves
    // nothing, and this test would pass over an empty set forever.
    assert!(
        baseline > 0,
        "fixture must emit bounds guards without --proven-safe, got {baseline}"
    );

    // Both the VACUOUS claim (0) and the TRUTHFUL one (65536) must leave every
    // guard standing: synth cannot establish the floor for an imported memory,
    // and absence of evidence is not evidence of safety.
    for claimed in [0u64, 65536] {
        let v = dir.join(format!("verdicts_{claimed}.json"));
        // The hash is CORRECT on purpose: with a wrong one the hash gate
        // refuses first and this test proves nothing about the floor (verified
        // by mutation — see `actual_module_sha256`).
        std::fs::write(
            &v,
            format!(
                r#"{{"schema":"scry/safe-accesses/v1",
                     "module_sha256":"{sha}",
                     "memory_min_bytes":{claimed},
                     "proven_safe":[{{"func":0,"pc":1,"op":"i32.load","width":4}}]}}"#
            ),
        )
        .expect("write verdicts");

        let (obj, stderr) = compile(&dir, &wat, &format!("out_{claimed}.o"), Some(&v));
        assert_eq!(
            guard_count(&obj),
            baseline,
            "claimed floor {claimed}: guards were elided for a module whose floor \
             synth cannot establish — this is #932, an unguarded access at an \
             attacker-controlled offset. stderr:\n{stderr}"
        );
        assert!(
            !stderr.contains("0 B floor"),
            "synth must never report proving anything 'against the 0 B floor' — \
             no access is in bounds of a zero-byte memory. stderr:\n{stderr}"
        );
    }
}

/// The feature must still WORK where a floor genuinely exists — otherwise the
/// fix above is indistinguishable from deleting the feature.
#[test]
fn declared_memory_still_elides_on_a_truthful_document() {
    let dir = workdir("declared");
    let wat = dir.join("decl.wat");
    std::fs::write(
        &wat,
        r#"(module
  (memory 1)
  (func (export "probe") (param $a i32) (result i32) (i32.load (local.get $a))))
"#,
    )
    .expect("write wat");

    let (base, _) = compile(&dir, &wat, "base.o", None);
    let baseline = guard_count(&base);
    assert!(baseline > 0, "fixture must emit guards, got {baseline}");

    let sha = actual_module_sha256(&dir, &wat);
    let v = dir.join("v.json");
    std::fs::write(
        &v,
        format!(
            r#"{{"schema":"scry/safe-accesses/v1","module_sha256":"{sha}",
                 "memory_min_bytes":65536,
                 "proven_safe":[{{"func":0,"pc":1,"op":"i32.load","width":4}}]}}"#
        ),
    )
    .expect("write verdicts");
    let (obj, stderr) = compile(&dir, &wat, "out.o", Some(&v));

    assert!(
        !stderr.contains("no linear memory"),
        "a DECLARED memory establishes a floor — the #932 refusal must not fire \
         here. stderr:\n{stderr}"
    );
    assert!(
        guard_count(&obj) < baseline,
        "the feature must still ELIDE where a floor genuinely exists, else the \
         #932 fix is indistinguishable from deleting it: baseline {baseline}, \
         got {}. stderr:\n{stderr}",
        guard_count(&obj)
    );
}
