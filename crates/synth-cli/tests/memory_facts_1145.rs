//! RQ-91-MPUENFORCE (#1145): `--emit-memory-facts`.
//!
//! The execution oracle is `scripts/repro/memory_facts_1145_differential.py`
//! (every legitimate access attributed by PC to its function and checked
//! against the sidecar). These tests pin the contract that needs no emulator:
//! the object is byte-identical with the flag, the sidecar names that object
//! and the per-memory sets of gale's two-tenant module, and the refusals carry
//! their names.

use std::path::{Path, PathBuf};
use std::process::Command;

mod artifact_guard;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../scripts/repro")
        .join(name)
}

fn compile(input: &Path, tag: &str, extra: &[&str]) -> (PathBuf, Vec<u8>) {
    let out = artifact_guard::unique_artifact(&format!("memfacts_{tag}"), "o");
    let mut cmd = Command::new(synth());
    cmd.args([
        "compile",
        input.to_str().unwrap(),
        "--target",
        "cortex-m3",
        "--all-exports",
        "--relocatable",
        "--embedder-data-init",
        "-o",
        out.to_str().unwrap(),
    ])
    .args(extra);
    let bytes = artifact_guard::compile_bytes_or_panic(&mut cmd, &out, tag);
    (out, bytes)
}

fn sidecar(out: &Path) -> serde_json::Value {
    let mut p = out.as_os_str().to_os_string();
    p.push(".memfacts.json");
    serde_json::from_str(&std::fs::read_to_string(PathBuf::from(p)).expect("sidecar"))
        .expect("json")
}

fn sha256_hex(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

#[test]
fn two_tenant_facts_name_the_object_and_its_sets_1145() {
    let tt = fixture("mem_isolation_two_tenant_1145.wat");
    let (_, plain) = compile(&tt, "plain", &[]);
    let (out, with) = compile(
        &tt,
        "facts",
        &[
            "--emit-memory-facts",
            "--memory-domain",
            "a=0",
            "--memory-domain",
            "b=1",
        ],
    );
    assert_eq!(plain, with, "the object is byte-identical with the flag");
    let doc = sidecar(&out);
    assert_eq!(doc["schema"], "synth-memfacts-v1");
    assert_eq!(doc["object_sha256"], sha256_hex(&with));
    assert_eq!(doc["memory_count"], 2);
    let sets: Vec<(String, Vec<u64>, bool)> = doc["functions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|f| {
            (
                f["export"].as_str().unwrap().to_string(),
                f["memories"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|m| m.as_u64().unwrap())
                    .collect(),
                f["spans_domains"].as_bool().unwrap(),
            )
        })
        .collect();
    assert_eq!(
        sets,
        vec![
            ("read_a".to_string(), vec![0], false),
            ("read_b".to_string(), vec![1], false),
            ("write_a".to_string(), vec![0], false),
        ]
    );
    let m1 = &doc["memories"][1];
    assert_eq!(m1["base"]["symbol"], "__synth_mem_base_1");
    assert_eq!(m1["base"]["section"], ".synth.wasm_mem_1");
    assert_eq!(m1["section_align"], 65536);
    assert_eq!(m1["size_bytes"], 65536);
    assert_eq!(doc["memories"][0]["base"]["register"], "r11");
    // No call, so no crossing; the roles travel with the facts.
    assert_eq!(doc["cross_domain_edges"], serde_json::json!([]));
    for key in [
        "direct_spans_domains",
        "spans_domains",
        "cross_domain_edges",
    ] {
        assert!(doc["field_roles"][key].is_string(), "role for {key}");
    }
}

fn refused(wat: &str, tag: &str, extra: &[&str]) -> String {
    let dir = std::env::temp_dir().join("synth_memfacts_tests");
    std::fs::create_dir_all(&dir).unwrap();
    let src = dir.join(format!("{tag}.wat"));
    std::fs::write(&src, wat).unwrap();
    let out = Command::new(synth())
        .args([
            "compile",
            src.to_str().unwrap(),
            "--target",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
            "-o",
            dir.join(format!("{tag}.o")).to_str().unwrap(),
        ])
        .args(extra)
        .output()
        .unwrap();
    assert!(!out.status.success(), "{tag} must refuse");
    String::from_utf8_lossy(&out.stderr).into_owned()
}

#[test]
fn facts_refuse_by_name_1145() {
    let one = "(module (memory 1) (func (export \"f\") (result i32) (i32.load (i32.const 0))))";
    assert!(refused(one, "one_facts", &["--emit-memory-facts"]).contains("no region table"));
    let two = "(module (memory $a 1) (memory $b 1) (func (export \"f\") (result i32) \
               (i32.load $b (i32.const 0))))";
    assert!(
        refused(
            two,
            "partial",
            &["--emit-memory-facts", "--memory-domain", "t=0"]
        )
        .contains("belong to no domain")
    );
    assert!(
        refused(two, "nofacts", &["--memory-domain", "t=0,1"])
            .contains("without --emit-memory-facts")
    );
}
