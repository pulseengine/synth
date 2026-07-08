//! VCR-PERF-002 Phase 2 (#494) — end-to-end gates for the fact-spec clamp
//! elision (`SYNTH_FACT_SPEC`, default OFF; per-elision ordeal obligation).
//!
//! Requires the `verify` feature (the pass needs the ordeal-backed solver):
//! run with `cargo test -p synth-cli --features verify --test fact_spec_clamp_494`
//! (the fact-spec CI job does). The execution differential (oracle 2 —
//! specialized ≡ wasmtime ≡ unspecialized over the proven bound) lives in
//! `scripts/repro/fact_spec_clamp_494_differential.py`; here we lock the
//! flag/fact gating matrix and the certificate evidence trail:
//!
//! - flag OFF + facts present  → byte-identical to baseline (no consumer);
//! - flag ON  + no facts       → byte-identical (nothing to consume);
//! - flag ON  + proven bound   → .text SHRINKS + 2 certificate ADMIT lines;
//! - flag ON  + wrong bound    → byte-identical + loud Sat DECLINE with a
//!   counterexample (the obligation is the gate, not the fact's say-so).
//!
//! Frozen anchors are untouched by construction (no fixture carries a facts
//! section) and additionally locked by `frozen_codegen_bytes.rs`.

use object::{Object, ObjectSection};
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture_wasm() -> Vec<u8> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/fact_spec_clamp_494.wat");
    let wat = std::fs::read(path).expect("read fixture wat");
    wat::parse_bytes(&wat)
        .expect("fixture wat must parse")
        .into_owned()
}

// ---- schema-v1 encoders (mirror docs/design/wsc-facts-encoding.md) ----

fn leb_u32(mut v: u32, out: &mut Vec<u8>) {
    loop {
        let mut b = (v & 0x7f) as u8;
        v >>= 7;
        if v != 0 {
            b |= 0x80;
        }
        out.push(b);
        if v == 0 {
            return;
        }
    }
}

fn leb_s64(mut v: i64, out: &mut Vec<u8>) {
    loop {
        let mut b = (v & 0x7f) as u8;
        v >>= 7;
        let done = (v == 0 && b & 0x40 == 0) || (v == -1 && b & 0x40 != 0);
        if !done {
            b |= 0x80;
        }
        out.push(b);
        if done {
            return;
        }
    }
}

/// One value-range fact `[lo, hi]` on (func 0, value_id 0 = the `local.get`
/// producing `ch`), wrapped as the `wsc.facts` custom section.
fn with_range_fact(mut wasm: Vec<u8>, lo: i64, hi: i64) -> Vec<u8> {
    let mut body = Vec::new();
    leb_s64(lo, &mut body);
    leb_s64(hi, &mut body);
    let mut payload = vec![0x01]; // version
    leb_u32(1, &mut payload); // count
    payload.push(0x01); // kind: value-range
    leb_u32(0, &mut payload); // func_index
    leb_u32(0, &mut payload); // value_id
    leb_u32(body.len() as u32, &mut payload);
    payload.extend_from_slice(&body);

    let name = b"wsc.facts";
    let mut content = Vec::new();
    leb_u32(name.len() as u32, &mut content);
    content.extend_from_slice(name);
    content.extend_from_slice(&payload);
    wasm.push(0x00);
    leb_u32(content.len() as u32, &mut wasm);
    wasm.extend_from_slice(&content);
    wasm
}

/// Compile on the shipped optimized ARM path; return (.text bytes, stderr).
fn compile(wasm: &[u8], tag: &str, fact_spec: bool) -> (Vec<u8>, String) {
    let dir = std::env::temp_dir().join("fact_spec_494");
    std::fs::create_dir_all(&dir).expect("mk tempdir");
    let input = dir.join(format!("{tag}.wasm"));
    let elf = dir.join(format!("{tag}.elf"));
    std::fs::write(&input, wasm).expect("write wasm");
    let mut cmd = Command::new(synth());
    cmd.args([
        "compile",
        input.to_str().unwrap(),
        "-o",
        elf.to_str().unwrap(),
        "-b",
        "arm",
        "--target",
        "cortex-m4",
        "--all-exports",
    ]);
    if fact_spec {
        cmd.env("SYNTH_FACT_SPEC", "1");
    } else {
        cmd.env_remove("SYNTH_FACT_SPEC");
    }
    let out = cmd.output().expect("run synth");
    assert!(
        out.status.success(),
        "compile of '{tag}' failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let bytes = std::fs::read(&elf).expect("read elf");
    let obj = object::File::parse(&*bytes).expect("parse elf");
    let text = obj
        .section_by_name(".text")
        .expect(".text")
        .data()
        .expect("read .text")
        .to_vec();
    (text, String::from_utf8_lossy(&out.stderr).into_owned())
}

/// Flag OFF is byte-identical to baseline even with facts present — the
/// Phase-2 lever is opt-in (SYNTH_FACT_SPEC=0 ≡ baseline, rivet
/// verification-criteria).
#[test]
fn flag_off_with_facts_is_byte_identical_494() {
    let base = fixture_wasm();
    let facts = with_range_fact(base.clone(), 524, 1524);
    let (t_base, _) = compile(&base, "off_base", false);
    let (t_facts, _) = compile(&facts, "off_facts", false);
    assert_eq!(
        t_base, t_facts,
        "SYNTH_FACT_SPEC unset must never consume facts"
    );
}

/// Flag ON without facts is byte-identical — the lever cannot fire without a
/// premise (this is also why every frozen fixture is trivially safe).
#[test]
fn flag_on_without_facts_is_byte_identical_494() {
    let base = fixture_wasm();
    let (t_off, _) = compile(&base, "nofacts_off", false);
    let (t_on, _) = compile(&base, "nofacts_on", true);
    assert_eq!(t_off, t_on, "no facts ⇒ nothing to elide ⇒ identical bytes");
}

/// THE PHASE-2 GATE: under the proven bound ch ∈ [524, 1524] both clamp
/// branches are certificate-elided — the .text shrinks and the stderr carries
/// the per-elision evidence trail (UNSAT + certificate-checked, per function).
#[test]
fn proven_bound_elides_both_clamps_with_certificates_494() {
    let base = fixture_wasm();
    let facts = with_range_fact(base.clone(), 524, 1524);
    let (t_base, _) = compile(&base, "proven_base", false);
    let (t_spec, stderr) = compile(&facts, "proven_spec", true);

    let admits = stderr.matches("fact-spec: ADMIT").count();
    assert_eq!(
        admits, 2,
        "both clamp `if`s must be certificate-admitted; stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("UNSAT") && stderr.contains("certificate-checked"),
        "the admit lines are the evidence trail:\n{stderr}"
    );
    assert!(
        t_spec.len() < t_base.len(),
        "specialized .text ({} B) must shrink vs baseline ({} B)",
        t_spec.len(),
        t_base.len()
    );
}

/// Wrong-bound fact (ch ∈ [0, 4000]): the branch IS reachable under the
/// premise, so the obligation is Sat — synth declines LOUDLY (with a model
/// counterexample) and emits the general lowering, byte-identical to
/// baseline. The obligation is the gate; the fact alone admits nothing.
#[test]
fn wrong_bound_declines_loudly_and_changes_nothing_494() {
    let base = fixture_wasm();
    let facts = with_range_fact(base.clone(), 0, 4000);
    let (t_base, _) = compile(&base, "wrong_base", false);
    let (t_spec, stderr) = compile(&facts, "wrong_spec", true);

    assert_eq!(
        stderr.matches("fact-spec: ADMIT").count(),
        0,
        "a Sat obligation must never admit:\n{stderr}"
    );
    assert!(
        stderr.contains("fact-spec: DECLINE") && stderr.contains("counterexample"),
        "declines must be loud and carry a model:\n{stderr}"
    );
    assert_eq!(
        t_base, t_spec,
        "declined ⇒ the general lowering, byte-identical to baseline"
    );
}
