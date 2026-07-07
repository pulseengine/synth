//! VCR-PERF-002 Phase 1 (#494) — `wsc.facts` ingestion is CODEGEN-NEUTRAL.
//!
//! Phase 1 is parse + plumbing only: loom's `wsc.facts` custom section
//! (encoding: `docs/design/wsc-facts-encoding.md`, schema v1) is decoded into
//! `CompileConfig::wsc_facts` / `current_func_facts`, and NOTHING consumes it
//! yet. The design doc's guarantee is that the facts-ABSENT compile is
//! byte-identical to baseline by construction; this gate proves the
//! facts-PRESENT compile is too — a module WITH a `wsc.facts` section must
//! produce `.text` byte-identical to the same module with the section
//! stripped, on the SHIPPED default configuration (no opt-out env vars — in
//! Phase 1 there is no lever to opt out of).
//!
//! Also locked here: the fail-safe skew rule end-to-end (loom#231 Q4) — a
//! MALFORMED or WRONG-VERSION section must neither fail the compile nor
//! change a byte (facts are optional accelerators; there is no error path).
//! Record-level parser behavior (each fact kind, unknown-kind tolerance,
//! truncation) is unit-tested in `synth-core/src/wsc_facts.rs`.
//!
//! NON-VACUITY: byte-identity would also hold if the section never parsed at
//! all, so `facts_actually_reach_the_decoded_module_494` first proves the
//! exact bytes appended here DO decode into facts via `decode_wasm_module` —
//! the same reader the compile paths use.
//!
//! Traceability: rivet `VCR-PERF-002` (epic #242), GitHub #494, loom#231.

use object::{Object, ObjectSection};
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join(name)
}

/// The frozen-suite control-flow fixture: multiple stores, a `br_if`, and a
/// clamp-ish shape — representative of what a fact would eventually annotate.
const FIXTURE: &str = "base_cse_branch.wat";

// ---- test-side encoders (mirror docs/design/wsc-facts-encoding.md) ----

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

/// A well-formed schema-v1 payload: the gust_mix-shaped value-range premise
/// `v ∈ [524, 1524]` on (func 0, value 1), plus a divisor-nonzero and a
/// from-the-future unknown kind (0x2A) that a tolerant parser must skip.
fn well_formed_facts_payload() -> Vec<u8> {
    let mut body = Vec::new();
    leb_s64(524, &mut body);
    leb_s64(1524, &mut body);

    let mut p = vec![0x01]; // version
    leb_u32(3, &mut p); // count
    // fact 1: value-range on (func 0, value 1)
    p.push(0x01);
    leb_u32(0, &mut p);
    leb_u32(1, &mut p);
    leb_u32(body.len() as u32, &mut p);
    p.extend_from_slice(&body);
    // fact 2: divisor-nonzero on (func 0, value 3)
    p.push(0x03);
    leb_u32(0, &mut p);
    leb_u32(3, &mut p);
    leb_u32(0, &mut p);
    // fact 3: unknown kind 0x2A with an opaque body (skipped via length prefix)
    p.push(0x2a);
    leb_u32(0, &mut p);
    leb_u32(4, &mut p);
    leb_u32(3, &mut p);
    p.extend_from_slice(&[0xde, 0xad, 0xbe]);
    p
}

/// Append a wasm custom section (id 0) named `wsc.facts` with `payload`.
fn append_wsc_facts_section(mut wasm: Vec<u8>, payload: &[u8]) -> Vec<u8> {
    let name = b"wsc.facts";
    let mut content = Vec::new();
    leb_u32(name.len() as u32, &mut content);
    content.extend_from_slice(name);
    content.extend_from_slice(payload);
    wasm.push(0x00); // custom section id
    leb_u32(content.len() as u32, &mut wasm);
    wasm.extend_from_slice(&content);
    wasm
}

/// Fixture wat → wasm bytes (the exact bytes the CLI would produce from .wat).
fn fixture_wasm() -> Vec<u8> {
    let wat = std::fs::read(fixture(FIXTURE)).expect("read fixture wat");
    wat::parse_bytes(&wat)
        .expect("fixture wat must parse")
        .into_owned()
}

/// Compile a `.wasm` byte blob on the shipped default config (optimized ARM
/// self-contained path, `--all-exports`) and return the `.text` bytes.
fn compile_text(wasm: &[u8], tag: &str) -> Vec<u8> {
    let dir = std::env::temp_dir().join("wsc_facts_494");
    std::fs::create_dir_all(&dir).expect("mk tempdir");
    let input = dir.join(format!("{tag}.wasm"));
    let elf = dir.join(format!("{tag}.elf"));
    std::fs::write(&input, wasm).expect("write wasm");
    let out = Command::new(synth())
        .args([
            "compile",
            input.to_str().unwrap(),
            "-o",
            elf.to_str().unwrap(),
            "-b",
            "arm",
            "--target",
            "cortex-m4",
            "--all-exports",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "#494 fail-safe violated: compile of '{tag}' failed (exit={:?}) — a \
         wsc.facts section must NEVER change a compilation outcome.\nstderr: {}",
        out.status.code(),
        String::from_utf8_lossy(&out.stderr)
    );
    let bytes = std::fs::read(&elf).expect("read elf");
    let obj = object::File::parse(&*bytes).expect("parse elf");
    obj.section_by_name(".text")
        .expect("fixture must have a .text section")
        .data()
        .expect("read .text")
        .to_vec()
}

/// NON-VACUITY GUARD: the exact section bytes the identity gates append DO
/// decode into facts through `decode_wasm_module` (the reader every compile
/// path uses). Without this, the byte-identity below would also pass if the
/// section were silently unparseable.
#[test]
fn facts_actually_reach_the_decoded_module_494() {
    use synth_core::wsc_facts::{FactKind, WscFact};
    let wasm = append_wsc_facts_section(fixture_wasm(), &well_formed_facts_payload());
    let module = synth_core::decode_wasm_module(&wasm).expect("decode");
    assert_eq!(
        module.wsc_facts,
        vec![
            WscFact {
                func_index: 0,
                value_id: 1,
                kind: FactKind::ValueRange { lo: 524, hi: 1524 },
            },
            WscFact {
                func_index: 0,
                value_id: 3,
                kind: FactKind::DivisorNonZero,
            },
        ],
        "well-formed facts must survive decode (unknown kind 0x2A skipped)"
    );
    // And the stripped module carries none.
    let module = synth_core::decode_wasm_module(&fixture_wasm()).expect("decode");
    assert_eq!(module.wsc_facts, vec![]);
}

/// THE PHASE-1 GATE (rivet VCR-PERF-002 verification-criteria, phase 1): a
/// module WITH a well-formed `wsc.facts` section compiles `.text`-byte-
/// identical to the same module WITHOUT it. Facts are parsed and threaded
/// (proven above) but consumed by nothing.
#[test]
fn facts_present_compile_is_byte_identical_494() {
    let base = fixture_wasm();
    let with_facts = append_wsc_facts_section(base.clone(), &well_formed_facts_payload());
    let text_without = compile_text(&base, "without_facts");
    let text_with = compile_text(&with_facts, "with_facts");
    assert_eq!(
        text_without, text_with,
        "#494 Phase 1 is ingestion ONLY: a wsc.facts section changed the \
         emitted .text with no consumer landed — some codegen path is reading \
         facts ahead of the Phase-2 gate (SYNTH_FACT_SPEC + per-elision \
         ordeal obligation)"
    );
}

/// Fail-safe skew rule end-to-end: a MALFORMED section (truncated framing)
/// and a WRONG-VERSION section both compile successfully AND byte-identical
/// to baseline — ignored entirely, never an error path.
#[test]
fn malformed_and_wrong_version_sections_are_ignored_494() {
    let base = fixture_wasm();
    let text_baseline = compile_text(&base, "skew_baseline");

    // Truncated: claims one record, provides only a kind byte.
    let malformed = append_wsc_facts_section(base.clone(), &[0x01, 0x01, 0x01]);
    let text_malformed = compile_text(&malformed, "skew_malformed");
    assert_eq!(
        text_baseline, text_malformed,
        "#494: a malformed wsc.facts section must be ignored entirely"
    );

    // Version 2 with otherwise-plausible bytes after it.
    let mut v2 = vec![0x02];
    v2.extend_from_slice(&well_formed_facts_payload()[1..]);
    let wrong_version = append_wsc_facts_section(base, &v2);
    let text_wrong_version = compile_text(&wrong_version, "skew_version");
    assert_eq!(
        text_baseline, text_wrong_version,
        "#494: an unknown-schema-version wsc.facts section must be ignored entirely"
    );
}
