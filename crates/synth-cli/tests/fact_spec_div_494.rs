//! VCR-PERF-002 Phase 2b (#494) — end-to-end gates for the divisor-nonzero
//! trap-guard elision (`SYNTH_FACT_SPEC`, default OFF; per-site ordeal
//! obligations, one per GUARD — the #633/#634 two-guard distinction).
//!
//! Requires the `verify` feature (the pass needs the ordeal-backed solver):
//! `cargo test -p synth-cli --features verify --test fact_spec_div_494`
//! (the fact-spec CI job does). The execution differential (oracle 3 —
//! specialized ≡ wasmtime ≡ unspecialized over the proven bound, plus the
//! red force-admit divergence demo) lives in
//! `scripts/repro/fact_spec_div_494_differential.py`; here we lock the byte
//! evidence and the certificate trail on `scripts/repro/fact_spec_div_494.wat`:
//!
//! - flag OFF + facts present → byte-identical to baseline (no consumer);
//! - flag ON + proven bounds  → the guard UDFs are GONE from qu/qs/ru, the
//!   i64 zero guard is gone from qs64 while its INT64_MIN/-1 OVERFLOW guard
//!   is RETAINED (divisor-nonzero alone never elides it), with one ADMIT
//!   certificate line per discharged obligation;
//! - flag ON + bound including 0 → Sat, loud decline, byte-identical
//!   (the guard is restored by the OBLIGATION, not by prudence);
//! - debug-only red lever: `SYNTH_FACT_SPEC_FORCE_ADMIT` admits the Sat site
//!   anyway (screaming) — the guard bytes vanish, proving the harness would
//!   catch an unsound admit; unsetting it restores baseline byte-identically.
//!
//! Frozen anchors are untouched by construction (no fixture carries a facts
//! section) and additionally locked by `frozen_codegen_bytes.rs`.

use object::{Object, ObjectSection, ObjectSymbol};
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture_wasm() -> Vec<u8> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/fact_spec_div_494.wat");
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

enum Fact {
    /// kind 0x01 — value-range `[lo, hi]` on `(func, value_id)`.
    Range(u32, u32, i64, i64),
    /// kind 0x03 — divisor-nonzero on `(func, value_id)`.
    NonZero(u32, u32),
}

/// Append the facts as one `wsc.facts` custom section.
fn with_facts(mut wasm: Vec<u8>, facts: &[Fact]) -> Vec<u8> {
    let mut payload = vec![0x01]; // version
    leb_u32(facts.len() as u32, &mut payload);
    for f in facts {
        match f {
            Fact::Range(func, vid, lo, hi) => {
                let mut body = Vec::new();
                leb_s64(*lo, &mut body);
                leb_s64(*hi, &mut body);
                payload.push(0x01);
                leb_u32(*func, &mut payload);
                leb_u32(*vid, &mut payload);
                leb_u32(body.len() as u32, &mut payload);
                payload.extend_from_slice(&body);
            }
            Fact::NonZero(func, vid) => {
                payload.push(0x03);
                leb_u32(*func, &mut payload);
                leb_u32(*vid, &mut payload);
                leb_u32(0, &mut payload); // empty body
            }
        }
    }
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

/// The green-run facts: d ∈ [1, 64] on the i32 divisors (discharges BOTH
/// div_s obligations), divisor-nonzero (kind 3) on the i64 divisor
/// (discharges the zero obligation ONLY — the overflow guard must survive).
fn proven_facts() -> Vec<Fact> {
    vec![
        Fact::Range(0, 1, 1, 64),
        Fact::Range(1, 1, 1, 64),
        Fact::Range(2, 1, 1, 64),
        Fact::NonZero(3, 1),
    ]
}

/// Compile on the shipped ARM path; return (.text, per-function slices, stderr).
fn compile(wasm: &[u8], tag: &str, fact_spec: bool, force_admit: bool) -> Compiled {
    let dir = std::env::temp_dir().join("fact_spec_div_494");
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
    if force_admit {
        cmd.env("SYNTH_FACT_SPEC_FORCE_ADMIT", "1");
    } else {
        cmd.env_remove("SYNTH_FACT_SPEC_FORCE_ADMIT");
    }
    let out = cmd.output().expect("run synth");
    assert!(
        out.status.success(),
        "compile of '{tag}' failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let bytes = std::fs::read(&elf).expect("read elf");
    let obj = object::File::parse(&*bytes).expect("parse elf");
    let text_section = obj.section_by_name(".text").expect(".text");
    let text = text_section.data().expect("read .text").to_vec();
    let text_addr = text_section.address();
    // Function regions from the symtab (the #489 lesson: symbols, not disasm
    // text). st_size may be 0 on this builder — slice to the next symbol.
    let text_end = text_addr + text.len() as u64;
    let mut syms: Vec<(String, u64)> = obj
        .symbols()
        .filter(|s| {
            // Thumb function symbols may carry the interworking bit.
            let addr = s.address() & !1;
            !s.name().unwrap_or("").is_empty() && addr >= text_addr && addr < text_end
        })
        .map(|s| {
            (
                s.name().unwrap().to_string(),
                (s.address() & !1) - text_addr,
            )
        })
        .collect();
    syms.sort_by_key(|&(_, a)| a);
    let mut funcs = std::collections::HashMap::new();
    for (i, (name, start)) in syms.iter().enumerate() {
        let end = syms
            .get(i + 1)
            .map(|&(_, a)| a as usize)
            .unwrap_or(text.len())
            .min(text.len());
        funcs.insert(name.clone(), text[*start as usize..end].to_vec());
    }
    Compiled {
        text,
        funcs,
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

struct Compiled {
    text: Vec<u8>,
    funcs: std::collections::HashMap<String, Vec<u8>>,
    stderr: String,
}

impl Compiled {
    /// Count aligned 16-bit words equal to `hw` in a function's region.
    fn halfword_count(&self, func: &str, hw: u16) -> usize {
        let code = self
            .funcs
            .get(func)
            .unwrap_or_else(|| panic!("symbol '{func}' missing from symtab"));
        code.chunks_exact(2)
            .filter(|c| u16::from_le_bytes([c[0], c[1]]) == hw)
            .count()
    }
}

const UDF0: u16 = 0xDE00; // divide-by-zero trap (and the i64 overflow trap)
const UDF1: u16 = 0xDE01; // i32 div_s INT32_MIN/-1 overflow trap

/// Flag OFF is byte-identical to baseline even with facts present.
#[test]
fn flag_off_with_facts_is_byte_identical_494() {
    let base = fixture_wasm();
    let facts = with_facts(base.clone(), &proven_facts());
    let t_base = compile(&base, "off_base", false, false);
    let t_facts = compile(&facts, "off_facts", false, false);
    assert_eq!(
        t_base.text, t_facts.text,
        "SYNTH_FACT_SPEC unset must never consume facts"
    );
}

/// THE PHASE-2b GATE (byte evidence, oracle 2): under the proven facts every
/// divide-by-zero guard is certificate-elided; the i32 div_s overflow guard
/// falls to the range fact's SEPARATE obligation; and the i64 div_s overflow
/// guard is RETAINED because divisor-nonzero alone does not discharge it
/// (#633/#634 — oracle 5).
#[test]
fn proven_facts_elide_guards_and_retain_i64_overflow_guard_494() {
    let base = fixture_wasm();
    let facts = with_facts(base.clone(), &proven_facts());
    let b = compile(&base, "proven_base", false, false);
    let s = compile(&facts, "proven_spec", true, false);

    // Baseline guard census: the guards are present without facts.
    assert_eq!(b.halfword_count("qu", UDF0), 1, "qu zero guard present");
    assert_eq!(b.halfword_count("qs", UDF0), 1, "qs zero guard present");
    assert_eq!(b.halfword_count("qs", UDF1), 1, "qs overflow guard present");
    assert_eq!(b.halfword_count("ru", UDF0), 1, "ru zero guard present");
    assert_eq!(
        b.halfword_count("qs64", UDF0),
        2,
        "qs64: zero trap + overflow trap"
    );

    // Specialized census: zero guards gone everywhere; i32 ovf gone (range
    // fact proves divisor != -1); i64 ovf RETAINED (kind-3 fact cannot).
    assert_eq!(s.halfword_count("qu", UDF0), 0, "qu zero guard elided");
    assert_eq!(s.halfword_count("qs", UDF0), 0, "qs zero guard elided");
    assert_eq!(s.halfword_count("qs", UDF1), 0, "qs overflow guard elided");
    assert_eq!(s.halfword_count("ru", UDF0), 0, "ru zero guard elided");
    assert_eq!(
        s.halfword_count("qs64", UDF0),
        1,
        "qs64: zero guard elided, INT64_MIN/-1 overflow guard RETAINED \
         (divisor ≠ 0 does not exclude -1 — the two-guard distinction)"
    );

    // Certificate trail: one ADMIT per discharged obligation — qu 1, qs 2
    // (zero + overflow, independently), ru 1, qs64 1 (zero only) = 5.
    let admits = s.stderr.matches("fact-spec: ADMIT").count();
    assert_eq!(admits, 5, "stderr:\n{}", s.stderr);
    assert!(
        s.stderr.contains("divide-by-zero guard elided")
            && s.stderr.contains("UNSAT(P ∧ divisor == 0)")
            && s.stderr.contains("certificate-checked"),
        "zero-guard admits name their obligation:\n{}",
        s.stderr
    );
    assert!(
        s.stderr.contains("overflow guard elided")
            && s.stderr.contains("dividend == INT32_MIN ∧ divisor == -1"),
        "the i32 overflow admit names its SEPARATE obligation:\n{}",
        s.stderr
    );
    // ... and the retained i64 overflow guard declined LOUDLY.
    assert!(
        s.stderr.contains("fact-spec: DECLINE")
            && s.stderr.contains("overflow-guard obligation Sat")
            && s.stderr.contains("RETAINED"),
        "the i64 overflow retention is a loud decline:\n{}",
        s.stderr
    );
}

/// A bound INCLUDING 0 is Sat: loud decline, guard bytes byte-identical to
/// baseline — the obligation is the gate, not the fact's say-so.
#[test]
fn bound_including_zero_declines_and_restores_guard_byte_identically_494() {
    let base = fixture_wasm();
    let facts = with_facts(base.clone(), &[Fact::Range(0, 1, 0, 64)]);
    let b = compile(&base, "sat_base", false, false);
    let s = compile(&facts, "sat_spec", true, false);
    assert_eq!(
        s.stderr.matches("fact-spec: ADMIT").count(),
        0,
        "a Sat obligation must never admit:\n{}",
        s.stderr
    );
    assert!(
        s.stderr.contains("zero-guard obligation Sat") && s.stderr.contains("counterexample"),
        "declines are loud and carry a model:\n{}",
        s.stderr
    );
    assert_eq!(
        b.text, s.text,
        "declined ⇒ the general lowering, byte-identical to baseline"
    );
}

/// RED (oracle 4, byte half): the debug-only force-admit lever elides the
/// guard under a Sat obligation — the UDF vanishes (this is the build whose
/// divisor=0 divergence the differential script demonstrates). Removing the
/// forcing restores the guard byte-identically (previous test). The lever
/// screams in the certificate line and is compiled out of release builds.
#[test]
fn force_admit_red_lever_elides_a_sat_guard_and_screams_494() {
    let base = fixture_wasm();
    let facts = with_facts(base.clone(), &[Fact::Range(0, 1, 0, 64)]);
    let forced = compile(&facts, "forced_spec", true, true);
    assert_eq!(
        forced.halfword_count("qu", UDF0),
        0,
        "the forced build must drop the guard — that is the point of the red demo"
    );
    assert!(
        forced.stderr.contains("UNSOUND FORCED ADMIT"),
        "the forced admit must scream:\n{}",
        forced.stderr
    );
}
