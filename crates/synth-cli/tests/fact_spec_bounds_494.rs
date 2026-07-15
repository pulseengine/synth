//! #494 bounds-elision × #390 `guard_bool` — end-to-end byte gates for the
//! ordeal-certified memory bounds-guard elision (`SYNTH_FACT_SPEC`, default
//! OFF; per-site obligation `UNSAT(P ∧ trap_mem_oob(zext64(index) + offset,
//! size, min_memory_bytes))`, ordeal 0.9.1 `trap_mem_oob` shape with
//! wraparound-safe 64-bit width extension).
//!
//! Requires the `verify` feature (the pass needs the ordeal-backed solver):
//! `cargo test -p synth-cli --features verify --test fact_spec_bounds_494`
//! (the fact-spec CI job does). The execution differential (in-bounds sweep
//! ≡ wasmtime ≡ unspecialized, the retained-trap leg, and the red
//! force-admit divergence demo) lives in
//! `scripts/repro/fact_spec_bounds_494_differential.py`; here we lock the
//! byte evidence and the certificate trail on
//! `scripts/repro/fact_spec_bounds_494.wat` (the gust_poll-shaped fixture —
//! 8 software-guarded accesses over a 16 B task-record array):
//!
//! - flag OFF + facts present → byte-identical to baseline (no consumer);
//! - flag ON + proven `slot ∈ [0, 63]` → all EIGHT guard UDFs are GONE and
//!   `poll` shrinks by 80 B (184 → 104 B — each guard is ADD.w 4 B + CMP
//!   2 B + BLO 2 B + UDF 2 B), one ADMIT certificate line per site;
//! - flag ON + a bound admitting OOB (`slot ∈ [0, 8192]`) → Sat, loud
//!   decline, byte-identical (the guard is restored by the OBLIGATION, not
//!   by prudence);
//! - flag ON + facts but WITHOUT `--safety-bounds software` → the marks are
//!   admitted (the obligation is mode-independent) but there is no guard to
//!   strip — the lowering stays sound and UDF-free either way.
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
        .join("scripts/repro/fact_spec_bounds_494.wat");
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

/// Append one value-range fact (`slot ∈ [lo, hi]` on func 0, value_id 0 —
/// the fixture's first `local.get $slot`) as a `wsc.facts` custom section.
fn with_slot_range(mut wasm: Vec<u8>, lo: i64, hi: i64) -> Vec<u8> {
    let mut payload = vec![0x01]; // version
    leb_u32(1, &mut payload); // one record
    let mut body = Vec::new();
    leb_s64(lo, &mut body);
    leb_s64(hi, &mut body);
    payload.push(0x01); // kind: ValueRange
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

/// Compile on the shipped ARM path; return (.text, per-function slices, stderr).
fn compile(wasm: &[u8], tag: &str, fact_spec: bool, software_bounds: bool) -> Compiled {
    let dir = std::env::temp_dir().join("fact_spec_bounds_494");
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
    if software_bounds {
        cmd.args(["--safety-bounds", "software"]);
    }
    if fact_spec {
        cmd.env("SYNTH_FACT_SPEC", "1");
    } else {
        cmd.env_remove("SYNTH_FACT_SPEC");
    }
    cmd.env_remove("SYNTH_FACT_SPEC_FORCE_ADMIT");
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
    fn func(&self, name: &str) -> &[u8] {
        self.funcs
            .get(name)
            .unwrap_or_else(|| panic!("symbol '{name}' missing from symtab"))
    }

    /// Count aligned 16-bit words equal to `hw` in a function's region.
    fn halfword_count(&self, func: &str, hw: u16) -> usize {
        self.func(func)
            .chunks_exact(2)
            .filter(|c| u16::from_le_bytes([c[0], c[1]]) == hw)
            .count()
    }
}

const UDF0: u16 = 0xDE00; // the software bounds-guard trap (#377 inline UDF)

/// Flag OFF is byte-identical to baseline even with facts present.
#[test]
fn flag_off_with_facts_is_byte_identical_494() {
    let base = fixture_wasm();
    let facts = with_slot_range(base.clone(), 0, 63);
    let t_base = compile(&base, "off_base", false, true);
    let t_facts = compile(&facts, "off_facts", false, true);
    assert_eq!(
        t_base.text, t_facts.text,
        "SYNTH_FACT_SPEC unset must never consume facts"
    );
}

/// THE BOUNDS-ELISION GATE (byte evidence): under `slot ∈ [0, 63]` all eight
/// software bounds guards are certificate-elided — the UDFs vanish and the
/// function sheds exactly 8 × 10 B of guard code (#390's `guard_bool` class).
#[test]
fn proven_slot_bound_elides_all_eight_guards_494() {
    let base = fixture_wasm();
    let facts = with_slot_range(base.clone(), 0, 63);
    let b = compile(&base, "proven_base", false, true);
    let s = compile(&facts, "proven_spec", true, true);

    // Baseline guard census: eight inline guards, one per access.
    assert_eq!(b.halfword_count("poll", UDF0), 8, "baseline guards present");
    assert_eq!(s.halfword_count("poll", UDF0), 0, "all guards elided");

    // The measured byte win — pinned exactly so a regression (or an
    // improvement) shows as a required update, like the size oracle.
    let (b_len, s_len) = (b.func("poll").len(), s.func("poll").len());
    assert_eq!(b_len, 184, "baseline poll size drifted");
    assert_eq!(s_len, 104, "specialized poll size drifted");
    assert_eq!(b_len - s_len, 80, "8 guards x 10 B (ADD.w+CMP+BLO+UDF)");

    // Certificate trail: one ADMIT per access, naming the obligation.
    let admits = s.stderr.matches("fact-spec: ADMIT").count();
    assert_eq!(admits, 8, "stderr:\n{}", s.stderr);
    assert!(
        s.stderr.contains("software bounds guard elided")
            && s.stderr.contains("trap_mem_oob")
            && s.stderr.contains("certificate-checked"),
        "admits name their obligation:\n{}",
        s.stderr
    );
}

/// A bound admitting OOB (`slot = 4096` ⇒ base = 65792 > 65536) is Sat:
/// loud decline, guard bytes byte-identical to baseline — the obligation is
/// the gate, not the fact's say-so.
#[test]
fn oob_admissible_bound_declines_and_restores_guards_byte_identically_494() {
    let base = fixture_wasm();
    let facts = with_slot_range(base.clone(), 0, 8192);
    let b = compile(&base, "sat_base", false, true);
    let s = compile(&facts, "sat_spec", true, true);
    assert_eq!(
        s.stderr.matches("fact-spec: ADMIT").count(),
        0,
        "a Sat obligation must never admit:\n{}",
        s.stderr
    );
    assert!(
        s.stderr.contains("bounds-guard obligation Sat") && s.stderr.contains("counterexample"),
        "declines are loud and carry a model:\n{}",
        s.stderr
    );
    assert_eq!(
        s.text, b.text,
        "declined build must be byte-identical to baseline"
    );
    assert_eq!(s.halfword_count("poll", UDF0), 8, "all guards retained");
}

/// Marks without `--safety-bounds software`: nothing to strip — the
/// unguarded lowering is emitted either way (mode-independent soundness;
/// `Masking` never consumes a mark by construction).
#[test]
fn marks_without_software_bounds_have_no_guard_to_strip_494() {
    let base = fixture_wasm();
    let facts = with_slot_range(base.clone(), 0, 63);
    let s = compile(&facts, "nobounds_spec", true, false);
    assert_eq!(
        s.stderr.matches("fact-spec: ADMIT").count(),
        8,
        "the obligation is bounds-mode-independent:\n{}",
        s.stderr
    );
    assert_eq!(s.halfword_count("poll", UDF0), 0, "no guards, no UDFs");
}
