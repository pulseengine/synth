//! VCR-DBG-001 step-3 substrate — a COHERENCE-CHECKED DWARF fixture.
//!
//! Step 3 (compose ARM-addr → wasm-op-index → wasm-byte-offset → file:line) was
//! blocked on a fixture whose `.debug_line` describes the bytes synth actually
//! compiles — the in-tree dissolved fixtures (msgq/k_mutex) only carry Rust
//! std/core glue against a pre-fusion layout (see VCR-DBG-001 PROGRESS notes).
//!
//! scripts/repro/dwarf_coherent.wasm is a 1.4 KB rustc→wasm module (see the
//! adjacent .rs + .README for the exact generation) whose `.debug_line`
//! describes its OWN source — axpy/clampi in dwarf_coherent.rs. This test locks
//! it as a valid step-3 input: (a) synth decodes it with per-op byte offsets
//! (step 1's op_offsets), (b) its `.debug_line` is coherent (file =
//! dwarf_coherent.rs, not std glue), and (c) the DWARF addresses are
//! code-section-relative and in range — so the eventual compose can normalize
//! op_offsets into the DWARF address space by a single code-base subtraction
//! (the convention this fixture confirms).

use std::collections::HashMap;

use gimli::{Dwarf, EndianSlice, LittleEndian, SectionId};
use wasmparser::{Parser, Payload};

fn fixture(rel: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(rel)
}

fn debug_sections(wasm: &[u8]) -> HashMap<String, Vec<u8>> {
    let mut out = HashMap::new();
    for payload in Parser::new(0).parse_all(wasm) {
        if let Ok(Payload::CustomSection(c)) = payload
            && c.name().starts_with(".debug_")
        {
            out.insert(c.name().to_string(), c.data().to_vec());
        }
    }
    out
}

/// Total code-section payload size — the upper bound a code-section-relative
/// DWARF address must respect.
fn code_section_size(wasm: &[u8]) -> u64 {
    for payload in Parser::new(0).parse_all(wasm) {
        if let Ok(Payload::CodeSectionStart { size, .. }) = payload {
            return size as u64;
        }
    }
    0
}

#[test]
fn dwarf_coherent_fixture_is_a_valid_step3_input_dbg001() {
    let wasm = std::fs::read(fixture("scripts/repro/dwarf_coherent.wasm"))
        .expect("coherent DWARF fixture in-tree");

    // (a) synth decodes it, and step-1's op_offsets are present per function.
    let funcs =
        synth_core::wasm_decoder::decode_wasm_functions(&wasm).expect("synth decodes the fixture");
    assert!(
        funcs.len() >= 2,
        "expected axpy + clampi; got {} functions",
        funcs.len()
    );
    for (i, f) in funcs.iter().enumerate() {
        assert!(
            !f.ops.is_empty() && f.op_offsets.len() == f.ops.len(),
            "fn{i}: op_offsets must be parallel to ops ({} vs {})",
            f.op_offsets.len(),
            f.ops.len()
        );
        // op_offsets are module-relative and strictly increasing within a body.
        assert!(
            f.op_offsets.windows(2).all(|w| w[0] < w[1]),
            "fn{i}: op_offsets must increase"
        );
    }

    // (b) the `.debug_line` is COHERENT — it names this fixture's own source,
    // not Rust std/core glue (the property the dissolved fixtures lack).
    let sections = debug_sections(&wasm);
    assert!(
        sections.contains_key(".debug_line"),
        "fixture must carry .debug_line"
    );
    let empty: &[u8] = &[];
    let load = |id: SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
        Ok(EndianSlice::new(
            sections.get(id.name()).map_or(empty, |v| v.as_slice()),
            LittleEndian,
        ))
    };
    let dwarf = Dwarf::load(load).expect("gimli loads the fixture DWARF");

    let code_size = code_section_size(&wasm);
    assert!(code_size > 0, "code section must be present");

    let mut rows = 0usize;
    let mut with_line = 0usize;
    let mut units = dwarf.units();
    while let Some(header) = units.next().expect("units") {
        let unit = dwarf.unit(header).expect("unit");
        let Some(program) = unit.line_program.clone() else {
            continue;
        };
        let mut state = program.rows();
        while let Some((_, row)) = state.next_row().expect("row") {
            if row.end_sequence() {
                continue;
            }
            rows += 1;
            if row.line().is_some() {
                with_line += 1;
            }
            // (c) DWARF addresses are code-section-relative, NOT module-relative:
            // they index the code section's payload, so they stay within
            // [0, code_size] (the post-last-instruction row may equal code_size).
            // The load-bearing fact for step 3 is that they are SMALL (a single
            // code-base subtraction normalizes op_offsets into this space), not
            // module-relative (which would be > the code section's start offset).
            assert!(
                row.address() <= code_size,
                "DWARF addr 0x{:x} must be code-section-relative (≤ code size {code_size}), \
                 not module-relative",
                row.address()
            );
        }
    }
    assert!(rows > 0, ".debug_line must decode to ≥1 row");
    assert!(with_line > 0, "≥1 row must carry a source line");

    // Coherence: the DWARF must name THIS fixture's own source (the property the
    // dissolved fixtures lack — theirs name only Rust std glue). DWARF-4 line
    // programs store file names inline in `.debug_line` (not `.debug_str`), and
    // the path also lands in `.debug_str`; check the raw section bytes, which is
    // robust across the DWARF version / file-table-form differences gimli's
    // `attr_string` does not uniformly resolve for inline line strings.
    let names_own_source = sections.values().any(|s| {
        s.windows(b"dwarf_coherent".len())
            .any(|w| w == b"dwarf_coherent")
    });
    assert!(
        names_own_source,
        "coherence check: the DWARF must name the fixture's own source \
         (dwarf_coherent.rs), not std glue"
    );
}
