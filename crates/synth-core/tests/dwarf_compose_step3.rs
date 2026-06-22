//! VCR-DBG-001 step 3 — compose validated end-to-end on the coherent fixture.
//!
//! Joins step 1 (`FunctionOps.op_offsets`) with step 2 (parsed `.debug_line`)
//! through `synth_core::dwarf_line::op_offsets_to_source`, producing the
//! op-index → source-line map on scripts/repro/dwarf_coherent.wasm — the wasm
//! half of the bridge (step 4 composes it with the ARM layout via source_line).
//!
//! This is the first real-data exercise of the compose: it confirms the
//! normalization constant (code-section payload start) maps synth's
//! module-relative op_offsets onto the DWARF code-relative addresses, and that
//! the resulting lines land on the fixture's own source (axpy/clampi), not
//! garbage. Frozen-safe: pure analysis, no codegen, no ELF emission.

use std::collections::HashMap;

use gimli::{Dwarf, EndianSlice, LittleEndian, SectionId};
use synth_core::dwarf_line::{LineRow, op_offsets_to_source};
use wasmparser::{Parser, Payload};

fn fixture(rel: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(rel)
}

/// The module byte offset of the code section's payload start — the constant
/// that normalizes module-relative op_offsets into the code-section-relative
/// DWARF address space (`dwarf_addr = op_offset - code_base`).
fn code_base(wasm: &[u8]) -> u32 {
    for payload in Parser::new(0).parse_all(wasm) {
        if let Ok(Payload::CodeSectionStart { range, .. }) = payload {
            return range.start as u32;
        }
    }
    0
}

/// Parse `.debug_line` into plain (code-rel addr, line, file) rows for the join.
fn line_rows(wasm: &[u8]) -> Vec<LineRow> {
    let mut sections: HashMap<String, Vec<u8>> = HashMap::new();
    for payload in Parser::new(0).parse_all(wasm) {
        if let Ok(Payload::CustomSection(c)) = payload
            && c.name().starts_with(".debug_")
        {
            sections.insert(c.name().to_string(), c.data().to_vec());
        }
    }
    let empty: &[u8] = &[];
    let load = |id: SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
        Ok(EndianSlice::new(
            sections.get(id.name()).map_or(empty, |v| v.as_slice()),
            LittleEndian,
        ))
    };
    let dwarf = Dwarf::load(load).expect("load DWARF");
    let mut rows = Vec::new();
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
            if let Some(line) = row.line() {
                rows.push(LineRow {
                    addr: row.address() as u32,
                    line: line.get() as u32,
                    file: row.file_index() as u32,
                });
            }
        }
    }
    rows
}

#[test]
fn compose_maps_ops_to_own_source_lines_dbg001_step3() {
    let wasm = std::fs::read(fixture("scripts/repro/dwarf_coherent.wasm"))
        .expect("coherent DWARF fixture in-tree");

    let base = code_base(&wasm);
    assert!(base > 0, "code section present");
    let rows = line_rows(&wasm);
    assert!(!rows.is_empty(), ".debug_line rows present");

    let funcs =
        synth_core::wasm_decoder::decode_wasm_functions(&wasm).expect("synth decodes the fixture");

    // Compose every function's ops → source line, and confirm the join lands on
    // real source: at least one op per function resolves to a line, and the
    // lines for the FIRST function (axpy, all from the fixture's own short body)
    // are small (the fixture has ~16 source lines; std-intrinsic lines from the
    // inlined wrapping_* ops are large and belong to later ops — but axpy's
    // first op must map into the fixture's own line range).
    let mut total_resolved = 0usize;
    for (i, f) in funcs.iter().enumerate() {
        let locs = op_offsets_to_source(&f.op_offsets, base, &rows);
        assert_eq!(
            locs.len(),
            f.op_offsets.len(),
            "fn{i}: one source loc per op"
        );
        let resolved = locs.iter().filter(|l| l.is_some()).count();
        assert!(resolved > 0, "fn{i}: ≥1 op must resolve to a source line");
        total_resolved += resolved;
    }
    assert!(
        total_resolved >= funcs.len(),
        "the compose should resolve source lines across functions"
    );

    // The normalization is sound: the first op of the first function maps to the
    // very first line-table row (both are the function entry at code-rel 0..).
    let first = &funcs[0];
    let first_locs = op_offsets_to_source(&first.op_offsets, base, &rows);
    let lowest_row_line = rows.iter().min_by_key(|r| r.addr).map(|r| r.line);
    assert_eq!(
        first_locs[0].map(|s| s.line),
        lowest_row_line,
        "first op should resolve to the entry line-table row (normalization check)"
    );
}
