//! VCR-DBG-001 Tier-1, STEP 2 (#394, #242) — READ the input wasm's DWARF.
//!
//! The DWARF feature-loop plan (artifacts/verified-codegen-roadmap.yaml,
//! VCR-DBG-001) bridges synth's source-to-object provenance in numbered steps:
//!
//!   (1) decoder records per-op wasm code BYTE OFFSET  → MERGED (#399): the
//!       `op_offsets: Vec<u32>` side-table on `FunctionOps`, giving
//!       wasm-op-index → wasm-byte-offset.
//!   (2) READ the input wasm DWARF (THIS spike): extract the `.debug_*` custom
//!       sections and parse `.debug_line` with gimli → (wasm-byte-offset →
//!       file:line) rows.
//!   (3) COMPOSE (1)+(2): ARM-text-offset → wasm-op-index → wasm-byte-offset →
//!       file:line.
//!   (4) EMIT the ARM/RV32 `.debug_line` as non-ALLOC ELF sections.
//!
//! This test proves step (2)'s READ capability in-tree, FROZEN-SAFE: gimli is a
//! DEV-dependency (no production dep, no MODULE.bazel pin — Bazel globs `src/`
//! only), the spike changes ZERO codegen, and every frozen fixture stays
//! bit-identical by construction. The production gimli dep + the emitter land
//! later (step 4), gated as a feature-loop release (v0.12.0).
//!
//! Real Rust/clang→wasm modules ship DWARF in custom sections; the in-tree
//! fixture `k_mutex_unlock.dissolved.wasm` carries `.debug_line`, `.debug_info`,
//! `.debug_abbrev`, `.debug_str`, and `.debug_ranges`. For a wasm module the
//! `.debug_line` row ADDRESS is the wasm code byte offset — exactly what step
//! (1)'s `op_offsets` produces, so steps (1) and (2) compose.

use std::collections::HashMap;

use gimli::{Dwarf, EndianSlice, LittleEndian, SectionId};
use wasmparser::{Parser, Payload};

/// Pull every `.debug_*` custom section out of a wasm module (the raw material
/// gimli consumes). wasmparser is already a production dep; this is the
/// extraction half of step (2).
fn extract_debug_sections(wasm: &[u8]) -> HashMap<String, Vec<u8>> {
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

fn fixture(rel: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(rel)
}

/// A resolved `.debug_line` row: the wasm code byte offset and its source line.
#[derive(Debug)]
struct LineRow {
    wasm_byte_offset: u64,
    line: u64,
    file: Option<String>,
}

/// Parse `.debug_line` from the extracted sections → (wasm-byte-offset → line)
/// rows. This is the parse half of step (2).
fn read_line_rows(sections: &HashMap<String, Vec<u8>>) -> Result<Vec<LineRow>, gimli::Error> {
    // gimli borrows section bytes; the closure hands each SectionId its bytes
    // (or an empty slice for sections this wasm doesn't carry).
    let empty: &[u8] = &[];
    let load = |id: SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
        let data = sections.get(id.name()).map_or(empty, |v| v.as_slice());
        Ok(EndianSlice::new(data, LittleEndian))
    };
    let dwarf = Dwarf::load(load)?;

    let mut rows = Vec::new();
    let mut units = dwarf.units();
    while let Some(header) = units.next()? {
        let unit = dwarf.unit(header)?;
        let Some(program) = unit.line_program.clone() else {
            continue;
        };
        let header = program.header().clone();
        let mut state = program.rows();
        while let Some((_, row)) = state.next_row()? {
            if row.end_sequence() {
                continue;
            }
            // Resolve the file name where the encoding makes it cheap (best
            // effort — DWARF<5 vs DWARF5 index conventions differ; the address
            // and line are the load-bearing facts for the wasm-offset bridge).
            let file = row.file(&header).and_then(|fe| {
                dwarf
                    .attr_string(&unit, fe.path_name())
                    .ok()
                    .and_then(|s| s.to_string().ok().map(|s| s.to_string()))
            });
            rows.push(LineRow {
                wasm_byte_offset: row.address(),
                line: row.line().map(|l| l.get()).unwrap_or(0),
                file,
            });
        }
    }
    Ok(rows)
}

#[test]
fn reads_wasm_debug_line_into_offset_line_rows_dbg001_step2() {
    let wasm = std::fs::read(fixture(
        "scripts/repro/synth-331/k_mutex_unlock.dissolved.wasm",
    ))
    .expect("DWARF-carrying fixture in-tree");
    let wasm_size = wasm.len() as u64;

    // (a) extraction — the fixture carries .debug_line + the tables it needs.
    let sections = extract_debug_sections(&wasm);
    assert!(
        sections.contains_key(".debug_line"),
        "fixture must carry .debug_line; found sections: {:?}",
        sections.keys().collect::<Vec<_>>()
    );
    assert!(
        !sections[".debug_line"].is_empty(),
        ".debug_line must be non-empty"
    );

    // (b) parse — gimli yields (wasm-byte-offset → line) rows.
    let rows = read_line_rows(&sections).expect("gimli parses the fixture's .debug_line");
    assert!(
        !rows.is_empty(),
        ".debug_line should decode to ≥1 source-line row"
    );

    // Soundness of the bridge: every row's address is a wasm code byte offset
    // (in range), and at least one row carries a real (non-zero) source line —
    // the wasm-offset → source mapping step (3) will compose against op_offsets.
    for r in &rows {
        assert!(
            r.wasm_byte_offset < wasm_size,
            "row offset {} out of wasm bounds {}",
            r.wasm_byte_offset,
            wasm_size
        );
    }
    let with_line = rows.iter().filter(|r| r.line > 0).count();
    assert!(
        with_line > 0,
        "expected ≥1 row with a non-zero source line; got {} rows",
        rows.len()
    );

    eprintln!(
        "[dbg001-step2] {} .debug_line rows from synth-331/k_mutex_unlock.dissolved.wasm \
         ({with_line} with a source line). sample:",
        rows.len(),
    );
    for r in rows.iter().filter(|r| r.line > 0).take(5) {
        eprintln!(
            "  wasm+0x{:04x} -> {}:{}",
            r.wasm_byte_offset,
            r.file.as_deref().unwrap_or("<file?>"),
            r.line
        );
    }
}
