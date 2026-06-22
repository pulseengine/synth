//! VCR-DBG-001 step 4 (emit) — FROZEN-SAFE emit-logic spike.
//!
//! Closes the read→compose→EMIT→read loop on the coherent fixture: it composes
//! synth's op-index → source-line table (steps 1-3), emits it as a `.debug_line`
//! via gimli::write, then reads it back via gimli::read and asserts the emitted
//! section resolves the SAME addresses to the SAME source lines — i.e. synth's
//! composed mapping survives emission as debugger-readable DWARF.
//!
//! This de-risks the emit FORMAT/LOGIC only. It is test-only (gimli is a DEV
//! dependency), changes NO production code and NO output ELF, so the frozen
//! fixtures stay bit-identical. The remaining, GATED step-4 work — a production
//! gimli dep (+ MODULE.bazel pin), wiring the section into the ELF builder with
//! real ARM text offsets, and host-link survival — is the deliberate v0.12.0
//! release step (the byte-additive `.debug_line`, `.text` still bit-identical),
//! never an idle-tick increment. Here the wasm code-relative addresses stand in
//! for the ARM text offsets the wired emitter will use.

use std::collections::HashMap;

use gimli::write::{Address, DwarfUnit, EndianVec, LineProgram, LineString, Sections};
use gimli::{Dwarf, EndianSlice, LittleEndian, SectionId};
use synth_core::dwarf_line::{LineRow, SourceLoc, op_offsets_to_source};
use wasmparser::{Parser, Payload};

fn fixture(rel: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(rel)
}

fn code_base(wasm: &[u8]) -> u32 {
    for p in Parser::new(0).parse_all(wasm) {
        if let Ok(Payload::CodeSectionStart { range, .. }) = p {
            return range.start as u32;
        }
    }
    0
}

fn read_rows(wasm: &[u8]) -> Vec<LineRow> {
    let mut sections: HashMap<String, Vec<u8>> = HashMap::new();
    for p in Parser::new(0).parse_all(wasm) {
        if let Ok(Payload::CustomSection(c)) = p
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
    let dwarf = Dwarf::load(load).expect("load");
    let mut out = Vec::new();
    let mut units = dwarf.units();
    while let Some(h) = units.next().expect("u") {
        let unit = dwarf.unit(h).expect("unit");
        let Some(program) = unit.line_program.clone() else {
            continue;
        };
        let mut state = program.rows();
        while let Some((_, row)) = state.next_row().expect("r") {
            if row.end_sequence() {
                continue;
            }
            if let Some(line) = row.line() {
                out.push(LineRow {
                    addr: row.address() as u32,
                    line: line.get() as u32,
                    file: 0,
                });
            }
        }
    }
    out
}

/// Emit an (address → line) table as a full minimal DWARF (gimli::write),
/// returning every `.debug_*` section so the round-trip read (which walks
/// `.debug_info` → line program) can reload them.
fn emit_dwarf(table: &[(u64, u32)]) -> HashMap<String, Vec<u8>> {
    let encoding = gimli::Encoding {
        format: gimli::Format::Dwarf32,
        version: 4,
        address_size: 4,
    };
    let mut dwarf = DwarfUnit::new(encoding);
    let mut program = LineProgram::new(
        encoding,
        gimli::LineEncoding::default(),
        LineString::String(b"/synth".to_vec()),
        LineString::String(b"dwarf_coherent.rs".to_vec()),
        None,
    );
    let dir = program.default_directory();
    let fid = program.add_file(LineString::String(b"dwarf_coherent.rs".to_vec()), dir, None);

    program.begin_sequence(Some(Address::Constant(0)));
    for &(addr, line) in table {
        let row = program.row();
        row.address_offset = addr;
        row.file = fid;
        row.line = line as u64;
        program.generate_row();
    }
    let end = table.iter().map(|&(a, _)| a).max().unwrap_or(0) + 1;
    program.end_sequence(end);
    dwarf.unit.line_program = program;

    let mut sections = Sections::new(EndianVec::new(gimli::LittleEndian));
    dwarf.write(&mut sections).expect("write dwarf");
    let mut out = HashMap::new();
    sections
        .for_each(|id, data| -> Result<(), ()> {
            let bytes = data.slice().to_vec();
            if !bytes.is_empty() {
                out.insert(id.name().to_string(), bytes);
            }
            Ok(())
        })
        .expect("collect sections");
    out
}

#[test]
fn synth_composed_table_survives_emit_then_read_dbg001_step4() {
    let wasm = std::fs::read(fixture("scripts/repro/dwarf_coherent.wasm")).expect("fixture");
    let base = code_base(&wasm);
    let rows = read_rows(&wasm);
    let funcs = synth_core::wasm_decoder::decode_wasm_functions(&wasm).expect("decode");

    // Build synth's (code-relative address → line) table from the compose, for
    // every op that resolves (the wasm code-relative address stands in for the
    // ARM text offset the wired emitter will use). De-dup to monotonic rows.
    let mut table: Vec<(u64, u32)> = Vec::new();
    for f in &funcs {
        let locs = op_offsets_to_source(&f.op_offsets, base, &rows);
        for (op_off, loc) in f.op_offsets.iter().zip(locs.iter()) {
            if let Some(SourceLoc { line, .. }) = loc {
                let addr = (op_off - base) as u64;
                table.push((addr, *line));
            }
        }
    }
    table.sort_by_key(|&(a, _)| a);
    table.dedup_by_key(|&mut (a, _)| a);
    assert!(
        table.len() >= 2,
        "compose should yield ≥2 distinct address rows; got {}",
        table.len()
    );

    // Emit → read back → the emitted DWARF must resolve the same addresses to
    // the same lines (faithful round-trip).
    let sections = emit_dwarf(&table);
    assert!(
        sections.contains_key(".debug_line") && !sections[".debug_line"].is_empty(),
        "emitted .debug_line is non-empty"
    );
    let empty: &[u8] = &[];
    let load = |id: SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
        Ok(EndianSlice::new(
            sections.get(id.name()).map_or(empty, |v| v.as_slice()),
            LittleEndian,
        ))
    };
    let dwarf = Dwarf::load(load).expect("reload emitted");
    let mut back: HashMap<u64, u32> = HashMap::new();
    let mut units = dwarf.units();
    while let Some(h) = units.next().expect("u") {
        let unit = dwarf.unit(h).expect("unit");
        let Some(program) = unit.line_program.clone() else {
            continue;
        };
        let mut state = program.rows();
        while let Some((_, row)) = state.next_row().expect("r") {
            if row.end_sequence() {
                continue;
            }
            if let Some(line) = row.line() {
                back.insert(row.address(), line.get() as u32);
            }
        }
    }

    for &(addr, line) in &table {
        assert_eq!(
            back.get(&addr),
            Some(&line),
            "emitted .debug_line must resolve addr 0x{addr:x} to line {line}"
        );
    }
}
