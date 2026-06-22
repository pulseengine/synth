//! VCR-DBG-001 step 3 — compose the source-line table (the join half).
//!
//! The DWARF Tier-1 bridge maps an ARM text offset back to a source `file:line`
//! through three established facts:
//!   1. each ARM instruction carries `source_line` = the wasm OP INDEX
//!      (`ArmInstruction.source_line`);
//!   2. step 1 (`FunctionOps.op_offsets`) maps op-index → the wasm code BYTE
//!      OFFSET (module-relative);
//!   3. step 2 parses the input wasm's `.debug_line` → (code-section-relative
//!      address → `file:line`) rows.
//!
//! This module is the join for the wasm half — **op-index → source line** —
//! which step 4 (emit) composes with the ARM layout (ARM-text-offset → op-index
//! is just `source_line`). It is pure plain-data (no gimli, no backend): the
//! caller parses the rows and supplies them, so the module is Bazel-clean and
//! unwired (frozen-safe) until the emitter consumes it.
//!
//! The crux it encodes (validated on `scripts/repro/dwarf_coherent.wasm`,
//! VCR-DBG-001 step-3 fixture): `op_offsets` are MODULE-relative while DWARF
//! addresses are CODE-section-relative, and they differ by a single constant —
//! the code section's payload start. So normalization is one subtraction:
//! `dwarf_addr = op_offset - code_base`.

/// One `.debug_line` row: a code-section-relative address and its source line.
/// `file` is an opaque caller-supplied id (e.g. an index into the line
/// program's file table) so this stays gimli-free.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LineRow {
    /// Code-section-relative address (the DWARF-for-wasm address space).
    pub addr: u32,
    pub line: u32,
    pub file: u32,
}

/// A resolved source location for a wasm op.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceLoc {
    pub line: u32,
    pub file: u32,
}

/// Map each wasm op (by its module-relative `op_offsets` byte offset) to a
/// source location, by normalizing into the code-section-relative DWARF address
/// space (`op_offset - code_base`) and taking the covering line-table row (the
/// last row whose address is ≤ the op's address — standard line-table lookup).
///
/// Returns one entry per `op_offsets` element (parallel to a function's ops).
/// `None` where the op precedes `code_base` (shouldn't happen for real code) or
/// no row covers it (an op before the first line-table address).
pub fn op_offsets_to_source(
    op_offsets: &[u32],
    code_base: u32,
    rows: &[LineRow],
) -> Vec<Option<SourceLoc>> {
    let mut sorted: Vec<LineRow> = rows.to_vec();
    sorted.sort_by_key(|r| r.addr);
    op_offsets
        .iter()
        .map(|&off| {
            let a = off.checked_sub(code_base)?;
            // Largest row addr ≤ a (the line in effect at address a).
            sorted
                .iter()
                .rev()
                .find(|r| r.addr <= a)
                .map(|r| SourceLoc {
                    line: r.line,
                    file: r.file,
                })
        })
        .collect()
}

// ---------------------------------------------------------------------------
// VCR-DBG-001 step 4 — PRODUCTION read + emit (the `--debug-line` feature).
//
// `read_input_dwarf_line` ports the read-side spike
// (`tests/dwarf_line_read_spike.rs` + `dwarf_compose_step3.rs::code_base`):
// pull the `.debug_*` custom sections out of the input wasm, parse `.debug_line`
// with gimli, and also report the code-section payload start (`code_base`) the
// compose normalizes against. `emit_debug_sections` ports the emit-side spike
// (`tests/dwarf_emit_roundtrip_step4.rs::emit_dwarf`): take an address-ordered
// (arm_addr → source line) table and produce a FULL debugger-readable DWARF unit
// (`.debug_info`/`.debug_abbrev`/`.debug_str`/`.debug_line`) via gimli::write,
// the CU's DW_AT_stmt_list pointing at the line table. Both are gated behind
// `--debug-line`; when the input carries no DWARF, `read_input_dwarf_line`
// returns empty rows (graceful no-op) and the emit is skipped, so the default
// object stays bit-identical.

use std::collections::HashMap;

use gimli::{Dwarf, EndianSlice, LittleEndian, SectionId};
use wasmparser::{Parser, Payload};

/// Result of reading the input wasm's DWARF line table: the parsed rows plus the
/// code-section payload start (`code_base`) the op-offset compose subtracts.
#[derive(Debug, Default, Clone)]
pub struct InputDwarfLine {
    /// Code-section-relative `.debug_line` rows (`addr` is a wasm code byte
    /// offset; for the synth bridge that equals the DWARF address space).
    pub rows: Vec<LineRow>,
    /// Module-relative byte offset of the code section payload start. Empty wasm
    /// or a wasm with no code section reports 0.
    pub code_base: u32,
}

/// Read the input wasm's `.debug_line` into code-section-relative
/// `(addr → line)` rows and report `code_base`. Returns an empty table (rows
/// empty, the feature a no-op) when the input carries no `.debug_*` sections or
/// no parseable line program — never an error for a DWARF-free module.
pub fn read_input_dwarf_line(wasm: &[u8]) -> InputDwarfLine {
    // (a) extract every `.debug_*` custom section + find the code payload start.
    let mut sections: HashMap<String, Vec<u8>> = HashMap::new();
    let mut code_base = 0u32;
    for payload in Parser::new(0).parse_all(wasm) {
        match payload {
            Ok(Payload::CustomSection(c)) if c.name().starts_with(".debug_") => {
                sections.insert(c.name().to_string(), c.data().to_vec());
            }
            Ok(Payload::CodeSectionStart { range, .. }) => {
                code_base = range.start as u32;
            }
            _ => {}
        }
    }
    if !sections.contains_key(".debug_line") {
        return InputDwarfLine {
            rows: Vec::new(),
            code_base,
        };
    }

    // (b) parse `.debug_line` with gimli. A malformed line program degrades to
    // an empty table (the feature no-ops) rather than failing the compile.
    let rows = parse_debug_line_rows(&sections).unwrap_or_default();
    InputDwarfLine { rows, code_base }
}

/// gimli read of `.debug_line` → rows. `file` is recorded as the line program's
/// file index (kept opaque per `LineRow`'s contract; the compose carries it but
/// only `addr`/`line` are load-bearing for the wasm-offset bridge).
fn parse_debug_line_rows(
    sections: &HashMap<String, Vec<u8>>,
) -> Result<Vec<LineRow>, gimli::Error> {
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
        let mut state = program.rows();
        while let Some((_, row)) = state.next_row()? {
            if row.end_sequence() {
                continue;
            }
            rows.push(LineRow {
                addr: row.address() as u32,
                line: row.line().map(|l| l.get() as u32).unwrap_or(0),
                file: row.file_index() as u32,
            });
        }
    }
    Ok(rows)
}

/// Emit an address-ordered `(arm_addr, line)` table as a FULL minimal DWARF unit
/// (gimli::write) and return EVERY non-empty `.debug_*` section it produces —
/// `.debug_info`, `.debug_abbrev`, `.debug_str`, `.debug_line` (and
/// `.debug_line_str`/`.debug_ranges` etc. when non-empty). The caller composes
/// the table (one address-sorted, de-duped sequence covering every function);
/// this produces the section bytes for non-ALLOC ELF `PROGBITS` sections.
/// Returns an empty `Vec` for an empty table (nothing to map ⇒ no sections ⇒
/// output stays byte-identical).
///
/// Crucially this emits a real root `DW_TAG_compile_unit` DIE with `DW_AT_name`,
/// `DW_AT_low_pc`/`DW_AT_high_pc` spanning the emitted text, and the line program
/// attached — so the CU's `DW_AT_stmt_list` points at `.debug_line`. That makes
/// the line table reachable via the NORMAL debugger walk (`.debug_info` → CU →
/// `DW_AT_stmt_list` → line program), not just a standalone `.debug_line` parse.
///
/// Ports `tests/dwarf_emit_roundtrip_step4.rs::emit_dwarf` (which emits the same
/// full unit and round-trips through `Dwarf::units()`).
pub fn emit_debug_sections(table: &[(u64, u32)], text_sym: usize) -> Vec<EmittedDwarfSection> {
    use gimli::write::{Address, AttributeValue, DwarfUnit, LineProgram, LineString, Sections};

    if table.is_empty() {
        return Vec::new();
    }

    let encoding = gimli::Encoding {
        format: gimli::Format::Dwarf32,
        version: 4,
        address_size: 4,
    };
    let mut dwarf = DwarfUnit::new(encoding);

    // The span of emitted text the unit describes: low_pc=`.text`+0 (text base),
    // high_pc one past the last mapped address.
    let high_pc = table.iter().map(|&(a, _)| a).max().unwrap_or(0) + 1;

    // gimli 0.33 split the comp-dir/file args: (working_dir, source_dir,
    // source_file, source_file_info). source_dir = None ⇒ the file sits in
    // working_dir, matching the previous single-dir behaviour.
    let mut program = LineProgram::new(
        encoding,
        gimli::LineEncoding::default(),
        LineString::String(b"/synth".to_vec()),
        None,
        LineString::String(b"synth.wasm".to_vec()),
        None,
    );
    let dir = program.default_directory();
    let fid = program.add_file(LineString::String(b"synth.wasm".to_vec()), dir, None);

    // The sequence base is `.text + 0` as a RELOCATABLE address (one
    // `DW_LNE_set_address` against the `.text` symbol, addend 0); each row's
    // `address_offset` stays a text-relative DELTA, so only this single site
    // needs a relocation per section. Addend 0 ⇒ the in-place bytes are
    // byte-identical to the previous `Address::Constant(0)` form.
    let text_base = Address::Symbol {
        symbol: text_sym,
        addend: 0,
    };
    program.begin_sequence(Some(text_base));
    for &(addr, line) in table {
        let row = program.row();
        row.address_offset = addr;
        row.file = fid;
        row.line = line as u64;
        program.generate_row();
    }
    program.end_sequence(high_pc);
    dwarf.unit.line_program = program;

    // Populate the root DW_TAG_compile_unit DIE: a name, the text span, and (via
    // gimli auto-wiring the attached line_program) DW_AT_stmt_list → .debug_line.
    {
        let name_id = dwarf.strings.add("synth.wasm");
        let root = dwarf.unit.root();
        let root_die = dwarf.unit.get_mut(root);
        root_die.set(gimli::DW_AT_name, AttributeValue::StringRef(name_id));
        root_die.set(gimli::DW_AT_low_pc, AttributeValue::Address(text_base));
        root_die.set(gimli::DW_AT_high_pc, AttributeValue::Udata(high_pc));
    }

    let seed = RelocWriter {
        inner: gimli::write::EndianVec::new(LittleEndian),
        relocs: Vec::new(),
    };
    let mut sections = Sections::new(seed);
    if dwarf.write(&mut sections).is_err() {
        return Vec::new();
    }

    let mut out: Vec<EmittedDwarfSection> = Vec::new();
    let _ = sections.for_each(|id, w: &RelocWriter| -> Result<(), ()> {
        let bytes = w.inner.slice();
        if !bytes.is_empty()
            && let Some(name) = section_name(id)
        {
            let text_relocs = w
                .relocs
                .iter()
                .map(|&(offset, _addend, size)| DwarfTextReloc {
                    offset: offset as u32,
                    size,
                })
                .collect();
            out.push(EmittedDwarfSection {
                name,
                bytes: bytes.to_vec(),
                text_relocs,
            });
        }
        Ok(())
    });
    out
}

/// A relocation a `.debug_*` section needs against the `.text` symbol so a host
/// linker fixes up the embedded `.text` address when `.text` is placed. REL
/// form: the in-place bytes already hold the addend (always `0` for our
/// text-base references), so only the site (`offset`) and `size` travel here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DwarfTextReloc {
    /// Byte offset within the section where the relocated address word sits.
    pub offset: u32,
    /// Size of the relocated value (always 4 for DWARF32 addresses).
    pub size: u8,
}

/// One emitted `.debug_*` section: its ELF name, bytes, and the `.text`-symbol
/// relocations it needs (empty for address-free sections like `.debug_str`).
#[derive(Debug, Clone)]
pub struct EmittedDwarfSection {
    /// `'static` ELF section name (e.g. `.debug_line`).
    pub name: &'static str,
    /// Section payload bytes.
    pub bytes: Vec<u8>,
    /// `.text`-symbol relocations within this section (REL, in-place addend 0).
    pub text_relocs: Vec<DwarfTextReloc>,
}

/// A gimli `write::Writer` that delegates to an inner `EndianVec` but records
/// every `Address::Symbol` write as a relocation. ONLY `write_address` is
/// overridden — `write_offset` (gimli's internal section-to-section references,
/// e.g. `.debug_info` → `.debug_str`/`.debug_abbrev` and `DW_AT_stmt_list` →
/// `.debug_line`) keeps the default, so those stay CONCRETE intra-file offsets
/// and need no section symbols. The only relocations captured are the two
/// `.text` references (the line program's `DW_LNE_set_address` and the CU's
/// `DW_AT_low_pc`). `Clone` so `Sections::new` can seed each section writer.
#[derive(Clone)]
struct RelocWriter {
    inner: gimli::write::EndianVec<LittleEndian>,
    /// (offset within section, addend, size) for each `Address::Symbol` write.
    relocs: Vec<(usize, i64, u8)>,
}

impl gimli::write::Writer for RelocWriter {
    type Endian = LittleEndian;

    fn endian(&self) -> Self::Endian {
        self.inner.endian()
    }

    fn len(&self) -> usize {
        self.inner.len()
    }

    fn write(&mut self, bytes: &[u8]) -> gimli::write::Result<()> {
        self.inner.write(bytes)
    }

    fn write_at(&mut self, offset: usize, bytes: &[u8]) -> gimli::write::Result<()> {
        self.inner.write_at(offset, bytes)
    }

    fn write_address(
        &mut self,
        address: gimli::write::Address,
        size: u8,
    ) -> gimli::write::Result<()> {
        use gimli::write::Address;
        match address {
            Address::Constant(val) => self.inner.write_udata(val, size),
            Address::Symbol { symbol: _, addend } => {
                // REL: record the site and write the addend in place (0 ⇒ the
                // bytes match the old `Address::Constant(0)` exactly).
                let offset = self.inner.len();
                self.relocs.push((offset, addend, size));
                self.inner.write_udata(addend as u64, size)
            }
        }
    }
}

/// `'static` ELF section name for the `.debug_*` sections the emitter can
/// produce. Returns `None` for any section id we do not wire (none are expected
/// for this minimal unit, but the match keeps the names `'static`).
fn section_name(id: SectionId) -> Option<&'static str> {
    Some(match id {
        SectionId::DebugInfo => ".debug_info",
        SectionId::DebugAbbrev => ".debug_abbrev",
        SectionId::DebugStr => ".debug_str",
        SectionId::DebugLine => ".debug_line",
        SectionId::DebugLineStr => ".debug_line_str",
        SectionId::DebugRanges => ".debug_ranges",
        SectionId::DebugRngLists => ".debug_rnglists",
        SectionId::DebugStrOffsets => ".debug_str_offsets",
        SectionId::DebugAddr => ".debug_addr",
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn covering_row_lookup() {
        // code_base 100; rows at code-rel 0→line10, 8→line11, 20→line12.
        let rows = [
            LineRow {
                addr: 0,
                line: 10,
                file: 1,
            },
            LineRow {
                addr: 8,
                line: 11,
                file: 1,
            },
            LineRow {
                addr: 20,
                line: 12,
                file: 1,
            },
        ];
        // ops at module 100 (→0), 104 (→4), 108 (→8), 130 (→30).
        let got = op_offsets_to_source(&[100, 104, 108, 130], 100, &rows);
        assert_eq!(got[0].map(|s| s.line), Some(10)); // addr 0  → row 0
        assert_eq!(got[1].map(|s| s.line), Some(10)); // addr 4  → still row 0
        assert_eq!(got[2].map(|s| s.line), Some(11)); // addr 8  → row 8
        assert_eq!(got[3].map(|s| s.line), Some(12)); // addr 30 → row 20 (last ≤)
    }

    #[test]
    fn op_before_first_row_is_none() {
        let rows = [LineRow {
            addr: 8,
            line: 11,
            file: 1,
        }];
        // op at module 100 → code-rel 0, before the first row (addr 8).
        let got = op_offsets_to_source(&[100], 100, &rows);
        assert_eq!(got[0], None);
    }

    #[test]
    fn op_before_code_base_is_none() {
        let rows = [LineRow {
            addr: 0,
            line: 1,
            file: 1,
        }];
        let got = op_offsets_to_source(&[50], 100, &rows);
        assert_eq!(got[0], None);
    }
}
