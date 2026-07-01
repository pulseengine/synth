//! VCR-DBG-001 step 4 (#394, #242) — the `--debug-line` EMIT oracles.
//!
//! synth's DWARF feature (v0.12.0) emits a `.debug_line` section mapping ARM
//! `.text` addresses back to the input wasm's source lines. PR A captured the
//! per-instruction `machine_offset → wasm_op_index` map; this PR wires the EMIT
//! side: read the input wasm's `.debug_line`, compose `arm_addr → source line`,
//! and add a NON-ALLOC PROGBITS `.debug_line` section to the relocatable object.
//!
//! Two oracles gate the feature:
//!
//!   A. ADDITIVITY (frozen-safe). Compiling with vs without `--debug-line` must
//!      leave `.text`/`.data`/`.bss` BYTE-IDENTICAL; ALL emitted `.debug_*`
//!      sections (`.debug_info`/`.debug_abbrev`/`.debug_str`/`.debug_line`)
//!      appear only under the flag. A no-DWARF input is byte-identical end-to-end
//!      (nothing to map ⇒ no sections). Proves the feature is purely additive —
//!      the default build is unchanged, so every frozen differential fixture holds.
//!
//!   B. CORRECTNESS (end-to-end, debugger-reachable). The emitted DWARF is real:
//!      walked the NORMAL debugger way (`gimli::Dwarf::load` → `dwarf.units()` →
//!      the unit's `DW_AT_stmt_list` line program) it resolves ≥1 ARM `.text`
//!      address (in-range) to a non-zero source line. This is the path a debugger
//!      takes, so passing it proves a debugger can reach the line data.

use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::process::Command;

use gimli::{EndianSlice, LittleEndian, SectionId};
use object::read::elf::ElfFile32;
use object::{Object, ObjectSection, ObjectSymbol};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn repro(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join(name)
}

/// Compile `wasm` to a relocatable object, optionally with `--debug-line`.
/// Returns the raw `.o` bytes.
fn compile(wasm: &Path, out: &str, debug_line: bool) -> Vec<u8> {
    let mut args = vec![
        "compile",
        wasm.to_str().unwrap(),
        "--target",
        "cortex-m4",
        "--all-exports",
        "--relocatable",
        "-o",
        out,
    ];
    if debug_line {
        args.push("--debug-line");
    }
    let r = Command::new(synth())
        .args(&args)
        .output()
        .expect("run synth");
    assert!(
        r.status.success(),
        "compile failed (debug_line={debug_line}): {}",
        String::from_utf8_lossy(&r.stderr)
    );
    std::fs::read(out).expect("read .o")
}

/// ORACLE D — the `--debug-line` HONEST-FAIL contract (#383 / VCR-DBG-001 PR C).
/// DWARF is emitted ONLY on the ARM relocatable-object path. On a SELF-CONTAINED
/// build (no imports, no `--relocatable` ⇒ a standalone executable image) there
/// is no relocatable `.text` symbol to anchor the addresses, so `--debug-line`
/// MUST loudly no-op — warn, emit no `.debug_*`, and still compile — rather than
/// silently mislead a consumer (jess) into expecting source lines that aren't
/// there (the #383 overclaim shape). v0.12.0 ships this behavior; this locks it.
///
/// (The relocatable path's positive behavior — `.debug_*` present and resolving
/// — is the additivity / resolves-to-source oracles above; this is its honest
/// negative complement, the previously-untested half of the contract.)
#[test]
fn debug_line_is_a_loud_noop_on_self_contained_build_394() {
    // gust_kernel imports nothing, so WITHOUT `--relocatable` synth emits a
    // self-contained executable image (not an ET_REL object).
    let wasm = repro("gust_kernel.wasm");
    let out = "/tmp/dbg394_selfcontained.elf";
    let r = Command::new(synth())
        .args([
            "compile",
            wasm.to_str().unwrap(),
            "--target",
            "cortex-m4",
            "--all-exports",
            "--debug-line",
            "-o",
            out,
        ])
        .output()
        .expect("run synth");

    // (1) it still compiles — the flag is a no-op, not an error.
    assert!(
        r.status.success(),
        "self-contained --debug-line must still compile: {}",
        String::from_utf8_lossy(&r.stderr)
    );

    // (2) it WARNS loudly (honest-fail), naming the relocatable-object path as
    // the way to actually get DWARF — never silent. The CLI's tracing subscriber
    // writes to stdout, so search the combined output rather than assuming a
    // stream.
    let mut output = String::from_utf8_lossy(&r.stdout).into_owned();
    output.push_str(&String::from_utf8_lossy(&r.stderr));
    assert!(
        output.contains("--debug-line has no effect") && output.contains("relocatable"),
        "expected a loud no-effect warning naming the relocatable path; output:\n{output}"
    );

    // (3) the emitted image is a standalone EXECUTABLE (confirms we exercised the
    // self-contained path, not ET_REL) and carries ZERO `.debug_*` sections.
    let elf = std::fs::read(out).expect("read elf");
    let obj = ElfFile32::<object::Endianness>::parse(&*elf).expect("parse ELF");
    assert_eq!(
        obj.kind(),
        object::ObjectKind::Executable,
        "self-contained build must be an executable image (ET_EXEC), not ET_REL"
    );
    let debug_sections: Vec<String> = obj
        .sections()
        .filter_map(|s| s.name().ok().map(str::to_string))
        .filter(|n| n.starts_with(".debug_"))
        .collect();
    assert!(
        debug_sections.is_empty(),
        "self-contained --debug-line must emit NO .debug_* sections (would be \
         unrelocated, silently-wrong addresses); found {debug_sections:?}"
    );
}

/// Map section-name → section data bytes (skip the null/empty-named section).
fn section_data(elf: &[u8]) -> HashMap<String, Vec<u8>> {
    let obj = ElfFile32::<object::Endianness>::parse(elf).expect("parse ELF");
    let mut out = HashMap::new();
    for sec in obj.sections() {
        if let Ok(name) = sec.name()
            && !name.is_empty()
        {
            out.insert(name.to_string(), sec.data().unwrap_or(&[]).to_vec());
        }
    }
    out
}

/// ORACLE A — additivity for a DWARF-carrying input: `.text`/`.data`/`.bss`
/// content is byte-identical with and without `--debug-line`; `.debug_line` is
/// present ONLY in the flagged build.
#[test]
fn debug_line_is_additive_on_dwarf_input_394() {
    let wasm = repro("msgq_put_359.wasm");
    let plain = compile(&wasm, "/tmp/dbg394_msgq_plain.o", false);
    let dbg = compile(&wasm, "/tmp/dbg394_msgq_dbg.o", true);

    let ps = section_data(&plain);
    let ds = section_data(&dbg);

    // The load-bearing code/data sections must be content-identical.
    for name in [".text", ".data", ".bss"] {
        match (ps.get(name), ds.get(name)) {
            (Some(a), Some(b)) => assert_eq!(
                a, b,
                "section {name} differs between plain and --debug-line builds"
            ),
            (None, None) => { /* fixture has no such section — fine */ }
            (a, b) => panic!(
                "section {name} presence mismatch: plain={} dbg={}",
                a.is_some(),
                b.is_some()
            ),
        }
    }

    // The whole DWARF unit appears only under the flag. Every `.debug_*` section
    // the emitter produces must be ABSENT in the plain build and PRESENT
    // (non-empty) in the flagged build — additivity over the full section set,
    // not just `.debug_line`. A debugger needs `.debug_info`/`.debug_abbrev`/
    // `.debug_str` to reach the line table via the CU's `DW_AT_stmt_list`.
    for name in [".debug_info", ".debug_abbrev", ".debug_str", ".debug_line"] {
        assert!(!ps.contains_key(name), "plain build must NOT carry {name}");
        assert!(
            ds.get(name).is_some_and(|d| !d.is_empty()),
            "--debug-line build must carry a non-empty {name}"
        );
    }
}

/// ORACLE A (no-DWARF half) — a wasm with no `.debug_line` produces a
/// BYTE-IDENTICAL object with or without `--debug-line` (nothing to map ⇒ no
/// section, no shstrtab change, no output change at all).
#[test]
fn debug_line_is_noop_on_nodwarf_input_394() {
    let wasm = repro("gust_kernel.wasm");
    let plain = compile(&wasm, "/tmp/dbg394_gust_plain.o", false);
    let dbg = compile(&wasm, "/tmp/dbg394_gust_dbg.o", true);
    assert_eq!(
        plain, dbg,
        "no-DWARF input: --debug-line must produce a byte-identical object"
    );
}

/// ORACLE B — the emitted DWARF is real, DEBUGGER-REACHABLE DWARF. Load the
/// emitted ELF's `.debug_*` sections and walk the NORMAL debugger path:
/// `gimli::Dwarf::load` → `dwarf.units()` → the unit's `DW_AT_stmt_list` line
/// program. Assert ≥1 row resolves an ARM `.text` address (in-range) to a
/// non-zero source line. If this CU→stmt_list walk finds rows, a debugger will
/// too — that is the property v0.12.0 actually promises.
#[test]
fn emitted_debug_line_resolves_arm_addr_to_source_394() {
    let wasm = repro("msgq_put_359.wasm");
    let dbg = compile(&wasm, "/tmp/dbg394_msgq_oracleb.o", true);

    let obj = ElfFile32::<object::Endianness>::parse(&*dbg).expect("parse ELF");
    let text_len = obj.section_by_name(".text").expect(".text present").size();
    assert!(text_len > 0, ".text must be non-empty");

    let secs = section_data(&dbg);

    // Load the full `.debug_*` section set the NORMAL gimli way — a debugger
    // resolves the line program through `.debug_info` → CU → `DW_AT_stmt_list`,
    // NOT by parsing `.debug_line` at offset 0. We must therefore reach the rows
    // by walking `dwarf.units()`; if that walk is empty, no debugger could reach
    // the line data even though `.debug_line` bytes exist.
    let empty: &[u8] = &[];
    let load = |id: SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
        let data = secs.get(id.name()).map_or(empty, |v| v.as_slice());
        Ok(EndianSlice::new(data, LittleEndian))
    };
    let dwarf = gimli::Dwarf::load(load).expect("load emitted .debug_* sections");

    let mut rows: Vec<(u64, u64)> = Vec::new();
    let mut unit_count = 0usize;
    let mut units = dwarf.units();
    while let Some(header) = units.next().expect("unit header") {
        unit_count += 1;
        let unit = dwarf.unit(header).expect("unit");
        let Some(program) = unit.line_program.clone() else {
            continue; // the CU has no DW_AT_stmt_list → unreachable line table
        };
        let mut state = program.rows();
        while let Some((_, row)) = state.next_row().expect("row") {
            if row.end_sequence() {
                continue;
            }
            if let Some(line) = row.line() {
                rows.push((row.address(), line.get()));
            }
        }
    }

    assert!(
        unit_count > 0,
        "emitted DWARF has NO compilation unit — `.debug_info` is missing or empty, \
         so a debugger cannot reach `.debug_line` via DW_AT_stmt_list"
    );
    assert!(
        !rows.is_empty(),
        "the normal `dwarf.units()` → line-program walk decoded ZERO rows from \
         {unit_count} unit(s); the CU's DW_AT_stmt_list does not reach the line table"
    );

    // At least one row must map a real ARM .text address to a non-zero line.
    let good = rows
        .iter()
        .filter(|&&(addr, line)| line > 0 && addr < text_len)
        .count();
    assert!(
        good > 0,
        "expected ≥1 .debug_line row with addr in .text (<0x{text_len:x}) and \
         non-zero line; got {} rows, sample: {:?}",
        rows.len(),
        rows.iter().take(5).collect::<Vec<_>>()
    );

    eprintln!(
        "[dbg394-oracleB] {unit_count} CU(s) via dwarf.units(); {} line rows, {good} \
         map an in-range .text addr to a non-zero source line. sample:",
        rows.len()
    );
    for (addr, line) in rows.iter().filter(|&&(a, l)| l > 0 && a < text_len).take(5) {
        eprintln!("  .text+0x{addr:04x} -> line {line}");
    }
}

/// R_ARM_ABS32 — the relocation type the DWARF `.text` references use.
const R_ARM_ABS32: u32 = 2;

/// Walk the NORMAL debugger path (`dwarf.units()` → CU `DW_AT_stmt_list` line
/// program) over a section-name → bytes map, returning every `(address, line)`
/// row. Shared by the un-relocated and relocated parses in Oracle C.
fn line_rows(secs: &HashMap<String, Vec<u8>>) -> Vec<(u64, u64)> {
    let empty: &[u8] = &[];
    let load = |id: SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
        let data = secs.get(id.name()).map_or(empty, |v| v.as_slice());
        Ok(EndianSlice::new(data, LittleEndian))
    };
    let dwarf = gimli::Dwarf::load(load).expect("load .debug_* sections");
    let mut rows = Vec::new();
    let mut units = dwarf.units();
    while let Some(header) = units.next().expect("unit header") {
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
                rows.push((row.address(), line.get()));
            }
        }
    }
    rows
}

/// ORACLE C — the `.rel.debug_*` relocations are real and CORRECT under linking
/// (VCR-DBG-001 PR C). The emitted object's `.debug_*` addresses are `.text`-base
/// 0; a host linker that places `.text` at a non-zero address must shift them via
/// `.rel.debug_*`. This oracle proves the records do exactly that:
///
///   1. `.debug_line` carries EXACTLY ONE relocation — `R_ARM_ABS32` against
///      `__synth_text_base` (the single `DW_LNE_set_address` anchor) — and
///      `.debug_info` one (the CU `DW_AT_low_pc`). REL form ⇒ the in-place addend
///      bytes are 0.
///   2. APPLY the `.debug_line` relocation at a NON-ZERO base (`S + A`, A=0 ⇒
///      the base itself), then re-walk the line program. EVERY row's address must
///      shift by exactly the base and its source LINE must be preserved — i.e. on
///      a linked image each `.text` address resolves to the SAME, CORRECT source
///      line it did object-relative. A missing/wrong relocation would leave the
///      addresses at base 0 (silently wrong on silicon — the #383 shape).
#[test]
fn rel_debug_relocations_shift_addresses_to_correct_line_394() {
    const LINK_BASE: u64 = 0x0800_0000; // a realistic non-zero flash `.text` base

    let wasm = repro("msgq_put_359.wasm");
    let dbg = compile(&wasm, "/tmp/dbg394_msgq_oraclec.o", true);
    let obj = ElfFile32::<object::Endianness>::parse(&*dbg).expect("parse ELF");

    // (1) Inspect the `.rel.debug_line` / `.rel.debug_info` records. object maps
    // each `.rel.<name>` (sh_info → target) onto the target section, so
    // `section.relocations()` yields them.
    let check_one_text_reloc = |sec_name: &str| -> u64 {
        let sec = obj
            .section_by_name(sec_name)
            .expect("debug section present");
        let relocs: Vec<_> = sec.relocations().collect();
        assert_eq!(
            relocs.len(),
            1,
            "{sec_name} must carry exactly one `.text` relocation (the single \
             relocatable address anchor); got {}",
            relocs.len()
        );
        let (offset, reloc) = &relocs[0];
        let offset = *offset;
        // R_ARM_ABS32 against __synth_text_base.
        match reloc.flags() {
            object::RelocationFlags::Elf { r_type } => assert_eq!(
                r_type, R_ARM_ABS32,
                "{sec_name} reloc must be R_ARM_ABS32, got r_type={r_type}"
            ),
            other => panic!("{sec_name} reloc has non-ELF flags: {other:?}"),
        }
        let object::RelocationTarget::Symbol(sym_idx) = reloc.target() else {
            panic!("{sec_name} reloc target is not a symbol");
        };
        let sym = obj.symbol_by_index(sym_idx).expect("reloc symbol");
        assert_eq!(
            sym.name().expect("sym name"),
            "__synth_text_base",
            "{sec_name} reloc must resolve against the .text base symbol"
        );
        // REL form: the in-place addend at the reloc site is 0.
        let data = sec.data().expect("section data");
        let off = offset as usize;
        let in_place = u32::from_le_bytes(data[off..off + 4].try_into().unwrap());
        assert_eq!(
            in_place, 0,
            "{sec_name} REL addend must be 0 in-place (S + A, A=0)"
        );
        offset
    };

    let line_reloc_off = check_one_text_reloc(".debug_line") as usize;
    let _ = check_one_text_reloc(".debug_info");

    // (2) Un-relocated rows (object-relative, base 0) vs rows after applying the
    // `.debug_line` relocation at a non-zero base.
    let secs = section_data(&dbg);
    let before = line_rows(&secs);
    assert!(!before.is_empty(), "expected line rows object-relative");

    let mut relocated = secs.clone();
    {
        let dl = relocated.get_mut(".debug_line").expect(".debug_line");
        // S + A with A = the in-place value (0) ⇒ write the link base itself.
        let patched = (LINK_BASE as u32).to_le_bytes();
        dl[line_reloc_off..line_reloc_off + 4].copy_from_slice(&patched);
    }
    let after = line_rows(&relocated);

    assert_eq!(
        before.len(),
        after.len(),
        "relocation changed the ROW COUNT — it must only shift addresses"
    );
    for ((a0, l0), (a1, l1)) in before.iter().zip(after.iter()) {
        assert_eq!(
            *l1, *l0,
            "relocation changed a source LINE ({l0} -> {l1}); it must preserve the mapping"
        );
        assert_eq!(
            *a1,
            a0 + LINK_BASE,
            "row at object-relative .text+0x{a0:x} did not shift to the linked \
             base 0x{LINK_BASE:x}+0x{a0:x} (got 0x{a1:x}); the `.rel.debug_line` \
             record is wrong"
        );
    }

    eprintln!(
        "[dbg394-oracleC] applied .rel.debug_line at base 0x{LINK_BASE:x}: {} rows \
         shifted by exactly the base, all source lines preserved.",
        after.len()
    );
}

/// The basename of a (possibly `/`- or `\`-separated) path string.
fn basename(name: &str) -> String {
    name.rsplit(['/', '\\']).next().unwrap_or(name).to_string()
}

/// Extract a wasm module's `.debug_*` custom sections into a name→bytes map.
fn wasm_debug_sections(wasm: &[u8]) -> HashMap<String, Vec<u8>> {
    use wasmparser::{Parser, Payload};
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

/// Walk a section-name→bytes DWARF map via `dwarf.units()` and return the
/// basenames of the source files that its `.debug_line` ROWS actually reference
/// (resolved through each unit's own file table). This is the set the compose
/// carries into the emitted object, so it is exactly what must reappear there —
/// derived from the fixture AT RUNTIME rather than hardcoded.
fn row_referenced_basenames(secs: &HashMap<String, Vec<u8>>) -> BTreeSet<String> {
    let empty: &[u8] = &[];
    let load = |id: SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
        let data = secs.get(id.name()).map_or(empty, |v| v.as_slice());
        Ok(EndianSlice::new(data, LittleEndian))
    };
    let dwarf = gimli::Dwarf::load(load).expect("load .debug_* sections");
    let mut out = BTreeSet::new();
    let mut units = dwarf.units();
    while let Some(header) = units.next().expect("unit header") {
        let unit = dwarf.unit(header).expect("unit");
        let Some(program) = unit.line_program.clone() else {
            continue;
        };
        // Clone the header (it borrows the program) before consuming `program`.
        let h = program.header().clone();
        let mut file_indices = Vec::new();
        let mut state = program.rows();
        while let Some((_, row)) = state.next_row().expect("row") {
            if row.end_sequence() {
                continue;
            }
            file_indices.push(row.file_index());
        }
        for fi in file_indices {
            if let Some(file) = h.file(fi)
                && let Ok(name) = dwarf.attr_string(&unit, file.path_name())
            {
                out.insert(basename(&name.to_string_lossy()));
            }
        }
    }
    out
}

/// Walk an emitted DWARF map and return the basenames present in the CU line
/// program's FILE TABLE (`header().file_names()`), the way a debugger reads it.
fn emitted_file_basenames(secs: &HashMap<String, Vec<u8>>) -> BTreeSet<String> {
    let empty: &[u8] = &[];
    let load = |id: SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
        let data = secs.get(id.name()).map_or(empty, |v| v.as_slice());
        Ok(EndianSlice::new(data, LittleEndian))
    };
    let dwarf = gimli::Dwarf::load(load).expect("load emitted .debug_* sections");
    let mut out = BTreeSet::new();
    let mut units = dwarf.units();
    while let Some(header) = units.next().expect("unit header") {
        let unit = dwarf.unit(header).expect("unit");
        let Some(program) = unit.line_program.clone() else {
            continue;
        };
        let h = program.header();
        for file in h.file_names() {
            if let Ok(name) = dwarf.attr_string(&unit, file.path_name()) {
                out.insert(basename(&name.to_string_lossy()));
            }
        }
    }
    out
}

/// ORACLE E — Tier-1 REAL source filenames (#394). Before this fix the emitter
/// hardcoded its only file as `synth.wasm` (dir `/synth`), a file that does not
/// exist, so gdb resolved every stop as `synth.wasm:N` — correct line, fabricated
/// file. This oracle proves the emitted line program's file table instead carries
/// the input wasm's REAL row-referenced source basenames (e.g. `panicking.rs`),
/// extracted from the fixture at runtime, and that `synth.wasm` is GONE.
#[test]
fn emitted_debug_line_carries_real_source_filenames_394() {
    let wasm = repro("msgq_put_359.wasm");
    let wasm_bytes = std::fs::read(&wasm).expect("read fixture wasm");

    // (a) The real source basenames the input's `.debug_line` rows reference —
    // exactly what the compose carries into the emitted object.
    let expected = row_referenced_basenames(&wasm_debug_sections(&wasm_bytes));
    assert!(
        !expected.is_empty(),
        "fixture must have `.debug_line` rows referencing ≥1 source file"
    );

    let dbg = compile(&wasm, "/tmp/dbg394_msgq_oraclee.o", true);
    let emitted = emitted_file_basenames(&section_data(&dbg));

    // (b) The fabricated filename must be GONE.
    assert!(
        !emitted.contains("synth.wasm"),
        "emitted line-program file table must NOT contain the fabricated \
         `synth.wasm`; got {emitted:?}"
    );

    // (a) The real row-referenced basenames must be present.
    for want in &expected {
        assert!(
            emitted.contains(want),
            "emitted file table missing real source file {want:?}; \
             expected {expected:?}, got {emitted:?}"
        );
    }

    eprintln!(
        "[dbg394-oracleE] input rows reference {expected:?}; emitted file table {emitted:?} \
         (real names propagated, synth.wasm gone)"
    );
}
