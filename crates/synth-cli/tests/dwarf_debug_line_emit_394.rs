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
//!
//! Oracles A–H parse the emitted bytes with `gimli::read` — the same library that
//! WROTE them. Oracle I (`emitted_dwarf_verifies_with_llvm_dwarfdump_394`) closes
//! that self-consistency gap with the INDEPENDENT LLVM parser: `llvm-dwarfdump
//! --verify` must report no errors and `--debug-info`/`--debug-line` must decode
//! the subprogram DIEs and line rows. The tool is REQUIRED (the gate fails, never
//! skips, if it is absent), and CI installs `llvm` so it is always present.

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
///      `__synth_text_base` (the single `DW_LNE_set_address` anchor), REL form ⇒
///      its in-place addend is 0. `.debug_info` carries `1 + N` relocations
///      (#394): the CU `DW_AT_low_pc` (addend 0) plus one per `DW_TAG_subprogram`
///      `DW_AT_low_pc`, each `R_ARM_ABS32` against `__synth_text_base` with its
///      in-place addend equal to that function's object-relative `.text` offset —
///      so on link each subprogram resolves to `text_base + low_pc`.
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

    // `.debug_info`: 1 CU low_pc reloc (addend 0) + one per subprogram low_pc
    // (addend = that function's object-relative `.text` offset), all R_ARM_ABS32
    // against `__synth_text_base`. The multiset of in-place addends must equal
    // {0} ∪ {each subprogram low_pc}, proving every subprogram low_pc relocates
    // by the base to `text_base + low_pc` (#394).
    {
        let subs = collect_subprograms(&section_data(&dbg));
        assert!(
            !subs.is_empty(),
            ".debug_info reloc check needs ≥1 subprogram DIE"
        );
        let sec = obj
            .section_by_name(".debug_info")
            .expect(".debug_info present");
        let data = sec.data().expect(".debug_info data");
        let relocs: Vec<_> = sec.relocations().collect();
        assert_eq!(
            relocs.len(),
            1 + subs.len(),
            ".debug_info must carry 1 (CU low_pc) + {} (subprogram low_pc) `.text` \
             relocations; got {}",
            subs.len(),
            relocs.len()
        );
        let mut got_addends: Vec<u64> = Vec::new();
        for (offset, reloc) in &relocs {
            match reloc.flags() {
                object::RelocationFlags::Elf { r_type } => assert_eq!(
                    r_type, R_ARM_ABS32,
                    ".debug_info reloc must be R_ARM_ABS32, got r_type={r_type}"
                ),
                other => panic!(".debug_info reloc has non-ELF flags: {other:?}"),
            }
            let object::RelocationTarget::Symbol(sym_idx) = reloc.target() else {
                panic!(".debug_info reloc target is not a symbol");
            };
            let sym = obj.symbol_by_index(sym_idx).expect("reloc symbol");
            assert_eq!(
                sym.name().expect("sym name"),
                "__synth_text_base",
                ".debug_info reloc must resolve against the .text base symbol"
            );
            let off = *offset as usize;
            got_addends.push(u32::from_le_bytes(data[off..off + 4].try_into().unwrap()) as u64);
        }
        got_addends.sort_unstable();
        // Expected: the CU (0) plus every subprogram's object-relative low_pc.
        let mut expected: Vec<u64> = std::iter::once(0u64)
            .chain(subs.iter().map(|s| s.low_pc))
            .collect();
        expected.sort_unstable();
        assert_eq!(
            got_addends, expected,
            ".debug_info in-place addends must be {{0 (CU)}} ∪ subprogram low_pcs; \
             each subprogram low_pc must relocate by the base"
        );
    }

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

/// One emitted `DW_TAG_subprogram` DIE: its `DW_AT_name` and the object-relative
/// `[low_pc, high_pc)` its `DW_AT_low_pc`/`DW_AT_high_pc` describe. On an ET_REL
/// object the low_pc read here is the in-place addend (object-relative `.text`
/// offset, base 0); `DW_AT_high_pc` is the offset form (size), so
/// `high_pc = low_pc + size`.
#[derive(Debug, Clone)]
struct SubprogramDie {
    name: Option<String>,
    low_pc: u64,
    high_pc: u64,
}

/// Walk an emitted DWARF map the debugger way (`dwarf.units()` → the CU tree) and
/// collect every `DW_TAG_subprogram` child DIE's name + `[low_pc, high_pc)`.
fn collect_subprograms(secs: &HashMap<String, Vec<u8>>) -> Vec<SubprogramDie> {
    let empty: &[u8] = &[];
    let load = |id: SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
        let data = secs.get(id.name()).map_or(empty, |v| v.as_slice());
        Ok(EndianSlice::new(data, LittleEndian))
    };
    let dwarf = gimli::Dwarf::load(load).expect("load emitted .debug_* sections");
    let mut out = Vec::new();
    let mut units = dwarf.units();
    while let Some(header) = units.next().expect("unit header") {
        let unit = dwarf.unit(header).expect("unit");
        let mut entries = unit.entries();
        while let Some(entry) = entries.next_dfs().expect("dfs") {
            if entry.tag() != gimli::DW_TAG_subprogram {
                continue;
            }
            let name = entry
                .attr_value(gimli::DW_AT_name)
                .and_then(|v| dwarf.attr_string(&unit, v).ok())
                .map(|s| s.to_string_lossy().into_owned());
            let low_pc = match entry.attr_value(gimli::DW_AT_low_pc) {
                Some(gimli::AttributeValue::Addr(a)) => a,
                other => panic!("subprogram DW_AT_low_pc must be an Addr, got {other:?}"),
            };
            // Tier-1 emits high_pc as the offset (size) form.
            let size = match entry.attr_value(gimli::DW_AT_high_pc) {
                Some(gimli::AttributeValue::Udata(n)) => n,
                other => {
                    panic!("subprogram DW_AT_high_pc must be Udata (offset form), got {other:?}")
                }
            };
            out.push(SubprogramDie {
                name,
                low_pc,
                high_pc: low_pc + size,
            });
        }
    }
    out
}

/// The exported FUNCTION names declared in the input wasm's export section —
/// ground truth for the subprogram names, derived from the fixture at runtime
/// (like Oracle E's filenames), NOT from synth's own symbol table. These MUST
/// reappear as `DW_TAG_subprogram` `DW_AT_name`s.
fn wasm_exported_func_names(wasm: &[u8]) -> BTreeSet<String> {
    use wasmparser::{ExternalKind, Parser, Payload};
    let mut out = BTreeSet::new();
    for payload in Parser::new(0).parse_all(wasm) {
        if let Ok(Payload::ExportSection(reader)) = payload {
            for export in reader.into_iter().flatten() {
                if export.kind == ExternalKind::Func {
                    out.insert(export.name.to_string());
                }
            }
        }
    }
    out
}

/// ORACLE F — Tier-1 `DW_TAG_subprogram` DIEs (#394). A debugger backtrace shows
/// FUNCTION NAMES (not bare addresses) only if each function has a subprogram DIE
/// carrying its name and address range. Before this fix the emitted CU had ZERO
/// children, so gdb/lldb resolved a `.text` address to `file:line` but printed no
/// function frame. This oracle proves the emitter now attaches one
/// `DW_TAG_subprogram` per compiled function under the CU:
///
///   (a) every EXPORTED wasm function name (derived from the input's export
///       section at runtime — non-circular) appears as a subprogram `DW_AT_name`;
///   (b) the subprogram COUNT equals the number of `func_N` symbols the object
///       defines (one per compiled function);
///   (c) every subprogram's `[low_pc, high_pc)` lies within `.text`
///       (`low_pc < high_pc <= text_len`).
#[test]
fn emitted_debug_info_has_subprogram_dies_per_function_394() {
    let wasm = repro("msgq_put_359.wasm");
    let wasm_bytes = std::fs::read(&wasm).expect("read fixture wasm");
    let expected_names = wasm_exported_func_names(&wasm_bytes);
    assert!(
        !expected_names.is_empty(),
        "fixture must export ≥1 function to anchor the name check"
    );

    let dbg = compile(&wasm, "/tmp/dbg394_msgq_oraclef.o", true);
    let obj = ElfFile32::<object::Endianness>::parse(&*dbg).expect("parse ELF");
    let text_len = obj.section_by_name(".text").expect(".text present").size();
    assert!(text_len > 0, ".text must be non-empty");

    // Count `func_N` symbols — every compiled function defines exactly one, so
    // this is a synth-independent-of-DWARF count of the functions in the object.
    let func_sym_count = obj
        .symbols()
        .filter_map(|s| s.name().ok().map(str::to_string))
        .filter(|n| {
            n.strip_prefix("func_")
                .is_some_and(|d| !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit()))
        })
        .count();
    assert!(func_sym_count > 0, "object must define ≥1 func_N symbol");

    let subs = collect_subprograms(&section_data(&dbg));
    assert!(
        !subs.is_empty(),
        "emitted CU has NO DW_TAG_subprogram children — a debugger backtrace \
         would show addresses, not function names"
    );

    // (b) one subprogram per compiled function.
    assert_eq!(
        subs.len(),
        func_sym_count,
        "expected one DW_TAG_subprogram per compiled function ({func_sym_count} \
         func_N symbols); got {} subprograms: {:?}",
        subs.len(),
        subs.iter().map(|s| &s.name).collect::<Vec<_>>()
    );

    // (c) every subprogram range is inside `.text`.
    for s in &subs {
        assert!(
            s.low_pc < s.high_pc && s.high_pc <= text_len,
            "subprogram {:?} range [0x{:x},0x{:x}) is not within .text (<0x{text_len:x})",
            s.name,
            s.low_pc,
            s.high_pc
        );
    }

    // (a) every exported function name is present as a subprogram DW_AT_name.
    let got_names: BTreeSet<String> = subs.iter().filter_map(|s| s.name.clone()).collect();
    for want in &expected_names {
        assert!(
            got_names.contains(want),
            "no DW_TAG_subprogram named {want:?} (an exported function); \
             got {got_names:?}"
        );
    }

    eprintln!(
        "[dbg394-oracleF] {} subprogram DIEs ({} func_N syms); exports {expected_names:?} \
         all present. sample: {:?}",
        subs.len(),
        func_sym_count,
        subs.iter()
            .take(5)
            .map(|s| format!("{:?} [0x{:x},0x{:x})", s.name, s.low_pc, s.high_pc))
            .collect::<Vec<_>>()
    );
}

/// The function-names subsection of the input wasm's `name` custom section —
/// full function index (imports first) → developer-facing name. Ground truth
/// for Oracle G, derived from the fixture at runtime (non-circular: read with
/// wasmparser directly, not through synth's decoder).
fn wasm_name_section_func_names(wasm: &[u8]) -> HashMap<u32, String> {
    use wasmparser::{KnownCustom, Parser, Payload};
    let mut out = HashMap::new();
    for payload in Parser::new(0).parse_all(wasm) {
        if let Ok(Payload::CustomSection(c)) = payload
            && let KnownCustom::Name(reader) = c.as_known()
        {
            for subsection in reader.into_iter().flatten() {
                if let wasmparser::Name::Function(map) = subsection {
                    for naming in map.into_iter().flatten() {
                        out.insert(naming.index, naming.name.to_string());
                    }
                }
            }
        }
    }
    out
}

/// ORACLE G — Tier-1.x REAL names for INTERNAL functions (#394 follow-up).
/// Oracle F proves exported functions get their export name; but an internal
/// (non-exported) callee — a panic helper, an outlined kernel routine — fell
/// back to the synthetic `func_N`, even when the input's `name` custom section
/// carried its real developer-facing name. A backtrace through a panic then
/// showed `func_7` instead of `core::panicking::panic_const::...`. This oracle
/// proves the `name`-section names are threaded through to the
/// `DW_TAG_subprogram` `DW_AT_name`s:
///
///   (a) ≥1 compiled function is INTERNAL (not exported) AND named by the
///       fixture's `name` section — otherwise the oracle would be vacuous;
///   (b) every such internal function's subprogram DIE carries its REAL
///       `name`-section name (e.g. `gale::msgq::put_decide::h...`);
///   (c) since the fixture's `name` section names EVERY function, NO
///       subprogram is left with a synthetic `func_N` name.
///
/// Ground truth (name section + export section) is parsed from the fixture at
/// runtime with wasmparser directly — independent of synth's decoder.
#[test]
fn emitted_subprogram_names_use_name_section_for_internal_functions_394() {
    let wasm = repro("msgq_put_359.wasm");
    let wasm_bytes = std::fs::read(&wasm).expect("read fixture wasm");
    let name_map = wasm_name_section_func_names(&wasm_bytes);
    assert!(
        !name_map.is_empty(),
        "fixture must carry a `name` custom section with function names \
         (otherwise this oracle tests nothing — pick a different fixture)"
    );
    let exported = wasm_exported_func_names(&wasm_bytes);

    // The real names of the fixture's INTERNAL (non-exported) functions.
    let internal_names: BTreeSet<String> = name_map
        .values()
        .filter(|n| !exported.contains(*n))
        .cloned()
        .collect();
    assert!(
        !internal_names.is_empty(),
        "fixture must have ≥1 internal function named by its `name` section"
    );

    let dbg = compile(&wasm, "/tmp/dbg394_msgq_oracleg.o", true);
    let subs = collect_subprograms(&section_data(&dbg));
    let got_names: BTreeSet<String> = subs.iter().filter_map(|s| s.name.clone()).collect();

    // (a)+(b): ≥1 compiled subprogram is an internal function carrying its
    // REAL `name`-section name. (Not every internal function need be compiled
    // — reachability/skips can drop some — but the fixture's export calls an
    // internal helper, so at least one must be present under its real name.)
    let internal_present: Vec<&String> = internal_names.intersection(&got_names).collect();
    assert!(
        !internal_present.is_empty(),
        "no DW_TAG_subprogram carries an internal function's `name`-section \
         name; internal names in fixture: {internal_names:?}, subprogram names: \
         {got_names:?} — internal functions are still falling back to `func_N`"
    );

    // (c) the fixture's `name` section names EVERY function, so no compiled
    // function may be left with the synthetic `func_N` fallback.
    let synthetic: Vec<&String> = got_names
        .iter()
        .filter(|n| {
            n.strip_prefix("func_")
                .is_some_and(|d| !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit()))
        })
        .collect();
    assert!(
        synthetic.is_empty(),
        "the fixture's `name` section names every function, yet {} subprogram \
         DIE(s) still carry the synthetic fallback: {synthetic:?}",
        synthetic.len()
    );

    eprintln!(
        "[dbg394-oracleG] {} subprogram DIEs; internal `name`-section names \
         present: {internal_present:?}; zero synthetic func_N names remain.",
        subs.len()
    );
}

/// The root `DW_TAG_compile_unit`'s `[low_pc, high_pc)`, walked the debugger way.
/// On an ET_REL object `DW_AT_low_pc` reads as the in-place addend (object-
/// relative `.text` offset, 0); `DW_AT_high_pc` is a constant-class value, i.e.
/// the DWARF offset-from-low_pc form, so `high_pc = low_pc + offset`.
fn compile_unit_range(secs: &HashMap<String, Vec<u8>>) -> (u64, u64) {
    let empty: &[u8] = &[];
    let load = |id: SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
        let data = secs.get(id.name()).map_or(empty, |v| v.as_slice());
        Ok(EndianSlice::new(data, LittleEndian))
    };
    let dwarf = gimli::Dwarf::load(load).expect("load emitted .debug_* sections");
    let mut units = dwarf.units();
    while let Some(header) = units.next().expect("unit header") {
        let unit = dwarf.unit(header).expect("unit");
        let mut entries = unit.entries();
        while let Some(entry) = entries.next_dfs().expect("dfs") {
            if entry.tag() != gimli::DW_TAG_compile_unit {
                continue;
            }
            let low_pc = match entry.attr_value(gimli::DW_AT_low_pc) {
                Some(gimli::AttributeValue::Addr(a)) => a,
                other => panic!("CU DW_AT_low_pc must be an Addr, got {other:?}"),
            };
            let size = match entry.attr_value(gimli::DW_AT_high_pc) {
                Some(gimli::AttributeValue::Udata(n)) => n,
                other => panic!("CU DW_AT_high_pc must be Udata (offset form), got {other:?}"),
            };
            return (low_pc, low_pc + size);
        }
    }
    panic!("no DW_TAG_compile_unit DIE in emitted .debug_info");
}

/// ORACLE H — CU/subprogram range CONTAINMENT (#564). The DWARF parent/child
/// containment rule `llvm-dwarfdump --verify` enforces post-link: every child
/// `DW_TAG_subprogram`'s `[low_pc, high_pc)` must lie INSIDE the compile_unit's
/// `[low_pc, high_pc)`. Before this fix the CU's `DW_AT_high_pc` was derived
/// from the LINE-TABLE extent (last mapped address + 1) while the subprogram
/// DIEs (#557) carry true CODE extents — so the last function, whose code
/// always extends past its last line-mapped instruction (the mapped op itself
/// is ≥2 bytes, plus any unmapped epilogue/literal-pool tail), fell OUTSIDE its
/// parent's range. llvm-dwarfdump then reports "DIE address ranges are not
/// contained in its parent's ranges" on the linked image, and a debugger
/// walking CUs by PC range misses that function entirely. Checked in-tree with
/// gimli::read — no llvm needed.
#[test]
fn compile_unit_range_contains_every_subprogram_564() {
    let wasm = repro("msgq_put_359.wasm");
    let dbg = compile(&wasm, "/tmp/dbg394_msgq_oracleh.o", true);
    let secs = section_data(&dbg);

    let (cu_low, cu_high) = compile_unit_range(&secs);
    let subs = collect_subprograms(&secs);
    assert!(
        !subs.is_empty(),
        "fixture must emit ≥1 DW_TAG_subprogram to anchor the containment check"
    );

    // Fixture-shape guard (non-vacuity, the exact #564 shape): at least one
    // function's CODE extends past the line-table extent (last mapped address
    // + 1). If this ever stops holding, the containment assertions below can
    // no longer distinguish line-table-extent from code-extent CU high_pc —
    // pick a fixture whose last function ends in unmapped instructions.
    let line_extent = line_rows(&secs)
        .iter()
        .map(|&(a, _)| a)
        .max()
        .expect("line table must have rows")
        + 1;
    let code_extent = subs.iter().map(|s| s.high_pc).max().unwrap();
    assert!(
        code_extent > line_extent,
        "fixture no longer exercises the #564 shape: max subprogram high_pc \
         0x{code_extent:x} must exceed the line-table extent 0x{line_extent:x}"
    );

    // The llvm-dwarfdump --verify containment rule.
    for s in &subs {
        assert!(
            cu_low <= s.low_pc && s.high_pc <= cu_high,
            "subprogram {:?} [0x{:x},0x{:x}) is NOT contained in its parent \
             compile_unit's range [0x{cu_low:x},0x{cu_high:x}) — the CU \
             DW_AT_high_pc is the line-table extent, not the code extent \
             (#564); llvm-dwarfdump --verify fails this post-link",
            s.name,
            s.low_pc,
            s.high_pc
        );
    }

    eprintln!(
        "[dbg394-oracleH] CU [0x{cu_low:x},0x{cu_high:x}) contains all {} \
         subprograms (code extent 0x{code_extent:x} > line extent 0x{line_extent:x})",
        subs.len()
    );
}

/// Locate an `llvm-dwarfdump` binary — the INDEPENDENT DWARF parser Oracle I
/// depends on. Search order: `LLVM_DWARFDUMP` env override, then `PATH`, then the
/// Xcode toolchain path (macOS dev hosts carry it there even when it's off PATH).
/// Returns the resolvable command name/path. Returns `None` only when no binary
/// is found anywhere — Oracle I turns that into a HARD FAILURE (never a skip), so
/// a CI host missing the tool is a red gate, not a silently-vacuous green one.
fn find_llvm_dwarfdump() -> Option<String> {
    // (1) explicit override.
    if let Ok(p) = std::env::var("LLVM_DWARFDUMP")
        && Command::new(&p)
            .arg("--version")
            .output()
            .is_ok_and(|o| o.status.success())
    {
        return Some(p);
    }
    // (2) PATH (ubuntu-latest CI installs `llvm`, which ships `llvm-dwarfdump`;
    // versioned names like `llvm-dwarfdump-18` are also common on apt images).
    let candidates = [
        "llvm-dwarfdump".to_string(),
        "llvm-dwarfdump-20".to_string(),
        "llvm-dwarfdump-19".to_string(),
        "llvm-dwarfdump-18".to_string(),
        "llvm-dwarfdump-17".to_string(),
        // (3) the macOS Xcode toolchain absolute path.
        "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.\
         xctoolchain/usr/bin/llvm-dwarfdump"
            .to_string(),
    ];
    candidates.into_iter().find(|c| {
        Command::new(c)
            .arg("--version")
            .output()
            .is_ok_and(|o| o.status.success())
    })
}

/// ORACLE I — INDEPENDENT-PARSER validation via `llvm-dwarfdump` (#394). Oracles
/// A–H parse synth's emitted DWARF with `gimli::read`, the SAME library
/// `gimli::write` produced the bytes with — so a self-consistent emitter bug
/// (an encoding gimli round-trips but real toolchains reject) passes them. This
/// oracle closes that gap: it runs the LLVM DWARF parser, a fully INDEPENDENT
/// implementation, against the emitted object and asserts
///
///   1. `llvm-dwarfdump --verify` reports NO errors — i.e. LLVM's structural
///      checks (unit-header chain, abbrev, `.debug_line`, and crucially the
///      parent/child PC-range CONTAINMENT that #564/Oracle H assert via gimli)
///      all pass. This is the exact check `llvm-dwarfdump --verify` runs post-link
///      on a real image, run here on the object.
///   2. `--debug-info` shows the CU DIE and ≥1 `DW_TAG_subprogram` with a
///      `DW_AT_name` and a `DW_AT_low_pc`/`DW_AT_high_pc` — LLVM successfully
///      decodes the DIE tree, not just accepts the bytes.
///   3. `--debug-line` decodes ≥1 line row (`Address … Line …`) — LLVM reaches
///      the line program via the CU's `DW_AT_stmt_list` and produces rows.
///
/// The tool is REQUIRED: if no `llvm-dwarfdump` is found the test FAILS (it never
/// skips), so this gate cannot silently go vacuous on a host that lacks it. CI
/// installs `llvm` in the Test job so the binary is always present.
#[test]
fn emitted_dwarf_verifies_with_llvm_dwarfdump_394() {
    let dwdump = find_llvm_dwarfdump().expect(
        "llvm-dwarfdump not found (checked $LLVM_DWARFDUMP, PATH, and the Xcode \
         toolchain). This independent-parser gate must not skip; install `llvm` \
         (ubuntu: `apt-get install -y llvm`) or set $LLVM_DWARFDUMP.",
    );

    let wasm = repro("msgq_put_359.wasm");
    let out = "/tmp/dbg394_msgq_oraclei.o";
    compile(&wasm, out, true);

    // (1) --verify must report no errors. Exit status is non-zero on failure and
    // the summary line prints "No errors." on success; assert both.
    let verify = Command::new(&dwdump)
        .args(["--verify", out])
        .output()
        .expect("run llvm-dwarfdump --verify");
    let vout = format!(
        "{}{}",
        String::from_utf8_lossy(&verify.stdout),
        String::from_utf8_lossy(&verify.stderr)
    );
    assert!(
        verify.status.success() && vout.contains("No errors"),
        "llvm-dwarfdump --verify rejected synth's emitted DWARF (independent \
         parser). status={:?}\noutput:\n{vout}",
        verify.status.code()
    );

    // (2) --debug-info must decode the CU + ≥1 subprogram DIE with a name and a
    // low_pc/high_pc, exactly as LLVM prints them.
    let info = Command::new(&dwdump)
        .args(["--debug-info", out])
        .output()
        .expect("run llvm-dwarfdump --debug-info");
    let iout = String::from_utf8_lossy(&info.stdout);
    assert!(
        info.status.success(),
        "llvm-dwarfdump --debug-info failed: {}",
        String::from_utf8_lossy(&info.stderr)
    );
    assert!(
        iout.contains("DW_TAG_compile_unit"),
        "--debug-info has no DW_TAG_compile_unit:\n{iout}"
    );
    let subprogram_dies = iout.matches("DW_TAG_subprogram").count();
    assert!(
        subprogram_dies >= 1,
        "--debug-info decoded no DW_TAG_subprogram DIE; LLVM output:\n{iout}"
    );
    // The subprogram DIEs must carry the low_pc/high_pc range attributes LLVM
    // prints (proves the address attrs decode, not just the tag).
    assert!(
        iout.contains("DW_AT_low_pc") && iout.contains("DW_AT_high_pc"),
        "--debug-info subprogram/CU DIEs lack DW_AT_low_pc/DW_AT_high_pc:\n{iout}"
    );

    // (3) --debug-line must decode ≥1 line row. LLVM prints an "Address … Line …"
    // header then one row per mapped address; count the data rows (16-hex-digit
    // address lines) rather than the header.
    let line = Command::new(&dwdump)
        .args(["--debug-line", out])
        .output()
        .expect("run llvm-dwarfdump --debug-line");
    let lout = String::from_utf8_lossy(&line.stdout);
    assert!(
        line.status.success(),
        "llvm-dwarfdump --debug-line failed: {}",
        String::from_utf8_lossy(&line.stderr)
    );
    let line_rows = lout
        .lines()
        .filter(|l| {
            let t = l.trim_start();
            // A data row begins with a 0x-prefixed 16-hex-digit address.
            t.starts_with("0x") && t.len() >= 18 && t[2..18].bytes().all(|b| b.is_ascii_hexdigit())
        })
        .count();
    assert!(
        line_rows >= 1,
        "llvm-dwarfdump --debug-line decoded no line rows; output:\n{lout}"
    );

    eprintln!(
        "[dbg394-oracleI] llvm-dwarfdump --verify: No errors; --debug-info \
         decoded {subprogram_dies} subprogram DIE(s); --debug-line decoded \
         {line_rows} row(s). Independent parser accepts synth's emitted DWARF."
    );
}
