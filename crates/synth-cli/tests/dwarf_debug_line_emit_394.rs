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

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use gimli::{EndianSlice, LittleEndian, SectionId};
use object::read::elf::ElfFile32;
use object::{Object, ObjectSection};

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
