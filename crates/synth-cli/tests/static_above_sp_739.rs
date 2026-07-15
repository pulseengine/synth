//! #739 — static ABOVE `sp_init` must be RELOCATED (and thereby re-based by
//! the #678 `--shadow-stack-size` down-shift), never BAKED as an un-relocated
//! MOVW/MOVT linmem offset.
//!
//! A meld `--memory shared` fused node places component statics ABOVE the
//! shared SP (17-page linmem, SP init 0x100000, statics at 0x10000C+). The
//! wit-bindgen byte-copy shape — DYNAMIC index + static-region memarg offset
//! on a sub-word load/store — previously fell through to the raw
//! `[R11 + addr + #offset]` lowering, baking `movw ip,#0xC; movt ip,#0x10`
//! (no relocation). The reloc-walking #678 rebase never touched it, and the
//! reloc-walking post-link in-range oracle passed anyway (vacuous, the
//! #712-class lesson) → silent OOB on the shrunk reservation.
//!
//! Execution differential: `scripts/repro/static_above_sp_739_differential.py`
//! (unicorn vs wasmtime, `.bss`/`.data` at separate bases, R11 = 0).

use std::path::PathBuf;
use std::process::Command;

use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn repro(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join(name)
}

fn compile(fixture: &str, extra: &[&str], out: &str) -> std::process::Output {
    let fx = repro(fixture);
    let mut args = vec![
        "compile",
        fx.to_str().unwrap(),
        "--target",
        "cortex-m3",
        "--native-pointer-abi",
        "--all-exports",
        "--relocatable",
        "-o",
        out,
    ];
    args.extend_from_slice(extra);
    Command::new(synth())
        .args(&args)
        .output()
        .expect("run synth")
}

fn parse<'a>(bytes: &'a [u8]) -> object::File<'a> {
    object::File::parse(bytes).expect("parse ELF")
}

/// All in-place REL addends of `__synth_wasm_data` R_ARM_ABS32 relocs.
fn wasm_data_addends(path: &str) -> Vec<u32> {
    let bytes = std::fs::read(path).expect("read .o");
    let obj = parse(&bytes);
    let text = obj.section_by_name(".text").expect(".text");
    let text_data = text.data().expect("text data");
    let mut addends = Vec::new();
    for (off, reloc) in text.relocations() {
        if let RelocationTarget::Symbol(sidx) = reloc.target() {
            let sym = obj.symbol_by_index(sidx).expect("sym");
            if sym.name() == Ok("__synth_wasm_data") {
                let p = off as usize;
                addends.push(u32::from_le_bytes(text_data[p..p + 4].try_into().unwrap()));
            }
        }
    }
    addends
}

fn bss_size(path: &str) -> u64 {
    let bytes = std::fs::read(path).expect("read .o");
    let obj = parse(&bytes);
    obj.sections()
        .find(|s| s.name() == Ok(".bss"))
        .expect(".bss present")
        .size()
}

/// TRUE if `.text` contains an un-relocated MOVW/MOVT pair (same rd)
/// materializing a constant in `[lo, hi)` — the baked-offset signature the
/// #739 miscompile shipped (`movw ip,#0xC; movt ip,#0x10` = 0x10000C).
fn has_baked_pair_in_window(path: &str, lo: u32, hi: u32) -> bool {
    let bytes = std::fs::read(path).expect("read .o");
    let obj = parse(&bytes);
    let text = obj.section_by_name(".text").expect(".text");
    let code = text.data().expect("text data");
    let reloc_offsets: Vec<u64> = text.relocations().map(|(off, _)| off).collect();
    let imm16 = |off: usize| -> u32 {
        let hw1 = u16::from_le_bytes([code[off], code[off + 1]]) as u32;
        let hw2 = u16::from_le_bytes([code[off + 2], code[off + 3]]) as u32;
        ((hw1 & 0xF) << 12) | (((hw1 >> 10) & 1) << 11) | (((hw2 >> 12) & 0x7) << 8) | (hw2 & 0xFF)
    };
    let mut off = 0usize;
    while off + 8 <= code.len() {
        let hw1_w = u16::from_le_bytes([code[off], code[off + 1]]);
        let hw1_t = u16::from_le_bytes([code[off + 4], code[off + 5]]);
        let rd_w = (u16::from_le_bytes([code[off + 2], code[off + 3]]) >> 8) & 0xF;
        let rd_t = (u16::from_le_bytes([code[off + 6], code[off + 7]]) >> 8) & 0xF;
        if hw1_w & 0xFBF0 == 0xF240 && hw1_t & 0xFBF0 == 0xF2C0 && rd_w == rd_t {
            let k = (imm16(off + 4) << 16) | imm16(off);
            let covered = reloc_offsets
                .iter()
                .any(|&r| (r as usize) < off + 8 && off < (r + 4) as usize);
            if !covered && k >= lo && k < hi {
                return true;
            }
        }
        off += 2;
    }
    false
}

const SP_INIT: u32 = 1_048_576; // 0x100000
const LINMEM: u32 = 1_114_112; // 17 pages
const BSS_STATIC: u32 = 1_048_588; // 0x10000C, above sp_init
const BUDGET: u32 = 2048;

/// RED before the fix (the object carried ZERO relocations — the sub-word
/// accesses baked 0x10000C/0x100020 as plain MOVW/MOVT immediates and the
/// whole native-pointer region was silently dropped) / GREEN after: the
/// above-SP BSS static relocates as `__synth_wasm_data + 0x10000C` and the
/// #678 shrink down-shifts it to `budget + 12 = 2060`.
#[test]
fn above_sp_static_relocates_and_downshifts_739() {
    let out = compile(
        "mem739_above_sp.wat",
        &["--shadow-stack-size", "2048"],
        "/tmp/mem739_shrunk_test.o",
    );
    assert!(
        out.status.success(),
        "must compile: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let addends = wasm_data_addends("/tmp/mem739_shrunk_test.o");
    assert!(
        addends.contains(&(BUDGET + (BSS_STATIC - SP_INIT))),
        "above-SP static must down-shift to budget + 12 = 2060, got addends {addends:?}"
    );
    // Reservation = budget + above-SP tail — nowhere near the 1 MiB page.
    let bss = bss_size("/tmp/mem739_shrunk_test.o");
    assert!(
        (BUDGET as u64..=(BUDGET + 4096) as u64).contains(&bss),
        ".bss must be the shrunk reservation, got {bss}"
    );
    // The #739 signature itself: NO un-relocated MOVW/MOVT pair may
    // materialize a static-region address (post-shrink window starts at the
    // budget — anything at/above it is un-rebased).
    assert!(
        !has_baked_pair_in_window("/tmp/mem739_shrunk_test.o", BUDGET, LINMEM),
        "un-relocated baked static-region MOVW/MOVT pair survived the shrink"
    );
}

/// The relocation fix stands on its own (no shrink): the above-SP static must
/// be `__synth_wasm_data + 0x10000C`, never a baked immediate — a baked
/// absolute linmem offset mis-addresses as soon as the linker places the
/// region anywhere.
#[test]
fn above_sp_static_relocates_without_shrink_739() {
    let out = compile("mem739_above_sp.wat", &[], "/tmp/mem739_noshrink_test.o");
    assert!(
        out.status.success(),
        "must compile: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let addends = wasm_data_addends("/tmp/mem739_noshrink_test.o");
    assert!(
        addends.contains(&BSS_STATIC),
        "above-SP static must relocate as __synth_wasm_data + 0x10000C, got {addends:?}"
    );
    assert!(
        !has_baked_pair_in_window("/tmp/mem739_noshrink_test.o", SP_INIT, LINMEM),
        "un-relocated baked static-region MOVW/MOVT pair in the un-shrunk object"
    );
}

/// #739 flag-honesty: `--shadow-stack-size` on a module whose code never
/// references the native-pointer region (no `__synth_wasm_data` /
/// `__synth_globals` reloc) must refuse LOUDLY — pre-fix it was silently
/// ignored (no region, no shrink, no diagnostic).
#[test]
fn shadow_stack_size_without_region_refuses_739() {
    let out = compile(
        "mem739_no_static.wat",
        &["--shadow-stack-size", "2048"],
        "/tmp/mem739_no_static_test.o",
    );
    assert!(
        !out.status.success(),
        "--shadow-stack-size with no reservation must refuse, not silently no-op"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("#739") && stderr.contains("no reservation to shrink"),
        "refusal must name the hole: {stderr}"
    );
}

/// #746 (the #739 residual): i64 accesses with a static-region memarg offset
/// get the #744 relocation treatment. Pre-#746 this exact module DECLINED
/// loudly ("#739: i64.load ... not yet relocated") and nothing was emitted —
/// now the i64 arm relocates `__synth_wasm_data + 0x100008` and compiles.
#[test]
fn i64_static_offset_relocates_746() {
    let dir = std::env::temp_dir().join("mem746_i64_test");
    std::fs::create_dir_all(&dir).unwrap();
    let wat = dir.join("i64_above_sp.wat");
    std::fs::write(
        &wat,
        r#"(module
  (memory (export "memory") 17)
  (global $sp (mut i32) (i32.const 1048576))
  (func (export "run") (param i32) (result i32)
    local.get 0
    i64.load offset=1048584
    i32.wrap_i64))"#,
    )
    .unwrap();
    let obj = dir.join("i64_above_sp.o");
    let out = Command::new(synth())
        .args([
            "compile",
            wat.to_str().unwrap(),
            "--target",
            "cortex-m3",
            "--native-pointer-abi",
            "--all-exports",
            "--relocatable",
            "-o",
            obj.to_str().unwrap(),
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "i64 static-region access must compile (relocated, #746): {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let addends = wasm_data_addends(obj.to_str().unwrap());
    assert!(
        addends.contains(&1_048_584),
        "i64 static must relocate as __synth_wasm_data + 0x100008, got {addends:?}"
    );
    assert!(
        !has_baked_pair_in_window(obj.to_str().unwrap(), SP_INIT, LINMEM),
        "un-relocated baked static-region MOVW/MOVT pair in the i64 object"
    );
}

/// #746 end-to-end shrink: the i64 wide + narrow static-region accesses of
/// the differential fixture relocate AND down-shift under
/// `--shadow-stack-size` — BSS statics 0x100010/0x100018 become
/// `budget + 16 / + 24`, the reservation is the shrunk one, and no baked
/// MOVW/MOVT static-region pair survives. RED on v0.42.0: the compile itself
/// fails (all 7 functions loud-decline, nothing to emit).
#[test]
fn wide_static_relocates_and_downshifts_746() {
    let out = compile(
        "mem746_wide_static.wat",
        &["--shadow-stack-size", "2048"],
        "/tmp/mem746_shrunk_test.o",
    );
    assert!(
        out.status.success(),
        "must compile: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let addends = wasm_data_addends("/tmp/mem746_shrunk_test.o");
    for want in [BUDGET + 16, BUDGET + 24] {
        assert!(
            addends.contains(&want),
            "above-SP i64 static must down-shift to {want}, got addends {addends:?}"
        );
    }
    let bss = bss_size("/tmp/mem746_shrunk_test.o");
    assert!(
        (BUDGET as u64..=(BUDGET + 4096) as u64).contains(&bss),
        ".bss must be the shrunk reservation, got {bss}"
    );
    assert!(
        !has_baked_pair_in_window("/tmp/mem746_shrunk_test.o", BUDGET, LINMEM),
        "un-relocated baked static-region MOVW/MOVT pair survived the shrink"
    );
}
