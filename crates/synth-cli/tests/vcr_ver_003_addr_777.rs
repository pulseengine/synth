//! VCR-VER-003 (#777 / #757) — the static-data addressing validator is wired
//! UNCONDITIONALLY into the mixed-split reloc path (`main.rs`, default
//! `--features riscv` build, no `verify` feature). It proves every retargeted
//! static-data relocation resolves to the runtime-correct byte (active data
//! segments applied in declaration order, later-wins).
//!
//! This is the DURABLE end-to-end tripwire for the #757 miscompile. gale's real
//! fused `gust:os` node (`scripts/repro/mem757_gale/loom.wasm`) declares three
//! active segments all at linmem `0x100000`; the string lives in the last
//! (`seg_2`) but a `.position()` (first-match) retargeting bound its reads to
//! `seg_0`'s stale consts. Because the validator now runs on every compile, this
//! test goes RED precisely when someone reverts the fix (`main.rs`
//! `.rposition()`→`.position()`) — that regression was demonstrated by hand in
//! the VCR-VER-003 PR (compile errored `func 9 reloc @ 0x250 __synth_wasm_seg_0
//! +0x8 serves 0x02 but runtime owns 0x67`); this test makes the GREEN side
//! permanent so the regression cannot land silently.
//!
//! The synthetic 3-overlap DISCRIMINATION (RED on `.position()`, GREEN on
//! `.rposition()`, same validator) is a permanent unit test in
//! `synth_core::static_data_addr` (`red_on_first_match_green_on_last_match`);
//! keeping the REAL module here honours the "synthetic reconstructions were all
//! green — the real module must live in CI" lesson (#757 survived 7 synthetic
//! shapes).

use std::path::PathBuf;
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn repro(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join(name)
}

/// The real gale overlapping-segment module compiles cleanly: the addressing
/// validator passes because the shipped `.rposition()` resolves the overlap to
/// the last-declared owner. A regression to `.position()` makes this compile
/// FAIL (VCR-VER-003 hard-error), so this GREEN is the #757 regression gate.
#[test]
fn gale_overlapping_segments_compile_clean() {
    let fixture = repro("mem757_gale/loom.wasm");
    assert!(
        fixture.exists(),
        "missing gale fixture {}",
        fixture.display()
    );
    let out = std::env::temp_dir().join("vcr_ver_003_gale.o");
    let output = Command::new(synth())
        .args([
            "compile",
            fixture.to_str().unwrap(),
            "--target",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
            "--native-pointer-abi",
            "--shadow-stack-size",
            "2048",
            "-o",
            out.to_str().unwrap(),
        ])
        .output()
        .expect("run synth");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "gale module must compile clean under the shipped .rposition() \
         retargeting — VCR-VER-003 rejected it, which means the overlapping \
         segments resolved to the WRONG segment (the #757 miscompile has \
         regressed):\n{stderr}"
    );
    // Sanity: the validator must NOT have fired on the correct path.
    assert!(
        !stderr.contains("VCR-VER-003"),
        "VCR-VER-003 must be silent on the runtime-correct resolution:\n{stderr}"
    );
    assert!(out.exists(), "expected a relocatable .o output");
    let _ = std::fs::remove_file(&out);
}

// ---------------------------------------------------------------------------
// Phase 2 (#777 follow-ups): span class, self-contained ROM image, RV32.
// ---------------------------------------------------------------------------

/// Write an inline wat to a temp file and return its path.
fn wat_file(name: &str, wat: &str) -> PathBuf {
    let dir = std::env::temp_dir().join("synth_vcr_ver_003_ph2");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let p = dir.join(name);
    std::fs::write(&p, wat).expect("write wat");
    p
}

fn compile(input: &std::path::Path, out_name: &str, extra: &[&str]) -> std::process::Output {
    let out = std::env::temp_dir()
        .join("synth_vcr_ver_003_ph2")
        .join(out_name);
    let mut args = vec![
        "compile",
        input.to_str().unwrap(),
        "--all-exports",
        "-o",
        out.to_str().unwrap(),
    ];
    args.extend_from_slice(extra);
    Command::new(synth())
        .args(&args)
        .output()
        .expect("run synth")
}

/// The span-class fixture: a STAGGERED overlap (seg_1 overwrites only seg_0's
/// tail) with an i32 load whose ADDEND byte is runtime-correct (owned by
/// seg_0) but whose 4-byte span crosses into seg_1's runtime-owned bytes —
/// the packed `__synth_wasm_seg_0` blob serves stale `a4 a5` where the
/// runtime image holds `b0 b1`. Phase 1 (addend byte only) accepted this and
/// emitted the miscompile (verified by hand on the v0.46 binary: compiles
/// clean, `.data` = seg_0's bytes verbatim). The load at 65542 straddles
/// 65544 where seg_1 takes over.
const SPAN_STRADDLE_WAT: &str = r#"(module
  (memory (export "memory") 2)
  (global $sp (mut i32) (i32.const 65536))
  (data (i32.const 65540) "\a0\a1\a2\a3\a4\a5\a6\a7")
  (data (i32.const 65544) "\b0\b1\b2\b3")
  (func (export "read_straddle") (result i32)
    i32.const 65542
    i32.load))"#;

/// PHASE-2 RED (span class): the straddling access is a genuine miscompile no
/// per-segment packing can serve (its bytes live in two non-adjacent packed
/// blobs), so the compile must FAIL LOUDLY with the span diagnostic — phase 1
/// shipped it silently.
#[test]
fn span_straddling_overlap_is_refused_on_the_mixed_split() {
    let fixture = wat_file("span_straddle_777.wat", SPAN_STRADDLE_WAT);
    let out = compile(
        &fixture,
        "span_straddle_777.o",
        &[
            "--target",
            "cortex-m3",
            "--native-pointer-abi",
            "--relocatable",
        ],
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success(),
        "the straddling stale-tail access MUST be refused (phase 1 silently \
         miscompiled it — the packed seg_0 serves a4a5 where the runtime \
         image owns b0b1):\nstderr: {stderr}"
    );
    assert!(
        stderr.contains("VCR-VER-003") && stderr.contains("span byte +2"),
        "the refusal must carry the span diagnostic:\n{stderr}"
    );
}

/// GREEN companion (same overlapping segments, non-straddling access): the
/// load at 65544 is owned by seg_1 and its span stays inside seg_1 + the
/// uncovered implicit-zero tail — the mixed split serves it correctly and the
/// module must keep compiling clean (the span check must not blanket-refuse
/// overlap shapes).
#[test]
fn span_owner_access_on_same_overlap_compiles_clean() {
    let wat = r#"(module
  (memory (export "memory") 2)
  (global $sp (mut i32) (i32.const 65536))
  (data (i32.const 65540) "\a0\a1\a2\a3\a4\a5\a6\a7")
  (data (i32.const 65544) "\b0\b1\b2\b3")
  (func (export "read_owner") (result i32)
    i32.const 65544
    i32.load))"#;
    let fixture = wat_file("span_owner_777.wat", wat);
    let out = compile(
        &fixture,
        "span_owner_777.o",
        &[
            "--target",
            "cortex-m3",
            "--native-pointer-abi",
            "--relocatable",
        ],
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "the correctly-owned access must compile clean:\n{stderr}"
    );
    assert!(
        !stderr.contains("VCR-VER-003"),
        "VCR-VER-003 must stay silent on the servable access:\n{stderr}"
    );
}

/// Self-contained twin (#758 ROM-copy class): the SAME straddling module is
/// correct on the self-contained path — the dense flash image (index = linmem
/// offset, later-wins fill) preserves adjacency and overlap, so the straddle
/// reads `a2 a3 b0 b1` exactly as WASM semantics demand. It must compile
/// clean with the (unconditional) dense-image validator silent. The red side
/// of this class is the permanent `rom_image_red_on_first_wins_green_on_last_wins`
/// unit gate in synth_core::static_data_addr (the overwrite policy is an
/// argument — phase 1's `resolve_owner` pattern).
#[test]
fn span_straddle_module_selfcontained_rom_image_validates() {
    let fixture = wat_file("span_straddle_777_sc.wat", SPAN_STRADDLE_WAT);
    let out = compile(
        &fixture,
        "span_straddle_777_sc.elf",
        &["--target", "cortex-m3"],
    );
    // tracing goes to stdout; hard errors to stderr — scan both.
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        out.status.success(),
        "the dense self-contained image serves the straddle correctly — must \
         compile clean:\n{all}"
    );
    assert!(
        !all.contains("VCR-VER-003"),
        "the dense-image validator must be silent on the correct pack:\n{all}"
    );
    // The #758 ROM image must actually be present (the validator ran on it).
    assert!(
        all.contains("#758 data ROM image"),
        "expected the #758 ROM-copy layout on this module:\n{all}"
    );
}

/// Read a named section's bytes out of an ELF object on disk.
fn section_bytes(path: &std::path::Path, name: &str) -> Option<Vec<u8>> {
    use object::{Object, ObjectSection};
    let bytes = std::fs::read(path).expect("read object");
    let obj = object::File::parse(&*bytes).expect("parse object");
    obj.section_by_name(name)
        .map(|s| s.data().expect("section data").to_vec())
}

/// RV32 class (#798, SHIPPED in v0.48): the single-base scheme used to ship a
/// `.text`-only object — nonzero active data was silently dropped (v0.47
/// warned loudly). Now the segments ship as `.wasm_data` records
/// ([u32 off][u32 len][bytes][pad4], declaration order) which the generated
/// startup copies to `__linear_memory_base + off` at reset. The compile is
/// GREEN, the old warning is GONE, and the object carries the exact record
/// bytes for the segment.
#[test]
fn rv32_nonzero_data_segment_ships_wasm_data_records() {
    let wat = r#"(module
  (memory 1)
  (data (i32.const 16) "\01\02\03\04")
  (func (export "get") (result i32) i32.const 16 i32.load))"#;
    let fixture = wat_file("rv32_data_777.wat", wat);
    let out_path = std::env::temp_dir()
        .join("synth_vcr_ver_003_ph2")
        .join("rv32_data_777.o");
    let out = compile(&fixture, "rv32_data_777.o", &["-b", "riscv"]);
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out.status.success(), "RV32 compile stays green:\n{all}");
    assert!(
        !all.contains("read as 0x00"),
        "the silent-drop warning must be gone — the data SHIPS now (#798):\n{all}"
    );
    assert!(
        all.contains("Shipping 1 wasm data segment(s)"),
        "the shipping info line names the segment count:\n{all}"
    );
    // The object carries the record verbatim: off=16, len=4, bytes 01020304.
    let records = section_bytes(&out_path, ".wasm_data")
        .expect("the object must ship a .wasm_data section");
    assert_eq!(
        records,
        [16u32.to_le_bytes(), 4u32.to_le_bytes()].concat().iter().copied()
            .chain([1u8, 2, 3, 4])
            .collect::<Vec<u8>>(),
        "record = [u32 off=16][u32 len=4][01 02 03 04]"
    );
}

/// RV32 later-wins (#798 + the #757 lesson): overlapping segments ship BOTH
/// records in declaration order — the startup's record-order copy leaves the
/// LAST-declared bytes in linear memory, exactly WASM instantiation
/// semantics. The read-back gate (validate_served_image over the emitted
/// blob) is green, so the compile succeeds with no VCR-VER-003 error.
#[test]
fn rv32_zero_overwritten_data_ships_both_records_in_order() {
    let wat = r#"(module
  (memory 1)
  (data (i32.const 16) "\01\02\03\04")
  (data (i32.const 16) "\00\00\00\00")
  (func (export "get") (result i32) i32.const 16 i32.load))"#;
    let fixture = wat_file("rv32_zero_777.wat", wat);
    let out_path = std::env::temp_dir()
        .join("synth_vcr_ver_003_ph2")
        .join("rv32_zero_777.o");
    let out = compile(&fixture, "rv32_zero_777.o", &["-b", "riscv"]);
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out.status.success(), "RV32 compile stays green:\n{all}");
    assert!(
        !all.contains("VCR-VER-003"),
        "the read-back gate must be silent on a correct pack:\n{all}"
    );
    let records = section_bytes(&out_path, ".wasm_data").expect(".wasm_data present");
    let mut expect = Vec::new();
    for seg in [[1u8, 2, 3, 4], [0u8, 0, 0, 0]] {
        expect.extend_from_slice(&16u32.to_le_bytes());
        expect.extend_from_slice(&4u32.to_le_bytes());
        expect.extend_from_slice(&seg);
    }
    assert_eq!(
        records, expect,
        "both records ship, declaration order (later-wins by copy order)"
    );
}

/// RV32 data-free modules ship NO `.wasm_data` section and stay byte-stable:
/// the empty-blob path is the pre-#798 layout exactly (the frozen RV32
/// fixtures without segments are untouched by construction — also unit-gated
/// in the ELF builder).
#[test]
fn rv32_data_free_module_has_no_wasm_data_section() {
    let wat = r#"(module
  (memory 1)
  (func (export "get") (result i32) i32.const 16 i32.load))"#;
    let fixture = wat_file("rv32_nodata_798.wat", wat);
    let out_path = std::env::temp_dir()
        .join("synth_vcr_ver_003_ph2")
        .join("rv32_nodata_798.o");
    let out = compile(&fixture, "rv32_nodata_798.o", &["-b", "riscv"]);
    assert!(out.status.success());
    assert!(
        section_bytes(&out_path, ".wasm_data").is_none(),
        "no segments => no .wasm_data section (byte-identical layout)"
    );
}

/// RV32 instantiation-trap guard (#798, #758 parity): a segment extending
/// past the declared linear memory can never be instantiated — refuse loudly
/// instead of shipping a layout whose startup copy would scribble past the
/// linear-memory window.
#[test]
fn rv32_segment_past_memory_is_refused() {
    let wat = r#"(module
  (memory 1)
  (data (i32.const 65534) "\01\02\03\04")
  (func (export "get") (result i32) i32.const 65534 i32.load))"#;
    let fixture = wat_file("rv32_oob_798.wat", wat);
    let out = compile(&fixture, "rv32_oob_798.o", &["-b", "riscv"]);
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        !out.status.success(),
        "segment past linear memory must be refused:\n{all}"
    );
    assert!(
        all.contains("instantiation would trap"),
        "the refusal names the reason:\n{all}"
    );
}
