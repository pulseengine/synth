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

// #977 RQ-59-FRESHNESS: nothing here parses an artifact until the artifact is
// proven to be THIS invocation's output — see `artifact_guard`.
mod artifact_guard;

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
    // #977: unique per call + remove-first + status/exists/non-empty guards.
    let out = artifact_guard::unique_artifact("vcr_ver_003_gale", "o");
    let mut cmd = Command::new(synth());
    cmd.args([
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
    ]);
    let (bytes, output) = artifact_guard::compile_artifact_with_output(&mut cmd, &out)
        .unwrap_or_else(|e| {
            panic!(
                "gale module must compile clean under the shipped .rposition() \
                 retargeting — VCR-VER-003 rejected it, which means the \
                 overlapping segments resolved to the WRONG segment (the #757 \
                 miscompile has regressed): {e}"
            )
        });
    let stderr = String::from_utf8_lossy(&output.stderr);
    // Sanity: the validator must NOT have fired on the correct path.
    assert!(
        !stderr.contains("VCR-VER-003"),
        "VCR-VER-003 must be silent on the runtime-correct resolution:\n{stderr}"
    );
    assert!(!bytes.is_empty(), "expected a relocatable .o output");
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

/// #977: the guarded READ-BACK form — compile and hand back the object bytes
/// proven to be this invocation's output (unique path + remove-first +
/// status/exists/non-empty via `artifact_guard`), plus combined stdout+stderr.
/// [`compile`] below stays for the tests that only assert on the process
/// output (refusals and validator diagnostics) and never read the artifact.
fn compile_read(input: &std::path::Path, tag: &str, extra: &[&str]) -> (Vec<u8>, String) {
    let out = artifact_guard::unique_artifact(tag, "o");
    let mut args = vec![
        "compile",
        input.to_str().unwrap(),
        "--all-exports",
        "-o",
        out.to_str().unwrap(),
    ];
    args.extend_from_slice(extra);
    let mut cmd = Command::new(synth());
    cmd.args(&args);
    match artifact_guard::compile_artifact_with_output(&mut cmd, &out) {
        Ok((bytes, output)) => {
            let _ = std::fs::remove_file(&out);
            let all = format!(
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            (bytes, all)
        }
        Err(e) => panic!("{tag}: {e}"),
    }
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
    // #1604: the selector's region-straddle guard now refuses this access
    // before VCR-VER-003 sees its relocation (the function is skipped, so no
    // reloc reaches the validator); VCR-VER-003's span check stays the
    // backstop, unit-tested in synth-core's static_data_addr.
    assert!(
        stderr.contains("(#1604)") && stderr.contains("[0x10006, 0x1000a)"),
        "the refusal must carry the #1604 region-straddle diagnostic:\n{stderr}"
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

/// Read a named section's bytes out of an ELF object already in memory
/// (#977: the bytes come from `compile_read`, never from a path a previous
/// run may have populated).
fn section_from_bytes(bytes: &[u8], name: &str) -> Option<Vec<u8>> {
    use object::{Object, ObjectSection};
    let obj = object::File::parse(bytes).expect("parse object");
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
    let (obj_bytes, all) = compile_read(&fixture, "rv32_data_777", &["-b", "riscv"]);
    assert!(
        !all.contains("read as 0x00"),
        "the silent-drop warning must be gone — the data SHIPS now (#798):\n{all}"
    );
    assert!(
        all.contains("Shipping 1 wasm data segment(s)"),
        "the shipping info line names the segment count:\n{all}"
    );
    // The object carries the record verbatim: off=16, len=4, bytes 01020304.
    let records = section_from_bytes(&obj_bytes, ".wasm_data")
        .expect("the object must ship a .wasm_data section");
    assert_eq!(
        records,
        [16u32.to_le_bytes(), 4u32.to_le_bytes()]
            .concat()
            .iter()
            .copied()
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
    let (obj_bytes, all) = compile_read(&fixture, "rv32_zero_777", &["-b", "riscv"]);
    assert!(
        !all.contains("VCR-VER-003"),
        "the read-back gate must be silent on a correct pack:\n{all}"
    );
    let records = section_from_bytes(&obj_bytes, ".wasm_data").expect(".wasm_data present");
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
    let (obj_bytes, _all) = compile_read(&fixture, "rv32_nodata_798", &["-b", "riscv"]);
    assert!(
        section_from_bytes(&obj_bytes, ".wasm_data").is_none(),
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

/// #977 RQ-59-FRESHNESS — the SILENT-direction demonstration for the
/// validator/attestation batch (vcr_ver_003_addr_777, proven_safe_bounds_901,
/// size_attribution_390, parity_benchmark_735,
/// promotion_exhaustion_fallback_474, wsc_facts_ingestion_494 — all now
/// compile through `artifact_guard`).
///
/// Prove the counterfactual: a planted VALID RV32 object (minted by this
/// file's own compile shape) parses and carries the `.wasm_data` section the
/// read-back gates assert on — so the pre-conversion path-based `fs::read` +
/// `File::parse` WOULD have re-confirmed last run's records as this run's
/// evidence. Then fail the compile at that path and require refusal AND an
/// empty path. For a validator gate a stale read is worse than a crash: it
/// re-certifies the served-image check on an object this run never produced.
#[test]
fn freshness_guard_refuses_stale_validator_artifact_977() {
    // 1. Mint a genuine object with this batch's own compile shape.
    let wat = r#"(module
  (memory 1)
  (data (i32.const 16) "\01\02\03\04")
  (func (export "get") (result i32) i32.const 16 i32.load))"#;
    let fixture = wat_file("freshness_demo_977.wat", wat);
    let (good, _all) = compile_read(&fixture, "freshness_demo_977", &["-b", "riscv"]);

    // 2. Plant it, and prove the OLD shape would have passed on it.
    let planted_at = artifact_guard::unique_artifact("vcr_ver_003_stale_planted", "o");
    std::fs::write(&planted_at, &good).expect("plant the stale artifact");
    let stale = std::fs::read(&planted_at).expect("read planted");
    assert!(
        section_from_bytes(&stale, ".wasm_data").is_some(),
        "the planted artifact must carry .wasm_data — substantial enough to \
         fool an unguarded read-back gate"
    );

    // 3. A FAILING compile aimed at that exact path (nonexistent input).
    let missing = std::env::temp_dir()
        .join("synth_vcr_ver_003_ph2")
        .join("does_not_exist_977.wat");
    let _ = std::fs::remove_file(&missing);
    let mut cmd = Command::new(synth());
    cmd.args([
        "compile",
        missing.to_str().unwrap(),
        "--all-exports",
        "-o",
        planted_at.to_str().unwrap(),
        "-b",
        "riscv",
    ]);
    let err = artifact_guard::compile_artifact(&mut cmd, &planted_at)
        .expect_err("REFUSAL REQUIRED: a failed compile must not return last run's bytes");

    // 4. The refusal names the compile, not the parser — and nothing is left.
    assert!(
        err.contains("synth compile FAILED"),
        "the refusal must name the compile failure, got: {err}"
    );
    assert!(
        !err.contains("file magic"),
        "and must not surface as a parse error, got: {err}"
    );
    assert!(
        !planted_at.exists(),
        "the stale artifact must be GONE — left in place, a later reader picks it up"
    );
}

// ---------------------------------------------------------------------------
// #1563: the span is each relocation's PROVEN access width, derived by the
// ARM backend from the final instruction stream. Before #1563 every reloc
// was spanned at 8 bytes.
// ---------------------------------------------------------------------------

/// Compile on the mixed split and return (success, stdout+stderr).
fn compile_1563(tag: &str, wat: &str) -> (bool, String) {
    let fixture = wat_file(&format!("{tag}_1563.wat"), wat);
    let out = compile(
        &fixture,
        &format!("{tag}_1563.o"),
        &[
            "--target",
            "cortex-m3",
            "--native-pointer-abi",
            "--relocatable",
        ],
    );
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (out.status.success(), all)
}

/// gale's meld-fused composite, reduced to its shape without gale's files:
/// a Rust constructor guard — `i32.load8_u` / `i32.store8` at linmem 0xe0c —
/// lives in a 1-byte segment that is declared AFTER the segment immediately
/// following it in linear memory (0xe10). The 1-byte accesses read and write
/// only the guard byte, which the packed guard segment serves correctly.
/// Before #1563 the 8-byte span read 0xe10.. from the guard's packed
/// neighbour and refused this correct image with 8 span errors (+4..+7 for
/// the load reloc and for the store reloc) — measured on the pre-fix binary.
const GALE_GUARD_1563_WAT: &str = r#"(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 1024))
  (data (i32.const 3600) "\01\02\03\04\05\06\07\08")
  (data (i32.const 3596) "\00")
  (func $ctor)
  (func (export "start")
    i32.const 0
    i32.load8_u offset=3596
    i32.eqz
    if
      i32.const 0
      i32.const 1
      i32.store8 offset=3596
      call $ctor
    end))"#;

#[test]
fn gale_1563_one_byte_guard_before_a_packed_neighbour_compiles_clean() {
    let (ok, all) = compile_1563("gale_guard", GALE_GUARD_1563_WAT);
    assert!(
        ok && !all.contains("VCR-VER-003"),
        "the 1-byte constructor guard is served correctly and must compile \
         clean (#1563 false positive):\n{all}"
    );
}

/// The staggered overlap every control below shares: seg_1 (declared later)
/// overwrites bytes +2,+3 of seg_0's range, so the packed seg_0 serves stale
/// `a2 a3` where the runtime image holds `b2 b3`.
fn staggered_1563(body: &str) -> String {
    format!(
        r#"(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 1024))
  (data (i32.const 2048) "\a0\a1\a2\a3\a4\a5\a6\a7")
  (data (i32.const 2050) "\b2\b3")
  (func (export "f") {body}))"#
    )
}

/// SOUNDNESS: every access that genuinely REACHES the overwritten bytes is
/// still refused, at its own proven width — this is what a "width forced to
/// 1" mutation turns green.
#[test]
fn width_1563_accesses_reaching_stale_bytes_are_refused_at_their_width() {
    for (tag, body, _vcr_ver_003_span) in [
        (
            "load32",
            "(result i32) i32.const 0 i32.load offset=2048",
            "span byte +2 of a 4-byte access",
        ),
        (
            "load16u",
            "(result i32) i32.const 0 i32.load16_u offset=2049",
            "span byte +1 of a 2-byte access",
        ),
        (
            "load16s",
            "(result i32) i32.const 0 i32.load16_s offset=2049",
            "span byte +1 of a 2-byte access",
        ),
        (
            "store32",
            "i32.const 0 i32.const 7 i32.store offset=2048",
            "span byte +2 of a 4-byte access",
        ),
        (
            "store16",
            "i32.const 0 i32.const 7 i32.store16 offset=2049",
            "span byte +1 of a 2-byte access",
        ),
    ] {
        // #1604: each of these spans seg_0's surviving bytes and seg_1's, so
        // the selector's region-straddle guard refuses it before VCR-VER-003
        // sees the relocation; the width it reports is the access's own.
        let (ok, all) = compile_1563(tag, &staggered_1563(body));
        assert!(
            !ok && all.contains("(#1604)") && all.contains("data segment 1 [0x802, 0x804)"),
            "{tag}: must be refused by the #1604 region-straddle guard:\n{all}"
        );
    }
}

/// The narrow accesses on the SAME geometry that stay inside the bytes their
/// segment really owns are correct and now compile (all were refused by the
/// 8-byte span before #1563).
#[test]
fn width_1563_narrow_accesses_inside_their_bytes_compile_clean() {
    for (tag, body) in [
        ("load8u", "(result i32) i32.const 0 i32.load8_u offset=2048"),
        ("load8s", "(result i32) i32.const 0 i32.load8_s offset=2049"),
        (
            "load8_owner",
            "(result i32) i32.const 0 i32.load8_u offset=2050",
        ),
        ("store8", "i32.const 0 i32.const 7 i32.store8 offset=2049"),
    ] {
        let (ok, all) = compile_1563(tag, &staggered_1563(body));
        assert!(
            ok && !all.contains("VCR-VER-003"),
            "{tag}: a 1-byte access inside its owner's bytes must compile:\n{all}"
        );
    }
}

/// SOUNDNESS, conservative side: where the width is NOT proven the 8-byte
/// span stays, and these shapes keep their pre-#1563 refusal — an i64 pair
/// access, a pointer `i32.const` used as an index register, a dynamic-index
/// access through `__synth_wasm_data + offset`, and a const address above
/// the selector's 0xFFF fold limit (lowered through the same dynamic path).
#[test]
fn width_1563_unproven_widths_stay_conservative() {
    let guard_geometry = |body: &str| {
        format!(
            r#"(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 1024))
  (data (i32.const 3600) "\01\02\03\04\05\06\07\08")
  (data (i32.const 3596) "\00")
  (func (export "f") {body}))"#
        )
    };
    for (tag, wat) in [
        (
            "load64",
            staggered_1563("(result i64) i32.const 0 i64.load offset=2048"),
        ),
        (
            "store64",
            staggered_1563("i32.const 0 i64.const 7 i64.store offset=2048"),
        ),
        (
            "ptr_index",
            guard_geometry("(result i32) i32.const 3596 i32.load8_u"),
        ),
        (
            "dynamic",
            guard_geometry("(param i32) (result i32) local.get 0 i32.load8_u offset=3596"),
        ),
        (
            "above_fold_limit",
            r#"(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 1024))
  (data (i32.const 8208) "\01\02\03\04\05\06\07\08")
  (data (i32.const 8204) "\00")
  (func (export "f") (result i32) i32.const 0 i32.load8_u offset=8204))"#
                .to_string(),
        ),
    ] {
        let (ok, all) = compile_1563(tag, &wat);
        // #1604: the two 8-byte accesses span both staggered segments, so the
        // selector's region-straddle guard refuses them first.
        let refused = if tag.ends_with("64") {
            all.contains("(#1604)")
        } else {
            all.contains("VCR-VER-003") && all.contains("width unproven")
        };
        assert!(
            !ok && refused,
            "{tag}: an unproven width must keep the conservative 8-byte span:\n{all}"
        );
    }
}

/// Straddle across two NON-overlapping segments: the 4-byte load at 0xe0c
/// reads `aa bb` from seg A and `cc dd` from seg B, which is declared EARLIER
/// and so is not A's packed neighbour. Refused at its proven width.
#[test]
fn width_1563_cross_segment_straddle_is_refused() {
    let wat = r#"(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 1024))
  (data (i32.const 3598) "\cc\dd")
  (data (i32.const 3596) "\aa\bb")
  (func (export "f") (result i32) i32.const 0 i32.load offset=3596))"#;
    let (ok, all) = compile_1563("straddle", wat);
    // #1604: refused by the selector's region-straddle guard, ahead of the
    // VCR-VER-003 span check that used to catch it.
    assert!(
        !ok && all.contains("(#1604)") && all.contains("[0xe0c, 0xe10)"),
        "the cross-segment straddle must be refused:\n{all}"
    );
}

/// A PROVEN width is checked against implicit-zero linear memory. The 4-byte
/// load at 2002 reads 2004/2005, which no segment covers (runtime 0x00), but
/// the packed blob serves the next declared segment's `05 06` there. The
/// pre-#1563 8-byte span SKIPPED uncovered bytes and compiled this silent
/// miscompile clean (measured on the pre-fix binary).
#[test]
fn width_1563_exact_width_refuses_packed_neighbour_in_implicit_zero_memory() {
    let wat = r#"(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 1024))
  (data (i32.const 2000) "\01\02\03\04")
  (data (i32.const 3000) "\05\06\07\08")
  (func (export "f") (result i32) i32.const 0 i32.load offset=2002))"#;
    let (ok, all) = compile_1563("implicit_zero", wat);
    // #1604: refused by the selector's region-straddle guard (segment ->
    // zero reservation), ahead of the VCR-VER-003 span check.
    assert!(
        !ok && all.contains("(#1604)")
            && all.contains("data segment 0 [0x7d0, 0x7d4) and the zero-initialised reservation"),
        "the 4-byte read of packed-neighbour bytes must be refused:\n{all}"
    );
}
