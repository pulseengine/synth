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

/// RV32 class: the single-base scheme (s11, zeroed RAM) ships NO initializer
/// image, so a module with NONZERO active data is a silent-drop risk — the
/// (unconditional) zero-served-image validator must WARN LOUDLY. It is a
/// warning, not a hard error: the CI-pinned RV32 frozen fixture
/// (control_step.wasm) freezes compile-success on this path; the hard decline
/// + initializer shipping is the named follow-up.
#[test]
fn rv32_nonzero_data_segment_warns_loudly() {
    let wat = r#"(module
  (memory 1)
  (data (i32.const 16) "\01\02\03\04")
  (func (export "get") (result i32) i32.const 16 i32.load))"#;
    let fixture = wat_file("rv32_data_777.wat", wat);
    let out = compile(&fixture, "rv32_data_777.o", &["-b", "riscv"]);
    // The warn! goes to stdout (tracing's default writer); scan both streams.
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out.status.success(), "RV32 compile stays green:\n{all}");
    assert!(
        all.contains("VCR-VER-003") && all.contains("read as 0x00"),
        "nonzero dropped initializers must warn loudly:\n{all}"
    );
}

/// RV32 non-vacuity: an all-zero runtime image (here a nonzero segment
/// OVERWRITTEN to zero by a later one — later-wins, not a bytes-grep) IS
/// served correctly by zeroed RAM, so the validator must stay silent.
#[test]
fn rv32_zero_overwritten_data_stays_silent() {
    let wat = r#"(module
  (memory 1)
  (data (i32.const 16) "\01\02\03\04")
  (data (i32.const 16) "\00\00\00\00")
  (func (export "get") (result i32) i32.const 16 i32.load))"#;
    let fixture = wat_file("rv32_zero_777.wat", wat);
    let out = compile(&fixture, "rv32_zero_777.o", &["-b", "riscv"]);
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out.status.success(), "RV32 compile stays green:\n{all}");
    assert!(
        !all.contains("VCR-VER-003"),
        "zeroed RAM serves the all-zero runtime image — no warning:\n{all}"
    );
}
