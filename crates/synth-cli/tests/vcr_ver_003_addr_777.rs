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
