//! VCR-PERF-001 Pass-1 spill-pressure baseline — CI-gated (#390, #242).
//!
//! gale #390 measured the gust hot-path size gap (gust_poll 816 B / 240 insns vs
//! 208 B / 104 native) and attributed the HEADLINE (~47%) to "Pass 1 — NO
//! register allocation: every wasm local/operand spilled to a stack slot". The
//! in-tree mechanism that reproduces this on synth's OWN frozen kernels was, until
//! now, only a shell script (`scripts/repro/spill_baseline_measure.sh`) — not run
//! in CI, so the baseline could silently drift. This promotes the load-bearing
//! claim into a CI-gated oracle.
//!
//! WHAT THIS LOCKS (and what it deliberately does NOT). It does NOT add
//! change-detection: the frozen differential hashes (control_step 0x00210A55 /
//! flat+inlined flight_algo 0x07FDF307 / divseam) already fail on any codegen byte
//! change, and value-pressure cannot move without codegen moving. Its value is to
//! lock, as an executable and continuously-verified claim, the INTERPRETATION
//! behind VCR-PERF-001 Pass-1:
//!
//!   On the frozen hot-path kernels, every function the shadow allocator measures
//!   has peak VALUE-pressure ≤ 9 (the R0–R8 pool). So the `[sp,#]` spills synth
//!   currently emits are SPURIOUS — an artifact of the frame-resident lowering
//!   model (local.get → ldr [sp]; local.set → str [sp]), NOT register pressure.
//!   A value-based SSA allocator (VCR-RA-001, today shadow-only behind
//!   SYNTH_SHADOW_ALLOC) eliminates them without adding spill code.
//!
//! That makes this the BEFORE-baseline the eventual allocator wiring must beat:
//! when VCR-RA-001 is wired, the spurious-spill count drops and this oracle's
//! "pressure ≤ 9" precondition is what proves the spills were eliminable, not
//! masked.
//!
//! FROZEN-SAFE BY CONSTRUCTION. `SYNTH_SHADOW_ALLOC=1` is measure-only,
//! side-effect-free instrumentation — it changes ZERO emitted bytes either way
//! (arm_backend.rs). The oracle drives the real `synth` binary (so it measures
//! exactly what ships, with no selector-config divergence) and reads synth's own
//! instrumentation — no external disassembler, CI-robust.

use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join(name)
}

/// The allocatable pool is R0–R8 (R9 globals / R10 mem-size / R11 mem-base /
/// R12 IP-scratch are reserved). Peak value-pressure ≤ this ⇒ a physical-register
/// spill is spurious (the function fits once virtually allocated).
const POOL_SIZE: usize = 9;

/// One parsed `[shadow-alloc]` verdict for a function.
#[derive(Debug)]
struct ShadowVerdict {
    /// Peak value-pressure, if the line reported one (`None` for "declined").
    peak: Option<usize>,
    /// True for "physical-graph would spill … but peak … spurious".
    spurious_spill: bool,
}

/// Run `synth compile` with the shadow allocator's measure-only instrumentation
/// on and parse every `[shadow-alloc]` verdict from stderr.
fn shadow_verdicts(wasm: &str) -> Vec<ShadowVerdict> {
    let path = fixture(wasm);
    let out = Command::new(synth())
        .env("SYNTH_SHADOW_ALLOC", "1")
        .args([
            "compile",
            path.to_str().unwrap(),
            "-o",
            &format!("/tmp/spillbase_{wasm}.elf"),
            "--target",
            "cortex-m4",
            "--all-exports",
            "--relocatable",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "synth compile failed for {wasm}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    stderr
        .lines()
        .filter(|l| l.contains("[shadow-alloc]"))
        .map(|l| ShadowVerdict {
            // Both verdict formats carry the peak: OK = "peak value-pressure N,";
            // NeedsSpill = "peak value-pressure is N (". "declined" carries none.
            peak: parse_peak(l),
            spurious_spill: l.contains("would spill") && l.contains("spurious"),
        })
        .collect()
}

/// Extract the integer after "peak value-pressure" (optionally "is"), if present.
fn parse_peak(line: &str) -> Option<usize> {
    let rest = line.split("peak value-pressure").nth(1)?;
    let rest = rest.trim_start();
    let rest = rest.strip_prefix("is ").unwrap_or(rest);
    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    digits.parse().ok()
}

/// THE ORACLE. For each frozen hot-path kernel: the instrumentation is alive
/// (non-empty), the parsed peak count is exactly what we locked (so a log-format
/// change fails LOUD rather than passing vacuously), and every reported peak is
/// within the R0–R8 pool. In aggregate, the spurious-spill waste is demonstrated.
#[test]
fn pass1_spills_are_spurious_pressure_fits_r0_r8_390() {
    // Locked baseline (debug binary, frozen fixtures, 2026-06-23): per fixture,
    // (expected shadow-alloc line count, expected peaks-parsed count). The line
    // count includes "declined" verdicts (which carry no peak), so peaks ≤ lines.
    // These are loud-failure guards: they move only when the frozen fixtures are
    // deliberately re-frozen (alongside the 0x00210A55 / 0x07FDF307 hashes).
    let cases = [
        ("flight_seam_flat.wasm", 3usize, 3usize),
        ("flight_seam.wasm", 3, 2),
        ("control_step.wasm", 1, 1),
    ];

    let mut total_peaks = 0usize;
    let mut total_spurious = 0usize;

    for (wasm, want_lines, want_peaks) in cases {
        let verdicts = shadow_verdicts(wasm);

        // (a) instrumentation alive — never pass vacuously on empty output.
        assert!(
            !verdicts.is_empty(),
            "{wasm}: no [shadow-alloc] verdicts — instrumentation produced nothing \
             (a measure-only regression, or the fixture failed to compile)"
        );

        // (b) locked line + peak counts — a format/decomposition change fails LOUD.
        assert_eq!(
            verdicts.len(),
            want_lines,
            "{wasm}: shadow-alloc line count changed ({} vs locked {want_lines}); \
             re-freeze the baseline iff the fixtures were deliberately re-frozen",
            verdicts.len()
        );
        let peaks: Vec<usize> = verdicts.iter().filter_map(|v| v.peak).collect();
        assert_eq!(
            peaks.len(),
            want_peaks,
            "{wasm}: parsed peak count changed ({} vs locked {want_peaks}); the \
             instrumentation log format likely changed — update parse_peak",
            peaks.len()
        );

        // (c) THE INVARIANT — every measured function fits the R0–R8 pool, so its
        // [sp,#] spills are spurious (eliminable by the value-based allocator).
        for (i, p) in peaks.iter().enumerate() {
            assert!(
                *p <= POOL_SIZE,
                "{wasm} fn#{i}: peak value-pressure {p} exceeds the R0–R8 pool \
                 ({POOL_SIZE}) — a spill here would be REAL, not spurious; the \
                 VCR-PERF-001 Pass-1 'spurious spills' premise no longer holds"
            );
        }

        total_peaks += peaks.len();
        total_spurious += verdicts.iter().filter(|v| v.spurious_spill).count();
    }

    // (d) the Pass-1 waste is real, in AGGREGATE (not every fixture exhibits a
    // spurious spill — flight_seam's top fn is "declined", calls/i64). At least
    // one frozen kernel must show a would-spill-but-spurious verdict, else the
    // "spills are spurious" claim has nothing to stand on.
    assert!(
        total_spurious >= 1,
        "expected ≥1 spurious physical-register spill across the frozen kernels \
         (the VCR-PERF-001 Pass-1 waste); found none"
    );
    // measured 2026-06-23: 6 peaks, 2 spurious. Keep a floor so the oracle cannot
    // pass on a collapsed measurement.
    assert!(
        total_peaks >= 6,
        "expected ≥6 measured functions across the suite; got {total_peaks}"
    );

    eprintln!(
        "[spill-baseline-390] {total_peaks} functions measured across 3 frozen \
         kernels; all peak value-pressure ≤ {POOL_SIZE} (R0–R8); {total_spurious} \
         spurious physical-register spills — the VCR-PERF-001 Pass-1 baseline the \
         value-based allocator (VCR-RA-001) must eliminate."
    );
}
