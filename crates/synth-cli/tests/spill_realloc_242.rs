//! VCR-RA-001 spill re-choice spike (#242) — CI-gated no-grow + firing +
//! headroom-report oracles.
//!
//! flat_flight's hot segment runs peak register pressure 11 > the R0–R8 pool
//! of 9, so every pressure-guarded optimization declines there and the greedy
//! lowering's spill placement is naive (gale: 17 spills + 61% redundant const
//! materializations on silicon, #209). This spike ships, flag-off:
//!
//!   - `SYNTH_SPILL_REALLOC=1` — slot-value forwarding BETWEEN reloads
//!     (`liveness::apply_spill_realloc`): the case `forward_stack_reloads`
//!     misses when pressure clobbers the spill store's source. 1-for-1 or
//!     deletion ⇒ never grows; per-segment pressure gate.
//!   - `SYNTH_SPILL_REPORT=1` — measure-only greedy-vs-Belady (farthest next
//!     use) frame-traffic report per segment: the recovery headroom the full
//!     VCR-RA-001 spill-choice rewrite targets.
//!
//! Flag-OFF byte-identity is owned by the existing gates (frozen_codegen_bytes
//! 3/3 + the const_cse_reduction_242 golden). Flag-ON semantic equivalence is
//! the unicorn-vs-wasmtime differentials (const_cse_differential.py,
//! frame_slot_dce_differential.py — both re-run green with the flag exported).
//! What THIS file locks:
//!
//!   1. NO-GROW: with the flag ON, no function in the measured corpus grows.
//!   2. NON-VACUOUS: the rewrite actually fires on a real fixture
//!      (flight_seam::flight_algo — 3 reloads forwarded, 306→300 B when
//!      measured 2026-07-02) — an inert pass cannot pass this.
//!   3. HONESTY: flat_flight stays byte-equal (its 3 surviving reloads have no
//!      register-resident holder — spill RE-CHOICE, not forwarding, is what
//!      recovers those; that is the next VCR-RA-001 step, not this one).
//!   4. HEADROOM IS REAL: the Belady report on flat_flight's pressure-11
//!      segment shows the ideal allocation needs strictly less frame traffic
//!      than the greedy lowering emitted.

use std::collections::HashMap;
use std::path::Path;
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture(rel: &str) -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(rel)
}

/// Compile `rel` on the optimized path; `flag` toggles `SYNTH_SPILL_REALLOC`.
/// Returns (ELF bytes, stderr).
fn compile(rel: &str, out: &str, flag: bool) -> (Vec<u8>, String) {
    let mut cmd = Command::new(synth());
    if flag {
        cmd.env("SYNTH_SPILL_REALLOC", "1");
    }
    let output = cmd
        .env("SYNTH_SPILL_REPORT", "1")
        .env("SYNTH_FUSE_STATS", "1")
        .args([
            "compile",
            fixture(rel).to_str().unwrap(),
            "-o",
            out,
            "-b",
            "arm",
            "--target",
            "cortex-m4",
            "--all-exports",
        ])
        .output()
        .expect("run synth compile");
    assert!(output.status.success(), "synth compile failed ({rel})");
    (
        std::fs::read(out).expect("read ELF"),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// Every function symbol → its `.text` byte size.
fn func_sizes(elf: &[u8]) -> HashMap<String, usize> {
    use object::{Object, ObjectSymbol, SymbolKind};
    let obj = object::read::elf::ElfFile32::<object::Endianness>::parse(elf).expect("parse ELF");
    let mut out = HashMap::new();
    for sym in obj.symbols() {
        if sym.kind() == SymbolKind::Text
            && sym.size() > 0
            && let Ok(name) = sym.name()
        {
            out.insert(name.to_string(), sym.size() as usize);
        }
    }
    out
}

/// One parsed `[spill-report]` line.
#[derive(Debug)]
struct SegReport {
    peak: usize,
    actual_reloads: usize,
    actual_stores: usize,
    belady_reloads: usize,
    belady_stores: usize,
}

/// Parse `[spill-report] seg@S len=L peak=P actual=Ald+Bst belady(k=9)=Cld+Dst`.
fn parse_reports(stderr: &str) -> Vec<SegReport> {
    fn lead_digits(s: &str) -> usize {
        let d: String = s.chars().take_while(|c| c.is_ascii_digit()).collect();
        d.parse().expect("leading digits")
    }
    fn after<'a>(line: &'a str, field: &str) -> &'a str {
        line.split(field)
            .nth(1)
            .unwrap_or_else(|| panic!("cannot parse `{field}` from: {line}"))
    }
    stderr
        .lines()
        .filter(|l| l.contains("[spill-report]"))
        .map(|l| {
            let actual = after(l, "actual=");
            let belady = after(l, "belady(k=9)=");
            SegReport {
                peak: lead_digits(after(l, "peak=")),
                actual_reloads: lead_digits(actual),
                actual_stores: lead_digits(after(actual, "ld+")),
                belady_reloads: lead_digits(belady),
                belady_stores: lead_digits(after(belady, "ld+")),
            }
        })
        .collect()
}

/// Sum of `[spill-realloc] N reload(s) forwarded/eliminated…` counts.
fn forwarded_total(stderr: &str) -> usize {
    stderr
        .lines()
        .filter(|l| l.contains("[spill-realloc]"))
        .map(|l| {
            l.split("[spill-realloc] ")
                .nth(1)
                .and_then(|r| {
                    let d: String = r.chars().take_while(|c| c.is_ascii_digit()).collect();
                    d.parse::<usize>().ok()
                })
                .unwrap_or_else(|| panic!("cannot parse [spill-realloc] line: {l}"))
        })
        .sum()
}

/// CLAIMS 1–3: no function grows flag-on; the rewrite fires on flight_seam's
/// flight_algo (which shrinks); pressure-saturated flat_flight honestly stays
/// byte-equal (nothing forwardable — re-choice, not forwarding, owns it).
#[test]
fn spill_realloc_no_grow_and_fires_on_flight_seam_242() {
    // flight_seam — the firing fixture.
    let (off_elf, _) = compile(
        "scripts/repro/flight_seam.wat",
        "/tmp/sr242_fs_off.elf",
        false,
    );
    let (on_elf, on_err) = compile(
        "scripts/repro/flight_seam.wat",
        "/tmp/sr242_fs_on.elf",
        true,
    );
    let (off, on) = (func_sizes(&off_elf), func_sizes(&on_elf));
    for (name, &o) in &off {
        let n = *on.get(name).unwrap_or(&o);
        assert!(
            n <= o,
            "no function may grow flag-on: {name} off={o}B on={n}B"
        );
    }
    assert!(
        on["flight_algo"] < off["flight_algo"],
        "the spike must shrink flight_seam::flight_algo (measured 306→300 B): off={}B on={}B",
        off["flight_algo"],
        on["flight_algo"]
    );
    let fired = forwarded_total(&on_err);
    assert!(
        fired >= 3,
        "expected ≥3 reloads forwarded on flight_seam (measured 3); got {fired} — the pass went inert"
    );
    eprintln!(
        "[spill-realloc-242] flight_seam::flight_algo off={}B on={}B, {} reload(s) forwarded",
        off["flight_algo"], on["flight_algo"], fired
    );

    // flat_flight — the honest non-firing fixture (holders all clobbered).
    let (ff_off_elf, _) = compile(
        "scripts/repro/flat_flight/flat_flight.loom.wasm",
        "/tmp/sr242_ff_off.elf",
        false,
    );
    let (ff_on_elf, _) = compile(
        "scripts/repro/flat_flight/flat_flight.loom.wasm",
        "/tmp/sr242_ff_on.elf",
        true,
    );
    assert_eq!(
        func_sizes(&ff_on_elf)["flat_flight"],
        func_sizes(&ff_off_elf)["flat_flight"],
        "flat_flight's surviving reloads have no register-resident holder; \
         forwarding must decline — recovering them is the spill RE-CHOICE step"
    );
}

/// CLAIM 4: the greedy-vs-Belady report is alive on flat_flight and shows real
/// recovery headroom on its pressure-saturated hot segment.
#[test]
fn spill_report_shows_flat_flight_headroom_242() {
    let (_, stderr) = compile(
        "scripts/repro/flat_flight/flat_flight.loom.wasm",
        "/tmp/sr242_ff_rep.elf",
        false,
    );
    let reports = parse_reports(&stderr);
    assert!(
        !reports.is_empty(),
        "no [spill-report] lines — the measure-only instrumentation went dead"
    );
    // The hot segment: peak pressure 11 > pool 9, with real frame traffic the
    // ideal (Belady, k=9) allocation would not need (measured 2026-07-02:
    // actual 3ld+3st vs belady 0ld+0st).
    let hot = reports
        .iter()
        .find(|r| r.peak > 9)
        .expect("flat_flight must report a peak>9 (pressure-saturated) segment");
    let (actual, ideal) = (
        hot.actual_reloads + hot.actual_stores,
        hot.belady_reloads + hot.belady_stores,
    );
    assert!(
        ideal < actual,
        "the pressure-11 segment must show recovery headroom: actual {actual} vs belady {ideal}"
    );
    eprintln!(
        "[spill-report-242] flat_flight hot segment: peak={} actual={}ld+{}st \
         belady(k=9)={}ld+{}st — the VCR-RA-001 recovery target",
        hot.peak, hot.actual_reloads, hot.actual_stores, hot.belady_reloads, hot.belady_stores
    );
}
