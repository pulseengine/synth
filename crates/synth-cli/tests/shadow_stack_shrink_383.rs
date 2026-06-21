//! VCR-MEM-001 layer-1 (#383) — native-pointer shadow-stack reservation shrink.
//!
//! gale's gust kernel declares `(memory 17)` (≈1 MiB) for a tiny live footprint;
//! under `--native-pointer-abi` synth reserved the full [0, sp_init) page as a
//! NOBITS `.bss`, which an 8 KiB-RAM STM32F100 cannot place. `--shadow-stack-size
//! B` re-bases the SP global slot to B and shrinks the reservation to
//! `B + static-tail`, behind an OPT-IN flag (unset ⇒ full page ⇒ frozen fixtures
//! bit-identical, verified separately by cmp).
//!
//! These tests drive the real `synth` binary on the in-tree gust fixture and
//! assert the shrink fired (and the honest-refuse paths), so the behaviour is
//! regression-locked. gale's on-silicon reflash on this exact fixture is the
//! final gate (a relocatable .o's runtime correctness can't be asserted here).

use std::path::PathBuf;
use std::process::Command;

use object::{Object, ObjectSection};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

/// Size of the NOBITS `.bss` (the native-pointer linmem reservation) in a `.o`.
fn bss_size(path: &str) -> u64 {
    let data = std::fs::read(path).expect("read .o");
    let obj = object::File::parse(&*data).expect("parse ELF");
    obj.sections()
        .find(|s| s.name() == Ok(".bss"))
        .expect(".bss section present")
        .size()
}

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/gust_kernel.wasm")
}

fn compile(extra: &[&str], out: &str) -> std::process::Output {
    let fx = fixture();
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

/// With `--shadow-stack-size 4096` the reservation shrinks from the full
/// declared page (1048720) to B + the 144-byte static tail = 4240, and the SP
/// global slot is re-based 1048576 → 4096.
#[test]
fn shadow_stack_size_shrinks_gust_reservation_383() {
    let out = compile(&["--shadow-stack-size", "4096"], "/tmp/gust_shrink_383.o");
    assert!(
        out.status.success(),
        "compile failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    // B (4096) + the 144-byte static tail above sp_init = 4240 (vs the full
    // 1048720-byte declared page).
    assert_eq!(
        bss_size("/tmp/gust_shrink_383.o"),
        4240,
        "reservation should shrink to B + static-tail"
    );
}

/// WITHOUT the flag the reservation is untouched — no shrink, full page reserved
/// (the opt-in / frozen-safe contract).
#[test]
fn no_flag_leaves_reservation_full_383() {
    let out = compile(&[], "/tmp/gust_noshrink_383.o");
    assert!(out.status.success());
    // The full declared page stays reserved (opt-in / frozen-safe contract).
    assert_eq!(
        bss_size("/tmp/gust_noshrink_383.o"),
        1048720,
        "no flag must leave the full reservation"
    );
}

/// A budget larger than the declared shadow-stack top is refused honestly
/// (would enlarge, not shrink) — the typed-Err contract, never a silent no-op.
#[test]
fn budget_above_sp_init_refused_383() {
    let out = compile(&["--shadow-stack-size", "2000000"], "/tmp/gust_bad_383.o");
    assert!(
        !out.status.success(),
        "budget > sp_init must be refused, not accepted"
    );
    let log = String::from_utf8_lossy(&out.stderr);
    assert!(
        log.contains("exceeds the declared shadow-stack top"),
        "expected honest refuse message; got:\n{log}"
    );
}
