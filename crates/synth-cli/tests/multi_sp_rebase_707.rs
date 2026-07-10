//! VCR-MEM-001 (#707) — co-rebase N aliased `__stack_pointer` globals.
//!
//! A `meld fuse --memory shared` multi-provider node keeps each fused component's
//! own `__stack_pointer` global, so the module carries N mutable i32 globals ALL
//! initialized to the same stack top (sp_init). They alias the ONE shared
//! reservation. Layer-1 (#383) re-based the *unique* global whose `init ==
//! sp_init` and REFUSED when more than one matched ("could not uniquely identify
//! the shadow-stack global"). That refusal gated the gust:os multi-provider OS
//! node (app + time-provider + log-provider = 3 SP globals, all init 0x100000).
//!
//! #707 re-bases the whole equivalence class: every mutable global with `init ==
//! sp_init` slides to the shrunk budget (they point into the same stack). A
//! single-SP module has exactly one match, so this is byte-identical there — the
//! #383 tests still pin that path. The execution differential
//! (`scripts/repro/multi_sp_707_differential.py`) confirms each co-rebased stack
//! roundtrips correctly and restores its own slot to the budget; gale's on-silicon
//! reflash on the real fused node is the final gate.

use std::path::PathBuf;
use std::process::Command;

use object::{Object, ObjectSection};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/mem707_multi_sp.wat")
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

fn bss_size(path: &str) -> u64 {
    let data = std::fs::read(path).expect("read .o");
    let obj = object::File::parse(&*data).expect("parse ELF");
    obj.sections()
        .find(|s| s.name() == Ok(".bss"))
        .expect(".bss present")
        .size()
}

/// The materialized global slots in `.data`, decoded as little-endian i32 words.
/// The fixture has three mutable SP globals + one immutable constant ⇒ four
/// 4-byte slots (slots 0..2 = sp0/sp1/sp2, slot 3 = the immutable `$konst`).
fn global_slots(path: &str) -> Vec<i32> {
    let bytes = std::fs::read(path).expect("read .o");
    let obj = object::File::parse(&*bytes).expect("parse ELF");
    let data = obj
        .section_by_name(".data")
        .expect(".data present")
        .data()
        .expect(".data bytes");
    data.chunks_exact(4)
        .map(|w| i32::from_le_bytes(w.try_into().unwrap()))
        .collect()
}

/// RED before the fix / GREEN after: the fused node with THREE `__stack_pointer`
/// globals (all init 4096) was refused ("could not uniquely identify"); #707
/// co-rebases all three to the budget and shrinks the reservation.
#[test]
fn all_aliased_sp_globals_rebase_707() {
    let out = compile(&["--shadow-stack-size", "512"], "/tmp/mem707_test.o");
    assert!(
        out.status.success(),
        "#707: the 3-SP fused node must now COMPILE (was refused): {}",
        String::from_utf8_lossy(&out.stderr)
    );
    // Every MUTABLE global whose init == sp_init (the three SP globals) re-bases
    // to 512; the immutable `$konst` (slot 3) — which merely COINCIDES with
    // sp_init — must stay 4096. Re-basing it would corrupt a program constant.
    assert_eq!(
        global_slots("/tmp/mem707_test.o"),
        vec![512, 512, 512, 4096],
        "the three mutable SP globals co-rebase; the immutable constant is untouched"
    );
    // Reservation shrinks 4096 → budget 512 (no static tail above sp_init).
    assert_eq!(bss_size("/tmp/mem707_test.o"), 512);
}

/// Opt-in / frozen-safe: WITHOUT the flag the same node keeps all three SP slots
/// at their declared top and the full reservation (byte-identical to pre-#707).
#[test]
fn no_flag_leaves_multi_sp_full_707() {
    let out = compile(&[], "/tmp/mem707_noflag_test.o");
    assert!(out.status.success());
    assert_eq!(
        global_slots("/tmp/mem707_noflag_test.o"),
        vec![4096, 4096, 4096, 4096],
        "no flag must leave every slot at its declared value"
    );
    assert_eq!(bss_size("/tmp/mem707_noflag_test.o"), 4096);
}
