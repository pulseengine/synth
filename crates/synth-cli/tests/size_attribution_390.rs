//! #390 / VCR-PERF-001 — tracked size oracle for the gust hot path.
//!
//! gale measured synth v0.11.50 lowering the gust mini-RTOS scheduler hot path
//! at ~3.9x the code size of native rustc/LLVM (gust_poll 816 B vs 208 B;
//! gust_mix 44 B vs 12 B). The gap is almost entirely synth-side lowering. The
//! companion harness `scripts/repro/size_attribution_390.py` attributes synth's
//! OWN measured `.text` into named causal buckets (spill/reload, addressing-mode
//! folding misses, redundant const, prologue/shadow-stack, guard/bool, copy) —
//! the map the perf lanes (VCR-RA-001 et al.) follow. The attribution report is
//! `artifacts/size_attribution_390.md`.
//!
//! This test is the *gate*: it pins the exact per-function `.text` size of the
//! gust fixture on the DEFAULT (optimized) path — the path #390's numbers
//! describe. A size regression reddens CI; a size WIN reddens it too and forces
//! a deliberate pin update (the pin going DOWN is the visible evidence a perf
//! lane landed). The fuzzy bucket attribution deliberately does NOT enter this
//! gate — instruction->cause is a judgement call owned by the report, exact
//! bytes are the machine-checkable fact.
//!
//! Method: per-function size = delta between sorted `.text` symbol addresses
//! (next symbol / section end) — the same symtab the frozen-fixture
//! differentials read; `st_size` is not relied upon. Identical to the helper in
//! `shift_mask_elide_686.rs`.

use std::collections::BTreeMap;
use std::process::Command;

use object::{Object, ObjectSection, ObjectSymbol, SymbolKind};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/gust_kernel.wasm")
}

/// Compile gust_kernel on the DEFAULT optimized path (no `--relocatable`) and
/// return per-function `.text` sizes by symbol name (sorted-address deltas).
fn per_function_sizes() -> BTreeMap<String, u64> {
    let elf = "/tmp/size_attribution_390_gate.o";
    let out = Command::new(synth())
        .args([
            "compile",
            fixture().to_str().unwrap(),
            "-o",
            elf,
            "-b",
            "arm",
            "--target",
            "cortex-m4",
            "--all-exports",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "synth compile failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let bytes = std::fs::read(elf).expect("read elf");
    let obj = object::File::parse(&*bytes).expect("parse elf");
    let text = obj.section_by_name(".text").expect(".text");
    let end = text.address() + text.size();

    let mut starts: Vec<(u64, String)> = obj
        .symbols()
        .filter(|s| {
            !s.name().unwrap_or("").is_empty()
                && matches!(
                    s.kind(),
                    SymbolKind::Text | SymbolKind::Label | SymbolKind::Unknown
                )
                && s.address() >= text.address()
                && s.address() < end
        })
        .map(|s| (s.address(), s.name().unwrap().to_string()))
        .collect();
    starts.sort();
    starts.dedup_by(|a, b| a.0 == b.0); // aliases (func_N + export name) — keep one

    let mut sizes = BTreeMap::new();
    for (i, (addr, name)) in starts.iter().enumerate() {
        let next = starts.get(i + 1).map(|(a, _)| *a).unwrap_or(end);
        sizes.insert(name.clone(), next - addr);
    }
    sizes
}

/// Locked per-function `.text` sizes (bytes), default optimized path, synth
/// v0.39.1. Numbers are MEASURED (see `artifacts/size_attribution_390.md`).
/// gust_poll/gust_mix are gale's #390 benchmark functions; func_0 is the kiln
/// `transition` body, func_1 the internal `mix`. To repin after a deliberate
/// size change, run the test and copy the printed REPIN block.
const LOCKED: &[(&str, u64)] = &[
    ("gust_poll", 740),
    ("gust_mix", 32),
    ("func_0", 408),
    ("func_1", 76),
];

#[test]
fn gust_hot_path_text_size_is_pinned_390() {
    let sizes = per_function_sizes();

    // Print an easy-to-copy repin block for whoever lands a size change.
    let mut repin = String::from("\nREPIN (per-function .text bytes):\n");
    for (name, _) in LOCKED {
        let got = sizes.get(*name).copied().unwrap_or(0);
        repin.push_str(&format!("    (\"{name}\", {got}),\n"));
    }
    println!("{repin}");

    let mut mismatches = Vec::new();
    for (name, locked) in LOCKED {
        let got = sizes
            .get(*name)
            .copied()
            .unwrap_or_else(|| panic!("function {name} not found in .text (renamed/dropped?)"));
        if got != *locked {
            mismatches.push(format!(
                "  {name}: {got} B (locked {locked} B, delta {:+})",
                got as i64 - *locked as i64
            ));
        }
    }
    assert!(
        mismatches.is_empty(),
        "gust hot-path .text size changed — this is the #390 size gate.\n{}\n\
         If a perf lane INTENTIONALLY shrank these (a win!), or a change grew them, \
         update LOCKED (copy the REPIN block above) and regenerate the attribution \
         report:\n    SYNTH=$CARGO_TARGET_DIR/debug/synth \
         python3 scripts/repro/size_attribution_390.py --report",
        mismatches.join("\n")
    );
}
