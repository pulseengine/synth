//! #472 RV32 local promotion — the per-function NO-GROW gate that HELD the
//! default-on flip out of the RV32 lever flip-wave (PR #601, epic #242).
//!
//! The lever: leaf functions' non-parameter i32 locals promoted into
//! callee-saved s-registers (s8/s9/s10) under `SYNTH_RV_LOCAL_PROMO`, so their
//! reads become free register aliases and the frame `lw`/`sw` traffic
//! disappears.
//!
//! Why the flip was HELD: the v1 profitability model ("≥2 accesses repay the
//! save/restore") under-charged — it priced neither the per-RETURN epilogue
//! restore (`preserve_callee_saved` duplicates the `lw s_i` restores into
//! EVERY `ret`) nor the WAR-snapshot `mv`s (`snapshot_aliases`). Small
//! functions with WAR writes or several returns grew net: war_set 56→64 B,
//! war_tee 60→68 B, control_step_decide 504→508 B (promo alone).
//!
//! The fix (this gate's counterpart in `synth-backend-riscv/src/selector.rs`):
//! the selector now MEASURES — it lowers the function with and without
//! promotion (and over every candidate subset) and keeps a promoted lowering
//! only when its emitted byte size is <= the unpromoted baseline. Every cost
//! (per-return restores, WAR `mv`s, zero-init, frame `addi` interactions) is
//! priced on the actual emitted sequence, not a side model — the #511
//! estimator-drift lesson.
//!
//! What THIS file locks, across the RV32-compiling repro corpus:
//!
//!   NO-GROW: for every function, text size(flag-on) <= text size(flag-off).
//!   NON-VACUITY: the lever genuinely fires (>=1 function shrinks — accum).
//!
//! This gate is the flip precondition: it was verified RED on the old model
//! (war_set/war_tee grew) before the measured decision landed.

use std::collections::HashMap;
use std::path::Path;
use std::process::Command;

use object::{Object, ObjectSymbol, SymbolKind};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture(rel: &str) -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join(rel)
}

/// Compile `rel` for RV32 exactly like the `.py` differentials do.
/// `promo_on` toggles ONLY `SYNTH_RV_LOCAL_PROMO`; every other lever env var
/// is removed so both arms run the shipped defaults and the gate isolates the
/// promotion lever.
fn compile(rel: &str, out: &str, promo_on: bool) -> Vec<u8> {
    let mut cmd = Command::new(synth());
    cmd.env_remove("SYNTH_RV_CMP_SELECT");
    cmd.env_remove("SYNTH_RV_SHIFT_FOLD");
    cmd.env_remove("SYNTH_RV_ADDR_FOLD");
    if promo_on {
        cmd.env("SYNTH_RV_LOCAL_PROMO", "1");
    } else {
        cmd.env_remove("SYNTH_RV_LOCAL_PROMO");
    }
    let out_status = cmd
        .args([
            "compile",
            fixture(rel).to_str().unwrap(),
            "-o",
            out,
            "-b",
            "riscv",
            "--target",
            "rv32imac",
            "--all-exports",
            "--relocatable",
        ])
        .output()
        .expect("run synth compile");
    assert!(
        out_status.status.success(),
        "synth compile failed ({rel}, promo_on={promo_on}): {}",
        String::from_utf8_lossy(&out_status.stderr)
    );
    std::fs::read(out).expect("read ELF")
}

/// Every function symbol → its `.text` byte size (ELF .symtab, not disasm
/// text — the disassembler is host-dependent).
fn func_sizes(elf: &[u8]) -> HashMap<String, usize> {
    let obj = object::File::parse(elf).expect("parse ELF");
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

/// NO-GROW + non-vacuity: across the RV32-compiling repro corpus no function
/// grows flag-on-vs-flag-off, the flag must not add or drop functions, and
/// the promotion genuinely fires (>=1 function shrinks — accum at minimum).
#[test]
fn rv32_local_promo_no_grow_corpus_472() {
    let corpus = [
        "control_step.wasm",
        "signed_div_const.wasm",
        "rv32_cmp_select_472.wat",
        "rv32_local_promotion_472.wat",
        "if_else_result_343.wat",
        "i64_divs_317.wat",
        "gust_kernel.wasm",
    ];
    let mut fired = 0usize;
    for rel in corpus {
        let tag = Path::new(rel).file_stem().unwrap().to_str().unwrap();
        let off = func_sizes(&compile(rel, &format!("/tmp/rvlp472_{tag}_off.o"), false));
        let on = func_sizes(&compile(rel, &format!("/tmp/rvlp472_{tag}_on.o"), true));
        // The flag may not change WHICH functions compile — a promoted-only
        // function would dodge the size comparison entirely.
        let mut off_names: Vec<&String> = off.keys().collect();
        let mut on_names: Vec<&String> = on.keys().collect();
        off_names.sort();
        on_names.sort();
        assert_eq!(
            off_names, on_names,
            "SYNTH_RV_LOCAL_PROMO must not change the compiled function set ({rel})"
        );
        for (name, &o) in &off {
            let n = on[name];
            assert!(
                n <= o,
                "no function may grow under RV32 local promotion: \
                 {name} flag-off={o}B flag-on={n}B ({rel})"
            );
            if n < o {
                fired += 1;
            }
        }
    }
    assert!(
        fired >= 1,
        "non-vacuity: RV32 local promotion must shrink at least one corpus \
         function (accum), saw {fired}"
    );
}
