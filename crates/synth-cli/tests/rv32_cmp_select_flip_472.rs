//! #472 RV32 cmp→select fusion — DEFAULT-ON flip gates (the RV32 lever
//! flip-wave; template = the ARM SYNTH_SPILL_REALLOC / SYNTH_BASE_CSE flips).
//!
//! The lever: the RV32 selector (VCR-SEL-004 port) deletes a comparison's
//! boolean materialization (`slt`/`xor+sltiu`/…) when the very next wasm op is
//! a `select` consuming that boolean, branching on the comparison directly
//! (`blt a, b` instead of `slt t, a, b; bne t, zero`). i64-operand selects
//! fuse too; i64 COMPARISONS decline (multi-word compare has no single fused
//! branch).
//!
//! Execution differentials were re-run green on the new DEFAULT bytes BEFORE
//! any golden was pinned (rv32_cmp_select_472, rv32_local_promotion_472,
//! if_else_result_343, i64_divs_317, control_step, signed_div_const — all
//! `*_riscv_differential.py`, unicorn vs wasmtime; see the flip PR). The
//! default golden + `SYNTH_RV_CMP_SELECT=0` escape hatch for the frozen RV32
//! anchors live in `frozen_codegen_bytes.rs`. What THIS file locks:
//!
//!   NO-GROW + non-vacuity: across the RV32-compiling repro corpus, no
//!   function grows default-vs-opt-out, and the firing fixtures genuinely
//!   shrink (control_step −12 B, the sel_* family −4/−8 B each, clamp −8 B
//!   at flip time).
//!
//! `SYNTH_RV_LOCAL_PROMO` (the wave's second lever) was HELD out of the wave
//! on a per-function no-grow blocker (its own WAR fixtures grew under the v1
//! access-count model: war_set 56→64 B, war_tee 60→68 B) and later flipped
//! default-on once profitability became MEASURED (#601; see
//! `rv32_local_promo_flip_472.rs`). This gate pins it OFF in both arms so it
//! keeps isolating the cmp→select lever against the same pre-promo baseline
//! it was frozen on.

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
/// `default_on` = the shipped default (env var removed so a stray opt-out in
/// the test environment can't skew the gate); `false` = the
/// `SYNTH_RV_CMP_SELECT=0` opt-out (pre-flip bytes).
fn compile(rel: &str, out: &str, default_on: bool) -> Vec<u8> {
    let mut cmd = Command::new(synth());
    // #601 promo flip: default-on now — pin OFF in both arms (see module doc).
    cmd.env("SYNTH_RV_LOCAL_PROMO", "0");
    // #242 flag-audit flip-wave: shift-fold is default-on; remove it so a
    // stray opt-out can't skew the cmp-select isolation (both arms fold).
    cmd.env_remove("SYNTH_RV_SHIFT_FOLD");
    if default_on {
        cmd.env_remove("SYNTH_RV_CMP_SELECT");
    } else {
        cmd.env("SYNTH_RV_CMP_SELECT", "0");
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
        "synth compile failed ({rel}, default_on={default_on}): {}",
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
/// grows default-vs-opt-out, and the fusion genuinely fires (≥2 functions
/// shrink — at flip time it was 14: control_step_decide, clamp, sel_i64 and
/// the eleven fusible sel_* wrappers). signed_div_const / if_else_result /
/// i64_divs / the local-promotion WAR fixtures are fusion-inert or
/// decline-shaped — they must stay EQUAL.
#[test]
fn rv32_cmp_select_no_grow_corpus_472() {
    let corpus = [
        "control_step.wasm",
        "signed_div_const.wasm",
        "rv32_cmp_select_472.wat",
        "rv32_local_promotion_472.wat",
        "if_else_result_343.wat",
        "i64_divs_317.wat",
    ];
    let mut fired = 0usize;
    for rel in corpus {
        let tag = Path::new(rel).file_stem().unwrap().to_str().unwrap();
        let off = func_sizes(&compile(rel, &format!("/tmp/rvcs472_{tag}_off.o"), false));
        let on = func_sizes(&compile(rel, &format!("/tmp/rvcs472_{tag}_on.o"), true));
        for (name, &o) in &off {
            let n = *on.get(name).unwrap_or(&o);
            assert!(
                n <= o,
                "no function may grow under default RV32 cmp→select: \
                 {name} opt-out={o}B default={n}B ({rel})"
            );
            if n < o {
                fired += 1;
            }
        }
    }
    assert!(
        fired >= 2,
        "non-vacuity: RV32 cmp→select must shrink the firing fixtures, \
         saw {fired} shrinking function(s)"
    );
}
