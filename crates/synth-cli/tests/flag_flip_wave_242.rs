//! #242 flag-audit flip-wave — per-flag NO-GROW corpus gates for the three
//! levers flipped default-on together (template: the SYNTH_RV_CMP_SELECT /
//! SYNTH_CONST_CSE flip gates):
//!
//!   - `SYNTH_RV_SHIFT_FOLD` (RV32, #472/#242): constant shift amounts fold
//!     into `slli/srli/srai`, dropping the `li tmp, N`. gale re-measured it
//!     still flag-off and worth −8 B toward the esp32c3 128 B floor (#242,
//!     2026-07-03) — a prior lane believed a v0.11.x fold covered this; that
//!     was the ARM `SYNTH_NO_IMM_SHIFT_FOLD` lever, a different flag. TRUE
//!     prior default: OFF (`is_some()` opt-in).
//!   - `SYNTH_DEAD_FRAME_ELIM` (ARM, VCR-RA-002 #390, #592 audit): elide the
//!     provably-dead `sub sp,#N`/`add sp,#N` frame. TRUE prior default: OFF.
//!   - `SYNTH_UXTH_FOLD` (ARM, #428, #592 audit): `movw #0xffff; and` →
//!     `uxth` (and the 0xff/uxtb form). TRUE prior default: OFF.
//!
//! Execution differentials were re-run green on the new DEFAULT bytes BEFORE
//! any golden was pinned (shift_fold_riscv 21/21, leaf_dead_frame, uxth_fold,
//! control_step 13/13 + control_step_riscv, flight_seam 0x07FDF307,
//! frame_slot_dce 8/8 — the full scripts/repro sweep, 52+3/56 PASS with
//! sret_decide a pre-existing flip-neutral harness discrepancy; see the flip
//! PR). The default goldens + per-flag `=0` escape hatches live in
//! `frozen_codegen_bytes.rs`. What THIS file locks, per flag:
//!
//!   NO-GROW + non-vacuity: across the measured repro corpus (BOTH ARM paths
//!   for the ARM levers — optimized and `--relocatable`/direct — since the
//!   passes are path-agnostic post-passes in `compile_wasm_to_arm`), no
//!   function grows default-vs-opt-out, and the firing fixtures genuinely
//!   shrink. Flip-time full-corpus numbers: shift-fold 0 grow / 20 shrink
//!   (control_step −8, flat_flight −36); dead-frame 0 grow / 58 shrink
//!   (controller_step −8, filter_step −12); uxth 0 grow / 13 shrink
//!   (control_step_decide −6, pack −12). The combined sweep was exactly
//!   additive (71 = 58 + 13): no lever interaction.
//!
//! The #601 local-promo precedent applies: had ANY function grown, the flag
//! would have been HELD with the numbers documented at the flag site (as
//! `SYNTH_RV_LOCAL_PROMO` was, until its measured-profitability fix flipped
//! it default-on — see `rv32_local_promo_flip_472.rs`).

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

/// Compile `rel` with `flag` either at the shipped default (env removed so a
/// stray opt-out in the test environment can't skew the gate) or the `=0`
/// opt-out (pre-flip bytes). `backend_args` selects ARM path / RV32.
fn compile(rel: &str, out: &str, flag: &str, default_on: bool, backend_args: &[&str]) -> Vec<u8> {
    let mut cmd = Command::new(synth());
    // #601 promo flip: local promotion is default-on now; pin it OFF in both
    // arms so this gate keeps isolating its own lever against the same
    // pre-promo baseline it was frozen on (the flip has its own gate in
    // `rv32_local_promo_flip_472.rs`).
    cmd.env("SYNTH_RV_LOCAL_PROMO", "0");
    if default_on {
        cmd.env_remove(flag);
    } else {
        cmd.env(flag, "0");
    }
    let out_status = cmd
        .args(["compile", fixture(rel).to_str().unwrap(), "-o", out])
        .args(backend_args)
        .args(["--all-exports"])
        .output()
        .expect("run synth compile");
    assert!(
        out_status.status.success(),
        "synth compile failed ({rel}, {flag} default_on={default_on}): {}",
        String::from_utf8_lossy(&out_status.stderr)
    );
    std::fs::read(out).expect("read ELF")
}

/// Every function symbol → its `.text` byte size (ELF symtab, not disasm
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

/// NO-GROW + non-vacuity for one flag over `corpus × configs`: no function may
/// grow default-vs-opt-out, and at least `min_fired` functions must shrink.
fn assert_no_grow(flag: &str, corpus: &[&str], configs: &[(&str, &[&str])], min_fired: usize) {
    let mut fired = 0usize;
    for rel in corpus {
        let tag = Path::new(rel).file_stem().unwrap().to_str().unwrap();
        for (mode, args) in configs {
            let off = func_sizes(&compile(
                rel,
                &format!("/tmp/ffw242_{flag}_{tag}_{mode}_off.o"),
                flag,
                false,
                args,
            ));
            let on = func_sizes(&compile(
                rel,
                &format!("/tmp/ffw242_{flag}_{tag}_{mode}_on.o"),
                flag,
                true,
                args,
            ));
            for (name, &o) in &off {
                let n = *on.get(name).unwrap_or(&o);
                assert!(
                    n <= o,
                    "no function may grow under default {flag}: \
                     {name} opt-out={o}B default={n}B ({rel} [{mode}])"
                );
                if n < o {
                    fired += 1;
                }
            }
        }
    }
    assert!(
        fired >= min_fired,
        "non-vacuity: {flag} must shrink its firing fixtures \
         (expected ≥{min_fired}, saw {fired} shrinking function(s))"
    );
}

const ARM_OPT: &[&str] = &["-b", "arm", "--target", "cortex-m4"];
const ARM_RELOC: &[&str] = &["-b", "arm", "--target", "cortex-m4", "--relocatable"];
const RV32: &[&str] = &["-b", "riscv", "--target", "rv32imac", "--relocatable"];

/// `SYNTH_RV_SHIFT_FOLD` — RV32 corpus. At flip time: 6 fixtures here held 9
/// shrinking functions (shift_fold.wat's five imm-shift wrappers −4 each,
/// control_step −8 — gale's exact esp32c3 number, flight_seam_flat's
/// controller_step/flight_algo −36 each, call_6_7args −20/−24);
/// signed_div_const and the variable-shift `shlvar` are fold-inert — they
/// must stay EQUAL.
#[test]
fn rv32_shift_fold_no_grow_corpus_242() {
    assert_no_grow(
        "SYNTH_RV_SHIFT_FOLD",
        &[
            "control_step.wasm",
            "signed_div_const.wasm",
            "shift_fold.wat",
            "flight_seam_flat.wasm",
            "call_6_7args.wat",
            "rv32_cmp_select_472.wat",
        ],
        &[("rv32", RV32)],
        2,
    );
}

/// `SYNTH_DEAD_FRAME_ELIM` — ARM corpus, BOTH paths (the elision is a
/// path-agnostic post-pass). At flip time: flight_seam's
/// controller_step/filter_step (−8/−12), native_pointer frame_roundtrip
/// (−12), leaf_caller_saved leaf3 (−8), memcopy writer (−12);
/// control_step / signed_div_const / uxth_fold are frame-inert — EQUAL.
#[test]
fn dead_frame_elim_no_grow_corpus_242() {
    assert_no_grow(
        "SYNTH_DEAD_FRAME_ELIM",
        &[
            "control_step.wasm",
            "signed_div_const.wasm",
            "flight_seam.wat",
            "native_pointer_shadow_stack.wat",
            "leaf_caller_saved.wat",
            "memcopy_dropped_359.wat",
            "uxth_fold.wat",
        ],
        &[("opt", ARM_OPT), ("reloc", ARM_RELOC)],
        2,
    );
}

/// `SYNTH_UXTH_FOLD` — ARM corpus, BOTH paths. At flip time: uxth_fold.wat's
/// pack (−12: two folds), control_step_decide (−6), gust_kernel's gust_mix
/// family (−6 each); flight_seam / signed_div_const have no 0xffff/0xff mask
/// materializations — EQUAL.
#[test]
fn uxth_fold_no_grow_corpus_242() {
    assert_no_grow(
        "SYNTH_UXTH_FOLD",
        &[
            "control_step.wasm",
            "signed_div_const.wasm",
            "uxth_fold.wat",
            "gust_kernel.wasm",
            "flight_seam.wat",
        ],
        &[("opt", ARM_OPT), ("reloc", ARM_RELOC)],
        2,
    );
}
