//! #468 base-CSE / const-address-fold — DEFAULT-ON flip gates (#242, the
//! SYNTH_SPILL_REALLOC-flip template).
//!
//! The lever: `optimizer_bridge::plan_base_cse` hoists the linear-memory base
//! into realloc-immune R11 once at entry and folds each single-use
//! const-address access to `[R11, #imm]`, dropping the per-access
//! `movw/movt` base re-materialization AND the dead address materialization.
//! It only activates on the narrow provably-profitable shape (every opcode
//! enumerated, ≥2 foldable accesses inside the imm12 window — anything else
//! declines the whole function), so on the 72-fixture corpus it fires on
//! exactly two fixtures and grows none.
//!
//! Execution differentials were re-run green on the new DEFAULT bytes BEFORE
//! these goldens were pinned (base_cse, volatile_segment_543, const_cse,
//! flight_seam, frame_slot_dce, spill_rung_581, control_step — see the flip
//! PR). What THIS file locks:
//!
//!   1. DEFAULT GOLDEN: the shipped default emits the folded `.text` on the
//!      two firing fixtures (pinned sha256 + length).
//!   2. ESCAPE HATCH: `SYNTH_BASE_CSE=0` restores the PRE-flip bytes
//!      byte-for-byte — the rollback proof and a tripwire against the planner
//!      leaking into the opt-out path. NOTE: pre-flip the gate was
//!      `is_ok()` (ANY value enabled it, including "0"); post-flip "0" is the
//!      documented opt-out, so these pre-flip goldens are the UNSET-env bytes
//!      of the pre-flip tree (captured on the parent commit).
//!   3. NO-GROW: across the measured corpus, no function grows
//!      default-vs-opt-out; the firing fixtures shrink (non-vacuity).
//!
//! The frozen `--relocatable` anchors (`frozen_codegen_bytes.rs`) are
//! untouched by construction: base-CSE lives only in the optimized path's
//! `ir_to_arm`. Semantic equivalence is `base_cse_differential.py` /
//! `volatile_segment_543_differential.py` (unicorn vs wasmtime).

use std::collections::HashMap;
use std::path::Path;
use std::process::Command;

use object::{Object, ObjectSection, ObjectSymbol, SymbolKind};
use sha2::{Digest, Sha256};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture(rel: &str) -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(rel)
}

/// Compile `rel` on the optimized ARM path. `default_on` = the shipped
/// default (env vars removed so a stray opt-out in the test environment can't
/// skew the gate); `false` = the `SYNTH_BASE_CSE=0` opt-out (pre-flip bytes).
///
/// COMPOSITION NOTE (#242): const-CSE is default-ON since its own flip, so
/// rolling back to the pre-BASE-CSE-flip bytes now also requires
/// `SYNTH_CONST_CSE=0` on the opt-out arm (const-CSE would otherwise rewrite
/// the verbatim per-access materializations these goldens pin). The DEFAULT
/// arm leaves both env vars untouched — verified at const-CSE-flip time that
/// the default goldens below are byte-identical under const-CSE (its
/// size-guarded passes find nothing left on the folded shape), so this gate
/// keeps pinning the TRUE shipped default.
fn compile(rel: &str, out: &str, default_on: bool) -> Vec<u8> {
    let mut cmd = Command::new(synth());
    if default_on {
        cmd.env_remove("SYNTH_CONST_CSE");
        cmd.env_remove("SYNTH_BASE_CSE");
    } else {
        cmd.env("SYNTH_CONST_CSE", "0");
        cmd.env("SYNTH_BASE_CSE", "0");
    }
    let out_status = cmd
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
    assert!(
        out_status.status.success(),
        "synth compile failed ({rel}, default_on={default_on}): {}",
        String::from_utf8_lossy(&out_status.stderr)
    );
    std::fs::read(out).expect("read ELF")
}

fn text_bytes(elf: &[u8]) -> Vec<u8> {
    let obj = object::File::parse(elf).expect("parse ELF");
    obj.section_by_name(".text")
        .expect(".text present")
        .data()
        .expect("read .text")
        .to_vec()
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Every function symbol → its `.text` byte size.
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

/// (fixture, DEFAULT golden sha256, len, PRE-flip/opt-out golden sha256, len)
/// — the two corpus fixtures the planner fires on. Default goldens pinned
/// AFTER the execution differentials passed on the new default bytes;
/// opt-out goldens captured from the parent (pre-flip) commit's default.
///
/// CORRECTNESS RE-PIN (#499): the redundant_base_materialization opt-out
/// golden originally pinned MISCOMPILED bytes — the flag-off spill frame
/// (`sub sp,#24`) was never deallocated before `pop {…,pc}` (PC read from a
/// spill slot; base_cse_differential.py tolerated it as "known #499"). The
/// fix adds the `add sp,#24` teardown (+4 B) and, with a balanced epilogue,
/// frame-slot DCE now removes the dead spill stores the mis-paired `pop`
/// previously appeared to read (−20 B): 342 → 326 B. New opt-out bytes
/// execution-validated (spill_frame_499_differential.py +
/// base_cse_differential.py, unicorn vs wasmtime) before re-pinning.
const GOLDENS: [(&str, &str, usize, &str, usize); 2] = [
    (
        "scripts/repro/redundant_base_materialization.wat",
        "a0f684bcfaaece182b55fdb2e98b94d54bbeab72243764ff354ed67b79a56aef",
        224,
        "b44084bebcc57701b39510d365a7e066d62f9bfae5a6f93a7860fe6e87f90a05",
        326,
    ),
    (
        "scripts/repro/volatile_segment_543.wat",
        "86af859f443eaaddf01a2a99811b81a60c66b6fe4118b53ceea121511c88070b",
        194,
        "eb9c8355416778fba8bedc26d1cf672a6f0334d915492f5cdffd95381d7572f7",
        256,
    ),
];

/// GATES 1+2 — the shipped default emits the folded bytes; `SYNTH_BASE_CSE=0`
/// restores the pre-flip bytes byte-for-byte (rollback proof).
#[test]
fn base_cse_escape_hatch_restores_old_bytes_468() {
    for &(rel, on_sha, on_len, off_sha, off_len) in &GOLDENS {
        let tag = Path::new(rel).file_stem().unwrap().to_str().unwrap();
        let on = text_bytes(&compile(rel, &format!("/tmp/bcse468_{tag}_on.elf"), true));
        assert_eq!(
            (on.len(), sha256_hex(&on).as_str()),
            (on_len, on_sha),
            "{rel}: shipped DEFAULT .text drifted from the flip golden"
        );
        let off = text_bytes(&compile(rel, &format!("/tmp/bcse468_{tag}_off.elf"), false));
        assert_eq!(
            (off.len(), sha256_hex(&off).as_str()),
            (off_len, off_sha),
            "{rel}: SYNTH_BASE_CSE=0 must restore the pre-flip bytes (rollback broken)"
        );
    }
}

/// GATE 3 — NO-GROW + non-vacuity: across the measured corpus no function
/// grows default-vs-opt-out, and the two firing fixtures genuinely shrink
/// (redundant_base_materialization −118 B, volatile_segment_543 −62 B at
/// flip time). Since the #242 const-CSE flip the opt-out arm disables BOTH
/// levers (see `compile`), so this is a combined-default no-grow claim;
/// flat_flight / flight_seam / const_cse decline for the base-CSE planner
/// (control flow / non-const addresses) but may shrink under const-CSE —
/// per-lever equality is pinned in each lever's own gate file.
#[test]
fn base_cse_no_grow_corpus_468() {
    let corpus = [
        "scripts/repro/redundant_base_materialization.wat",
        "scripts/repro/volatile_segment_543.wat",
        "scripts/repro/base_cse_branch.wat",
        "scripts/repro/const_cse.wat",
        "scripts/repro/flight_seam.wat",
        "scripts/repro/flat_flight/flat_flight.loom.wasm",
    ];
    let mut fired = 0usize;
    for rel in corpus {
        let tag = format!(
            "ng_{}",
            Path::new(rel).file_stem().unwrap().to_str().unwrap()
        );
        let off = func_sizes(&compile(rel, &format!("/tmp/bcse468_{tag}_off.elf"), false));
        let on = func_sizes(&compile(rel, &format!("/tmp/bcse468_{tag}_on.elf"), true));
        for (name, &o) in &off {
            let n = *on.get(name).unwrap_or(&o);
            assert!(
                n <= o,
                "no function may grow under default base-CSE: {name} opt-out={o}B default={n}B ({rel})"
            );
            if n < o {
                fired += 1;
            }
        }
    }
    assert!(
        fired >= 2,
        "non-vacuity: base-CSE must shrink at least the two firing fixtures, saw {fired} shrinking function(s)"
    );
}
