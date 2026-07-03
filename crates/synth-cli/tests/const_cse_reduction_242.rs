//! VCR-RA const-CSE (#242) — flip gates: default golden, escape hatch,
//! reduction, and no-grow corpus.
//!
//! The ARM path re-materializes a constant at every use (`i32.const N` → a
//! fresh `movw`/`movt` each time). gale measured this on silicon: flat_flight
//! spends 61% of its const materializations on values already held in a
//! register. const-CSE removes the redundant materializations via the
//! post-hoc, liveness-proven `liveness::apply_const_cse` passes (PR1 #519
//! cross-register fold + PR2 #562 extending-alias hoist), wired LAST in
//! `arm_backend.rs` — DEFAULT-ON since the #242 flip; `SYNTH_CONST_CSE=0` is
//! the opt-out.
//!
//! FLIP PREREQUISITES — recorded here pre-flip, now RETIRED:
//!   - ALIAS-EVICTION: the bridge-level INLINE const cache (alias a repeated
//!     const's vreg to the register already holding it, in
//!     `optimizer_bridge::ir_to_arm`) made two live vregs share one physical
//!     register, breaking the spill model's vreg↔reg bijection — a spilled
//!     shared victim would leave the surviving alias reading a reused
//!     register. RETIRED BY DELETION (this flip's PR): the inline arm is gone;
//!     every const materializes normally and the flag gates ONLY the post-hoc
//!     passes, which rewrite already-register-assigned code (removal+retarget,
//!     never two-vregs-one-reg) — the eviction paths keep a `count == 1` alias
//!     guard as a structural tripwire.
//!   - reg_effect DEF-COMPLETENESS: the INLINE cache's "never stale-wrong"
//!     property rested on `liveness::reg_effect` reporting every GP-register
//!     write. Retired WITH the inline cache: the post-hoc passes treat any
//!     `reg_effect = None` op as an opaque segment boundary and only rewrite
//!     within fully-modeled straight-line segments, so an unmodeled op declines
//!     instead of going stale (per-op under-reporting remains an ordinary
//!     modeled-op bug class, pinned by the #513 consistency oracle + the
//!     execution differentials).
//!
//! Claims locked here as executable CI gates; semantic equivalence on the
//! default bytes is the separate `const_cse_differential.py`
//! unicorn-vs-wasmtime oracle (re-run green BEFORE these goldens were pinned):
//!
//!   1. ESCAPE HATCH (`=0` ≡ pre-flip baseline). With `SYNTH_CONST_CSE=0` the
//!      optimized path emits the SAME pinned `.text` the pre-flip default
//!      emitted (the golden survives the flip UNCHANGED from its pre-flip
//!      capture — the opt-out path is untouched). The rollback proof, and the
//!      ONLY gate pinning optimized-path opt-out bytes.
//!
//!   2. DEFAULT GOLDEN. The shipped default emits the CSE'd `.text` on the
//!      headroom fixture (pinned FNV + length), so an accidental change to the
//!      default lowering fails loud.
//!
//!   3. REAL REDUCTION ON HEADROOM + NO-GROW (below): `large3` and `spill12`
//!      strictly shrink under the default; nothing in the corpus grows.

use std::collections::HashMap;
use std::path::Path;
use std::process::Command;

use object::read::elf::ElfFile32;
use object::{Object, ObjectSection};

/// Golden FNV-1a-64 of the OPT-OUT (`SYNTH_CONST_CSE=0`) optimized-path `.text`
/// for `const_cse.wat`. Captured against the pre-const-CSE tree (stash-compare
/// verified) and UNCHANGED by the default-on flip — the opt-out path is the
/// pre-flip default. Re-bless ONLY when an intentional optimized-path lowering
/// change is made — a surprise failure here means the opt-out rollback drifted.
const GOLDEN_OFF_TEXT_FNV1A: u64 = 0xa68a_a2da_e5af_e4a7;
const GOLDEN_OFF_TEXT_LEN: usize = 576;

/// Golden FNV-1a-64 of the SHIPPED-DEFAULT optimized-path `.text` for
/// `const_cse.wat` (const-CSE on). Pinned at flip time, AFTER
/// `const_cse_differential.py` re-ran green on these exact bytes.
const GOLDEN_DEFAULT_TEXT_FNV1A: u64 = 0x9577_c583_bc14_5a46;
const GOLDEN_DEFAULT_TEXT_LEN: usize = 452;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/const_cse.wat")
}

/// Compile the const-CSE fixture via the optimized path. `cse = true` is the
/// SHIPPED DEFAULT (env removed so a stray opt-out can't skew a gate);
/// `cse = false` is the `SYNTH_CONST_CSE=0` opt-out. Returns the raw ELF bytes.
fn compile(out: &str, cse: bool) -> Vec<u8> {
    let mut cmd = Command::new(synth());
    if cse {
        cmd.env_remove("SYNTH_CONST_CSE");
    } else {
        cmd.env("SYNTH_CONST_CSE", "0");
    }
    let status = cmd
        .args([
            "compile",
            fixture().to_str().unwrap(),
            "-o",
            out,
            "-b",
            "arm",
            "--target",
            "cortex-m4",
            "--all-exports",
        ])
        .status()
        .expect("run synth compile");
    assert!(status.success(), "synth compile failed (cse={cse})");
    std::fs::read(out).expect("read ELF")
}

/// Map every named section to its bytes.
fn sections(elf: &[u8]) -> HashMap<String, Vec<u8>> {
    let obj = ElfFile32::<object::Endianness>::parse(elf).expect("parse ELF");
    let mut out = HashMap::new();
    for sec in obj.sections() {
        if let Ok(name) = sec.name()
            && !name.is_empty()
        {
            out.insert(name.to_string(), sec.data().unwrap_or(&[]).to_vec());
        }
    }
    out
}

/// `.text` bytes of one named function, by reading its symbol size.
fn func_text_len(elf: &[u8], name: &str) -> usize {
    use object::ObjectSymbol;
    let obj = ElfFile32::<object::Endianness>::parse(elf).expect("parse ELF");
    for sym in obj.symbols() {
        if sym.name() == Ok(name) {
            return sym.size() as usize;
        }
    }
    panic!("symbol {name} not found");
}

/// Compile an arbitrary repo-relative fixture via the optimized path.
/// `cse` semantics as in [`compile`]: `true` = shipped default, `false` = the
/// `=0` opt-out.
fn compile_fixture(rel: &str, out: &str, cse: bool) -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(rel);
    let mut cmd = Command::new(synth());
    if cse {
        cmd.env_remove("SYNTH_CONST_CSE");
    } else {
        cmd.env("SYNTH_CONST_CSE", "0");
    }
    let status = cmd
        .args([
            "compile",
            path.to_str().unwrap(),
            "-o",
            out,
            "-b",
            "arm",
            "--target",
            "cortex-m4",
            "--all-exports",
        ])
        .status()
        .expect("run synth compile");
    assert!(status.success(), "synth compile failed ({rel}, cse={cse})");
    std::fs::read(out).expect("read ELF")
}

/// Every function symbol → its `.text` byte size.
fn func_sizes(elf: &[u8]) -> HashMap<String, usize> {
    use object::{ObjectSymbol, SymbolKind};
    let obj = ElfFile32::<object::Endianness>::parse(elf).expect("parse ELF");
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

/// Compile a fixture opt-out (`=0`) and default (CSE on) and assert the PR2
/// (#242) win-recovery invariant: NO function grows under the default. Returns
/// `(off, on)` size maps for per-function asserts.
fn corpus_offon(rel: &str, tag: &str) -> (HashMap<String, usize>, HashMap<String, usize>) {
    let off = func_sizes(&compile_fixture(
        rel,
        &format!("/tmp/cse_{tag}_off.elf"),
        false,
    ));
    let on = func_sizes(&compile_fixture(
        rel,
        &format!("/tmp/cse_{tag}_on.elf"),
        true,
    ));
    for (name, &off_len) in &off {
        let on_len = *on.get(name).unwrap_or(&off_len);
        assert!(
            on_len <= off_len,
            "no function may grow under default const-CSE: {name} opt-out={off_len}B default={on_len}B ({rel})"
        );
    }
    (off, on)
}

/// CLAIM 3 (PR2) — flag ON recovers real byte wins on functions with register
/// HEADROOM, while never growing any function across the whole corpus.
///
///   - `flight_seam.wat` `flight_algo`: the greedy selector re-materializes the
///     same constant into one register at two reuses (the register is clobbered
///     between), so Pass 1's still-resident fold cannot see it. The PR2
///     same-register hoist pins it in a free register and drops the repeat.
///   - `const_cse.wat` `spill12`: a 32-bit `movw+movt` constant re-materialized
///     12× — recovered only because [`const_units`] reconstructs the pair (PR2
///     item 1) so the hoist recognizes the value at all. This is the largest win
///     and is differential-verified (`const_cse_differential.py`).
///
/// `flat_flight.loom.wasm` is DELIBERATELY not asserted to shrink: its hot
/// segment has peak register pressure 11 > the pool of 9 (it already spills), so
/// the pressure guard correctly declines every hoist — the extra live register
/// would force a spill. Recovering flat_flight's redundant consts needs the
/// separate liveness-based *spilling* lever (VCR-RA SSA allocator), not const-CSE.
/// Here it must merely NOT GROW, which `corpus_offon` checks.
#[test]
fn const_cse_pr2_recovers_headroom_wins_without_growth_242() {
    // flight_seam: flight_algo shrinks; nothing grows.
    let (fs_off, fs_on) = corpus_offon("scripts/repro/flight_seam.wat", "fseam");
    let (off, on) = (fs_off["flight_algo"], fs_on["flight_algo"]);
    assert!(
        on < off,
        "PR2 must shrink flight_seam::flight_algo on headroom: off={off}B on={on}B"
    );

    // spill12: the 32-bit movw+movt hoist — the headline recovered win.
    let (s_off, s_on) = corpus_offon("scripts/repro/const_cse.wat", "spill");
    let (off, on) = (s_off["spill12"], s_on["spill12"]);
    assert!(
        on < off,
        "PR2 must shrink const_cse::spill12 (32-bit movw+movt hoist): off={off}B on={on}B"
    );
    assert!(
        off - on >= 8,
        "expected a real spill12 win (≥1 movw+movt pair, 8B), got {}B",
        off - on
    );

    // flat_flight: pressure-saturated → must not grow (recovery needs spilling).
    let (ff_off, ff_on) = corpus_offon("scripts/repro/flat_flight/flat_flight.loom.wasm", "flatf");
    assert_eq!(
        ff_on["flat_flight"], ff_off["flat_flight"],
        "flat_flight is pressure-saturated (peak 11 > pool 9); the guard declines, so it stays equal"
    );
}

fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// CLAIM 1 — ESCAPE HATCH: `SYNTH_CONST_CSE=0` emits the pinned, pre-flip
/// `.text` byte-for-byte (the golden is the pre-const-CSE capture, unchanged
/// by the flip). The rollback proof and a tripwire against the post-hoc CSE
/// passes leaking into the opt-out path.
#[test]
fn const_cse_escape_hatch_restores_old_bytes_242() {
    let off = compile("/tmp/const_cse_off.elf", false);
    let text = sections(&off).remove(".text").expect(".text present");
    assert_eq!(
        text.len(),
        GOLDEN_OFF_TEXT_LEN,
        "opt-out .text length drifted from the pre-flip baseline"
    );
    assert_eq!(
        fnv1a64(&text),
        GOLDEN_OFF_TEXT_FNV1A,
        "SYNTH_CONST_CSE=0 optimized-path .text drifted from the pre-const-CSE \
         baseline — the opt-out is supposed to restore the pre-flip bytes; \
         re-bless the golden ONLY if this was an intentional optimized-path \
         lowering change"
    );
}

/// CLAIM 2a — DEFAULT GOLDEN: the shipped default emits the pinned CSE'd
/// `.text` (pinned AFTER const_cse_differential.py re-ran green on these
/// bytes). An accidental change to the default lowering fails loud here.
#[test]
fn const_cse_default_matches_flip_golden_242() {
    let on = compile("/tmp/const_cse_def.elf", true);
    let text = sections(&on).remove(".text").expect(".text present");
    assert_eq!(
        (text.len(), fnv1a64(&text)),
        (GOLDEN_DEFAULT_TEXT_LEN, GOLDEN_DEFAULT_TEXT_FNV1A),
        "shipped-default optimized-path .text drifted from the flip golden — \
         if intentional, re-run const_cse_differential.py on this commit and \
         re-pin (they move together)"
    );
}

/// CLAIM 2b — the default strictly shrinks `large3` (a >16-bit const reused 3×
/// with register headroom): the redundant movw+movt pairs are dropped and the
/// reads retargeted by the post-hoc passes.
#[test]
fn const_cse_on_shrinks_headroom_function_242() {
    let off = compile("/tmp/const_cse_red_off.elf", false);
    let on = compile("/tmp/const_cse_red_on.elf", true);

    let off_len = func_text_len(&off, "large3");
    let on_len = func_text_len(&on, "large3");

    assert!(
        on_len < off_len,
        "const-CSE must shrink large3 on headroom: off={off_len}B on={on_len}B"
    );

    // Each eliminated `i32.const 100000` removes a movw(4)+movt(4) = 8 bytes;
    // two of the three are redundant, so expect ~16 bytes saved.
    assert!(
        off_len - on_len >= 8,
        "expected ≥8B saved (≥1 movw+movt pair), got {}B",
        off_len - on_len
    );
}
