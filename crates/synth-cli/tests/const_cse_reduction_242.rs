//! VCR-RA const-CSE (#242) — CI-gated reduction + frozen-safety oracle.
//!
//! The optimized (non-`--relocatable`) ARM path re-materializes a constant at
//! every use (`i32.const N` → a fresh `movw`/`movt` each time). gale measured
//! this on silicon: flat_flight spends 61% of its const materializations on
//! values already held in a register. `SYNTH_CONST_CSE=1` enables a
//! pressure-neutral const cache (`optimizer_bridge.rs`) that aliases a repeated
//! const to the register already holding it, emitting nothing.
//!
//! This is byte-CHANGING codegen, so the flag ships DEFAULT-OFF. Two claims are
//! locked here as executable CI gates; semantic equivalence under flag-ON is the
//! separate `const_cse_differential.py` unicorn-vs-wasmtime oracle:
//!
//!   1. FROZEN-SAFE (OFF ≡ pre-change baseline). With the flag OFF the optimized
//!      path emits a SPECIFIC, pinned `.text` — the golden below was captured
//!      against the pre-const-CSE tree (verified equal by a `git stash` compare:
//!      post-change-OFF hash == pre-change hash, both `8c3dfcbb…`). The frozen
//!      differential fixtures (control_step / flight_algo) compile `--relocatable`
//!      → they exercise the DIRECT path and never touch this code, so this golden
//!      is the ONLY gate pinning optimized-path-OFF bytes. A golden, not a
//!      compile-twice determinism check: determinism alone would not catch the
//!      flag-off path drifting away from the byte-identical baseline.
//!
//!   2. REAL REDUCTION ON HEADROOM. On `large3` — a >16-bit const reused 3× with
//!      ample free registers — the flag-ON `.text` is STRICTLY SMALLER (the two
//!      redundant `movw`+`movt` pairs collapse to register aliases). If a future
//!      change makes CSE inert on headroom, this fails.
//!
//! WHAT THIS DOES NOT CLAIM — the named prerequisites for a default-ON flip
//! (a separate, silicon-gated release, NOT this PR):
//!   - reg_effect DEF-COMPLETENESS. The cache's "never stale-wrong" property
//!     rests on `liveness::reg_effect` reporting EVERY GP-register a non-const op
//!     writes (so the reconciliation clears a clobbered alias). That is a broader
//!     property than the #513 reg_effect↔rewrite_op *consistency* oracle, which
//!     only pins that the two AGREE — they could agree and both under-report. The
//!     flip must be gated on op-coverage of reg_effect, not on #513.
//!   - ALIAS-EVICTION. Aliasing `dest` to an existing register makes two live
//!     vregs share one physical register, breaking the spill model's vreg↔reg
//!     bijection. If the OLDER alias is chosen as a spill victim while the
//!     younger keeps the alias, the freed register is reused under the younger →
//!     stale read. Not reachable in today's fixtures (the IR optimizer dedups
//!     two consecutive identical consts before they reach this pass), but the
//!     flip must either prove unreachability or make the spill path alias-aware.

use std::collections::HashMap;
use std::path::Path;
use std::process::Command;

use object::read::elf::ElfFile32;
use object::{Object, ObjectSection};

/// Golden FNV-1a-64 of the flag-OFF optimized-path `.text` for `const_cse.wat`.
/// Captured against the pre-const-CSE tree (stash-compare verified). Re-bless
/// ONLY when an intentional optimized-path lowering change is made — a surprise
/// failure here means the supposedly-frozen flag-off path drifted.
const GOLDEN_OFF_TEXT_FNV1A: u64 = 0xa68a_a2da_e5af_e4a7;
const GOLDEN_OFF_TEXT_LEN: usize = 576;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/const_cse.wat")
}

/// Compile the const-CSE fixture via the optimized path. `cse` toggles
/// `SYNTH_CONST_CSE`; returns the raw ELF bytes.
fn compile(out: &str, cse: bool) -> Vec<u8> {
    let mut cmd = Command::new(synth());
    if cse {
        cmd.env("SYNTH_CONST_CSE", "1");
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
fn compile_fixture(rel: &str, out: &str, cse: bool) -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(rel);
    let mut cmd = Command::new(synth());
    if cse {
        cmd.env("SYNTH_CONST_CSE", "1");
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

/// Compile a fixture flag-off and flag-on and assert the PR2 (#242) win-recovery
/// invariant: NO function grows, and every named function shrinks by at most the
/// bytes accounted for. Returns `(off, on)` size maps for per-function asserts.
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
            "no function may grow flag-on: {name} off={off_len}B on={on_len}B ({rel})"
        );
    }
    (off, on)
}

/// CLAIM 3 (PR2) — flag ON recovers real byte wins on functions with register
/// HEADROOM, while never growing any function across the whole corpus.
///
///   - `flight_seam.wat` `flight_algo`: the greedy selector re-materializes the
///     same constant into one register at two reuses (the register is clobbered
///     between), so neither Pass 1 nor the inline cache can see it. The PR2
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

/// CLAIM 1 — flag OFF emits the pinned, pre-change-identical `.text`.
#[test]
fn const_cse_off_matches_frozen_baseline_242() {
    let off = compile("/tmp/const_cse_off.elf", false);
    let text = sections(&off).remove(".text").expect(".text present");
    assert_eq!(
        text.len(),
        GOLDEN_OFF_TEXT_LEN,
        "flag-off .text length drifted from the frozen baseline"
    );
    assert_eq!(
        fnv1a64(&text),
        GOLDEN_OFF_TEXT_FNV1A,
        "flag-off optimized-path .text drifted from the pre-const-CSE baseline \
         — the default-off path is supposed to be byte-identical; re-bless the \
         golden ONLY if this was an intentional optimized-path lowering change"
    );
}

/// CLAIM 2 — flag ON strictly shrinks `large3` (a >16-bit const reused 3× with
/// register headroom): the redundant movw+movt pairs become register aliases.
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
