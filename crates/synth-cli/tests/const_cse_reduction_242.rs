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
