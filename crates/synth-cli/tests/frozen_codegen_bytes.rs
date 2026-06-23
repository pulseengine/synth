//! VCR-ORACLE-001 (#242) — frozen-codegen `.text` byte gate, in cargo CI.
//!
//! The repo's frozen result-identity invariants (control_step `0x00210A55`,
//! flat+inlined flight_algo `0x07FDF307`, the div seam) are asserted ONLY by the
//! out-of-CI `scripts/repro/*_differential.py` unicorn scripts — which need
//! wasmtime + unicorn + pyelftools and are never run by `cargo test` nor the
//! Renode bazel suite. So `spill_baseline_pressure_390.rs`'s load-bearing aside
//! ("the frozen differential hashes already fail on any codegen byte change") is,
//! in cargo CI, NOT actually enforced: an accidental lowering change — e.g. a
//! dependabot `wasmparser`/`wat` bump that shifts decode, or a flag flipped on by
//! mistake — could alter a frozen fixture's machine code and every cargo gate
//! would stay green.
//!
//! This closes that hole with a **byte gate**: compile each frozen fixture with
//! the shipped (flag-off) config the differentials use, extract the `.text`
//! section, and assert its SHA-256 matches a locked golden. It is the
//! **locally-verifiable** complement to the python differentials — derivable and
//! checkable with `cargo test` alone (no emulator), which the operating contract
//! ("a verifier you didn't run isn't a verifier") prefers over wiring an
//! unrunnable-here Python gate into CI.
//!
//! WHAT IT IS NOT. This proves byte-IDENTITY, not result-identity. It is NOT the
//! execution differential the VCR-SEL-004 cmp→select default-on flip owes — that
//! flip *deliberately* changes these bytes and must prove the RESULT is unchanged
//! across the change (run the ELF, assert `0x00210A55`); this gate will correctly
//! FAIL on that flip and demand a deliberate re-freeze. Different invariant,
//! different purpose. Byte gate ⇒ catch accidental drift + force deliberate
//! re-freeze. It does not reduce the flip's owed work.
//!
//! DETERMINISM. synth is a cross-compiler: `.text` is a pure function of (wasm,
//! target, flags), independent of the host. So these goldens (derived on macOS)
//! must match Linux CI. If a host actually diverged, this fails LOUD on its own
//! first CI run — self-correcting, never a shipped landmine.
//!
//! RE-FREEZING. When a codegen change is intentional, update the golden HERE
//! **and** re-run the `scripts/repro/*_differential.py` result checks on the same
//! commit — the two must move together. A bare golden bump with no differential
//! re-run is the anti-pattern this gate exists to prevent.

use std::process::Command;

use object::{Object, ObjectSection};
use sha2::{Digest, Sha256};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join(name)
}

/// Compile a frozen fixture with the exact config the `.py` differentials use
/// (`--target cortex-m4 --all-exports --relocatable`), return the SHA-256 hex of
/// its `.text` and the section length. `SYNTH_CMP_SELECT_FUSE` is explicitly
/// removed so an enabled-in-the-environment flag can never silently re-freeze the
/// gate — it locks the SHIPPED, flag-off lowering.
fn text_sha256(wasm: &str) -> (String, usize) {
    let path = fixture(wasm);
    let out = Command::new(synth())
        .env_remove("SYNTH_CMP_SELECT_FUSE")
        .env_remove("SYNTH_CONST_CSE")
        .args([
            "compile",
            path.to_str().unwrap(),
            "-o",
            &format!("/tmp/frozenbytes_{wasm}.elf"),
            "--target",
            "cortex-m4",
            "--all-exports",
            "--relocatable",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "synth compile failed for {wasm}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let bytes = std::fs::read(format!("/tmp/frozenbytes_{wasm}.elf")).expect("read elf");
    let obj = object::File::parse(&*bytes).expect("parse elf");
    let text = obj
        .section_by_name(".text")
        .expect("frozen fixture must have a .text section");
    let data = text.data().expect("read .text");
    let mut hasher = Sha256::new();
    hasher.update(data);
    let digest = hasher.finalize();
    let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
    (hex, data.len())
}

/// THE GATE. Each frozen fixture's `.text` must hash to its locked golden. The
/// length is asserted too, so a re-freeze prints the size delta (a quick read on
/// "how much codegen moved") and a hash collision can't pass on a wrong length.
///
/// Goldens derived on main @ ef97f86 (post-#444 cmp→select, flag-off), 2026-06-23.
#[test]
fn frozen_fixtures_text_is_bit_identical_oracle_001() {
    // (fixture, golden sha256 of .text, golden .text length). These are the
    // canonical frozen perf fixtures (the ones spill_baseline_390 + the .py
    // differentials cover): control_step ↔ 0x00210A55, flight_seam_flat ↔
    // flat+inlined flight_algo 0x07FDF307, plus flight_seam and the div seam.
    let cases = [
        (
            "control_step.wasm",
            "5efa58ca2667fb2f910b5ebf0ef8020a7fc1b9224f3ec070e9e0028de9d83a57",
            354usize,
        ),
        (
            "flight_seam.wasm",
            "1f39b77b65f0695693deda9ee56e3a7fb3af4127858a8ac6c3ce0fd3398de516",
            1016,
        ),
        (
            "flight_seam_flat.wasm",
            "f6244f35f932aac7661b9ed1cbf70dc1b5353a9f5c03178ebad3a38a891d7b8f",
            1240,
        ),
        (
            "signed_div_const.wasm",
            "b277453b7829a5b2c64527131298d89fa63f5641231b1d4c7336675e8cdab9b0",
            34,
        ),
    ];

    for (wasm, golden, golden_len) in cases {
        let (got, len) = text_sha256(wasm);
        assert_eq!(
            len, golden_len,
            "{wasm}: .text length changed ({len} vs locked {golden_len}) — codegen \
             moved. If intentional, re-freeze the golden HERE and re-run \
             scripts/repro/*_differential.py on this commit (they move together)."
        );
        assert_eq!(
            got, golden,
            "{wasm}: .text SHA-256 changed — a frozen fixture's machine code drifted \
             with no deliberate re-freeze. This is the gate working: either a \
             codegen change leaked in (investigate — dep bump? flag? selector?), or \
             it is intentional, in which case update the golden HERE and re-run the \
             scripts/repro/*_differential.py result checks (control_step 0x00210A55 \
             / flight_algo 0x07FDF307) on the SAME commit."
        );
    }
}
