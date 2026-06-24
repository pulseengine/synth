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

/// Compile a frozen fixture for `(backend, target)` with the exact `--all-exports
/// --relocatable` config the `.py` differentials use, and return the SHA-256 hex
/// of its `.text` and the section length. `SYNTH_NO_CMP_SELECT_FUSE` (the v0.13.0
/// cmp→select opt-out) / `SYNTH_CONST_CSE` are explicitly removed so a flag set in
/// the environment can never silently re-freeze the gate — it locks the SHIPPED
/// lowering, which since v0.13.0 INCLUDES cmp→select fusion (default-on). The
/// `object` crate reads `.text` arch-agnostically (ARM Thumb-2 and RV32 alike).
fn text_sha256(wasm: &str, backend: &str, target: &str) -> (String, usize) {
    let path = fixture(wasm);
    let elf = format!("/tmp/frozenbytes_{backend}_{wasm}.elf");
    let out = Command::new(synth())
        .env_remove("SYNTH_NO_CMP_SELECT_FUSE")
        .env_remove("SYNTH_CONST_CSE")
        .args([
            "compile",
            path.to_str().unwrap(),
            "-o",
            &elf,
            "-b",
            backend,
            "--target",
            target,
            "--all-exports",
            "--relocatable",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "synth compile failed for {wasm} ({backend}/{target}): {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let bytes = std::fs::read(&elf).expect("read elf");
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

/// Assert each `(fixture, golden sha256, golden len)` for `(backend, target)`.
/// The length is asserted too, so a re-freeze prints the size delta (a quick read
/// on "how much codegen moved") and a hash collision can't pass on a wrong length.
fn assert_frozen(cases: &[(&str, &str, usize)], backend: &str, target: &str) {
    for &(wasm, golden, golden_len) in cases {
        let (got, len) = text_sha256(wasm, backend, target);
        assert_eq!(
            len, golden_len,
            "{wasm} ({backend}): .text length changed ({len} vs locked {golden_len}) \
             — codegen moved. If intentional, re-freeze the golden HERE and re-run \
             scripts/repro/*_differential.py on this commit (they move together)."
        );
        assert_eq!(
            got, golden,
            "{wasm} ({backend}): .text SHA-256 changed — a frozen fixture's machine \
             code drifted with no deliberate re-freeze. This is the gate working: \
             either a codegen change leaked in (investigate — dep bump? flag? \
             selector?), or it is intentional, in which case update the golden HERE \
             and re-run the scripts/repro/*_differential.py result checks on the \
             SAME commit."
        );
    }
}

/// THE ARM GATE. The canonical frozen perf fixtures (the ones spill_baseline_390 +
/// the `.py` differentials cover): control_step ↔ 0x00210A55, flight_seam_flat ↔
/// flat+inlined flight_algo 0x07FDF307, plus flight_seam and the div seam.
///
/// Goldens RE-FROZEN for v0.13.0 (#428): cmp→select fusion is now default-on, so
/// these lock the FUSED .text. The execution RESULTS are preserved — re-verified on
/// this commit with fusion on: control_step still 0x00210A55 (control_step_differential
/// .py 13/13), flat+inlined flight_algo still 0x07FDF307 (flight_seam_differential.py
/// MATCH). .text shrank: control_step 354→324, flight_seam 1016→902, flight_seam_flat
/// 1240→1122 (−262 B total); signed_div_const (0 fusion sites) unchanged. Prior
/// flag-off goldens were on main @ ef97f86 (post-#444), 2026-06-23.
#[test]
fn frozen_fixtures_text_is_bit_identical_oracle_001() {
    let cases = [
        (
            "control_step.wasm",
            "b4c4c290be2c8a83055d4c9696ae4ebb16486a8fd3fc268531607eeef35325e5",
            324usize,
        ),
        (
            "flight_seam.wasm",
            "300fdf3b92a0941da63b3215441a799d9b32ef942fd404b4803a83a6efb1bb60",
            902,
        ),
        (
            "flight_seam_flat.wasm",
            "23d0b6829414a855f365d84c7c3301c256f1843fe46b2cc9b369fec30610913d",
            1122,
        ),
        (
            "signed_div_const.wasm",
            "b277453b7829a5b2c64527131298d89fa63f5641231b1d4c7336675e8cdab9b0",
            34,
        ),
    ];
    assert_frozen(&cases, "arm", "cortex-m4");
}

/// THE RV32 GATE. The RISC-V backend (`synth-backend-riscv`) is an INDEPENDENT
/// codegen path with its own miscompile history (#220/#223/#226) — the ARM gate
/// gives it zero protection, and its frozen RV32 result-identity invariants
/// (control_step RV32 = 0x00210A55, matching ARM + wasmtime) live ONLY in the
/// out-of-CI `scripts/repro/*_riscv_differential.py`. Same hole, same live trigger
/// (the open dependabot wasmparser/wat bumps feed BOTH backends' decode). Scoped to
/// the frozen fixtures that compile on the rv32imac skeleton AND have a dedicated
/// `_riscv_differential.py` — control_step + signed_div_const. (flight_seam needs an
/// import-call relocation the RV32 skeleton does not yet emit.)
///
/// Goldens derived on main @ 57206a1 (post-#445), 2026-06-23.
#[test]
fn frozen_fixtures_rv32_text_is_bit_identical_oracle_001() {
    let cases = [
        (
            "control_step.wasm",
            "6e734c4c67b651067a56ff2a7593015f48ea24fe068a7a20c17f1c08a4e48e83",
            504usize,
        ),
        (
            "signed_div_const.wasm",
            "15fa429d5ef5474f8b65fdd9c81b3da4c70176fb077df25131e2ec3988eb999e",
            88,
        ),
    ];
    assert_frozen(&cases, "riscv", "rv32imac");
}
