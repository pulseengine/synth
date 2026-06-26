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
/// of its `.text` and the section length. The default-changing opt-out flags
/// (`SYNTH_NO_CMP_SELECT_FUSE` — v0.13.0 cmp→select; `SYNTH_NO_LOCAL_PROMOTE` —
/// v0.14.0 local promotion) and `SYNTH_CONST_CSE` are explicitly removed so a flag
/// set in the environment can never silently re-freeze the gate — it locks the
/// SHIPPED lowering, which since v0.14.0 INCLUDES cmp→select fusion AND local
/// promotion (both default-on). The `object` crate reads `.text` arch-agnostically
/// (ARM Thumb-2 and RV32 alike).
fn text_sha256(wasm: &str, backend: &str, target: &str) -> (String, usize) {
    let path = fixture(wasm);
    let elf = format!("/tmp/frozenbytes_{backend}_{wasm}.elf");
    let out = Command::new(synth())
        .env_remove("SYNTH_NO_CMP_SELECT_FUSE")
        .env_remove("SYNTH_NO_LOCAL_PROMOTE")
        .env_remove("SYNTH_NO_IMM_SHIFT_FOLD")
        .env_remove("SYNTH_NO_STACK_FWD")
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
/// Goldens RE-FROZEN for the SYNTH_STACK_FWD flip (#242 feature loop): stack-reload
/// forwarding + frame-slot dead-store elimination are now default-on (on top of
/// v0.13.0 cmp→select + v0.14.0 local promotion + v0.15.0 immediate-shift folding),
/// so these lock the forwarded+DCE'd .text. The execution RESULTS are preserved —
/// re-verified on this commit: control_step still 0x00210A55
/// (control_step_differential.py 13/13), flat+inlined flight_algo still 0x07FDF307
/// (flight_seam_differential.py MATCH on BOTH flat and inlined). .text shrank again
/// (dead frame stores removed, reloads → register moves): flight_seam 774→738,
/// flight_seam_flat 910→878 (−68 B); control_step (no spurious slot reuse) and
/// signed_div_const unchanged. Instruction/memory-op proxy: flight_algo sp-traffic
/// 20→7, 139→135 insns — the measured CYCLE number is gale's G474RE (post-ship).
/// Escape hatch `SYNTH_NO_STACK_FWD=1` restores the prior goldens (asserted by
/// `frozen_fixtures_stack_fwd_escape_hatch_restores_old_bytes`). Prior (flag-off)
/// goldens were flight_seam 9e73eea3…/774, flight_seam_flat 887ea546…/910.
#[test]
fn frozen_fixtures_text_is_bit_identical_oracle_001() {
    let cases = [
        (
            "control_step.wasm",
            "1a97711cfb4754794a8577814388f08b81eff444edcba3de7d3e3d18ff435183",
            304usize,
        ),
        (
            "flight_seam.wasm",
            "dce728b48e14aa9187774799c0b268c6ad60be6dc0fa3e7cc9458c17dc65403b",
            738,
        ),
        (
            "flight_seam_flat.wasm",
            "0665e623f33457479940046d57a4b7ec02416a61bcc6ec71ea3556ed5b3cb568",
            878,
        ),
        (
            "signed_div_const.wasm",
            "b277453b7829a5b2c64527131298d89fa63f5641231b1d4c7336675e8cdab9b0",
            34,
        ),
    ];
    assert_frozen(&cases, "arm", "cortex-m4");
}

/// ESCAPE-HATCH GATE for the SYNTH_STACK_FWD flip (#242). Proves the opt-out
/// actually rolls back: with `SYNTH_NO_STACK_FWD=1` the two fixtures the flip moved
/// restore their PRE-flip goldens byte-for-byte. This is both the rollback proof and
/// a tripwire — if forwarding/DCE ever leaks into the opt-out path, the old hashes
/// stop matching. (control_step / signed_div_const are unaffected by the flip, so
/// they are not re-checked here; the default gate above already locks them.)
#[test]
fn frozen_fixtures_stack_fwd_escape_hatch_restores_old_bytes() {
    // (fixture, PRE-flip golden sha256, PRE-flip len) — the v0.15.0 goldens.
    let old = [
        (
            "flight_seam.wasm",
            "9e73eea3867ba085820329951e84a7d650c38a7fc78d9d03a6a83d02963f9670",
            774usize,
        ),
        (
            "flight_seam_flat.wasm",
            "887ea546429a4569112147fdc94b0ba90f02a6ccd2b511aa2ca48dab017dbc2c",
            910,
        ),
    ];
    for &(wasm, golden, golden_len) in &old {
        let elf = format!("/tmp/frozen_nofwd_{wasm}.elf");
        let out = Command::new(synth())
            .env("SYNTH_NO_STACK_FWD", "1")
            .env_remove("SYNTH_NO_CMP_SELECT_FUSE")
            .env_remove("SYNTH_NO_LOCAL_PROMOTE")
            .env_remove("SYNTH_NO_IMM_SHIFT_FOLD")
            .env_remove("SYNTH_CONST_CSE")
            .args([
                "compile",
                fixture(wasm).to_str().unwrap(),
                "-o",
                &elf,
                "-b",
                "arm",
                "--target",
                "cortex-m4",
                "--all-exports",
                "--relocatable",
            ])
            .output()
            .expect("run synth");
        assert!(out.status.success(), "compile failed for {wasm}");
        let bytes = std::fs::read(&elf).expect("read elf");
        let obj = object::File::parse(&*bytes).expect("parse elf");
        let data = obj
            .section_by_name(".text")
            .expect(".text")
            .data()
            .expect("read .text");
        assert_eq!(
            data.len(),
            golden_len,
            "{wasm}: SYNTH_NO_STACK_FWD must restore the pre-flip length"
        );
        let hex: String = Sha256::digest(data)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        assert_eq!(
            hex, golden,
            "{wasm}: SYNTH_NO_STACK_FWD=1 must restore the pre-flip bytes (rollback broken)"
        );
    }
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
