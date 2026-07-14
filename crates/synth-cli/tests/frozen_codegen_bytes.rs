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
/// v0.14.0 local promotion; `SYNTH_RV_CMP_SELECT` — #472 RV32 cmp→select,
/// `=0` opts out; `SYNTH_CONST_CSE` — #242 const-CSE, `=0` opts out;
/// `SYNTH_RV_LOCAL_PROMO` — #472/#601 RV32 local promotion, `=0` opts out)
/// are explicitly removed so a flag set in the environment can never silently
/// re-freeze the gate — it locks the SHIPPED lowering, which since v0.14.0
/// INCLUDES cmp→select fusion AND local promotion on ARM (both default-on),
/// since the #472 flip-wave includes RV32 cmp→select fusion, since the #601
/// measured-profitability flip includes RV32 local promotion (byte-neutral on
/// these goldens — the measured gate declines everywhere in them, verified at
/// flip time), and since the #242 const-CSE flip includes the post-hoc
/// `apply_const_cse` passes on ARM (both paths). The `object` crate reads
/// `.text` arch-agnostically (ARM Thumb-2 and RV32 alike).
fn text_sha256(wasm: &str, backend: &str, target: &str) -> (String, usize) {
    let path = fixture(wasm);
    let elf = format!("/tmp/frozenbytes_{backend}_{wasm}.elf");
    let out = Command::new(synth())
        .env_remove("SYNTH_NO_CMP_SELECT_FUSE")
        .env_remove("SYNTH_NO_LOCAL_PROMOTE")
        .env_remove("SYNTH_NO_IMM_SHIFT_FOLD")
        .env_remove("SYNTH_NO_STACK_FWD")
        .env_remove("SYNTH_SPILL_REALLOC")
        .env_remove("SYNTH_CONST_CSE")
        .env_remove("SYNTH_BASE_CSE")
        .env_remove("SYNTH_RV_CMP_SELECT")
        .env_remove("SYNTH_RV_LOCAL_PROMO")
        .env_remove("SYNTH_RV_SHIFT_FOLD")
        .env_remove("SYNTH_DEAD_FRAME_ELIM")
        .env_remove("SYNTH_UXTH_FOLD")
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
        // Refreeze ritual aid: with SYNTH_REFREEZE_PRINT=1 the gate prints the
        // NEW golden tuples instead of asserting — paste them over the old
        // pins ONLY after every scripts/repro/*_differential.py passes on the
        // new bytes (they move together; see the assert message below).
        if std::env::var("SYNTH_REFREEZE_PRINT").is_ok() {
            println!("REPIN ({backend}/{target}): (\"{wasm}\", \"{got}\", {len}),");
            continue;
        }
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
/// Goldens RE-FROZEN for the SYNTH_SPILL_REALLOC flip (#242, VCR-RA-001): the
/// three-stage Belady spill lever (#569 reload forwarding, #576 spill re-choice,
/// #579 whole-fn slot liveness) is now default-on, on top of the earlier flips
/// (v0.13.0 cmp→select, v0.14.0 local promotion, v0.15.0 imm-shift fold,
/// SYNTH_STACK_FWD). The execution RESULTS are preserved — re-verified on this
/// commit BEFORE re-pinning: flat+inlined flight_algo still 0x07FDF307
/// (flight_seam_differential.py MATCH + frame_slot_dce_differential.py 8/8),
/// control_step semantics match wasmtime (r12_spill_496_differential.py 5/5;
/// control_step_differential.py has a pre-existing symbol-parse harness break
/// that fails identically with the opt-out), const_cse_differential.py PASS,
/// spill_rung_581_differential.py 12/12, i64_param_518 + br_table_value_509
/// PASS. .text shrank again (reloads dissolved + dead frame stores dropped):
/// flight_seam 738→730 (−8), flight_seam_flat 878→866 (−12); control_step and
/// signed_div_const unchanged (no surviving spill traffic there). Escape hatch
/// `SYNTH_SPILL_REALLOC=0` restores the prior goldens (asserted by
/// `frozen_fixtures_spill_realloc_escape_hatch_restores_old_bytes`). Prior
/// goldens were flight_seam dce728b4…/738, flight_seam_flat 0665e623…/878.
///
/// The SYNTH_BASE_CSE flip (#468, default-on) does NOT move these goldens:
/// the fixtures compile `--relocatable` → the DIRECT selector, and base-CSE
/// lives only in the optimized path's `ir_to_arm` (verified: hashes unchanged
/// under the flip). Its own default/opt-out goldens live in
/// `base_cse_flip_468.rs`. `SYNTH_BASE_CSE` is still env-removed above so a
/// stray opt-out in the environment can't skew any future coupling.
///
/// Goldens RE-FROZEN for the SYNTH_CONST_CSE flip (#242): the post-hoc
/// `apply_const_cse` passes run on the direct path too (they rewrite the
/// selected ArmOp stream in `compile_wasm_to_arm`, path-agnostic), so
/// control_step (304→300, −4) and flight_seam (730→726, −4) each drop one
/// redundant materialization; flight_seam_flat and signed_div_const are
/// byte-identical (nothing redundant survives the earlier folds there).
/// Execution differentials re-run green on the new default bytes BEFORE this
/// re-pin: control_step 13/13 vs wasmtime, flight_seam flat+inlined
/// flight_algo 0x07FDF307, const_cse, frame_slot_dce 8/8, spill_rung_581 6/6,
/// volatile_segment_543 (see the flip PR). `SYNTH_CONST_CSE=0` restores the
/// prior goldens (asserted by
/// `frozen_fixtures_const_cse_escape_hatch_restores_old_bytes`). Prior
/// goldens were control_step 1a97711c…/304, flight_seam 6872d6f3…/730.
///
/// Goldens RE-FROZEN for the #242 FLAG-AUDIT FLIP-WAVE (SYNTH_DEAD_FRAME_ELIM
/// and SYNTH_UXTH_FOLD, both default-on; #592 audit items): the uxth/uxtb fold
/// drops control_step's `movw #0xffff` mask materializations (300→294, −6);
/// dead-frame elimination removes the provably-dead `sub/add sp` frames in
/// flight_seam's controller_step (−8) and filter_step (−12) — flight_seam
/// 726→706, flight_seam_flat 866→846. signed_div_const is inert under both.
/// Execution differentials re-run green on the new default bytes BEFORE this
/// re-pin: 52/56 scripts/repro/*_differential.py PASS incl. uxth_fold,
/// leaf_dead_frame, control_step 13/13, flight_seam flat+inlined flight_algo
/// 0x07FDF307, frame_slot_dce 8/8 (the 4 non-PASS: 3 needed regenerated
/// external inputs then passed; sret_decide is a pre-existing flip-neutral
/// harness discrepancy — its fixture bytes are IDENTICAL default vs opt-out).
/// Per-flag opt-outs restore the prior goldens (asserted by
/// `frozen_fixtures_dead_frame_elim_escape_hatch_restores_old_bytes` and
/// `frozen_fixtures_uxth_fold_escape_hatch_restores_old_bytes`). Prior
/// goldens were control_step 158b036b…/300, flight_seam 1e1d2b75…/726,
/// flight_seam_flat d11849db…/866.
/// Goldens RE-FROZEN for the #390 stack-fwd strengthening (v0.42 lane):
/// `forward_stack_reloads` upgraded to a conditional-branch-transparent
/// holder-lattice walk (forwards/deletes reloads across `br_if`
/// compare→branch ladders — joins still reset all state). control_step
/// 314→308 (−6), flight_seam_flat 1014→1010 (−4); flight_seam and
/// signed_div_const are byte-identical. Execution differentials re-run green
/// on the new default bytes BEFORE this re-pin: the full
/// scripts/repro/*_differential.py sweep (86/87 — u64_unpack_riscv is
/// env-broken identically on the old bytes) incl. flight_seam flat+inlined
/// flight_algo 0x07FDF307, control_step, frame_slot_dce, const_cse,
/// spill_rung_581, and the NEW gust_spill_fwd_390_differential.py
/// (gust_poll state+return vs wasmtime in default + both lever opt-outs).
/// `SYNTH_NO_STACK_FWD=1` restores the prior stack-fwd-off bytes (asserted by
/// `frozen_fixtures_stack_fwd_escape_hatch_restores_old_bytes`, pins
/// untouched). Prior goldens were control_step f962794f…/314,
/// flight_seam_flat 64388237…/1014.
#[test]
fn frozen_fixtures_text_is_bit_identical_oracle_001() {
    let cases = [
        (
            "control_step.wasm",
            "b365a29ef47ddd3e5ef8755d54cbd0d46c504af64dd24d08e9500385f674d892",
            308usize,
        ),
        (
            "flight_seam.wasm",
            "28642d60533c3fc154dfc7ab27e6a9f4ffe5b0a81adfe4c0fba493d490fc8d2c",
            870,
        ),
        (
            "flight_seam_flat.wasm",
            "7d3145c4ed0493cd326f867ab068930a64f3813bce60d031b19f535d0f800998",
            1010,
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
///
/// COMPOSITION NOTE: rolling back to the pre-STACK_FWD bytes now also requires
/// opting out of the LATER spill-realloc lever (`SYNTH_SPILL_REALLOC=0`), the
/// const-CSE lever (`SYNTH_CONST_CSE=0`, #242), and the flag-audit flip-wave
/// levers (`SYNTH_DEAD_FRAME_ELIM=0` + `SYNTH_UXTH_FOLD=0`, #242) — all
/// default on since their own flips and would otherwise rewrite the traffic
/// these goldens pin. The opt-outs compose; each is separately gated.
#[test]
fn frozen_fixtures_stack_fwd_escape_hatch_restores_old_bytes() {
    // (fixture, PRE-flip golden sha256, PRE-flip len) — the v0.15.0 goldens.
    let old = [
        (
            "flight_seam.wasm",
            "a11ed21e5fe53cdd3bc45382e7ad4288a53abf7fbdffa42c299cf1d2bc24f1da",
            938usize,
        ),
        (
            "flight_seam_flat.wasm",
            "973a630e6ed687ec02dc73ce9f79cb8261455fceaca1f373c51279d23943ef8a",
            1078,
        ),
    ];
    for &(wasm, golden, golden_len) in &old {
        let elf = format!("/tmp/frozen_nofwd_{wasm}.elf");
        let out = Command::new(synth())
            .env("SYNTH_NO_STACK_FWD", "1")
            .env("SYNTH_SPILL_REALLOC", "0")
            .env("SYNTH_CONST_CSE", "0")
            .env("SYNTH_DEAD_FRAME_ELIM", "0")
            .env("SYNTH_UXTH_FOLD", "0")
            .env_remove("SYNTH_NO_CMP_SELECT_FUSE")
            .env_remove("SYNTH_NO_LOCAL_PROMOTE")
            .env_remove("SYNTH_NO_IMM_SHIFT_FOLD")
            .env_remove("SYNTH_BASE_CSE")
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
        if std::env::var("SYNTH_REFREEZE_PRINT").is_ok() {
            let hex: String = Sha256::digest(data)
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            println!("REPIN: (\"{wasm}\", \"{hex}\", {}),", data.len());
            continue;
        }
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

/// ESCAPE-HATCH GATE for the SYNTH_SPILL_REALLOC flip (#242, VCR-RA-001).
/// Proves the opt-out actually rolls back: with `SYNTH_SPILL_REALLOC=0` the two
/// fixtures the flip moved restore their PRE-flip goldens byte-for-byte — the
/// rollback proof AND a tripwire against the spill-realloc stages leaking into
/// the opt-out path. (control_step / signed_div_const are byte-identical under
/// the flip — no surviving spill traffic — so the default gate above already
/// locks them for both settings.)
///
/// COMPOSITION NOTE: rolling back to these bytes now also requires opting out
/// of the LATER const-CSE lever (`SYNTH_CONST_CSE=0`, #242 flip) and the
/// flag-audit flip-wave levers (`SYNTH_DEAD_FRAME_ELIM=0` + `SYNTH_UXTH_FOLD=0`,
/// #242), which would otherwise rewrite traffic these goldens pin.
#[test]
fn frozen_fixtures_spill_realloc_escape_hatch_restores_old_bytes() {
    // (fixture, opt-out golden sha256, len). RE-DERIVED at the #390 stack-fwd
    // strengthening: stack-fwd stays ON in this config, and its
    // conditional-branch-transparent forwarding now catches (earlier in the
    // pipeline) the same reloads spill-realloc's stage 1 forwarded — so these
    // are no longer the historical pre-spill-realloc defaults byte-for-byte.
    // The gate's TRIPWIRE semantics are unchanged: `SYNTH_SPILL_REALLOC=0`
    // must land exactly here, so any stage-2/3 leak into the opt-out path
    // still reddens. Prior pins were flight_seam b590aea8…/902,
    // flight_seam_flat 49ebf8a1…/1046.
    let old = [
        (
            "flight_seam.wasm",
            "d8af257f82594e0a41d75c2fba2aaee62041fff54863342f4a9c3aebe39e10f3",
            894usize,
        ),
        (
            "flight_seam_flat.wasm",
            "b521284d672f0b420ba0db65281259f5824fdd7fe39a217730529fd6f5661006",
            1038,
        ),
    ];
    for &(wasm, golden, golden_len) in &old {
        let elf = format!("/tmp/frozen_nospillrealloc_{wasm}.elf");
        let out = Command::new(synth())
            .env("SYNTH_SPILL_REALLOC", "0")
            .env("SYNTH_CONST_CSE", "0")
            .env("SYNTH_DEAD_FRAME_ELIM", "0")
            .env("SYNTH_UXTH_FOLD", "0")
            .env_remove("SYNTH_NO_CMP_SELECT_FUSE")
            .env_remove("SYNTH_NO_LOCAL_PROMOTE")
            .env_remove("SYNTH_NO_IMM_SHIFT_FOLD")
            .env_remove("SYNTH_NO_STACK_FWD")
            .env_remove("SYNTH_BASE_CSE")
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
        if std::env::var("SYNTH_REFREEZE_PRINT").is_ok() {
            let hex: String = Sha256::digest(data)
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            println!("REPIN: (\"{wasm}\", \"{hex}\", {}),", data.len());
            continue;
        }
        assert_eq!(
            data.len(),
            golden_len,
            "{wasm}: SYNTH_SPILL_REALLOC=0 must restore the pre-flip length"
        );
        let hex: String = Sha256::digest(data)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        assert_eq!(
            hex, golden,
            "{wasm}: SYNTH_SPILL_REALLOC=0 must restore the pre-flip bytes (rollback broken)"
        );
    }
}

/// ESCAPE-HATCH GATE for the SYNTH_CONST_CSE flip (#242). Proves the opt-out
/// actually rolls back: with `SYNTH_CONST_CSE=0` the two fixtures the flip
/// moved restore their PRE-flip goldens byte-for-byte — the rollback proof
/// AND a tripwire against the post-hoc CSE passes leaking into the opt-out
/// path. (flight_seam_flat / signed_div_const are byte-identical under the
/// flip, so the default gate above locks them for both settings.)
///
/// COMPOSITION NOTE: since the #242 flag-audit flip-wave, rolling back to
/// these bytes also requires opting out of the LATER levers
/// (`SYNTH_DEAD_FRAME_ELIM=0` + `SYNTH_UXTH_FOLD=0`), which fire on
/// control_step (uxth) and flight_seam (dead-frame).
#[test]
fn frozen_fixtures_const_cse_escape_hatch_restores_old_bytes() {
    // (fixture, opt-out golden sha256, len). control_step RE-DERIVED at the
    // #390 stack-fwd strengthening (stack-fwd stays ON in this config and now
    // forwards −6 B of control_step's reload traffic; prior pin was
    // 93ef2610…/324); flight_seam is untouched by that change. The tripwire
    // semantics are unchanged: `SYNTH_CONST_CSE=0` must land exactly here.
    let old = [
        (
            "control_step.wasm",
            "5771a1a1e74e2aedfd07daa526b7b8301022cc76c5d3ed79c0adb2c81404c838",
            318usize,
        ),
        (
            "flight_seam.wasm",
            "d8af257f82594e0a41d75c2fba2aaee62041fff54863342f4a9c3aebe39e10f3",
            894,
        ),
    ];
    for &(wasm, golden, golden_len) in &old {
        let elf = format!("/tmp/frozen_nocse_{wasm}.elf");
        let out = Command::new(synth())
            .env("SYNTH_CONST_CSE", "0")
            .env("SYNTH_DEAD_FRAME_ELIM", "0")
            .env("SYNTH_UXTH_FOLD", "0")
            .env_remove("SYNTH_NO_CMP_SELECT_FUSE")
            .env_remove("SYNTH_NO_LOCAL_PROMOTE")
            .env_remove("SYNTH_NO_IMM_SHIFT_FOLD")
            .env_remove("SYNTH_NO_STACK_FWD")
            .env_remove("SYNTH_SPILL_REALLOC")
            .env_remove("SYNTH_BASE_CSE")
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
        if std::env::var("SYNTH_REFREEZE_PRINT").is_ok() {
            let hex: String = Sha256::digest(data)
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            println!("REPIN: (\"{wasm}\", \"{hex}\", {}),", data.len());
            continue;
        }
        assert_eq!(
            data.len(),
            golden_len,
            "{wasm}: SYNTH_CONST_CSE=0 must restore the pre-flip length"
        );
        let hex: String = Sha256::digest(data)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        assert_eq!(
            hex, golden,
            "{wasm}: SYNTH_CONST_CSE=0 must restore the pre-flip bytes (rollback broken)"
        );
    }
}

/// ESCAPE-HATCH GATE for the SYNTH_DEAD_FRAME_ELIM flip (#242 flag-audit
/// flip-wave, VCR-RA-002 #390). Proves the opt-out actually rolls back: with
/// `SYNTH_DEAD_FRAME_ELIM=0` ALONE the two fixtures the flip moved restore
/// their PRE-flip goldens byte-for-byte — the rollback proof AND a tripwire
/// against `elide_dead_frame` leaking into the opt-out path. No composition
/// needed for THESE fixtures: the sibling uxth lever is fold-inert on
/// flight_seam/flight_seam_flat (no 0xffff/0xff mask materializations), so
/// `=0` alone lands exactly on the previous shipped default there.
/// (control_step / signed_div_const are dead-frame-inert — the default gate
/// above locks them.)
#[test]
fn frozen_fixtures_dead_frame_elim_escape_hatch_restores_old_bytes() {
    // (fixture, opt-out golden sha256, len). flight_seam_flat RE-DERIVED at
    // the #390 stack-fwd strengthening (stack-fwd stays ON in this config;
    // the holder-lattice walk deletes a now-no-op reload, −4 B; prior pin was
    // d62bdfa3…/1034); flight_seam is untouched by that change. The tripwire
    // semantics are unchanged: `SYNTH_DEAD_FRAME_ELIM=0` must land exactly
    // here.
    let old = [
        (
            "flight_seam.wasm",
            "18163e0b37f5932f0e97fe573d9626f53ca1962b823c24e8f5057a34cf8c4318",
            890usize,
        ),
        (
            "flight_seam_flat.wasm",
            "aacd064cefc3087fe63e969796c5f87e659f3c8724a4d0999c817de38ef824a1",
            1030,
        ),
    ];
    for &(wasm, golden, golden_len) in &old {
        let elf = format!("/tmp/frozen_nodfe_{wasm}.elf");
        let out = Command::new(synth())
            .env("SYNTH_DEAD_FRAME_ELIM", "0")
            .env_remove("SYNTH_UXTH_FOLD")
            .env_remove("SYNTH_NO_CMP_SELECT_FUSE")
            .env_remove("SYNTH_NO_LOCAL_PROMOTE")
            .env_remove("SYNTH_NO_IMM_SHIFT_FOLD")
            .env_remove("SYNTH_NO_STACK_FWD")
            .env_remove("SYNTH_SPILL_REALLOC")
            .env_remove("SYNTH_CONST_CSE")
            .env_remove("SYNTH_BASE_CSE")
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
        if std::env::var("SYNTH_REFREEZE_PRINT").is_ok() {
            let hex: String = Sha256::digest(data)
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            println!("REPIN: (\"{wasm}\", \"{hex}\", {}),", data.len());
            continue;
        }
        assert_eq!(
            data.len(),
            golden_len,
            "{wasm}: SYNTH_DEAD_FRAME_ELIM=0 must restore the pre-flip length"
        );
        let hex: String = Sha256::digest(data)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        assert_eq!(
            hex, golden,
            "{wasm}: SYNTH_DEAD_FRAME_ELIM=0 must restore the pre-flip bytes (rollback broken)"
        );
    }
}

/// ESCAPE-HATCH GATE for the SYNTH_UXTH_FOLD flip (#242 flag-audit flip-wave,
/// #428). Proves the opt-out actually rolls back: with `SYNTH_UXTH_FOLD=0`
/// ALONE the fixture the flip moved restores its PRE-flip golden
/// byte-for-byte — the rollback proof AND a tripwire against `fold_uxth`
/// leaking into the opt-out path. No composition needed: the sibling
/// dead-frame lever is inert on control_step (no dead frame survives), so
/// `=0` alone lands exactly on the previous shipped default.
#[test]
fn frozen_fixtures_uxth_fold_escape_hatch_restores_old_bytes() {
    // (fixture, opt-out golden sha256, len). RE-DERIVED at the #390 stack-fwd
    // strengthening (stack-fwd stays ON in this config and forwards −6 B of
    // control_step's reload traffic; prior pin was fdcfbac1…/320). The
    // tripwire semantics are unchanged: `SYNTH_UXTH_FOLD=0` must land exactly
    // here.
    let old = [(
        "control_step.wasm",
        "3a488afa1612a5698d3a1817a4ad526f9e3cde9f62a324195027a48780b635e6",
        314usize,
    )];
    for &(wasm, golden, golden_len) in &old {
        let elf = format!("/tmp/frozen_nouxth_{wasm}.elf");
        let out = Command::new(synth())
            .env("SYNTH_UXTH_FOLD", "0")
            .env_remove("SYNTH_DEAD_FRAME_ELIM")
            .env_remove("SYNTH_NO_CMP_SELECT_FUSE")
            .env_remove("SYNTH_NO_LOCAL_PROMOTE")
            .env_remove("SYNTH_NO_IMM_SHIFT_FOLD")
            .env_remove("SYNTH_NO_STACK_FWD")
            .env_remove("SYNTH_SPILL_REALLOC")
            .env_remove("SYNTH_CONST_CSE")
            .env_remove("SYNTH_BASE_CSE")
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
        if std::env::var("SYNTH_REFREEZE_PRINT").is_ok() {
            let hex: String = Sha256::digest(data)
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            println!("REPIN: (\"{wasm}\", \"{hex}\", {}),", data.len());
            continue;
        }
        assert_eq!(
            data.len(),
            golden_len,
            "{wasm}: SYNTH_UXTH_FOLD=0 must restore the pre-flip length"
        );
        let hex: String = Sha256::digest(data)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        assert_eq!(
            hex, golden,
            "{wasm}: SYNTH_UXTH_FOLD=0 must restore the pre-flip bytes (rollback broken)"
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
/// Goldens RE-FROZEN for the SYNTH_RV_CMP_SELECT flip (#472, the RV32 lever
/// flip-wave): cmp→select fusion is now DEFAULT-ON for the RV32 selector
/// (VCR-SEL-004 port), so control_step's three fused selects drop their
/// boolean materializations (504 → 492 B, −12). signed_div_const has no
/// selects — byte-identical, hash unchanged. Execution differentials were
/// re-run green on the new default bytes BEFORE this re-pin
/// (control_step_riscv / signed_div_const_riscv / rv32_cmp_select_472_riscv /
/// rv32_local_promotion_472_riscv / if_else_result_343_riscv /
/// i64_divs_317_riscv — see the flip PR). `SYNTH_RV_CMP_SELECT=0` restores
/// the prior goldens (asserted by
/// `frozen_fixtures_rv32_cmp_select_escape_hatch_restores_old_bytes`). Prior
/// goldens (main @ 57206a1, 2026-06-23) were control_step 6e734c4c…/504,
/// signed_div_const 15fa429d…/88.
///
/// `SYNTH_RV_LOCAL_PROMO` (#472's second lever) flipped DEFAULT-ON with the
/// #601 measured-profitability fix (profitability is measured per candidate
/// subset against the unpromoted baseline — strict no-grow by construction).
/// These goldens are UNCHANGED by that flip: the measured gate declines
/// promotion everywhere in control_step and signed_div_const, so the promo-ON
/// bytes are bit-identical to the promo-UNSET bytes pinned here (verified by
/// hash at flip time; `frozen_fixtures_rv32_local_promo_escape_hatch_is_noop`
/// locks the opt-out side). Execution differentials were re-run green on the
/// flag-ON bytes BEFORE the flip (all 11 `*_riscv_differential.py`; corpus
/// no-grow gate `rv32_local_promo_no_grow_corpus_472`: 10 shrink / 0 grow
/// across 67 fixtures — see the flip PR).
///
/// Goldens RE-FROZEN for the SYNTH_RV_SHIFT_FOLD flip (#242 flag-audit
/// flip-wave; gale re-measured the fold still off and worth −8 B toward the
/// esp32c3 128 B floor, #242 2026-07-03): constant shift amounts fold into
/// the immediate forms (`slli/srli/srai`), dropping the `li tmp, N` —
/// control_step 492→484 (−8, exactly gale's number). signed_div_const has no
/// constant shifts surviving selection — byte-identical, hash unchanged.
/// Execution differentials re-run green on the new default bytes BEFORE this
/// re-pin (shift_fold_riscv 21/21, control_step_riscv 0x00210A55, plus the
/// full *_riscv_differential.py set — see the flip PR).
/// `SYNTH_RV_SHIFT_FOLD=0` restores the prior goldens (asserted by
/// `frozen_fixtures_rv32_shift_fold_escape_hatch_restores_old_bytes`). Prior
/// goldens were control_step 780e427a…/492, signed_div_const 15fa429d…/88.
#[test]
fn frozen_fixtures_rv32_text_is_bit_identical_oracle_001() {
    let cases = [
        (
            "control_step.wasm",
            "6ac5d7f94f3e17b0314aa2549e24b172b50dc0df110130c80a94e19d62c7b75b",
            484usize,
        ),
        (
            "signed_div_const.wasm",
            "15fa429d5ef5474f8b65fdd9c81b3da4c70176fb077df25131e2ec3988eb999e",
            88,
        ),
    ];
    assert_frozen(&cases, "riscv", "rv32imac");
}

/// ESCAPE-HATCH GATE for the SYNTH_RV_SHIFT_FOLD flip (#242 flag-audit
/// flip-wave): `SYNTH_RV_SHIFT_FOLD=0` ALONE must restore the pre-flip RV32
/// goldens byte-for-byte — the rollback proof, and a tripwire against
/// `fold_const_shift` leaking into the opt-out lowering. signed_div_const is
/// fold-inert, so its pin is identical in both configurations — it guards
/// that the opt-out stays a no-op there.
#[test]
fn frozen_fixtures_rv32_shift_fold_escape_hatch_restores_old_bytes() {
    let cases = [
        (
            "control_step.wasm",
            "780e427a7ce94b54e0aaad0165e4984bebc1c0c43d25def5b5e9abf6a3929fed",
            492usize,
        ),
        (
            "signed_div_const.wasm",
            "15fa429d5ef5474f8b65fdd9c81b3da4c70176fb077df25131e2ec3988eb999e",
            88,
        ),
    ];
    for &(wasm, golden, golden_len) in &cases {
        let path = fixture(wasm);
        let elf = format!("/tmp/frozenbytes_rv32_shiftfold_off_{wasm}.elf");
        // COMPOSITION (#601 promo flip): local promotion is default-on but
        // byte-neutral on these fixtures; pin it off anyway so the rollback
        // stays an exact pre-flip composition, not a byte-neutrality bet.
        let out = Command::new(synth())
            .env("SYNTH_RV_LOCAL_PROMO", "0")
            .env_remove("SYNTH_RV_CMP_SELECT")
            .env("SYNTH_RV_SHIFT_FOLD", "0")
            .args([
                "compile",
                path.to_str().unwrap(),
                "-o",
                &elf,
                "-b",
                "riscv",
                "--target",
                "rv32imac",
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
        if std::env::var("SYNTH_REFREEZE_PRINT").is_ok() {
            let hex: String = Sha256::digest(data)
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            println!("REPIN: (\"{wasm}\", \"{hex}\", {}),", data.len());
            continue;
        }
        assert_eq!(
            data.len(),
            golden_len,
            "{wasm}: SYNTH_RV_SHIFT_FOLD=0 must restore the pre-flip length"
        );
        let hex: String = Sha256::digest(data)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        assert_eq!(
            hex, golden,
            "{wasm}: SYNTH_RV_SHIFT_FOLD=0 must restore the pre-flip bytes (rollback broken)"
        );
    }
}

/// The RV32 flip-wave ESCAPE HATCH (#472): `SYNTH_RV_CMP_SELECT=0` must
/// restore the pre-flip RV32 goldens byte-for-byte — the rollback proof, and
/// a tripwire against the fusion path leaking into the opt-out lowering.
/// signed_div_const is fusion-inert (no selects), so its pin is identical in
/// both configurations — it guards that the opt-out stays a no-op there.
///
/// COMPOSITION NOTE: since the #242 flag-audit flip-wave, rolling back to
/// these bytes also requires opting out of the LATER shift-fold lever
/// (`SYNTH_RV_SHIFT_FOLD=0`), which fires on control_step; since the #601
/// promo flip, `SYNTH_RV_LOCAL_PROMO=0` is pinned too (byte-neutral here,
/// pinned for exactness).
#[test]
fn frozen_fixtures_rv32_cmp_select_escape_hatch_restores_old_bytes() {
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
    for &(wasm, golden, golden_len) in &cases {
        let path = fixture(wasm);
        let elf = format!("/tmp/frozenbytes_rv32_cmpsel_off_{wasm}.elf");
        // COMPOSITION (#601 promo flip): see the shift-fold hatch — promo is
        // pinned off so the rollback composition stays exact.
        let out = Command::new(synth())
            .env("SYNTH_RV_LOCAL_PROMO", "0")
            .env("SYNTH_RV_CMP_SELECT", "0")
            .env("SYNTH_RV_SHIFT_FOLD", "0")
            .args([
                "compile",
                path.to_str().unwrap(),
                "-o",
                &elf,
                "-b",
                "riscv",
                "--target",
                "rv32imac",
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
        if std::env::var("SYNTH_REFREEZE_PRINT").is_ok() {
            let hex: String = Sha256::digest(data)
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            println!("REPIN: (\"{wasm}\", \"{hex}\", {}),", data.len());
            continue;
        }
        assert_eq!(
            data.len(),
            golden_len,
            "{wasm}: SYNTH_RV_CMP_SELECT=0 must restore the pre-flip length"
        );
        let hex: String = Sha256::digest(data)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        assert_eq!(
            hex, golden,
            "{wasm}: SYNTH_RV_CMP_SELECT=0 must restore the pre-flip bytes (rollback broken)"
        );
    }
}

/// ESCAPE-HATCH GATE for the SYNTH_RV_LOCAL_PROMO flip (#472/#601):
/// `SYNTH_RV_LOCAL_PROMO=0` ALONE (every other lever at the shipped default)
/// must restore the pre-flip RV32 goldens byte-for-byte. Both pinned fixtures
/// are promo-NEUTRAL — the measured profitability gate declines promotion
/// everywhere in them, so pre-flip bytes == the current default goldens and
/// this doubles as the tripwire that (a) the opt-out stays a genuine no-op
/// here and (b) no promotion machinery leaks into the `=0` lowering. The
/// fixtures where the lever genuinely fires are locked by the corpus gate in
/// `rv32_local_promo_flip_472.rs` (default-vs-opt-out, no-grow + non-vacuity).
#[test]
fn frozen_fixtures_rv32_local_promo_escape_hatch_is_noop() {
    let cases = [
        (
            "control_step.wasm",
            "6ac5d7f94f3e17b0314aa2549e24b172b50dc0df110130c80a94e19d62c7b75b",
            484usize,
        ),
        (
            "signed_div_const.wasm",
            "15fa429d5ef5474f8b65fdd9c81b3da4c70176fb077df25131e2ec3988eb999e",
            88,
        ),
    ];
    for &(wasm, golden, golden_len) in &cases {
        let path = fixture(wasm);
        let elf = format!("/tmp/frozenbytes_rv32_promo_off_{wasm}.elf");
        let out = Command::new(synth())
            .env("SYNTH_RV_LOCAL_PROMO", "0")
            .env_remove("SYNTH_RV_CMP_SELECT")
            .env_remove("SYNTH_RV_SHIFT_FOLD")
            .args([
                "compile",
                path.to_str().unwrap(),
                "-o",
                &elf,
                "-b",
                "riscv",
                "--target",
                "rv32imac",
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
        if std::env::var("SYNTH_REFREEZE_PRINT").is_ok() {
            let hex: String = Sha256::digest(data)
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            println!("REPIN: (\"{wasm}\", \"{hex}\", {}),", data.len());
            continue;
        }
        assert_eq!(
            data.len(),
            golden_len,
            "{wasm}: SYNTH_RV_LOCAL_PROMO=0 must restore the pre-flip length"
        );
        let hex: String = Sha256::digest(data)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        assert_eq!(
            hex, golden,
            "{wasm}: SYNTH_RV_LOCAL_PROMO=0 must restore the pre-flip bytes (rollback broken)"
        );
    }
}
