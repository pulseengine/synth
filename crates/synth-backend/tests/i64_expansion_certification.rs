//! #667 move 2 — i64 pseudo-op expansion certification oracle.
//!
//! Feeds the **literal bytes this crate's Thumb-2 encoder emits** for each
//! covered i64 pseudo-op to `synth_verify::validate_expansion`, which decodes
//! them, symbolically executes the sequence (path conditions for the forward
//! branches, IT-block predication, the scratch push/pop stack model) and
//! discharges `UNSAT(wasm_op_semantics != sequence_semantics)` through the
//! certificate-checked solver.
//!
//! GREEN: every shipped expansion certifies (canonical + high-register
//! assignments).
//! RED: the literal #632 bug shape — the popcount result materialised into a
//! register inside the scratch-restore `POP {R3,R4,R5}` set — MUST fail
//! validation, as must a wrong-condition compare and a bit-count expansion
//! with its `+32` arm removed. A validator that stays green on those shapes
//! is vacuous.
//!
//! HELD OUT (loudly, not silently): `I64DivS/U`, `I64RemS/U` — their
//! expansions contain 64-round long-division loops (backward branches). The
//! validator reports them `Unsupported`/decode-error rather than certifying;
//! see `docs/validator-pattern.md` for the unrolling/invariant plan. This is
//! also why the #633 missing-overflow-guard shape is not yet expressible at
//! this layer (the guard lives inside the div expansion, and trap-guard
//! equivalence needs UDF-reachability modeling on top of loop support).

use synth_backend::ArmEncoder;
use synth_synthesis::rules::Condition;
use synth_synthesis::{ArmOp, Reg};
use synth_verify::{
    ExpansionError, covered_i64_pseudo_selections, validate_expansion, with_verification_context,
};

fn thumb_bytes(pseudo: &ArmOp) -> Vec<u8> {
    ArmEncoder::new_thumb2()
        .encode(pseudo)
        .expect("shipped encoder must encode the pseudo-op")
}

/// Every covered pseudo-op expansion, as emitted by the shipped encoder,
/// certifies against its WASM reference. One certificate line per op.
#[test]
fn shipped_expansions_certify() {
    with_verification_context(|| {
        for (wasm, pseudo) in covered_i64_pseudo_selections() {
            let code = thumb_bytes(&pseudo);
            match validate_expansion(&wasm, &pseudo, &code) {
                Ok(w) => {
                    println!(
                        "✓ certified {}: {} Thumb-2 instrs, {} bytes [unsat, LRAT-checked]",
                        w.wasm_op_label, w.instr_count, w.byte_len
                    );
                }
                Err(e) => panic!("shipped expansion for {wasm:?} failed validation: {e}"),
            }
        }
    });
}

/// High-register / allocator-shaped variants: the encodings change (CMP
/// high-reg form, MOV.W materialisation for rd >= R8 (#311), the #632 result
/// route through R12 for a destination inside the restore set) — all must
/// still certify.
#[test]
fn shipped_expansions_certify_high_register_variants() {
    with_verification_context(|| {
        let variants: Vec<(synth_core::WasmOp, ArmOp)> = vec![
            // rd = R8: exercises the 32-bit MOV.W materialisation (#311).
            (
                synth_core::WasmOp::I64LtS,
                ArmOp::I64SetCond {
                    rd: Reg::R8,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::LT,
                },
            ),
            (
                synth_core::WasmOp::I64Eqz,
                ArmOp::I64SetCondZ {
                    rd: Reg::R8,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                },
            ),
            // Non-canonical operand pairs.
            (
                synth_core::WasmOp::I64Mul,
                ArmOp::I64Mul {
                    rd_lo: Reg::R4,
                    rd_hi: Reg::R5,
                    rn_lo: Reg::R4,
                    rn_hi: Reg::R5,
                    rm_lo: Reg::R6,
                    rm_hi: Reg::R7,
                },
            ),
            // rd = R5 sits INSIDE the popcnt scratch-restore set {R3,R4,R5}
            // — the exact #632 trigger. The fixed expansion routes the count
            // through R12 across the POP, so this must certify.
            (
                synth_core::WasmOp::I64Popcnt,
                ArmOp::I64Popcnt {
                    rd: Reg::R5,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                },
            ),
        ];
        for (wasm, pseudo) in variants {
            let code = thumb_bytes(&pseudo);
            match validate_expansion(&wasm, &pseudo, &code) {
                Ok(w) => println!(
                    "✓ certified {} (variant): {} instrs, {} bytes",
                    w.wasm_op_label, w.instr_count, w.byte_len
                ),
                Err(e) => panic!("variant expansion for {wasm:?} failed validation: {e}"),
            }
        }
    });
}

/// RED — the literal #632 bug shape. The shipped fix computes the total into
/// R12, restores the scratch registers, and only then moves the result into
/// `rd`:
///
/// ```text
/// ADD.W R12, R4, R5      ; total, in a register POP cannot touch
/// POP   {R3, R4, R5}
/// MOV   rd, R12
/// MOV.W rnhi, #0
/// ```
///
/// The pre-fix encoder materialised the total straight into the allocator's
/// `rd` — which can land inside `{R3,R4,R5}` — and popped over it:
///
/// ```text
/// ADDS  R5, R4, R5       ; total ... in the restore set
/// POP   {R3, R4, R5}     ; total DESTROYED one instruction later
/// MOV   rd, R5           ; stale stack garbage
/// ```
///
/// Splicing that literal tail onto the shipped popcount body MUST produce a
/// counterexample: the validator models POP as restoring the pushed values,
/// so the returned "count" is the caller's dead R5 — wrong for almost every
/// input.
#[test]
fn red_632_popcnt_result_in_restore_set_fails() {
    with_verification_context(|| {
        let pseudo = ArmOp::I64Popcnt {
            rd: Reg::R0,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
        };
        let code = thumb_bytes(&pseudo);

        // The shipped tail (12 bytes): ADD.W R12,R4,R5; POP; MOV rd,R12;
        // MOV.W rnhi,#0. Pin it so this test screams if the encoder changes.
        let tail: Vec<u8> = [0xEB04u16, 0x0C05, 0xBC38, 0x4660, 0xF04F, 0x0100]
            .iter()
            .flat_map(|hw| hw.to_le_bytes())
            .collect();
        assert_eq!(
            &code[code.len() - 12..],
            &tail[..],
            "shipped popcnt tail changed — update the #632 red-shape splice"
        );

        // The #632 shape: ADDS R5,R4,R5 (0x1965); POP {R3,R4,R5}; MOV R0,R5
        // (0x4628); MOV.W R1,#0.
        let mut buggy = code[..code.len() - 12].to_vec();
        for hw in [0x1965u16, 0xBC38, 0x4628, 0xF04F, 0x0100] {
            buggy.extend_from_slice(&hw.to_le_bytes());
        }

        match validate_expansion(&synth_core::WasmOp::I64Popcnt, &pseudo, &buggy) {
            Err(ExpansionError::Counterexample {
                wasm_op_label,
                description,
            }) => {
                println!("✗ #632 shape rejected as required: {wasm_op_label}: {description}");
            }
            other => panic!(
                "#632 bug shape (popcnt result in the restore set) must FAIL validation, got {other:?}"
            ),
        }
    });
}

/// RED — wrong condition: `i64.lt_s` validated against the encoder's GE
/// sequence must produce a counterexample.
#[test]
fn red_wrong_condition_fails() {
    with_verification_context(|| {
        let pseudo = ArmOp::I64SetCond {
            rd: Reg::R0,
            rn_lo: Reg::R0,
            rn_hi: Reg::R1,
            rm_lo: Reg::R2,
            rm_hi: Reg::R3,
            cond: Condition::GE, // deliberately wrong for lt_s
        };
        let code = thumb_bytes(&pseudo);
        match validate_expansion(&synth_core::WasmOp::I64LtS, &pseudo, &code) {
            Err(ExpansionError::Counterexample { .. }) => {}
            other => panic!("lt_s vs GE sequence must FAIL validation, got {other:?}"),
        }
    });
}

/// RED — a Clz expansion whose `+32` arm is nulled (ADD.W rd, rd, #0) is a
/// wrong-value miscompile for every hi==0 input; must fail.
#[test]
fn red_clz_missing_plus32_fails() {
    with_verification_context(|| {
        let pseudo = ArmOp::I64Clz {
            rd: Reg::R0,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
        };
        let mut code = thumb_bytes(&pseudo);
        // Locate the ADD.W R0, R0, #32 (F100 0020) and zero the immediate.
        let pos = code
            .windows(4)
            .position(|w| w == [0x00, 0xF1, 0x20, 0x00])
            .expect("shipped clz expansion must contain ADD.W rd, rd, #32");
        code[pos + 2] = 0x00;
        match validate_expansion(&synth_core::WasmOp::I64Clz, &pseudo, &code) {
            Err(ExpansionError::Counterexample { .. }) => {}
            other => panic!("clz with nulled +32 arm must FAIL validation, got {other:?}"),
        }
    });
}

/// HELD OUT — the i64 division family is a loop (64-round long division);
/// the validator refuses it loudly instead of green-washing.
#[test]
fn div_family_is_held_out_loudly() {
    with_verification_context(|| {
        let pseudo = ArmOp::I64DivU {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
            rmlo: Reg::R2,
            rmhi: Reg::R3,
            elide_zero_guard: false,
        };
        let code = thumb_bytes(&pseudo);
        match validate_expansion(&synth_core::WasmOp::I64DivU, &pseudo, &code) {
            Err(ExpansionError::Unsupported(_)) | Err(ExpansionError::Decode { .. }) => {}
            other => panic!("i64.div_u must be held out loudly, got {other:?}"),
        }
    });
}
