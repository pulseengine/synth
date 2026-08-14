//! ISA-faithfulness tests for `synth_verify::ArmSemantics` (#923, step 2).
//!
//! # What these tests are for
//!
//! `arm_semantics.rs` is the ARM side of translation validation — the model
//! `synth-verify` consults to decide a lowering is correct. A bug here does not
//! produce a wrong program directly; it produces a **verifier that passes
//! something wrong**. #682 is the precedent in this repo: a green Qed against a
//! model that described `LSL (register)` with WASM's mod-32 masking instead of
//! ARMv7-M's `Rm<7:0>`. The proof was fine. The MODEL was unfaithful.
//!
//! So every assertion below is written against the **ARM architecture**, never
//! against the model's own output. Two disciplines make that concrete:
//!
//! * **Independent oracle.** Where a relation has a Rust equivalent (signed vs
//!   unsigned comparison, wrapping arithmetic, `count_ones`, `leading_zeros`,
//!   `reverse_bits`, IEEE-754 `<`), the expected value is computed by Rust and
//!   the model must agree. Rust is a second implementation, not a mirror.
//! * **Discriminating vectors.** A test that only exercises the easy range
//!   agrees with every plausible-but-wrong model. The vectors here are chosen to
//!   SEPARATE the ARM rule from the rules it is most often confused with — the
//!   shift-amount cases below distinguish `Rm<7:0>` from BOTH `Rm mod 32` and
//!   the raw 32-bit `Rm`, and the flag cases separate ARM's `C = NOT borrow`
//!   from the borrow polarity.
//!
//! Deliberately NOT asserted: any behaviour whose ARM answer and model answer
//! are known to differ under a documented exclusion. `SDIV`/`UDIV` by zero is
//! the case in point — ARM (with `DIV_0_TRP` clear) yields 0, SMT-LIB
//! `bvsdiv`/`bvudiv` by zero is total and yields something else, and WASM traps.
//! The value clause is asserted only on the non-trapping path, by the
//! trap-gated VC (`TranslationValidator::is_trap_gated_op`). Pinning either
//! answer here would convert a scoped exclusion into a false claim, so the
//! division tests stop at the edges where ARM, SMT and WASM all agree.
//!
//! References are to the ARMv7-M Architecture Reference Manual (DDI 0403E.b).

#![cfg(feature = "arm")]

use synth_synthesis::rules::Condition;
use synth_synthesis::{ArmOp, Operand2, Reg, VfpReg, WasmOp};
use synth_verify::{
    ArmSemantics, ArmState, BV, TranslationValidator, ValidationResult, with_verification_context,
};

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

/// Execute one op over concrete inputs and read a register back as `u32`.
fn run1(setup: &[(Reg, u32)], op: ArmOp, read: Reg) -> u32 {
    let e = ArmSemantics::new();
    let mut s = ArmState::new_symbolic();
    for (r, v) in setup {
        s.set_reg(r, BV::from_u64(*v as u64, 32));
    }
    e.encode_op(&op, &mut s);
    assert!(
        s.unmodeled.is_none(),
        "op left unmodeled by the ARM model: {:?}",
        s.unmodeled
    );
    s.get_reg(&read)
        .simplify()
        .as_u64()
        .expect("result did not simplify to a constant") as u32
}

/// Execute a sequence over concrete inputs and read a register back.
fn run_seq(setup: &[(Reg, u32)], ops: &[ArmOp], read: Reg) -> u32 {
    let e = ArmSemantics::new();
    let mut s = ArmState::new_symbolic();
    for (r, v) in setup {
        s.set_reg(r, BV::from_u64(*v as u64, 32));
    }
    for op in ops {
        e.encode_op(op, &mut s);
        assert!(
            s.unmodeled.is_none(),
            "op left unmodeled by the ARM model: {:?}",
            s.unmodeled
        );
    }
    s.get_reg(&read)
        .simplify()
        .as_u64()
        .expect("result did not simplify to a constant") as u32
}

/// NZCV after a flag-setting op over concrete inputs.
fn flags_after(setup: &[(Reg, u32)], op: ArmOp) -> (bool, bool, bool, bool) {
    let e = ArmSemantics::new();
    let mut s = ArmState::new_symbolic();
    for (r, v) in setup {
        s.set_reg(r, BV::from_u64(*v as u64, 32));
    }
    e.encode_op(&op, &mut s);
    assert!(s.unmodeled.is_none(), "flag op unmodeled: {:?}", s.unmodeled);
    (
        s.flags.n.simplify().as_bool().expect("N not concrete"),
        s.flags.z.simplify().as_bool().expect("Z not concrete"),
        s.flags.c.simplify().as_bool().expect("C not concrete"),
        s.flags.v.simplify().as_bool().expect("V not concrete"),
    )
}

/// `CMP rn, rm` then `SetCond(cond)` — the shipped comparison lowering.
fn cmp_setcond(a: u32, b: u32, cond: Condition) -> u32 {
    run_seq(
        &[(Reg::R1, a), (Reg::R2, b)],
        &[
            ArmOp::Cmp {
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            },
            ArmOp::SetCond { rd: Reg::R0, cond },
        ],
        Reg::R0,
    )
}

/// Run a VFP-compare pseudo-op through the trap-subset executor (the only
/// entry point that gives these ops their real bit-pattern semantics) and read
/// the 0/1 result.
fn vfp_cmp(regs: &[(VfpReg, u64)], op: ArmOp) -> u32 {
    let e = ArmSemantics::new();
    let mut s = ArmState::new_symbolic();
    for (r, v) in regs {
        let width = if matches!(
            r,
            VfpReg::D0
                | VfpReg::D1
                | VfpReg::D2
                | VfpReg::D3
                | VfpReg::D4
                | VfpReg::D5
                | VfpReg::D6
                | VfpReg::D7
        ) {
            64
        } else {
            32
        };
        s.set_vfp_reg(r, BV::from_u64(*v, width));
    }
    e.encode_sequence_value_straightline(&[op], &mut s)
        .expect("VFP compare declined by the trap-subset executor");
    s.get_reg(&Reg::R0)
        .simplify()
        .as_u64()
        .expect("compare result not concrete") as u32
}

// ===========================================================================
// 1. Register-amount shifts — the #682 class, in the file where it is decided
// ===========================================================================

/// ARMv7-M A7.7.68 (LSL register), A7.7.70 (LSR), A7.7.12 (ASR), A7.7.117
/// (ROR): every register form computes `shift_n = UInt(R[m]<7:0>)`.
///
/// The vectors here are chosen so that the three candidate rules give THREE
/// DIFFERENT answers, which is what makes this a faithfulness test rather than
/// a coverage test. With `Rn = 1`:
///
/// | `Rm`         | `Rm<7:0>` (ARM) | `Rm mod 32` | raw 32-bit `Rm` |
/// |--------------|-----------------|-------------|-----------------|
/// | `0x0000_0100`| 0   → `1`       | 0   → `1`   | 256 → `0`       |
/// | `0x0000_0120`| 32  → `0`       | 0   → `1`   | 288 → `0`       |
/// | `0x0000_0101`| 1   → `2`       | 1   → `2`   | 257 → `0`       |
///
/// `0x100` separates ARM from the raw-32 reading; `0x120` separates ARM from
/// the WASM mod-32 reading. Together they pin `<7:0>` exactly.
#[test]
fn lsl_register_masks_rm_low_eight_bits_not_mod_32_and_not_raw() {
    with_verification_context(|| {
        let lsl = |rn: u32, rm: u32| {
            run1(
                &[(Reg::R1, rn), (Reg::R2, rm)],
                ArmOp::LslReg {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    rm: Reg::R2,
                },
                Reg::R0,
            )
        };

        // The discriminating triple.
        assert_eq!(lsl(1, 0x0000_0100), 1, "Rm<7:0> = 0 is a shift by ZERO");
        assert_eq!(lsl(1, 0x0000_0120), 0, "Rm<7:0> = 32 shifts everything out");
        assert_eq!(lsl(1, 0x0000_0101), 2, "Rm<7:0> = 1");

        // In-range agreement with a wrapping Rust shift.
        for rn in [1u32, 0xFFFF_FFFF, 0x8000_0001, 0x1234_5678] {
            for amount in 0u32..32 {
                assert_eq!(
                    lsl(rn, amount),
                    rn << amount,
                    "LSL {rn:#010x} by {amount}"
                );
                // High bits of Rm above bit 7 must not participate.
                assert_eq!(
                    lsl(rn, amount | 0xFFFF_FF00),
                    lsl(rn, amount),
                    "bits 31:8 of Rm must not affect LSL"
                );
            }
        }

        // shift_n in 32..=255 clears the register (A7.7.68: LSL_C over an
        // arbitrarily wide intermediate, truncated to 32 bits).
        for amount in [32u32, 33, 64, 200, 255] {
            assert_eq!(lsl(0xFFFF_FFFF, amount), 0, "LSL by {amount} yields 0");
        }
    });
}

#[test]
fn lsr_register_masks_rm_low_eight_bits() {
    with_verification_context(|| {
        let lsr = |rn: u32, rm: u32| {
            run1(
                &[(Reg::R1, rn), (Reg::R2, rm)],
                ArmOp::LsrReg {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    rm: Reg::R2,
                },
                Reg::R0,
            )
        };

        assert_eq!(lsr(0x8000_0000, 0x0000_0100), 0x8000_0000, "shift by zero");
        assert_eq!(lsr(0x8000_0000, 0x0000_0120), 0, "shift_n = 32 yields 0");

        for rn in [0x8000_0000u32, 0xFFFF_FFFF, 0x1234_5678] {
            for amount in 0u32..32 {
                assert_eq!(lsr(rn, amount), rn >> amount, "LSR {rn:#010x} by {amount}");
                assert_eq!(lsr(rn, amount | 0x0000_FF00), lsr(rn, amount));
            }
        }
        for amount in [32u32, 100, 255] {
            assert_eq!(lsr(0xFFFF_FFFF, amount), 0);
        }
    });
}

/// ASR differs from LSL/LSR out of range: `shift_n >= 32` yields a SIGN FILL,
/// not zero (A7.7.12, `ASR_C`).
#[test]
fn asr_register_sign_fills_beyond_31_and_masks_rm_low_eight_bits() {
    with_verification_context(|| {
        let asr = |rn: u32, rm: u32| {
            run1(
                &[(Reg::R1, rn), (Reg::R2, rm)],
                ArmOp::AsrReg {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    rm: Reg::R2,
                },
                Reg::R0,
            )
        };

        assert_eq!(asr(0x8000_0000, 0x0000_0100), 0x8000_0000, "shift by zero");

        for amount in [32u32, 33, 255] {
            assert_eq!(
                asr(0x8000_0000, amount),
                0xFFFF_FFFF,
                "negative operand sign-fills at shift_n = {amount}"
            );
            assert_eq!(
                asr(0x7FFF_FFFF, amount),
                0,
                "positive operand zero-fills at shift_n = {amount}"
            );
        }

        for rn in [0x8000_0000u32, 0x7FFF_FFFF, 0xFFFF_FFFF, 0x1234_5678] {
            for amount in 0u32..32 {
                assert_eq!(
                    asr(rn, amount),
                    ((rn as i32) >> amount) as u32,
                    "ASR {rn:#010x} by {amount}"
                );
                assert_eq!(asr(rn, amount | 0xFF00), asr(rn, amount));
            }
        }
    });
}

/// ROR is the one register-shift form where `<7:0>` and the full `Rm` agree —
/// rotation has period 32 and 256 is a multiple of 32. Pinned anyway so a
/// future reader does not have to re-derive why this arm is allowed to differ
/// from its three siblings.
#[test]
fn ror_register_rotates_by_rm_low_eight_bits() {
    with_verification_context(|| {
        let ror = |rn: u32, rm: u32| {
            run1(
                &[(Reg::R1, rn), (Reg::R2, rm)],
                ArmOp::RorReg {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    rm: Reg::R2,
                },
                Reg::R0,
            )
        };

        assert_eq!(ror(0x1234_5678, 4), 0x8123_4567);
        assert_eq!(ror(0x1234_5678, 0x0000_0100), 0x1234_5678, "rotate by zero");
        assert_eq!(ror(0x1234_5678, 36), ror(0x1234_5678, 4), "period 32");

        for rn in [0x1234_5678u32, 0x8000_0001, 0xFFFF_FFFF] {
            for amount in 0u32..64 {
                assert_eq!(
                    ror(rn, amount),
                    rn.rotate_right(amount % 32),
                    "ROR {rn:#010x} by {amount}"
                );
            }
        }
    });
}

/// `RSB Rd, Rn, #imm` is `Rd = imm - Rn` (A7.7.119) — the amount negation the
/// shipped `i32.rotl` lowering uses. It was on the trap subset's delegate
/// allowlist while `encode_op` had no arm for it (#923).
#[test]
fn rsb_immediate_is_imm_minus_rn() {
    with_verification_context(|| {
        let rsb = |rn: u32, imm: u32| {
            run1(
                &[(Reg::R1, rn)],
                ArmOp::Rsb {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    imm,
                },
                Reg::R0,
            )
        };
        assert_eq!(rsb(5, 32), 27);
        assert_eq!(rsb(0, 0), 0);
        assert_eq!(rsb(1, 0), 0xFFFF_FFFF, "0 - 1 wraps");
        assert_eq!(rsb(0x8000_0000, 0), 0x8000_0000, "0 - INT_MIN wraps to itself");
        for rn in [0u32, 1, 31, 0x7FFF_FFFF, 0x8000_0000, 0xFFFF_FFFF] {
            assert_eq!(rsb(rn, 32), 32u32.wrapping_sub(rn));
        }
    });
}

/// Byte/halfword extension (A7.7.166/.168/.217/.219, rotation 0).
#[test]
fn sign_and_zero_extension_take_the_low_byte_or_halfword() {
    with_verification_context(|| {
        let ext = |op: fn(Reg, Reg) -> ArmOp, rm: u32| {
            run1(&[(Reg::R1, rm)], op(Reg::R0, Reg::R1), Reg::R0)
        };
        let sxtb = |rd, rm| ArmOp::Sxtb { rd, rm };
        let sxth = |rd, rm| ArmOp::Sxth { rd, rm };
        let uxtb = |rd, rm| ArmOp::Uxtb { rd, rm };
        let uxth = |rd, rm| ArmOp::Uxth { rd, rm };

        for v in [
            0x0000_0000u32,
            0x0000_007F,
            0x0000_0080,
            0x0000_00FF,
            0x0000_7FFF,
            0x0000_8000,
            0xDEAD_BEEF,
            0xFFFF_FFFF,
        ] {
            assert_eq!(ext(sxtb, v), ((v as u8) as i8 as i32) as u32, "SXTB {v:#010x}");
            assert_eq!(
                ext(sxth, v),
                ((v as u16) as i16 as i32) as u32,
                "SXTH {v:#010x}"
            );
            assert_eq!(ext(uxtb, v), v & 0xFF, "UXTB {v:#010x}");
            assert_eq!(ext(uxth, v), v & 0xFFFF, "UXTH {v:#010x}");
        }
    });
}

/// `MOVW` writes the whole register (top halfword ZEROED); `MOVT` writes bits
/// 31:16 and PRESERVES 15:0 (A7.7.76/.79). The pair is the shipped 32-bit
/// constant idiom, so getting MOVT's preservation wrong would model it as
/// producing only the high half.
#[test]
fn movw_movt_materialize_a_32_bit_constant() {
    with_verification_context(|| {
        for value in [
            0x0000_0000u32,
            0x0000_FFFF,
            0xFFFF_0000,
            0xDEAD_BEEF,
            0x2000_0100,
        ] {
            let got = run_seq(
                &[(Reg::R0, 0xAAAA_AAAA)], // prior contents must not survive
                &[
                    ArmOp::Movw {
                        rd: Reg::R0,
                        imm16: value as u16,
                    },
                    ArmOp::Movt {
                        rd: Reg::R0,
                        imm16: (value >> 16) as u16,
                    },
                ],
                Reg::R0,
            );
            assert_eq!(got, value, "MOVW/MOVT for {value:#010x}");
        }

        // MOVW alone must ZERO the top half, not merge into it.
        assert_eq!(
            run_seq(
                &[(Reg::R0, 0xFFFF_FFFF)],
                &[ArmOp::Movw {
                    rd: Reg::R0,
                    imm16: 0x1234
                }],
                Reg::R0,
            ),
            0x0000_1234,
        );
        // MOVT alone must PRESERVE the bottom half.
        assert_eq!(
            run_seq(
                &[(Reg::R0, 0x0000_5678)],
                &[ArmOp::Movt {
                    rd: Reg::R0,
                    imm16: 0x1234
                }],
                Reg::R0,
            ),
            0x1234_5678,
        );
    });
}

// ===========================================================================
// 2. Condition flags — ARM polarity, not "some consistent polarity"
// ===========================================================================

/// `CMP Rn, Rm` computes `Rn - Rm` and sets NZCV from
/// `AddWithCarry(Rn, NOT(Rm), '1')` (A7.7.27). The consequential half is the
/// carry: on ARM `C = 1` means NO BORROW, i.e. `Rn >=u Rm`. Inverting it is the
/// classic bug, and it would silently flip every `HS`/`LO`/`HI`/`LS`
/// comparison the selector emits.
#[test]
fn cmp_sets_arm_flag_polarity_including_carry_is_not_borrow() {
    with_verification_context(|| {
        let cmp = |a: u32, b: u32| {
            flags_after(
                &[(Reg::R1, a), (Reg::R2, b)],
                ArmOp::Cmp {
                    rn: Reg::R1,
                    op2: Operand2::Reg(Reg::R2),
                },
            )
        };

        //                                        (N,     Z,     C,     V)
        assert_eq!(cmp(5, 3), (false, false, true, false), "5 - 3");
        assert_eq!(cmp(3, 5), (true, false, false, false), "3 - 5 borrows");
        assert_eq!(cmp(5, 5), (false, true, true, false), "equal: Z=1, C=1");
        assert_eq!(cmp(0, 1), (true, false, false, false), "0 - 1 borrows");
        assert_eq!(cmp(0, 0), (false, true, true, false));

        // Signed-overflow edges.
        assert_eq!(
            cmp(0x8000_0000, 1),
            (false, false, true, true),
            "INT_MIN - 1 overflows: V=1, result positive so N=0"
        );
        assert_eq!(
            cmp(0x7FFF_FFFF, 0xFFFF_FFFF),
            (true, false, false, true),
            "INT_MAX - (-1) overflows: V=1, result negative"
        );
        assert_eq!(
            cmp(0x8000_0000, 0xFFFF_FFFF),
            (true, false, false, false),
            "INT_MIN - (-1): same signs, no signed overflow; borrows unsigned"
        );

        // Exhaustive cross-check of all four flags against an independent
        // Rust computation, over a grid that includes every sign combination.
        let grid = [
            0u32,
            1,
            2,
            0x7FFF_FFFE,
            0x7FFF_FFFF,
            0x8000_0000,
            0x8000_0001,
            0xFFFF_FFFE,
            0xFFFF_FFFF,
        ];
        for &a in &grid {
            for &b in &grid {
                let r = a.wrapping_sub(b);
                let expected = (
                    (r >> 31) == 1,
                    r == 0,
                    a >= b, // C = NOT borrow
                    (a as i32).checked_sub(b as i32).is_none(),
                );
                assert_eq!(cmp(a, b), expected, "CMP {a:#010x}, {b:#010x}");
            }
        }
    });
}

/// `CMN Rn, op2` sets the flags of `Rn + op2` (A7.7.25). It drives the
/// `i32.div_s` INT_MIN/-1 overflow guard (`CMN Rm, #1` is "is the divisor
/// −1?"), so a wrong C or V here is a wrong TRAP condition, not just a wrong
/// value. `update_flags_add` had zero test coverage before #923.
#[test]
fn cmn_sets_addition_flags_and_drives_the_div_s_overflow_guard() {
    with_verification_context(|| {
        let cmn = |a: u32, imm: i32| {
            flags_after(
                &[(Reg::R1, a)],
                ArmOp::Cmn {
                    rn: Reg::R1,
                    op2: Operand2::Imm(imm),
                },
            )
        };

        // The shipped guard idiom: Z is set exactly when Rn == -1.
        assert_eq!(cmn(0xFFFF_FFFF, 1).1, true, "CMN -1, #1 sets Z");
        for other in [0u32, 1, 2, 0x8000_0000, 0x7FFF_FFFF, 0xFFFF_FFFE] {
            assert_eq!(cmn(other, 1).1, false, "CMN {other:#010x}, #1 must not set Z");
        }

        // Carry out of the unsigned addition.
        assert_eq!(cmn(0xFFFF_FFFF, 1).2, true, "-1 + 1 carries out");
        assert_eq!(cmn(1, 1).2, false, "1 + 1 does not carry out");

        // Signed overflow.
        assert_eq!(
            cmn(0x7FFF_FFFF, 1),
            (true, false, false, true),
            "INT_MAX + 1 overflows to INT_MIN"
        );

        let grid = [0u32, 1, 2, 0x7FFF_FFFF, 0x8000_0000, 0xFFFF_FFFF];
        for &a in &grid {
            for imm in [0i32, 1, -1, 2] {
                let b = imm as u32;
                let r = a.wrapping_add(b);
                let expected = (
                    (r >> 31) == 1,
                    r == 0,
                    (a as u64 + b as u64) > 0xFFFF_FFFF, // carry out
                    (a as i32).checked_add(imm).is_none(),
                );
                assert_eq!(cmn(a, imm), expected, "CMN {a:#010x}, #{imm}");
            }
        }
    });
}

/// The condition codes themselves (A7.3, table A7-1): `HS`/`LO`/`HI`/`LS` read
/// `C` (unsigned), `GE`/`LT`/`GT`/`LE` read `N`/`V` (signed). Confusing the two
/// families is the other classic bug, and it is invisible unless a vector
/// exists where the signed and unsigned answers DIFFER — `CMP 1, -1` is that
/// vector, and the grid below is full of them.
#[test]
fn setcond_after_cmp_matches_the_arm_condition_table() {
    with_verification_context(|| {
        // The one that separates the families, spelled out.
        assert_eq!(cmp_setcond(1, 0xFFFF_FFFF, Condition::GT), 1, "1 >s -1");
        assert_eq!(cmp_setcond(1, 0xFFFF_FFFF, Condition::HI), 0, "1 <u 0xFFFFFFFF");
        assert_eq!(cmp_setcond(1, 0xFFFF_FFFF, Condition::LT), 0);
        assert_eq!(cmp_setcond(1, 0xFFFF_FFFF, Condition::LO), 1);

        let grid = [
            0u32,
            1,
            2,
            0x7FFF_FFFE,
            0x7FFF_FFFF,
            0x8000_0000,
            0x8000_0001,
            0xFFFF_FFFE,
            0xFFFF_FFFF,
        ];
        for &a in &grid {
            for &b in &grid {
                let (sa, sb) = (a as i32, b as i32);
                for (cond, want) in [
                    (Condition::EQ, a == b),
                    (Condition::NE, a != b),
                    (Condition::LT, sa < sb),
                    (Condition::LE, sa <= sb),
                    (Condition::GT, sa > sb),
                    (Condition::GE, sa >= sb),
                    (Condition::LO, a < b),
                    (Condition::LS, a <= b),
                    (Condition::HI, a > b),
                    (Condition::HS, a >= b),
                ] {
                    assert_eq!(
                        cmp_setcond(a, b, cond),
                        want as u32,
                        "CMP {a:#010x}, {b:#010x} ; SetCond({cond:?})"
                    );
                }
            }
        }
    });
}

// ===========================================================================
// 3. Arithmetic edges
// ===========================================================================

/// `SDIV` truncates toward zero, and `INT_MIN / -1` yields `INT_MIN` on ARM
/// (A7.7.126) — the overflow case WASM traps on and the one SMT-LIB `bvsdiv`
/// agrees with by wrapping. Division by zero is deliberately NOT asserted; see
/// this file's header.
#[test]
fn sdiv_truncates_toward_zero_and_wraps_at_int_min_over_minus_one() {
    with_verification_context(|| {
        let sdiv = |a: u32, b: u32| {
            run1(
                &[(Reg::R1, a), (Reg::R2, b)],
                ArmOp::Sdiv {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    rm: Reg::R2,
                },
                Reg::R0,
            )
        };
        assert_eq!(
            sdiv(0x8000_0000, 0xFFFF_FFFF),
            0x8000_0000,
            "INT_MIN / -1 wraps to INT_MIN"
        );
        for (a, b) in [
            (7i32, 2i32),
            (-7, 2),
            (7, -2),
            (-7, -2),
            (1, 1),
            (i32::MIN, 2),
            (i32::MAX, -1),
            (0, 5),
        ] {
            assert_eq!(
                sdiv(a as u32, b as u32),
                a.wrapping_div(b) as u32,
                "SDIV {a} / {b} truncates toward zero"
            );
        }
    });
}

#[test]
fn udiv_and_mls_form_the_remainder_idiom() {
    with_verification_context(|| {
        for (a, b) in [(7u32, 2u32), (0, 5), (0xFFFF_FFFF, 3), (1, 0xFFFF_FFFF)] {
            let q = run1(
                &[(Reg::R1, a), (Reg::R2, b)],
                ArmOp::Udiv {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    rm: Reg::R2,
                },
                Reg::R0,
            );
            assert_eq!(q, a / b, "UDIV {a} / {b}");

            // MLS Rd, Rn, Rm, Ra  ->  Rd = Ra - Rn*Rm (A7.7.75): a - q*b.
            let r = run_seq(
                &[(Reg::R1, q), (Reg::R2, b), (Reg::R3, a)],
                &[ArmOp::Mls {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    rm: Reg::R2,
                    ra: Reg::R3,
                }],
                Reg::R0,
            );
            assert_eq!(r, a % b, "MLS remainder for {a} % {b}");
        }
    });
}

/// `UMULL RdLo, RdHi, Rn, Rm` is the full 64-bit unsigned product (A7.7.204);
/// the high word is what the reciprocal-multiply lowerings consume, so a model
/// that dropped it would bless any of them.
#[test]
fn umull_produces_the_full_64_bit_unsigned_product() {
    with_verification_context(|| {
        for (a, b) in [
            (0xFFFF_FFFFu32, 0xFFFF_FFFFu32),
            (0x1234_5678, 0x9ABC_DEF0),
            (1, 0xFFFF_FFFF),
            (0, 0xFFFF_FFFF),
            (0x8000_0000, 2),
        ] {
            let e = ArmSemantics::new();
            let mut s = ArmState::new_symbolic();
            s.set_reg(&Reg::R2, BV::from_u64(a as u64, 32));
            s.set_reg(&Reg::R3, BV::from_u64(b as u64, 32));
            e.encode_op(
                &ArmOp::Umull {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rn: Reg::R2,
                    rm: Reg::R3,
                },
                &mut s,
            );
            let lo = s.get_reg(&Reg::R0).simplify().as_u64().unwrap();
            let hi = s.get_reg(&Reg::R1).simplify().as_u64().unwrap();
            let want = (a as u64) * (b as u64);
            assert_eq!(lo, want & 0xFFFF_FFFF, "UMULL low word {a:#x}*{b:#x}");
            assert_eq!(hi, want >> 32, "UMULL high word {a:#x}*{b:#x}");
        }
    });
}

/// `CLZ` (A7.7.24), `RBIT` (A7.7.112) and the population-count pseudo-op,
/// against Rust's own bit intrinsics.
#[test]
fn bit_counting_ops_match_the_rust_intrinsics() {
    with_verification_context(|| {
        let vals = [
            0u32,
            1,
            2,
            3,
            0x8000_0000,
            0x8000_0001,
            0x0000_FFFF,
            0xFFFF_0000,
            0xFFFF_FFFF,
            0xDEAD_BEEF,
            0x0000_0100,
        ];
        for v in vals {
            assert_eq!(
                run1(
                    &[(Reg::R1, v)],
                    ArmOp::Clz {
                        rd: Reg::R0,
                        rm: Reg::R1
                    },
                    Reg::R0
                ),
                v.leading_zeros(),
                "CLZ {v:#010x}"
            );
            assert_eq!(
                run1(
                    &[(Reg::R1, v)],
                    ArmOp::Rbit {
                        rd: Reg::R0,
                        rm: Reg::R1
                    },
                    Reg::R0
                ),
                v.reverse_bits(),
                "RBIT {v:#010x}"
            );
            assert_eq!(
                run1(
                    &[(Reg::R1, v)],
                    ArmOp::Popcnt {
                        rd: Reg::R0,
                        rm: Reg::R1
                    },
                    Reg::R0
                ),
                v.count_ones(),
                "POPCNT {v:#010x}"
            );
        }
        // CLZ of zero is 32, the edge every hand-rolled binary search gets
        // wrong first.
        assert_eq!(
            run1(
                &[(Reg::R1, 0)],
                ArmOp::Clz {
                    rd: Reg::R0,
                    rm: Reg::R1
                },
                Reg::R0
            ),
            32
        );
    });
}

// ===========================================================================
// 4. 64-bit register pairs
// ===========================================================================

/// The `ADDS`/`ADC` and `SUBS`/`SBC` carry chains: the low word's carry-out
/// must reach the high word. Checked against 64-bit Rust arithmetic.
#[test]
fn i64_add_and_sub_propagate_carry_and_borrow_across_the_pair() {
    with_verification_context(|| {
        let pairs: [(u64, u64); 7] = [
            (0x0000_0000_FFFF_FFFF, 0x0000_0000_0000_0001), // carry into high
            (0x0000_0000_0000_0000, 0x0000_0000_0000_0000),
            (0xFFFF_FFFF_FFFF_FFFF, 0x0000_0000_0000_0001), // wraps to zero
            (0x1234_5678_9ABC_DEF0, 0x0FED_CBA9_8765_4321),
            (0x0000_0001_0000_0000, 0x0000_0000_0000_0001),
            (0x8000_0000_0000_0000, 0x8000_0000_0000_0000),
            (0x0000_0000_0000_0001, 0x0000_0000_FFFF_FFFF), // borrow out of low
        ];
        for (n, m) in pairs {
            let (nlo, nhi) = (n as u32, (n >> 32) as u32);
            let (mlo, mhi) = (m as u32, (m >> 32) as u32);
            let e = ArmSemantics::new();

            for (op, want) in [
                (
                    ArmOp::I64Add {
                        rdlo: Reg::R0,
                        rdhi: Reg::R1,
                        rnlo: Reg::R2,
                        rnhi: Reg::R3,
                        rmlo: Reg::R4,
                        rmhi: Reg::R5,
                    },
                    n.wrapping_add(m),
                ),
                (
                    ArmOp::I64Sub {
                        rdlo: Reg::R0,
                        rdhi: Reg::R1,
                        rnlo: Reg::R2,
                        rnhi: Reg::R3,
                        rmlo: Reg::R4,
                        rmhi: Reg::R5,
                    },
                    n.wrapping_sub(m),
                ),
            ] {
                let mut s = ArmState::new_symbolic();
                for (r, v) in [
                    (Reg::R2, nlo),
                    (Reg::R3, nhi),
                    (Reg::R4, mlo),
                    (Reg::R5, mhi),
                ] {
                    s.set_reg(&r, BV::from_u64(v as u64, 32));
                }
                e.encode_op(&op, &mut s);
                let lo = s.get_reg(&Reg::R0).simplify().as_u64().unwrap();
                let hi = s.get_reg(&Reg::R1).simplify().as_u64().unwrap();
                assert_eq!(
                    (hi << 32) | lo,
                    want,
                    "{op:?} over {n:#018x} and {m:#018x}"
                );
            }
        }
    });
}

/// The lexicographic 64-bit comparisons. The load-bearing detail is that the
/// LOW-word tiebreak is UNSIGNED even for the SIGNED comparison: using a signed
/// compare on the low word makes `0x0000_0000_8000_0000` compare LESS than
/// `0x0000_0000_0000_0001`, which is the vector below.
#[test]
fn i64_comparisons_are_lexicographic_with_an_unsigned_low_word() {
    with_verification_context(|| {
        let cmp64 = |op: ArmOp, n: u64, m: u64| -> u32 {
            let e = ArmSemantics::new();
            let mut s = ArmState::new_symbolic();
            for (r, v) in [
                (Reg::R2, n as u32),
                (Reg::R3, (n >> 32) as u32),
                (Reg::R4, m as u32),
                (Reg::R5, (m >> 32) as u32),
            ] {
                s.set_reg(&r, BV::from_u64(v as u64, 32));
            }
            e.encode_op(&op, &mut s);
            assert!(s.unmodeled.is_none());
            s.get_reg(&Reg::R0).simplify().as_u64().unwrap() as u32
        };
        let lt_s = ArmOp::I64LtS {
            rd: Reg::R0,
            rnlo: Reg::R2,
            rnhi: Reg::R3,
            rmlo: Reg::R4,
            rmhi: Reg::R5,
        };
        let lt_u = ArmOp::I64LtU {
            rd: Reg::R0,
            rnlo: Reg::R2,
            rnhi: Reg::R3,
            rmlo: Reg::R4,
            rmhi: Reg::R5,
        };
        let eq = ArmOp::I64Eq {
            rd: Reg::R0,
            rnlo: Reg::R2,
            rnhi: Reg::R3,
            rmlo: Reg::R4,
            rmhi: Reg::R5,
        };

        // High words equal, low word has its top bit set: unsigned tiebreak.
        assert_eq!(
            cmp64(lt_s.clone(), 0x0000_0000_8000_0000, 0x0000_0000_0000_0001),
            0,
            "low-word tiebreak must be UNSIGNED"
        );

        let vals: [u64; 8] = [
            0,
            1,
            0x0000_0000_8000_0000,
            0x0000_0000_FFFF_FFFF,
            0x0000_0001_0000_0000,
            0x7FFF_FFFF_FFFF_FFFF,
            0x8000_0000_0000_0000,
            0xFFFF_FFFF_FFFF_FFFF,
        ];
        for &n in &vals {
            for &m in &vals {
                assert_eq!(
                    cmp64(lt_s.clone(), n, m),
                    ((n as i64) < (m as i64)) as u32,
                    "i64.lt_s {n:#018x} {m:#018x}"
                );
                assert_eq!(
                    cmp64(lt_u.clone(), n, m),
                    (n < m) as u32,
                    "i64.lt_u {n:#018x} {m:#018x}"
                );
                assert_eq!(
                    cmp64(eq.clone(), n, m),
                    (n == m) as u32,
                    "i64.eq {n:#018x} {m:#018x}"
                );
            }
        }
    });
}

/// `I64RemU`/`I64RemS` are modeled with native 64-bit remainders (#825/#836)
/// rather than havoc, so they can carry a real value obligation. Checked
/// against Rust; the ÷0 case is excluded for the same reason as `SDIV`.
#[test]
fn i64_remainders_match_native_64_bit_arithmetic() {
    with_verification_context(|| {
        let rem = |op: ArmOp, n: u64, m: u64| -> u64 {
            let e = ArmSemantics::new();
            let mut s = ArmState::new_symbolic();
            for (r, v) in [
                (Reg::R2, n as u32),
                (Reg::R3, (n >> 32) as u32),
                (Reg::R4, m as u32),
                (Reg::R5, (m >> 32) as u32),
            ] {
                s.set_reg(&r, BV::from_u64(v as u64, 32));
            }
            e.encode_op(&op, &mut s);
            assert!(s.unmodeled.is_none());
            let lo = s.get_reg(&Reg::R0).simplify().as_u64().unwrap();
            let hi = s.get_reg(&Reg::R1).simplify().as_u64().unwrap();
            (hi << 32) | lo
        };
        let mk = |signed: bool| {
            if signed {
                ArmOp::I64RemS {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R2,
                    rnhi: Reg::R3,
                    rmlo: Reg::R4,
                    rmhi: Reg::R5,
                    elide_zero_guard: false,
                }
            } else {
                ArmOp::I64RemU {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R2,
                    rnhi: Reg::R3,
                    rmlo: Reg::R4,
                    rmhi: Reg::R5,
                    elide_zero_guard: false,
                }
            }
        };
        for (n, m) in [
            (17u64, 5u64),
            (0, 7),
            (0xFFFF_FFFF_FFFF_FFFF, 3),
            (0x8000_0000_0000_0000, 2),
            (1, 0xFFFF_FFFF_FFFF_FFFF),
        ] {
            assert_eq!(rem(mk(false), n, m), n % m, "i64.rem_u {n:#x} % {m:#x}");
        }
        // rem_s follows the sign of the dividend (WASM and SMT-LIB agree);
        // rem_s(INT64_MIN, -1) == 0 with no overflow trap.
        for (n, m) in [
            (17i64, 5i64),
            (-17, 5),
            (17, -5),
            (-17, -5),
            (i64::MIN, -1),
            (i64::MIN, 2),
        ] {
            assert_eq!(
                rem(mk(true), n as u64, m as u64) as i64,
                n.wrapping_rem(m),
                "i64.rem_s {n} % {m}"
            );
        }
    });
}

// ===========================================================================
// 5. VFP ordered compares — the trunc-guard trap derivation (#709 / #756)
// ===========================================================================

/// The `F32Lt`/`F32Gt`/`F32Ge` pseudo-ops stand for `VCMP.F32` + `VMRS` + `IT`,
/// and their result is what the `i32.trunc_f32_*` guard branches on. IEEE 754
/// says every ordered relation is FALSE when either operand is NaN, `+0.0` and
/// `-0.0` compare EQUAL despite different bit patterns, and negative floats
/// order by DECREASING magnitude — three properties a bit-pattern comparison
/// gets wrong unless it is written for them. A wrong answer here is a dropped
/// or spurious TRAP, not a wrong value.
#[test]
fn f32_ordered_compares_follow_ieee754_including_nan_and_signed_zero() {
    with_verification_context(|| {
        let bits = |x: f32| x.to_bits() as u64;
        let lt = |a: f32, b: f32| {
            vfp_cmp(
                &[(VfpReg::S1, bits(a)), (VfpReg::S2, bits(b))],
                ArmOp::F32Lt {
                    rd: Reg::R0,
                    sn: VfpReg::S1,
                    sm: VfpReg::S2,
                },
            )
        };
        let gt = |a: f32, b: f32| {
            vfp_cmp(
                &[(VfpReg::S1, bits(a)), (VfpReg::S2, bits(b))],
                ArmOp::F32Gt {
                    rd: Reg::R0,
                    sn: VfpReg::S1,
                    sm: VfpReg::S2,
                },
            )
        };
        let ge = |a: f32, b: f32| {
            vfp_cmp(
                &[(VfpReg::S1, bits(a)), (VfpReg::S2, bits(b))],
                ArmOp::F32Ge {
                    rd: Reg::R0,
                    sn: VfpReg::S1,
                    sm: VfpReg::S2,
                },
            )
        };

        // NaN: every ordered relation is false, INCLUDING `Ge`, which a
        // `!(a < b)` implementation would wrongly report as true.
        for other in [0.0f32, 1.0, -1.0, f32::INFINITY, f32::NEG_INFINITY] {
            assert_eq!(lt(f32::NAN, other), 0, "NaN < {other} is false");
            assert_eq!(gt(f32::NAN, other), 0, "NaN > {other} is false");
            assert_eq!(ge(f32::NAN, other), 0, "NaN >= {other} is false");
            assert_eq!(lt(other, f32::NAN), 0);
            assert_eq!(gt(other, f32::NAN), 0);
            assert_eq!(ge(other, f32::NAN), 0, "{other} >= NaN is false");
        }

        // Signed zero: different bit patterns, equal values.
        assert_eq!(lt(-0.0, 0.0), 0, "-0.0 < +0.0 is false");
        assert_eq!(gt(0.0, -0.0), 0, "+0.0 > -0.0 is false");
        assert_eq!(ge(-0.0, 0.0), 1, "-0.0 >= +0.0 is true");
        assert_eq!(ge(0.0, -0.0), 1);

        // Negatives order by decreasing magnitude.
        assert_eq!(lt(-2.0, -1.0), 1, "-2.0 < -1.0");
        assert_eq!(lt(-1.0, -2.0), 0);

        // Exhaustive cross-check against Rust's own f32 comparison.
        let vals = [
            0.0f32,
            -0.0,
            1.0,
            -1.0,
            2.0,
            -2.0,
            f32::MIN_POSITIVE,
            -f32::MIN_POSITIVE,
            f32::MAX,
            f32::MIN,
            f32::INFINITY,
            f32::NEG_INFINITY,
            f32::NAN,
        ];
        for &a in &vals {
            for &b in &vals {
                assert_eq!(lt(a, b), (a < b) as u32, "f32 {a} < {b}");
                assert_eq!(gt(a, b), (a > b) as u32, "f32 {a} > {b}");
                assert_eq!(ge(a, b), (a >= b) as u32, "f32 {a} >= {b}");
            }
        }
    });
}

/// The 64-bit twins (`#756`, the `i32.trunc_f64_*` and `i64.trunc_f64_*`
/// guards), same properties over the wider format.
#[test]
fn f64_ordered_compares_follow_ieee754_including_nan_and_signed_zero() {
    with_verification_context(|| {
        let bits = |x: f64| x.to_bits();
        let cmp = |kind: u8, a: f64, b: f64| {
            let op = match kind {
                0 => ArmOp::F64Lt {
                    rd: Reg::R0,
                    dn: VfpReg::D1,
                    dm: VfpReg::D2,
                },
                1 => ArmOp::F64Gt {
                    rd: Reg::R0,
                    dn: VfpReg::D1,
                    dm: VfpReg::D2,
                },
                _ => ArmOp::F64Ge {
                    rd: Reg::R0,
                    dn: VfpReg::D1,
                    dm: VfpReg::D2,
                },
            };
            vfp_cmp(&[(VfpReg::D1, bits(a)), (VfpReg::D2, bits(b))], op)
        };

        for other in [0.0f64, 1.0, -1.0, f64::INFINITY, f64::NEG_INFINITY] {
            for kind in 0..3u8 {
                assert_eq!(cmp(kind, f64::NAN, other), 0, "NaN vs {other}, kind {kind}");
                assert_eq!(cmp(kind, other, f64::NAN), 0, "{other} vs NaN, kind {kind}");
            }
        }
        assert_eq!(cmp(0, -0.0, 0.0), 0, "-0.0 < +0.0 is false");
        assert_eq!(cmp(2, -0.0, 0.0), 1, "-0.0 >= +0.0 is true");
        assert_eq!(cmp(0, -2.0, -1.0), 1, "-2.0 < -1.0");

        let vals = [
            0.0f64,
            -0.0,
            1.0,
            -1.0,
            2.0,
            -2.0,
            f64::MAX,
            f64::MIN,
            f64::MIN_POSITIVE,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
        ];
        for &a in &vals {
            for &b in &vals {
                assert_eq!(cmp(0, a, b), (a < b) as u32, "f64 {a} < {b}");
                assert_eq!(cmp(1, a, b), (a > b) as u32, "f64 {a} > {b}");
                assert_eq!(cmp(2, a, b), (a >= b) as u32, "f64 {a} >= {b}");
            }
        }
    });
}

// ===========================================================================
// 6. #923 regressions — the silent no-op, in both of its directions
// ===========================================================================

/// The false-ACCEPT. `ADD r0,r0,r1 ; UXTB r0,r0` returns `(x + y) & 0xFF` on
/// silicon, which is not `i32.add`. Before #923 `UXTB` had no arm in
/// `encode_op`, the default arm dropped it silently, and the value VC — the one
/// `synth verify` runs — returned `Verified` for this sequence.
#[test]
fn a_lowering_that_destroys_its_own_result_is_rejected() {
    with_verification_context(|| {
        let v = TranslationValidator::new();
        let wrong = vec![
            ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            },
            ArmOp::Uxtb {
                rd: Reg::R0,
                rm: Reg::R0,
            },
        ];
        assert!(
            matches!(
                v.verify_equivalence(&WasmOp::I32Add, &wrong),
                Ok(ValidationResult::Invalid { .. })
            ),
            "a truncating i32.add lowering must produce a counterexample, not a pass"
        );
    });
}

/// The residual, made LOUD. Ops outside the modeled set (MVE vectors, stack and
/// branch ops, symbol relocations) are still unmodeled — deliberately — but a
/// sequence containing one can no longer be "verified" from a partial
/// execution. It declines, and names the op.
#[test]
fn a_sequence_containing_an_unmodeled_op_declines_by_name() {
    with_verification_context(|| {
        let v = TranslationValidator::new();
        for op in [
            ArmOp::Pop {
                regs: vec![Reg::R0],
            },
            ArmOp::Push {
                regs: vec![Reg::R0],
            },
            ArmOp::MemoryGrow {
                rd: Reg::R0,
                rn: Reg::R1,
            },
        ] {
            let name = format!("{op:?}");
            let name = name.split([' ', '{', '(']).next().unwrap().to_string();
            let seq = vec![
                ArmOp::Add {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                },
                op,
            ];
            match v.verify_equivalence(&WasmOp::I32Add, &seq) {
                Err(e) => {
                    let msg = e.to_string();
                    assert!(
                        msg.contains(&name),
                        "the decline must name the unmodeled op; got {msg}"
                    );
                }
                other => panic!("expected a loud decline for {name}, got {other:?}"),
            }
        }
    });
}

/// The false-ALARM, gone. These are the lowerings the shipped selector emits
/// for the WASM shift and rotate ops; before #923 every one of them was
/// reported `Invalid` because the ARM model executed the `AND` and then
/// dropped the shift.
#[test]
fn the_shipped_shift_and_rotate_lowerings_now_verify() {
    with_verification_context(|| {
        let v = TranslationValidator::new();
        let mask = ArmOp::And {
            rd: Reg::R1,
            rn: Reg::R1,
            op2: Operand2::Imm(31),
        };
        let cases: Vec<(WasmOp, Vec<ArmOp>)> = vec![
            (
                WasmOp::I32Shl,
                vec![
                    mask.clone(),
                    ArmOp::LslReg {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        rm: Reg::R1,
                    },
                ],
            ),
            (
                WasmOp::I32ShrU,
                vec![
                    mask.clone(),
                    ArmOp::LsrReg {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        rm: Reg::R1,
                    },
                ],
            ),
            (
                WasmOp::I32ShrS,
                vec![
                    mask.clone(),
                    ArmOp::AsrReg {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        rm: Reg::R1,
                    },
                ],
            ),
            (
                WasmOp::I32Rotr,
                vec![
                    mask.clone(),
                    ArmOp::RorReg {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        rm: Reg::R1,
                    },
                ],
            ),
            (
                WasmOp::I32Rotl,
                vec![
                    ArmOp::Rsb {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        imm: 0,
                    },
                    ArmOp::RorReg {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        rm: Reg::R1,
                    },
                ],
            ),
        ];
        for (wasm, ops) in cases {
            assert!(
                matches!(
                    v.verify_equivalence(&wasm, &ops),
                    Ok(ValidationResult::Verified)
                ),
                "shipped lowering for {wasm:?} must verify"
            );
        }
    });
}

/// The lowering that skips the mask stays rejected — and the counterexample is
/// one only the `Rm<7:0>` model can find. `Rm = 0x4000_0080` has `Rm mod 32 =
/// 0` (WASM: shift by zero, result `Rn`) but `Rm<7:0> = 128 >= 32` (ARM: result
/// 0). A model that used the raw 32-bit `Rm` would also reject this lowering,
/// but never with THIS witness — which is how the test tells the two apart.
#[test]
fn an_unmasked_shift_lowering_is_still_rejected() {
    with_verification_context(|| {
        let v = TranslationValidator::new();
        let unmasked = vec![ArmOp::LslReg {
            rd: Reg::R0,
            rn: Reg::R0,
            rm: Reg::R1,
        }];
        assert!(
            matches!(
                v.verify_equivalence(&WasmOp::I32Shl, &unmasked),
                Ok(ValidationResult::Invalid { .. })
            ),
            "an unmasked LSL is not i32.shl"
        );

        // The witness itself, checked directly against the ARM rule: shifting
        // by a value whose low byte is >= 32 clears the register, while WASM's
        // mod-32 rule would leave it alone.
        assert_eq!(
            run1(
                &[(Reg::R1, 0x1234_5678), (Reg::R2, 0x4000_0080)],
                ArmOp::LslReg {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    rm: Reg::R2
                },
                Reg::R0
            ),
            0,
            "Rm<7:0> = 128 clears the register; Rm mod 32 = 0 would not"
        );
    });
}

/// The drift guard, exercised. `exec_trap_subset_op` keeps an allowlist of ops
/// it delegates to `encode_op`, and before #923 three entries on that list
/// (`Rsb`, `I32TruncF32S`, `I32TruncF32U`) named ops `encode_op` did not model
/// — so the guard whose own doc says the silent default "must never green-wash
/// a trap derivation" passed them through as no-ops. Every allowlisted op must
/// now either execute or decline; none may silently skip.
#[test]
fn every_trap_subset_delegate_is_actually_modeled() {
    with_verification_context(|| {
        let e = ArmSemantics::new();
        let delegates = vec![
            ArmOp::Cmp {
                rn: Reg::R1,
                op2: Operand2::Imm(0),
            },
            ArmOp::Cmn {
                rn: Reg::R1,
                op2: Operand2::Imm(1),
            },
            ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            },
            ArmOp::Movt {
                rd: Reg::R0,
                imm16: 1,
            },
            ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Imm(1),
            },
            ArmOp::Sub {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Imm(1),
            },
            ArmOp::Rsb {
                rd: Reg::R0,
                rn: Reg::R1,
                imm: 0,
            },
            ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(1),
            },
            ArmOp::And {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Imm(1),
            },
            ArmOp::Orr {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Imm(1),
            },
            ArmOp::Eor {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Imm(1),
            },
            ArmOp::Mul {
                rd: Reg::R0,
                rn: Reg::R1,
                rm: Reg::R2,
            },
            ArmOp::Mls {
                rd: Reg::R0,
                rn: Reg::R1,
                rm: Reg::R2,
                ra: Reg::R3,
            },
            ArmOp::Sdiv {
                rd: Reg::R0,
                rn: Reg::R1,
                rm: Reg::R2,
            },
            ArmOp::Udiv {
                rd: Reg::R0,
                rn: Reg::R1,
                rm: Reg::R2,
            },
            ArmOp::SetCond {
                rd: Reg::R0,
                cond: Condition::EQ,
            },
            ArmOp::Nop,
            ArmOp::I32TruncF32S {
                rd: Reg::R0,
                sm: VfpReg::S0,
            },
            ArmOp::I32TruncF32U {
                rd: Reg::R0,
                sm: VfpReg::S0,
            },
            ArmOp::I32TruncF64S {
                rd: Reg::R0,
                dm: VfpReg::D0,
            },
            ArmOp::I32TruncF64U {
                rd: Reg::R0,
                dm: VfpReg::D0,
            },
        ];
        for op in delegates {
            let mut s = ArmState::new_symbolic();
            e.encode_sequence_value_straightline(std::slice::from_ref(&op), &mut s)
                .unwrap_or_else(|err| {
                    panic!("trap-subset delegate {op:?} declined unexpectedly: {err}")
                });
            assert!(
                s.unmodeled.is_none(),
                "{op:?} is allowlisted for the trap-derivation subset but has no \
                 semantics in encode_op — the #923 drift is back"
            );
        }
    });
}
