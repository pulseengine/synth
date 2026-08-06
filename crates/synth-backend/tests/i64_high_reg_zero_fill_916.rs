//! #916 — the 16-bit `MOVS` T1 zero-fill transmutes to `CMP` for a high
//! destination (R8-R12), so the half that must be zeroed is NEVER WRITTEN.
//!
//! `MOVS Rd, #imm8` (T1) is `0010 0 Rd(3) imm8` — the Rd field is **three
//! bits**. `reg_to_bits(R8)` is 8, so `8 << 8 = 0x0800` lands in bit 11 and
//! `0x2000 | 0x0800 = 0x2800`, which is not a MOV at all: it is `CMP r0, #0`.
//! The intended destination keeps whatever it held; the flags are clobbered.
//!
//! This is the same class as #180 / H-CODE-9 and the same defect #311 already
//! fixed for `I64SetCond` / `I64SetCondZ` (emit the 32-bit `MOV.W`, T2
//! `F04F 0000 | rd<<8 | imm8`, whenever `rd >= R8`).
//!
//! ## Scope — the issue named 2 sites; there are FIVE
//!
//! | op | register zeroed | reachable via |
//! |----|-----------------|---------------|
//! | `I64Shl`         | `rd_lo` (large-shift arm) | `i64.shl`, n >= 32 |
//! | `I64ShrU`        | `rd_hi` (large-shift arm) | `i64.shr_u`, n >= 32 |
//! | `I64Clz`         | `rnhi` (high-word clear)  | `i64.clz`, ALWAYS |
//! | `I64Ctz`         | `rnhi` (high-word clear)  | `i64.ctz`, ALWAYS |
//! | `I64ExtendI32U`  | `rdhi` (high-word clear)  | `i64.extend_i32_u`, ALWAYS |
//!
//! The two shift sites are *conditionally* wrong (only the `n >= 32` path
//! reaches the MOV). The other three are **unconditionally** wrong for a high
//! destination — every `i64.clz` / `i64.ctz` / `i64.extend_i32_u` whose high
//! half lands in R8 returns a value whose upper 32 bits are garbage.
//!
//! ## Why this is not a one-liner: instruction SIZE
//!
//! `MOV.W` is 4 bytes where `MOVS` was 2. Whether that moves a branch target
//! has to be settled **per site by decoding the branch imm**, not by eyeballing
//! the comments:
//!
//! * `I64Shl` / `I64ShrU`: `B .done` (`0xE002`) targets halfword 19 = the END
//!   of the expansion, which is PAST the MOV at halfword 18. Widening the MOV
//!   moves `.done` → the displacement MUST become `0xE003`. `BPL .large`
//!   (`0xD50A`) targets halfword 16, BEFORE the MOV, so it is unaffected.
//! * `I64Clz` / `I64Ctz`: `B .done` targets byte 22 / 30, which IS THE MOV's
//!   OWN ADDRESS (the branch jumps *to* the final instruction, not past it).
//!   Widening an instruction does not move its own address → no displacement
//!   change. `BEQ` targets 14 / 18, before the MOV → unaffected.
//! * `I64ExtendI32U`: no branches at all.
//!
//! `assert_branches_still_land` below re-derives those targets from the emitted
//! bytes so a mis-recomputed displacement fails here rather than at run time —
//! trading a data miscompile for a control-flow one would be strictly worse.

use synth_backend::ArmEncoder;
use synth_synthesis::{ArmOp, Reg};

fn thumb(op: &ArmOp) -> Vec<u8> {
    ArmEncoder::new_thumb2()
        .encode(op)
        .expect("shipped encoder must encode the pseudo-op")
}

fn halfwords(bytes: &[u8]) -> Vec<u16> {
    bytes
        .chunks_exact(2)
        .map(|c| u16::from_le_bytes([c[0], c[1]]))
        .collect()
}

/// The 32-bit `MOV.W Rd, #0` (T2): `F04F 0000 | Rd<<8`.
fn movw_imm_zero(rd: u16) -> [u16; 2] {
    [0xF04F, rd << 8]
}

/// Assert the tail of `bytes` zeroes register number `rd` — as the 16-bit
/// `MOVS` for a low register, as the 32-bit `MOV.W` for a high one — and in
/// particular that it is NOT the transmuted `0x2800` (`CMP r0, #0`).
fn assert_zero_fill(label: &str, bytes: &[u8], rd: u16) {
    let hw = halfwords(bytes);
    assert!(hw.len() >= 2, "{label}: expansion too short");
    let tail = *hw.last().unwrap();

    assert_ne!(
        tail, 0x2800,
        "{label}: emitted tail halfword is 0x2800 — that is CMP r0,#0, NOT a \
         zero-fill of R{rd}. The 3-bit MOVS T1 Rd field overflowed (#916): the \
         half is never written and keeps stale data.\nfull stream: {hw:04X?}"
    );

    if rd < 8 {
        assert_eq!(
            tail,
            0x2000 | (rd << 8),
            "{label}: low register must keep the 16-bit MOVS form (byte-identical)"
        );
    } else {
        let want = movw_imm_zero(rd);
        let got = [hw[hw.len() - 2], hw[hw.len() - 1]];
        assert_eq!(
            got, want,
            "{label}: high register must be zeroed by the 32-bit MOV.W (T2), \
             the #311 shape.\nfull stream: {hw:04X?}"
        );
    }
}

/// Re-derive every forward branch target in an expansion from the EMITTED
/// bytes and assert it still lands where the expansion means it to.
///
/// Thumb branch semantics: for a branch at halfword index `i`, the target
/// halfword index is `i + 2 + imm` (PC reads as the instruction address + 4).
///
/// `expected` maps a branch's halfword index to its intended target halfword
/// index. A widened `MOV.W` that shifts a target without the displacement
/// being recomputed fails here.
fn assert_branches_still_land(label: &str, bytes: &[u8], expected: &[(usize, usize)]) {
    let hw = halfwords(bytes);
    for &(idx, want_target) in expected {
        let insn = hw[idx];
        // B (T2, unconditional): 1110 0 imm11.  B<cond> (T1): 1101 cond imm8.
        let imm: i32 = if (insn & 0xF800) == 0xE000 {
            let imm11 = (insn & 0x07FF) as i32;
            if imm11 & 0x400 != 0 {
                imm11 - 0x800
            } else {
                imm11
            }
        } else if (insn & 0xF000) == 0xD000 {
            let imm8 = (insn & 0x00FF) as i32;
            if imm8 & 0x80 != 0 { imm8 - 0x100 } else { imm8 }
        } else {
            panic!("{label}: halfword {idx} = {insn:#06X} is not a branch");
        };
        let target = idx as i32 + 2 + imm;
        assert_eq!(
            target, want_target as i32,
            "{label}: branch at halfword {idx} ({insn:#06X}) lands at halfword \
             {target}, not {want_target}. A displacement was not recomputed \
             after the zero-fill was widened — this is a CONTROL-FLOW \
             miscompile, strictly worse than the data bug it replaced.\n\
             full stream: {hw:04X?}"
        );
    }
}

// ---------------------------------------------------------------------------
// The five defective sites, at a high destination.
// ---------------------------------------------------------------------------

#[test]
fn i64_shl_zero_fills_a_high_rd_lo() {
    // i64.shl with n >= 32: the low half must become 0.
    let op = ArmOp::I64Shl {
        rd_lo: Reg::R8,
        rd_hi: Reg::R7,
        rn_lo: Reg::R0,
        rn_hi: Reg::R1,
        rm_lo: Reg::R2,
        rm_hi: Reg::R3,
    };
    let bytes = thumb(&op);
    assert_zero_fill("I64Shl{rd_lo=R8}", &bytes, 8);
}

#[test]
fn i64_shr_u_zero_fills_a_high_rd_hi() {
    // i64.shr_u with n >= 32: the high half must become 0.
    // This is the shape `scripts/repro/rv32_cmp_select_472.wat` actually emits
    // at `-b arm --target cortex-m4` (rd_hi = R8, allocator pool R0-R8).
    let op = ArmOp::I64ShrU {
        rd_lo: Reg::R7,
        rd_hi: Reg::R8,
        rn_lo: Reg::R3,
        rn_hi: Reg::R4,
        rm_lo: Reg::R5,
        rm_hi: Reg::R6,
    };
    let bytes = thumb(&op);
    assert_zero_fill("I64ShrU{rd_hi=R8}", &bytes, 8);
}

#[test]
fn i64_clz_zero_fills_a_high_high_word() {
    // i64.clz returns i64 — the high word is ALWAYS cleared, so a high `rnhi`
    // is unconditionally miscompiled (no `n >= 32` precondition needed).
    let op = ArmOp::I64Clz {
        rd: Reg::R0,
        rnlo: Reg::R1,
        rnhi: Reg::R8,
    };
    let bytes = thumb(&op);
    assert_zero_fill("I64Clz{rnhi=R8}", &bytes, 8);
}

#[test]
fn i64_ctz_zero_fills_a_high_high_word() {
    let op = ArmOp::I64Ctz {
        rd: Reg::R0,
        rnlo: Reg::R1,
        rnhi: Reg::R8,
    };
    let bytes = thumb(&op);
    assert_zero_fill("I64Ctz{rnhi=R8}", &bytes, 8);
}

#[test]
fn i64_extend_i32_u_zero_fills_a_high_rdhi() {
    // i64.extend_i32_u: the high word is ALWAYS cleared. No branches here, so
    // widening is a pure size change.
    let op = ArmOp::I64ExtendI32U {
        rdlo: Reg::R0,
        rdhi: Reg::R8,
        rn: Reg::R1,
    };
    let bytes = thumb(&op);
    assert_zero_fill("I64ExtendI32U{rdhi=R8}", &bytes, 8);
}

// ---------------------------------------------------------------------------
// Control flow must survive the widening.
// ---------------------------------------------------------------------------

#[test]
fn i64_shl_branches_land_for_both_low_and_high_destinations() {
    for (rd_lo, tail_hw) in [(Reg::R6, 19usize), (Reg::R8, 20usize)] {
        let bytes = thumb(&ArmOp::I64Shl {
            rd_lo,
            rd_hi: Reg::R7,
            rn_lo: Reg::R0,
            rn_hi: Reg::R1,
            rm_lo: Reg::R2,
            rm_hi: Reg::R3,
        });
        // BPL .large at halfword 4 → halfword 16 (before the MOV, never moves).
        // B .done at halfword 15 → the END of the expansion (PAST the MOV).
        assert_branches_still_land(
            &format!("I64Shl{{rd_lo={rd_lo:?}}}"),
            &bytes,
            &[(4, 16), (15, tail_hw)],
        );
        assert_eq!(
            bytes.len(),
            tail_hw * 2,
            "I64Shl{{rd_lo={rd_lo:?}}}: unexpected expansion length"
        );
    }
}

#[test]
fn i64_shr_u_branches_land_for_both_low_and_high_destinations() {
    for (rd_hi, tail_hw) in [(Reg::R6, 19usize), (Reg::R8, 20usize)] {
        let bytes = thumb(&ArmOp::I64ShrU {
            rd_lo: Reg::R7,
            rd_hi,
            rn_lo: Reg::R0,
            rn_hi: Reg::R1,
            rm_lo: Reg::R2,
            rm_hi: Reg::R3,
        });
        assert_branches_still_land(
            &format!("I64ShrU{{rd_hi={rd_hi:?}}}"),
            &bytes,
            &[(4, 16), (15, tail_hw)],
        );
        assert_eq!(
            bytes.len(),
            tail_hw * 2,
            "I64ShrU{{rd_hi={rd_hi:?}}}: unexpected expansion length"
        );
    }
}

#[test]
fn i64_clz_ctz_branches_target_the_final_mov_itself() {
    // The discriminating fact vs Shl/ShrU: here `B .done` jumps TO the final
    // MOV, so widening it in place cannot move the target. Pinned so a future
    // restructuring that moves `.done` past the MOV is caught.
    for rnhi in [Reg::R2, Reg::R8] {
        let clz = thumb(&ArmOp::I64Clz {
            rd: Reg::R0,
            rnlo: Reg::R1,
            rnhi,
        });
        // BEQ@2 → hw 7 (byte 14); B@5 → hw 11 (byte 22) = the MOV.
        assert_branches_still_land(
            &format!("I64Clz{{rnhi={rnhi:?}}}"),
            &clz,
            &[(2, 7), (5, 11)],
        );

        let ctz = thumb(&ArmOp::I64Ctz {
            rd: Reg::R0,
            rnlo: Reg::R1,
            rnhi,
        });
        // BEQ@2 → hw 9 (byte 18); B@7 → hw 15 (byte 30) = the MOV.
        assert_branches_still_land(
            &format!("I64Ctz{{rnhi={rnhi:?}}}"),
            &ctz,
            &[(2, 9), (7, 15)],
        );
    }
}

// ---------------------------------------------------------------------------
// Low registers must be byte-identical: the fix is confined to rd >= R8.
// ---------------------------------------------------------------------------

#[test]
fn low_register_expansions_are_byte_identical() {
    let cases: Vec<(&str, ArmOp, usize)> = vec![
        (
            "I64Shl",
            ArmOp::I64Shl {
                rd_lo: Reg::R0,
                rd_hi: Reg::R1,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
                rm_lo: Reg::R4,
                rm_hi: Reg::R5,
            },
            38,
        ),
        (
            "I64ShrU",
            ArmOp::I64ShrU {
                rd_lo: Reg::R0,
                rd_hi: Reg::R1,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
                rm_lo: Reg::R4,
                rm_hi: Reg::R5,
            },
            38,
        ),
        (
            "I64ShrS",
            ArmOp::I64ShrS {
                rd_lo: Reg::R0,
                rd_hi: Reg::R1,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
                rm_lo: Reg::R4,
                rm_hi: Reg::R5,
            },
            40,
        ),
        (
            "I64Clz",
            ArmOp::I64Clz {
                rd: Reg::R0,
                rnlo: Reg::R1,
                rnhi: Reg::R2,
            },
            24,
        ),
        (
            "I64Ctz",
            ArmOp::I64Ctz {
                rd: Reg::R0,
                rnlo: Reg::R1,
                rnhi: Reg::R2,
            },
            32,
        ),
        (
            "I64ExtendI32U",
            ArmOp::I64ExtendI32U {
                rdlo: Reg::R0,
                rdhi: Reg::R1,
                rn: Reg::R2,
            },
            4,
        ),
    ];
    for (label, op, want_len) in cases {
        let bytes = thumb(&op);
        assert_eq!(
            bytes.len(),
            want_len,
            "{label}: low-register expansion length changed — the #916 fix must \
             be confined to rd >= R8 so frozen anchors do not move"
        );
    }
}

/// `I64ShrS` has NO 16-bit zero-fill: its large-shift arm sign-fills with the
/// 32-bit `ASR.W rd_hi, rn_hi, #31`, which has a 4-bit Rd field. Pinned so the
/// asymmetry is deliberate rather than an oversight.
#[test]
fn i64_shr_s_has_no_16bit_zero_fill_to_transmute() {
    let bytes = thumb(&ArmOp::I64ShrS {
        rd_lo: Reg::R7,
        rd_hi: Reg::R8,
        rn_lo: Reg::R0,
        rn_hi: Reg::R1,
        rm_lo: Reg::R2,
        rm_hi: Reg::R3,
    });
    let hw = halfwords(&bytes);
    assert_eq!(bytes.len(), 40, "I64ShrS length must be register-invariant");
    assert!(
        !hw.contains(&0x2800),
        "I64ShrS must not contain a transmuted MOVS: {hw:04X?}"
    );
    // .large arm sign-fill is ASR.W (0xEA4F ...), Rd field is 4 bits.
    assert_eq!(hw[hw.len() - 2], 0xEA4F, "expected ASR.W sign-fill");
}

/// The A32 (cortex-r5) expansions do NOT share the defect: A32 `MOV Rd, #imm`
/// is `0xE3A00000 | Rd<<12` and the Rd field is **four** bits, so R8 encodes
/// correctly. Pinned so the sweep is recorded, not merely asserted in prose.
#[test]
fn a32_zero_fill_is_not_affected_by_a_high_destination() {
    let enc = ArmEncoder::new_arm32();
    for (label, op, rd_bits) in [
        (
            "I64Shl{rd_lo=R8}",
            ArmOp::I64Shl {
                rd_lo: Reg::R8,
                rd_hi: Reg::R7,
                rn_lo: Reg::R0,
                rn_hi: Reg::R1,
                rm_lo: Reg::R2,
                rm_hi: Reg::R3,
            },
            8u32,
        ),
        (
            "I64ShrU{rd_hi=R8}",
            ArmOp::I64ShrU {
                rd_lo: Reg::R7,
                rd_hi: Reg::R8,
                rn_lo: Reg::R0,
                rn_hi: Reg::R1,
                rm_lo: Reg::R2,
                rm_hi: Reg::R3,
            },
            8u32,
        ),
    ] {
        let bytes = enc.encode(&op).expect("A32 encode");
        let last = u32::from_le_bytes(bytes[bytes.len() - 4..].try_into().unwrap());
        assert_eq!(
            last,
            0xE3A00000 | (rd_bits << 12),
            "{label}: A32 MOV Rd,#0 must encode R8 in its 4-bit Rd field"
        );
    }
}
