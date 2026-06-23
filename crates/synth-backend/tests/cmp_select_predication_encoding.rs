//! VCR-SEL-004 — `SelectMove` Thumb-2 encoding must be correct for ALL 10
//! conditions, not just the EQ/NE the selector emits today.
//!
//! The cmp→select fusion (`synth_synthesis::liveness::fuse_cmp_select`) retargets
//! the two predicated moves of a `select` from EQ/NE onto the comparison's own
//! condition and its inverse — so a fused clamp newly emits `SelectMove` with
//! LT/GE, LO/HS, GT/LE, HI/LS. This is the "verify bytes, not IR" gate (#180/#185):
//! the unit tests in liveness.rs prove the right *ops* are produced; this proves
//! the *encoder* turns each into a correct, independent `IT <cond>; MOV{cond}`.
//!
//! Each `SelectMove` is its OWN single-Then IT block (mask 0x8) — the two moves of
//! a fused pair are two separate IT blocks, never a hardware ITE — so retargeting
//! their conditions needs no encoder change. These byte assertions lock that.

use synth_backend::ArmEncoder;
use synth_synthesis::rules::{ArmOp, Condition, Reg};

fn enc(rd: Reg, rm: Reg, cond: Condition) -> Vec<u8> {
    ArmEncoder::new_thumb2()
        .encode(&ArmOp::SelectMove { rd, rm, cond })
        .expect("encode SelectMove")
}

#[test]
fn select_move_signed_pair_lt_ge_bytes() {
    // movlt r4, r5 : IT LT (0xBFB8) ; MOV r4,r5 (0x462C)
    assert_eq!(
        enc(Reg::R4, Reg::R5, Condition::LT),
        vec![0xB8, 0xBF, 0x2C, 0x46]
    );
    // movge r4, r5 : IT GE (0xBFA8) ; MOV r4,r5 (0x462C)
    assert_eq!(
        enc(Reg::R4, Reg::R5, Condition::GE),
        vec![0xA8, 0xBF, 0x2C, 0x46]
    );
}

#[test]
fn select_move_unsigned_pair_lo_hs_bytes() {
    // movlo r4, r6 : IT LO (0xBF38) ; MOV r4,r6 (0x4634)
    assert_eq!(
        enc(Reg::R4, Reg::R6, Condition::LO),
        vec![0x38, 0xBF, 0x34, 0x46]
    );
    // movhs r4, r6 : IT HS (0xBF28) ; MOV r4,r6 (0x4634)
    assert_eq!(
        enc(Reg::R4, Reg::R6, Condition::HS),
        vec![0x28, 0xBF, 0x34, 0x46]
    );
}

#[test]
fn select_move_all_ten_conditions_are_distinct_single_then_it_blocks() {
    use Condition::*;
    let conds = [EQ, NE, LT, LE, GT, GE, LO, LS, HI, HS];
    let mut seen = std::collections::BTreeSet::new();
    for c in conds {
        let bytes = enc(Reg::R0, Reg::R1, c);
        assert_eq!(bytes.len(), 4, "{c:?}: IT + MOV is 4 bytes");
        // IT halfword = 0xBF00 | (cond4 << 4) | 0x8 (single Then, mask 0x8).
        let it = u16::from_le_bytes([bytes[0], bytes[1]]);
        assert_eq!(it & 0xFF0F, 0xBF08, "{c:?}: not a single-Then IT block");
        // The encoded firstcond must be unique per condition.
        let firstcond = (it >> 4) & 0xF;
        assert!(
            seen.insert(firstcond),
            "{c:?}: duplicate IT firstcond {firstcond:#x}"
        );
    }
    assert_eq!(
        seen.len(),
        10,
        "all 10 conditions encode to distinct firstcond"
    );
}
