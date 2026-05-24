//! VFP-D (Double-Precision) Encoding Unit Tests
//!
//! Validates that F64 VFP-D instructions encode to the canonical ARM machine
//! code bytes documented in the ARMv7-M Architecture Reference Manual,
//! Section A7.5 (Floating-point data-processing instructions).
//!
//! VFP-D encoding (32-bit word, same in ARM32 and Thumb-2):
//!
//!   31..28  cond / 1110 (always)
//!   27..24  1110
//!   23..20  op fields
//!   19..16  Vn[3:0]    (Dn = (N << 4) | Vn — but for D0..D15, N is in bit 7 and = 0)
//!   15..12  Vd[3:0]    (Dd = (D << 4) | Vd — but for D0..D15, D is in bit 22 and = 0)
//!   11..8   1011       (coprocessor 11 = double-precision)
//!   7       N
//!   6..5    op2 / M
//!   3..0    Vm[3:0]
//!
//! Test bytes are cross-checked against ARM ARM Table A7-50/A7-52/A7-54 and
//! against the synth-backend `arm_encoder.rs` helpers, which derive the same
//! bit layout from the manual. Adding `arm-none-eabi-as -mthumb -mcpu=cortex-m7
//! -mfpu=fpv5-d16` assembly of an equivalent one-line program produces the
//! same bytes.

use synth_backend::ArmEncoder;
use synth_core::target::FPUPrecision;
use synth_synthesis::{ArmOp, MemAddr, Reg, VfpReg};

// ============================================================================
// HELPERS
// ============================================================================

/// Reconstruct a 32-bit instruction word from Thumb-2 byte encoding
/// (two little-endian halfwords: hw1[0..2], hw2[2..4]).
fn thumb_bytes_to_word(bytes: &[u8]) -> u32 {
    assert_eq!(bytes.len(), 4, "Expected 4-byte Thumb-2 VFP instruction");
    let hw1 = u16::from_le_bytes([bytes[0], bytes[1]]) as u32;
    let hw2 = u16::from_le_bytes([bytes[2], bytes[3]]) as u32;
    (hw1 << 16) | hw2
}

/// Reconstruct a 32-bit instruction word from ARM32 byte encoding (single LE u32).
fn arm_bytes_to_word(bytes: &[u8]) -> u32 {
    assert_eq!(bytes.len(), 4, "Expected 4-byte ARM32 instruction");
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
}

fn thumb_encoder() -> ArmEncoder {
    ArmEncoder::new_thumb2_with_fpu(Some(FPUPrecision::Double))
}

fn arm_encoder() -> ArmEncoder {
    ArmEncoder::new_arm32()
}

// ============================================================================
// VADD.F64 / VSUB.F64 / VMUL.F64 / VDIV.F64
// ============================================================================

#[test]
fn test_vadd_f64_d0_d0_d0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Add {
            dd: VfpReg::D0,
            dn: VfpReg::D0,
            dm: VfpReg::D0,
        })
        .unwrap();
    // Base: 0xEE300B00, all reg fields zero. Coprocessor 11 (cp11 = 0xB).
    assert_eq!(
        thumb_bytes_to_word(&bytes),
        0xEE300B00,
        "VADD.F64 D0, D0, D0"
    );
}

#[test]
fn test_vadd_f64_d1_d2_d3_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Add {
            dd: VfpReg::D1,
            dn: VfpReg::D2,
            dm: VfpReg::D3,
        })
        .unwrap();
    // D1: Vd=1, D=0;  D2: Vn=2, N=0;  D3: Vm=3, M=0
    // word = 0xEE300B00 | (2<<16) | (1<<12) | 3 = 0xEE321B03
    assert_eq!(
        thumb_bytes_to_word(&bytes),
        0xEE321B03,
        "VADD.F64 D1, D2, D3"
    );
}

#[test]
fn test_vsub_f64_d0_d0_d0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Sub {
            dd: VfpReg::D0,
            dn: VfpReg::D0,
            dm: VfpReg::D0,
        })
        .unwrap();
    // VSUB.F64 has op=1 → bit 6 set → 0xEE300B40
    assert_eq!(
        thumb_bytes_to_word(&bytes),
        0xEE300B40,
        "VSUB.F64 D0, D0, D0"
    );
}

#[test]
fn test_vmul_f64_d4_d5_d6_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Mul {
            dd: VfpReg::D4,
            dn: VfpReg::D5,
            dm: VfpReg::D6,
        })
        .unwrap();
    // base 0xEE200B00 | (5<<16) | (4<<12) | 6 = 0xEE254B06
    assert_eq!(
        thumb_bytes_to_word(&bytes),
        0xEE254B06,
        "VMUL.F64 D4, D5, D6"
    );
}

#[test]
fn test_vdiv_f64_d0_d0_d0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Div {
            dd: VfpReg::D0,
            dn: VfpReg::D0,
            dm: VfpReg::D0,
        })
        .unwrap();
    // VDIV.F64 base = 0xEE800B00
    assert_eq!(
        thumb_bytes_to_word(&bytes),
        0xEE800B00,
        "VDIV.F64 D0, D0, D0"
    );
}

#[test]
fn test_vdiv_f64_d15_d14_d13_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Div {
            dd: VfpReg::D15,
            dn: VfpReg::D14,
            dm: VfpReg::D13,
        })
        .unwrap();
    // D15: Vd=15, D=0;  D14: Vn=14, N=0;  D13: Vm=13, M=0
    // base 0xEE800B00 | (14<<16) | (15<<12) | 13 = 0xEE8EFB0D
    assert_eq!(
        thumb_bytes_to_word(&bytes),
        0xEE8EFB0D,
        "VDIV.F64 D15, D14, D13"
    );
}

// ============================================================================
// VABS.F64 / VNEG.F64 / VSQRT.F64
// ============================================================================

#[test]
fn test_vabs_f64_d0_d0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Abs {
            dd: VfpReg::D0,
            dm: VfpReg::D0,
        })
        .unwrap();
    assert_eq!(thumb_bytes_to_word(&bytes), 0xEEB00BC0, "VABS.F64 D0, D0");
}

#[test]
fn test_vneg_f64_d0_d0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Neg {
            dd: VfpReg::D0,
            dm: VfpReg::D0,
        })
        .unwrap();
    assert_eq!(thumb_bytes_to_word(&bytes), 0xEEB10B40, "VNEG.F64 D0, D0");
}

#[test]
fn test_vsqrt_f64_d0_d0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Sqrt {
            dd: VfpReg::D0,
            dm: VfpReg::D0,
        })
        .unwrap();
    assert_eq!(thumb_bytes_to_word(&bytes), 0xEEB10BC0, "VSQRT.F64 D0, D0");
}

#[test]
fn test_vsqrt_f64_d3_d7_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Sqrt {
            dd: VfpReg::D3,
            dm: VfpReg::D7,
        })
        .unwrap();
    // base 0xEEB10BC0 | (3<<12) | 7 = 0xEEB13BC7
    assert_eq!(thumb_bytes_to_word(&bytes), 0xEEB13BC7, "VSQRT.F64 D3, D7");
}

#[test]
fn test_vabs_f64_d8_d9_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Abs {
            dd: VfpReg::D8,
            dm: VfpReg::D9,
        })
        .unwrap();
    // base 0xEEB00BC0 | (8<<12) | 9 = 0xEEB08BC9
    assert_eq!(thumb_bytes_to_word(&bytes), 0xEEB08BC9, "VABS.F64 D8, D9");
}

// ============================================================================
// VLDR.64 / VSTR.64
// ============================================================================

#[test]
fn test_vldr_f64_d0_r0_8_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Load {
            dd: VfpReg::D0,
            addr: MemAddr::imm(Reg::R0, 8),
        })
        .unwrap();
    // VLDR.64 base 0xED900B00 with positive offset (U=1 already in base);
    // imm8 = 8/4 = 2 → 0xED900B02
    assert_eq!(
        thumb_bytes_to_word(&bytes),
        0xED900B02,
        "VLDR.64 D0, [R0, #8]"
    );
}

#[test]
fn test_vstr_f64_d0_sp_0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Store {
            dd: VfpReg::D0,
            addr: MemAddr::imm(Reg::SP, 0),
        })
        .unwrap();
    // VSTR.64 base 0xED800B00, Rn=SP=13, imm8=0 → 0xED8D0B00
    assert_eq!(
        thumb_bytes_to_word(&bytes),
        0xED8D0B00,
        "VSTR.64 D0, [SP, #0]"
    );
}

#[test]
fn test_vldr_f64_d2_r1_16_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Load {
            dd: VfpReg::D2,
            addr: MemAddr::imm(Reg::R1, 16),
        })
        .unwrap();
    // base 0xED900B00 | (1<<16) | (2<<12) | (16/4) = 0xED912B04
    assert_eq!(
        thumb_bytes_to_word(&bytes),
        0xED912B04,
        "VLDR.64 D2, [R1, #16]"
    );
}

// ============================================================================
// Coprocessor identification — F64 must use cp11 (0xB), not cp10 (0xA)
// ============================================================================

#[test]
fn test_f64_uses_cp11_thumb() {
    let enc = thumb_encoder();

    // VADD.F64 — cp11
    let bytes = enc
        .encode(&ArmOp::F64Add {
            dd: VfpReg::D0,
            dn: VfpReg::D0,
            dm: VfpReg::D0,
        })
        .unwrap();
    let instr = thumb_bytes_to_word(&bytes);
    assert_eq!(
        (instr >> 8) & 0xF,
        0xB,
        "F64Add must use coprocessor 11 (0xB)"
    );

    // VSQRT.F64 — cp11
    let bytes = enc
        .encode(&ArmOp::F64Sqrt {
            dd: VfpReg::D0,
            dm: VfpReg::D0,
        })
        .unwrap();
    let instr = thumb_bytes_to_word(&bytes);
    assert_eq!(
        (instr >> 8) & 0xF,
        0xB,
        "F64Sqrt must use coprocessor 11 (0xB)"
    );

    // VLDR.64 — cp11
    let bytes = enc
        .encode(&ArmOp::F64Load {
            dd: VfpReg::D0,
            addr: MemAddr::imm(Reg::R0, 0),
        })
        .unwrap();
    let instr = thumb_bytes_to_word(&bytes);
    assert_eq!(
        (instr >> 8) & 0xF,
        0xB,
        "F64Load must use coprocessor 11 (0xB)"
    );
}

#[test]
fn test_f64_uses_cp11_arm32() {
    let enc = arm_encoder();

    // VADD.F64 — cp11
    let bytes = enc
        .encode(&ArmOp::F64Add {
            dd: VfpReg::D0,
            dn: VfpReg::D0,
            dm: VfpReg::D0,
        })
        .unwrap();
    let instr = arm_bytes_to_word(&bytes);
    assert_eq!(
        (instr >> 8) & 0xF,
        0xB,
        "F64Add ARM32 must use coprocessor 11 (0xB)"
    );
}

// ============================================================================
// VFP-D bit-pattern symmetry — F64 base matches F32 base + sz bit
// ============================================================================

#[test]
fn test_f64_add_equals_f32_add_with_sz_bit() {
    let enc = thumb_encoder();

    let f32_bytes = enc
        .encode(&ArmOp::F32Add {
            sd: VfpReg::S0,
            sn: VfpReg::S0,
            sm: VfpReg::S0,
        })
        .unwrap();
    let f64_bytes = enc
        .encode(&ArmOp::F64Add {
            dd: VfpReg::D0,
            dn: VfpReg::D0,
            dm: VfpReg::D0,
        })
        .unwrap();

    let f32_word = thumb_bytes_to_word(&f32_bytes);
    let f64_word = thumb_bytes_to_word(&f64_bytes);

    // F32 has sz=0 (cp10), F64 has sz=1 (cp11). Differ only in bit 8.
    assert_eq!(
        f64_word ^ f32_word,
        1 << 8,
        "F32/F64 of the same op should differ only in the sz bit (bit 8)"
    );
}

// ============================================================================
// ARM32 mirrors Thumb-2 (VFP instruction words are identical)
// ============================================================================

#[test]
fn test_vadd_f64_d1_d2_d3_arm32_matches_thumb() {
    let thumb_bytes = thumb_encoder()
        .encode(&ArmOp::F64Add {
            dd: VfpReg::D1,
            dn: VfpReg::D2,
            dm: VfpReg::D3,
        })
        .unwrap();
    let arm_bytes = arm_encoder()
        .encode(&ArmOp::F64Add {
            dd: VfpReg::D1,
            dn: VfpReg::D2,
            dm: VfpReg::D3,
        })
        .unwrap();
    // Both encode the same 32-bit VFP word, just split differently.
    assert_eq!(
        thumb_bytes_to_word(&thumb_bytes),
        arm_bytes_to_word(&arm_bytes)
    );
}

// ============================================================================
// VMOV core ↔ D-register (F64ReinterpretI64 / I64ReinterpretF64)
// ============================================================================

#[test]
fn test_vmov_core_to_dreg_thumb() {
    let enc = thumb_encoder();
    // VMOV D0, R0, R1: 0xEC400B10
    let bytes = enc
        .encode(&ArmOp::F64ReinterpretI64 {
            dd: VfpReg::D0,
            rmlo: Reg::R0,
            rmhi: Reg::R1,
        })
        .unwrap();
    assert_eq!(thumb_bytes_to_word(&bytes), 0xEC410B10, "VMOV D0, R0, R1");
}

#[test]
fn test_vmov_dreg_to_core_thumb() {
    let enc = thumb_encoder();
    // VMOV R0, R1, D0: 0xEC500B10 base, Rt2=R1, Rt=R0, Dm=D0
    // 0xEC500B10 | (1<<16) | (0<<12) | 0 = 0xEC510B10
    let bytes = enc
        .encode(&ArmOp::I64ReinterpretF64 {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            dm: VfpReg::D0,
        })
        .unwrap();
    assert_eq!(thumb_bytes_to_word(&bytes), 0xEC510B10, "VMOV R0, R1, D0");
}

// ============================================================================
// VCVT.F64.F32 (F64PromoteF32)
// ============================================================================

#[test]
fn test_vcvt_f64_f32_d0_s0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64PromoteF32 {
            dd: VfpReg::D0,
            sm: VfpReg::S0,
        })
        .unwrap();
    // VCVT.F64.F32 Dd, Sm: 0xEEB70AC0 — all register fields zero.
    assert_eq!(
        thumb_bytes_to_word(&bytes),
        0xEEB70AC0,
        "VCVT.F64.F32 D0, S0"
    );
}

// ============================================================================
// Size & shape — every f64 op the selector emits should encode without panic
// ============================================================================

#[test]
fn test_f64_arith_encodes_to_4_bytes_thumb() {
    let enc = thumb_encoder();
    for op in [
        ArmOp::F64Add {
            dd: VfpReg::D0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        ArmOp::F64Sub {
            dd: VfpReg::D3,
            dn: VfpReg::D4,
            dm: VfpReg::D5,
        },
        ArmOp::F64Mul {
            dd: VfpReg::D6,
            dn: VfpReg::D7,
            dm: VfpReg::D8,
        },
        ArmOp::F64Div {
            dd: VfpReg::D9,
            dn: VfpReg::D10,
            dm: VfpReg::D11,
        },
        ArmOp::F64Abs {
            dd: VfpReg::D12,
            dm: VfpReg::D13,
        },
        ArmOp::F64Neg {
            dd: VfpReg::D14,
            dm: VfpReg::D15,
        },
        ArmOp::F64Sqrt {
            dd: VfpReg::D0,
            dm: VfpReg::D1,
        },
    ] {
        let bytes = enc.encode(&op).expect("encoding should succeed");
        assert_eq!(bytes.len(), 4, "{op:?} should encode to 4 bytes");
        // Coprocessor must be cp11
        let word = thumb_bytes_to_word(&bytes);
        assert_eq!(
            (word >> 8) & 0xF,
            0xB,
            "{op:?} must use cp11 (got cp{:X})",
            (word >> 8) & 0xF
        );
    }
}

#[test]
fn test_f64_ldst_encodes_to_4_bytes_thumb() {
    let enc = thumb_encoder();
    for op in [
        ArmOp::F64Load {
            dd: VfpReg::D0,
            addr: MemAddr::imm(Reg::R0, 0),
        },
        ArmOp::F64Load {
            dd: VfpReg::D15,
            addr: MemAddr::imm(Reg::R11, 32),
        },
        ArmOp::F64Store {
            dd: VfpReg::D0,
            addr: MemAddr::imm(Reg::SP, 0),
        },
        ArmOp::F64Store {
            dd: VfpReg::D7,
            addr: MemAddr::imm(Reg::R4, 64),
        },
    ] {
        let bytes = enc.encode(&op).expect("encoding should succeed");
        assert_eq!(bytes.len(), 4, "{op:?} should encode to 4 bytes");
        let word = thumb_bytes_to_word(&bytes);
        assert_eq!((word >> 8) & 0xF, 0xB, "{op:?} must use cp11");
    }
}

#[test]
fn test_f64_const_encodes_to_20_bytes_thumb() {
    // F64Const is a pseudo-op that expands to MOVW+MOVT+MOVW+MOVT+VMOV = 20 bytes
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F64Const {
            dd: VfpReg::D0,
            value: 1.5,
        })
        .unwrap();
    assert_eq!(bytes.len(), 20, "F64Const should encode to 20 bytes");
}
