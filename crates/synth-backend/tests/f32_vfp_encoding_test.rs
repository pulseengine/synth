//! VFP Encoding Unit Tests
//!
//! Validates that F32 VFP instructions encode to correct ARM machine code bytes.
//! Tests both Thumb-2 mode (primary target: Cortex-M4F) and ARM32 mode.
//!
//! VFP encoding reference: ARM Architecture Reference Manual, Section A7.5
//! S-register bit split: Sd = (Vd << 1) | D, where Vd is bits[15:12] and D is bit[22].

use synth_synthesis::{ArmOp, MemAddr, Reg, VfpReg};

// ArmEncoder is in synth-backend, import via the crate's public API
use synth_backend::ArmEncoder;
use synth_core::target::FPUPrecision;

// ============================================================================
// HELPER: Extract 32-bit instruction word from Thumb-2 bytes
// ============================================================================

/// Reconstruct a 32-bit instruction word from Thumb-2 byte encoding
/// (two little-endian halfwords: hw1[0..2], hw2[2..4])
fn thumb_bytes_to_word(bytes: &[u8]) -> u32 {
    assert_eq!(bytes.len(), 4, "Expected 4-byte Thumb-2 VFP instruction");
    let hw1 = u16::from_le_bytes([bytes[0], bytes[1]]) as u32;
    let hw2 = u16::from_le_bytes([bytes[2], bytes[3]]) as u32;
    (hw1 << 16) | hw2
}

/// Reconstruct a 32-bit instruction word from ARM32 byte encoding (single LE u32)
fn arm_bytes_to_word(bytes: &[u8]) -> u32 {
    assert_eq!(bytes.len(), 4, "Expected 4-byte ARM32 instruction");
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
}

fn thumb_encoder() -> ArmEncoder {
    ArmEncoder::new_thumb2_with_fpu(Some(FPUPrecision::Single))
}

fn arm_encoder() -> ArmEncoder {
    ArmEncoder::new_arm32()
}

// ============================================================================
// VADD.F32 / VSUB.F32 / VMUL.F32 / VDIV.F32
// ============================================================================

#[test]
fn test_vadd_f32_s0_s0_s0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Add {
            sd: VfpReg::S0,
            sn: VfpReg::S0,
            sm: VfpReg::S0,
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    // VADD.F32 S0, S0, S0
    // Base: 0xEE300A00, all register fields zero
    assert_eq!(word, 0xEE300A00, "VADD.F32 S0, S0, S0");
}

#[test]
fn test_vadd_f32_s1_s2_s3_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Add {
            sd: VfpReg::S1,
            sn: VfpReg::S2,
            sm: VfpReg::S3,
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    // S1: Vd=0, D=1 → bit22=1
    // S2: Vn=1, N=0 → bits[19:16]=1
    // S3: Vm=1, M=1 → bits[3:0]=1, bit5=1
    assert_eq!(word, 0xEE710A21, "VADD.F32 S1, S2, S3");
}

#[test]
fn test_vsub_f32_s0_s0_s0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Sub {
            sd: VfpReg::S0,
            sn: VfpReg::S0,
            sm: VfpReg::S0,
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    assert_eq!(word, 0xEE300A40, "VSUB.F32 S0, S0, S0");
}

#[test]
fn test_vmul_f32_s4_s5_s6_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Mul {
            sd: VfpReg::S4,
            sn: VfpReg::S5,
            sm: VfpReg::S6,
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    // S4: Vd=2, D=0
    // S5: Vn=2, N=1 → bit7=1
    // S6: Vm=3, M=0
    assert_eq!(word, 0xEE222A83, "VMUL.F32 S4, S5, S6");
}

#[test]
fn test_vdiv_f32_s0_s0_s0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Div {
            sd: VfpReg::S0,
            sn: VfpReg::S0,
            sm: VfpReg::S0,
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    assert_eq!(word, 0xEE800A00, "VDIV.F32 S0, S0, S0");
}

// ============================================================================
// VNEG.F32 / VABS.F32 / VSQRT.F32 (2-register ops)
// ============================================================================

#[test]
fn test_vneg_f32_s0_s0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Neg {
            sd: VfpReg::S0,
            sm: VfpReg::S0,
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    assert_eq!(word, 0xEEB10A40, "VNEG.F32 S0, S0");
}

#[test]
fn test_vabs_f32_s0_s0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Abs {
            sd: VfpReg::S0,
            sm: VfpReg::S0,
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    assert_eq!(word, 0xEEB00AC0, "VABS.F32 S0, S0");
}

#[test]
fn test_vsqrt_f32_s2_s4_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Sqrt {
            sd: VfpReg::S2,
            sm: VfpReg::S4,
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    // S2: Vd=1, D=0 → bits[15:12]=1
    // S4: Vm=2, M=0 → bits[3:0]=2
    assert_eq!(word, 0xEEB11AC2, "VSQRT.F32 S2, S4");
}

// ============================================================================
// VLDR.F32 / VSTR.F32 (load/store)
// ============================================================================

#[test]
fn test_vldr_f32_s0_r11_offset0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Load {
            sd: VfpReg::S0,
            addr: MemAddr::imm(Reg::R11, 0),
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    // VLDR S0, [R11, #0]
    // Base: 0xED900A00, U=1 (bit23), Rn=R11=11
    assert_eq!(word, 0xED9B0A00, "VLDR S0, [R11, #0]");
}

#[test]
fn test_vldr_f32_s0_r0_offset16_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Load {
            sd: VfpReg::S0,
            addr: MemAddr::imm(Reg::R0, 16),
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    // VLDR S0, [R0, #16]: offset=16, imm8=16/4=4, U=1
    assert_eq!(word, 0xED900A04, "VLDR S0, [R0, #16]");
}

#[test]
fn test_vstr_f32_s0_r11_offset0_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Store {
            sd: VfpReg::S0,
            addr: MemAddr::imm(Reg::R11, 0),
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    assert_eq!(word, 0xED8B0A00, "VSTR S0, [R11, #0]");
}

// ============================================================================
// VMOV core↔VFP register transfers
// ============================================================================

#[test]
fn test_vmov_s0_r0_thumb() {
    // F32ReinterpretI32: VMOV S0, R0
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32ReinterpretI32 {
            sd: VfpReg::S0,
            rm: Reg::R0,
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    // VMOV Sn, Rt: 0xEE000A10 | Vn<<16 | Rt<<12 | N<<7
    // S0: Vn=0, N=0, Rt=R0=0
    assert_eq!(word, 0xEE000A10, "VMOV S0, R0");
}

#[test]
fn test_vmov_r0_s0_thumb() {
    // I32ReinterpretF32: VMOV R0, S0
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::I32ReinterpretF32 {
            rd: Reg::R0,
            sm: VfpReg::S0,
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    // VMOV Rt, Sn: 0xEE100A10 | Vn<<16 | Rt<<12 | N<<7
    assert_eq!(word, 0xEE100A10, "VMOV R0, S0");
}

#[test]
fn test_vmov_s1_r3_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32ReinterpretI32 {
            sd: VfpReg::S1,
            rm: Reg::R3,
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    // S1: Vn=0, N=1 → bit7=1; Rt=R3=3 → bits[15:12]=3
    assert_eq!(word, 0xEE003A90, "VMOV S1, R3");
}

// ============================================================================
// F32 comparison (VCMP + VMRS + MOV sequence)
// ============================================================================

#[test]
fn test_f32_eq_comparison_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Eq {
            rd: Reg::R0,
            sn: VfpReg::S0,
            sm: VfpReg::S0,
        })
        .unwrap();
    // Should be: VCMP(4) + VMRS(4) + MOVS(2) + IT(2) + MOV(2) = 14 bytes
    assert_eq!(
        bytes.len(),
        14,
        "F32 comparison should be 14 bytes for low regs"
    );

    // First 4 bytes: VCMP.F32 S0, S0
    let vcmp = thumb_bytes_to_word(&bytes[0..4]);
    assert_eq!(vcmp, 0xEEB40A40, "VCMP.F32 S0, S0");

    // Next 4 bytes: VMRS APSR_nzcv, FPSCR
    let vmrs = thumb_bytes_to_word(&bytes[4..8]);
    assert_eq!(vmrs, 0xEEF1FA10, "VMRS APSR_nzcv, FPSCR");
}

// ============================================================================
// F32Const (MOVW + MOVT + VMOV sequence)
// ============================================================================

#[test]
fn test_f32_const_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Const {
            sd: VfpReg::S0,
            value: 1.0f32,
        })
        .unwrap();
    // MOVW(4) + MOVT(4) + VMOV(4) = 12 bytes
    assert_eq!(bytes.len(), 12, "F32Const should be 12 bytes");

    // Last 4 bytes should be VMOV S0, R12
    let vmov = thumb_bytes_to_word(&bytes[8..12]);
    // VMOV S0, R12: 0xEE000A10 | (0<<16) | (12<<12) | (0<<7)
    assert_eq!(vmov, 0xEE00CA10, "VMOV S0, R12");
}

#[test]
fn test_f32_const_zero_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Const {
            sd: VfpReg::S0,
            value: 0.0f32,
        })
        .unwrap();
    assert_eq!(bytes.len(), 12, "F32Const 0.0 should be 12 bytes");
}

// ============================================================================
// F32 conversions (multi-instruction)
// ============================================================================

#[test]
fn test_f32_convert_i32s_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::F32ConvertI32S {
            sd: VfpReg::S0,
            rm: Reg::R0,
        })
        .unwrap();
    // VMOV(4) + VCVT(4) = 8 bytes
    assert_eq!(bytes.len(), 8, "F32ConvertI32S should be 8 bytes");
}

#[test]
fn test_i32_trunc_f32s_thumb() {
    let enc = thumb_encoder();
    let bytes = enc
        .encode(&ArmOp::I32TruncF32S {
            rd: Reg::R0,
            sm: VfpReg::S0,
        })
        .unwrap();
    // VCVT(4) + VMOV(4) = 8 bytes
    assert_eq!(bytes.len(), 8, "I32TruncF32S should be 8 bytes");
}

// ============================================================================
// ARM32 mode encodings
// ============================================================================

#[test]
fn test_vadd_f32_s0_s0_s0_arm32() {
    let enc = arm_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Add {
            sd: VfpReg::S0,
            sn: VfpReg::S0,
            sm: VfpReg::S0,
        })
        .unwrap();
    let word = arm_bytes_to_word(&bytes);
    assert_eq!(word, 0xEE300A00, "ARM32 VADD.F32 S0, S0, S0");
}

#[test]
fn test_vneg_f32_arm32() {
    let enc = arm_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Neg {
            sd: VfpReg::S0,
            sm: VfpReg::S0,
        })
        .unwrap();
    let word = arm_bytes_to_word(&bytes);
    assert_eq!(word, 0xEEB10A40, "ARM32 VNEG.F32 S0, S0");
}

#[test]
fn test_vldr_f32_arm32() {
    let enc = arm_encoder();
    let bytes = enc
        .encode(&ArmOp::F32Load {
            sd: VfpReg::S0,
            addr: MemAddr::imm(Reg::R0, 8),
        })
        .unwrap();
    let word = arm_bytes_to_word(&bytes);
    // VLDR S0, [R0, #8]: U=1, Rn=0, imm8=8/4=2
    assert_eq!(word, 0xED900A02, "ARM32 VLDR S0, [R0, #8]");
}

#[test]
fn test_vmov_s0_r0_arm32() {
    let enc = arm_encoder();
    let bytes = enc
        .encode(&ArmOp::F32ReinterpretI32 {
            sd: VfpReg::S0,
            rm: Reg::R0,
        })
        .unwrap();
    let word = arm_bytes_to_word(&bytes);
    assert_eq!(word, 0xEE000A10, "ARM32 VMOV S0, R0");
}

// ============================================================================
// Pseudo-ops now generate real instruction sequences
// ============================================================================

#[test]
fn test_f32_ceil_encodes_successfully() {
    let enc = thumb_encoder();
    let result = enc.encode(&ArmOp::F32Ceil {
        sd: VfpReg::S0,
        sm: VfpReg::S0,
    });
    assert!(result.is_ok(), "F32Ceil should encode successfully");
    assert_eq!(result.unwrap().len(), 8); // VCVT.S32.F32 + VCVT.F32.S32
}

#[test]
fn test_f32_min_encodes_successfully() {
    let enc = thumb_encoder();
    let result = enc.encode(&ArmOp::F32Min {
        sd: VfpReg::S0,
        sn: VfpReg::S0,
        sm: VfpReg::S0,
    });
    assert!(result.is_ok(), "F32Min should encode successfully");
    // VMOV(4) + VCMP(4) + VMRS(4) + IT(2) + VMOV(4) = 18
    assert_eq!(result.unwrap().len(), 18);
}

// ============================================================================
// Register encoding correctness — verify S-register bit splitting
// ============================================================================

#[test]
fn test_sreg_encoding_high_registers() {
    let enc = thumb_encoder();
    // S14: number=14, Vd=7, D=0
    // S15: number=15, Vd=7, D=1
    let bytes = enc
        .encode(&ArmOp::F32Add {
            sd: VfpReg::S14,
            sn: VfpReg::S15,
            sm: VfpReg::S0,
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    // S14: Vd=7 → bits[15:12]=7, D=0 → bit22=0
    // S15: Vn=7 → bits[19:16]=7, N=1 → bit7=1
    // S0: Vm=0, M=0
    let expected = 0xEE377A80;
    assert_eq!(
        word, expected,
        "VADD.F32 S14, S15, S0: got {word:#010X}, expected {expected:#010X}"
    );
}

#[test]
fn test_sreg_encoding_odd_registers() {
    let enc = thumb_encoder();
    // S1: Vd=0, D=1; S3: Vn=1, N=1; S5: Vm=2, M=1
    let bytes = enc
        .encode(&ArmOp::F32Add {
            sd: VfpReg::S1,
            sn: VfpReg::S3,
            sm: VfpReg::S5,
        })
        .unwrap();
    let word = thumb_bytes_to_word(&bytes);
    // D=1→bit22, Vn=1→bits[19:16], Vd=0→bits[15:12], N=1→bit7, M=1→bit5, Vm=2→bits[3:0]
    let expected = 0xEE710AA2;
    assert_eq!(
        word, expected,
        "VADD.F32 S1, S3, S5: got {word:#010X}, expected {expected:#010X}"
    );
}
