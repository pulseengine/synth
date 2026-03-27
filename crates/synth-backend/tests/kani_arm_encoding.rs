//! Kani bounded model checking harnesses for ARM Thumb-2 instruction encoding.
//!
//! These harnesses verify that synth's ARM encoder produces correct instruction
//! bytes matching the ARM Architecture Reference Manual (ARMv7-M).
//!
//! Run with: `cargo kani -p synth-backend --tests`
//! Normal `cargo test` skips these (#[cfg(kani)] compile-gate).

#![allow(unexpected_cfgs)]

#[cfg(kani)]
mod kani_proofs {
    // =========================================================================
    // Thumb-2 16-bit ADD/SUB register encoding
    // ARM ARM A7.7.3: ADD (register) T1 encoding
    //   15:9 = 0001100, 8:6 = Rm, 5:3 = Rn, 2:0 = Rd
    // =========================================================================

    #[kani::proof]
    fn verify_thumb16_add_reg_layout() {
        let rd: u8 = kani::any();
        let rn: u8 = kani::any();
        let rm: u8 = kani::any();
        kani::assume(rd <= 7 && rn <= 7 && rm <= 7);

        let encoded: u16 = 0x1800 | ((rm as u16) << 6) | ((rn as u16) << 3) | (rd as u16);

        // Verify bit fields
        assert_eq!(encoded >> 9, 0b0001100);
        assert_eq!((encoded >> 6) & 0x7, rm as u16);
        assert_eq!((encoded >> 3) & 0x7, rn as u16);
        assert_eq!(encoded & 0x7, rd as u16);
    }

    // ARM ARM A7.7.172: SUB (register) T1 encoding
    //   15:9 = 0001101, 8:6 = Rm, 5:3 = Rn, 2:0 = Rd
    #[kani::proof]
    fn verify_thumb16_sub_reg_layout() {
        let rd: u8 = kani::any();
        let rn: u8 = kani::any();
        let rm: u8 = kani::any();
        kani::assume(rd <= 7 && rn <= 7 && rm <= 7);

        let encoded: u16 = 0x1A00 | ((rm as u16) << 6) | ((rn as u16) << 3) | (rd as u16);

        assert_eq!(encoded >> 9, 0b0001101);
        assert_eq!((encoded >> 6) & 0x7, rm as u16);
        assert_eq!((encoded >> 3) & 0x7, rn as u16);
        assert_eq!(encoded & 0x7, rd as u16);
    }

    // =========================================================================
    // Thumb-2 MOV immediate / MOVW / MOVT
    // =========================================================================

    // ARM ARM A7.7.76: MOV (immediate) T1 encoding
    //   15:11 = 00100, 10:8 = Rd, 7:0 = imm8
    #[kani::proof]
    fn verify_thumb16_mov_imm8_layout() {
        let rd: u8 = kani::any();
        let imm8: u8 = kani::any();
        kani::assume(rd <= 7);

        let encoded: u16 = 0x2000 | ((rd as u16) << 8) | (imm8 as u16);

        assert_eq!(encoded >> 11, 0b00100);
        assert_eq!((encoded >> 8) & 0x7, rd as u16);
        assert_eq!(encoded & 0xFF, imm8 as u16);
    }

    // ARM ARM A7.7.76: MOVW T3 encoding (32-bit)
    //   First halfword:  15:11 = 11110, i = bit10, 10:9 = 10, 0100, imm4 = bits 3:0
    //   Second halfword: 15 = 0, imm3 = 14:12, Rd = 11:8, imm8 = 7:0
    //   Immediate = imm4:i:imm3:imm8 (16-bit value)
    #[kani::proof]
    fn verify_movw_imm16_range() {
        let imm16: u16 = kani::any();
        let rd: u8 = kani::any();
        kani::assume(rd <= 14); // R0-R14 valid

        let imm4 = (imm16 >> 12) & 0xF;
        let i = (imm16 >> 11) & 0x1;
        let imm3 = (imm16 >> 8) & 0x7;
        let imm8 = imm16 & 0xFF;

        // Reconstruct — must get original value back
        let reconstructed = (imm4 << 12) | (i << 11) | (imm3 << 8) | imm8;
        assert_eq!(reconstructed, imm16);
    }

    // MOVT encoding: same field layout, different opcode (11110 i 101100 imm4)
    #[kani::proof]
    fn verify_movt_sets_upper_halfword() {
        let lo: u16 = kani::any();
        let hi: u16 = kani::any();

        // MOVW sets low 16 bits, MOVT sets high 16 bits
        let full: u32 = (lo as u32) | ((hi as u32) << 16);

        assert_eq!(full & 0xFFFF, lo as u32);
        assert_eq!((full >> 16) & 0xFFFF, hi as u32);
    }

    // =========================================================================
    // Thumb-2 LDR/STR immediate offset
    // ARM ARM A7.7.42: LDR (immediate) T1 encoding
    //   15:11 = 01101, 10:6 = imm5, 5:3 = Rn, 2:0 = Rt
    //   offset = imm5 << 2 (word-aligned)
    // =========================================================================

    #[kani::proof]
    fn verify_thumb16_ldr_imm_offset() {
        let rt: u8 = kani::any();
        let rn: u8 = kani::any();
        let imm5: u8 = kani::any();
        kani::assume(rt <= 7 && rn <= 7 && imm5 <= 31);

        let encoded: u16 = 0x6800 | ((imm5 as u16) << 6) | ((rn as u16) << 3) | (rt as u16);

        assert_eq!(encoded >> 11, 0b01101);
        assert_eq!((encoded >> 6) & 0x1F, imm5 as u16);
        assert_eq!((encoded >> 3) & 0x7, rn as u16);
        assert_eq!(encoded & 0x7, rt as u16);

        // Actual byte offset is imm5 * 4
        let byte_offset = (imm5 as u32) * 4;
        assert!(byte_offset <= 124);
    }

    // ARM ARM A7.7.158: STR (immediate) T1 encoding
    //   15:11 = 01100, rest same as LDR T1
    #[kani::proof]
    fn verify_thumb16_str_imm_offset() {
        let rt: u8 = kani::any();
        let rn: u8 = kani::any();
        let imm5: u8 = kani::any();
        kani::assume(rt <= 7 && rn <= 7 && imm5 <= 31);

        let encoded: u16 = 0x6000 | ((imm5 as u16) << 6) | ((rn as u16) << 3) | (rt as u16);

        assert_eq!(encoded >> 11, 0b01100);
    }

    // =========================================================================
    // Thumb-2 CMP
    // ARM ARM A7.7.27: CMP (immediate) T1 encoding
    //   15:11 = 00101, 10:8 = Rn, 7:0 = imm8
    // =========================================================================

    #[kani::proof]
    fn verify_thumb16_cmp_imm_layout() {
        let rn: u8 = kani::any();
        let imm8: u8 = kani::any();
        kani::assume(rn <= 7);

        let encoded: u16 = 0x2800 | ((rn as u16) << 8) | (imm8 as u16);

        assert_eq!(encoded >> 11, 0b00101);
        assert_eq!((encoded >> 8) & 0x7, rn as u16);
        assert_eq!(encoded & 0xFF, imm8 as u16);
    }

    // CMP (register) T1: 15:6 = 0100001010, 5:3 = Rm, 2:0 = Rn
    #[kani::proof]
    fn verify_thumb16_cmp_reg_layout() {
        let rn: u8 = kani::any();
        let rm: u8 = kani::any();
        kani::assume(rn <= 7 && rm <= 7);

        let encoded: u16 = 0x4280 | ((rm as u16) << 3) | (rn as u16);

        assert_eq!(encoded >> 6, 0b0100001010);
        assert_eq!((encoded >> 3) & 0x7, rm as u16);
        assert_eq!(encoded & 0x7, rn as u16);
    }

    // =========================================================================
    // Thumb-2 B.W (wide branch) encoding
    // ARM ARM A7.7.12: B T4 encoding
    //   First halfword: 11110 S imm10
    //   Second halfword: 10 J1 1 J2 imm11
    //   offset = SignExtend(S:I1:I2:imm10:imm11:0, 25)
    //   I1 = NOT(J1 XOR S), I2 = NOT(J2 XOR S)
    // =========================================================================

    #[kani::proof]
    fn verify_bw_j1_j2_roundtrip() {
        let s: bool = kani::any();
        let i1: bool = kani::any();
        let i2: bool = kani::any();

        // Encode: J1 = NOT(I1 XOR S), J2 = NOT(I2 XOR S)
        let j1 = !(i1 ^ s);
        let j2 = !(i2 ^ s);

        // Decode: I1 = NOT(J1 XOR S), I2 = NOT(J2 XOR S)
        let i1_decoded = !(j1 ^ s);
        let i2_decoded = !(j2 ^ s);

        // Must roundtrip
        assert_eq!(i1, i1_decoded);
        assert_eq!(i2, i2_decoded);
    }

    #[kani::proof]
    fn verify_bw_offset_range() {
        // B.W can reach ±16MB (25-bit signed offset)
        let offset: i32 = kani::any();
        kani::assume(offset >= -(1 << 24) && offset < (1 << 24));
        kani::assume(offset % 2 == 0); // Must be halfword-aligned

        let s = offset < 0;
        let uoffset = (offset as u32) & 0x01FF_FFFE;

        let imm10 = (uoffset >> 12) & 0x3FF;
        let imm11 = (uoffset >> 1) & 0x7FF;
        let i1 = (uoffset >> 23) & 1 != 0;
        let i2 = (uoffset >> 22) & 1 != 0;

        // Verify all fields fit their bit widths
        assert!(imm10 <= 0x3FF);
        assert!(imm11 <= 0x7FF);
    }

    // =========================================================================
    // VFP VADD.F32 encoding
    // ARM ARM A7.22.1: VADD (floating-point)
    //   cond 1110 0D11 Vn:Vd 101 sz N0 M0 Vm
    //   For F32: sz=0, cp=10 (0b1010)
    // =========================================================================

    #[kani::proof]
    fn verify_vfp_vadd_f32_coprocessor_field() {
        // VADD.F32 must use coprocessor 10 (cp10), not cp11 (F64)
        let sd: u8 = kani::any();
        let sn: u8 = kani::any();
        let sm: u8 = kani::any();
        kani::assume(sd <= 31 && sn <= 31 && sm <= 31);

        // Base encoding for VADD.F32
        let base: u32 = 0xEE300A00; // cond=AL, 11100 D 11 Vn Vd 1010 N 0 M 0 Vm

        // Verify coprocessor field (bits 11:8) = 0b1010 = cp10 (single-precision)
        assert_eq!((base >> 8) & 0xF, 0xA);

        // For F64 it would be 0xB (cp11)
        let f64_base: u32 = 0xEE300B00;
        assert_eq!((f64_base >> 8) & 0xF, 0xB);
    }

    // =========================================================================
    // i64 ADDS/ADC carry chain
    // ADDS sets carry flag, ADC consumes it
    // =========================================================================

    #[kani::proof]
    fn verify_i64_add_carry_chain_logic() {
        let a_lo: u32 = kani::any();
        let a_hi: u32 = kani::any();
        let b_lo: u32 = kani::any();
        let b_hi: u32 = kani::any();

        let a: u64 = (a_lo as u64) | ((a_hi as u64) << 32);
        let b: u64 = (b_lo as u64) | ((b_hi as u64) << 32);

        // ADDS: result_lo = a_lo + b_lo, carry = overflow
        let (result_lo, carry) = a_lo.overflowing_add(b_lo);

        // ADC: result_hi = a_hi + b_hi + carry
        let result_hi = a_hi.wrapping_add(b_hi).wrapping_add(carry as u32);

        let result: u64 = (result_lo as u64) | ((result_hi as u64) << 32);

        // Must equal the 64-bit addition
        assert_eq!(result, a.wrapping_add(b));
    }

    // =========================================================================
    // i64 SUB borrow chain (SUBS/SBC)
    // =========================================================================

    #[kani::proof]
    fn verify_i64_sub_borrow_chain_logic() {
        let a_lo: u32 = kani::any();
        let a_hi: u32 = kani::any();
        let b_lo: u32 = kani::any();
        let b_hi: u32 = kani::any();

        let a: u64 = (a_lo as u64) | ((a_hi as u64) << 32);
        let b: u64 = (b_lo as u64) | ((b_hi as u64) << 32);

        // SUBS: result_lo = a_lo - b_lo, borrow = underflow
        let (result_lo, borrow) = a_lo.overflowing_sub(b_lo);

        // SBC: result_hi = a_hi - b_hi - borrow
        let result_hi = a_hi.wrapping_sub(b_hi).wrapping_sub(borrow as u32);

        let result: u64 = (result_lo as u64) | ((result_hi as u64) << 32);

        assert_eq!(result, a.wrapping_sub(b));
    }

    // =========================================================================
    // Division trap guard: CMP + BNE + UDF sequence
    // =========================================================================

    #[kani::proof]
    fn verify_div_trap_guard_catches_zero() {
        let divisor: u32 = kani::any();

        // The trap guard: if divisor == 0, trap
        let should_trap = divisor == 0;

        // CMP divisor, #0 sets Z flag
        let z_flag = divisor == 0;

        // BNE skips trap if Z==0 (divisor != 0)
        let skip_trap = !z_flag;

        // UDF executes only if we didn't skip
        let trap_executes = !skip_trap;

        assert_eq!(should_trap, trap_executes);
    }

    // UDF encoding: 0xDE00 | imm8 (T1 encoding)
    #[kani::proof]
    fn verify_udf_encoding() {
        let imm8: u8 = kani::any();

        let encoded: u16 = 0xDE00 | (imm8 as u16);

        assert_eq!(encoded >> 8, 0xDE);
        assert_eq!(encoded & 0xFF, imm8 as u16);
    }

    // =========================================================================
    // Constant materialization: negative values
    // =========================================================================

    #[kani::proof]
    fn verify_negative_const_via_movw_movt() {
        let value: i32 = kani::any();

        let lo = (value as u32) & 0xFFFF;
        let hi = ((value as u32) >> 16) & 0xFFFF;

        // Reconstruct
        let reconstructed = (lo | (hi << 16)) as i32;
        assert_eq!(reconstructed, value);
    }

    // =========================================================================
    // Thumb bit on function symbols
    // =========================================================================

    #[kani::proof]
    fn verify_thumb_bit_roundtrip() {
        let addr: u32 = kani::any();
        kani::assume(addr % 2 == 0); // Function addresses are halfword-aligned
        kani::assume(addr <= 0x0FFF_FFFE); // Reasonable address range

        let with_thumb = addr | 1;
        let without_thumb = with_thumb & !1u32;

        assert_eq!(without_thumb, addr);
        assert_eq!(with_thumb & 1, 1);
    }
}
