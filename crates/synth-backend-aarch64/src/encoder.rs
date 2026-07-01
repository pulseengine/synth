//! Minimal AArch64 (A64) instruction encoder — milestone-1 integer subset (#538).
//!
//! Every A64 instruction is a fixed 32-bit little-endian word. This module
//! encodes only the subset milestone-1 needs (32-bit `w` register
//! data-processing, `movz`/`movk`, and `ret`); float, SIMD, 64-bit, and
//! control-flow are later milestones. Each encoding is cross-checked in tests
//! against ground truth produced by `clang -target aarch64` (see `tests`), so the
//! bit-twiddling is verified, not asserted.
//!
//! Register numbering is the A64 architectural number 0..=30 (`w0..w30`); 31 is
//! `wzr`/`wsp` depending on context.

/// A 32-bit general register operand (`w0..w30`; 31 = `wzr`).
pub type Reg = u8;

pub const WZR: Reg = 31;

/// A binary `Wd = Wn OP Wm` data-processing op over the shifted-register form
/// (shift = 0). The `base` is the opcode with all operand fields zero.
fn dp3(base: u32, rd: Reg, rn: Reg, rm: Reg) -> u32 {
    base | ((rm as u32) << 16) | ((rn as u32) << 5) | (rd as u32)
}

/// `add wd, wn, wm`
pub fn add(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    dp3(0x0B00_0000, rd, rn, rm)
}
/// `sub wd, wn, wm`
pub fn sub(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    dp3(0x4B00_0000, rd, rn, rm)
}
/// `and wd, wn, wm`
pub fn and(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    dp3(0x0A00_0000, rd, rn, rm)
}
/// `orr wd, wn, wm`
pub fn orr(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    dp3(0x2A00_0000, rd, rn, rm)
}
/// `eor wd, wn, wm`
pub fn eor(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    dp3(0x4A00_0000, rd, rn, rm)
}

/// `mul wd, wn, wm` — `madd wd, wn, wm, wzr` (Ra = 31).
pub fn mul(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    0x1B00_0000 | ((rm as u32) << 16) | (0x1F << 10) | ((rn as u32) << 5) | (rd as u32)
}

/// `mov wd, wn` — architectural alias `orr wd, wzr, wn`.
pub fn mov_reg(rd: Reg, rn: Reg) -> u32 {
    orr(rd, WZR, rn)
}

/// `movz wd, #imm16` — zero the register and set bits [15:0].
pub fn movz(rd: Reg, imm16: u16) -> u32 {
    0x5280_0000 | ((imm16 as u32) << 5) | (rd as u32)
}

/// `movk wd, #imm16, lsl #(16*hw)` — keep other bits, set the `hw`-th halfword.
pub fn movk(rd: Reg, imm16: u16, hw: u8) -> u32 {
    0x7280_0000 | ((hw as u32) << 21) | ((imm16 as u32) << 5) | (rd as u32)
}

/// `ret` (`ret x30`).
pub fn ret() -> u32 {
    0xD65F_03C0
}

/// Materialize a 32-bit constant into `wd` with `movz` + optional `movk`.
/// Returns 1 or 2 words.
pub fn mov_imm32(rd: Reg, value: u32) -> Vec<u32> {
    let lo = (value & 0xFFFF) as u16;
    let hi = ((value >> 16) & 0xFFFF) as u16;
    let mut out = vec![movz(rd, lo)];
    if hi != 0 {
        out.push(movk(rd, hi, 1));
    }
    out
}

/// Append a 32-bit instruction word to a little-endian byte buffer.
pub fn emit(buf: &mut Vec<u8>, word: u32) {
    buf.extend_from_slice(&word.to_le_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;

    // Ground truth from `clang -target aarch64-linux-gnu` (see the #538 build log).
    #[test]
    fn encodings_match_clang() {
        assert_eq!(add(0, 0, 1), 0x0B01_0000);
        assert_eq!(sub(2, 3, 4), 0x4B04_0062);
        assert_eq!(mul(5, 6, 7), 0x1B07_7CC5);
        assert_eq!(and(0, 1, 2), 0x0A02_0020);
        assert_eq!(orr(3, 4, 5), 0x2A05_0083);
        assert_eq!(eor(6, 7, 0), 0x4A00_00E6);
        assert_eq!(movz(9, 5), 0x5280_00A9);
        assert_eq!(movk(9, 1, 1), 0x72A0_0029);
        assert_eq!(mov_reg(0, 9), 0x2A09_03E0);
        assert_eq!(ret(), 0xD65F_03C0);
    }

    #[test]
    fn mov_imm32_uses_movz_then_movk() {
        assert_eq!(mov_imm32(0, 5), vec![movz(0, 5)]);
        assert_eq!(mov_imm32(0, 0x1234), vec![movz(0, 0x1234)]);
        assert_eq!(
            mov_imm32(3, 0x0001_2345),
            vec![movz(3, 0x2345), movk(3, 1, 1)]
        );
    }
}
