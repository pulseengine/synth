//! Minimal AArch64 (A64) instruction encoder — #538 integer subset.
//!
//! Every A64 instruction is a fixed 32-bit little-endian word. Milestone 1
//! covered the 32-bit `w` register data-processing core (`add/sub/mul/and/or/
//! xor`, `movz/movk`, `ret`); **milestone 2** broadens this to the full i32 and
//! i64 integer ALU: 64-bit `x`-forms (the `sf` bit), variable shifts/rotates,
//! `clz`/`ctz`, and the compare→`cset` family. Float, SIMD, division (A64
//! `SDIV`/`UDIV` do not trap — the WASM trap-on-zero/`INT_MIN÷-1` guards are a
//! later, deliberately-declined milestone), popcnt, and control-flow remain out
//! of scope. Each encoding is cross-checked against ground truth produced by
//! `clang -target aarch64-linux-gnu` (see `tests`), so the bit-twiddling is
//! verified, not asserted.
//!
//! Register numbering is the A64 architectural number 0..=30 (`w0..w30` /
//! `x0..x30`; the register *number* is width-agnostic — the `sf` bit selects the
//! 32- vs 64-bit view). 31 is `wzr`/`xzr` (or `wsp`/`sp`) depending on context.

/// A general register operand (`0..=30`; 31 = `wzr`/`xzr`).
pub type Reg = u8;

pub const WZR: Reg = 31;
pub const XZR: Reg = 31;

/// The `sf` bit (bit 31) that promotes a 32-bit `w`-form data-processing /
/// shift / bit op to its 64-bit `x`-form. Arithmetic, logical, shift-variable,
/// `clz`, `rbit`, `cmp` and `cset` all share this single-bit convention.
const SF64: u32 = 0x8000_0000;

/// A binary `Rd = Rn OP Rm` data-processing op over the shifted-register form
/// (shift = 0). The `base` is the 32-bit opcode with all operand fields zero;
/// `sf` sets the 64-bit width bit.
fn dp3_sf(base: u32, sf: bool, rd: Reg, rn: Reg, rm: Reg) -> u32 {
    let w = base | ((rm as u32) << 16) | ((rn as u32) << 5) | (rd as u32);
    if sf { w | SF64 } else { w }
}

/// A binary `Wd = Wn OP Wm` data-processing op (32-bit form).
fn dp3(base: u32, rd: Reg, rn: Reg, rm: Reg) -> u32 {
    dp3_sf(base, false, rd, rn, rm)
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

// ---------------------------------------------------------------------------
// 64-bit (`x`-form) arithmetic/logical: the same base opcodes with `sf` set.
// A64 is natively 64-bit so i64 add/sub/mul/and/or/xor cost exactly one insn.
// ---------------------------------------------------------------------------

/// `add xd, xn, xm`
pub fn add64(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    dp3_sf(0x0B00_0000, true, rd, rn, rm)
}
/// `sub xd, xn, xm`
pub fn sub64(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    dp3_sf(0x4B00_0000, true, rd, rn, rm)
}
/// `and xd, xn, xm`
pub fn and64(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    dp3_sf(0x0A00_0000, true, rd, rn, rm)
}
/// `orr xd, xn, xm`
pub fn orr64(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    dp3_sf(0x2A00_0000, true, rd, rn, rm)
}
/// `eor xd, xn, xm`
pub fn eor64(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    dp3_sf(0x4A00_0000, true, rd, rn, rm)
}
/// `mul xd, xn, xm` — `madd xd, xn, xm, xzr` (Ra = 31).
pub fn mul64(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    0x9B00_0000 | ((rm as u32) << 16) | (0x1F << 10) | ((rn as u32) << 5) | (rd as u32)
}

// ---------------------------------------------------------------------------
// Variable shifts / rotates (register shift amount). Base = `0x1AC0_2000`
// with the op2 field selecting LSL/LSR/ASR/ROR at bits [11:10]:
//   00 = LSLV, 01 = LSRV, 10 = ASRV, 11 = RORV.
// A64 masks the shift amount mod 32 (w) / mod 64 (x) — EXACTLY WASM's
// shift/rotate-count semantics, so the register forms are correct for free
// (unlike the immediate forms, which we deliberately avoid).
// ---------------------------------------------------------------------------

fn shiftv(op2: u32, sf: bool, rd: Reg, rn: Reg, rm: Reg) -> u32 {
    let w = 0x1AC0_2000 | ((rm as u32) << 16) | (op2 << 10) | ((rn as u32) << 5) | (rd as u32);
    if sf { w | SF64 } else { w }
}
/// `lslv wd, wn, wm` (i32 `shl`)
pub fn lslv(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    shiftv(0, false, rd, rn, rm)
}
/// `lsrv wd, wn, wm` (i32 `shr_u`)
pub fn lsrv(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    shiftv(1, false, rd, rn, rm)
}
/// `asrv wd, wn, wm` (i32 `shr_s`)
pub fn asrv(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    shiftv(2, false, rd, rn, rm)
}
/// `rorv wd, wn, wm` (i32 `rotr`)
pub fn rorv(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    shiftv(3, false, rd, rn, rm)
}
/// `lslv xd, xn, xm` (i64 `shl`)
pub fn lslv64(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    shiftv(0, true, rd, rn, rm)
}
/// `lsrv xd, xn, xm` (i64 `shr_u`)
pub fn lsrv64(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    shiftv(1, true, rd, rn, rm)
}
/// `asrv xd, xn, xm` (i64 `shr_s`)
pub fn asrv64(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    shiftv(2, true, rd, rn, rm)
}
/// `rorv xd, xn, xm` (i64 `rotr`)
pub fn rorv64(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    shiftv(3, true, rd, rn, rm)
}

// ---------------------------------------------------------------------------
// One-operand data processing: `clz` and `rbit` (base `0x5AC0_0000`, opcode
// field at [11:10]: 00 = RBIT, 100 (bit 12) = CLZ → `0x5AC0_1000`). `ctz` is
// `rbit` then `clz`; A64 has no direct scalar CTZ.
// ---------------------------------------------------------------------------

/// `clz wd, wn`
pub fn clz(rd: Reg, rn: Reg) -> u32 {
    0x5AC0_1000 | ((rn as u32) << 5) | (rd as u32)
}
/// `clz xd, xn`
pub fn clz64(rd: Reg, rn: Reg) -> u32 {
    clz(rd, rn) | SF64
}
/// `rbit wd, wn` — reverse bit order (paired with `clz` to synthesize `ctz`).
pub fn rbit(rd: Reg, rn: Reg) -> u32 {
    0x5AC0_0000 | ((rn as u32) << 5) | (rd as u32)
}
/// `rbit xd, xn`
pub fn rbit64(rd: Reg, rn: Reg) -> u32 {
    rbit(rd, rn) | SF64
}

/// `neg wd, wn` — `sub wd, wzr, wn`. Used for `rotl` = `rorv wd, wn, (−k)`.
pub fn neg(rd: Reg, rn: Reg) -> u32 {
    sub(rd, WZR, rn)
}
/// `neg xd, xn`
pub fn neg64(rd: Reg, rn: Reg) -> u32 {
    sub64(rd, XZR, rn)
}

// ---------------------------------------------------------------------------
// Compare (`subs …, wzr` = `cmp`) + conditional set (`cset`). WASM comparisons
// lower to `cmp rn, rm` then `cset rd, <cond>`. `cset rd, cond` is the alias
// `csinc rd, wzr, wzr, invert(cond)`; base word `0x1A9F_07E0` carries the
// already-inverted condition at bits [15:12], so we table each WASM predicate
// to its A64 condition field directly (clang-verified).
// ---------------------------------------------------------------------------

/// A64 condition codes as encoded in a `cset` (already the *inverted* form the
/// hardware wants, matching clang's `cset wd, <cond>` output).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cond {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    Lo,
    Hi,
    Ls,
    Hs,
}

impl Cond {
    /// The bits [15:12] field of the `cset` encoding for this condition, as
    /// emitted by clang (`0x1A9F_07E0` is `cset wd, ne`).
    fn cset_field(self) -> u32 {
        match self {
            Cond::Ne => 0x0,
            Cond::Eq => 0x1,
            Cond::Hs => 0x3,
            Cond::Lo => 0x2,
            Cond::Hi => 0x9,
            Cond::Ls => 0x8,
            Cond::Ge => 0xB,
            Cond::Lt => 0xA,
            Cond::Gt => 0xD,
            Cond::Le => 0xC,
        }
    }
}

/// `cmp wn, wm` — `subs wzr, wn, wm` (flags only).
pub fn cmp(rn: Reg, rm: Reg) -> u32 {
    0x6B00_0000 | ((rm as u32) << 16) | ((rn as u32) << 5) | (WZR as u32)
}
/// `cmp xn, xm`
pub fn cmp64(rn: Reg, rm: Reg) -> u32 {
    cmp(rn, rm) | SF64
}
/// `cset wd, <cond>` — set `wd` to 1 if the condition holds, else 0. Width is
/// immaterial for a 0/1 result (both forms produce the same low 32 bits); we
/// emit the 32-bit form.
pub fn cset(rd: Reg, cond: Cond) -> u32 {
    0x1A9F_07E0 | (cond.cset_field() << 12) | (rd as u32)
}

/// `mov wd, wn` — architectural alias `orr wd, wzr, wn`.
pub fn mov_reg(rd: Reg, rn: Reg) -> u32 {
    orr(rd, WZR, rn)
}
/// `mov xd, xn` — `orr xd, xzr, xn`. Zeroes nothing; used to funnel a 64-bit
/// result to `x0`. Correct for i32 too: w-form producers zero the upper half.
pub fn mov_reg64(rd: Reg, rn: Reg) -> u32 {
    orr64(rd, XZR, rn)
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

/// `brk #imm16` — A64 breakpoint/trap. Used for wasm `unreachable` (#665):
/// WASM §4.4.5 requires an unconditional trap, the A64 analogue of Thumb-2
/// `udf #0` / RV32 `ebreak`.
pub fn brk(imm16: u16) -> u32 {
    0xD420_0000 | ((imm16 as u32) << 5)
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

/// Materialize a 64-bit constant into `xd` with `movz` + up to three `movk`s.
/// Emits only the non-zero halfwords (a leading `movz` is always emitted so the
/// register is fully written even for value 0). `movz`/`movk` set the `sf` bit
/// via the 0x8000_0000 promotion the 32-bit `movz`/`movk` share.
pub fn mov_imm64(rd: Reg, value: u64) -> Vec<u32> {
    let hw = [
        (value & 0xFFFF) as u16,
        ((value >> 16) & 0xFFFF) as u16,
        ((value >> 32) & 0xFFFF) as u16,
        ((value >> 48) & 0xFFFF) as u16,
    ];
    // First non-zero halfword becomes the movz; if all zero, movz #0.
    let first = hw.iter().position(|&h| h != 0).unwrap_or(0);
    let mut out = vec![movz(rd, hw[first]) | SF64];
    for (i, &h) in hw.iter().enumerate() {
        if i != first && h != 0 {
            out.push(movk(rd, h, i as u8) | SF64);
        }
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

    // Milestone-2 broadening. Ground truth from `clang -target aarch64-linux-gnu`
    // (assemble the mnemonic, `objdump -d`, read the 32-bit word).
    #[test]
    fn i64_arith_logical_encodings_match_clang() {
        assert_eq!(add64(0, 1, 2), 0x8B02_0020);
        assert_eq!(sub64(3, 4, 5), 0xCB05_0083);
        assert_eq!(and64(6, 7, 8), 0x8A08_00E6);
        assert_eq!(orr64(9, 10, 11), 0xAA0B_0149);
        assert_eq!(eor64(12, 13, 14), 0xCA0E_01AC);
        assert_eq!(mul64(0, 1, 2), 0x9B02_7C20);
        assert_eq!(mov_reg64(0, 9), 0xAA09_03E0);
    }

    #[test]
    fn variable_shift_encodings_match_clang() {
        // 32-bit forms
        assert_eq!(lslv(5, 6, 7), 0x1AC7_20C5);
        assert_eq!(lsrv(5, 6, 7), 0x1AC7_24C5);
        assert_eq!(asrv(5, 6, 7), 0x1AC7_28C5);
        assert_eq!(rorv(5, 6, 7), 0x1AC7_2CC5);
        // 64-bit forms
        assert_eq!(lslv64(5, 6, 7), 0x9AC7_20C5);
        assert_eq!(lsrv64(5, 6, 7), 0x9AC7_24C5);
        assert_eq!(asrv64(5, 6, 7), 0x9AC7_28C5);
        assert_eq!(rorv64(5, 6, 7), 0x9AC7_2CC5);
    }

    #[test]
    fn clz_rbit_neg_encodings_match_clang() {
        assert_eq!(clz(0, 1), 0x5AC0_1020);
        assert_eq!(clz64(0, 1), 0xDAC0_1020);
        assert_eq!(rbit(0, 1), 0x5AC0_0020);
        assert_eq!(rbit64(0, 1), 0xDAC0_0020);
        assert_eq!(neg(0, 1), 0x4B01_03E0);
        assert_eq!(neg64(0, 1), 0xCB01_03E0);
    }

    #[test]
    fn cmp_and_cset_encodings_match_clang() {
        assert_eq!(cmp(0, 1), 0x6B01_001F);
        assert_eq!(cmp64(0, 1), 0xEB01_001F);
        assert_eq!(cset(0, Cond::Eq), 0x1A9F_17E0);
        assert_eq!(cset(0, Cond::Ne), 0x1A9F_07E0);
        assert_eq!(cset(0, Cond::Lt), 0x1A9F_A7E0);
        assert_eq!(cset(0, Cond::Gt), 0x1A9F_D7E0);
        assert_eq!(cset(0, Cond::Le), 0x1A9F_C7E0);
        assert_eq!(cset(0, Cond::Ge), 0x1A9F_B7E0);
        assert_eq!(cset(0, Cond::Lo), 0x1A9F_27E0);
        assert_eq!(cset(0, Cond::Hi), 0x1A9F_97E0);
        assert_eq!(cset(0, Cond::Ls), 0x1A9F_87E0);
        assert_eq!(cset(0, Cond::Hs), 0x1A9F_37E0);
    }

    #[test]
    fn mov_imm64_emits_movz_then_movks() {
        // 0x2345 → single movz (sf set).
        assert_eq!(mov_imm64(0, 0x2345), vec![0xD284_68A0]);
        // full 64-bit: movz #0x2345 ; movk #1<<16 ; movk #0xdead<<32 ; movk #0xbeef<<48
        assert_eq!(
            mov_imm64(0, 0xBEEF_DEAD_0001_2345),
            vec![0xD284_68A0, 0xF2A0_0020, 0xF2DB_D5A0, 0xF2F7_DDE0]
        );
        // zero → a single `movz x, #0`.
        assert_eq!(mov_imm64(0, 0), vec![movz(0, 0) | 0x8000_0000]);
    }
}
