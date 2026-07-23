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
    /// `mi` — N set. WASM float `lt` lowers to `cset mi` after `fcmp`: ordered
    /// less-than sets N=1, while an unordered (NaN) compare sets C=1,V=1 ⇒ N=0,
    /// so `mi` correctly yields 0 (matching clang's f32/f64 `<` lowering).
    Mi,
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
            Cond::Mi => 0x5,
        }
    }

    /// The ARCHITECTURAL condition encoding (`b.<cond>` bits [3:0]) — the
    /// NON-inverted form, i.e. `cset_field() ^ 1`. Clang ground truth:
    /// `b.mi` = cond 0x4, `b.ge` = 0xA, `b.gt` = 0xC.
    fn bcond_field(self) -> u32 {
        self.cset_field() ^ 1
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

/// `movz wd, #imm16, lsl #(16*hw)` — zero the register and set the `hw`-th
/// halfword. The shifted form the leading write of [`mov_imm64`] needs when the
/// first non-zero halfword is NOT halfword 0 (e.g. f64 `-0.0` =
/// `0x8000_0000_0000_0000`).
pub fn movz_hw(rd: Reg, imm16: u16, hw: u8) -> u32 {
    movz(rd, imm16) | ((hw as u32) << 21)
}

/// `movk wd, #imm16, lsl #(16*hw)` — keep other bits, set the `hw`-th halfword.
pub fn movk(rd: Reg, imm16: u16, hw: u8) -> u32 {
    0x7280_0000 | ((hw as u32) << 21) | ((imm16 as u32) << 5) | (rd as u32)
}

/// `ret` (`ret x30`).
pub fn ret() -> u32 {
    0xD65F_03C0
}

/// The stack-pointer register operand (architectural number 31 in the
/// base-register position of a load/store or an add/sub-immediate, where 31
/// means SP rather than the zero register).
pub const SP: Reg = 31;

/// `str xt, [xn, #imm]` — 64-bit store, unsigned scaled offset. `imm` is a BYTE
/// offset that must be a multiple of 8 (the 64-bit access size); the encoded
/// `imm12` field is `imm/8`. Used to zero-init and write non-param local frame
/// slots (#851). Clang ground truth: `str x9, [sp, #8]` = 0xF90007E9.
pub fn str_x_imm(rt: Reg, rn: Reg, imm: u32) -> u32 {
    debug_assert!(imm.is_multiple_of(8), "str x offset must be 8-byte aligned");
    let imm12 = imm / 8;
    debug_assert!(imm12 < 0x1000, "str x offset out of unsigned-imm12 range");
    0xF900_0000 | (imm12 << 10) | ((rn as u32) << 5) | (rt as u32)
}

/// `ldr xt, [xn, #imm]` — 64-bit load, unsigned scaled offset (byte offset,
/// multiple of 8). The copy-semantics read of a non-param local frame slot
/// (#851): each `local.get` loads a FRESH register so a later `local.set` to the
/// same index cannot alias a value already on the stack. Clang ground truth:
/// `ldr x9, [sp, #8]` = 0xF94007E9.
pub fn ldr_x_imm(rt: Reg, rn: Reg, imm: u32) -> u32 {
    debug_assert!(imm.is_multiple_of(8), "ldr x offset must be 8-byte aligned");
    let imm12 = imm / 8;
    debug_assert!(imm12 < 0x1000, "ldr x offset out of unsigned-imm12 range");
    0xF940_0000 | (imm12 << 10) | ((rn as u32) << 5) | (rt as u32)
}

/// `sub xd, xn, #imm12` — 64-bit subtract of an unsigned 12-bit immediate (no
/// shift). Used to LOWER the stack pointer by the non-param-local frame size at
/// prologue. Clang ground truth: `sub sp, sp, #16` = 0xD10043FF.
pub fn sub_imm64(rd: Reg, rn: Reg, imm12: u32) -> u32 {
    debug_assert!(imm12 < 0x1000, "sub imm12 out of range");
    0xD100_0000 | (imm12 << 10) | ((rn as u32) << 5) | (rd as u32)
}

/// `add xd, xn, #imm12` — 64-bit add of an unsigned 12-bit immediate (no shift).
/// RAISES the stack pointer back at epilogue. Clang: `add sp, sp, #16` = 0x910043FF.
pub fn add_imm64(rd: Reg, rn: Reg, imm12: u32) -> u32 {
    debug_assert!(imm12 < 0x1000, "add imm12 out of range");
    0x9100_0000 | (imm12 << 10) | ((rn as u32) << 5) | (rd as u32)
}

/// `brk #imm16` — A64 breakpoint/trap. Used for wasm `unreachable` (#665) and
/// the m4 trunc-guard trap path: WASM §4.4.5 requires an unconditional trap,
/// the A64 analogue of Thumb-2 `udf #0` / RV32 `ebreak`.
pub fn brk(imm16: u16) -> u32 {
    0xD420_0000 | ((imm16 as u32) << 5)
}

/// `b.<cond> #(imm19*4)` — conditional branch, PC-relative in words. Used by
/// the m4 trunc domain guards to SKIP the `brk` trap when the operand is
/// proven in-range (`b.mi +2` hops exactly over the following `brk`). Clang
/// ground truth: `b.mi .+8` = 0x5400_0044 (imm19 = 2, cond = MI = 0x4).
pub fn bcond(cond: Cond, imm19: i32) -> u32 {
    0x5400_0000 | (((imm19 as u32) & 0x7FFFF) << 5) | cond.bcond_field()
}

/// `b #(imm26*4)` — unconditional PC-relative branch, offset in words (signed
/// 26-bit). Used by the void-block control lowering to reach a forward block-end
/// label. Clang ground truth: `b .+8` = 0x1400_0002 (imm26 = 2).
pub fn b_uncond(imm26: i32) -> u32 {
    0x1400_0000 | ((imm26 as u32) & 0x03FF_FFFF)
}

/// `cbnz wt, #(imm19*4)` — compare-and-branch-if-nonzero, 32-bit form, offset in
/// words (signed 19-bit). WASM `br_if` branches when the popped i32 condition is
/// nonzero, so `cbnz w_cond, <block-end>` is the exact lowering. Clang ground
/// truth: `cbnz w9, .+8` = 0x3500_0049 (imm19 = 2, Rt = 9).
pub fn cbnz(rt: Reg, imm19: i32) -> u32 {
    0x3500_0000 | (((imm19 as u32) & 0x7FFFF) << 5) | (rt as u32)
}

/// `cbz wt, #(imm19*4)` — compare-and-branch-if-zero, 32-bit form. Symmetric
/// partner of [`cbnz`]; kept for completeness. Clang: `cbz w9, .+8` = 0x3400_0049.
pub fn cbz(rt: Reg, imm19: i32) -> u32 {
    0x3400_0000 | (((imm19 as u32) & 0x7FFFF) << 5) | (rt as u32)
}

/// `bic wd, wn, wm` — AND with complement (`wd = wn & !wm`). Used by the
/// copysign lowering to clear the sign bit with the SAME mask register that
/// isolates the source sign (one materialized mask instead of two).
pub fn bic(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    dp3(0x0A20_0000, rd, rn, rm)
}
/// `bic xd, xn, xm`
pub fn bic64(rd: Reg, rn: Reg, rm: Reg) -> u32 {
    dp3_sf(0x0A20_0000, true, rd, rn, rm)
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
    // First non-zero halfword becomes the movz; if all zero, movz #0. The movz
    // MUST carry the halfword's shift (`lsl #(16*first)`) — a plain `movz`
    // would deposit it in halfword 0 (the latent m3 bug that hit every constant
    // whose low halfwords are all zero, e.g. f64 -0.0 = 0x8000_0000_0000_0000
    // and the 2^31 trunc-guard boundary 0x41E0_0000_0000_0000; clang ground
    // truth: `movz x0, #0x8000, lsl #48` = 0xD2F0_0000, not 0xD290_0000).
    let first = hw.iter().position(|&h| h != 0).unwrap_or(0);
    let mut out = vec![movz_hw(rd, hw[first], first as u8) | SF64];
    for (i, &h) in hw.iter().enumerate() {
        if i != first && h != 0 {
            out.push(movk(rd, h, i as u8) | SF64);
        }
    }
    out
}

// ===========================================================================
// Milestone 3 — scalar floating point (V/D/S register file).
//
// A64 keeps floats in a SEPARATE register file (V0..V31; the `s`/`d` views are
// the low 32/64 bits). Data-processing float ops name V registers by number in
// the same [20:16]/[9:5]/[4:0] fields as the integer forms, but the opcode's
// `ftype` field at bits [23:22] selects single (00) vs double (01) precision —
// NOT the `sf` bit. `FMOV` between the GP and FP files is the only bridge.
//
// Every base below is derived from `clang -target aarch64-linux-gnu` ground
// truth (see the `fp_*` tests): assemble the mnemonic, read the 32-bit word,
// subtract the operand fields.
//
// SOUNDNESS: the float→int truncations that TRAP in WASM on out-of-range /NaN
// (`i32.trunc_f32_s` and friends) are NOT encoded here — A64 `FCVTZS`/`FCVTZU`
// SATURATE instead of trapping (the #709 "more-total-than-WASM" class), so the
// selector loud-declines them rather than emit a silently-wrong saturating
// result. Only the total, non-trapping float ops live here.
// ===========================================================================

/// A float register operand (`0..=31`; the `s`/`d` view is width-selected by the
/// op's `ftype` field, not by the register number).
pub type FReg = u8;

/// A two-source float data-processing op (`Fd = Fn OP Fm`). `base` is the 32-bit
/// single-precision opcode with all operand fields zero; the double-precision
/// twin sets `ftype=01` (bit 22).
fn fp3(base: u32, rd: FReg, rn: FReg, rm: FReg) -> u32 {
    base | ((rm as u32) << 16) | ((rn as u32) << 5) | (rd as u32)
}
/// A one-source float op (`Fd = OP Fn`).
fn fp2(base: u32, rd: FReg, rn: FReg) -> u32 {
    base | ((rn as u32) << 5) | (rd as u32)
}

/// `fadd sd, sn, sm`
pub fn fadd_s(rd: FReg, rn: FReg, rm: FReg) -> u32 {
    fp3(0x1E20_2800, rd, rn, rm)
}
/// `fsub sd, sn, sm`
pub fn fsub_s(rd: FReg, rn: FReg, rm: FReg) -> u32 {
    fp3(0x1E20_3800, rd, rn, rm)
}
/// `fmul sd, sn, sm`
pub fn fmul_s(rd: FReg, rn: FReg, rm: FReg) -> u32 {
    fp3(0x1E20_0800, rd, rn, rm)
}
/// `fdiv sd, sn, sm`
pub fn fdiv_s(rd: FReg, rn: FReg, rm: FReg) -> u32 {
    fp3(0x1E20_1800, rd, rn, rm)
}
/// `fadd dd, dn, dm`
pub fn fadd_d(rd: FReg, rn: FReg, rm: FReg) -> u32 {
    fp3(0x1E60_2800, rd, rn, rm)
}
/// `fsub dd, dn, dm`
pub fn fsub_d(rd: FReg, rn: FReg, rm: FReg) -> u32 {
    fp3(0x1E60_3800, rd, rn, rm)
}
/// `fmul dd, dn, dm`
pub fn fmul_d(rd: FReg, rn: FReg, rm: FReg) -> u32 {
    fp3(0x1E60_0800, rd, rn, rm)
}
/// `fdiv dd, dn, dm`
pub fn fdiv_d(rd: FReg, rn: FReg, rm: FReg) -> u32 {
    fp3(0x1E60_1800, rd, rn, rm)
}

/// `fabs sd, sn`
pub fn fabs_s(rd: FReg, rn: FReg) -> u32 {
    fp2(0x1E20_C000, rd, rn)
}
/// `fneg sd, sn`
pub fn fneg_s(rd: FReg, rn: FReg) -> u32 {
    fp2(0x1E21_4000, rd, rn)
}
/// `fsqrt sd, sn`
pub fn fsqrt_s(rd: FReg, rn: FReg) -> u32 {
    fp2(0x1E21_C000, rd, rn)
}
/// `fabs dd, dn`
pub fn fabs_d(rd: FReg, rn: FReg) -> u32 {
    fp2(0x1E60_C000, rd, rn)
}
/// `fneg dd, dn`
pub fn fneg_d(rd: FReg, rn: FReg) -> u32 {
    fp2(0x1E61_4000, rd, rn)
}
/// `fsqrt dd, dn`
pub fn fsqrt_d(rd: FReg, rn: FReg) -> u32 {
    fp2(0x1E61_C000, rd, rn)
}

/// `fcmp sn, sm` — sets NZCV (unordered ⇒ C=1,V=1). The WASM float predicate is
/// then materialized with a `cset` of the clang-matched condition (see selector).
pub fn fcmp_s(rn: FReg, rm: FReg) -> u32 {
    0x1E20_2000 | ((rm as u32) << 16) | ((rn as u32) << 5)
}
/// `fcmp dn, dm`
pub fn fcmp_d(rn: FReg, rm: FReg) -> u32 {
    0x1E60_2000 | ((rm as u32) << 16) | ((rn as u32) << 5)
}

// ---------------------------------------------------------------------------
// Milestone 4 — min/max + guarded trapping truncation.
//
// `FMIN`/`FMAX` (NOT the `NM` variants) implement IEEE 754-2019
// minimum/maximum: either-NaN ⇒ NaN, and -0.0 < +0.0 — EXACTLY WASM
// `f{32,64}.{min,max}` semantics (`FMINNM`/`FMAXNM` are minNum/maxNum, which
// RETURN THE NUMBER when one operand is NaN — the wrong semantics). Verified
// by execution against wasmtime in aarch64_m4_trunc_minmax_538_differential.py
// (NaN + ±0 matrix), not assumed.
//
// `FCVTZS`/`FCVTZU` SATURATE on out-of-range/NaN where WASM TRAPS (#709), so
// they are ONLY emitted behind the selector's fcmp+b.cond+brk domain guard —
// on the guarded path every reachable input is in-range, where the two
// semantics agree.
// ---------------------------------------------------------------------------

/// `fmin sd, sn, sm` — IEEE 754-2019 minimum (NaN-propagating, -0 < +0).
pub fn fmin_s(rd: FReg, rn: FReg, rm: FReg) -> u32 {
    fp3(0x1E20_5800, rd, rn, rm)
}
/// `fmax sd, sn, sm` — IEEE 754-2019 maximum (NaN-propagating, -0 < +0).
pub fn fmax_s(rd: FReg, rn: FReg, rm: FReg) -> u32 {
    fp3(0x1E20_4800, rd, rn, rm)
}
/// `fmin dd, dn, dm`
pub fn fmin_d(rd: FReg, rn: FReg, rm: FReg) -> u32 {
    fp3(0x1E60_5800, rd, rn, rm)
}
/// `fmax dd, dn, dm`
pub fn fmax_d(rd: FReg, rn: FReg, rm: FReg) -> u32 {
    fp3(0x1E60_4800, rd, rn, rm)
}

/// `fcvtzs wd, sn` — f32 → signed i32, round-toward-zero. SATURATES: emit only
/// behind the trunc domain guard.
pub fn fcvtzs_w_from_s(rd: Reg, rn: FReg) -> u32 {
    fp2(0x1E38_0000, rd, rn)
}
/// `fcvtzu wd, sn` — f32 → unsigned i32, round-toward-zero. Saturating; guarded.
pub fn fcvtzu_w_from_s(rd: Reg, rn: FReg) -> u32 {
    fp2(0x1E39_0000, rd, rn)
}
/// `fcvtzs wd, dn` — f64 → signed i32, round-toward-zero. Saturating; guarded.
pub fn fcvtzs_w_from_d(rd: Reg, rn: FReg) -> u32 {
    fp2(0x1E78_0000, rd, rn)
}
/// `fcvtzu wd, dn` — f64 → unsigned i32, round-toward-zero. Saturating; guarded.
pub fn fcvtzu_w_from_d(rd: Reg, rn: FReg) -> u32 {
    fp2(0x1E79_0000, rd, rn)
}

// #782a: the 64-bit-destination (`x`) FCVTZ forms (sf=1). The saturating
// behavior (NaN → 0, out-of-range → INT64_MIN/MAX / 0/UINT64_MAX) that the
// TRAPPING trunc lowerings must guard against is EXACTLY the WASM §4.3.2
// `trunc_sat` semantics, so the i64 trunc_sat lowerings emit these bare.
/// `fcvtzs xd, sn` — f32 → signed i64, round-toward-zero, saturating.
pub fn fcvtzs_x_from_s(rd: Reg, rn: FReg) -> u32 {
    fp2(0x9E38_0000, rd, rn)
}
/// `fcvtzu xd, sn` — f32 → unsigned i64, round-toward-zero, saturating.
pub fn fcvtzu_x_from_s(rd: Reg, rn: FReg) -> u32 {
    fp2(0x9E39_0000, rd, rn)
}
/// `fcvtzs xd, dn` — f64 → signed i64, round-toward-zero, saturating.
pub fn fcvtzs_x_from_d(rd: Reg, rn: FReg) -> u32 {
    fp2(0x9E78_0000, rd, rn)
}
/// `fcvtzu xd, dn` — f64 → unsigned i64, round-toward-zero, saturating.
pub fn fcvtzu_x_from_d(rd: Reg, rn: FReg) -> u32 {
    fp2(0x9E79_0000, rd, rn)
}

/// `fmov sd, wn` — reinterpret the 32-bit GP register `wn` into `sd` (no numeric
/// conversion). Bridges the GP→FP files; used for `f32.reinterpret_i32`, moving a
/// materialized f32 const bit-pattern into an S register, and float param setup.
pub fn fmov_s_from_w(rd: FReg, rn: Reg) -> u32 {
    fp2(0x1E27_0000, rd, rn)
}
/// `fmov wd, sn` — reinterpret `sn`'s 32 bits into GP `wd` (`i32.reinterpret_f32`,
/// and funneling a float result to `w0`).
pub fn fmov_w_from_s(rd: Reg, rn: FReg) -> u32 {
    fp2(0x1E26_0000, rd, rn)
}
/// `fmov dd, xn` — reinterpret 64-bit GP `xn` into `dd` (`f64.reinterpret_i64`).
pub fn fmov_d_from_x(rd: FReg, rn: Reg) -> u32 {
    fp2(0x9E67_0000, rd, rn)
}
/// `fmov xd, dn` — reinterpret `dn` into GP `xd` (`i64.reinterpret_f64`, and
/// funneling an f64 result to `x0`).
pub fn fmov_x_from_d(rd: Reg, rn: FReg) -> u32 {
    fp2(0x9E66_0000, rd, rn)
}
/// `fmov sd, sn` — copy between S registers.
pub fn fmov_s(rd: FReg, rn: FReg) -> u32 {
    fp2(0x1E20_4000, rd, rn)
}
/// `fmov dd, dn` — copy between D registers.
pub fn fmov_d(rd: FReg, rn: FReg) -> u32 {
    fp2(0x1E60_4000, rd, rn)
}

/// `fcvt dd, sn` — single→double (`f64.promote_f32`). Exact, never traps.
pub fn fcvt_d_from_s(rd: FReg, rn: FReg) -> u32 {
    fp2(0x1E22_C000, rd, rn)
}
/// `fcvt sd, dn` — double→single (`f32.demote_f64`). Round-to-nearest, never
/// traps (overflow ⇒ ±inf, matching WASM demote).
pub fn fcvt_s_from_d(rd: FReg, rn: FReg) -> u32 {
    fp2(0x1E62_4000, rd, rn)
}

/// `scvtf sd, wn` — signed i32 → f32 (`f32.convert_i32_s`). Total.
pub fn scvtf_s_from_w(rd: FReg, rn: Reg) -> u32 {
    fp2(0x1E22_0000, rd, rn)
}
/// `ucvtf sd, wn` — unsigned i32 → f32 (`f32.convert_i32_u`). Total.
pub fn ucvtf_s_from_w(rd: FReg, rn: Reg) -> u32 {
    fp2(0x1E23_0000, rd, rn)
}
/// `scvtf dd, wn` — signed i32 → f64 (`f64.convert_i32_s`). Exact, total.
pub fn scvtf_d_from_w(rd: FReg, rn: Reg) -> u32 {
    fp2(0x1E62_0000, rd, rn)
}
/// `ucvtf dd, wn` — unsigned i32 → f64 (`f64.convert_i32_u`). Exact, total.
pub fn ucvtf_d_from_w(rd: FReg, rn: Reg) -> u32 {
    fp2(0x1E63_0000, rd, rn)
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

    // #851 non-param-local frame ops. Ground truth from
    // `clang -target aarch64-linux-gnu` (assemble, objdump, read the word).
    #[test]
    fn local_frame_encodings_match_clang() {
        // str x9, [sp]        = f90003e9 ; str x9, [sp, #8]  = f90007e9
        assert_eq!(str_x_imm(9, SP, 0), 0xF900_03E9);
        assert_eq!(str_x_imm(9, SP, 8), 0xF900_07E9);
        // str xzr, [sp]       = f90003ff ; str xzr, [sp, #16] = f9000bff
        assert_eq!(str_x_imm(XZR, SP, 0), 0xF900_03FF);
        assert_eq!(str_x_imm(XZR, SP, 16), 0xF900_0BFF);
        // ldr x9, [sp]        = f94003e9 ; ldr x10, [sp, #8]  = f94007ea
        assert_eq!(ldr_x_imm(9, SP, 0), 0xF940_03E9);
        assert_eq!(ldr_x_imm(10, SP, 8), 0xF940_07EA);
        // sub sp, sp, #16     = d10043ff ; add sp, sp, #16     = 910043ff
        assert_eq!(sub_imm64(SP, SP, 16), 0xD100_43FF);
        assert_eq!(add_imm64(SP, SP, 16), 0x9100_43FF);
        // sub sp, sp, #32     = d10083ff
        assert_eq!(sub_imm64(SP, SP, 32), 0xD100_83FF);
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

    // Milestone 3 — scalar float. Ground truth from `clang -target
    // aarch64-linux-gnu` (assemble mnemonic, `objdump -d`, read the word).
    #[test]
    fn fp_arith_encodings_match_clang() {
        assert_eq!(fadd_s(0, 1, 2), 0x1E22_2820);
        assert_eq!(fsub_s(3, 4, 5), 0x1E25_3883);
        assert_eq!(fmul_s(6, 7, 8), 0x1E28_08E6);
        assert_eq!(fdiv_s(9, 10, 11), 0x1E2B_1949);
        assert_eq!(fadd_d(0, 1, 2), 0x1E62_2820);
        assert_eq!(fsub_d(3, 4, 5), 0x1E65_3883);
        assert_eq!(fmul_d(6, 7, 8), 0x1E68_08E6);
        assert_eq!(fdiv_d(9, 10, 11), 0x1E6B_1949);
    }

    #[test]
    fn fp_unary_encodings_match_clang() {
        assert_eq!(fabs_s(0, 1), 0x1E20_C020);
        assert_eq!(fneg_s(2, 3), 0x1E21_4062);
        assert_eq!(fsqrt_s(4, 5), 0x1E21_C0A4);
        assert_eq!(fabs_d(0, 1), 0x1E60_C020);
        assert_eq!(fneg_d(2, 3), 0x1E61_4062);
        assert_eq!(fsqrt_d(4, 5), 0x1E61_C0A4);
    }

    #[test]
    fn fp_cmp_and_mi_cond_match_clang() {
        assert_eq!(fcmp_s(0, 1), 0x1E21_2000);
        assert_eq!(fcmp_d(0, 1), 0x1E61_2000);
        // WASM float `lt` → `cset mi` (clang f32/f64 `<` lowering).
        assert_eq!(cset(0, Cond::Mi), 0x1A9F_57E0);
    }

    #[test]
    fn fmov_bridge_encodings_match_clang() {
        assert_eq!(fmov_s_from_w(0, 1), 0x1E27_0020);
        assert_eq!(fmov_w_from_s(0, 1), 0x1E26_0020);
        assert_eq!(fmov_d_from_x(0, 1), 0x9E67_0020);
        assert_eq!(fmov_x_from_d(0, 1), 0x9E66_0020);
        assert_eq!(fmov_s(5, 6), 0x1E20_40C5);
        assert_eq!(fmov_d(5, 6), 0x1E60_40C5);
    }

    #[test]
    fn fp_convert_encodings_match_clang() {
        assert_eq!(fcvt_d_from_s(0, 1), 0x1E22_C020);
        assert_eq!(fcvt_s_from_d(0, 1), 0x1E62_4020);
        assert_eq!(scvtf_s_from_w(0, 1), 0x1E22_0020);
        assert_eq!(ucvtf_s_from_w(0, 1), 0x1E23_0020);
        assert_eq!(scvtf_d_from_w(0, 1), 0x1E62_0020);
        assert_eq!(ucvtf_d_from_w(0, 1), 0x1E63_0020);
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

    #[test]
    fn mov_imm64_leading_movz_carries_the_halfword_shift() {
        // The latent m3 bug: when the FIRST non-zero halfword is not hw 0, the
        // leading movz must be the SHIFTED form. Clang ground truth:
        //   mov x0, #0x8000000000000000  →  movz x0, #0x8000, lsl #48 = 0xD2F0_0000
        //   mov x0, #0x41e0000000000000  →  movz x0, #0x41e0, lsl #48 = 0xD2E8_3C00
        // (f64 -0.0 and the 2^31 f64 trunc-guard boundary, respectively).
        assert_eq!(mov_imm64(0, 0x8000_0000_0000_0000), vec![0xD2F0_0000]);
        assert_eq!(mov_imm64(0, 0x41E0_0000_0000_0000), vec![0xD2E8_3C00]);
        // Mixed: 0x0001_0000 → movz w/ hw=1 then nothing else.
        assert_eq!(mov_imm64(3, 0x0001_0000), vec![movz_hw(3, 1, 1) | SF64]);
    }

    // Milestone 4 — trunc guards + min/max. Ground truth from `clang -target
    // aarch64-linux-gnu` (assemble mnemonic, `objdump -d`, read the word).
    #[test]
    fn m4_fcvtz_encodings_match_clang() {
        assert_eq!(fcvtzs_w_from_s(0, 1), 0x1E38_0020);
        assert_eq!(fcvtzu_w_from_s(0, 1), 0x1E39_0020);
        assert_eq!(fcvtzs_w_from_d(0, 1), 0x1E78_0020);
        assert_eq!(fcvtzu_w_from_d(0, 1), 0x1E79_0020);
        assert_eq!(fcvtzs_w_from_s(5, 6), 0x1E38_00C5);
    }

    // #782a — the x-destination (i64-target) FCVTZ forms. Ground truth from
    // `clang -target aarch64-none-elf` + objdump on this exact operand set.
    #[test]
    fn trunc_sat_782_fcvtz_x_encodings_match_clang() {
        assert_eq!(fcvtzs_x_from_s(0, 1), 0x9E38_0020);
        assert_eq!(fcvtzu_x_from_s(0, 1), 0x9E39_0020);
        assert_eq!(fcvtzs_x_from_d(0, 1), 0x9E78_0020);
        assert_eq!(fcvtzu_x_from_d(0, 1), 0x9E79_0020);
        assert_eq!(fcvtzs_x_from_s(5, 6), 0x9E38_00C5);
        assert_eq!(fcvtzu_x_from_d(9, 15), 0x9E79_01E9);
    }

    #[test]
    fn m4_fmin_fmax_encodings_match_clang() {
        assert_eq!(fmin_s(0, 1, 2), 0x1E22_5820);
        assert_eq!(fmax_s(3, 4, 5), 0x1E25_4883);
        assert_eq!(fmin_d(0, 1, 2), 0x1E62_5820);
        assert_eq!(fmax_d(3, 4, 5), 0x1E65_4883);
    }

    #[test]
    fn m4_bcond_bic_encodings_match_clang() {
        // b.mi .+8 / b.ge .+8 / b.gt .+8 / b.mi .+12
        assert_eq!(bcond(Cond::Mi, 2), 0x5400_0044);
        assert_eq!(bcond(Cond::Ge, 2), 0x5400_004A);
        assert_eq!(bcond(Cond::Gt, 2), 0x5400_004C);
        assert_eq!(bcond(Cond::Mi, 3), 0x5400_0064);
        assert_eq!(bic(0, 1, 2), 0x0A22_0020);
        assert_eq!(bic64(3, 4, 5), 0x8A25_0083);
    }

    #[test]
    fn control_branch_encodings_match_clang() {
        // Void-block control lowering: unconditional b, cbnz, cbz.
        // clang -target aarch64: `b .+8` = 0x14000002; `cbnz w9,.+8` = 0x35000049;
        // `cbz w9,.+8` = 0x34000049. Negative offsets use the signed field.
        assert_eq!(b_uncond(2), 0x1400_0002);
        assert_eq!(b_uncond(-2), 0x17FF_FFFE); // b .-8
        assert_eq!(cbnz(9, 2), 0x3500_0049);
        assert_eq!(cbz(9, 2), 0x3400_0049);
        assert_eq!(cbnz(0, 3), 0x3500_0060); // cbnz w0, .+12
    }
}
