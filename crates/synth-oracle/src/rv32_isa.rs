//! RQ-91-RV32ISA (Refs #1744): an RV32 instruction-set DECODER, independent
//! of synth's encoder, that says which standard extension each emitted
//! instruction belongs to.
//!
//! unicorn cannot emulate a restricted RV32 core: its models are RV32IMAC
//! (SiFive E31), RV32GC-ish (`BASE32`, `SIFIVE_U34`), and a `misa` write is
//! dropped because no model sets `RISCV_FEATURE_MISA` (unicorn-engine-sys
//! 2.1.5, `qemu/target/riscv/csr.c` `write_misa`). So the profile is enforced
//! BY DECODE: every instruction in every emitted function must decode into
//! the declared extension set. Accepted code then executes on the E31, a
//! superset, which gives the profile core's result for code the decode
//! proved stays inside the profile.
//!
//! The classification is from the ISA manual's opcode map (Volume I, "RV32/64G
//! Instruction Set Listings" and the RVC quadrant table), not from synth's
//! `RiscVOp`, so an encoder bug that emitted, say, an AMO under a wrong
//! opcode would be classified by what the BITS are.

/// The extension an instruction belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Ext {
    /// RV32I base, with Zicsr and Zifencei (CSR ops, `fence`, `fence.i`,
    /// `ecall`/`ebreak`/`mret`/`wfi`).
    I,
    M,
    A,
    /// A 16-bit compressed instruction.
    C,
    /// F or D (loads/stores, arithmetic, fused multiply-add).
    FD,
    /// Not a valid RV32 encoding in any extension this decoder knows.
    Unknown,
}

/// A declared profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Profile {
    pub name: &'static str,
    pub m: bool,
    pub a: bool,
    pub c: bool,
}

impl Profile {
    pub const fn new(name: &'static str, m: bool, a: bool, c: bool) -> Self {
        Self { name, m, a, c }
    }

    /// Whether an instruction of extension `e` may appear under this profile.
    pub fn allows(&self, e: Ext) -> bool {
        match e {
            Ext::I => true,
            Ext::M => self.m,
            Ext::A => self.a,
            Ext::C => self.c,
            Ext::FD | Ext::Unknown => false,
        }
    }

    /// The `e_flags` an object of this profile must carry: `EF_RISCV_RVC`
    /// iff C, float-ABI bits 0 (ILP32 soft-float).
    pub fn e_flags(&self) -> u32 {
        u32::from(self.c)
    }
}

/// Classify one 32-bit instruction word (low two bits `11`).
pub fn classify32(w: u32) -> Ext {
    let opcode = w & 0x7F;
    let funct3 = (w >> 12) & 0x7;
    let funct7 = w >> 25;
    match opcode {
        0x37 | 0x17 | 0x6F => Ext::I,                 // LUI, AUIPC, JAL
        0x67 if funct3 == 0 => Ext::I,                // JALR
        0x63 if funct3 != 2 && funct3 != 3 => Ext::I, // BRANCH
        0x03 if matches!(funct3, 0 | 1 | 2 | 4 | 5) => Ext::I, // LB..LHU
        0x23 if funct3 <= 2 => Ext::I,                // SB, SH, SW
        0x13 => match funct3 {
            1 if funct7 == 0 => Ext::I,                   // SLLI
            5 if funct7 == 0 || funct7 == 0x20 => Ext::I, // SRLI, SRAI
            1 | 5 => Ext::Unknown,
            _ => Ext::I,
        },
        0x33 => match funct7 {
            0x00 => Ext::I,
            0x20 if funct3 == 0 || funct3 == 5 => Ext::I, // SUB, SRA
            0x01 => Ext::M,
            _ => Ext::Unknown,
        },
        0x0F if funct3 <= 1 => Ext::I, // FENCE, FENCE.I
        0x73 => Ext::I,                // ECALL/EBREAK/MRET/WFI, Zicsr
        0x2F if funct3 == 2 => Ext::A, // LR.W/SC.W/AMO*.W
        0x07 | 0x27 | 0x43 | 0x47 | 0x4B | 0x4F | 0x53 => Ext::FD,
        _ => Ext::Unknown,
    }
}

/// One decoded instruction: offset within the function, raw bits, length.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Insn {
    pub offset: usize,
    pub bits: u32,
    pub len: usize,
    pub ext: Ext,
}

/// Walk `code` instruction by instruction (2 bytes when the low two bits are
/// not `11`, else 4). The all-zero halfword is the defined-illegal
/// instruction and classifies [`Ext::Unknown`], as does a 32-bit
/// instruction cut off at the end, and the 48/64-bit prefixes.
pub fn decode(code: &[u8]) -> Vec<Insn> {
    let mut out = Vec::new();
    let mut i = 0;
    while i + 2 <= code.len() {
        let lo = u16::from_le_bytes([code[i], code[i + 1]]);
        if lo & 0b11 != 0b11 {
            let ext = if lo == 0 { Ext::Unknown } else { Ext::C };
            out.push(Insn {
                offset: i,
                bits: u32::from(lo),
                len: 2,
                ext,
            });
            i += 2;
            continue;
        }
        if lo & 0b1_1100 == 0b1_1100 || i + 4 > code.len() {
            // 48-bit+ prefix, or a truncated 32-bit instruction.
            out.push(Insn {
                offset: i,
                bits: u32::from(lo),
                len: 2,
                ext: Ext::Unknown,
            });
            i += 2;
            continue;
        }
        let w = u32::from_le_bytes([code[i], code[i + 1], code[i + 2], code[i + 3]]);
        out.push(Insn {
            offset: i,
            bits: w,
            len: 4,
            ext: classify32(w),
        });
        i += 4;
    }
    if i < code.len() {
        out.push(Insn {
            offset: i,
            bits: u32::from(code[i]),
            len: 1,
            ext: Ext::Unknown,
        });
    }
    out
}

/// The instructions in `code` that `profile` does not allow.
pub fn violations(profile: &Profile, code: &[u8]) -> Vec<Insn> {
    decode(code)
        .into_iter()
        .filter(|i| !profile.allows(i.ext))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const RV32I: Profile = Profile::new("rv32i", false, false, false);
    const RV32IMC: Profile = Profile::new("rv32imc", true, false, true);
    const RV32IMAC: Profile = Profile::new("rv32imac", true, true, true);

    fn bytes(ws: &[u32]) -> Vec<u8> {
        ws.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    // Encodings cross-checked against the ISA manual's tables (and GNU as).
    const ADD_T2_T0_T1: u32 = 0x0062_83B3; // add t2, t0, t1
    const MUL_T2_T0_T1: u32 = 0x0262_83B3; // mul t2, t0, t1
    const REMU_T1_T2_T0: u32 = 0x0253_F333; // remu t1, t2, t0
    const AMOADD_W: u32 = 0x00C5_A52F; // amoadd.w a0, a2, (a1)
    const LR_W: u32 = 0x1005_A52F; // lr.w a0, (a1)
    const EBREAK: u32 = 0x0010_0073;
    const RET: u32 = 0x0000_8067; // jalr x0, 0(ra)
    const FLW: u32 = 0x0005_2007; // flw f0, 0(a0)
    const CSRRW_MTVEC: u32 = 0x3052_9073; // csrw mtvec, t0

    #[test]
    fn classifies_by_the_opcode_map() {
        assert_eq!(classify32(ADD_T2_T0_T1), Ext::I);
        assert_eq!(classify32(MUL_T2_T0_T1), Ext::M);
        assert_eq!(classify32(REMU_T1_T2_T0), Ext::M);
        assert_eq!(classify32(AMOADD_W), Ext::A);
        assert_eq!(classify32(LR_W), Ext::A);
        assert_eq!(classify32(EBREAK), Ext::I);
        assert_eq!(classify32(RET), Ext::I);
        assert_eq!(classify32(FLW), Ext::FD);
        assert_eq!(classify32(CSRRW_MTVEC), Ext::I);
        assert_eq!(classify32(0xFFFF_FFFF), Ext::Unknown);
        // OP with funct7 0x20 is only SUB/SRA.
        assert_eq!(classify32(0x4062_83B3), Ext::I); // sub t2, t0, t1
        assert_eq!(classify32(0x4062_C3B3), Ext::Unknown); // funct3=4, funct7=0x20
    }

    #[test]
    fn walks_mixed_lengths() {
        // c.addi a0, 1 (0x0505), then mul.
        let mut code = vec![0x05, 0x05];
        code.extend(MUL_T2_T0_T1.to_le_bytes());
        let d = decode(&code);
        assert_eq!(d.len(), 2);
        assert_eq!((d[0].len, d[0].ext), (2, Ext::C));
        assert_eq!((d[1].offset, d[1].ext), (2, Ext::M));
        // Zero padding is the illegal instruction, never "compressed".
        assert_eq!(decode(&[0, 0])[0].ext, Ext::Unknown);
        // Truncated 32-bit instruction.
        assert_eq!(decode(&[0x33, 0x83])[0].ext, Ext::Unknown);
    }

    /// POTENCY: each profile reds on exactly what it lacks.
    #[test]
    fn profiles_red_on_what_they_lack() {
        let base = bytes(&[ADD_T2_T0_T1, EBREAK, RET]);
        for p in [RV32I, RV32IMC, RV32IMAC] {
            assert!(violations(&p, &base).is_empty(), "{}", p.name);
        }
        let m = bytes(&[ADD_T2_T0_T1, MUL_T2_T0_T1, RET]);
        assert_eq!(violations(&RV32I, &m).len(), 1);
        assert!(violations(&RV32IMC, &m).is_empty());
        let a = bytes(&[AMOADD_W, RET]);
        assert_eq!(violations(&RV32IMC, &a).len(), 1);
        assert!(violations(&RV32IMAC, &a).is_empty());
        let c = [0x05u8, 0x05, 0x67, 0x80, 0x00, 0x00];
        assert_eq!(violations(&RV32I, &c).len(), 1);
        assert!(violations(&RV32IMC, &c).is_empty());
        let f = bytes(&[FLW]);
        assert_eq!(violations(&RV32IMAC, &f).len(), 1);
        assert_eq!(RV32I.e_flags(), 0);
        assert_eq!(RV32IMC.e_flags(), 1);
    }
}
