//! RISC-V instruction representation.
//!
//! These are *post-instruction-selection* enum values — the equivalent of
//! `synth_synthesis::ArmOp` for ARM. The instruction selector emits these;
//! the encoder translates them to 32-bit machine words.
//!
//! Each variant maps to a single base RV32I/M/A instruction. Pseudo-ops
//! (e.g. `li`, `mv`, `nop`) are expressed via existing variants — for
//! example `mv rd, rs` → `Addi { rd, rs1: rs, imm: 0 }`.

use crate::register::Reg;

/// Branch condition for the `Branch` instruction (BEQ/BNE/BLT/BGE/BLTU/BGEU).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Branch {
    /// Branch if equal (`beq`)
    Eq,
    /// Branch if not equal (`bne`)
    Ne,
    /// Branch if less-than, signed (`blt`)
    Lt,
    /// Branch if greater-or-equal, signed (`bge`)
    Ge,
    /// Branch if less-than, unsigned (`bltu`)
    Ltu,
    /// Branch if greater-or-equal, unsigned (`bgeu`)
    Geu,
}

impl Branch {
    /// funct3 field for the branch instruction.
    pub fn funct3(self) -> u8 {
        match self {
            Branch::Eq => 0b000,
            Branch::Ne => 0b001,
            Branch::Lt => 0b100,
            Branch::Ge => 0b101,
            Branch::Ltu => 0b110,
            Branch::Geu => 0b111,
        }
    }
}

/// CSR (Control and Status Register) — used for trap setup, mtvec, mstatus, etc.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Csr(pub u16);

impl Csr {
    pub const MSTATUS: Csr = Csr(0x300);
    pub const MISA: Csr = Csr(0x301);
    pub const MIE: Csr = Csr(0x304);
    pub const MTVEC: Csr = Csr(0x305);
    pub const MEPC: Csr = Csr(0x341);
    pub const MCAUSE: Csr = Csr(0x342);
    pub const MTVAL: Csr = Csr(0x343);
    pub const MIP: Csr = Csr(0x344);
}

/// A single RISC-V instruction (post-selection, pre-encoding).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RiscVOp {
    // ──────────────────────────────────────────────────────────────────
    // RV32I — base integer
    // ──────────────────────────────────────────────────────────────────

    // U-type — load upper immediate
    /// `lui rd, imm20` — load (imm20 << 12) into rd
    Lui { rd: Reg, imm20: u32 },
    /// `auipc rd, imm20` — pc + (imm20 << 12)
    Auipc { rd: Reg, imm20: u32 },

    // J-type / I-type — jumps
    /// `jal rd, label` — pc-relative; `rd` gets pc+4 as link
    Jal { rd: Reg, label: String },
    /// `jalr rd, imm(rs1)` — register-indirect; `rd` gets pc+4 as link
    Jalr { rd: Reg, rs1: Reg, imm: i32 },

    // B-type — branches
    /// Branch if `cond(rs1, rs2)` — pc-relative to label
    Branch {
        cond: Branch,
        rs1: Reg,
        rs2: Reg,
        label: String,
    },

    // I-type — register/immediate ops
    /// `addi rd, rs1, imm` — rd = rs1 + sign_extend(imm12)
    Addi { rd: Reg, rs1: Reg, imm: i32 },
    /// `slti rd, rs1, imm` — rd = (rs1 <s imm) ? 1 : 0
    Slti { rd: Reg, rs1: Reg, imm: i32 },
    /// `sltiu rd, rs1, imm` — rd = (rs1 <u imm) ? 1 : 0
    Sltiu { rd: Reg, rs1: Reg, imm: i32 },
    /// `xori rd, rs1, imm`
    Xori { rd: Reg, rs1: Reg, imm: i32 },
    /// `ori rd, rs1, imm`
    Ori { rd: Reg, rs1: Reg, imm: i32 },
    /// `andi rd, rs1, imm`
    Andi { rd: Reg, rs1: Reg, imm: i32 },
    /// `slli rd, rs1, shamt` — shift logical left, shamt 0..31
    Slli { rd: Reg, rs1: Reg, shamt: u8 },
    /// `srli rd, rs1, shamt` — shift logical right
    Srli { rd: Reg, rs1: Reg, shamt: u8 },
    /// `srai rd, rs1, shamt` — shift arithmetic right
    Srai { rd: Reg, rs1: Reg, shamt: u8 },

    // R-type — register/register ops
    /// `add rd, rs1, rs2`
    Add { rd: Reg, rs1: Reg, rs2: Reg },
    /// `sub rd, rs1, rs2`
    Sub { rd: Reg, rs1: Reg, rs2: Reg },
    /// `sll rd, rs1, rs2` — register shift logical left
    Sll { rd: Reg, rs1: Reg, rs2: Reg },
    /// `slt rd, rs1, rs2` — set if less-than (signed)
    Slt { rd: Reg, rs1: Reg, rs2: Reg },
    /// `sltu rd, rs1, rs2` — set if less-than (unsigned)
    Sltu { rd: Reg, rs1: Reg, rs2: Reg },
    /// `xor rd, rs1, rs2`
    Xor { rd: Reg, rs1: Reg, rs2: Reg },
    /// `srl rd, rs1, rs2`
    Srl { rd: Reg, rs1: Reg, rs2: Reg },
    /// `sra rd, rs1, rs2`
    Sra { rd: Reg, rs1: Reg, rs2: Reg },
    /// `or rd, rs1, rs2`
    Or { rd: Reg, rs1: Reg, rs2: Reg },
    /// `and rd, rs1, rs2`
    And { rd: Reg, rs1: Reg, rs2: Reg },

    // I-type — loads
    /// `lb rd, imm(rs1)` — sign-extending byte load
    Lb { rd: Reg, rs1: Reg, imm: i32 },
    /// `lh rd, imm(rs1)` — sign-extending halfword load
    Lh { rd: Reg, rs1: Reg, imm: i32 },
    /// `lw rd, imm(rs1)` — word load
    Lw { rd: Reg, rs1: Reg, imm: i32 },
    /// `lbu rd, imm(rs1)` — zero-extending byte load
    Lbu { rd: Reg, rs1: Reg, imm: i32 },
    /// `lhu rd, imm(rs1)` — zero-extending halfword load
    Lhu { rd: Reg, rs1: Reg, imm: i32 },

    // S-type — stores
    /// `sb rs2, imm(rs1)` — store byte
    Sb { rs1: Reg, rs2: Reg, imm: i32 },
    /// `sh rs2, imm(rs1)` — store halfword
    Sh { rs1: Reg, rs2: Reg, imm: i32 },
    /// `sw rs2, imm(rs1)` — store word
    Sw { rs1: Reg, rs2: Reg, imm: i32 },

    // System / fence — used by trap handlers and ordering
    /// `ecall` — environment call (used for syscalls and trap exits)
    Ecall,
    /// `ebreak` — debugger breakpoint
    Ebreak,
    /// `mret` — return from machine-mode trap
    Mret,
    /// `wfi` — wait for interrupt (suspend until exception/interrupt)
    Wfi,
    /// `fence` — memory ordering (skeleton emits the canonical fence)
    Fence,

    // Zicsr — CSR manipulation (needed for any trap setup)
    /// `csrrw rd, csr, rs1` — atomic read+write CSR
    Csrrw { rd: Reg, csr: Csr, rs1: Reg },
    /// `csrrs rd, csr, rs1` — atomic read+set bits
    Csrrs { rd: Reg, csr: Csr, rs1: Reg },
    /// `csrrc rd, csr, rs1` — atomic read+clear bits
    Csrrc { rd: Reg, csr: Csr, rs1: Reg },
    /// `csrrwi rd, csr, uimm5`
    Csrrwi { rd: Reg, csr: Csr, uimm5: u8 },
    /// `csrrsi rd, csr, uimm5`
    Csrrsi { rd: Reg, csr: Csr, uimm5: u8 },
    /// `csrrci rd, csr, uimm5`
    Csrrci { rd: Reg, csr: Csr, uimm5: u8 },

    // ──────────────────────────────────────────────────────────────────
    // M-extension — multiply / divide
    // ──────────────────────────────────────────────────────────────────
    /// `mul rd, rs1, rs2` — low 32 bits of signed×signed
    Mul { rd: Reg, rs1: Reg, rs2: Reg },
    /// `mulh rd, rs1, rs2` — high 32 bits of signed×signed
    Mulh { rd: Reg, rs1: Reg, rs2: Reg },
    /// `mulhsu rd, rs1, rs2` — high 32 bits of signed×unsigned
    Mulhsu { rd: Reg, rs1: Reg, rs2: Reg },
    /// `mulhu rd, rs1, rs2` — high 32 bits of unsigned×unsigned
    Mulhu { rd: Reg, rs1: Reg, rs2: Reg },
    /// `div rd, rs1, rs2` — signed divide
    Div { rd: Reg, rs1: Reg, rs2: Reg },
    /// `divu rd, rs1, rs2` — unsigned divide
    Divu { rd: Reg, rs1: Reg, rs2: Reg },
    /// `rem rd, rs1, rs2` — signed remainder
    Rem { rd: Reg, rs1: Reg, rs2: Reg },
    /// `remu rd, rs1, rs2` — unsigned remainder
    Remu { rd: Reg, rs1: Reg, rs2: Reg },

    // ──────────────────────────────────────────────────────────────────
    // Pseudo-ops & label support
    // ──────────────────────────────────────────────────────────────────
    /// Forward/backward label marker — does not encode to bytes itself.
    /// The ELF builder resolves these to byte offsets when emitting
    /// `Jal`/`Branch` targets.
    Label { name: String },

    /// Called function (linker-resolved). Emits `auipc + jalr` pair when
    /// the target is out of `jal`'s ±1 MiB range; the encoder picks.
    Call { label: String },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn branch_funct3_values() {
        assert_eq!(Branch::Eq.funct3(), 0b000);
        assert_eq!(Branch::Ne.funct3(), 0b001);
        assert_eq!(Branch::Lt.funct3(), 0b100);
        assert_eq!(Branch::Ge.funct3(), 0b101);
        assert_eq!(Branch::Ltu.funct3(), 0b110);
        assert_eq!(Branch::Geu.funct3(), 0b111);
    }

    #[test]
    fn standard_csrs() {
        assert_eq!(Csr::MSTATUS.0, 0x300);
        assert_eq!(Csr::MTVEC.0, 0x305);
        assert_eq!(Csr::MEPC.0, 0x341);
    }
}
