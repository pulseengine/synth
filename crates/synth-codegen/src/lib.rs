//! ARM Thumb-2 Code Generation
//!
//! This module translates optimized IR with register allocation to ARM Thumb-2 assembly.

use std::fmt;
use synth_opt::{Instruction, Opcode, Reg};
use synth_regalloc::PhysicalReg;

/// ARM Thumb-2 instruction
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArmInstruction {
    // Data processing
    Mov {
        rd: PhysicalReg,
        op: ArmOperand,
    },
    Mvn {
        rd: PhysicalReg,
        op: ArmOperand,
    },
    Add {
        rd: PhysicalReg,
        rn: PhysicalReg,
        op: ArmOperand,
    },
    Sub {
        rd: PhysicalReg,
        rn: PhysicalReg,
        op: ArmOperand,
    },
    Mul {
        rd: PhysicalReg,
        rn: PhysicalReg,
        rm: PhysicalReg,
    },
    Sdiv {
        rd: PhysicalReg,
        rn: PhysicalReg,
        rm: PhysicalReg,
    },
    Udiv {
        rd: PhysicalReg,
        rn: PhysicalReg,
        rm: PhysicalReg,
    },

    // Bitwise
    And {
        rd: PhysicalReg,
        rn: PhysicalReg,
        op: ArmOperand,
    },
    Orr {
        rd: PhysicalReg,
        rn: PhysicalReg,
        op: ArmOperand,
    },
    Eor {
        rd: PhysicalReg,
        rn: PhysicalReg,
        op: ArmOperand,
    },
    Lsl {
        rd: PhysicalReg,
        rn: PhysicalReg,
        op: ArmOperand,
    },
    Lsr {
        rd: PhysicalReg,
        rn: PhysicalReg,
        op: ArmOperand,
    },
    Asr {
        rd: PhysicalReg,
        rn: PhysicalReg,
        op: ArmOperand,
    },

    // Comparison
    Cmp {
        rn: PhysicalReg,
        op: ArmOperand,
    },

    // Memory
    Ldr {
        rd: PhysicalReg,
        addr: MemoryAddress,
    },
    Str {
        rd: PhysicalReg,
        addr: MemoryAddress,
    },
    Push {
        regs: Vec<PhysicalReg>,
    },
    Pop {
        regs: Vec<PhysicalReg>,
    },

    // Control flow
    B {
        label: String,
    },
    Beq {
        label: String,
    },
    Bne {
        label: String,
    },
    Blt {
        label: String,
    },
    Ble {
        label: String,
    },
    Bgt {
        label: String,
    },
    Bge {
        label: String,
    },
    Bl {
        function: String,
    },
    Bx {
        rm: PhysicalReg,
    },

    // Special
    Nop,
    Label {
        name: String,
    },
}

/// ARM operand (register or immediate)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArmOperand {
    Reg(PhysicalReg),
    Imm(i32),
}

/// Memory addressing mode
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MemoryAddress {
    /// [Rn, #offset]
    Offset { base: PhysicalReg, offset: i32 },
    /// [SP, #offset]
    StackOffset { offset: i32 },
}

impl fmt::Display for ArmInstruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArmInstruction::Mov { rd, op } => {
                write!(f, "    mov {}, {}", rd.to_str(), op)
            }
            ArmInstruction::Mvn { rd, op } => {
                write!(f, "    mvn {}, {}", rd.to_str(), op)
            }
            ArmInstruction::Add { rd, rn, op } => {
                write!(f, "    add {}, {}, {}", rd.to_str(), rn.to_str(), op)
            }
            ArmInstruction::Sub { rd, rn, op } => {
                write!(f, "    sub {}, {}, {}", rd.to_str(), rn.to_str(), op)
            }
            ArmInstruction::Mul { rd, rn, rm } => {
                write!(
                    f,
                    "    mul {}, {}, {}",
                    rd.to_str(),
                    rn.to_str(),
                    rm.to_str()
                )
            }
            ArmInstruction::Sdiv { rd, rn, rm } => {
                write!(
                    f,
                    "    sdiv {}, {}, {}",
                    rd.to_str(),
                    rn.to_str(),
                    rm.to_str()
                )
            }
            ArmInstruction::Udiv { rd, rn, rm } => {
                write!(
                    f,
                    "    udiv {}, {}, {}",
                    rd.to_str(),
                    rn.to_str(),
                    rm.to_str()
                )
            }
            ArmInstruction::And { rd, rn, op } => {
                write!(f, "    and {}, {}, {}", rd.to_str(), rn.to_str(), op)
            }
            ArmInstruction::Orr { rd, rn, op } => {
                write!(f, "    orr {}, {}, {}", rd.to_str(), rn.to_str(), op)
            }
            ArmInstruction::Eor { rd, rn, op } => {
                write!(f, "    eor {}, {}, {}", rd.to_str(), rn.to_str(), op)
            }
            ArmInstruction::Lsl { rd, rn, op } => {
                write!(f, "    lsl {}, {}, {}", rd.to_str(), rn.to_str(), op)
            }
            ArmInstruction::Lsr { rd, rn, op } => {
                write!(f, "    lsr {}, {}, {}", rd.to_str(), rn.to_str(), op)
            }
            ArmInstruction::Asr { rd, rn, op } => {
                write!(f, "    asr {}, {}, {}", rd.to_str(), rn.to_str(), op)
            }
            ArmInstruction::Cmp { rn, op } => {
                write!(f, "    cmp {}, {}", rn.to_str(), op)
            }
            ArmInstruction::Ldr { rd, addr } => {
                write!(f, "    ldr {}, {}", rd.to_str(), addr)
            }
            ArmInstruction::Str { rd, addr } => {
                write!(f, "    str {}, {}", rd.to_str(), addr)
            }
            ArmInstruction::Push { regs } => {
                let reg_list = regs
                    .iter()
                    .map(|r| r.to_str())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "    push {{{}}}", reg_list)
            }
            ArmInstruction::Pop { regs } => {
                let reg_list = regs
                    .iter()
                    .map(|r| r.to_str())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "    pop {{{}}}", reg_list)
            }
            ArmInstruction::B { label } => {
                write!(f, "    b {}", label)
            }
            ArmInstruction::Beq { label } => {
                write!(f, "    beq {}", label)
            }
            ArmInstruction::Bne { label } => {
                write!(f, "    bne {}", label)
            }
            ArmInstruction::Blt { label } => {
                write!(f, "    blt {}", label)
            }
            ArmInstruction::Ble { label } => {
                write!(f, "    ble {}", label)
            }
            ArmInstruction::Bgt { label } => {
                write!(f, "    bgt {}", label)
            }
            ArmInstruction::Bge { label } => {
                write!(f, "    bge {}", label)
            }
            ArmInstruction::Bl { function } => {
                write!(f, "    bl {}", function)
            }
            ArmInstruction::Bx { rm } => {
                write!(f, "    bx {}", rm.to_str())
            }
            ArmInstruction::Nop => {
                write!(f, "    nop")
            }
            ArmInstruction::Label { name } => {
                write!(f, "{}:", name)
            }
        }
    }
}

impl fmt::Display for ArmOperand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArmOperand::Reg(reg) => write!(f, "{}", reg.to_str()),
            ArmOperand::Imm(val) => write!(f, "#{}", val),
        }
    }
}

impl fmt::Display for MemoryAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MemoryAddress::Offset { base, offset } => {
                write!(f, "[{}, #{}]", base.to_str(), offset)
            }
            MemoryAddress::StackOffset { offset } => {
                write!(f, "[sp, #{}]", offset)
            }
        }
    }
}

/// Code generator for ARM Thumb-2
pub struct CodeGenerator {
    /// Generated ARM instructions
    instructions: Vec<ArmInstruction>,
    /// Label counter for generating unique labels
    label_counter: usize,
}

impl CodeGenerator {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            label_counter: 0,
        }
    }

    /// Generate ARM code from IR instructions with register allocation
    pub fn generate(
        &mut self,
        ir_instructions: &[Instruction],
        allocation: &std::collections::HashMap<Reg, PhysicalReg>,
    ) -> Result<(), String> {
        for inst in ir_instructions {
            if inst.is_dead {
                continue;
            }

            self.generate_instruction(&inst.opcode, allocation)?;
        }

        Ok(())
    }

    /// Generate ARM instruction from IR opcode
    fn generate_instruction(
        &mut self,
        opcode: &Opcode,
        allocation: &std::collections::HashMap<Reg, PhysicalReg>,
    ) -> Result<(), String> {
        match opcode {
            Opcode::Const { dest, value } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                self.emit(ArmInstruction::Mov {
                    rd,
                    op: ArmOperand::Imm(*value),
                });
            }

            Opcode::Add { dest, src1, src2 } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                let rn = self.get_physical_reg(src1, allocation)?;
                let rm = self.get_physical_reg(src2, allocation)?;
                self.emit(ArmInstruction::Add {
                    rd,
                    rn,
                    op: ArmOperand::Reg(rm),
                });
            }

            Opcode::Sub { dest, src1, src2 } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                let rn = self.get_physical_reg(src1, allocation)?;
                let rm = self.get_physical_reg(src2, allocation)?;
                self.emit(ArmInstruction::Sub {
                    rd,
                    rn,
                    op: ArmOperand::Reg(rm),
                });
            }

            Opcode::Mul { dest, src1, src2 } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                let rn = self.get_physical_reg(src1, allocation)?;
                let rm = self.get_physical_reg(src2, allocation)?;
                self.emit(ArmInstruction::Mul { rd, rn, rm });
            }

            Opcode::DivS { dest, src1, src2 } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                let rn = self.get_physical_reg(src1, allocation)?;
                let rm = self.get_physical_reg(src2, allocation)?;
                self.emit(ArmInstruction::Sdiv { rd, rn, rm });
            }

            Opcode::DivU { dest, src1, src2 } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                let rn = self.get_physical_reg(src1, allocation)?;
                let rm = self.get_physical_reg(src2, allocation)?;
                self.emit(ArmInstruction::Udiv { rd, rn, rm });
            }

            Opcode::And { dest, src1, src2 } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                let rn = self.get_physical_reg(src1, allocation)?;
                let rm = self.get_physical_reg(src2, allocation)?;
                self.emit(ArmInstruction::And {
                    rd,
                    rn,
                    op: ArmOperand::Reg(rm),
                });
            }

            Opcode::Or { dest, src1, src2 } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                let rn = self.get_physical_reg(src1, allocation)?;
                let rm = self.get_physical_reg(src2, allocation)?;
                self.emit(ArmInstruction::Orr {
                    rd,
                    rn,
                    op: ArmOperand::Reg(rm),
                });
            }

            Opcode::Xor { dest, src1, src2 } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                let rn = self.get_physical_reg(src1, allocation)?;
                let rm = self.get_physical_reg(src2, allocation)?;
                self.emit(ArmInstruction::Eor {
                    rd,
                    rn,
                    op: ArmOperand::Reg(rm),
                });
            }

            Opcode::Shl { dest, src1, src2 } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                let rn = self.get_physical_reg(src1, allocation)?;
                let rm = self.get_physical_reg(src2, allocation)?;
                self.emit(ArmInstruction::Lsl {
                    rd,
                    rn,
                    op: ArmOperand::Reg(rm),
                });
            }

            Opcode::ShrU { dest, src1, src2 } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                let rn = self.get_physical_reg(src1, allocation)?;
                let rm = self.get_physical_reg(src2, allocation)?;
                self.emit(ArmInstruction::Lsr {
                    rd,
                    rn,
                    op: ArmOperand::Reg(rm),
                });
            }

            Opcode::ShrS { dest, src1, src2 } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                let rn = self.get_physical_reg(src1, allocation)?;
                let rm = self.get_physical_reg(src2, allocation)?;
                self.emit(ArmInstruction::Asr {
                    rd,
                    rn,
                    op: ArmOperand::Reg(rm),
                });
            }

            Opcode::Eq { dest, src1, src2 } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                let rn = self.get_physical_reg(src1, allocation)?;
                let rm = self.get_physical_reg(src2, allocation)?;
                // cmp rn, rm; moveq rd, #1; movne rd, #0
                self.emit(ArmInstruction::Cmp {
                    rn,
                    op: ArmOperand::Reg(rm),
                });
                self.emit(ArmInstruction::Mov {
                    rd,
                    op: ArmOperand::Imm(0),
                });
                // Would need conditional execution or branches
            }

            Opcode::Load { dest, addr } => {
                let rd = self.get_physical_reg(dest, allocation)?;
                self.emit(ArmInstruction::Ldr {
                    rd,
                    addr: MemoryAddress::StackOffset {
                        offset: *addr as i32,
                    },
                });
            }

            Opcode::Store { src, addr } => {
                let rs = self.get_physical_reg(src, allocation)?;
                self.emit(ArmInstruction::Str {
                    rd: rs,
                    addr: MemoryAddress::StackOffset {
                        offset: *addr as i32,
                    },
                });
            }

            Opcode::Return { value } => {
                if let Some(vreg) = value {
                    let rs = self.get_physical_reg(vreg, allocation)?;
                    // Move return value to R0 if not already there
                    if rs != PhysicalReg::R0 {
                        self.emit(ArmInstruction::Mov {
                            rd: PhysicalReg::R0,
                            op: ArmOperand::Reg(rs),
                        });
                    }
                }
                self.emit(ArmInstruction::Bx {
                    rm: PhysicalReg::LR,
                });
            }

            Opcode::Nop => {
                self.emit(ArmInstruction::Nop);
            }

            _ => {
                return Err(format!("Unsupported opcode: {:?}", opcode));
            }
        }

        Ok(())
    }

    /// Emit an ARM instruction
    fn emit(&mut self, inst: ArmInstruction) {
        self.instructions.push(inst);
    }

    /// Get physical register from virtual register
    fn get_physical_reg(
        &self,
        vreg: &Reg,
        allocation: &std::collections::HashMap<Reg, PhysicalReg>,
    ) -> Result<PhysicalReg, String> {
        allocation
            .get(vreg)
            .copied()
            .ok_or_else(|| format!("No allocation for {:?}", vreg))
    }

    /// Generate a unique label
    pub fn gen_label(&mut self, prefix: &str) -> String {
        let label = format!("{}{}", prefix, self.label_counter);
        self.label_counter += 1;
        label
    }

    /// Get generated instructions
    pub fn instructions(&self) -> &[ArmInstruction] {
        &self.instructions
    }

    /// Generate assembly code as string
    pub fn to_asm(&self) -> String {
        self.instructions
            .iter()
            .map(|inst| inst.to_string())
            .collect::<Vec<_>>()
            .join("\n")
    }
}

impl Default for CodeGenerator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_mov() {
        let mut codegen = CodeGenerator::new();
        let mut allocation = std::collections::HashMap::new();
        allocation.insert(Reg(0), PhysicalReg::R0);

        let instructions = vec![Instruction {
            id: 0,
            opcode: Opcode::Const {
                dest: Reg(0),
                value: 42,
            },
            block_id: 0,
            is_dead: false,
        }];

        codegen.generate(&instructions, &allocation).unwrap();

        assert_eq!(codegen.instructions.len(), 1);
        assert_eq!(
            codegen.instructions[0],
            ArmInstruction::Mov {
                rd: PhysicalReg::R0,
                op: ArmOperand::Imm(42)
            }
        );
    }

    #[test]
    fn test_add_instruction() {
        let mut codegen = CodeGenerator::new();
        let mut allocation = std::collections::HashMap::new();
        allocation.insert(Reg(0), PhysicalReg::R0);
        allocation.insert(Reg(1), PhysicalReg::R1);
        allocation.insert(Reg(2), PhysicalReg::R2);

        let instructions = vec![Instruction {
            id: 0,
            opcode: Opcode::Add {
                dest: Reg(2),
                src1: Reg(0),
                src2: Reg(1),
            },
            block_id: 0,
            is_dead: false,
        }];

        codegen.generate(&instructions, &allocation).unwrap();

        assert_eq!(codegen.instructions.len(), 1);
        assert_eq!(
            codegen.instructions[0],
            ArmInstruction::Add {
                rd: PhysicalReg::R2,
                rn: PhysicalReg::R0,
                op: ArmOperand::Reg(PhysicalReg::R1)
            }
        );
    }

    #[test]
    fn test_asm_output() {
        let mut codegen = CodeGenerator::new();
        let mut allocation = std::collections::HashMap::new();
        allocation.insert(Reg(0), PhysicalReg::R0);
        allocation.insert(Reg(1), PhysicalReg::R1);
        allocation.insert(Reg(2), PhysicalReg::R2);

        let instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const {
                    dest: Reg(0),
                    value: 10,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Const {
                    dest: Reg(1),
                    value: 20,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::Add {
                    dest: Reg(2),
                    src1: Reg(0),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        codegen.generate(&instructions, &allocation).unwrap();

        let asm = codegen.to_asm();
        assert!(asm.contains("mov r0, #10"));
        assert!(asm.contains("mov r1, #20"));
        assert!(asm.contains("add r2, r0, r1"));
    }
}
