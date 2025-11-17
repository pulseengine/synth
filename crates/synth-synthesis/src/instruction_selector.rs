//! Instruction Selection - Converts WebAssembly IR to ARM instructions
//!
//! Uses pattern matching to select optimal ARM instruction sequences

use crate::rules::{ArmOp, MemAddr, Operand2, Replacement, Reg, SynthesisRule, WasmOp};
use crate::{Bindings, PatternMatcher};
use std::collections::HashMap;
use synth_core::Result;

/// ARM instruction with operands
#[derive(Debug, Clone, PartialEq)]
pub struct ArmInstruction {
    /// The ARM operation
    pub op: ArmOp,
    /// Source line (for debugging)
    pub source_line: Option<usize>,
}

/// Convert register index to Reg enum
fn index_to_reg(index: u8) -> Reg {
    match index % 13 {  // R0-R12 only, avoid SP/LR/PC
        0 => Reg::R0,
        1 => Reg::R1,
        2 => Reg::R2,
        3 => Reg::R3,
        4 => Reg::R4,
        5 => Reg::R5,
        6 => Reg::R6,
        7 => Reg::R7,
        8 => Reg::R8,
        9 => Reg::R9,
        10 => Reg::R10,
        11 => Reg::R11,
        _ => Reg::R12,
    }
}

/// Register allocator state
#[derive(Debug, Clone)]
pub struct RegisterState {
    /// Next available register
    next_reg: u8,
    /// Register map for variables
    var_map: HashMap<String, Reg>,
}

impl RegisterState {
    /// Create a new register state
    pub fn new() -> Self {
        Self {
            next_reg: 0,
            var_map: HashMap::new(),
        }
    }

    /// Allocate a new register
    pub fn alloc_reg(&mut self) -> Reg {
        let reg = index_to_reg(self.next_reg);
        self.next_reg = (self.next_reg + 1) % 13; // R0-R12
        reg
    }

    /// Get or allocate register for variable
    pub fn get_or_alloc(&mut self, var: &str) -> Reg {
        if let Some(&reg) = self.var_map.get(var) {
            reg
        } else {
            let reg = self.alloc_reg();
            self.var_map.insert(var.to_string(), reg);
            reg
        }
    }

    /// Reset allocator
    pub fn reset(&mut self) {
        self.next_reg = 0;
        self.var_map.clear();
    }
}

impl Default for RegisterState {
    fn default() -> Self {
        Self::new()
    }
}

/// Instruction selector
pub struct InstructionSelector {
    /// Pattern matcher with synthesis rules
    matcher: PatternMatcher,
    /// Register allocator
    regs: RegisterState,
}

impl InstructionSelector {
    /// Create a new instruction selector
    pub fn new(rules: Vec<SynthesisRule>) -> Self {
        Self {
            matcher: PatternMatcher::new(rules),
            regs: RegisterState::new(),
        }
    }

    /// Select ARM instructions for a sequence of WASM operations
    pub fn select(&mut self, wasm_ops: &[WasmOp]) -> Result<Vec<ArmInstruction>> {
        let mut arm_instructions = Vec::new();
        let mut index = 0;

        while index < wasm_ops.len() {
            let remaining = &wasm_ops[index..];
            let matches = self.matcher.match_sequence(remaining);

            if let Some(best_match) = matches.first() {
                // Apply the rule to generate ARM instructions
                let arm_ops = self.apply_replacement(&best_match.rule.replacement, &best_match.bindings)?;

                for op in arm_ops {
                    arm_instructions.push(ArmInstruction {
                        op,
                        source_line: Some(index),
                    });
                }

                index += best_match.length;
            } else {
                // No rule matched - generate default instruction
                let arm_op = self.select_default(&wasm_ops[index])?;
                arm_instructions.push(ArmInstruction {
                    op: arm_op,
                    source_line: Some(index),
                });
                index += 1;
            }
        }

        Ok(arm_instructions)
    }

    /// Apply a replacement pattern to generate ARM instructions
    fn apply_replacement(&mut self, replacement: &Replacement, _bindings: &Bindings) -> Result<Vec<ArmOp>> {
        match replacement {
            Replacement::Identity => {
                // For identity replacement, generate a default instruction
                Ok(vec![ArmOp::Mov {
                    rd: Reg::R0,
                    op2: Operand2::Reg(Reg::R0),
                }])
            }

            Replacement::ArmInstr(op) => {
                // Single ARM instruction
                Ok(vec![op.clone()])
            }

            Replacement::ArmSequence(ops) => {
                // Sequence of ARM instructions
                Ok(ops.clone())
            }

            Replacement::Var(_var_name) => {
                // Use variable from pattern - would substitute from bindings
                Ok(vec![ArmOp::Nop])  // Placeholder
            }

            Replacement::Inline => {
                // Inline function call - would inline the function body
                Ok(vec![ArmOp::Nop])  // Placeholder
            }
        }
    }

    /// Select default ARM instruction for a WASM operation (no pattern match)
    fn select_default(&mut self, wasm_op: &WasmOp) -> Result<ArmOp> {
        use WasmOp::*;

        let rd = self.regs.alloc_reg();
        let rn = self.regs.alloc_reg();
        let rm = self.regs.alloc_reg();

        Ok(match wasm_op {
            I32Add => ArmOp::Add {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            },

            I32Sub => ArmOp::Sub {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            },

            I32Mul => ArmOp::Mul { rd, rn, rm },

            I32And => ArmOp::And {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            },

            I32Or => ArmOp::Orr {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            },

            I32Xor => ArmOp::Eor {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            },

            I32Shl => ArmOp::Lsl {
                rd,
                rn,
                shift: 0,  // Placeholder - would extract from operand
            },

            I32ShrS => ArmOp::Asr {
                rd,
                rn,
                shift: 0,
            },

            I32ShrU => ArmOp::Lsr {
                rd,
                rn,
                shift: 0,
            },

            // Rotate operations
            I32Rotl => {
                // Rotate left: ROR rd, rn, #(32-shift)
                // For now, simplified with shift=0
                ArmOp::Ror {
                    rd,
                    rn,
                    shift: 0,  // Would be 32 - actual_shift
                }
            },

            I32Rotr => ArmOp::Ror {
                rd,
                rn,
                shift: 0,  // Placeholder - would extract from operand
            },

            // Bit count operations
            I32Clz => ArmOp::Clz {
                rd,
                rm,
            },

            I32Ctz => {
                // Count trailing zeros: RBIT + CLZ
                // This would need to be a sequence, but for now return RBIT
                ArmOp::Rbit {
                    rd,
                    rm,
                }
            },

            I32Popcnt => {
                // Population count - no native ARM instruction
                // Would need to implement with sequence
                // Placeholder for now
                ArmOp::Nop
            },

            I32Const(val) => {
                let imm_val = if *val >= 0 {
                    *val as i32
                } else {
                    *val
                };
                ArmOp::Mov {
                    rd,
                    op2: Operand2::Imm(imm_val),
                }
            }

            I32Load { offset, .. } => ArmOp::Ldr {
                rd,
                addr: MemAddr {
                    base: rn,
                    offset: *offset as i32,
                },
            },

            I32Store { offset, .. } => ArmOp::Str {
                rd,
                addr: MemAddr {
                    base: rn,
                    offset: *offset as i32,
                },
            },

            LocalGet(_index) => ArmOp::Ldr {
                rd,
                addr: MemAddr {
                    base: Reg::SP,
                    offset: 0,  // Simplified - would use proper frame offset
                },
            },

            LocalSet(_index) => ArmOp::Str {
                rd,
                addr: MemAddr {
                    base: Reg::SP,
                    offset: 0,
                },
            },

            Call(_func_idx) => ArmOp::Bl {
                label: "func".to_string(),  // Simplified - would use proper target
            },

            // Control flow (simplified - structural control flow)
            Block => ArmOp::Nop,  // Block is a label
            Loop => ArmOp::Nop,   // Loop is a label
            Br(_label) => ArmOp::B {
                label: "br_target".to_string(),
            },
            BrIf(_label) => {
                // Conditional branch - would pop condition from stack
                // For now, placeholder
                ArmOp::B { label: "br_if_target".to_string() }
            },
            Return => ArmOp::Bx { rm: Reg::LR },  // Return via link register

            // Locals
            LocalTee(_index) => {
                // Tee is like set but keeps value on stack
                ArmOp::Str {
                    rd,
                    addr: MemAddr {
                        base: Reg::SP,
                        offset: 0,
                    },
                }
            },

            // Comparisons
            I32Eq => {
                ArmOp::Cmp {
                    rn,
                    op2: Operand2::Reg(rm),
                }
            },
            I32Ne => {
                ArmOp::Cmp {
                    rn,
                    op2: Operand2::Reg(rm),
                }
            },
            I32LtS | I32LtU | I32LeS | I32LeU | I32GtS | I32GtU | I32GeS | I32GeU => {
                ArmOp::Cmp {
                    rn,
                    op2: Operand2::Reg(rm),
                }
            },

            // Division and remainder (ARMv7-M+)
            I32DivS => {
                // Signed division: SDIV Rd, Rn, Rm
                ArmOp::Sdiv { rd, rn, rm }
            },
            I32DivU => {
                // Unsigned division: UDIV Rd, Rn, Rm
                ArmOp::Udiv { rd, rn, rm }
            },
            I32RemS => {
                // Signed remainder: quotient = SDIV Rn, Rm
                // remainder = Rn - (quotient * Rm)
                // For now, simplified to SDIV (would need sequence)
                ArmOp::Sdiv { rd, rn, rm }
            },
            I32RemU => {
                // Unsigned remainder: quotient = UDIV Rn, Rm
                // remainder = Rn - (quotient * Rm)
                // For now, simplified to UDIV (would need sequence)
                ArmOp::Udiv { rd, rn, rm }
            },

            _ => ArmOp::Nop,  // Other unsupported operations
        })
    }

    /// Get statistics about instruction selection
    pub fn get_stats(&self) -> SelectionStats {
        SelectionStats {
            total_registers_used: self.regs.next_reg as usize,
            variables_mapped: self.regs.var_map.len(),
        }
    }

    /// Reset the selector state
    pub fn reset(&mut self) {
        self.regs.reset();
    }
}

/// Statistics from instruction selection
#[derive(Debug, Clone, Default)]
pub struct SelectionStats {
    /// Total number of registers used
    pub total_registers_used: usize,
    /// Number of variables mapped to registers
    pub variables_mapped: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::RuleDatabase;

    #[test]
    fn test_register_allocation() {
        let mut regs = RegisterState::new();

        let r0 = regs.alloc_reg();
        let r1 = regs.alloc_reg();
        let r2 = regs.alloc_reg();

        assert_eq!(r0, Reg::R0);
        assert_eq!(r1, Reg::R1);
        assert_eq!(r2, Reg::R2);
    }

    #[test]
    fn test_variable_mapping() {
        let mut regs = RegisterState::new();

        let r1 = regs.get_or_alloc("x");
        let r2 = regs.get_or_alloc("y");
        let r3 = regs.get_or_alloc("x");  // Should reuse same register

        assert_eq!(r1, r3);  // Same variable gets same register
        assert_ne!(r1, r2);  // Different variables get different registers
    }

    #[test]
    fn test_instruction_selector_creation() {
        let db = RuleDatabase::new();
        let selector = InstructionSelector::new(db.rules().to_vec());

        assert_eq!(selector.regs.next_reg, 0);
    }

    #[test]
    fn test_select_default_add() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Add];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Add { .. } => {}
            _ => panic!("Expected Add instruction"),
        }
    }

    #[test]
    fn test_select_arithmetic_sequence() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Const(5),
            WasmOp::I32Const(10),
            WasmOp::I32Add,
            WasmOp::I32Const(2),
            WasmOp::I32Mul,
        ];

        let arm_instrs = selector.select(&wasm_ops).unwrap();

        // Should generate at least one instruction per WASM op
        assert!(arm_instrs.len() >= wasm_ops.len());
    }

    #[test]
    fn test_select_memory_operations() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Load {
                offset: 0,
                align: 4,
            },
            WasmOp::I32Const(42),
            WasmOp::I32Store {
                offset: 4,
                align: 4,
            },
        ];

        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 3);

        // First should be load
        match &arm_instrs[0].op {
            ArmOp::Ldr { .. } => {}
            _ => panic!("Expected Ldr instruction"),
        }

        // Last should be store
        match &arm_instrs[2].op {
            ArmOp::Str { .. } => {}
            _ => panic!("Expected Str instruction"),
        }
    }

    #[test]
    fn test_selector_stats() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Add, WasmOp::I32Sub, WasmOp::I32Mul];
        let _ = selector.select(&wasm_ops).unwrap();

        let stats = selector.get_stats();
        assert!(stats.total_registers_used > 0);
    }

    #[test]
    fn test_selector_reset() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Add];
        let _ = selector.select(&wasm_ops).unwrap();

        assert!(selector.regs.next_reg > 0);

        selector.reset();
        assert_eq!(selector.regs.next_reg, 0);
    }

    #[test]
    fn test_bitwise_operations() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32And, WasmOp::I32Or, WasmOp::I32Xor];

        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 3);

        match &arm_instrs[0].op {
            ArmOp::And { .. } => {}
            _ => panic!("Expected And"),
        }

        match &arm_instrs[1].op {
            ArmOp::Orr { .. } => {}
            _ => panic!("Expected Orr"),
        }

        match &arm_instrs[2].op {
            ArmOp::Eor { .. } => {}
            _ => panic!("Expected Eor"),
        }
    }

    #[test]
    fn test_shift_operations() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Shl, WasmOp::I32ShrS, WasmOp::I32ShrU];

        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 3);

        match &arm_instrs[0].op {
            ArmOp::Lsl { .. } => {}
            _ => panic!("Expected Lsl"),
        }

        match &arm_instrs[1].op {
            ArmOp::Asr { .. } => {}
            _ => panic!("Expected Asr"),
        }

        match &arm_instrs[2].op {
            ArmOp::Lsr { .. } => {}
            _ => panic!("Expected Lsr"),
        }
    }

    #[test]
    fn test_index_to_reg_conversion() {
        assert_eq!(index_to_reg(0), Reg::R0);
        assert_eq!(index_to_reg(1), Reg::R1);
        assert_eq!(index_to_reg(12), Reg::R12);
        assert_eq!(index_to_reg(13), Reg::R0);  // Wraps around
    }
}
