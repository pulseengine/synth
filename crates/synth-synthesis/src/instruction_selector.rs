//! Instruction Selection - Converts WebAssembly IR to ARM instructions
//!
//! Uses pattern matching to select optimal ARM instruction sequences

use crate::rules::{ArmOp, Condition, MemAddr, Operand2, Reg, Replacement, SynthesisRule};
use crate::{Bindings, PatternMatcher};
use std::collections::HashMap;
use synth_core::Result;
use synth_core::WasmOp;

/// Bounds checking configuration for memory operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundsCheckConfig {
    /// No bounds checking (relies on MPU or other hardware protection)
    None,
    /// Software bounds checking with CMP/BHS before each access
    /// R10 holds the memory size, initialized by startup code
    Software,
    /// Masking: AND address with (memory_size - 1) for power-of-2 sizes
    /// Lower overhead but only works with power-of-2 memory sizes
    Masking,
}

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
    match index % 13 {
        // R0-R12 only, avoid SP/LR/PC
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
    /// Bounds checking configuration
    bounds_check: BoundsCheckConfig,
}

impl InstructionSelector {
    /// Create a new instruction selector
    pub fn new(rules: Vec<SynthesisRule>) -> Self {
        Self {
            matcher: PatternMatcher::new(rules),
            regs: RegisterState::new(),
            bounds_check: BoundsCheckConfig::None,
        }
    }

    /// Create a new instruction selector with bounds checking
    pub fn with_bounds_check(rules: Vec<SynthesisRule>, bounds_check: BoundsCheckConfig) -> Self {
        Self {
            matcher: PatternMatcher::new(rules),
            regs: RegisterState::new(),
            bounds_check,
        }
    }

    /// Set bounds checking configuration
    pub fn set_bounds_check(&mut self, config: BoundsCheckConfig) {
        self.bounds_check = config;
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
                let arm_ops =
                    self.apply_replacement(&best_match.rule.replacement, &best_match.bindings)?;

                for op in arm_ops {
                    arm_instructions.push(ArmInstruction {
                        op,
                        source_line: Some(index),
                    });
                }

                index += best_match.length;
            } else {
                // No rule matched - generate default instruction(s)
                let arm_ops = self.select_default(&wasm_ops[index])?;
                for op in arm_ops {
                    arm_instructions.push(ArmInstruction {
                        op,
                        source_line: Some(index),
                    });
                }
                index += 1;
            }
        }

        Ok(arm_instructions)
    }

    /// Apply a replacement pattern to generate ARM instructions
    fn apply_replacement(
        &mut self,
        replacement: &Replacement,
        _bindings: &Bindings,
    ) -> Result<Vec<ArmOp>> {
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
                Ok(vec![ArmOp::Nop]) // Placeholder
            }

            Replacement::Inline => {
                // Inline function call - would inline the function body
                Ok(vec![ArmOp::Nop]) // Placeholder
            }
        }
    }

    /// Select default ARM instruction(s) for a WASM operation (no pattern match)
    /// Returns a sequence of instructions (may include bounds checking for memory ops)
    fn select_default(&mut self, wasm_op: &WasmOp) -> Result<Vec<ArmOp>> {
        use WasmOp::*;

        let rd = self.regs.alloc_reg();
        let rn = self.regs.alloc_reg();
        let rm = self.regs.alloc_reg();

        Ok(match wasm_op {
            I32Add => vec![ArmOp::Add {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            }],

            I32Sub => vec![ArmOp::Sub {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            }],

            I32Mul => vec![ArmOp::Mul { rd, rn, rm }],

            I32And => vec![ArmOp::And {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            }],

            I32Or => vec![ArmOp::Orr {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            }],

            I32Xor => vec![ArmOp::Eor {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            }],

            I32Shl => vec![ArmOp::Lsl {
                rd,
                rn,
                shift: 0, // Placeholder - would extract from operand
            }],

            I32ShrS => vec![ArmOp::Asr { rd, rn, shift: 0 }],

            I32ShrU => vec![ArmOp::Lsr { rd, rn, shift: 0 }],

            // Rotate operations
            I32Rotl => {
                // Rotate left: ROR rd, rn, #(32-shift)
                // For now, simplified with shift=0
                vec![ArmOp::Ror {
                    rd,
                    rn,
                    shift: 0, // Would be 32 - actual_shift
                }]
            }

            I32Rotr => vec![ArmOp::Ror {
                rd,
                rn,
                shift: 0, // Placeholder - would extract from operand
            }],

            // Bit count operations
            I32Clz => vec![ArmOp::Clz { rd, rm }],

            I32Ctz => {
                // Count trailing zeros: RBIT + CLZ
                // This would need to be a sequence, but for now return RBIT
                vec![ArmOp::Rbit { rd, rm }]
            }

            I32Popcnt => {
                // Population count - no native ARM instruction
                // Would need to implement with sequence
                // Placeholder for now
                vec![ArmOp::Nop]
            }

            I32Const(val) => {
                let imm_val = if *val >= 0 { *val as i32 } else { *val };
                vec![ArmOp::Mov {
                    rd,
                    op2: Operand2::Imm(imm_val),
                }]
            }

            I32Load { offset, .. } => {
                // WASM memory access: address from stack (rn) + static offset
                // R11 is the dedicated memory base register for memory 0
                // Effective address = R11 + rn + offset
                self.generate_load_with_bounds_check(rd, rn, *offset as i32, 4)
            }

            I32Store { offset, .. } => {
                // WASM memory access: address from stack (rn) + static offset
                // R11 is the dedicated memory base register for memory 0
                // Effective address = R11 + rn + offset
                self.generate_store_with_bounds_check(rd, rn, *offset as i32, 4)
            }

            LocalGet(_index) => vec![ArmOp::Ldr {
                rd,
                addr: MemAddr::imm(Reg::SP, 0), // Simplified - would use proper frame offset
            }],

            LocalSet(_index) => vec![ArmOp::Str {
                rd,
                addr: MemAddr::imm(Reg::SP, 0),
            }],

            Call(_func_idx) => vec![ArmOp::Bl {
                label: "func".to_string(), // Simplified - would use proper target
            }],

            CallIndirect {
                type_index,
                table_index: _,
            } => {
                // Table index is on top of stack (in rn), call target via table lookup
                // For now, generate the pseudo-instruction; ARM encoder will expand
                vec![ArmOp::CallIndirect {
                    rd,
                    type_idx: *type_index,
                    table_index_reg: rn, // Table index from stack
                }]
            }

            // Control flow (simplified - structural control flow)
            Block => vec![ArmOp::Nop], // Block is a label
            Loop => vec![ArmOp::Nop],  // Loop is a label
            Br(_label) => vec![ArmOp::B {
                label: "br_target".to_string(),
            }],
            BrIf(_label) => {
                // Conditional branch - would pop condition from stack
                // For now, placeholder
                vec![ArmOp::B {
                    label: "br_if_target".to_string(),
                }]
            }
            Return => vec![ArmOp::Bx { rm: Reg::LR }], // Return via link register

            // Locals
            LocalTee(_index) => {
                // Tee is like set but keeps value on stack
                vec![ArmOp::Str {
                    rd,
                    addr: MemAddr::imm(Reg::SP, 0),
                }]
            }

            // Comparisons
            I32Eq => vec![ArmOp::Cmp {
                rn,
                op2: Operand2::Reg(rm),
            }],
            I32Ne => vec![ArmOp::Cmp {
                rn,
                op2: Operand2::Reg(rm),
            }],
            I32LtS | I32LtU | I32LeS | I32LeU | I32GtS | I32GtU | I32GeS | I32GeU => {
                vec![ArmOp::Cmp {
                    rn,
                    op2: Operand2::Reg(rm),
                }]
            }

            // Division and remainder (ARMv7-M+)
            I32DivS => {
                // Signed division: SDIV Rd, Rn, Rm
                vec![ArmOp::Sdiv { rd, rn, rm }]
            }
            I32DivU => {
                // Unsigned division: UDIV Rd, Rn, Rm
                vec![ArmOp::Udiv { rd, rn, rm }]
            }
            I32RemS => {
                // Signed remainder: quotient = SDIV Rn, Rm
                // remainder = Rn - (quotient * Rm)
                // For now, simplified to SDIV (would need sequence)
                vec![ArmOp::Sdiv { rd, rn, rm }]
            }
            I32RemU => {
                // Unsigned remainder: quotient = UDIV Rn, Rm
                // remainder = Rn - (quotient * Rm)
                // For now, simplified to UDIV (would need sequence)
                vec![ArmOp::Udiv { rd, rn, rm }]
            }

            // Sign extension operations
            I32Extend8S => {
                // Sign-extend byte: SXTB Rd, Rm
                vec![ArmOp::Sxtb { rd, rm }]
            }
            I32Extend16S => {
                // Sign-extend halfword: SXTH Rd, Rm
                vec![ArmOp::Sxth { rd, rm }]
            }

            _ => vec![ArmOp::Nop], // Other unsupported operations
        })
    }

    /// Generate a load with optional bounds checking
    /// R10 = memory size, R11 = memory base
    fn generate_load_with_bounds_check(
        &self,
        rd: Reg,
        addr_reg: Reg,
        offset: i32,
        _access_size: u32,
    ) -> Vec<ArmOp> {
        let load_op = ArmOp::Ldr {
            rd,
            addr: MemAddr::reg_imm(Reg::R11, addr_reg, offset),
        };

        match self.bounds_check {
            BoundsCheckConfig::None => vec![load_op],
            BoundsCheckConfig::Software => {
                // Software bounds check sequence:
                // ADD temp, addr_reg, #offset   ; Calculate effective address
                // CMP temp, R10                 ; Compare against memory size (in R10)
                // BHS .trap                     ; Branch to trap if >= memory size
                // LDR rd, [R11, addr_reg, #offset]
                let temp = Reg::R12; // Use R12 as scratch (IP register)
                vec![
                    // Calculate effective address: temp = addr_reg + offset
                    ArmOp::Add {
                        rd: temp,
                        rn: addr_reg,
                        op2: Operand2::Imm(offset),
                    },
                    // Compare against memory size (in R10)
                    ArmOp::Cmp {
                        rn: temp,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    // Branch to trap handler if >= (unsigned)
                    ArmOp::Bhs {
                        label: "Trap_Handler".to_string(),
                    },
                    // Actual load
                    load_op,
                ]
            }
            BoundsCheckConfig::Masking => {
                // Masking approach: AND address with (memory_size - 1)
                // This only works for power-of-2 memory sizes
                // AND addr_reg, addr_reg, R10  ; R10 should contain mask (size - 1)
                // LDR rd, [R11, addr_reg, #offset]
                vec![
                    ArmOp::And {
                        rd: addr_reg,
                        rn: addr_reg,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    load_op,
                ]
            }
        }
    }

    /// Generate a store with optional bounds checking
    /// R10 = memory size (or mask for masking mode), R11 = memory base
    fn generate_store_with_bounds_check(
        &self,
        value_reg: Reg,
        addr_reg: Reg,
        offset: i32,
        _access_size: u32,
    ) -> Vec<ArmOp> {
        let store_op = ArmOp::Str {
            rd: value_reg,
            addr: MemAddr::reg_imm(Reg::R11, addr_reg, offset),
        };

        match self.bounds_check {
            BoundsCheckConfig::None => vec![store_op],
            BoundsCheckConfig::Software => {
                // Software bounds check sequence:
                // ADD temp, addr_reg, #offset   ; Calculate effective address
                // CMP temp, R10                 ; Compare against memory size (in R10)
                // BHS .trap                     ; Branch to trap if >= memory size
                // STR value_reg, [R11, addr_reg, #offset]
                let temp = Reg::R12; // Use R12 as scratch (IP register)
                vec![
                    // Calculate effective address: temp = addr_reg + offset
                    ArmOp::Add {
                        rd: temp,
                        rn: addr_reg,
                        op2: Operand2::Imm(offset),
                    },
                    // Compare against memory size (in R10)
                    ArmOp::Cmp {
                        rn: temp,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    // Branch to trap handler if >= (unsigned)
                    ArmOp::Bhs {
                        label: "Trap_Handler".to_string(),
                    },
                    // Actual store
                    store_op,
                ]
            }
            BoundsCheckConfig::Masking => {
                // Masking approach: AND address with (memory_size - 1)
                vec![
                    ArmOp::And {
                        rd: addr_reg,
                        rn: addr_reg,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    store_op,
                ]
            }
        }
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

    /// Select ARM instructions using a stack-based approach with AAPCS calling convention
    ///
    /// This method properly tracks the WASM virtual stack and generates code that
    /// uses r0-r3 for the first 4 parameters per AAPCS.
    pub fn select_with_stack(
        &mut self,
        wasm_ops: &[WasmOp],
        num_params: u32,
    ) -> Result<Vec<ArmInstruction>> {
        use WasmOp::*;

        let mut instructions = Vec::new();
        // Virtual stack holds register indices
        let mut stack: Vec<Reg> = Vec::new();
        // Next available register for temporaries (start after params)
        let mut next_temp = num_params.min(4) as u8;

        // Map of local index -> register
        let mut local_to_reg: std::collections::HashMap<u32, Reg> =
            std::collections::HashMap::new();
        // First 4 params are in r0-r3
        for i in 0..num_params.min(4) {
            local_to_reg.insert(i, index_to_reg(i as u8));
        }

        for (idx, op) in wasm_ops.iter().enumerate() {
            match op {
                LocalGet(local_idx) => {
                    // Get the register for this local
                    let reg = if let Some(&r) = local_to_reg.get(local_idx) {
                        r
                    } else {
                        // Local not in register (spilled to stack) - load it
                        let dst = index_to_reg(next_temp);
                        next_temp = (next_temp + 1) % 13;
                        instructions.push(ArmInstruction {
                            op: ArmOp::Ldr {
                                rd: dst,
                                addr: MemAddr::imm(Reg::SP, (*local_idx as i32 - 4) * 4),
                            },
                            source_line: Some(idx),
                        });
                        dst
                    };
                    stack.push(reg);
                }

                I32Const(val) => {
                    let dst = index_to_reg(next_temp);
                    next_temp = (next_temp + 1) % 13;
                    instructions.push(ArmInstruction {
                        op: ArmOp::Mov {
                            rd: dst,
                            op2: Operand2::Imm(*val as i32),
                        },
                        source_line: Some(idx),
                    });
                    stack.push(dst);
                }

                I32Add => {
                    let b = stack.pop().unwrap_or(Reg::R1);
                    let a = stack.pop().unwrap_or(Reg::R0);
                    // Result goes in r0 for return value (or temp if not last op)
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        let t = index_to_reg(next_temp);
                        next_temp = (next_temp + 1) % 13;
                        t
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::Add {
                            rd: dst,
                            rn: a,
                            op2: Operand2::Reg(b),
                        },
                        source_line: Some(idx),
                    });
                    stack.push(dst);
                }

                I32Sub => {
                    let b = stack.pop().unwrap_or(Reg::R1);
                    let a = stack.pop().unwrap_or(Reg::R0);
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        index_to_reg(next_temp)
                    };
                    if dst != Reg::R0 {
                        next_temp = (next_temp + 1) % 13;
                    }
                    instructions.push(ArmInstruction {
                        op: ArmOp::Sub {
                            rd: dst,
                            rn: a,
                            op2: Operand2::Reg(b),
                        },
                        source_line: Some(idx),
                    });
                    stack.push(dst);
                }

                I32Mul => {
                    let b = stack.pop().unwrap_or(Reg::R1);
                    let a = stack.pop().unwrap_or(Reg::R0);
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        index_to_reg(next_temp)
                    };
                    if dst != Reg::R0 {
                        next_temp = (next_temp + 1) % 13;
                    }
                    instructions.push(ArmInstruction {
                        op: ArmOp::Mul {
                            rd: dst,
                            rn: a,
                            rm: b,
                        },
                        source_line: Some(idx),
                    });
                    stack.push(dst);
                }

                I32And => {
                    let b = stack.pop().unwrap_or(Reg::R1);
                    let a = stack.pop().unwrap_or(Reg::R0);
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        index_to_reg(next_temp)
                    };
                    if dst != Reg::R0 {
                        next_temp = (next_temp + 1) % 13;
                    }
                    instructions.push(ArmInstruction {
                        op: ArmOp::And {
                            rd: dst,
                            rn: a,
                            op2: Operand2::Reg(b),
                        },
                        source_line: Some(idx),
                    });
                    stack.push(dst);
                }

                I32Or => {
                    let b = stack.pop().unwrap_or(Reg::R1);
                    let a = stack.pop().unwrap_or(Reg::R0);
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        index_to_reg(next_temp)
                    };
                    if dst != Reg::R0 {
                        next_temp = (next_temp + 1) % 13;
                    }
                    instructions.push(ArmInstruction {
                        op: ArmOp::Orr {
                            rd: dst,
                            rn: a,
                            op2: Operand2::Reg(b),
                        },
                        source_line: Some(idx),
                    });
                    stack.push(dst);
                }

                I32Xor => {
                    let b = stack.pop().unwrap_or(Reg::R1);
                    let a = stack.pop().unwrap_or(Reg::R0);
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        index_to_reg(next_temp)
                    };
                    if dst != Reg::R0 {
                        next_temp = (next_temp + 1) % 13;
                    }
                    instructions.push(ArmInstruction {
                        op: ArmOp::Eor {
                            rd: dst,
                            rn: a,
                            op2: Operand2::Reg(b),
                        },
                        source_line: Some(idx),
                    });
                    stack.push(dst);
                }

                // Division operations with trap checks for divide-by-zero
                I32DivU => {
                    let divisor = stack.pop().unwrap_or(Reg::R1); // b (divisor)
                    let dividend = stack.pop().unwrap_or(Reg::R0); // a (dividend)
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        index_to_reg(next_temp)
                    };
                    if dst != Reg::R0 {
                        next_temp = (next_temp + 1) % 13;
                    }

                    // Trap check: if divisor == 0, trigger UDF (UsageFault -> Trap_Handler)
                    // CMP divisor, #0
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmp {
                            rn: divisor,
                            op2: Operand2::Imm(0),
                        },
                        source_line: Some(idx),
                    });
                    // BNE.N +0 (skip UDF if divisor != 0)
                    // offset=0 means skip to PC+4, which skips the 2-byte UDF
                    instructions.push(ArmInstruction {
                        op: ArmOp::BCondOffset {
                            cond: Condition::NE,
                            offset: 0,
                        },
                        source_line: Some(idx),
                    });
                    // UDF #0 (triggers trap on divide by zero)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Udf { imm: 0 },
                        source_line: Some(idx),
                    });
                    // UDIV dst, dividend, divisor
                    instructions.push(ArmInstruction {
                        op: ArmOp::Udiv {
                            rd: dst,
                            rn: dividend,
                            rm: divisor,
                        },
                        source_line: Some(idx),
                    });
                    stack.push(dst);
                }

                I32DivS => {
                    let divisor = stack.pop().unwrap_or(Reg::R1);
                    let dividend = stack.pop().unwrap_or(Reg::R0);
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        index_to_reg(next_temp)
                    };
                    if dst != Reg::R0 {
                        next_temp = (next_temp + 1) % 13;
                    }

                    // Trap check 1: divide by zero
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmp {
                            rn: divisor,
                            op2: Operand2::Imm(0),
                        },
                        source_line: Some(idx),
                    });
                    instructions.push(ArmInstruction {
                        op: ArmOp::BCondOffset {
                            cond: Condition::NE,
                            offset: 0,
                        },
                        source_line: Some(idx),
                    });
                    instructions.push(ArmInstruction {
                        op: ArmOp::Udf { imm: 0 },
                        source_line: Some(idx),
                    });

                    // Trap check 2: signed overflow (INT_MIN / -1)
                    // We need a temp register for INT_MIN (0x80000000)
                    let tmp = index_to_reg(next_temp);
                    next_temp = (next_temp + 1) % 13;

                    // Load INT_MIN into tmp: MOVW tmp, #0; MOVT tmp, #0x8000
                    instructions.push(ArmInstruction {
                        op: ArmOp::Movw { rd: tmp, imm16: 0 },
                        source_line: Some(idx),
                    });
                    instructions.push(ArmInstruction {
                        op: ArmOp::Movt {
                            rd: tmp,
                            imm16: 0x8000,
                        },
                        source_line: Some(idx),
                    });
                    // CMP dividend, tmp (check if dividend == INT_MIN)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmp {
                            rn: dividend,
                            op2: Operand2::Reg(tmp),
                        },
                        source_line: Some(idx),
                    });
                    // BNE.N +3 (skip overflow check if dividend != INT_MIN)
                    // Skip 8 bytes: CMN.W(4) + BNE(2) + UDF(2)
                    // Branch target = PC + (imm8 << 1) = B+4 + 6 = B+10 (SDIV)
                    instructions.push(ArmInstruction {
                        op: ArmOp::BCondOffset {
                            cond: Condition::NE,
                            offset: 3,
                        },
                        source_line: Some(idx),
                    });
                    // CMN divisor, #1 (check if divisor == -1: -1 + 1 = 0 sets Z flag)
                    // CMN.W is 4 bytes
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmn {
                            rn: divisor,
                            op2: Operand2::Imm(1),
                        },
                        source_line: Some(idx),
                    });
                    // BNE.N +0 (skip UDF if divisor != -1)
                    instructions.push(ArmInstruction {
                        op: ArmOp::BCondOffset {
                            cond: Condition::NE,
                            offset: 0,
                        },
                        source_line: Some(idx),
                    });
                    // UDF #1 (triggers trap on overflow)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Udf { imm: 1 },
                        source_line: Some(idx),
                    });

                    // SDIV dst, dividend, divisor (safe to divide now)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Sdiv {
                            rd: dst,
                            rn: dividend,
                            rm: divisor,
                        },
                        source_line: Some(idx),
                    });
                    stack.push(dst);
                }

                I32RemU => {
                    let divisor = stack.pop().unwrap_or(Reg::R1);
                    let dividend = stack.pop().unwrap_or(Reg::R0);
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        index_to_reg(next_temp)
                    };
                    if dst != Reg::R0 {
                        next_temp = (next_temp + 1) % 13;
                    }

                    // Trap check: divide by zero
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmp {
                            rn: divisor,
                            op2: Operand2::Imm(0),
                        },
                        source_line: Some(idx),
                    });
                    instructions.push(ArmInstruction {
                        op: ArmOp::BCondOffset {
                            cond: Condition::NE,
                            offset: 0,
                        },
                        source_line: Some(idx),
                    });
                    instructions.push(ArmInstruction {
                        op: ArmOp::Udf { imm: 0 },
                        source_line: Some(idx),
                    });

                    // Remainder: dst = dividend - (dividend / divisor) * divisor
                    // quotient = UDIV tmp, dividend, divisor
                    let tmp = index_to_reg(next_temp);
                    next_temp = (next_temp + 1) % 13;
                    instructions.push(ArmInstruction {
                        op: ArmOp::Udiv {
                            rd: tmp,
                            rn: dividend,
                            rm: divisor,
                        },
                        source_line: Some(idx),
                    });
                    // MLS dst, tmp, divisor, dividend  (dst = dividend - tmp * divisor)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Mls {
                            rd: dst,
                            rn: tmp,
                            rm: divisor,
                            ra: dividend,
                        },
                        source_line: Some(idx),
                    });
                    stack.push(dst);
                }

                I32RemS => {
                    let divisor = stack.pop().unwrap_or(Reg::R1);
                    let dividend = stack.pop().unwrap_or(Reg::R0);
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        index_to_reg(next_temp)
                    };
                    if dst != Reg::R0 {
                        next_temp = (next_temp + 1) % 13;
                    }

                    // Trap check: divide by zero (rem_s doesn't trap on INT_MIN % -1)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmp {
                            rn: divisor,
                            op2: Operand2::Imm(0),
                        },
                        source_line: Some(idx),
                    });
                    instructions.push(ArmInstruction {
                        op: ArmOp::BCondOffset {
                            cond: Condition::NE,
                            offset: 0,
                        },
                        source_line: Some(idx),
                    });
                    instructions.push(ArmInstruction {
                        op: ArmOp::Udf { imm: 0 },
                        source_line: Some(idx),
                    });

                    // Signed remainder: dst = dividend - (dividend / divisor) * divisor
                    let tmp = index_to_reg(next_temp);
                    next_temp = (next_temp + 1) % 13;
                    instructions.push(ArmInstruction {
                        op: ArmOp::Sdiv {
                            rd: tmp,
                            rn: dividend,
                            rm: divisor,
                        },
                        source_line: Some(idx),
                    });
                    instructions.push(ArmInstruction {
                        op: ArmOp::Mls {
                            rd: dst,
                            rn: tmp,
                            rm: divisor,
                            ra: dividend,
                        },
                        source_line: Some(idx),
                    });
                    stack.push(dst);
                }

                // Memory operations need stack-aware handling
                I32Load { offset, .. } => {
                    // Pop address from stack
                    let addr = stack.pop().unwrap_or(Reg::R0);
                    // Result goes in R0 if this is the last value-producing op (before End)
                    // Check if next op is End or if we're at the last position
                    let is_return_value = idx == wasm_ops.len() - 1
                        || (idx + 1 < wasm_ops.len() && matches!(wasm_ops[idx + 1], End));
                    let dst = if is_return_value {
                        Reg::R0
                    } else {
                        let t = index_to_reg(next_temp);
                        next_temp = (next_temp + 1) % 13;
                        t
                    };

                    // Generate load with optional bounds checking
                    let load_ops =
                        self.generate_load_with_bounds_check(dst, addr, *offset as i32, 4);
                    for op in load_ops {
                        instructions.push(ArmInstruction {
                            op,
                            source_line: Some(idx),
                        });
                    }
                    stack.push(dst);
                }

                I32Store { offset, .. } => {
                    // WASM i32.store pops: value first, then address
                    let value = stack.pop().unwrap_or(Reg::R1);
                    let addr = stack.pop().unwrap_or(Reg::R0);

                    // Generate store with optional bounds checking
                    let store_ops =
                        self.generate_store_with_bounds_check(value, addr, *offset as i32, 4);
                    for op in store_ops {
                        instructions.push(ArmInstruction {
                            op,
                            source_line: Some(idx),
                        });
                    }
                    // Store doesn't push anything to stack
                }

                // For other operations, fall back to default behavior
                _ => {
                    let arm_ops = self.select_default(op)?;
                    for arm_op in arm_ops {
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                    }
                }
            }
        }

        // Add BX LR at the end to return
        instructions.push(ArmInstruction {
            op: ArmOp::Bx { rm: Reg::LR },
            source_line: None,
        });

        Ok(instructions)
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
        let r3 = regs.get_or_alloc("x"); // Should reuse same register

        assert_eq!(r1, r3); // Same variable gets same register
        assert_ne!(r1, r2); // Different variables get different registers
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
        assert_eq!(index_to_reg(13), Reg::R0); // Wraps around
    }

    #[test]
    fn test_bounds_check_none() {
        // With BoundsCheckConfig::None, loads/stores should generate single instruction
        let db = RuleDatabase::new();
        let mut selector =
            InstructionSelector::with_bounds_check(db.rules().to_vec(), BoundsCheckConfig::None);

        let wasm_ops = vec![WasmOp::I32Load {
            offset: 0,
            align: 4,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        // Should be just the LDR instruction (1 instruction)
        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Ldr { .. } => {}
            _ => panic!("Expected Ldr instruction"),
        }
    }

    #[test]
    fn test_bounds_check_software() {
        // With BoundsCheckConfig::Software, loads should generate bounds check sequence
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::with_bounds_check(
            db.rules().to_vec(),
            BoundsCheckConfig::Software,
        );

        let wasm_ops = vec![WasmOp::I32Load {
            offset: 4,
            align: 4,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        // Should be: ADD temp, addr, #offset; CMP temp, R10; BHS trap; LDR
        assert_eq!(arm_instrs.len(), 4);

        // First: ADD to calculate effective address
        match &arm_instrs[0].op {
            ArmOp::Add {
                rd,
                rn: _,
                op2: Operand2::Imm(4),
            } => {
                assert_eq!(*rd, Reg::R12); // Uses R12 as temp
            }
            other => panic!("Expected Add with immediate 4, got {:?}", other),
        }

        // Second: CMP against R10 (memory size)
        match &arm_instrs[1].op {
            ArmOp::Cmp {
                rn,
                op2: Operand2::Reg(Reg::R10),
            } => {
                assert_eq!(*rn, Reg::R12); // Compare temp
            }
            other => panic!("Expected Cmp against R10, got {:?}", other),
        }

        // Third: BHS to trap handler
        match &arm_instrs[2].op {
            ArmOp::Bhs { label } => {
                assert_eq!(label, "Trap_Handler");
            }
            other => panic!("Expected Bhs to Trap_Handler, got {:?}", other),
        }

        // Fourth: The actual LDR
        match &arm_instrs[3].op {
            ArmOp::Ldr { .. } => {}
            other => panic!("Expected Ldr instruction, got {:?}", other),
        }
    }

    #[test]
    fn test_bounds_check_masking() {
        // With BoundsCheckConfig::Masking, loads should generate AND + LDR
        let db = RuleDatabase::new();
        let mut selector =
            InstructionSelector::with_bounds_check(db.rules().to_vec(), BoundsCheckConfig::Masking);

        let wasm_ops = vec![WasmOp::I32Store {
            offset: 0,
            align: 4,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        // Should be: AND addr, addr, R10; STR
        assert_eq!(arm_instrs.len(), 2);

        // First: AND to mask address
        match &arm_instrs[0].op {
            ArmOp::And {
                rn: _,
                op2: Operand2::Reg(Reg::R10),
                ..
            } => {}
            other => panic!("Expected And with R10, got {:?}", other),
        }

        // Second: The actual STR
        match &arm_instrs[1].op {
            ArmOp::Str { .. } => {}
            other => panic!("Expected Str instruction, got {:?}", other),
        }
    }
}
