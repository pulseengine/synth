//! Instruction Selection - Converts WebAssembly IR to ARM instructions
//!
//! Uses pattern matching to select optimal ARM instruction sequences

use crate::control_flow::{BlockType, BranchableInstruction, ControlFlowManager};
use crate::rules::{ArmOp, Condition, MemAddr, Operand2, Reg, Replacement, SynthesisRule, VfpReg};
use crate::{Bindings, PatternMatcher};
use std::collections::HashMap;
use synth_core::Result;
use synth_core::WasmOp;
use synth_core::target::FPUPrecision;

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

impl BranchableInstruction for ArmInstruction {
    fn set_branch_offset(&mut self, offset: i32) {
        match &self.op {
            ArmOp::B { .. } => {
                self.op = ArmOp::BOffset { offset };
            }
            ArmOp::Bcc { cond, .. } => {
                self.op = ArmOp::BCondOffset {
                    cond: *cond,
                    offset,
                };
            }
            ArmOp::Bhs { .. } => {
                self.op = ArmOp::BCondOffset {
                    cond: Condition::HS,
                    offset,
                };
            }
            ArmOp::Blo { .. } => {
                self.op = ArmOp::BCondOffset {
                    cond: Condition::LO,
                    offset,
                };
            }
            _ => {} // Not a branch instruction
        }
    }

    fn is_branch(&self) -> bool {
        matches!(
            self.op,
            ArmOp::B { .. }
                | ArmOp::Bcc { .. }
                | ArmOp::Bhs { .. }
                | ArmOp::Blo { .. }
                | ArmOp::Bl { .. }
                | ArmOp::BOffset { .. }
                | ArmOp::BCondOffset { .. }
        )
    }
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

/// Convert VFP register index to VfpReg enum (S0-S15 for linear allocation)
fn index_to_vfp_reg(index: u8) -> VfpReg {
    match index % 16 {
        0 => VfpReg::S0,
        1 => VfpReg::S1,
        2 => VfpReg::S2,
        3 => VfpReg::S3,
        4 => VfpReg::S4,
        5 => VfpReg::S5,
        6 => VfpReg::S6,
        7 => VfpReg::S7,
        8 => VfpReg::S8,
        9 => VfpReg::S9,
        10 => VfpReg::S10,
        11 => VfpReg::S11,
        12 => VfpReg::S12,
        13 => VfpReg::S13,
        14 => VfpReg::S14,
        _ => VfpReg::S15,
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
    /// Number of imported functions (calls to func_idx < this go through Meld dispatch)
    num_imports: u32,
    /// FPU capability of the target (None = soft-float only)
    fpu: Option<FPUPrecision>,
    /// Target name for error messages
    target_name: String,
    /// Next available VFP S-register (S0-S15, wrapping)
    next_vfp_reg: u8,
    /// Label counter for generating unique label names
    label_counter: u32,
}

impl InstructionSelector {
    /// Create a new instruction selector
    pub fn new(rules: Vec<SynthesisRule>) -> Self {
        Self {
            matcher: PatternMatcher::new(rules),
            regs: RegisterState::new(),
            bounds_check: BoundsCheckConfig::None,
            num_imports: 0,
            fpu: None,
            target_name: "cortex-m3".to_string(),
            next_vfp_reg: 0,
            label_counter: 0,
        }
    }

    /// Create a new instruction selector with bounds checking
    pub fn with_bounds_check(rules: Vec<SynthesisRule>, bounds_check: BoundsCheckConfig) -> Self {
        Self {
            matcher: PatternMatcher::new(rules),
            regs: RegisterState::new(),
            bounds_check,
            num_imports: 0,
            fpu: None,
            target_name: "cortex-m3".to_string(),
            next_vfp_reg: 0,
            label_counter: 0,
        }
    }

    /// Set the number of imported functions for Meld dispatch
    pub fn set_num_imports(&mut self, num_imports: u32) {
        self.num_imports = num_imports;
    }

    /// Set bounds checking configuration
    pub fn set_bounds_check(&mut self, config: BoundsCheckConfig) {
        self.bounds_check = config;
    }

    /// Set target FPU capability and name (for target-aware error messages)
    pub fn set_target(&mut self, fpu: Option<FPUPrecision>, target_name: &str) {
        self.fpu = fpu;
        self.target_name = target_name.to_string();
    }

    /// Generate a unique label name with the given prefix
    fn alloc_label(&mut self, prefix: &str) -> String {
        let id = self.label_counter;
        self.label_counter += 1;
        format!(".L{}_{}", prefix, id)
    }

    /// Allocate a VFP S-register (S0-S15, wrapping)
    fn alloc_vfp_reg(&mut self) -> VfpReg {
        let reg = index_to_vfp_reg(self.next_vfp_reg);
        self.next_vfp_reg = (self.next_vfp_reg + 1) % 16;
        reg
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

        let instrs = match wasm_op {
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

            // Shifts: WASM pops both value (rn) and shift amount (rm) from stack
            I32Shl => vec![ArmOp::LslReg { rd, rn, rm }],
            I32ShrS => vec![ArmOp::AsrReg { rd, rn, rm }],
            I32ShrU => vec![ArmOp::LsrReg { rd, rn, rm }],

            // Rotate operations: shift amount from stack register
            I32Rotl => {
                // Rotate left by N = Rotate right by (32 - N)
                // RSB rtmp, rm, #32; ROR rd, rn, rtmp
                let rtmp = self.regs.alloc_reg();
                vec![
                    ArmOp::Rsb {
                        rd: rtmp,
                        rn: rm,
                        imm: 32,
                    },
                    ArmOp::RorReg { rd, rn, rm: rtmp },
                ]
            }

            I32Rotr => vec![ArmOp::RorReg { rd, rn, rm }],

            // Bit count operations
            I32Clz => vec![ArmOp::Clz { rd, rm }],

            I32Ctz => {
                // Count trailing zeros: RBIT + CLZ
                vec![ArmOp::Rbit { rd, rm }, ArmOp::Clz { rd, rm: rd }]
            }

            I32Popcnt => {
                // Population count - no native ARM instruction
                // Use Popcnt pseudo-op which the encoder expands to a parallel
                // bit-count algorithm (shift-and-add with masks)
                vec![ArmOp::Popcnt { rd, rm }]
            }

            I32Const(val) => {
                vec![ArmOp::Mov {
                    rd,
                    op2: Operand2::Imm(*val),
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

            Call(func_idx) => {
                if *func_idx < self.num_imports {
                    // Import call — dispatch through Meld runtime
                    // R0 = import index, then BL __meld_dispatch_import
                    vec![
                        ArmOp::Mov {
                            rd: Reg::R0,
                            op2: Operand2::Imm(*func_idx as i32),
                        },
                        ArmOp::Bl {
                            label: "__meld_dispatch_import".to_string(),
                        },
                    ]
                } else {
                    // Local function call
                    vec![ArmOp::Bl {
                        label: format!("func_{}", func_idx),
                    }]
                }
            }

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

            // Control flow — labels and branches are emitted here.
            // Full structured control flow is handled in select_with_stack;
            // select_default emits a reasonable per-instruction lowering.
            Block => {
                let label = self.alloc_label("block_end");
                vec![ArmOp::Label { name: label }]
            }
            Loop => {
                let label = self.alloc_label("loop_start");
                vec![ArmOp::Label { name: label }]
            }
            Br(depth) => vec![ArmOp::B {
                label: format!("br_target_{}", depth),
            }],
            BrIf(depth) => {
                // Pop condition from stack (in rn), branch if non-zero
                vec![
                    ArmOp::Cmp {
                        rn,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::Bcc {
                        cond: Condition::NE,
                        label: format!("br_if_target_{}", depth),
                    },
                ]
            }
            Return => vec![ArmOp::Bx { rm: Reg::LR }],

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
                // Signed remainder: quotient = SDIV tmp, rn, rm
                // remainder = MLS rd, tmp, rm, rn  (rd = rn - tmp * rm)
                let rtmp = self.regs.alloc_reg();
                vec![
                    ArmOp::Sdiv { rd: rtmp, rn, rm },
                    ArmOp::Mls {
                        rd,
                        rn: rtmp,
                        rm,
                        ra: rn,
                    },
                ]
            }
            I32RemU => {
                // Unsigned remainder: quotient = UDIV tmp, rn, rm
                // remainder = MLS rd, tmp, rm, rn  (rd = rn - tmp * rm)
                let rtmp = self.regs.alloc_reg();
                vec![
                    ArmOp::Udiv { rd: rtmp, rn, rm },
                    ArmOp::Mls {
                        rd,
                        rn: rtmp,
                        rm,
                        ra: rn,
                    },
                ]
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

            // Comparison: equal to zero (unary)
            I32Eqz => vec![ArmOp::Cmp {
                rn,
                op2: Operand2::Imm(0),
            }],

            // Structural control flow delimiters — handled structurally in select_with_stack
            Nop => vec![ArmOp::Nop],
            End => vec![ArmOp::Nop],
            Drop => vec![ArmOp::Nop],
            If => {
                // In select_default (non-stack mode), emit a placeholder CMP + BEQ
                let else_label = self.alloc_label("else");
                vec![
                    ArmOp::Cmp {
                        rn,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::Bcc {
                        cond: Condition::EQ,
                        label: else_label,
                    },
                ]
            }
            Else => {
                // Jump over else block (end of then block)
                let end_label = self.alloc_label("if_end");
                vec![
                    ArmOp::B {
                        label: end_label.clone(),
                    },
                    ArmOp::Label { name: end_label },
                ]
            }

            // Trap: unreachable should generate an undefined instruction
            Unreachable => vec![ArmOp::Udf { imm: 0 }],

            // br_table: emit a jump table via TBB/TBH or cascading branches
            BrTable { targets, default } => {
                // Emit a cascading compare-and-branch sequence
                // index is in rn (from stack)
                let mut instrs = Vec::new();
                for (i, target) in targets.iter().enumerate() {
                    // CMP rn, #i
                    instrs.push(ArmOp::Cmp {
                        rn,
                        op2: Operand2::Imm(i as i32),
                    });
                    // BEQ to target label
                    instrs.push(ArmOp::Bcc {
                        cond: Condition::EQ,
                        label: format!("br_table_target_{}", target),
                    });
                }
                // Default: unconditional branch
                instrs.push(ArmOp::B {
                    label: format!("br_table_target_{}", default),
                });
                instrs
            }
            GlobalGet(index) => {
                // WASM globals are stored in a globals table in memory.
                // R9 is the dedicated globals base register (set up by runtime startup).
                // Each i32 global occupies 4 bytes: globals_base + index * 4.
                vec![ArmOp::Ldr {
                    rd,
                    addr: MemAddr::imm(Reg::R9, (*index as i32) * 4),
                }]
            }
            GlobalSet(index) => {
                // Store value from source register to globals_base + index * 4.
                // R9 is the dedicated globals base register.
                vec![ArmOp::Str {
                    rd,
                    addr: MemAddr::imm(Reg::R9, (*index as i32) * 4),
                }]
            }
            Select => {
                // WASM select: pops condition, val2, val1 from stack;
                // pushes val1 if condition != 0, else val2.
                // In select_default (non-stack mode), we emit:
                //   CMP rcond, #0
                //   MOV rd, rval1     (default: pick val1)
                //   IT EQ; MOVEQ rd, rval2  (override if cond == 0)
                let rcond = self.regs.alloc_reg();
                vec![
                    ArmOp::Cmp {
                        rn: rcond,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::Mov {
                        rd,
                        op2: Operand2::Reg(rn),
                    },
                    ArmOp::SelectMove {
                        rd,
                        rm,
                        cond: Condition::EQ,
                    },
                ]
            }

            // ===== i64 operations using register pairs on 32-bit ARM =====
            // Convention: i64 operand 1 in (R0,R1), operand 2 in (R2,R3), result in (R0,R1)
            I64Const(val) => {
                vec![ArmOp::I64Const {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    value: *val,
                }]
            }

            I64ExtendI32S => {
                vec![ArmOp::I64ExtendI32S {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rn: Reg::R0,
                }]
            }

            I64ExtendI32U => {
                vec![ArmOp::I64ExtendI32U {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rn: Reg::R0,
                }]
            }

            I32WrapI64 => {
                // Just take the low 32 bits (R0) — effectively a no-op if result is in R0
                vec![ArmOp::I32WrapI64 {
                    rd: Reg::R0,
                    rnlo: Reg::R0,
                }]
            }

            I64Extend8S => {
                vec![ArmOp::I64Extend8S {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                }]
            }

            I64Extend16S => {
                vec![ArmOp::I64Extend16S {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                }]
            }

            I64Extend32S => {
                vec![ArmOp::I64Extend32S {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                }]
            }

            // i64 arithmetic: ADDS/ADC for add, SUBS/SBC for sub
            I64Add => {
                vec![
                    ArmOp::Adds {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R2),
                    },
                    ArmOp::Adc {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Reg(Reg::R3),
                    },
                ]
            }

            I64Sub => {
                vec![
                    ArmOp::Subs {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R2),
                    },
                    ArmOp::Sbc {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Reg(Reg::R3),
                    },
                ]
            }

            // i64 bitwise: operate on each half independently
            I64And => {
                vec![
                    ArmOp::And {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R2),
                    },
                    ArmOp::And {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Reg(Reg::R3),
                    },
                ]
            }

            I64Or => {
                vec![
                    ArmOp::Orr {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R2),
                    },
                    ArmOp::Orr {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Reg(Reg::R3),
                    },
                ]
            }

            I64Xor => {
                vec![
                    ArmOp::Eor {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R2),
                    },
                    ArmOp::Eor {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Reg(Reg::R3),
                    },
                ]
            }

            // i64 comparisons: compare register pairs, result 0/1 in R0
            I64Eqz => {
                vec![ArmOp::I64SetCondZ {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                }]
            }

            I64Eq => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::EQ,
                }]
            }

            I64Ne => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::NE,
                }]
            }

            I64LtS => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::LT,
                }]
            }

            I64LtU => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::LO,
                }]
            }

            I64LeS => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::LE,
                }]
            }

            I64LeU => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::LS,
                }]
            }

            I64GtS => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::GT,
                }]
            }

            I64GtU => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::HI,
                }]
            }

            I64GeS => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::GE,
                }]
            }

            I64GeU => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::HS,
                }]
            }

            // i64 multiply: UMULL + MLA cross products
            I64Mul => {
                vec![ArmOp::I64Mul {
                    rd_lo: Reg::R0,
                    rd_hi: Reg::R1,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                }]
            }

            // i64 shifts: multi-instruction funnel shifts
            I64Shl => {
                vec![ArmOp::I64Shl {
                    rd_lo: Reg::R0,
                    rd_hi: Reg::R1,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                }]
            }

            I64ShrU => {
                vec![ArmOp::I64ShrU {
                    rd_lo: Reg::R0,
                    rd_hi: Reg::R1,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                }]
            }

            I64ShrS => {
                vec![ArmOp::I64ShrS {
                    rd_lo: Reg::R0,
                    rd_hi: Reg::R1,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                }]
            }

            I64Rotl => {
                vec![ArmOp::I64Rotl {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    shift: Reg::R2,
                }]
            }

            I64Rotr => {
                vec![ArmOp::I64Rotr {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    shift: Reg::R2,
                }]
            }

            // i64 bit manipulation
            I64Clz => {
                vec![ArmOp::I64Clz {
                    rd: Reg::R0,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                }]
            }

            I64Ctz => {
                vec![ArmOp::I64Ctz {
                    rd: Reg::R0,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                }]
            }

            I64Popcnt => {
                vec![ArmOp::I64Popcnt {
                    rd: Reg::R0,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                }]
            }

            // i64 division/remainder
            I64DivS => {
                vec![ArmOp::I64DivS {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    rmlo: Reg::R2,
                    rmhi: Reg::R3,
                }]
            }

            I64DivU => {
                vec![ArmOp::I64DivU {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    rmlo: Reg::R2,
                    rmhi: Reg::R3,
                }]
            }

            I64RemS => {
                vec![ArmOp::I64RemS {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    rmlo: Reg::R2,
                    rmhi: Reg::R3,
                }]
            }

            I64RemU => {
                vec![ArmOp::I64RemU {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    rmlo: Reg::R2,
                    rmhi: Reg::R3,
                }]
            }

            // i64 memory operations
            I64Load { offset, .. } => {
                vec![ArmOp::I64Ldr {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    addr: MemAddr::reg_imm(Reg::R11, rn, *offset as i32),
                }]
            }

            I64Store { offset, .. } => {
                vec![ArmOp::I64Str {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    addr: MemAddr::reg_imm(Reg::R11, rn, *offset as i32),
                }]
            }

            // ===== F32 operations =====
            // Path A: no FPU → error
            // Path B: FPU present → generate VFP instructions
            // Path C: unsupported ops → specific error
            F32Add if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Add { sd, sn, sm }]
            }
            F32Sub if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Sub { sd, sn, sm }]
            }
            F32Mul if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Mul { sd, sn, sm }]
            }
            F32Div if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Div { sd, sn, sm }]
            }

            F32Abs if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Abs { sd, sm }]
            }
            F32Neg if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Neg { sd, sm }]
            }
            F32Sqrt if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Sqrt { sd, sm }]
            }

            F32Eq if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Eq { rd, sn, sm }]
            }
            F32Ne if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Ne { rd, sn, sm }]
            }
            F32Lt if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Lt { rd, sn, sm }]
            }
            F32Le if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Le { rd, sn, sm }]
            }
            F32Gt if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Gt { rd, sn, sm }]
            }
            F32Ge if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Ge { rd, sn, sm }]
            }

            F32Const(val) if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                vec![ArmOp::F32Const { sd, value: *val }]
            }

            F32Load { offset, .. } if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let addr_reg = self.regs.alloc_reg();
                vec![ArmOp::F32Load {
                    sd,
                    addr: MemAddr::reg_imm(Reg::R11, addr_reg, *offset as i32),
                }]
            }
            F32Store { offset, .. } if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let addr_reg = self.regs.alloc_reg();
                vec![ArmOp::F32Store {
                    sd,
                    addr: MemAddr::reg_imm(Reg::R11, addr_reg, *offset as i32),
                }]
            }

            F32ConvertI32S if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                vec![ArmOp::F32ConvertI32S { sd, rm }]
            }
            F32ConvertI32U if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                vec![ArmOp::F32ConvertI32U { sd, rm }]
            }

            F32ReinterpretI32 if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                vec![ArmOp::F32ReinterpretI32 { sd, rm }]
            }
            I32ReinterpretF32 if self.fpu.is_some() => {
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::I32ReinterpretF32 { rd, sm }]
            }

            I32TruncF32S if self.fpu.is_some() => {
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::I32TruncF32S { rd, sm }]
            }
            I32TruncF32U if self.fpu.is_some() => {
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::I32TruncF32U { rd, sm }]
            }

            // F32 rounding pseudo-ops — emit ArmOp variants, encoder expands to
            // multi-instruction sequences using FPSCR rounding-mode manipulation
            F32Ceil if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Ceil { sd, sm }]
            }
            F32Floor if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Floor { sd, sm }]
            }
            F32Trunc if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Trunc { sd, sm }]
            }
            F32Nearest if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Nearest { sd, sm }]
            }
            // F32 min/max — emit ArmOp variants, encoder expands to VCMP + conditional VMOV
            F32Min if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Min { sd, sn, sm }]
            }
            F32Max if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Max { sd, sn, sm }]
            }
            // F32 copysign — emit ArmOp variant, encoder expands to VABS + sign extraction
            F32Copysign if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Copysign { sd, sn, sm }]
            }

            op @ (F32ConvertI64S | F32ConvertI64U) if self.fpu.is_some() => {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?} not supported (requires i64 register pairs on 32-bit ARM)"
                )));
            }

            op @ F32DemoteF64 if self.fpu.is_some() => {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?} not supported on single-precision target {}",
                    self.target_name
                )));
            }

            // Path A: all F32 ops with no FPU → error
            op @ (F32Add
            | F32Sub
            | F32Mul
            | F32Div
            | F32Eq
            | F32Ne
            | F32Lt
            | F32Le
            | F32Gt
            | F32Ge
            | F32Abs
            | F32Neg
            | F32Ceil
            | F32Floor
            | F32Trunc
            | F32Nearest
            | F32Sqrt
            | F32Min
            | F32Max
            | F32Copysign
            | F32Const(_)
            | F32Load { .. }
            | F32Store { .. }
            | F32ConvertI32S
            | F32ConvertI32U
            | F32ConvertI64S
            | F32ConvertI64U
            | F32DemoteF64
            | F32ReinterpretI32
            | I32ReinterpretF32
            | I32TruncF32S
            | I32TruncF32U) => {
                return Err(synth_core::Error::synthesis(format!(
                    "target {} has no FPU; cannot compile {op:?}",
                    self.target_name
                )));
            }

            // F64 ops — always rejected (single-precision targets don't support F64,
            // and no-FPU targets don't support any float)
            op @ (F64Add
            | F64Sub
            | F64Mul
            | F64Div
            | F64Eq
            | F64Ne
            | F64Lt
            | F64Le
            | F64Gt
            | F64Ge
            | F64Abs
            | F64Neg
            | F64Ceil
            | F64Floor
            | F64Trunc
            | F64Nearest
            | F64Sqrt
            | F64Min
            | F64Max
            | F64Copysign
            | F64Const(_)
            | F64Load { .. }
            | F64Store { .. }
            | F64ConvertI32S
            | F64ConvertI32U
            | F64ConvertI64S
            | F64ConvertI64U
            | F64PromoteF32
            | F64ReinterpretI64
            | I64ReinterpretF64
            | I64TruncF64S
            | I64TruncF64U
            | I32TruncF64S
            | I32TruncF64U) => {
                let msg = if self.fpu.is_some() {
                    format!(
                        "F64 not supported on single-precision target {} for {op:?}",
                        self.target_name
                    )
                } else {
                    format!(
                        "target {} has no FPU; cannot compile {op:?}",
                        self.target_name
                    )
                };
                return Err(synth_core::Error::synthesis(msg));
            }
        };
        Ok(instrs)
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
        self.label_counter = 0;
    }

    /// Select ARM instructions using a stack-based approach with AAPCS calling convention
    ///
    /// This method properly tracks the WASM virtual stack and generates code that
    /// uses r0-r3 for the first 4 parameters per AAPCS. Handles WASM structured
    /// control flow (block, loop, if/else, br, br_if, br_table, return, call).
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

        // Control flow tracking
        let mut cf = ControlFlowManager::new();
        cf.enter_function();
        // Stack of (label, is_loop) for branch target resolution
        // For blocks: label is the end label; for loops: label is the start label
        let mut block_labels: Vec<(String, bool)> = Vec::new();
        // Stack of (else_label, end_label) for if/else blocks
        let mut if_labels: Vec<(String, String)> = Vec::new();

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
                            op2: Operand2::Imm(*val),
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

                // =========================================================
                // Control flow operations
                // =========================================================
                Block => {
                    let label = self.alloc_label("block_end");
                    // Push block info so br can find the end label
                    cf.enter_block(BlockType::Block);
                    block_labels.push((label.clone(), false)); // (end_label, is_loop)
                    // No ARM code emitted at block entry (label at end)
                }

                Loop => {
                    let label = self.alloc_label("loop_start");
                    cf.enter_block(BlockType::Loop);
                    block_labels.push((label.clone(), true)); // (start_label, is_loop)
                    // Emit loop start label
                    instructions.push(ArmInstruction {
                        op: ArmOp::Label { name: label },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                If => {
                    // Pop condition from stack
                    let cond_reg = stack.pop().unwrap_or(Reg::R0);
                    let else_label = self.alloc_label("else");
                    let end_label = self.alloc_label("if_end");

                    cf.enter_block(BlockType::If);
                    // Store both labels: else_label for the if-branch, end_label for the end
                    if_labels.push((else_label.clone(), end_label.clone()));
                    block_labels.push((end_label, false));

                    // CMP cond_reg, #0
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmp {
                            rn: cond_reg,
                            op2: Operand2::Imm(0),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    // BEQ else_label (skip then-block if condition is zero)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Bcc {
                            cond: Condition::EQ,
                            label: else_label,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                Else => {
                    // End of then-block: jump to end of if
                    if let Some((_, end_label)) = if_labels.last() {
                        instructions.push(ArmInstruction {
                            op: ArmOp::B {
                                label: end_label.clone(),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    // Emit else label
                    if let Some((else_label, _)) = if_labels.last() {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Label {
                                name: else_label.clone(),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                }

                End => {
                    cf.exit_block();
                    // If this closes an if-block, emit the end label
                    // and possibly the else label (if no else was present)
                    if let Some((else_label, end_label)) = if_labels.last().cloned() {
                        // Check if the else label was already emitted
                        // by looking for it in the instructions
                        let else_emitted = instructions
                            .iter()
                            .any(|i| matches!(&i.op, ArmOp::Label { name } if *name == else_label));
                        if !else_emitted {
                            // No else clause: emit else label (same as end)
                            instructions.push(ArmInstruction {
                                op: ArmOp::Label { name: else_label },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        instructions.push(ArmInstruction {
                            op: ArmOp::Label { name: end_label },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        if_labels.pop();
                        block_labels.pop();
                    } else if let Some((label, is_loop)) = block_labels.pop()
                        && !is_loop
                    {
                        // Block end: emit end label
                        instructions.push(ArmInstruction {
                            op: ArmOp::Label { name: label },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        // Loop end: no label at end (label is at start)
                    }
                    // else: function-level end, nothing to emit
                }

                Br(depth) => {
                    // Branch to the Nth enclosing block/loop
                    // block_labels + if_labels are combined into the block_labels stack
                    let target_idx = block_labels.len().saturating_sub(1 + *depth as usize);
                    if target_idx < block_labels.len() {
                        let (label, is_loop) = &block_labels[target_idx];
                        if *is_loop {
                            // Loop: branch back to start
                            instructions.push(ArmInstruction {
                                op: ArmOp::B {
                                    label: label.clone(),
                                },
                                source_line: Some(idx),
                            });
                        } else {
                            // Block: branch forward to end
                            instructions.push(ArmInstruction {
                                op: ArmOp::B {
                                    label: label.clone(),
                                },
                                source_line: Some(idx),
                            });
                        }
                    } else {
                        // Depth exceeds stack — branch to function return
                        instructions.push(ArmInstruction {
                            op: ArmOp::Bx { rm: Reg::LR },
                            source_line: Some(idx),
                        });
                    }
                    cf.add_instruction();
                }

                BrIf(depth) => {
                    // Pop condition from stack
                    let cond_reg = stack.pop().unwrap_or(Reg::R0);

                    // CMP cond_reg, #0
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmp {
                            rn: cond_reg,
                            op2: Operand2::Imm(0),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    // BNE target_label (branch if non-zero)
                    let target_idx = block_labels.len().saturating_sub(1 + *depth as usize);
                    if target_idx < block_labels.len() {
                        let (label, _) = &block_labels[target_idx];
                        instructions.push(ArmInstruction {
                            op: ArmOp::Bcc {
                                cond: Condition::NE,
                                label: label.clone(),
                            },
                            source_line: Some(idx),
                        });
                    }
                    cf.add_instruction();
                }

                BrTable { targets, default } => {
                    // Pop index from stack
                    let index_reg = stack.pop().unwrap_or(Reg::R0);

                    // Emit cascading CMP + BEQ for each target
                    for (i, target) in targets.iter().enumerate() {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Cmp {
                                rn: index_reg,
                                op2: Operand2::Imm(i as i32),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();

                        let target_idx = block_labels.len().saturating_sub(1 + *target as usize);
                        if target_idx < block_labels.len() {
                            let (label, _) = &block_labels[target_idx];
                            instructions.push(ArmInstruction {
                                op: ArmOp::Bcc {
                                    cond: Condition::EQ,
                                    label: label.clone(),
                                },
                                source_line: Some(idx),
                            });
                        }
                        cf.add_instruction();
                    }

                    // Default branch
                    let default_idx = block_labels.len().saturating_sub(1 + *default as usize);
                    if default_idx < block_labels.len() {
                        let (label, _) = &block_labels[default_idx];
                        instructions.push(ArmInstruction {
                            op: ArmOp::B {
                                label: label.clone(),
                            },
                            source_line: Some(idx),
                        });
                    }
                    cf.add_instruction();
                }

                Return => {
                    // Move top-of-stack to R0 for return value (AAPCS)
                    if let Some(val) = stack.last()
                        && *val != Reg::R0
                    {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: Reg::R0,
                                op2: Operand2::Reg(*val),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    instructions.push(ArmInstruction {
                        op: ArmOp::Bx { rm: Reg::LR },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                Call(func_idx) => {
                    if *func_idx < self.num_imports {
                        // Import call — dispatch through Meld runtime
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: Reg::R0,
                                op2: Operand2::Imm(*func_idx as i32),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        instructions.push(ArmInstruction {
                            op: ArmOp::Bl {
                                label: "__meld_dispatch_import".to_string(),
                            },
                            source_line: Some(idx),
                        });
                    } else {
                        // Local function call
                        instructions.push(ArmInstruction {
                            op: ArmOp::Bl {
                                label: format!("func_{}", func_idx),
                            },
                            source_line: Some(idx),
                        });
                    }
                    cf.add_instruction();
                    // Push R0 as return value
                    stack.push(Reg::R0);
                }

                CallIndirect { type_index, .. } => {
                    let table_idx_reg = stack.pop().unwrap_or(Reg::R0);
                    instructions.push(ArmInstruction {
                        op: ArmOp::CallIndirect {
                            rd: Reg::R0,
                            type_idx: *type_index,
                            table_index_reg: table_idx_reg,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(Reg::R0);
                }

                Unreachable => {
                    instructions.push(ArmInstruction {
                        op: ArmOp::Udf { imm: 0 },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                Nop => {
                    instructions.push(ArmInstruction {
                        op: ArmOp::Nop,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                Drop => {
                    // Just pop a value from the stack and discard it
                    stack.pop();
                }

                Select => {
                    // Select: pop condition, val2, val1; push val1 if cond != 0, else val2
                    let cond_reg = stack.pop().unwrap_or(Reg::R2);
                    let val2 = stack.pop().unwrap_or(Reg::R1);
                    let val1 = stack.pop().unwrap_or(Reg::R0);
                    let dst = index_to_reg(next_temp);
                    next_temp = (next_temp + 1) % 13;

                    // CMP cond, #0
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmp {
                            rn: cond_reg,
                            op2: Operand2::Imm(0),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    // MOV dst, val1 (default: pick val1)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Mov {
                            rd: dst,
                            op2: Operand2::Reg(val1),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    // If cond == 0, overwrite with val2 using IT EQ + MOV
                    instructions.push(ArmInstruction {
                        op: ArmOp::SelectMove {
                            rd: dst,
                            rm: val2,
                            cond: Condition::EQ,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(dst);
                }

                LocalSet(local_idx) => {
                    let val = stack.pop().unwrap_or(Reg::R0);
                    if *local_idx < num_params.min(4) {
                        let target = index_to_reg(*local_idx as u8);
                        if val != target {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Mov {
                                    rd: target,
                                    op2: Operand2::Reg(val),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        local_to_reg.insert(*local_idx, target);
                    } else {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, (*local_idx as i32 - 4) * 4),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                }

                LocalTee(local_idx) => {
                    // Like local.set but keeps value on stack
                    let val = stack.last().copied().unwrap_or(Reg::R0);
                    if *local_idx < num_params.min(4) {
                        let target = index_to_reg(*local_idx as u8);
                        if val != target {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Mov {
                                    rd: target,
                                    op2: Operand2::Reg(val),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        local_to_reg.insert(*local_idx, target);
                    } else {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, (*local_idx as i32 - 4) * 4),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                }

                GlobalGet(global_idx) => {
                    // Load global value from globals table (R9 = globals base).
                    // Each i32 global occupies 4 bytes at offset index * 4.
                    let dst = index_to_reg(next_temp);
                    next_temp = (next_temp + 1) % 13;
                    instructions.push(ArmInstruction {
                        op: ArmOp::Ldr {
                            rd: dst,
                            addr: MemAddr::imm(Reg::R9, (*global_idx as i32) * 4),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(dst);
                }

                GlobalSet(global_idx) => {
                    // Pop value from stack and store to globals table (R9 = globals base).
                    let val = stack.pop().unwrap_or(Reg::R0);
                    instructions.push(ArmInstruction {
                        op: ArmOp::Str {
                            rd: val,
                            addr: MemAddr::imm(Reg::R9, (*global_idx as i32) * 4),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                // For other operations, fall back to default behavior
                _ => {
                    let arm_ops = self.select_default(op)?;
                    for arm_op in arm_ops {
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
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

/// Validate that all ARM instructions in the sequence are supported by the target.
///
/// This is the ISA feature gate: it checks each generated ARM instruction against
/// the target's FPU capabilities and returns an error for the first unsupported
/// instruction encountered. This must be called AFTER instruction selection but
/// BEFORE encoding, to ensure the compiler never emits an instruction that the
/// target platform cannot execute.
pub fn validate_instructions(
    instructions: &[ArmInstruction],
    fpu: Option<FPUPrecision>,
    target_name: &str,
) -> Result<()> {
    for instr in instructions {
        // Check FPU requirement (single-precision or higher)
        if instr.op.requires_fpu() && fpu.is_none() {
            return Err(synth_core::Error::UnsupportedInstruction(format!(
                "instruction {} requires FPU, but target {} has no FPU",
                instr.op.instruction_name(),
                target_name,
            )));
        }

        // Check double-precision FPU requirement
        if instr.op.requires_double_precision_fpu() && !matches!(fpu, Some(FPUPrecision::Double)) {
            let reason = if fpu.is_some() {
                "only has single-precision FPU"
            } else {
                "has no FPU"
            };
            return Err(synth_core::Error::UnsupportedInstruction(format!(
                "instruction {} requires double-precision FPU, but target {} {}",
                instr.op.instruction_name(),
                target_name,
                reason,
            )));
        }
    }
    Ok(())
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

        // WASM shifts take the shift amount from the stack (dynamic),
        // so we emit register-based shift instructions.
        let wasm_ops = vec![WasmOp::I32Shl, WasmOp::I32ShrS, WasmOp::I32ShrU];

        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 3);

        match &arm_instrs[0].op {
            ArmOp::LslReg { .. } => {}
            _ => panic!("Expected LslReg, got {:?}", arm_instrs[0].op),
        }

        match &arm_instrs[1].op {
            ArmOp::AsrReg { .. } => {}
            _ => panic!("Expected AsrReg, got {:?}", arm_instrs[1].op),
        }

        match &arm_instrs[2].op {
            ArmOp::LsrReg { .. } => {}
            _ => panic!("Expected LsrReg, got {:?}", arm_instrs[2].op),
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
    fn test_validate_instructions_rejects_fpu_on_no_fpu_target() {
        // Simulate FPU instructions being generated, then validate against a no-FPU target
        let instrs = vec![ArmInstruction {
            op: ArmOp::F32Add {
                sd: VfpReg::S0,
                sn: VfpReg::S1,
                sm: VfpReg::S2,
            },
            source_line: Some(0),
        }];
        let result = super::validate_instructions(&instrs, None, "cortex-m3");
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(
            err.contains("requires FPU"),
            "Error should mention FPU requirement, got: {err}"
        );
        assert!(
            err.contains("cortex-m3"),
            "Error should mention target name, got: {err}"
        );
    }

    #[test]
    fn test_validate_instructions_allows_fpu_on_fpu_target() {
        let instrs = vec![ArmInstruction {
            op: ArmOp::F32Add {
                sd: VfpReg::S0,
                sn: VfpReg::S1,
                sm: VfpReg::S2,
            },
            source_line: Some(0),
        }];
        let result =
            super::validate_instructions(&instrs, Some(FPUPrecision::Single), "cortex-m4f");
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_instructions_rejects_f64_on_single_precision() {
        let instrs = vec![ArmInstruction {
            op: ArmOp::F64Add {
                dd: VfpReg::D0,
                dn: VfpReg::D1,
                dm: VfpReg::D2,
            },
            source_line: Some(0),
        }];
        let result =
            super::validate_instructions(&instrs, Some(FPUPrecision::Single), "cortex-m4f");
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(
            err.contains("double-precision"),
            "Error should mention double-precision, got: {err}"
        );
    }

    #[test]
    fn test_validate_instructions_allows_f64_on_double_precision() {
        let instrs = vec![ArmInstruction {
            op: ArmOp::F64Add {
                dd: VfpReg::D0,
                dn: VfpReg::D1,
                dm: VfpReg::D2,
            },
            source_line: Some(0),
        }];
        let result =
            super::validate_instructions(&instrs, Some(FPUPrecision::Double), "cortex-m7dp");
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_instructions_allows_integer_ops_on_all_targets() {
        let instrs = vec![
            ArmInstruction {
                op: ArmOp::Add {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    op2: Operand2::Reg(Reg::R2),
                },
                source_line: Some(0),
            },
            ArmInstruction {
                op: ArmOp::Mul {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    rm: Reg::R2,
                },
                source_line: Some(1),
            },
            ArmInstruction {
                op: ArmOp::Sdiv {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    rm: Reg::R2,
                },
                source_line: Some(2),
            },
            ArmInstruction {
                op: ArmOp::Clz {
                    rd: Reg::R0,
                    rm: Reg::R1,
                },
                source_line: Some(3),
            },
        ];

        // Should pass on M3 (no FPU)
        let result = super::validate_instructions(&instrs, None, "cortex-m3");
        assert!(result.is_ok(), "Integer ops should pass on cortex-m3");

        // Should pass on M4F (with FPU)
        let result =
            super::validate_instructions(&instrs, Some(FPUPrecision::Single), "cortex-m4f");
        assert!(result.is_ok(), "Integer ops should pass on cortex-m4f");

        // Should pass on M7DP (with double FPU)
        let result =
            super::validate_instructions(&instrs, Some(FPUPrecision::Double), "cortex-m7dp");
        assert!(result.is_ok(), "Integer ops should pass on cortex-m7dp");
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

    // =========================================================================
    // Control flow tests
    // =========================================================================

    #[test]
    fn test_control_flow_simple_block() {
        // block ... end — should emit a label at the end
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::Block, WasmOp::I32Const(42), WasmOp::End];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain a Label instruction for block end
        let has_label = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Label { .. }));
        assert!(has_label, "Block should emit an end label");

        // Should contain a MOV for the constant
        let has_mov = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Mov { .. }));
        assert!(has_mov, "Should emit MOV for i32.const");
    }

    #[test]
    fn test_control_flow_loop_with_br() {
        // loop ... br 0 ... end — should emit a label at loop start and branch back
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::Loop,
            WasmOp::I32Const(1),
            WasmOp::Br(0), // Branch back to loop start
            WasmOp::End,
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain a Label for loop start
        let label_instrs: Vec<_> = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Label { name } if name.contains("loop_start")))
            .collect();
        assert_eq!(
            label_instrs.len(),
            1,
            "Should have exactly one loop_start label"
        );

        // Should contain a B (branch) instruction targeting the loop label
        let has_branch = arm_instrs.iter().any(|i| matches!(&i.op, ArmOp::B { .. }));
        assert!(has_branch, "Loop with br should emit a B instruction");
    }

    #[test]
    fn test_control_flow_if_else() {
        // if ... else ... end — conditional execution
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Const(1),  // Push condition
            WasmOp::If,           // Start if block
            WasmOp::I32Const(10), // Then body
            WasmOp::Else,         // Else
            WasmOp::I32Const(20), // Else body
            WasmOp::End,          // End if
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain a CMP (condition test)
        let has_cmp = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Cmp {
                    op2: Operand2::Imm(0),
                    ..
                }
            )
        });
        assert!(has_cmp, "If should emit CMP for condition check");

        // Should contain a conditional branch (BEQ to else)
        let has_beq = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Bcc {
                    cond: Condition::EQ,
                    ..
                }
            )
        });
        assert!(has_beq, "If should emit BEQ to else label");

        // Should contain an unconditional branch (B to end, at end of then-block)
        let has_b = arm_instrs.iter().any(|i| matches!(&i.op, ArmOp::B { .. }));
        assert!(has_b, "Else should emit B to end label");

        // Should contain labels for else and end
        let labels: Vec<_> = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Label { .. }))
            .collect();
        assert!(
            labels.len() >= 2,
            "Should have at least else and end labels, got {}",
            labels.len()
        );
    }

    #[test]
    fn test_control_flow_if_without_else() {
        // if ... end — no else clause
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Const(1),  // Push condition
            WasmOp::If,           // Start if block
            WasmOp::I32Const(10), // Then body
            WasmOp::End,          // End if (no else)
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should still emit else label (same as end) and end label
        let labels: Vec<_> = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Label { .. }))
            .collect();
        assert!(
            labels.len() >= 2,
            "If without else should emit both else (=end) and end labels"
        );
    }

    #[test]
    fn test_control_flow_br_if() {
        // br_if — conditional branch
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::Block,
            WasmOp::I32Const(1),  // Push condition
            WasmOp::BrIf(0),      // Conditional branch to block end
            WasmOp::I32Const(42), // Code after br_if (only reached if condition was 0)
            WasmOp::End,
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain CMP and BNE
        let has_cmp = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Cmp {
                    op2: Operand2::Imm(0),
                    ..
                }
            )
        });
        assert!(has_cmp, "br_if should emit CMP");

        let has_bne = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Bcc {
                    cond: Condition::NE,
                    ..
                }
            )
        });
        assert!(has_bne, "br_if should emit BNE (branch if non-zero)");
    }

    #[test]
    fn test_control_flow_nested_blocks() {
        // Nested blocks with br to outer block
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::Block,        // Outer block (depth 1 from inner)
            WasmOp::Block,        // Inner block (depth 0)
            WasmOp::Br(1),        // Branch to outer block end
            WasmOp::End,          // End inner
            WasmOp::I32Const(99), // This is skipped by br 1
            WasmOp::End,          // End outer
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // The br(1) should target the outer block's end label
        let branch_instrs: Vec<_> = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::B { .. }))
            .collect();
        assert!(
            !branch_instrs.is_empty(),
            "br(1) should emit a B instruction targeting outer block"
        );
    }

    #[test]
    fn test_control_flow_call() {
        // Call a local function
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::Call(5)];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        let has_bl = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Bl { label } if label == "func_5"));
        assert!(has_bl, "Call(5) should emit BL func_5");
    }

    #[test]
    fn test_control_flow_call_import() {
        // Call an imported function via Meld dispatch
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        selector.set_num_imports(3);

        let wasm_ops = vec![WasmOp::Call(1)]; // Import index 1 (< 3)
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should emit MOV R0, #1 (import index) then BL __meld_dispatch_import
        let has_mov = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Mov {
                    rd: Reg::R0,
                    op2: Operand2::Imm(1)
                }
            )
        });
        assert!(has_mov, "Import call should set R0 to import index");

        let has_bl = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Bl { label } if label == "__meld_dispatch_import"));
        assert!(has_bl, "Import call should BL to __meld_dispatch_import");
    }

    #[test]
    fn test_control_flow_return() {
        // Return from function
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Const(42), WasmOp::Return];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain BX LR for the return
        let bx_count = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Bx { rm: Reg::LR }))
            .count();
        assert!(bx_count >= 1, "Return should emit BX LR");
    }

    #[test]
    fn test_control_flow_unreachable() {
        // Unreachable trap
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::Unreachable];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        let has_udf = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Udf { imm: 0 }));
        assert!(has_udf, "Unreachable should emit UDF");
    }

    #[test]
    fn test_control_flow_nop() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::Nop];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        let has_nop = arm_instrs.iter().any(|i| matches!(&i.op, ArmOp::Nop));
        assert!(has_nop, "Nop should emit NOP");
    }

    #[test]
    fn test_control_flow_drop() {
        // Drop should pop from virtual stack without emitting code
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Const(42), WasmOp::Drop, WasmOp::I32Const(10)];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should emit MOVs for the consts but no instruction for Drop
        let mov_count = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Mov { .. }))
            .count();
        assert_eq!(mov_count, 2, "Should have two MOVs for the two consts");
    }

    #[test]
    fn test_control_flow_select() {
        // Select: pick between two values based on condition
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Const(10), // val1
            WasmOp::I32Const(20), // val2
            WasmOp::I32Const(1),  // condition
            WasmOp::Select,
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain CMP for condition check
        let has_cmp = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Cmp {
                    op2: Operand2::Imm(0),
                    ..
                }
            )
        });
        assert!(has_cmp, "Select should emit CMP for condition");

        // Should contain SelectMove for conditional assignment
        let has_select_move = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::SelectMove {
                    cond: Condition::EQ,
                    ..
                }
            )
        });
        assert!(has_select_move, "Select should emit SelectMove");
    }

    #[test]
    fn test_control_flow_br_table() {
        // br_table — indexed branch
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::Block,       // Target for case 0 (depth 0)
            WasmOp::Block,       // Target for case 1 (depth 0)
            WasmOp::I32Const(0), // index
            WasmOp::BrTable {
                targets: vec![1, 0], // case 0 -> depth 1, case 1 -> depth 0
                default: 1,          // default -> depth 1
            },
            WasmOp::End,
            WasmOp::End,
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain multiple CMP instructions (one per target)
        let cmp_count = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Cmp { .. }))
            .count();
        assert!(
            cmp_count >= 2,
            "br_table should emit CMP for each target, got {}",
            cmp_count
        );

        // Should contain conditional branches (BEQ)
        let beq_count = arm_instrs
            .iter()
            .filter(|i| {
                matches!(
                    &i.op,
                    ArmOp::Bcc {
                        cond: Condition::EQ,
                        ..
                    }
                )
            })
            .count();
        assert!(
            beq_count >= 2,
            "br_table should emit BEQ for each target, got {}",
            beq_count
        );

        // Should contain a default unconditional branch (B)
        let has_default_b = arm_instrs.iter().any(|i| matches!(&i.op, ArmOp::B { .. }));
        assert!(has_default_b, "br_table should emit B for default target");
    }

    #[test]
    fn test_control_flow_local_set_get() {
        // local.set and local.get round-trip
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Const(42),
            WasmOp::LocalSet(0), // Set local 0 (param r0)
            WasmOp::LocalGet(0), // Get local 0
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should contain instructions (MOV for const, MOV for set, then get is register reuse)
        assert!(
            !arm_instrs.is_empty(),
            "local.set/get sequence should emit instructions"
        );
    }

    #[test]
    fn test_branchable_instruction_trait() {
        // Test the BranchableInstruction trait implementation
        let mut instr = ArmInstruction {
            op: ArmOp::B {
                label: "target".to_string(),
            },
            source_line: Some(0),
        };

        assert!(instr.is_branch());
        instr.set_branch_offset(10);
        assert_eq!(instr.op, ArmOp::BOffset { offset: 10 });

        // Test conditional branch
        let mut cond_instr = ArmInstruction {
            op: ArmOp::Bcc {
                cond: Condition::EQ,
                label: "target".to_string(),
            },
            source_line: Some(0),
        };

        assert!(cond_instr.is_branch());
        cond_instr.set_branch_offset(5);
        assert_eq!(
            cond_instr.op,
            ArmOp::BCondOffset {
                cond: Condition::EQ,
                offset: 5,
            }
        );
    }

    #[test]
    fn test_label_emits_no_code() {
        // Verify that Label pseudo-instruction doesn't produce any encoding
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::Block, WasmOp::End];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Labels should be present in instructions
        let label_count = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Label { .. }))
            .count();
        assert!(
            label_count >= 1,
            "Block/end should produce at least one label"
        );
    }

    #[test]
    fn test_loop_backward_branch_label() {
        // Verify loop emits label at start and br(0) branches back to it
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::Loop,
            WasmOp::Br(0), // Back to loop start
            WasmOp::End,
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Get the loop start label name
        let loop_label = arm_instrs.iter().find_map(|i| {
            if let ArmOp::Label { name } = &i.op
                && name.contains("loop_start")
            {
                return Some(name.clone());
            }
            None
        });
        assert!(loop_label.is_some(), "Loop should emit loop_start label");
        let loop_label = loop_label.unwrap();

        // The branch should target the same label
        let branch_target = arm_instrs.iter().find_map(|i| {
            if let ArmOp::B { label } = &i.op {
                return Some(label.clone());
            }
            None
        });
        assert_eq!(
            branch_target.as_deref(),
            Some(loop_label.as_str()),
            "br(0) in loop should branch back to loop_start label"
        );
    }

    // =========================================================================
    // Complex control flow tests (GitHub issue #36)
    //
    // These exercise the control flow compilation paths landed in PR #52:
    // nested blocks, loops with conditional exit, if/else with nested blocks,
    // br_table dispatch, and realistic multi-construct programs like
    // factorial and fibonacci.
    // =========================================================================

    /// Helper: create a fresh InstructionSelector with no optimization rules
    fn fresh_selector() -> InstructionSelector {
        InstructionSelector::new(vec![])
    }

    /// Helper: collect all Label names from an instruction sequence
    fn collect_labels(instrs: &[ArmInstruction]) -> Vec<String> {
        instrs
            .iter()
            .filter_map(|i| {
                if let ArmOp::Label { name } = &i.op {
                    Some(name.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Helper: collect all unconditional branch targets (B { label })
    fn collect_branch_targets(instrs: &[ArmInstruction]) -> Vec<String> {
        instrs
            .iter()
            .filter_map(|i| {
                if let ArmOp::B { label } = &i.op {
                    Some(label.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Helper: collect all conditional branch targets (Bcc { label, .. })
    fn collect_cond_branch_targets(instrs: &[ArmInstruction]) -> Vec<(Condition, String)> {
        instrs
            .iter()
            .filter_map(|i| {
                if let ArmOp::Bcc { cond, label } = &i.op {
                    Some((*cond, label.clone()))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Helper: count instructions of a given kind
    fn count_op<F: Fn(&ArmOp) -> bool>(instrs: &[ArmInstruction], pred: F) -> usize {
        instrs.iter().filter(|i| pred(&i.op)).count()
    }

    // ----- Test 1: Nested blocks with branch-out (br to outer block) -----

    #[test]
    fn test_complex_nested_blocks_br_to_outer() {
        // WASM equivalent:
        //   (block $outer            ;; depth 2 from innermost
        //     (block $middle         ;; depth 1 from innermost
        //       (block $inner        ;; depth 0
        //         i32.const 1
        //         br 2               ;; jump to $outer end
        //       )
        //       i32.const 2          ;; skipped by br 2
        //     )
        //     i32.const 3            ;; also skipped by br 2
        //   )
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block, // $outer
            WasmOp::Block, // $middle
            WasmOp::Block, // $inner
            WasmOp::I32Const(1),
            WasmOp::Br(2), // jump to $outer end
            WasmOp::End,   // end $inner
            WasmOp::I32Const(2),
            WasmOp::End, // end $middle
            WasmOp::I32Const(3),
            WasmOp::End, // end $outer
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have 3 block end labels (one per block)
        let labels = collect_labels(&instrs);
        assert!(
            labels.len() >= 3,
            "Three nested blocks should produce at least 3 end labels, got {}",
            labels.len()
        );

        // The br(2) should generate a B instruction
        let branches = collect_branch_targets(&instrs);
        assert!(
            !branches.is_empty(),
            "br(2) should generate an unconditional branch"
        );

        // The branch target should be the outer block's end label (the first
        // label pushed on block_labels, which is the outermost block end)
        let outer_end_label = &labels[labels.len() - 1]; // last label emitted is outermost end
        assert!(
            branches.contains(outer_end_label),
            "br(2) should target the outermost block end label '{}', targets: {:?}",
            outer_end_label,
            branches
        );
    }

    // ----- Test 2: Loop with conditional exit (br_if) -----

    #[test]
    fn test_complex_loop_with_conditional_exit() {
        // WASM equivalent (countdown loop):
        //   (block $exit
        //     (loop $loop
        //       local.get 0          ;; counter
        //       i32.eqz
        //       br_if 1              ;; if counter == 0, exit block
        //       local.get 0
        //       i32.const 1
        //       i32.sub
        //       local.set 0          ;; counter -= 1
        //       br 0                 ;; loop back
        //     )
        //   )
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block,       // $exit
            WasmOp::Loop,        // $loop
            WasmOp::LocalGet(0), // counter
            WasmOp::I32Eqz,      // counter == 0?
            WasmOp::BrIf(1),     // if zero, exit to $exit end
            WasmOp::LocalGet(0),
            WasmOp::I32Const(1),
            WasmOp::I32Sub,      // counter - 1
            WasmOp::LocalSet(0), // counter = counter - 1
            WasmOp::Br(0),       // loop back to $loop start
            WasmOp::End,         // end $loop
            WasmOp::End,         // end $exit
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should have a loop_start label
        let loop_labels: Vec<_> = collect_labels(&instrs)
            .into_iter()
            .filter(|l| l.contains("loop_start"))
            .collect();
        assert_eq!(
            loop_labels.len(),
            1,
            "Should have exactly one loop_start label"
        );

        // Should have an unconditional branch back to loop_start (br 0)
        let branches = collect_branch_targets(&instrs);
        assert!(
            branches.contains(&loop_labels[0]),
            "br(0) should branch back to loop_start label"
        );

        // Should have a conditional branch (br_if 1) targeting exit block end
        let cond_branches = collect_cond_branch_targets(&instrs);
        let ne_branches: Vec<_> = cond_branches
            .iter()
            .filter(|(c, _)| *c == Condition::NE)
            .collect();
        assert!(
            !ne_branches.is_empty(),
            "br_if should generate a BNE conditional branch"
        );

        // Should emit a SUB for counter decrement
        let has_sub = instrs.iter().any(|i| matches!(&i.op, ArmOp::Sub { .. }));
        assert!(has_sub, "Should emit SUB for i32.sub (counter -= 1)");
    }

    // ----- Test 3: If/else with computation in both arms -----

    #[test]
    fn test_complex_if_else_with_computation() {
        // WASM equivalent:
        //   local.get 0              ;; condition from param
        //   (if
        //     (then
        //       local.get 1
        //       i32.const 10
        //       i32.add
        //       local.set 1          ;; x += 10
        //       local.get 1
        //       i32.const 100
        //       i32.mul
        //       local.set 1          ;; x *= 100
        //     )
        //     (else
        //       local.get 1
        //       i32.const 20
        //       i32.sub
        //       local.set 1          ;; x -= 20
        //       local.get 1
        //       i32.const 2
        //       i32.mul
        //       local.set 1          ;; x *= 2
        //     )
        //   )
        //   local.get 1              ;; return x
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::LocalGet(0), // condition
            WasmOp::If,
            // then-arm: x += 10, x *= 100
            WasmOp::LocalGet(1),
            WasmOp::I32Const(10),
            WasmOp::I32Add,
            WasmOp::LocalSet(1),
            WasmOp::LocalGet(1),
            WasmOp::I32Const(100),
            WasmOp::I32Mul,
            WasmOp::LocalSet(1),
            WasmOp::Else,
            // else-arm: x -= 20, x *= 2
            WasmOp::LocalGet(1),
            WasmOp::I32Const(20),
            WasmOp::I32Sub,
            WasmOp::LocalSet(1),
            WasmOp::LocalGet(1),
            WasmOp::I32Const(2),
            WasmOp::I32Mul,
            WasmOp::LocalSet(1),
            WasmOp::End,         // end if
            WasmOp::LocalGet(1), // return x
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 2).unwrap();

        // Should have CMP for condition
        let cmp_count = count_op(&instrs, |op| matches!(op, ArmOp::Cmp { .. }));
        assert!(cmp_count >= 1, "If should emit CMP for condition");

        // Should have conditional branch to else (BEQ)
        let beq_count = count_op(&instrs, |op| {
            matches!(
                op,
                ArmOp::Bcc {
                    cond: Condition::EQ,
                    ..
                }
            )
        });
        assert!(beq_count >= 1, "If should emit BEQ to skip to else");

        // Should have unconditional branch to skip else at end of then
        let b_count = count_op(&instrs, |op| matches!(op, ArmOp::B { .. }));
        assert!(
            b_count >= 1,
            "End of then-arm should emit B to skip else, got {}",
            b_count
        );

        // Should have labels for else and if_end
        let labels = collect_labels(&instrs);
        let else_labels: Vec<_> = labels.iter().filter(|l| l.contains("else")).collect();
        let end_labels: Vec<_> = labels.iter().filter(|l| l.contains("if_end")).collect();
        assert!(!else_labels.is_empty(), "Should have an else label");
        assert!(!end_labels.is_empty(), "Should have an if_end label");

        // Should have ADD for then-arm and SUB for else-arm
        let add_count = count_op(&instrs, |op| matches!(op, ArmOp::Add { .. }));
        assert!(add_count >= 1, "Then-arm should have ADD");
        let sub_count = count_op(&instrs, |op| matches!(op, ArmOp::Sub { .. }));
        assert!(sub_count >= 1, "Else-arm should have SUB");

        // Should have MUL instructions for both arms
        let mul_count = count_op(&instrs, |op| matches!(op, ArmOp::Mul { .. }));
        assert_eq!(
            mul_count, 2,
            "Should have 2 MUL instructions (one per arm), got {}",
            mul_count
        );
    }

    // ----- Test 4: br_table (switch-like dispatch) -----

    #[test]
    fn test_complex_br_table_switch_dispatch() {
        // WASM equivalent (switch with 3 cases + default):
        //   (block $case2
        //     (block $case1
        //       (block $case0
        //         (block $default
        //           local.get 0          ;; switch index
        //           br_table 0 1 2 3     ;; targets=[0,1,2], default=3
        //         )
        //         ;; default body
        //         i32.const 99
        //         br 2
        //       )
        //       ;; case 0 body
        //       i32.const 0
        //       br 1
        //     )
        //     ;; case 1 body
        //     i32.const 1
        //     br 0
        //   )
        //   ;; case 2 falls through here
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block,       // $case2
            WasmOp::Block,       // $case1
            WasmOp::Block,       // $case0
            WasmOp::Block,       // $default
            WasmOp::LocalGet(0), // switch index
            WasmOp::BrTable {
                targets: vec![0, 1, 2], // case 0->$default, 1->$case0, 2->$case1
                default: 3,             // default->$case2
            },
            WasmOp::End,          // end $default
            WasmOp::I32Const(99), // default body
            WasmOp::Br(2),        // skip to $case2 end
            WasmOp::End,          // end $case0
            WasmOp::I32Const(0),  // case 0 body
            WasmOp::Br(1),        // skip to $case2 end
            WasmOp::End,          // end $case1
            WasmOp::I32Const(1),  // case 1 body
            WasmOp::Br(0),        // skip to $case2 end
            WasmOp::End,          // end $case2
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // br_table should emit CMP+BEQ for each target (3 targets)
        let cmp_count = count_op(&instrs, |op| matches!(op, ArmOp::Cmp { .. }));
        assert!(
            cmp_count >= 3,
            "br_table with 3 targets should emit at least 3 CMPs, got {}",
            cmp_count
        );

        let beq_count = count_op(&instrs, |op| {
            matches!(
                op,
                ArmOp::Bcc {
                    cond: Condition::EQ,
                    ..
                }
            )
        });
        assert!(
            beq_count >= 3,
            "br_table with 3 targets should emit at least 3 BEQs, got {}",
            beq_count
        );

        // Should emit a default unconditional branch
        let b_count = count_op(&instrs, |op| matches!(op, ArmOp::B { .. }));
        assert!(
            b_count >= 4,
            "Should have at least 4 B instructions (1 default + 3 case br), got {}",
            b_count
        );

        // Should have 4 block end labels
        let labels = collect_labels(&instrs);
        let block_end_labels: Vec<_> = labels.iter().filter(|l| l.contains("block_end")).collect();
        assert_eq!(
            block_end_labels.len(),
            4,
            "Should have 4 block_end labels for 4 blocks, got {}",
            block_end_labels.len()
        );
    }

    // ----- Test 5: Factorial (loop + if + arithmetic) -----

    #[test]
    fn test_complex_factorial() {
        // WASM equivalent of iterative factorial:
        //   (func $factorial (param $n i32) (result i32)
        //     (local $result i32)
        //     i32.const 1
        //     local.set 1             ;; result = 1
        //     (block $exit
        //       (loop $loop
        //         local.get 0         ;; n
        //         i32.const 1
        //         i32.le_s
        //         br_if 1             ;; if n <= 1, exit
        //         local.get 1         ;; result
        //         local.get 0         ;; n
        //         i32.mul
        //         local.set 1         ;; result *= n
        //         local.get 0
        //         i32.const 1
        //         i32.sub
        //         local.set 0         ;; n -= 1
        //         br 0                ;; loop
        //       )
        //     )
        //     local.get 1             ;; return result
        //   )
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::I32Const(1),
            WasmOp::LocalSet(1), // result = 1
            WasmOp::Block,       // $exit
            WasmOp::Loop,        // $loop
            WasmOp::LocalGet(0), // n
            WasmOp::I32Const(1),
            WasmOp::I32LeS,      // n <= 1?
            WasmOp::BrIf(1),     // exit if true
            WasmOp::LocalGet(1), // result
            WasmOp::LocalGet(0), // n
            WasmOp::I32Mul,      // result * n
            WasmOp::LocalSet(1), // result = result * n
            WasmOp::LocalGet(0), // n
            WasmOp::I32Const(1),
            WasmOp::I32Sub,      // n - 1
            WasmOp::LocalSet(0), // n = n - 1
            WasmOp::Br(0),       // loop back
            WasmOp::End,         // end $loop
            WasmOp::End,         // end $exit
            WasmOp::LocalGet(1), // return result
        ];

        // 2 params: $n in r0, $result in r1 (via local.set 1)
        let instrs = selector.select_with_stack(&wasm_ops, 2).unwrap();

        // Should have a loop_start label
        let labels = collect_labels(&instrs);
        let loop_starts: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(loop_starts.len(), 1, "Should have exactly one loop_start");

        // Should have backward branch (br 0) to loop
        let branches = collect_branch_targets(&instrs);
        assert!(
            branches.contains(loop_starts[0]),
            "br(0) should branch back to loop_start"
        );

        // Should have conditional exit (br_if 1)
        let cond_branches = collect_cond_branch_targets(&instrs);
        assert!(
            !cond_branches.is_empty(),
            "br_if(1) should emit conditional branch to exit"
        );

        // Should have MUL for result * n
        let mul_count = count_op(&instrs, |op| matches!(op, ArmOp::Mul { .. }));
        assert_eq!(mul_count, 1, "Should have exactly one MUL for result * n");

        // Should have SUB for n - 1
        let sub_count = count_op(&instrs, |op| matches!(op, ArmOp::Sub { .. }));
        assert_eq!(sub_count, 1, "Should have exactly one SUB for n - 1");

        // Should have BX LR at the end for function return
        let has_bx_lr = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Bx { rm: Reg::LR }));
        assert!(has_bx_lr, "Function should end with BX LR");
    }

    // ----- Test 6: Fibonacci (loop + if + arithmetic) -----

    #[test]
    fn test_complex_fibonacci() {
        // WASM equivalent of iterative fibonacci:
        //   (func $fib (param $n i32) (result i32)
        //     (local $a i32)   ;; local 1 = 0
        //     (local $b i32)   ;; local 2 = 1
        //     (local $tmp i32) ;; local 3
        //     i32.const 0
        //     local.set 1         ;; a = 0
        //     i32.const 1
        //     local.set 2         ;; b = 1
        //     (block $exit
        //       (loop $loop
        //         local.get 0     ;; n
        //         i32.eqz
        //         br_if 1         ;; if n == 0, exit
        //         local.get 1     ;; a
        //         local.get 2     ;; b
        //         i32.add
        //         local.set 3     ;; tmp = a + b
        //         local.get 2
        //         local.set 1     ;; a = b
        //         local.get 3
        //         local.set 2     ;; b = tmp
        //         local.get 0
        //         i32.const 1
        //         i32.sub
        //         local.set 0     ;; n -= 1
        //         br 0            ;; loop
        //       )
        //     )
        //     local.get 1         ;; return a
        //   )
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::I32Const(0),
            WasmOp::LocalSet(1), // a = 0
            WasmOp::I32Const(1),
            WasmOp::LocalSet(2), // b = 1
            WasmOp::Block,       // $exit
            WasmOp::Loop,        // $loop
            WasmOp::LocalGet(0), // n
            WasmOp::I32Eqz,      // n == 0?
            WasmOp::BrIf(1),     // exit if n == 0
            WasmOp::LocalGet(1), // a
            WasmOp::LocalGet(2), // b
            WasmOp::I32Add,      // a + b
            WasmOp::LocalSet(3), // tmp = a + b
            WasmOp::LocalGet(2), // b
            WasmOp::LocalSet(1), // a = b
            WasmOp::LocalGet(3), // tmp
            WasmOp::LocalSet(2), // b = tmp
            WasmOp::LocalGet(0), // n
            WasmOp::I32Const(1),
            WasmOp::I32Sub,      // n - 1
            WasmOp::LocalSet(0), // n = n - 1
            WasmOp::Br(0),       // loop
            WasmOp::End,         // end $loop
            WasmOp::End,         // end $exit
            WasmOp::LocalGet(1), // return a
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 4).unwrap();

        // Should have loop_start label
        let labels = collect_labels(&instrs);
        let loop_starts: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(loop_starts.len(), 1, "Should have one loop_start");

        // Should have backward branch
        let branches = collect_branch_targets(&instrs);
        assert!(
            branches.contains(loop_starts[0]),
            "Should branch back to loop_start"
        );

        // Should have ADD for a + b
        let add_count = count_op(&instrs, |op| matches!(op, ArmOp::Add { .. }));
        assert!(add_count >= 1, "Should have ADD for a + b");

        // Should have SUB for n - 1
        let sub_count = count_op(&instrs, |op| matches!(op, ArmOp::Sub { .. }));
        assert!(sub_count >= 1, "Should have SUB for n - 1");

        // Should have conditional branch for br_if
        let cond_branches = collect_cond_branch_targets(&instrs);
        let ne_branches: Vec<_> = cond_branches
            .iter()
            .filter(|(c, _)| *c == Condition::NE)
            .collect();
        assert!(
            !ne_branches.is_empty(),
            "br_if should generate BNE for conditional exit"
        );
    }

    // ----- Test 7: Empty blocks -----

    #[test]
    fn test_complex_empty_blocks() {
        // Empty blocks should compile without error and produce minimal code
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block,
            WasmOp::End,
            WasmOp::Block,
            WasmOp::Block,
            WasmOp::End,
            WasmOp::End,
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should succeed and produce labels
        let labels = collect_labels(&instrs);
        assert!(
            labels.len() >= 3,
            "Three empty blocks should produce at least 3 labels, got {}",
            labels.len()
        );

        // No branches should be emitted (no br instructions)
        let b_count = count_op(&instrs, |op| matches!(op, ArmOp::B { .. }));
        assert_eq!(
            b_count, 0,
            "Empty blocks should not emit branches, got {}",
            b_count
        );
    }

    // ----- Test 8: Deeply nested blocks (5 levels) -----

    #[test]
    fn test_complex_deeply_nested_blocks() {
        // 5 levels of nesting with br from innermost to outermost
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block, // depth 4 from innermost
            WasmOp::Block, // depth 3
            WasmOp::Block, // depth 2
            WasmOp::Block, // depth 1
            WasmOp::Block, // depth 0 (innermost)
            WasmOp::I32Const(42),
            WasmOp::Br(4), // jump to outermost block end
            WasmOp::End,   // end depth 0
            WasmOp::End,   // end depth 1
            WasmOp::End,   // end depth 2
            WasmOp::End,   // end depth 3
            WasmOp::End,   // end depth 4
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have 5 block end labels
        let labels = collect_labels(&instrs);
        let block_end_labels: Vec<_> = labels.iter().filter(|l| l.contains("block_end")).collect();
        assert_eq!(
            block_end_labels.len(),
            5,
            "5 nested blocks should have 5 end labels, got {}",
            block_end_labels.len()
        );

        // The br(4) should branch to the outermost block's end
        let branches = collect_branch_targets(&instrs);
        assert_eq!(branches.len(), 1, "Should have exactly one branch (br 4)");

        // The target should be the last label emitted (outermost end)
        let outermost_label = block_end_labels.last().unwrap();
        assert_eq!(
            &branches[0], *outermost_label,
            "br(4) should target outermost block end"
        );
    }

    // ----- Test 9: Loop re-entry via br 0 -----

    #[test]
    fn test_complex_loop_reentry() {
        // Multiple br 0 in a loop body (different code paths re-enter the loop)
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Loop,        // $loop
            WasmOp::LocalGet(0), // condition
            WasmOp::If,
            WasmOp::I32Const(1),
            WasmOp::LocalSet(0),
            WasmOp::Br(1), // re-enter loop from then-arm
            WasmOp::Else,
            WasmOp::I32Const(0),
            WasmOp::LocalSet(0),
            WasmOp::Br(1), // re-enter loop from else-arm
            WasmOp::End,   // end if
            WasmOp::End,   // end loop
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should have loop_start label
        let labels = collect_labels(&instrs);
        let loop_labels: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(loop_labels.len(), 1, "Should have one loop_start label");

        // Should have two unconditional branches targeting loop_start (br 1 from both arms)
        // Plus the B that skips else at end of then-arm
        let branches = collect_branch_targets(&instrs);
        let loop_branches: Vec<_> = branches
            .iter()
            .filter(|b| b.contains("loop_start"))
            .collect();
        assert_eq!(
            loop_branches.len(),
            2,
            "Both br(1) should branch to loop_start, got {} branches to loop_start",
            loop_branches.len()
        );
    }

    // ----- Test 10: Mixed control flow — block containing loop containing if/else -----

    #[test]
    fn test_complex_block_loop_if_combined() {
        // WASM equivalent:
        //   (block $outer
        //     (loop $loop
        //       local.get 0
        //       i32.const 10
        //       i32.gt_s
        //       (if
        //         (then
        //           br 2            ;; exit $outer
        //         )
        //         (else
        //           local.get 0
        //           i32.const 1
        //           i32.add
        //           local.set 0
        //           br 1            ;; re-enter $loop
        //         )
        //       )
        //     )
        //   )
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block,       // $outer
            WasmOp::Loop,        // $loop
            WasmOp::LocalGet(0), // counter
            WasmOp::I32Const(10),
            WasmOp::I32GtS, // counter > 10?
            WasmOp::If,
            // then: exit outer
            WasmOp::Br(2), // exit $outer
            WasmOp::Else,
            // else: increment and loop
            WasmOp::LocalGet(0),
            WasmOp::I32Const(1),
            WasmOp::I32Add,
            WasmOp::LocalSet(0),
            WasmOp::Br(1), // re-enter $loop
            WasmOp::End,   // end if
            WasmOp::End,   // end loop
            WasmOp::End,   // end outer
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Verify structural elements
        let labels = collect_labels(&instrs);

        // Should have loop_start
        let loop_starts: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(loop_starts.len(), 1, "Should have one loop_start");

        // Should have block_end for outer block
        let block_ends: Vec<_> = labels.iter().filter(|l| l.contains("block_end")).collect();
        assert!(
            !block_ends.is_empty(),
            "Should have block_end label for outer block"
        );

        // Should have else and if_end labels
        let else_labels: Vec<_> = labels.iter().filter(|l| l.contains("else")).collect();
        assert!(!else_labels.is_empty(), "Should have an else label");

        let if_end_labels: Vec<_> = labels.iter().filter(|l| l.contains("if_end")).collect();
        assert!(!if_end_labels.is_empty(), "Should have an if_end label");

        // Verify branches
        let branches = collect_branch_targets(&instrs);

        // br(2) should target outer block end
        assert!(
            branches.iter().any(|b| b.contains("block_end")),
            "br(2) should target outer block_end, branches: {:?}",
            branches
        );

        // br(1) should target loop_start
        assert!(
            branches.iter().any(|b| b.contains("loop_start")),
            "br(1) should target loop_start, branches: {:?}",
            branches
        );

        // Should have ADD for counter + 1
        let add_count = count_op(&instrs, |op| matches!(op, ArmOp::Add { .. }));
        assert!(add_count >= 1, "Should have ADD for counter + 1");
    }

    // ----- Test 11: br_table within a loop -----

    #[test]
    fn test_complex_br_table_in_loop() {
        // State machine pattern: loop with br_table dispatch
        //   (loop $loop
        //     (block $state2
        //       (block $state1
        //         (block $state0
        //           local.get 0       ;; state variable
        //           br_table 0 1 2    ;; dispatch to state blocks
        //         )
        //         ;; state 0 body
        //         i32.const 1
        //         local.set 0          ;; state = 1
        //         br 2                 ;; continue loop
        //       )
        //       ;; state 1 body
        //       i32.const 2
        //       local.set 0            ;; state = 2
        //       br 1                   ;; continue loop
        //     )
        //     ;; state 2: exit (fall through to end)
        //   )
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Loop,        // $loop
            WasmOp::Block,       // $state2
            WasmOp::Block,       // $state1
            WasmOp::Block,       // $state0
            WasmOp::LocalGet(0), // state
            WasmOp::BrTable {
                targets: vec![0, 1, 2], // dispatch per state
                default: 2,             // default -> $state2 (exit)
            },
            WasmOp::End, // end $state0
            WasmOp::I32Const(1),
            WasmOp::LocalSet(0), // state = 1
            WasmOp::Br(2),       // back to $loop
            WasmOp::End,         // end $state1
            WasmOp::I32Const(2),
            WasmOp::LocalSet(0), // state = 2
            WasmOp::Br(1),       // back to $loop
            WasmOp::End,         // end $state2
            WasmOp::End,         // end $loop
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should have loop_start label
        let labels = collect_labels(&instrs);
        let loop_labels: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(loop_labels.len(), 1, "Should have one loop_start");

        // br_table should emit 3 CMP + BEQ pairs
        let cmp_count = count_op(&instrs, |op| matches!(op, ArmOp::Cmp { .. }));
        assert!(
            cmp_count >= 3,
            "br_table should emit at least 3 CMPs, got {}",
            cmp_count
        );

        // Should have branches back to loop_start (br 2 and br 1 target loop)
        let branches = collect_branch_targets(&instrs);
        let to_loop: Vec<_> = branches
            .iter()
            .filter(|b| b.contains("loop_start"))
            .collect();
        assert!(
            to_loop.len() >= 2,
            "Should have at least 2 branches back to loop_start (from state 0 and 1), got {}",
            to_loop.len()
        );
    }

    // ----- Test 12: Nested if/else without inner else clause -----

    #[test]
    fn test_complex_nested_if_no_else() {
        // Nested if without else exercises the else-label dedup path
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::I32Const(1), // outer condition
            WasmOp::If,
            WasmOp::I32Const(1), // inner condition
            WasmOp::If,
            WasmOp::I32Const(42), // deeply nested body
            WasmOp::End,          // end inner if (no else)
            WasmOp::End,          // end outer if (no else)
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Each if-without-else should emit both else label and if_end label
        let labels = collect_labels(&instrs);
        let else_labels: Vec<_> = labels.iter().filter(|l| l.contains("else")).collect();
        let end_labels: Vec<_> = labels.iter().filter(|l| l.contains("if_end")).collect();

        assert!(
            else_labels.len() >= 2,
            "Two if-without-else should emit at least 2 else labels, got {}",
            else_labels.len()
        );
        assert!(
            end_labels.len() >= 2,
            "Two if blocks should emit at least 2 if_end labels, got {}",
            end_labels.len()
        );

        // Should have 2 BEQ instructions (one per if)
        let beq_count = count_op(&instrs, |op| {
            matches!(
                op,
                ArmOp::Bcc {
                    cond: Condition::EQ,
                    ..
                }
            )
        });
        assert_eq!(
            beq_count, 2,
            "Two if blocks should emit 2 BEQ, got {}",
            beq_count
        );
    }

    // ----- Test 13: Function call within loop -----

    #[test]
    fn test_complex_call_in_loop() {
        // Loop that calls a function each iteration
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block,       // $exit
            WasmOp::Loop,        // $loop
            WasmOp::LocalGet(0), // counter
            WasmOp::I32Eqz,      // counter == 0?
            WasmOp::BrIf(1),     // exit if zero
            WasmOp::LocalGet(0), // pass counter as arg
            WasmOp::Call(5),     // call func_5
            WasmOp::Drop,        // discard return value
            WasmOp::LocalGet(0),
            WasmOp::I32Const(1),
            WasmOp::I32Sub,
            WasmOp::LocalSet(0), // counter -= 1
            WasmOp::Br(0),       // loop
            WasmOp::End,         // end loop
            WasmOp::End,         // end block
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should have a BL func_5 call
        let has_bl = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Bl { label } if label == "func_5"));
        assert!(has_bl, "Should emit BL func_5 for Call(5)");

        // Should have loop_start and backward branch
        let labels = collect_labels(&instrs);
        let loop_labels: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(loop_labels.len(), 1, "Should have one loop_start");

        let branches = collect_branch_targets(&instrs);
        assert!(
            branches.contains(loop_labels[0]),
            "Should branch back to loop_start"
        );
    }

    // ----- Test 14: Early return from nested control flow -----

    #[test]
    fn test_complex_return_from_nested() {
        // Return from inside a nested block+loop+if
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block,
            WasmOp::Loop,
            WasmOp::LocalGet(0),
            WasmOp::I32Const(0),
            WasmOp::I32Eq,
            WasmOp::If,
            WasmOp::I32Const(42),
            WasmOp::Return, // early return from inside if inside loop inside block
            WasmOp::End,    // end if
            WasmOp::Br(0),  // loop
            WasmOp::End,    // end loop
            WasmOp::End,    // end block
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should have BX LR for the Return instruction (plus the one at function end)
        let bx_count = count_op(&instrs, |op| matches!(op, ArmOp::Bx { rm: Reg::LR }));
        assert!(
            bx_count >= 2,
            "Should have at least 2 BX LR (early return + function epilogue), got {}",
            bx_count
        );

        // Should have loop_start
        let labels = collect_labels(&instrs);
        assert!(
            labels.iter().any(|l| l.contains("loop_start")),
            "Should have loop_start label"
        );

        // Should have if-related labels
        assert!(
            labels
                .iter()
                .any(|l| l.contains("if_end") || l.contains("else")),
            "Should have if-related labels"
        );
    }

    // ----- Test 15: Unreachable inside control flow -----

    #[test]
    fn test_complex_unreachable_in_block() {
        // Unreachable trap inside a conditional block
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::I32Const(0),
            WasmOp::If,
            WasmOp::Unreachable, // trap if condition is true
            WasmOp::Else,
            WasmOp::I32Const(1), // normal path
            WasmOp::End,
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have UDF for unreachable
        let udf_count = count_op(&instrs, |op| matches!(op, ArmOp::Udf { .. }));
        assert_eq!(udf_count, 1, "Should have exactly one UDF for unreachable");

        // Should still have proper if/else structure
        let labels = collect_labels(&instrs);
        assert!(
            labels.iter().any(|l| l.contains("else")),
            "Should have else label"
        );
        assert!(
            labels.iter().any(|l| l.contains("if_end")),
            "Should have if_end label"
        );
    }

    // ----- Test 16: Multiple loops (sequential, not nested) -----

    #[test]
    fn test_complex_sequential_loops() {
        // Two loops in sequence (not nested)
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            // First loop: count up
            WasmOp::Block,
            WasmOp::Loop,
            WasmOp::LocalGet(0),
            WasmOp::I32Const(10),
            WasmOp::I32GeS,
            WasmOp::BrIf(1), // exit if >= 10
            WasmOp::LocalGet(0),
            WasmOp::I32Const(1),
            WasmOp::I32Add,
            WasmOp::LocalSet(0),
            WasmOp::Br(0), // loop
            WasmOp::End,
            WasmOp::End,
            // Second loop: count down
            WasmOp::Block,
            WasmOp::Loop,
            WasmOp::LocalGet(0),
            WasmOp::I32Eqz,
            WasmOp::BrIf(1), // exit if == 0
            WasmOp::LocalGet(0),
            WasmOp::I32Const(1),
            WasmOp::I32Sub,
            WasmOp::LocalSet(0),
            WasmOp::Br(0), // loop
            WasmOp::End,
            WasmOp::End,
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should have 2 loop_start labels
        let labels = collect_labels(&instrs);
        let loop_labels: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(
            loop_labels.len(),
            2,
            "Should have 2 loop_start labels for sequential loops, got {}",
            loop_labels.len()
        );

        // Each loop should have a backward branch
        let branches = collect_branch_targets(&instrs);
        for ll in &loop_labels {
            assert!(
                branches.contains(ll),
                "Should branch back to loop_start '{}', branches: {:?}",
                ll,
                branches
            );
        }
    }

    // ----- Test 17: Instruction count sanity checks -----

    #[test]
    fn test_complex_instruction_count_sanity() {
        // Verify that control flow constructs produce a reasonable number of
        // instructions (not zero, not explosively large)
        let mut selector = fresh_selector();

        // Simple block with one instruction
        let wasm_ops = vec![WasmOp::Block, WasmOp::I32Const(1), WasmOp::End];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();
        // MOV for const + Label for block end + BX LR
        assert!(
            instrs.len() <= 5,
            "Simple block should produce <= 5 ARM instructions, got {}",
            instrs.len()
        );
        assert!(
            instrs.len() >= 2,
            "Simple block should produce >= 2 ARM instructions, got {}",
            instrs.len()
        );

        // Loop with br should produce bounded output
        selector.reset();
        let wasm_ops = vec![WasmOp::Loop, WasmOp::Br(0), WasmOp::End];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();
        assert!(
            instrs.len() <= 5,
            "Simple loop+br should produce <= 5 ARM instructions, got {}",
            instrs.len()
        );
    }

    // =========================================================================
    // GlobalGet / GlobalSet tests
    // =========================================================================

    #[test]
    fn test_global_get_select_default() {
        // global.get should generate LDR from globals base (R9)
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::GlobalGet(0)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Ldr { rd: _, addr } => {
                assert_eq!(addr.base, Reg::R9, "Globals base should be R9");
                assert_eq!(addr.offset, 0, "Global 0 should have offset 0");
                assert!(addr.offset_reg.is_none(), "No offset register");
            }
            other => panic!("Expected Ldr for global.get, got {:?}", other),
        }
    }

    #[test]
    fn test_global_get_nonzero_index_select_default() {
        // global.get with index 3 should use offset 12 (3 * 4)
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::GlobalGet(3)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Ldr { rd: _, addr } => {
                assert_eq!(addr.base, Reg::R9);
                assert_eq!(addr.offset, 12, "Global 3 should have offset 3*4=12");
            }
            other => panic!("Expected Ldr for global.get(3), got {:?}", other),
        }
    }

    #[test]
    fn test_global_set_select_default() {
        // global.set should generate STR to globals base (R9)
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::GlobalSet(0)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Str { rd: _, addr } => {
                assert_eq!(addr.base, Reg::R9, "Globals base should be R9");
                assert_eq!(addr.offset, 0, "Global 0 should have offset 0");
            }
            other => panic!("Expected Str for global.set, got {:?}", other),
        }
    }

    #[test]
    fn test_global_set_nonzero_index_select_default() {
        // global.set with index 5 should use offset 20 (5 * 4)
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::GlobalSet(5)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Str { rd: _, addr } => {
                assert_eq!(addr.base, Reg::R9);
                assert_eq!(addr.offset, 20, "Global 5 should have offset 5*4=20");
            }
            other => panic!("Expected Str for global.set(5), got {:?}", other),
        }
    }

    #[test]
    fn test_global_get_stack_mode() {
        // global.get in stack mode should push result register onto virtual stack
        let mut selector = fresh_selector();

        let wasm_ops = vec![
            WasmOp::GlobalGet(2), // Load global 2
            WasmOp::I32Const(1),
            WasmOp::I32Add, // Add 1 to global value
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have LDR from R9+8 (global index 2, offset 2*4=8)
        let has_global_ldr = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Ldr { addr, .. }
                if addr.base == Reg::R9 && addr.offset == 8
            )
        });
        assert!(
            has_global_ldr,
            "global.get(2) should emit LDR from [R9, #8]"
        );

        // Should have ADD (from the i32.add)
        let has_add = instrs.iter().any(|i| matches!(&i.op, ArmOp::Add { .. }));
        assert!(has_add, "Should emit ADD for i32.add after global.get");
    }

    #[test]
    fn test_global_set_stack_mode() {
        // global.set in stack mode should pop value and store to globals table
        let mut selector = fresh_selector();

        let wasm_ops = vec![
            WasmOp::I32Const(42), // Push value
            WasmOp::GlobalSet(1), // Store to global 1
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have STR to R9+4 (global index 1, offset 1*4=4)
        let has_global_str = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Str { addr, .. }
                if addr.base == Reg::R9 && addr.offset == 4
            )
        });
        assert!(has_global_str, "global.set(1) should emit STR to [R9, #4]");
    }

    #[test]
    fn test_global_get_set_roundtrip() {
        // global.get + modify + global.set should work correctly
        let mut selector = fresh_selector();

        let wasm_ops = vec![
            WasmOp::GlobalGet(0), // Load global 0
            WasmOp::I32Const(10), // Push 10
            WasmOp::I32Add,       // global_0 + 10
            WasmOp::GlobalSet(0), // Store back to global 0
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have LDR from R9 (global.get 0)
        let has_load = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Ldr { addr, .. }
                if addr.base == Reg::R9 && addr.offset == 0
            )
        });
        assert!(has_load, "Should have LDR from [R9, #0] for global.get(0)");

        // Should have STR to R9 (global.set 0)
        let has_store = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Str { addr, .. }
                if addr.base == Reg::R9 && addr.offset == 0
            )
        });
        assert!(has_store, "Should have STR to [R9, #0] for global.set(0)");

        // Should have ADD for the increment
        let has_add = instrs.iter().any(|i| matches!(&i.op, ArmOp::Add { .. }));
        assert!(has_add, "Should have ADD for i32.add");
    }

    // =========================================================================
    // Select instruction tests
    // =========================================================================

    #[test]
    fn test_select_default_mode() {
        // Select in select_default should emit CMP + MOV + SelectMove
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::Select];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 3, "Select should emit 3 instructions");

        // First: CMP rcond, #0
        match &arm_instrs[0].op {
            ArmOp::Cmp {
                op2: Operand2::Imm(0),
                ..
            } => {}
            other => panic!("Expected CMP rcond, #0, got {:?}", other),
        }

        // Second: MOV rd, rval1 (default)
        match &arm_instrs[1].op {
            ArmOp::Mov { .. } => {}
            other => panic!("Expected MOV rd, rval1, got {:?}", other),
        }

        // Third: SelectMove (conditional override)
        match &arm_instrs[2].op {
            ArmOp::SelectMove {
                cond: Condition::EQ,
                ..
            } => {}
            other => panic!("Expected SelectMove with EQ condition, got {:?}", other),
        }
    }

    #[test]
    fn test_select_stack_mode_with_constants() {
        // Select with three constant operands
        let mut selector = fresh_selector();

        let wasm_ops = vec![
            WasmOp::I32Const(10), // val1
            WasmOp::I32Const(20), // val2
            WasmOp::I32Const(1),  // condition (nonzero -> pick val1)
            WasmOp::Select,
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have CMP for condition
        let has_cmp = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Cmp {
                    op2: Operand2::Imm(0),
                    ..
                }
            )
        });
        assert!(has_cmp, "Select should emit CMP condition, #0");

        // Should have SelectMove EQ (conditional override)
        let has_select_move = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::SelectMove {
                    cond: Condition::EQ,
                    ..
                }
            )
        });
        assert!(has_select_move, "Select should emit SelectMove with EQ");
    }

    #[test]
    fn test_select_with_global_values() {
        // Combine global.get with select: select between two globals based on condition
        let mut selector = fresh_selector();

        let wasm_ops = vec![
            WasmOp::GlobalGet(0), // val1 = global 0
            WasmOp::GlobalGet(1), // val2 = global 1
            WasmOp::LocalGet(0),  // condition from param
            WasmOp::Select,       // pick val1 if cond != 0, else val2
            WasmOp::GlobalSet(2), // store result to global 2
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should load from globals 0 and 1
        let global_loads: Vec<_> = instrs
            .iter()
            .filter(|i| {
                matches!(
                    &i.op,
                    ArmOp::Ldr { addr, .. }
                    if addr.base == Reg::R9
                )
            })
            .collect();
        assert_eq!(
            global_loads.len(),
            2,
            "Should have 2 LDR from globals (indices 0 and 1), got {}",
            global_loads.len()
        );

        // Should store to global 2
        let global_stores: Vec<_> = instrs
            .iter()
            .filter(|i| {
                matches!(
                    &i.op,
                    ArmOp::Str { addr, .. }
                    if addr.base == Reg::R9 && addr.offset == 8
                )
            })
            .collect();
        assert_eq!(
            global_stores.len(),
            1,
            "Should have 1 STR to global 2 at [R9, #8]"
        );

        // Should have select logic
        let has_select_move = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::SelectMove {
                    cond: Condition::EQ,
                    ..
                }
            )
        });
        assert!(has_select_move, "Should have SelectMove for the select op");
    }

    // =========================================================================
    // i64 instruction selection tests
    // =========================================================================

    #[test]
    fn test_i64_const() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Const(0x0000_0001_0000_0002)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64Const { rdlo, rdhi, value } => {
                assert_eq!(*rdlo, Reg::R0);
                assert_eq!(*rdhi, Reg::R1);
                assert_eq!(*value, 0x0000_0001_0000_0002);
            }
            other => panic!("Expected I64Const, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_const_negative() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Const(-1)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64Const { value, .. } => {
                assert_eq!(*value, -1);
            }
            other => panic!("Expected I64Const, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_extend_i32_s() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64ExtendI32S];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64ExtendI32S { rdlo, rdhi, rn } => {
                assert_eq!(*rdlo, Reg::R0);
                assert_eq!(*rdhi, Reg::R1);
                assert_eq!(*rn, Reg::R0);
            }
            other => panic!("Expected I64ExtendI32S, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_extend_i32_u() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64ExtendI32U];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64ExtendI32U { rdlo, rdhi, rn } => {
                assert_eq!(*rdlo, Reg::R0);
                assert_eq!(*rdhi, Reg::R1);
                assert_eq!(*rn, Reg::R0);
            }
            other => panic!("Expected I64ExtendI32U, got {other:?}"),
        }
    }

    #[test]
    fn test_i32_wrap_i64() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32WrapI64];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I32WrapI64 { rd, rnlo } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(*rnlo, Reg::R0);
            }
            other => panic!("Expected I32WrapI64, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_add() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Add];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        // i64 add generates ADDS + ADC (two instructions)
        assert_eq!(arm_instrs.len(), 2);
        match &arm_instrs[0].op {
            ArmOp::Adds { rd, rn, op2 } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(*rn, Reg::R0);
                assert_eq!(*op2, Operand2::Reg(Reg::R2));
            }
            other => panic!("Expected Adds, got {other:?}"),
        }
        match &arm_instrs[1].op {
            ArmOp::Adc { rd, rn, op2 } => {
                assert_eq!(*rd, Reg::R1);
                assert_eq!(*rn, Reg::R1);
                assert_eq!(*op2, Operand2::Reg(Reg::R3));
            }
            other => panic!("Expected Adc, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_sub() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Sub];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 2);
        match &arm_instrs[0].op {
            ArmOp::Subs { rd, rn, op2 } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(*rn, Reg::R0);
                assert_eq!(*op2, Operand2::Reg(Reg::R2));
            }
            other => panic!("Expected Subs, got {other:?}"),
        }
        match &arm_instrs[1].op {
            ArmOp::Sbc { rd, rn, op2 } => {
                assert_eq!(*rd, Reg::R1);
                assert_eq!(*rn, Reg::R1);
                assert_eq!(*op2, Operand2::Reg(Reg::R3));
            }
            other => panic!("Expected Sbc, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_and() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64And];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 2);
        match &arm_instrs[0].op {
            ArmOp::And { rd, rn, op2 } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(*rn, Reg::R0);
                assert_eq!(*op2, Operand2::Reg(Reg::R2));
            }
            other => panic!("Expected And (lo), got {other:?}"),
        }
        match &arm_instrs[1].op {
            ArmOp::And { rd, rn, op2 } => {
                assert_eq!(*rd, Reg::R1);
                assert_eq!(*rn, Reg::R1);
                assert_eq!(*op2, Operand2::Reg(Reg::R3));
            }
            other => panic!("Expected And (hi), got {other:?}"),
        }
    }

    #[test]
    fn test_i64_or() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Or];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 2);
        assert!(matches!(&arm_instrs[0].op, ArmOp::Orr { .. }));
        assert!(matches!(&arm_instrs[1].op, ArmOp::Orr { .. }));
    }

    #[test]
    fn test_i64_xor() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Xor];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 2);
        assert!(matches!(&arm_instrs[0].op, ArmOp::Eor { .. }));
        assert!(matches!(&arm_instrs[1].op, ArmOp::Eor { .. }));
    }

    #[test]
    fn test_i64_eqz() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Eqz];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCondZ { rd, rn_lo, rn_hi } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(*rn_lo, Reg::R0);
                assert_eq!(*rn_hi, Reg::R1);
            }
            other => panic!("Expected I64SetCondZ, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_eq() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Eq];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond {
                rd,
                rn_lo,
                rn_hi,
                rm_lo,
                rm_hi,
                cond,
            } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(*rn_lo, Reg::R0);
                assert_eq!(*rn_hi, Reg::R1);
                assert_eq!(*rm_lo, Reg::R2);
                assert_eq!(*rm_hi, Reg::R3);
                assert_eq!(*cond, Condition::EQ);
            }
            other => panic!("Expected I64SetCond EQ, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_ne() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Ne];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond { cond, .. } => {
                assert_eq!(*cond, Condition::NE);
            }
            other => panic!("Expected I64SetCond NE, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_lt_s() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64LtS];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond { cond, .. } => assert_eq!(*cond, Condition::LT),
            other => panic!("Expected I64SetCond LT, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_lt_u() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64LtU];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond { cond, .. } => assert_eq!(*cond, Condition::LO),
            other => panic!("Expected I64SetCond LO, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_le_s() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64LeS];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond { cond, .. } => assert_eq!(*cond, Condition::LE),
            other => panic!("Expected I64SetCond LE, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_gt_s() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64GtS];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond { cond, .. } => assert_eq!(*cond, Condition::GT),
            other => panic!("Expected I64SetCond GT, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_ge_s() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64GeS];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond { cond, .. } => assert_eq!(*cond, Condition::GE),
            other => panic!("Expected I64SetCond GE, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_unsigned_comparisons() {
        let db = RuleDatabase::new();

        // Test all unsigned comparison conditions
        let tests = vec![
            (WasmOp::I64LeU, Condition::LS),
            (WasmOp::I64GtU, Condition::HI),
            (WasmOp::I64GeU, Condition::HS),
        ];

        for (op, expected_cond) in tests {
            let mut selector = InstructionSelector::new(db.rules().to_vec());
            let arm_instrs = selector.select(std::slice::from_ref(&op)).unwrap();
            assert_eq!(arm_instrs.len(), 1);
            match &arm_instrs[0].op {
                ArmOp::I64SetCond { cond, .. } => {
                    assert_eq!(*cond, expected_cond, "Wrong condition for {op:?}");
                }
                other => panic!("Expected I64SetCond for {op:?}, got {other:?}"),
            }
        }
    }

    #[test]
    fn test_i64_mul() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Mul];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64Mul {
                rd_lo,
                rd_hi,
                rn_lo,
                rn_hi,
                rm_lo,
                rm_hi,
            } => {
                assert_eq!(*rd_lo, Reg::R0);
                assert_eq!(*rd_hi, Reg::R1);
                assert_eq!(*rn_lo, Reg::R0);
                assert_eq!(*rn_hi, Reg::R1);
                assert_eq!(*rm_lo, Reg::R2);
                assert_eq!(*rm_hi, Reg::R3);
            }
            other => panic!("Expected I64Mul, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_shifts() {
        let db = RuleDatabase::new();

        // Shift left
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let arm_instrs = selector.select(&[WasmOp::I64Shl]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Shl { .. }));

        // Shift right unsigned
        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64ShrU]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64ShrU { .. }));

        // Shift right signed
        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64ShrS]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64ShrS { .. }));
    }

    #[test]
    fn test_i64_rotations() {
        let db = RuleDatabase::new();

        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let arm_instrs = selector.select(&[WasmOp::I64Rotl]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Rotl { .. }));

        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64Rotr]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Rotr { .. }));
    }

    #[test]
    fn test_i64_bit_manipulation() {
        let db = RuleDatabase::new();

        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let arm_instrs = selector.select(&[WasmOp::I64Clz]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Clz { .. }));

        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64Ctz]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Ctz { .. }));

        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64Popcnt]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Popcnt { .. }));
    }

    #[test]
    fn test_i64_division_remainder() {
        let db = RuleDatabase::new();

        let ops = vec![
            (WasmOp::I64DivS, "I64DivS"),
            (WasmOp::I64DivU, "I64DivU"),
            (WasmOp::I64RemS, "I64RemS"),
            (WasmOp::I64RemU, "I64RemU"),
        ];

        for (op, name) in ops {
            let mut selector = InstructionSelector::new(db.rules().to_vec());
            let arm_instrs = selector.select(&[op]).unwrap();
            assert_eq!(arm_instrs.len(), 1, "Failed for {name}");
            // Each should emit the corresponding i64 pseudo-op
        }
    }

    #[test]
    fn test_i64_extend_sign_operations() {
        let db = RuleDatabase::new();

        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let arm_instrs = selector.select(&[WasmOp::I64Extend8S]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Extend8S { .. }));

        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64Extend16S]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Extend16S { .. }));

        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64Extend32S]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Extend32S { .. }));
    }

    #[test]
    fn test_i64_add_sequence() {
        // Test a full i64 add sequence: const + const + add
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Const(1), WasmOp::I64Const(2), WasmOp::I64Add];

        let arm_instrs = selector.select(&wasm_ops).unwrap();
        // I64Const(1) -> 1 instr
        // I64Const(2) -> 1 instr
        // I64Add -> 2 instrs (ADDS + ADC)
        assert_eq!(arm_instrs.len(), 4);

        // First two are I64Const
        assert!(matches!(
            &arm_instrs[0].op,
            ArmOp::I64Const { value: 1, .. }
        ));
        assert!(matches!(
            &arm_instrs[1].op,
            ArmOp::I64Const { value: 2, .. }
        ));
        // Then ADDS + ADC
        assert!(matches!(&arm_instrs[2].op, ArmOp::Adds { .. }));
        assert!(matches!(&arm_instrs[3].op, ArmOp::Adc { .. }));
    }

    #[test]
    fn test_i64_wrap_extend_roundtrip() {
        // extend_i32_u followed by wrap_i64 should produce two instructions
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64ExtendI32U, WasmOp::I32WrapI64];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 2);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64ExtendI32U { .. }));
        assert!(matches!(&arm_instrs[1].op, ArmOp::I32WrapI64 { .. }));
    }

    #[test]
    fn test_i64_load_store() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I64Load {
                offset: 8,
                align: 8,
            },
            WasmOp::I64Store {
                offset: 16,
                align: 8,
            },
        ];

        let arm_instrs = selector.select(&wasm_ops).unwrap();
        assert_eq!(arm_instrs.len(), 2);

        match &arm_instrs[0].op {
            ArmOp::I64Ldr { rdlo, rdhi, addr } => {
                assert_eq!(*rdlo, Reg::R0);
                assert_eq!(*rdhi, Reg::R1);
                assert_eq!(addr.offset, 8);
            }
            other => panic!("Expected I64Ldr, got {other:?}"),
        }

        match &arm_instrs[1].op {
            ArmOp::I64Str { rdlo, rdhi, addr } => {
                assert_eq!(*rdlo, Reg::R0);
                assert_eq!(*rdhi, Reg::R1);
                assert_eq!(addr.offset, 16);
            }
            other => panic!("Expected I64Str, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_all_ops_no_error() {
        // Verify that ALL i64 operations now succeed (no more "requires register pairs" error)
        let db = RuleDatabase::new();

        let all_i64_ops: Vec<WasmOp> = vec![
            WasmOp::I64Const(42),
            WasmOp::I64Add,
            WasmOp::I64Sub,
            WasmOp::I64Mul,
            WasmOp::I64DivS,
            WasmOp::I64DivU,
            WasmOp::I64RemS,
            WasmOp::I64RemU,
            WasmOp::I64And,
            WasmOp::I64Or,
            WasmOp::I64Xor,
            WasmOp::I64Shl,
            WasmOp::I64ShrS,
            WasmOp::I64ShrU,
            WasmOp::I64Rotl,
            WasmOp::I64Rotr,
            WasmOp::I64Clz,
            WasmOp::I64Ctz,
            WasmOp::I64Popcnt,
            WasmOp::I64Eqz,
            WasmOp::I64Eq,
            WasmOp::I64Ne,
            WasmOp::I64LtS,
            WasmOp::I64LtU,
            WasmOp::I64LeS,
            WasmOp::I64LeU,
            WasmOp::I64GtS,
            WasmOp::I64GtU,
            WasmOp::I64GeS,
            WasmOp::I64GeU,
            WasmOp::I64ExtendI32S,
            WasmOp::I64ExtendI32U,
            WasmOp::I32WrapI64,
            WasmOp::I64Extend8S,
            WasmOp::I64Extend16S,
            WasmOp::I64Extend32S,
            WasmOp::I64Load {
                offset: 0,
                align: 8,
            },
            WasmOp::I64Store {
                offset: 0,
                align: 8,
            },
        ];

        // Each should succeed individually (no error)
        for op in &all_i64_ops {
            let mut selector = InstructionSelector::new(db.rules().to_vec());
            let result = selector.select(std::slice::from_ref(op));
            assert!(
                result.is_ok(),
                "i64 operation {op:?} should succeed but got error: {:?}",
                result.err()
            );
        }
    }
}
