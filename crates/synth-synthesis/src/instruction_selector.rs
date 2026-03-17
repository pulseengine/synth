//! Instruction Selection - Converts WebAssembly IR to ARM instructions
//!
//! Uses pattern matching to select optimal ARM instruction sequences

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

/// Convert VFP D-register index to VfpReg enum (D0-D15 for linear allocation)
fn index_to_dreg(index: u8) -> VfpReg {
    match index % 16 {
        0 => VfpReg::D0,
        1 => VfpReg::D1,
        2 => VfpReg::D2,
        3 => VfpReg::D3,
        4 => VfpReg::D4,
        5 => VfpReg::D5,
        6 => VfpReg::D6,
        7 => VfpReg::D7,
        8 => VfpReg::D8,
        9 => VfpReg::D9,
        10 => VfpReg::D10,
        11 => VfpReg::D11,
        12 => VfpReg::D12,
        13 => VfpReg::D13,
        14 => VfpReg::D14,
        _ => VfpReg::D15,
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
    /// Next available VFP D-register (D0-D15, wrapping)
    next_dreg: u8,
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
            next_dreg: 0,
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
            next_dreg: 0,
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

    /// Allocate a VFP S-register (S0-S15, wrapping)
    fn alloc_vfp_reg(&mut self) -> VfpReg {
        let reg = index_to_vfp_reg(self.next_vfp_reg);
        self.next_vfp_reg = (self.next_vfp_reg + 1) % 16;
        reg
    }

    /// Allocate a VFP D-register (D0-D15, wrapping)
    fn alloc_dreg(&mut self) -> VfpReg {
        let reg = index_to_dreg(self.next_dreg);
        self.next_dreg = (self.next_dreg + 1) % 16;
        reg
    }

    /// Check if target has double-precision FPU
    fn has_double_precision(&self) -> bool {
        matches!(self.fpu, Some(FPUPrecision::Double))
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
                // Requires multi-instruction sequence (shift-and-add or lookup table)
                return Err(synth_core::Error::synthesis(
                    "i32.popcnt not yet implemented (no native ARM instruction)",
                ));
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

            // Structural control flow — no ARM code emitted, handled by control flow pass
            Nop | End | Drop => vec![ArmOp::Nop],
            If | Else => vec![ArmOp::Nop],

            // Trap: unreachable should generate an undefined instruction
            Unreachable => vec![ArmOp::Udf { imm: 0 }],

            // --- Unsupported operations: explicit error instead of silent NOP ---
            BrTable { .. } => {
                return Err(synth_core::Error::synthesis(
                    "br_table not yet implemented in instruction selector",
                ));
            }
            GlobalGet(_) | GlobalSet(_) => {
                return Err(synth_core::Error::synthesis(
                    "global.get/global.set not yet implemented",
                ));
            }
            Select => {
                return Err(synth_core::Error::synthesis("select not yet implemented"));
            }

            // i64 operations — not supported on 32-bit ARM without register pairs
            op @ (I64Add
            | I64Sub
            | I64Mul
            | I64DivS
            | I64DivU
            | I64RemS
            | I64RemU
            | I64And
            | I64Or
            | I64Xor
            | I64Shl
            | I64ShrS
            | I64ShrU
            | I64Rotl
            | I64Rotr
            | I64Clz
            | I64Ctz
            | I64Popcnt
            | I64Eqz
            | I64Eq
            | I64Ne
            | I64LtS
            | I64LtU
            | I64LeS
            | I64LeU
            | I64GtS
            | I64GtU
            | I64GeS
            | I64GeU
            | I64Const(_)
            | I64Load { .. }
            | I64Store { .. }
            | I64ExtendI32S
            | I64ExtendI32U
            | I32WrapI64
            | I64Extend8S
            | I64Extend16S
            | I64Extend32S) => {
                return Err(synth_core::Error::synthesis(format!(
                    "i64 operation not supported (requires register pairs on 32-bit ARM): {op:?}"
                )));
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

            // F32 pseudo-ops with FPU — generate VFP sequences
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

            F32DemoteF64 if self.has_double_precision() => {
                // VCVT.F32.F64 Sd, Dm — needs a dedicated ArmOp.
                // For now, return an error until the ArmOp variant is added.
                return Err(synth_core::Error::synthesis(format!(
                    "F32DemoteF64 not yet supported on target {} (needs VCVT.F32.F64 encoding)",
                    self.target_name
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

            // ===== F64 operations (double-precision FPU required) =====
            F64Add if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dn = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Add { dd, dn, dm }]
            }
            F64Sub if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dn = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Sub { dd, dn, dm }]
            }
            F64Mul if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dn = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Mul { dd, dn, dm }]
            }
            F64Div if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dn = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Div { dd, dn, dm }]
            }

            F64Abs if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Abs { dd, dm }]
            }
            F64Neg if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Neg { dd, dm }]
            }
            F64Sqrt if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Sqrt { dd, dm }]
            }
            F64Ceil if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Ceil { dd, dm }]
            }
            F64Floor if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Floor { dd, dm }]
            }
            F64Trunc if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Trunc { dd, dm }]
            }
            F64Nearest if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Nearest { dd, dm }]
            }
            F64Min if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dn = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Min { dd, dn, dm }]
            }
            F64Max if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dn = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Max { dd, dn, dm }]
            }
            F64Copysign if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let dn = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Copysign { dd, dn, dm }]
            }

            F64Eq if self.has_double_precision() => {
                let dn = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Eq { rd, dn, dm }]
            }
            F64Ne if self.has_double_precision() => {
                let dn = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Ne { rd, dn, dm }]
            }
            F64Lt if self.has_double_precision() => {
                let dn = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Lt { rd, dn, dm }]
            }
            F64Le if self.has_double_precision() => {
                let dn = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Le { rd, dn, dm }]
            }
            F64Gt if self.has_double_precision() => {
                let dn = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Gt { rd, dn, dm }]
            }
            F64Ge if self.has_double_precision() => {
                let dn = self.alloc_dreg();
                let dm = self.alloc_dreg();
                vec![ArmOp::F64Ge { rd, dn, dm }]
            }

            F64Const(val) if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                vec![ArmOp::F64Const { dd, value: *val }]
            }

            F64Load { offset, .. } if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let addr_reg = self.regs.alloc_reg();
                vec![ArmOp::F64Load {
                    dd,
                    addr: MemAddr::reg_imm(Reg::R11, addr_reg, *offset as i32),
                }]
            }
            F64Store { offset, .. } if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let addr_reg = self.regs.alloc_reg();
                vec![ArmOp::F64Store {
                    dd,
                    addr: MemAddr::reg_imm(Reg::R11, addr_reg, *offset as i32),
                }]
            }

            F64ConvertI32S if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                vec![ArmOp::F64ConvertI32S { dd, rm }]
            }
            F64ConvertI32U if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                vec![ArmOp::F64ConvertI32U { dd, rm }]
            }
            F64PromoteF32 if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F64PromoteF32 { dd, sm }]
            }

            F64ReinterpretI64 if self.has_double_precision() => {
                let dd = self.alloc_dreg();
                let rmlo = self.regs.alloc_reg();
                let rmhi = self.regs.alloc_reg();
                vec![ArmOp::F64ReinterpretI64 { dd, rmlo, rmhi }]
            }
            I64ReinterpretF64 if self.has_double_precision() => {
                let rdlo = self.regs.alloc_reg();
                let rdhi = self.regs.alloc_reg();
                let dm = self.alloc_dreg();
                vec![ArmOp::I64ReinterpretF64 { rdlo, rdhi, dm }]
            }

            I32TruncF64S if self.has_double_precision() => {
                let dm = self.alloc_dreg();
                vec![ArmOp::I32TruncF64S { rd, dm }]
            }
            I32TruncF64U if self.has_double_precision() => {
                let dm = self.alloc_dreg();
                vec![ArmOp::I32TruncF64U { rd, dm }]
            }

            // Complex i64↔f64 conversions — require multi-step sequences
            op @ (F64ConvertI64S | F64ConvertI64U | I64TruncF64S | I64TruncF64U)
                if self.has_double_precision() =>
            {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?} not supported (requires i64 register pairs on 32-bit ARM)"
                )));
            }

            // F64 ops on non-double-precision targets
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
}
