//! Optimizer Bridge - Integrates optimization passes with instruction selection
//!
//! This module bridges the synthesis engine with the optimization framework,
//! allowing WASM-level and IR-level optimizations before final code generation.
//!
//! ## Multi-Pass Architecture
//!
//! 1. WASM preprocessing: Pattern-match if-else→select, etc.
//! 2. WASM → IR conversion
//! 3. IR optimization passes (constant folding, DCE, etc.)
//! 4. IR → ARM lowering
//! 5. ARM encoding with branch resolution

use crate::rules::{ArmOp, WasmOp};
use crate::Condition;
use synth_cfg::{Cfg, CfgBuilder};
use synth_core::Result;
use synth_opt::{
    AlgebraicSimplification, CommonSubexpressionElimination, ConstantFolding, DeadCodeElimination,
    Instruction, Opcode, OptResult, PassManager, PeepholeOptimization, Reg as OptReg,
};

/// Optimization configuration
#[derive(Debug, Clone)]
pub struct OptimizationConfig {
    /// Enable constant folding
    pub enable_constant_folding: bool,
    /// Enable CSE
    pub enable_cse: bool,
    /// Enable algebraic simplification
    pub enable_algebraic: bool,
    /// Enable peephole optimization
    pub enable_peephole: bool,
    /// Enable dead code elimination
    pub enable_dce: bool,
    /// Maximum optimization iterations
    pub max_iterations: usize,
    /// Verbose output
    pub verbose: bool,
}

impl Default for OptimizationConfig {
    fn default() -> Self {
        Self {
            enable_constant_folding: true,
            enable_cse: true,
            enable_algebraic: true,
            enable_peephole: true,
            enable_dce: true,
            max_iterations: 10,
            verbose: false,
        }
    }
}

impl OptimizationConfig {
    /// Create config with all optimizations enabled
    pub fn all() -> Self {
        Self::default()
    }

    /// Create config with all optimizations disabled
    pub fn none() -> Self {
        Self {
            enable_constant_folding: false,
            enable_cse: false,
            enable_algebraic: false,
            enable_peephole: false,
            enable_dce: false,
            max_iterations: 0,
            verbose: false,
        }
    }

    /// Create config with only fast optimizations
    pub fn fast() -> Self {
        Self {
            enable_constant_folding: true,
            enable_algebraic: true,
            enable_peephole: true,
            enable_cse: false,
            enable_dce: false,
            max_iterations: 3,
            verbose: false,
        }
    }

    /// Create config compatible with Loom preprocessing
    ///
    /// When Loom is used as a WASM-level optimizer before Synth,
    /// disable passes that Loom already handles to avoid redundant work:
    /// - Constant folding (Loom does this)
    /// - Strength reduction (via algebraic, Loom does this)
    ///
    /// Keep passes that operate at IR level and complement Loom:
    /// - CSE (at register IR level)
    /// - DCE (at register IR level)
    /// - Peephole (ARM-specific patterns)
    pub fn loom_compat() -> Self {
        Self {
            enable_constant_folding: false, // Loom handles this
            enable_algebraic: false,        // Loom handles strength reduction
            enable_peephole: true,          // ARM-specific, Loom doesn't do this
            enable_cse: true,               // IR-level, complements Loom
            enable_dce: true,               // IR-level, complements Loom
            max_iterations: 5,
            verbose: false,
        }
    }
}

/// Optimization statistics
#[derive(Debug, Clone, Default)]
pub struct OptimizationStats {
    /// Number of instructions removed
    pub removed: usize,
    /// Number of instructions modified
    pub modified: usize,
    /// Number of instructions added
    pub added: usize,
    /// Number of optimization passes run
    pub passes_run: usize,
}

/// Optimizer bridge that integrates with synthesis pipeline
pub struct OptimizerBridge {
    config: OptimizationConfig,
}

impl OptimizerBridge {
    /// Create a new optimizer bridge with default configuration
    pub fn new() -> Self {
        Self {
            config: OptimizationConfig::default(),
        }
    }

    /// Create with custom configuration
    pub fn with_config(config: OptimizationConfig) -> Self {
        Self { config }
    }

    /// Preprocess WASM ops to transform patterns before IR conversion
    ///
    /// This pass converts control flow patterns to select instructions,
    /// which can be lowered to branchless ARM code (conditional moves).
    ///
    /// ## Pattern 1: Simple if-else
    /// ```text
    /// condition           ; value on stack
    /// If                  ; start if
    ///   value1            ; then-block pushes one value
    /// Else
    ///   value2            ; else-block pushes one value
    /// End
    /// ```
    /// Becomes:
    /// ```text
    /// value1              ; true value (pushed first)
    /// value2              ; false value (pushed second)
    /// condition           ; condition (on top)
    /// Select              ; pick one
    /// ```
    ///
    /// ## Pattern 2: Nested if-else
    /// ```text
    /// outer_cond
    /// If
    ///   inner_cond
    ///   If
    ///     val1
    ///   Else
    ///     val2
    ///   End
    /// Else
    ///   val3
    /// End
    /// ```
    /// Becomes:
    /// ```text
    /// val1, val2, inner_cond, Select   ; inner select
    /// val3                              ; else value
    /// outer_cond                        ; outer condition
    /// Select                            ; outer select
    /// ```
    ///
    /// ## Pattern 3: br_if at block end with simple value
    /// ```text
    /// Block
    ///   val1
    ///   cond
    ///   BrIf(0)     ; if cond, return val1
    ///   Drop
    ///   val2        ; else return val2
    /// End
    /// ```
    /// Becomes:
    /// ```text
    /// val1              ; true value
    /// val2              ; false value
    /// cond              ; condition
    /// Select            ; pick one
    /// ```
    fn preprocess_wasm_ops(&self, wasm_ops: &[WasmOp]) -> Vec<WasmOp> {
        let mut result = Vec::new();
        let mut i = 0;

        while i < wasm_ops.len() {
            // Pattern 3: Block with br_if early exit
            // Block, val1, cond, BrIf(0), Drop, val2, End
            if i + 6 < wasm_ops.len()
                && matches!(wasm_ops[i], WasmOp::Block)
                && Self::is_simple_value(&wasm_ops[i + 1])
                && Self::is_condition_producer(&wasm_ops[i + 2])
                && matches!(wasm_ops[i + 3], WasmOp::BrIf(0))
                && matches!(wasm_ops[i + 4], WasmOp::Drop)
                && Self::is_simple_value(&wasm_ops[i + 5])
                && matches!(wasm_ops[i + 6], WasmOp::End)
            {
                // br_if pattern: select(val1, val2, cond)
                let val1 = wasm_ops[i + 1].clone();
                let cond = wasm_ops[i + 2].clone();
                let val2 = wasm_ops[i + 5].clone();

                // Emit: val1, val2, cond, select
                result.push(val1);
                result.push(val2);
                result.push(cond);
                result.push(WasmOp::Select);

                i += 7;
                continue;
            }

            // Pattern 2: Nested if-else → nested select
            // [outer_cond already in result], If, inner_cond, If, val1, Else, val2, End, Else, val3, End
            // Pattern: i=If, i+1=inner_cond, i+2=If, i+3=val1, i+4=Else, i+5=val2, i+6=End, i+7=Else, i+8=val3, i+9=End
            //
            // IMPORTANT: The outer condition (e.g., LocalGet 0 = R0) must be evaluated BEFORE
            // the inner select runs, because the inner select writes its result to R0.
            // We save the outer condition to a synthetic local (index 255) to preserve it.
            if i + 9 < wasm_ops.len()
                && matches!(wasm_ops[i], WasmOp::If)
                && Self::is_condition_producer(&wasm_ops[i + 1])
                && matches!(wasm_ops[i + 2], WasmOp::If)
                && Self::is_simple_value(&wasm_ops[i + 3])
                && matches!(wasm_ops[i + 4], WasmOp::Else)
                && Self::is_simple_value(&wasm_ops[i + 5])
                && matches!(wasm_ops[i + 6], WasmOp::End)
                && matches!(wasm_ops[i + 7], WasmOp::Else)
                && Self::is_simple_value(&wasm_ops[i + 8])
                && matches!(wasm_ops[i + 9], WasmOp::End)
            {
                // Pop outer condition (e.g., LocalGet 0)
                let outer_cond = if !result.is_empty() {
                    result.pop()
                } else {
                    None
                };

                let inner_cond = wasm_ops[i + 1].clone();
                let val1 = wasm_ops[i + 3].clone();
                let val2 = wasm_ops[i + 5].clone();
                let val3 = wasm_ops[i + 8].clone();

                // Save outer condition to synthetic local 255 BEFORE inner select
                // This preserves the outer condition value before R0 gets overwritten
                if let Some(ref cond) = outer_cond {
                    result.push(cond.clone());
                    result.push(WasmOp::LocalSet(255)); // Save to synthetic local
                }

                // Emit inner select: val1, val2, inner_cond, select
                result.push(val1);
                result.push(val2);
                result.push(inner_cond);
                result.push(WasmOp::Select);

                // Emit outer select: [inner_result on stack], val3, outer_cond, select
                result.push(val3);
                if outer_cond.is_some() {
                    // Load the saved outer condition from synthetic local
                    result.push(WasmOp::LocalGet(255));
                } else {
                    result.push(WasmOp::I32Const(0));
                }
                result.push(WasmOp::Select);

                i += 10;
                continue;
            }

            // Pattern 1: Simple if-else → select
            // [condition], If, [then_value], Else, [else_value], End
            if i + 4 < wasm_ops.len()
                && matches!(wasm_ops[i], WasmOp::If)
                && Self::is_simple_value(&wasm_ops[i + 1])
                && matches!(wasm_ops[i + 2], WasmOp::Else)
                && Self::is_simple_value(&wasm_ops[i + 3])
                && matches!(wasm_ops[i + 4], WasmOp::End)
            {
                // Pop the condition (last thing added before If)
                let condition = if !result.is_empty() {
                    result.pop()
                } else {
                    None
                };

                // Extract the then and else values
                let then_value = wasm_ops[i + 1].clone();
                let else_value = wasm_ops[i + 3].clone();

                // Emit: then_value, else_value, condition, select
                result.push(then_value);
                result.push(else_value);
                if let Some(cond) = condition {
                    result.push(cond);
                } else {
                    // No condition found, use a placeholder
                    result.push(WasmOp::I32Const(0));
                }
                result.push(WasmOp::Select);

                // Skip the matched pattern
                i += 5;
            } else {
                // No pattern match, just copy the op
                result.push(wasm_ops[i].clone());
                i += 1;
            }
        }

        result
    }

    /// Check if a WASM op produces a simple value (suitable for if-else→select transform)
    fn is_simple_value(op: &WasmOp) -> bool {
        matches!(
            op,
            WasmOp::I32Const(_)
                | WasmOp::LocalGet(_)
                | WasmOp::GlobalGet(_)
        )
    }

    /// Check if a WASM op is a condition producer (comparison, local.get, etc.)
    /// Used to identify conditions in nested if-else patterns
    fn is_condition_producer(op: &WasmOp) -> bool {
        matches!(
            op,
            WasmOp::I32Const(_)
                | WasmOp::LocalGet(_)
                | WasmOp::GlobalGet(_)
                | WasmOp::I32Eqz
                | WasmOp::I32Eq
                | WasmOp::I32Ne
                | WasmOp::I32LtS
                | WasmOp::I32LtU
                | WasmOp::I32LeS
                | WasmOp::I32LeU
                | WasmOp::I32GtS
                | WasmOp::I32GtU
                | WasmOp::I32GeS
                | WasmOp::I32GeU
        )
    }

    /// Returns how many i64 values a WASM op consumes (0 if not an i64-consuming op)
    fn i64_operand_count(op: &WasmOp) -> usize {
        match op {
            // Binary ops consuming 2 i64 values
            WasmOp::I64Add | WasmOp::I64Sub | WasmOp::I64And | WasmOp::I64Or
            | WasmOp::I64Xor | WasmOp::I64Mul | WasmOp::I64Shl | WasmOp::I64ShrS
            | WasmOp::I64ShrU | WasmOp::I64Rotl | WasmOp::I64Rotr
            // Comparisons also consume 2 i64 values (but produce i32)
            | WasmOp::I64Eq | WasmOp::I64Ne | WasmOp::I64LtS | WasmOp::I64LtU
            | WasmOp::I64GtS | WasmOp::I64GtU | WasmOp::I64LeS | WasmOp::I64LeU
            | WasmOp::I64GeS | WasmOp::I64GeU => 2,
            // Unary ops consuming 1 i64 value
            WasmOp::I64Eqz | WasmOp::I64Clz | WasmOp::I64Ctz | WasmOp::I64Popcnt => 1,
            _ => 0,
        }
    }

    /// Analyze WASM ops to determine which LocalGet operations load i64 values.
    /// Returns a set of indices where LocalGet should be treated as i64.
    fn analyze_i64_local_gets(wasm_ops: &[WasmOp]) -> std::collections::HashSet<usize> {
        use std::collections::HashSet;
        let mut i64_local_gets: HashSet<usize> = HashSet::new();

        // Track stack depth to find which LocalGets feed into i64 ops
        for (i, op) in wasm_ops.iter().enumerate() {
            let count = Self::i64_operand_count(op);
            if count > 0 {
                // Walk backward to find the i64 operands (LocalGets or I64Consts)
                let mut found = 0;
                let mut j = i;
                while j > 0 && found < count {
                    j -= 1;
                    match &wasm_ops[j] {
                        WasmOp::LocalGet(_) => {
                            i64_local_gets.insert(j);
                            found += 1;
                        }
                        WasmOp::I64Const(_) => {
                            found += 1;
                        }
                        // Skip non-value-producing ops
                        _ => {}
                    }
                }
            }
        }

        i64_local_gets
    }

    /// Convert WASM operations to optimization IR
    fn wasm_to_ir(&self, wasm_ops: &[WasmOp]) -> (Vec<Instruction>, Cfg) {
        let mut builder = CfgBuilder::new();
        let mut instructions = Vec::new();
        let mut inst_id: usize = 0;

        // Analyze which LocalGets should produce i64 values (using 2 register slots)
        let i64_local_gets = Self::analyze_i64_local_gets(wasm_ops);

        // Track control flow block stack for proper branch target resolution
        // Each entry is (block_type, start_inst_id) where block_type: 0=block, 1=loop
        let mut block_stack: Vec<(u8, usize)> = Vec::new();

        for (wasm_idx, wasm_op) in wasm_ops.iter().enumerate() {
            builder.add_instruction();

            let opcode = match wasm_op {
                WasmOp::I32Const(val) => Opcode::Const {
                    dest: OptReg(inst_id as u32),
                    value: *val,
                },

                // Arithmetic operations
                WasmOp::I32Add => Opcode::Add {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32Sub => Opcode::Sub {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32Mul => Opcode::Mul {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32DivS => Opcode::DivS {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32DivU => Opcode::DivU {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32RemS => Opcode::RemS {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32RemU => Opcode::RemU {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },

                // Bitwise operations
                WasmOp::I32And => Opcode::And {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32Or => Opcode::Or {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32Xor => Opcode::Xor {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32Shl => Opcode::Shl {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32ShrS => Opcode::ShrS {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32ShrU => Opcode::ShrU {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32Rotl => Opcode::Rotl {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32Rotr => Opcode::Rotr {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },

                // Comparison operations
                WasmOp::I32Eq => Opcode::Eq {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32Ne => Opcode::Ne {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32LtS => Opcode::LtS {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32LtU => Opcode::LtU {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32LeS => Opcode::LeS {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32LeU => Opcode::LeU {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32GtS => Opcode::GtS {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32GtU => Opcode::GtU {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32GeS => Opcode::GeS {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32GeU => Opcode::GeU {
                    dest: OptReg(inst_id as u32),
                    src1: OptReg(inst_id.saturating_sub(2) as u32),
                    src2: OptReg(inst_id.saturating_sub(1) as u32),
                },

                // Equal to zero (unary comparison)
                WasmOp::I32Eqz => Opcode::Eqz {
                    dest: OptReg(inst_id as u32),
                    src: OptReg(inst_id.saturating_sub(1) as u32),
                },

                // Bit count operations (unary)
                WasmOp::I32Clz => Opcode::Clz {
                    dest: OptReg(inst_id as u32),
                    src: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32Ctz => Opcode::Ctz {
                    dest: OptReg(inst_id as u32),
                    src: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32Popcnt => Opcode::Popcnt {
                    dest: OptReg(inst_id as u32),
                    src: OptReg(inst_id.saturating_sub(1) as u32),
                },

                // Sign extension (unary)
                WasmOp::I32Extend8S => Opcode::Extend8S {
                    dest: OptReg(inst_id as u32),
                    src: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I32Extend16S => Opcode::Extend16S {
                    dest: OptReg(inst_id as u32),
                    src: OptReg(inst_id.saturating_sub(1) as u32),
                },

                // Memory and locals
                // For i64 LocalGets, we use I64Load which produces 2 register slots
                WasmOp::LocalGet(idx) => {
                    if i64_local_gets.contains(&wasm_idx) {
                        // This LocalGet is for an i64 value - use I64Load
                        // I64Load produces dest_lo at inst_id and dest_hi at inst_id+1
                        let opcode = Opcode::I64Load {
                            dest_lo: OptReg(inst_id as u32),
                            dest_hi: OptReg((inst_id + 1) as u32),
                            addr: *idx,
                        };
                        // We need to "consume" an extra instruction slot for the hi register
                        // This is done by incrementing inst_id by 2 instead of 1 later
                        instructions.push(Instruction {
                            id: inst_id,
                            opcode,
                            block_id: 0,
                            is_dead: false,
                        });
                        inst_id += 2; // Skip an extra slot for hi register
                        builder.add_instruction(); // Add extra instruction for hi part
                        continue; // Skip the normal instruction push at end of loop
                    } else {
                        Opcode::Load {
                            dest: OptReg(inst_id as u32),
                            addr: *idx,
                        }
                    }
                }
                WasmOp::LocalSet(idx) => Opcode::Store {
                    src: OptReg(inst_id.saturating_sub(1) as u32),
                    addr: *idx,
                },

                // i64 operations (use register pairs on 32-bit ARM)
                // For i64, we use pairs of virtual registers:
                // - First i64 operand: inst_id-4 (lo), inst_id-3 (hi)
                // - Second i64 operand: inst_id-2 (lo), inst_id-1 (hi)
                // - Result: inst_id (lo), inst_id+1 (hi)
                WasmOp::I64Const(val) => {
                    let opcode = Opcode::I64Const {
                        dest_lo: OptReg(inst_id as u32),
                        dest_hi: OptReg((inst_id + 1) as u32),
                        value: *val,
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    inst_id += 2; // Consume 2 slots for lo and hi
                    builder.add_instruction(); // Add extra instruction for hi part
                    continue;
                }
                WasmOp::I64Add => Opcode::I64Add {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I64Sub => Opcode::I64Sub {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I64And => Opcode::I64And {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I64Or => Opcode::I64Or {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I64Xor => Opcode::I64Xor {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },

                // i64 multiply and shifts (produce i64 pair result)
                WasmOp::I64Mul => Opcode::I64Mul {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },
                // i64 division and remainder (produce i64 pair result)
                WasmOp::I64DivS => Opcode::I64DivS {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I64DivU => Opcode::I64DivU {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I64RemS => Opcode::I64RemS {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I64RemU => Opcode::I64RemU {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I64Shl => Opcode::I64Shl {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I64ShrS => Opcode::I64ShrS {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I64ShrU => Opcode::I64ShrU {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I64Rotl => Opcode::I64Rotl {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },
                WasmOp::I64Rotr => Opcode::I64Rotr {
                    dest_lo: OptReg(inst_id as u32),
                    dest_hi: OptReg((inst_id + 1) as u32),
                    src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                    src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                    src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                },

                // i64 comparisons (consume 2 i64 pairs, produce single i32 result)
                WasmOp::I64Eq | WasmOp::I64Ne | WasmOp::I64LtS | WasmOp::I64LtU
                | WasmOp::I64GtS | WasmOp::I64GtU | WasmOp::I64LeS | WasmOp::I64LeU
                | WasmOp::I64GeS | WasmOp::I64GeU => {
                    // Comparisons take 2 i64 values (4 regs) and produce 1 i32 (1 reg)
                    let opcode = match wasm_op {
                        WasmOp::I64Eq => Opcode::I64Eq {
                            dest: OptReg(inst_id as u32),
                            src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                            src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                            src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                            src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                        },
                        WasmOp::I64Ne => Opcode::I64Ne {
                            dest: OptReg(inst_id as u32),
                            src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                            src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                            src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                            src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                        },
                        WasmOp::I64LtS => Opcode::I64LtS {
                            dest: OptReg(inst_id as u32),
                            src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                            src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                            src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                            src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                        },
                        WasmOp::I64LtU => Opcode::I64LtU {
                            dest: OptReg(inst_id as u32),
                            src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                            src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                            src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                            src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                        },
                        WasmOp::I64GtS => Opcode::I64GtS {
                            dest: OptReg(inst_id as u32),
                            src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                            src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                            src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                            src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                        },
                        WasmOp::I64GtU => Opcode::I64GtU {
                            dest: OptReg(inst_id as u32),
                            src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                            src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                            src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                            src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                        },
                        WasmOp::I64LeS => Opcode::I64LeS {
                            dest: OptReg(inst_id as u32),
                            src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                            src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                            src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                            src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                        },
                        WasmOp::I64LeU => Opcode::I64LeU {
                            dest: OptReg(inst_id as u32),
                            src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                            src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                            src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                            src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                        },
                        WasmOp::I64GeS => Opcode::I64GeS {
                            dest: OptReg(inst_id as u32),
                            src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                            src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                            src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                            src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                        },
                        WasmOp::I64GeU => Opcode::I64GeU {
                            dest: OptReg(inst_id as u32),
                            src1_lo: OptReg(inst_id.saturating_sub(4) as u32),
                            src1_hi: OptReg(inst_id.saturating_sub(3) as u32),
                            src2_lo: OptReg(inst_id.saturating_sub(2) as u32),
                            src2_hi: OptReg(inst_id.saturating_sub(1) as u32),
                        },
                        _ => unreachable!(),
                    };
                    // Single i32 result: don't increment by 2
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                // i64 equal-to-zero (consumes 1 i64 value, produces i32)
                WasmOp::I64Eqz => {
                    let opcode = Opcode::I64Eqz {
                        dest: OptReg(inst_id as u32),
                        src_lo: OptReg(inst_id.saturating_sub(2) as u32),
                        src_hi: OptReg(inst_id.saturating_sub(1) as u32),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                // i64 count leading zeros (consumes 1 i64 value, produces i32)
                WasmOp::I64Clz => {
                    let opcode = Opcode::I64Clz {
                        dest: OptReg(inst_id as u32),
                        src_lo: OptReg(inst_id.saturating_sub(2) as u32),
                        src_hi: OptReg(inst_id.saturating_sub(1) as u32),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                // i64 count trailing zeros (consumes 1 i64 value, produces i32)
                WasmOp::I64Ctz => {
                    let opcode = Opcode::I64Ctz {
                        dest: OptReg(inst_id as u32),
                        src_lo: OptReg(inst_id.saturating_sub(2) as u32),
                        src_hi: OptReg(inst_id.saturating_sub(1) as u32),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                // i64 population count (consumes 1 i64 value, produces i32)
                WasmOp::I64Popcnt => {
                    let opcode = Opcode::I64Popcnt {
                        dest: OptReg(inst_id as u32),
                        src_lo: OptReg(inst_id.saturating_sub(2) as u32),
                        src_hi: OptReg(inst_id.saturating_sub(1) as u32),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                // i64 sign extension (takes i64, produces i64)
                WasmOp::I64Extend8S => {
                    let opcode = Opcode::I64Extend8S {
                        dest_lo: OptReg(inst_id as u32),
                        dest_hi: OptReg((inst_id + 1) as u32),
                        src_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                WasmOp::I64Extend16S => {
                    let opcode = Opcode::I64Extend16S {
                        dest_lo: OptReg(inst_id as u32),
                        dest_hi: OptReg((inst_id + 1) as u32),
                        src_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                WasmOp::I64Extend32S => {
                    let opcode = Opcode::I64Extend32S {
                        dest_lo: OptReg(inst_id as u32),
                        dest_hi: OptReg((inst_id + 1) as u32),
                        src_lo: OptReg(inst_id.saturating_sub(2) as u32),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                // Select: dest = cond != 0 ? val_true : val_false
                // Stack: [val_true, val_false, cond] -> [result]
                WasmOp::Select => Opcode::Select {
                    dest: OptReg(inst_id as u32),
                    val_true: OptReg(inst_id.saturating_sub(3) as u32),
                    val_false: OptReg(inst_id.saturating_sub(2) as u32),
                    cond: OptReg(inst_id.saturating_sub(1) as u32),
                },

                // ========================================================================
                // Control Flow Operations (Loop Support)
                // ========================================================================

                // Loop: emit a label at the start (backward branch target)
                // WASM loop semantics: br to a loop jumps to START of loop
                WasmOp::Loop => {
                    // Push loop onto block stack - target is the CURRENT instruction
                    block_stack.push((1, inst_id)); // 1 = loop
                    Opcode::Label { id: inst_id }
                }

                // Block: emit a label placeholder (forward branch target at End)
                WasmOp::Block => {
                    // Push block onto stack - target will be at End
                    block_stack.push((0, inst_id)); // 0 = block
                    Opcode::Nop // Label will be at End
                }

                // End: marks the end of a block/loop/function
                // For blocks, this is where forward branches land
                WasmOp::End => {
                    // Pop the block stack
                    block_stack.pop();
                    Opcode::Label { id: inst_id }
                }

                // Br: unconditional branch to label
                WasmOp::Br(depth) => {
                    // Find the target block at given depth
                    let target_idx = block_stack.len().saturating_sub(1 + *depth as usize);
                    if target_idx < block_stack.len() {
                        let (block_type, target_inst) = block_stack[target_idx];
                        // For loops, branch to start; for blocks, target will be resolved later
                        Opcode::Branch { target: target_inst }
                    } else {
                        Opcode::Branch { target: 0 }
                    }
                }

                // BrIf: conditional branch - branch if top of stack is non-zero
                WasmOp::BrIf(depth) => {
                    // Find the target block at given depth
                    let target_idx = block_stack.len().saturating_sub(1 + *depth as usize);
                    let target = if target_idx < block_stack.len() {
                        let (block_type, target_inst) = block_stack[target_idx];
                        // For loops (type 1), branch to start instruction
                        target_inst
                    } else {
                        0
                    };
                    Opcode::CondBranch {
                        cond: OptReg(inst_id.saturating_sub(1) as u32),
                        target,
                    }
                }

                // LocalTee: store value AND keep it on stack
                // This is store + copy (value stays on stack for next op)
                WasmOp::LocalTee(idx) => {
                    // TeeStore combines Store + Copy:
                    // 1. Store src to local[addr]
                    // 2. Copy src to dest (keeps value available for next op)
                    Opcode::TeeStore {
                        dest: OptReg(inst_id as u32),
                        src: OptReg(inst_id.saturating_sub(1) as u32),
                        addr: *idx,
                    }
                }

                // ========================================================================
                // Linear Memory Operations (i32.load / i32.store)
                // ========================================================================

                // I32Load: pop address, load 32-bit value from linear memory
                // Stack: [addr] -> [value]
                WasmOp::I32Load { offset, .. } => Opcode::MemLoad {
                    dest: OptReg(inst_id as u32),
                    addr: OptReg(inst_id.saturating_sub(1) as u32),
                    offset: *offset,
                },

                // I32Store: pop value and address, store to linear memory
                // Stack: [addr, value] -> []
                WasmOp::I32Store { offset, .. } => Opcode::MemStore {
                    src: OptReg(inst_id.saturating_sub(1) as u32),
                    addr: OptReg(inst_id.saturating_sub(2) as u32),
                    offset: *offset,
                },

                // Fallback for unsupported ops
                _ => Opcode::Nop,
            };

            instructions.push(Instruction {
                id: inst_id,
                opcode,
                block_id: 0,
                is_dead: false,
            });

            inst_id += 1;
        }

        let cfg = builder.build();
        (instructions, cfg)
    }

    /// Optimize WASM operation sequence and return the optimized IR
    ///
    /// This is the main entry point for the optimization pipeline. It converts
    /// WASM ops to the optimizer IR, runs all enabled passes, and returns
    /// the optimized instructions along with the CFG and statistics.
    pub fn optimize_full(
        &self,
        wasm_ops: &[WasmOp],
    ) -> Result<(Vec<Instruction>, Cfg, OptimizationStats)> {
        if wasm_ops.is_empty() {
            return Ok((Vec::new(), CfgBuilder::new().build(), OptimizationStats::default()));
        }

        // Preprocess: convert if-else patterns to select
        let preprocessed = self.preprocess_wasm_ops(wasm_ops);

        // Convert to IR
        let (mut instructions, mut cfg) = self.wasm_to_ir(&preprocessed);

        // Build and run optimization pipeline
        let result = self.run_passes(&mut cfg, &mut instructions);

        // Filter out dead/nop instructions
        let live_instructions: Vec<Instruction> = instructions
            .into_iter()
            .filter(|i| !i.is_dead && i.opcode != Opcode::Nop)
            .collect();

        Ok((live_instructions, cfg, OptimizationStats {
            removed: result.removed_count,
            modified: result.modified_count,
            added: result.added_count,
            passes_run: self.count_enabled_passes(),
        }))
    }

    /// Count how many passes are enabled
    fn count_enabled_passes(&self) -> usize {
        let mut count = 0;
        if self.config.enable_peephole { count += 1; }
        if self.config.enable_constant_folding { count += 1; }
        if self.config.enable_algebraic { count += 1; }
        if self.config.enable_cse { count += 1; }
        if self.config.enable_dce { count += 1; }
        count
    }

    /// Run optimization passes on the given instructions
    fn run_passes(&self, cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        let mut manager = PassManager::new().with_max_iterations(self.config.max_iterations);

        if self.config.enable_peephole {
            let pass = if self.config.verbose {
                PeepholeOptimization::new().with_verbose()
            } else {
                PeepholeOptimization::new()
            };
            manager = manager.add_pass(pass);
        }

        if self.config.enable_constant_folding {
            let pass = if self.config.verbose {
                ConstantFolding::new().with_verbose()
            } else {
                ConstantFolding::new()
            };
            manager = manager.add_pass(pass);
        }

        if self.config.enable_algebraic {
            let pass = if self.config.verbose {
                AlgebraicSimplification::new().with_verbose()
            } else {
                AlgebraicSimplification::new()
            };
            manager = manager.add_pass(pass);
        }

        if self.config.enable_cse {
            let pass = if self.config.verbose {
                CommonSubexpressionElimination::new().with_verbose()
            } else {
                CommonSubexpressionElimination::new()
            };
            manager = manager.add_pass(pass);
        }

        if self.config.enable_dce {
            let pass = if self.config.verbose {
                DeadCodeElimination::new().with_verbose()
            } else {
                DeadCodeElimination::new()
            };
            manager = manager.add_pass(pass);
        }

        manager.run(cfg, instructions)
    }

    /// Optimize WASM operation sequence (legacy - returns only stats)
    pub fn optimize(&self, wasm_ops: &[WasmOp]) -> Result<OptimizationStats> {
        if wasm_ops.is_empty() {
            return Ok(OptimizationStats::default());
        }

        // Preprocess and convert to IR
        let preprocessed = self.preprocess_wasm_ops(wasm_ops);
        let (mut instructions, mut cfg) = self.wasm_to_ir(&preprocessed);
        let result = self.run_passes(&mut cfg, &mut instructions);

        Ok(OptimizationStats {
            removed: result.removed_count,
            modified: result.modified_count,
            added: result.added_count,
            passes_run: self.count_enabled_passes(),
        })
    }

    /// Get the current configuration
    pub fn config(&self) -> &OptimizationConfig {
        &self.config
    }

    /// Convert optimized IR instructions back to ARM instructions
    ///
    /// This function maps the register-based optimizer IR to ARM instructions.
    /// For function parameters, local indices 0..num_params map to R0..R3 per AAPCS.
    pub fn ir_to_arm(&self, instructions: &[Instruction], num_params: usize) -> Vec<ArmOp> {
        use crate::rules::{ArmOp, Operand2, Reg};
        use std::collections::HashMap;

        let mut arm_instrs = Vec::new();
        let mut vreg_to_arm: HashMap<u32, Reg> = HashMap::new();

        // For branch resolution: map IR instruction index -> ARM instruction index
        let mut ir_to_arm_idx: HashMap<usize, usize> = HashMap::new();
        // Track pending branches: (arm_instr_idx, target_ir_idx)
        let mut pending_branches: Vec<(usize, usize, bool)> = Vec::new();

        // Map local indices to ARM registers for params
        // AAPCS: first 4 params in R0-R3
        let param_regs = [Reg::R0, Reg::R1, Reg::R2, Reg::R3];

        // Track which ARM register currently holds each local variable
        // This avoids stack spills for simple cases
        let mut local_to_reg: HashMap<u32, Reg> = HashMap::new();
        // Registers available for locals (callee-saved)
        let local_regs = [Reg::R4, Reg::R5, Reg::R6, Reg::R7];
        // Track vregs that have been consumed and can be freed
        // This enables register reuse after values are no longer needed
        let mut dead_vregs: std::collections::HashSet<u32> = std::collections::HashSet::new();
        // Track vregs that correspond to local variables (shouldn't be marked dead after use)
        let mut local_vregs: std::collections::HashSet<u32> = std::collections::HashSet::new();

        // Track the last value-producing vreg (for function return value)
        let mut last_result_vreg: Option<u32> = None;
        // Track whether the last result is an i64 (result already in R0:R1, no move needed)
        let mut is_i64_result = false;
        // WASM operand value stack - tracks vreg IDs for correct stack semantics
        // Used to restore last_result_vreg after br_if pops its condition
        let mut value_stack: Vec<u32> = Vec::new();

        // Helper to get ARM reg from virtual reg
        let get_arm_reg = |vreg: &OptReg, map: &HashMap<u32, Reg>| -> Reg {
            map.get(&vreg.0).copied().unwrap_or(Reg::R0)
        };

        // First pass: map Load instructions (local.get) to ARM registers
        for inst in instructions {
            if let Opcode::Load { dest, addr } = &inst.opcode {
                // If this is loading a function parameter (local.get N where N < num_params)
                if (*addr as usize) < num_params && (*addr as usize) < 4 {
                    // Map this virtual register to the ARM register holding the param
                    vreg_to_arm.insert(dest.0, param_regs[*addr as usize]);
                } else {
                    // For non-param locals, allocate a temp register
                    // Simple strategy: use R4+ for non-param locals
                    let temp_regs = [Reg::R4, Reg::R5, Reg::R6, Reg::R7];
                    let idx = vreg_to_arm.len().saturating_sub(num_params);
                    if idx < temp_regs.len() {
                        vreg_to_arm.insert(dest.0, temp_regs[idx]);
                    }
                }
            }
        }

        // Second pass: generate ARM instructions
        for inst in instructions {
            match &inst.opcode {
                Opcode::Nop => continue,

                // Load for params: no instruction needed, value is already in register
                Opcode::Load { dest, addr } if (*addr as usize) < num_params => {
                    // Value is already in param register, just record the mapping
                    if (*addr as usize) < 4 {
                        vreg_to_arm.insert(dest.0, param_regs[*addr as usize]);
                    }
                    // Mark as local vreg (shouldn't be freed after use)
                    local_vregs.insert(dest.0);
                    // Track as potential return value
                    last_result_vreg = Some(dest.0);
                }

                // Load for non-param locals: use tracked register or allocate one
                Opcode::Load { dest, addr } => {
                    // Check if we have this local in a register
                    if let Some(&src_reg) = local_to_reg.get(addr) {
                        // Local is already in a register, just track the mapping
                        vreg_to_arm.insert(dest.0, src_reg);
                    } else {
                        // Allocate a register for this local
                        let local_idx = (*addr as usize).saturating_sub(num_params);
                        let rd = if local_idx < local_regs.len() {
                            local_regs[local_idx]
                        } else {
                            Reg::R4
                        };
                        vreg_to_arm.insert(dest.0, rd);
                        local_to_reg.insert(*addr, rd);
                    }
                    // Mark as local vreg (shouldn't be freed after use)
                    local_vregs.insert(dest.0);
                    // Track as potential return value
                    last_result_vreg = Some(dest.0);
                }

                // Store: write to local variable
                Opcode::Store { src, addr } => {
                    let rs = get_arm_reg(src, &vreg_to_arm);
                    // Track which register holds this local's value
                    // Special case: synthetic local 255 is used for preserving conditions
                    // across nested selects - use R11 which is rarely used elsewhere
                    if *addr == 255 {
                        let local_reg = Reg::R11;
                        if rs != local_reg {
                            arm_instrs.push(ArmOp::Mov { rd: local_reg, op2: Operand2::Reg(rs) });
                        }
                        local_to_reg.insert(*addr, local_reg);
                    } else if (*addr as usize) >= num_params {
                        // For non-param locals, we keep the value in a dedicated register
                        let local_idx = (*addr as usize).saturating_sub(num_params);
                        let local_reg = if local_idx < local_regs.len() {
                            local_regs[local_idx]
                        } else {
                            Reg::R4
                        };
                        // Move value to the local's register if not already there
                        if rs != local_reg {
                            arm_instrs.push(ArmOp::Mov { rd: local_reg, op2: Operand2::Reg(rs) });
                        }
                        local_to_reg.insert(*addr, local_reg);
                    }
                    // For param locals (addr < num_params), value stays in param register
                    // Mark source vreg as dead (unless it's a local vreg)
                    if !local_vregs.contains(&src.0) {
                        dead_vregs.insert(src.0);
                    }
                }

                // Constant: mov immediate to register
                Opcode::Const { dest, value } => {
                    // Allocate a register for this constant
                    let rd = if let Some(&r) = vreg_to_arm.get(&dest.0) {
                        r
                    } else {
                        // Find next available temp register
                        // Exclude live vregs (not dead) and local_to_reg to avoid clobbering
                        let used: Vec<_> = vreg_to_arm.iter()
                            .filter(|(k, _)| !dead_vregs.contains(k))
                            .map(|(_, v)| *v)
                            .chain(local_to_reg.values().copied())
                            .collect();
                        // Expanded temp register pool: R4-R11 (callee-saved) plus R3
                        // Note: R0-R2 are reserved for params/return, R12 is IP, R13 is SP, R14 is LR, R15 is PC
                        let temp_regs = [Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::R9, Reg::R10, Reg::R11, Reg::R3];
                        let rd = temp_regs.iter().find(|r| !used.contains(r)).copied()
                            .expect("Register allocation exhausted - too many live values");
                        vreg_to_arm.insert(dest.0, rd);
                        rd
                    };
                    // For 32-bit values outside 16-bit range, use MOVW + MOVT
                    // ARM Thumb MOVW only handles 0-65535, so -1 (0xFFFFFFFF) needs both
                    let val_u32 = *value as u32;
                    if val_u32 > 0xFFFF {
                        // Need MOVW (lower 16) + MOVT (upper 16) for full 32-bit value
                        let lo = (val_u32 & 0xFFFF) as u16;
                        let hi = ((val_u32 >> 16) & 0xFFFF) as u16;
                        arm_instrs.push(ArmOp::Movw { rd, imm16: lo });
                        arm_instrs.push(ArmOp::Movt { rd, imm16: hi });
                    } else {
                        arm_instrs.push(ArmOp::Mov { rd, op2: Operand2::Imm(*value) });
                    }
                }

                // Arithmetic operations
                // Use a temp register (R8) for intermediate results to avoid clobbering params
                // The final return value will be moved to R0 at function end
                Opcode::Add { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    // Use R8 for intermediate results to preserve params in R0-R3
                    let rd = Reg::R3;
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Add { rd, rn, op2: Operand2::Reg(rm) });
                    last_result_vreg = Some(dest.0);
                    // Mark source vregs as dead (unless they're local vregs)
                    if !local_vregs.contains(&src1.0) { dead_vregs.insert(src1.0); }
                    if !local_vregs.contains(&src2.0) { dead_vregs.insert(src2.0); }
                }

                Opcode::Sub { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    let rd = Reg::R3;
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Sub { rd, rn, op2: Operand2::Reg(rm) });
                    last_result_vreg = Some(dest.0);
                    if !local_vregs.contains(&src1.0) { dead_vregs.insert(src1.0); }
                    if !local_vregs.contains(&src2.0) { dead_vregs.insert(src2.0); }
                }

                Opcode::Mul { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    let rd = Reg::R3;
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Mul { rd, rn, rm });
                    last_result_vreg = Some(dest.0);
                    if !local_vregs.contains(&src1.0) { dead_vregs.insert(src1.0); }
                    if !local_vregs.contains(&src2.0) { dead_vregs.insert(src2.0); }
                }

                Opcode::DivS { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    let rd = Reg::R3;
                    vreg_to_arm.insert(dest.0, rd);

                    // Trap check 1: divide by zero
                    arm_instrs.push(ArmOp::Cmp { rn: rm, op2: Operand2::Imm(0) });
                    arm_instrs.push(ArmOp::BCondOffset { cond: Condition::NE, offset: 0 });
                    arm_instrs.push(ArmOp::Udf { imm: 0 });

                    // Trap check 2: signed overflow (INT_MIN / -1)
                    // Load INT_MIN (0x80000000) into R12
                    arm_instrs.push(ArmOp::Movw { rd: Reg::R12, imm16: 0 });
                    arm_instrs.push(ArmOp::Movt { rd: Reg::R12, imm16: 0x8000 });
                    // CMP dividend, INT_MIN
                    arm_instrs.push(ArmOp::Cmp { rn, op2: Operand2::Reg(Reg::R12) });
                    // BNE.N +3 (skip overflow check if dividend != INT_MIN)
                    // Skip 8 bytes: CMN.W(4) + BNE(2) + UDF(2)
                    // Branch target = PC + (imm8 << 1) = B+4 + 6 = B+10 (SDIV)
                    arm_instrs.push(ArmOp::BCondOffset { cond: Condition::NE, offset: 3 });
                    // CMN divisor, #1 (check if divisor == -1: -1 + 1 = 0 sets Z flag)
                    // CMN.W is 4 bytes
                    arm_instrs.push(ArmOp::Cmn { rn: rm, op2: Operand2::Imm(1) });
                    // BNE.N +0 (skip UDF if divisor != -1)
                    arm_instrs.push(ArmOp::BCondOffset { cond: Condition::NE, offset: 0 });
                    // UDF #1 (trap on overflow)
                    arm_instrs.push(ArmOp::Udf { imm: 1 });

                    arm_instrs.push(ArmOp::Sdiv { rd, rn, rm });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::DivU { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    let rd = Reg::R0;
                    vreg_to_arm.insert(dest.0, rd);

                    // Trap check: divide by zero
                    arm_instrs.push(ArmOp::Cmp { rn: rm, op2: Operand2::Imm(0) });
                    arm_instrs.push(ArmOp::BCondOffset { cond: Condition::NE, offset: 0 });
                    arm_instrs.push(ArmOp::Udf { imm: 0 });

                    arm_instrs.push(ArmOp::Udiv { rd, rn, rm });
                    last_result_vreg = Some(dest.0);
                }

                // Remainder: rd = rn - (rn / rm) * rm
                Opcode::RemS { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    let rd = Reg::R0;
                    vreg_to_arm.insert(dest.0, rd);

                    // Trap check: divide by zero (rem_s doesn't trap on INT_MIN % -1)
                    arm_instrs.push(ArmOp::Cmp { rn: rm, op2: Operand2::Imm(0) });
                    arm_instrs.push(ArmOp::BCondOffset { cond: Condition::NE, offset: 0 });
                    arm_instrs.push(ArmOp::Udf { imm: 0 });

                    // Use MLS: rd = ra - rn * rm, where ra = dividend, result of div in temp
                    arm_instrs.push(ArmOp::Sdiv { rd: Reg::R12, rn, rm }); // R12 = rn / rm
                    arm_instrs.push(ArmOp::Mls { rd, rn: Reg::R12, rm, ra: rn }); // rd = rn - R12 * rm
                    last_result_vreg = Some(dest.0);
                }

                Opcode::RemU { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    let rd = Reg::R0;
                    vreg_to_arm.insert(dest.0, rd);

                    // Trap check: divide by zero
                    arm_instrs.push(ArmOp::Cmp { rn: rm, op2: Operand2::Imm(0) });
                    arm_instrs.push(ArmOp::BCondOffset { cond: Condition::NE, offset: 0 });
                    arm_instrs.push(ArmOp::Udf { imm: 0 });

                    arm_instrs.push(ArmOp::Udiv { rd: Reg::R12, rn, rm });
                    arm_instrs.push(ArmOp::Mls { rd, rn: Reg::R12, rm, ra: rn });
                    last_result_vreg = Some(dest.0);
                }

                // Bitwise operations
                Opcode::And { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    let rd = Reg::R0;
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::And { rd, rn, op2: Operand2::Reg(rm) });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Or { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    // Use R3 as temp to avoid clobbering R0 (param register)
                    let rd = Reg::R3;
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Orr { rd, rn, op2: Operand2::Reg(rm) });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Xor { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    // Use R3 as temp to avoid clobbering R0 (param register)
                    let rd = Reg::R3;
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Eor { rd, rn, op2: Operand2::Reg(rm) });
                    last_result_vreg = Some(dest.0);
                }

                // Shifts - WASM spec: shift amount masked to 5 bits (& 31)
                // ARM LSL/LSR/ASR by register use low byte, so shift >= 32
                // produces 0 (not wrapping). We must mask first.
                Opcode::Shl { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    let rd = Reg::R3;
                    vreg_to_arm.insert(dest.0, rd);
                    // Mask shift amount: R12 = rm & 31
                    arm_instrs.push(ArmOp::And { rd: Reg::R12, rn: rm, op2: Operand2::Imm(31) });
                    arm_instrs.push(ArmOp::LslReg { rd, rn, rm: Reg::R12 });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::ShrS { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    let rd = Reg::R3;
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::And { rd: Reg::R12, rn: rm, op2: Operand2::Imm(31) });
                    arm_instrs.push(ArmOp::AsrReg { rd, rn, rm: Reg::R12 });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::ShrU { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    let rd = Reg::R3;
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::And { rd: Reg::R12, rn: rm, op2: Operand2::Imm(31) });
                    arm_instrs.push(ArmOp::LsrReg { rd, rn, rm: Reg::R12 });
                    last_result_vreg = Some(dest.0);
                }

                // Rotate right: WASM masks to 5 bits, ARM ROR by register
                // uses low byte (ROR by 32 = no-op on ARM, but WASM wants same)
                // Actually ROR wraps naturally, but we mask for consistency
                Opcode::Rotr { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    let rd = Reg::R3;
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::And { rd: Reg::R12, rn: rm, op2: Operand2::Imm(31) });
                    arm_instrs.push(ArmOp::RorReg { rd, rn, rm: Reg::R12 });
                    last_result_vreg = Some(dest.0);
                }

                // Rotate left: ROTL(x, n) = ROR(x, 32 - (n & 31))
                // Emit: AND R12, Rm, #31; RSB R12, R12, #32; ROR.W Rd, Rn, R12
                Opcode::Rotl { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    let rd = Reg::R3;
                    vreg_to_arm.insert(dest.0, rd);
                    // R12 = rm & 31
                    arm_instrs.push(ArmOp::And { rd: Reg::R12, rn: rm, op2: Operand2::Imm(31) });
                    // R12 = 32 - R12
                    arm_instrs.push(ArmOp::Rsb { rd: Reg::R12, rn: Reg::R12, imm: 32 });
                    // rd = ROR(rn, R12)
                    arm_instrs.push(ArmOp::RorReg { rd, rn, rm: Reg::R12 });
                    last_result_vreg = Some(dest.0);
                }

                // Bit count operations (unary)
                Opcode::Clz { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm);
                    let rd = Reg::R0;
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Clz { rd, rm });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Ctz { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm);
                    let rd = Reg::R0;
                    vreg_to_arm.insert(dest.0, rd);
                    // CTZ = CLZ(RBIT(x)) - reverse bits, then count leading zeros
                    arm_instrs.push(ArmOp::Rbit { rd, rm });
                    arm_instrs.push(ArmOp::Clz { rd, rm: rd });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Popcnt { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm);
                    let rd = Reg::R0;
                    vreg_to_arm.insert(dest.0, rd);
                    // Popcnt - no direct instruction, use Popcnt pseudo-op
                    arm_instrs.push(ArmOp::Popcnt { rd, rm });
                    last_result_vreg = Some(dest.0);
                }

                // Sign extension operations (unary)
                Opcode::Extend8S { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm);
                    let rd = Reg::R0;
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Sxtb { rd, rm });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Extend16S { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm);
                    let rd = Reg::R0;
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Sxth { rd, rm });
                    last_result_vreg = Some(dest.0);
                }

                // Eqz - compare with zero (unary)
                Opcode::Eqz { dest, src } => {
                    let rn = get_arm_reg(src, &vreg_to_arm);
                    let rd = Reg::R0;
                    vreg_to_arm.insert(dest.0, rd);

                    // CMP rn, #0; SetCond rd, EQ
                    arm_instrs.push(ArmOp::Cmp { rn, op2: Operand2::Imm(0) });
                    arm_instrs.push(ArmOp::SetCond { rd, cond: crate::rules::Condition::EQ });
                    last_result_vreg = Some(dest.0);
                }

                // Comparisons - set result to 0 or 1
                Opcode::Eq { dest, src1, src2 } |
                Opcode::Ne { dest, src1, src2 } |
                Opcode::LtS { dest, src1, src2 } |
                Opcode::LtU { dest, src1, src2 } |
                Opcode::LeS { dest, src1, src2 } |
                Opcode::LeU { dest, src1, src2 } |
                Opcode::GtS { dest, src1, src2 } |
                Opcode::GtU { dest, src1, src2 } |
                Opcode::GeS { dest, src1, src2 } |
                Opcode::GeU { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm);
                    let rm = get_arm_reg(src2, &vreg_to_arm);
                    // Use R7 for comparison results to avoid clobbering R0
                    // R0 is needed for return values in loops
                    // Note: R7 must be used (not R12) because 16-bit MOV can only address R0-R7
                    let rd = Reg::R7;
                    vreg_to_arm.insert(dest.0, rd);

                    let cond = match &inst.opcode {
                        Opcode::Eq { .. } => crate::rules::Condition::EQ,
                        Opcode::Ne { .. } => crate::rules::Condition::NE,
                        Opcode::LtS { .. } => crate::rules::Condition::LT,
                        Opcode::LtU { .. } => crate::rules::Condition::LO,
                        Opcode::LeS { .. } => crate::rules::Condition::LE,
                        Opcode::LeU { .. } => crate::rules::Condition::LS,
                        Opcode::GtS { .. } => crate::rules::Condition::GT,
                        Opcode::GtU { .. } => crate::rules::Condition::HI,
                        Opcode::GeS { .. } => crate::rules::Condition::GE,
                        Opcode::GeU { .. } => crate::rules::Condition::HS,
                        _ => crate::rules::Condition::EQ,
                    };

                    arm_instrs.push(ArmOp::Cmp { rn, op2: Operand2::Reg(rm) });
                    arm_instrs.push(ArmOp::SetCond { rd, cond });
                    // Track comparison result as potential return value
                    last_result_vreg = Some(dest.0);
                }

                // Control flow
                Opcode::Branch { target } => {
                    // Record this branch for later resolution
                    pending_branches.push((arm_instrs.len(), *target, false));
                    // Emit placeholder - will be patched later
                    arm_instrs.push(ArmOp::BOffset { offset: 0 });
                }

                Opcode::CondBranch { cond, target } => {
                    let rcond = get_arm_reg(cond, &vreg_to_arm);
                    arm_instrs.push(ArmOp::Cmp { rn: rcond, op2: Operand2::Imm(0) });
                    // Record this branch for later resolution
                    pending_branches.push((arm_instrs.len(), *target, true));
                    // Emit placeholder conditional branch (branch if NOT equal to zero)
                    arm_instrs.push(ArmOp::BCondOffset {
                        cond: crate::rules::Condition::NE,
                        offset: 0,
                    });
                }

                Opcode::Return { value } => {
                    if let Some(v) = value {
                        let rv = get_arm_reg(v, &vreg_to_arm);
                        if rv != Reg::R0 {
                            arm_instrs.push(ArmOp::Mov { rd: Reg::R0, op2: Operand2::Reg(rv) });
                        }
                    }
                    arm_instrs.push(ArmOp::Bx { rm: Reg::LR });
                }

                // Select: dest = cond != 0 ? val_true : val_false
                // Implementation: CMP cond, #0; IT EQ; MOVEQ dest, val_false
                // (if cond==0, move val_false to dest; otherwise val_true is already in position)
                Opcode::Select { dest, val_true, val_false, cond } => {
                    let r_cond = get_arm_reg(cond, &vreg_to_arm);
                    let r_true = get_arm_reg(val_true, &vreg_to_arm);
                    let r_false = get_arm_reg(val_false, &vreg_to_arm);

                    // Use R3 as result to avoid clobbering R0 (may hold param)
                    // Final return value will be moved to R0 at function end
                    let rd = Reg::R3;
                    vreg_to_arm.insert(dest.0, rd);

                    // CRITICAL: If condition is in rd and we need to move val_true to rd,
                    // we must save the condition first to avoid clobbering it
                    let actual_cond = if r_cond == rd && r_true != rd {
                        // Save condition to R12 (IP) before overwriting rd
                        arm_instrs.push(ArmOp::Mov { rd: Reg::R12, op2: Operand2::Reg(r_cond) });
                        Reg::R12
                    } else {
                        r_cond
                    };

                    // Move val_true to result (it will be overwritten if cond==0)
                    if r_true != rd {
                        arm_instrs.push(ArmOp::Mov { rd, op2: Operand2::Reg(r_true) });
                    }

                    // Compare condition with 0
                    arm_instrs.push(ArmOp::Cmp { rn: actual_cond, op2: Operand2::Imm(0) });

                    // If cond == 0, overwrite with val_false using conditional move
                    arm_instrs.push(ArmOp::SelectMove {
                        rd,
                        rm: r_false,
                        cond: crate::rules::Condition::EQ,
                    });

                    // Track Select result as the function return value
                    last_result_vreg = Some(dest.0);
                }

                // i64 operations (register pairs on 32-bit ARM)
                // Per AAPCS: i64 params in R0:R1 and R2:R3, result in R0:R1

                // I64Load: load an i64 parameter from local index
                // For i64 params on 32-bit ARM:
                // - Param 0 (i64) is in R0:R1
                // - Param 1 (i64) is in R2:R3
                Opcode::I64Load { dest_lo, dest_hi, addr } => {
                    // Map local index to register pair
                    // Per AAPCS: i64 uses consecutive even/odd register pairs
                    let (lo_reg, hi_reg) = if *addr == 0 {
                        (Reg::R0, Reg::R1) // First i64 param
                    } else if *addr == 1 {
                        (Reg::R2, Reg::R3) // Second i64 param
                    } else {
                        // For other locals, we'd need stack access
                        // For now, use R4:R5 as temp
                        (Reg::R4, Reg::R5)
                    };
                    vreg_to_arm.insert(dest_lo.0, lo_reg);
                    vreg_to_arm.insert(dest_hi.0, hi_reg);
                    // No ARM instructions needed - values are already in registers for params
                    last_result_vreg = Some(dest_lo.0);
                }

                Opcode::I64Const { dest_lo, dest_hi, value } => {
                    // Load 64-bit constant into register pair
                    let lo = (*value & 0xFFFFFFFF) as u32;
                    let hi = ((*value >> 32) & 0xFFFFFFFF) as u32;
                    // Choose register pair based on virtual register number
                    // If dest_lo.0 is 0 or 1, use R0:R1 (first i64 slot)
                    // If dest_lo.0 is 2 or 3, use R2:R3 (second i64 slot)
                    let (lo_reg, hi_reg) = if dest_lo.0 <= 1 {
                        (Reg::R0, Reg::R1)
                    } else {
                        (Reg::R2, Reg::R3)
                    };
                    vreg_to_arm.insert(dest_lo.0, lo_reg);
                    vreg_to_arm.insert(dest_hi.0, hi_reg);
                    // Load low word
                    if lo <= 255 {
                        arm_instrs.push(ArmOp::Mov { rd: lo_reg, op2: Operand2::Imm(lo as i32) });
                    } else {
                        arm_instrs.push(ArmOp::Movw { rd: lo_reg, imm16: (lo & 0xFFFF) as u16 });
                        if lo > 0xFFFF {
                            arm_instrs.push(ArmOp::Movt { rd: lo_reg, imm16: ((lo >> 16) & 0xFFFF) as u16 });
                        }
                    }
                    // Load high word
                    if hi <= 255 {
                        arm_instrs.push(ArmOp::Mov { rd: hi_reg, op2: Operand2::Imm(hi as i32) });
                    } else {
                        arm_instrs.push(ArmOp::Movw { rd: hi_reg, imm16: (hi & 0xFFFF) as u16 });
                        if hi > 0xFFFF {
                            arm_instrs.push(ArmOp::Movt { rd: hi_reg, imm16: ((hi >> 16) & 0xFFFF) as u16 });
                        }
                    }
                }

                Opcode::I64Add { dest_lo, dest_hi, .. } => {
                    // i64.add: R0:R1 = R0:R1 + R2:R3
                    // ADDS R0, R0, R2 (sets carry)
                    // ADC  R1, R1, R3 (adds carry)
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::Adds { rd: Reg::R0, rn: Reg::R0, op2: Operand2::Reg(Reg::R2) });
                    arm_instrs.push(ArmOp::Adc { rd: Reg::R1, rn: Reg::R1, op2: Operand2::Reg(Reg::R3) });
                    // Mark as i64 result - no final mov needed, result already in R0:R1
                    is_i64_result = true;
                }

                Opcode::I64Sub { dest_lo, dest_hi, .. } => {
                    // i64.sub: R0:R1 = R0:R1 - R2:R3
                    // SUBS R0, R0, R2 (sets borrow)
                    // SBC  R1, R1, R3 (subtracts borrow)
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::Subs { rd: Reg::R0, rn: Reg::R0, op2: Operand2::Reg(Reg::R2) });
                    arm_instrs.push(ArmOp::Sbc { rd: Reg::R1, rn: Reg::R1, op2: Operand2::Reg(Reg::R3) });
                    // Mark as i64 result - no final mov needed, result already in R0:R1
                    is_i64_result = true;
                }

                Opcode::I64And { dest_lo, dest_hi, .. } => {
                    // i64.and: R0:R1 = R0:R1 & R2:R3
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::And { rd: Reg::R0, rn: Reg::R0, op2: Operand2::Reg(Reg::R2) });
                    arm_instrs.push(ArmOp::And { rd: Reg::R1, rn: Reg::R1, op2: Operand2::Reg(Reg::R3) });
                    // Mark as i64 result - no final mov needed, result already in R0:R1
                    is_i64_result = true;
                }

                Opcode::I64Or { dest_lo, dest_hi, .. } => {
                    // i64.or: R0:R1 = R0:R1 | R2:R3
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::Orr { rd: Reg::R0, rn: Reg::R0, op2: Operand2::Reg(Reg::R2) });
                    arm_instrs.push(ArmOp::Orr { rd: Reg::R1, rn: Reg::R1, op2: Operand2::Reg(Reg::R3) });
                    // Mark as i64 result - no final mov needed, result already in R0:R1
                    is_i64_result = true;
                }

                Opcode::I64Xor { dest_lo, dest_hi, .. } => {
                    // i64.xor: R0:R1 = R0:R1 ^ R2:R3
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::Eor { rd: Reg::R0, rn: Reg::R0, op2: Operand2::Reg(Reg::R2) });
                    arm_instrs.push(ArmOp::Eor { rd: Reg::R1, rn: Reg::R1, op2: Operand2::Reg(Reg::R3) });
                    // Mark as i64 result - no final mov needed, result already in R0:R1
                    is_i64_result = true;
                }

                // ========================================================================
                // i64 Comparisons (result is single i32 in R0)
                // ========================================================================

                Opcode::I64Eq { dest, .. } => {
                    // i64.eq: (R0:R1) == (R2:R3), result in R0
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd: Reg::R0,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                        cond: Condition::EQ,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64Ne { dest, .. } => {
                    // i64.ne: (R0:R1) != (R2:R3), result in R0
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd: Reg::R0,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                        cond: Condition::NE,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64LtS { dest, .. } => {
                    // i64.lt_s: (R0:R1) < (R2:R3) signed, result in R0
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd: Reg::R0,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                        cond: Condition::LT,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64GtS { dest, .. } => {
                    // i64.gt_s: (R0:R1) > (R2:R3) signed, result in R0
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd: Reg::R0,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                        cond: Condition::GT,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64LeS { dest, .. } => {
                    // i64.le_s: (R0:R1) <= (R2:R3) signed, result in R0
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd: Reg::R0,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                        cond: Condition::LE,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64GeS { dest, .. } => {
                    // i64.ge_s: (R0:R1) >= (R2:R3) signed, result in R0
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd: Reg::R0,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                        cond: Condition::GE,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Unsigned i64 comparisons
                Opcode::I64LtU { dest, .. } => {
                    // i64.lt_u: (R0:R1) < (R2:R3) unsigned, result in R0
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd: Reg::R0,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                        cond: Condition::LO,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64GtU { dest, .. } => {
                    // i64.gt_u: (R0:R1) > (R2:R3) unsigned, result in R0
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd: Reg::R0,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                        cond: Condition::HI,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64LeU { dest, .. } => {
                    // i64.le_u: (R0:R1) <= (R2:R3) unsigned, result in R0
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd: Reg::R0,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                        cond: Condition::LS,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64GeU { dest, .. } => {
                    // i64.ge_u: (R0:R1) >= (R2:R3) unsigned, result in R0
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd: Reg::R0,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                        cond: Condition::HS,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64Eqz { dest, .. } => {
                    // i64.eqz: (R0:R1) == 0, result in R0
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64SetCondZ {
                        rd: Reg::R0,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // i64 count leading zeros (returns i64 where high word is always 0)
                Opcode::I64Clz { dest, .. } => {
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64Clz {
                        rd: Reg::R0,
                        rnlo: Reg::R0, rnhi: Reg::R1,
                    });
                    last_result_vreg = Some(dest.0);
                    is_i64_result = true;
                }

                // i64 count trailing zeros (returns i64 where high word is always 0)
                Opcode::I64Ctz { dest, .. } => {
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64Ctz {
                        rd: Reg::R0,
                        rnlo: Reg::R0, rnhi: Reg::R1,
                    });
                    last_result_vreg = Some(dest.0);
                    is_i64_result = true;
                }

                // i64 population count (returns i64 where high word is always 0)
                Opcode::I64Popcnt { dest, .. } => {
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    arm_instrs.push(ArmOp::I64Popcnt {
                        rd: Reg::R0,
                        rnlo: Reg::R0, rnhi: Reg::R1,
                    });
                    last_result_vreg = Some(dest.0);
                    is_i64_result = true;
                }

                // i64 sign extension operations
                Opcode::I64Extend8S { dest_lo, dest_hi, .. } => {
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::I64Extend8S {
                        rdlo: Reg::R0, rdhi: Reg::R1,
                        rnlo: Reg::R0,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    is_i64_result = true;
                }

                Opcode::I64Extend16S { dest_lo, dest_hi, .. } => {
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::I64Extend16S {
                        rdlo: Reg::R0, rdhi: Reg::R1,
                        rnlo: Reg::R0,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    is_i64_result = true;
                }

                Opcode::I64Extend32S { dest_lo, dest_hi, .. } => {
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::I64Extend32S {
                        rdlo: Reg::R0, rdhi: Reg::R1,
                        rnlo: Reg::R0,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    is_i64_result = true;
                }

                // i64 multiply: UMULL + MLA cross products
                Opcode::I64Mul { dest_lo, dest_hi, .. } => {
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::I64Mul {
                        rd_lo: Reg::R0, rd_hi: Reg::R1,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                    });
                    is_i64_result = true;
                }

                // i64 shift left
                Opcode::I64Shl { dest_lo, dest_hi, .. } => {
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::I64Shl {
                        rd_lo: Reg::R0, rd_hi: Reg::R1,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                    });
                    is_i64_result = true;
                }

                // i64 arithmetic shift right
                Opcode::I64ShrS { dest_lo, dest_hi, .. } => {
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::I64ShrS {
                        rd_lo: Reg::R0, rd_hi: Reg::R1,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                    });
                    is_i64_result = true;
                }

                // i64 logical shift right
                Opcode::I64ShrU { dest_lo, dest_hi, .. } => {
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::I64ShrU {
                        rd_lo: Reg::R0, rd_hi: Reg::R1,
                        rn_lo: Reg::R0, rn_hi: Reg::R1,
                        rm_lo: Reg::R2, rm_hi: Reg::R3,
                    });
                    is_i64_result = true;
                }

                // i64 rotate left
                Opcode::I64Rotl { dest_lo, dest_hi, .. } => {
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::I64Rotl {
                        rdlo: Reg::R0, rdhi: Reg::R1,
                        rnlo: Reg::R0, rnhi: Reg::R1,
                        shift: Reg::R2, // Only use low word of shift amount
                    });
                    is_i64_result = true;
                }

                // i64 rotate right
                Opcode::I64Rotr { dest_lo, dest_hi, .. } => {
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::I64Rotr {
                        rdlo: Reg::R0, rdhi: Reg::R1,
                        rnlo: Reg::R0, rnhi: Reg::R1,
                        shift: Reg::R2, // Only use low word of shift amount
                    });
                    is_i64_result = true;
                }

                // i64 signed division
                Opcode::I64DivS { dest_lo, dest_hi, .. } => {
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::I64DivS {
                        rdlo: Reg::R0, rdhi: Reg::R1,
                        rnlo: Reg::R0, rnhi: Reg::R1,
                        rmlo: Reg::R2, rmhi: Reg::R3,
                    });
                    is_i64_result = true;
                }

                // i64 unsigned division
                Opcode::I64DivU { dest_lo, dest_hi, .. } => {
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::I64DivU {
                        rdlo: Reg::R0, rdhi: Reg::R1,
                        rnlo: Reg::R0, rnhi: Reg::R1,
                        rmlo: Reg::R2, rmhi: Reg::R3,
                    });
                    is_i64_result = true;
                }

                // i64 signed remainder
                Opcode::I64RemS { dest_lo, dest_hi, .. } => {
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::I64RemS {
                        rdlo: Reg::R0, rdhi: Reg::R1,
                        rnlo: Reg::R0, rnhi: Reg::R1,
                        rmlo: Reg::R2, rmhi: Reg::R3,
                    });
                    is_i64_result = true;
                }

                // i64 unsigned remainder
                Opcode::I64RemU { dest_lo, dest_hi, .. } => {
                    vreg_to_arm.insert(dest_lo.0, Reg::R0);
                    vreg_to_arm.insert(dest_hi.0, Reg::R1);
                    arm_instrs.push(ArmOp::I64RemU {
                        rdlo: Reg::R0, rdhi: Reg::R1,
                        rnlo: Reg::R0, rnhi: Reg::R1,
                        rmlo: Reg::R2, rmhi: Reg::R3,
                    });
                    is_i64_result = true;
                }

                // ========================================================================
                // Control Flow Operations (Loop Support)
                // ========================================================================

                // Label: marks a branch target position
                // Labels don't emit any code - they're just markers for branch offset calculation
                Opcode::Label { id } => {
                    // Record where this IR instruction maps to in ARM instructions
                    // The branch target is the NEXT ARM instruction to be emitted
                    ir_to_arm_idx.insert(*id, arm_instrs.len());
                    // No ARM instruction emitted for labels
                }

                // Copy: move value from src to dest (for local.tee semantics)
                Opcode::Copy { dest, src } => {
                    let rs = get_arm_reg(src, &vreg_to_arm);
                    let rd = Reg::R0;
                    vreg_to_arm.insert(dest.0, rd);
                    if rs != rd {
                        arm_instrs.push(ArmOp::Mov { rd, op2: Operand2::Reg(rs) });
                    }
                    last_result_vreg = Some(dest.0);
                }

                // TeeStore: Store to local AND keep value on stack (local.tee)
                Opcode::TeeStore { dest, src, addr } => {
                    let rs = get_arm_reg(src, &vreg_to_arm);

                    // For non-param locals, move to the local's dedicated register
                    if (*addr as usize) >= num_params {
                        let local_idx = (*addr as usize).saturating_sub(num_params);
                        let local_reg = if local_idx < local_regs.len() {
                            local_regs[local_idx]
                        } else {
                            Reg::R4
                        };
                        // Move value to the local's register if not already there
                        if rs != local_reg {
                            arm_instrs.push(ArmOp::Mov { rd: local_reg, op2: Operand2::Reg(rs) });
                        }
                        local_to_reg.insert(*addr, local_reg);
                        // The dest vreg now refers to the local's register
                        vreg_to_arm.insert(dest.0, local_reg);
                    } else {
                        // For param locals (local.tee to a param), move to param register
                        // This handles cases like modifying loop counter that was passed as param
                        let param_reg = if (*addr as usize) < 4 {
                            param_regs[*addr as usize]
                        } else {
                            Reg::R0
                        };
                        if rs != param_reg {
                            arm_instrs.push(ArmOp::Mov { rd: param_reg, op2: Operand2::Reg(rs) });
                        }
                        vreg_to_arm.insert(dest.0, param_reg);
                    }
                    // TeeStore produces a value that may be the function result
                    last_result_vreg = Some(dest.0);
                }

                // ========================================================================
                // Linear Memory Operations
                // ========================================================================

                // MemLoad: load 32-bit value from linear memory
                // Generates: MOVW R12, #base_lo; MOVT R12, #base_hi; ADD R12, R12, Raddr; LDR Rd, [R12, #offset]
                Opcode::MemLoad { dest, addr, offset } => {
                    let r_addr = get_arm_reg(addr, &vreg_to_arm);
                    let rd = Reg::R3;
                    vreg_to_arm.insert(dest.0, rd);

                    // Linear memory base address: 0x20000100 (in SRAM, above stack area)
                    let base: u32 = 0x20000100;
                    let base_lo = (base & 0xFFFF) as u16;
                    let base_hi = ((base >> 16) & 0xFFFF) as u16;

                    // Load base address into R12 (scratch register)
                    arm_instrs.push(ArmOp::Movw { rd: Reg::R12, imm16: base_lo });
                    arm_instrs.push(ArmOp::Movt { rd: Reg::R12, imm16: base_hi });
                    // Add WASM address offset
                    arm_instrs.push(ArmOp::Add { rd: Reg::R12, rn: Reg::R12, op2: Operand2::Reg(r_addr) });
                    // Load from [base + wasm_addr + static_offset]
                    arm_instrs.push(ArmOp::Ldr {
                        rd,
                        addr: crate::rules::MemAddr::imm(Reg::R12, *offset as i32),
                    });
                    last_result_vreg = Some(dest.0);
                }

                // MemStore: store 32-bit value to linear memory
                // Generates: MOVW R12, #base_lo; MOVT R12, #base_hi; ADD R12, R12, Raddr; STR Rsrc, [R12, #offset]
                Opcode::MemStore { src, addr, offset } => {
                    let r_addr = get_arm_reg(addr, &vreg_to_arm);
                    let r_src = get_arm_reg(src, &vreg_to_arm);

                    // Linear memory base address: 0x20000100 (in SRAM, above stack area)
                    let base: u32 = 0x20000100;
                    let base_lo = (base & 0xFFFF) as u16;
                    let base_hi = ((base >> 16) & 0xFFFF) as u16;

                    // Load base address into R12 (scratch register)
                    arm_instrs.push(ArmOp::Movw { rd: Reg::R12, imm16: base_lo });
                    arm_instrs.push(ArmOp::Movt { rd: Reg::R12, imm16: base_hi });
                    // Add WASM address offset
                    arm_instrs.push(ArmOp::Add { rd: Reg::R12, rn: Reg::R12, op2: Operand2::Reg(r_addr) });
                    // Store to [base + wasm_addr + static_offset]
                    arm_instrs.push(ArmOp::Str {
                        rd: r_src,
                        addr: crate::rules::MemAddr::imm(Reg::R12, *offset as i32),
                    });
                    // MemStore does not produce a value
                }
            }

            // Track WASM operand value stack for correct br_if semantics.
            // br_if pops the condition; the value underneath is the result.
            match &inst.opcode {
                // Binary ops: consume 2, produce 1
                Opcode::Add { dest, .. } | Opcode::Sub { dest, .. } | Opcode::Mul { dest, .. } |
                Opcode::DivS { dest, .. } | Opcode::DivU { dest, .. } |
                Opcode::RemS { dest, .. } | Opcode::RemU { dest, .. } |
                Opcode::And { dest, .. } | Opcode::Or { dest, .. } | Opcode::Xor { dest, .. } |
                Opcode::Shl { dest, .. } | Opcode::ShrS { dest, .. } | Opcode::ShrU { dest, .. } |
                Opcode::Rotl { dest, .. } | Opcode::Rotr { dest, .. } |
                Opcode::Eq { dest, .. } | Opcode::Ne { dest, .. } |
                Opcode::LtS { dest, .. } | Opcode::LtU { dest, .. } |
                Opcode::LeS { dest, .. } | Opcode::LeU { dest, .. } |
                Opcode::GtS { dest, .. } | Opcode::GtU { dest, .. } |
                Opcode::GeS { dest, .. } | Opcode::GeU { dest, .. } => {
                    value_stack.pop();
                    value_stack.pop();
                    value_stack.push(dest.0);
                }
                // Unary ops: consume 1, produce 1
                Opcode::Clz { dest, .. } | Opcode::Ctz { dest, .. } |
                Opcode::Popcnt { dest, .. } | Opcode::Eqz { dest, .. } |
                Opcode::Copy { dest, .. } |
                Opcode::Extend8S { dest, .. } | Opcode::Extend16S { dest, .. } => {
                    value_stack.pop();
                    value_stack.push(dest.0);
                }
                // MemLoad: consume 1 (addr), produce 1 (loaded value)
                Opcode::MemLoad { dest, .. } => {
                    value_stack.pop();
                    value_stack.push(dest.0);
                }
                // Value producers: push 1
                Opcode::Load { dest, .. } | Opcode::Const { dest, .. } => {
                    value_stack.push(dest.0);
                }
                // Store: consume 1
                Opcode::Store { .. } => {
                    value_stack.pop();
                }
                // MemStore: consume 2 (addr, value), produce 0
                Opcode::MemStore { .. } => {
                    value_stack.pop();
                    value_stack.pop();
                }
                // TeeStore: consume 1, produce 1 (value stays on stack)
                Opcode::TeeStore { dest, .. } => {
                    value_stack.pop();
                    value_stack.push(dest.0);
                }
                // CondBranch (br_if): pops condition, result is value underneath
                Opcode::CondBranch { .. } => {
                    value_stack.pop(); // pop condition
                    if let Some(&top) = value_stack.last() {
                        last_result_vreg = Some(top);
                    }
                }
                // Select: consume 3 (val1, val2, cond), produce 1
                Opcode::Select { dest, .. } => {
                    value_stack.pop();
                    value_stack.pop();
                    value_stack.pop();
                    value_stack.push(dest.0);
                }
                // Label, Branch, Nop, Return: no stack effect
                _ => {}
            }
        }

        // ========================================================================
        // Branch Resolution Pass: Patch branch offsets
        // ========================================================================
        // Calculate byte offsets for each instruction to handle variable-length
        // Thumb-2 encoding (SetCond = 6 bytes, most others = 2 bytes).

        // Helper to estimate instruction byte size
        // Must match the encoder's behavior for correct branch offset calculation
        // Helper to get register number
        let reg_num = |r: &Reg| -> u8 {
            match r {
                Reg::R0 => 0, Reg::R1 => 1, Reg::R2 => 2, Reg::R3 => 3,
                Reg::R4 => 4, Reg::R5 => 5, Reg::R6 => 6, Reg::R7 => 7,
                Reg::R8 => 8, Reg::R9 => 9, Reg::R10 => 10, Reg::R11 => 11,
                Reg::R12 => 12, Reg::SP => 13, Reg::LR => 14, Reg::PC => 15,
            }
        };

        let instr_byte_size = |op: &ArmOp| -> usize {
            match op {
                // SetCond: ITE + MOV #1 + MOV #0 = 2 + 2 + 2 = 6 bytes
                ArmOp::SetCond { .. } => 6,
                // SelectMove: IT + MOV = 2 + 2 = 4 bytes
                ArmOp::SelectMove { .. } => 4,
                // 32-bit Thumb-2 instructions (always 4 bytes)
                ArmOp::Movw { .. } | ArmOp::Movt { .. } => 4,
                // Register shifts and RSB are always 32-bit Thumb-2
                ArmOp::LslReg { .. } | ArmOp::LsrReg { .. } |
                ArmOp::AsrReg { .. } | ArmOp::RorReg { .. } |
                ArmOp::Rsb { .. } => 4,
                // MUL, MLS, SDIV, UDIV are always 32-bit Thumb-2
                ArmOp::Mul { .. } | ArmOp::Mls { .. } |
                ArmOp::Sdiv { .. } | ArmOp::Udiv { .. } => 4,
                // ADC, SBC are always 32-bit Thumb-2
                ArmOp::Adc { .. } | ArmOp::Sbc { .. } => 4,
                // CLZ, RBIT are always 32-bit Thumb-2
                ArmOp::Clz { .. } | ArmOp::Rbit { .. } => 4,
                // SXTB, SXTH can be 16-bit for low registers
                ArmOp::Sxtb { rd, rm } | ArmOp::Sxth { rd, rm } => {
                    let rd_bits = reg_num(rd);
                    let rm_bits = reg_num(rm);
                    if rd_bits < 8 && rm_bits < 8 { 2 } else { 4 }
                }
                // I64SetCond: multi-instruction sequence (12 bytes for all conditions)
                // EQ/NE: CMP(2) + IT EQ(2) + CMP(2) + ITE(2) + MOV(2) + MOV(2)
                // LT/GT: CMP(2) + SBCS(4) + ITE(2) + MOV(2) + MOV(2)
                ArmOp::I64SetCond { .. } => 12,
                // I64SetCondZ: ORR.W(4) + CMP(2) + ITE(2) + MOV(2) + MOV(2)
                ArmOp::I64SetCondZ { .. } => 12,
                // I64Mul: MUL(4) + MLA(4) + UMULL(4) + ADD(2) = 14 bytes
                ArmOp::I64Mul { .. } => 14,
                // I64Shl/ShrU: AND.W(4) + SUBS.W(4) + BPL(2) + small_block(22) + B(2) + large_block(6) - but byte_size = total = 38
                ArmOp::I64Shl { .. } | ArmOp::I64ShrU { .. } => 38,
                // I64ShrS: same as ShrU but large block is 8 bytes (ASR+ASR vs LSR+MOV) = 40
                ArmOp::I64ShrS { .. } => 40,
                // I64Rotl/Rotr: PUSH(2) + AND(4) + SUBS(4) + BPL(2) + small_block(30) + B(2) + large_block(30) + POP(2) = 74 bytes
                ArmOp::I64Rotl { .. } | ArmOp::I64Rotr { .. } => 74,
                // I64Clz: CMP.W(4) + BEQ(2) + CLZ.W(4) + B(2) + NOP(2) + CLZ.W(4) + ADD.W(4) + MOV(2) = 24 bytes
                ArmOp::I64Clz { .. } => 24,
                // I64Ctz: CMP.W(4) + BEQ(2) + RBIT.W(4) + CLZ.W(4) + B(2) + NOP(2) + RBIT.W(4) + CLZ.W(4) + ADD.W(4) + MOV(2) = 32 bytes
                ArmOp::I64Ctz { .. } => 32,
                // I64Popcnt: large implementation with PUSH/POP and duplicate algorithm for lo and hi = ~180 bytes
                ArmOp::I64Popcnt { .. } => 200,
                // I64 sign extension: SXTB/SXTH/ASR + ASR = 4-8 bytes
                ArmOp::I64Extend8S { .. } => 8,
                ArmOp::I64Extend16S { .. } => 8,
                ArmOp::I64Extend32S { .. } => 8,
                // I64 division: PUSH + init + loop body + MOV + POP = ~80-150 bytes
                ArmOp::I64DivU { .. } => 100,
                ArmOp::I64RemU { .. } => 100,
                // Signed versions have additional negation logic
                ArmOp::I64DivS { .. } => 150,
                ArmOp::I64RemS { .. } => 150,
                // AND/OR/XOR: encoder always uses 32-bit Thumb-2 (.W) encoding
                ArmOp::And { .. } | ArmOp::Orr { .. } | ArmOp::Eor { .. } => 4,
                // LDR/STR with high base register or large offset need 32-bit
                ArmOp::Ldr { rd, addr } => {
                    let rd_bits = reg_num(rd);
                    let base_bits = reg_num(&addr.base);
                    let offset = addr.offset as u32;
                    if rd_bits < 8 && base_bits < 8 && (offset & 0x3) == 0 && offset <= 124 { 2 } else { 4 }
                }
                ArmOp::Str { rd, addr } => {
                    let rd_bits = reg_num(rd);
                    let base_bits = reg_num(&addr.base);
                    let offset = addr.offset as u32;
                    if rd_bits < 8 && base_bits < 8 && (offset & 0x3) == 0 && offset <= 124 { 2 } else { 4 }
                }
                // BL is always 32-bit
                ArmOp::Bl { .. } => 4,
                // MOV with high register (R8-R15) or large immediate needs MOVW (4 bytes)
                ArmOp::Mov { rd, op2: Operand2::Imm(v) } => {
                    if reg_num(rd) > 7 || *v > 255 || *v < 0 { 4 } else { 2 }
                }
                // SUB/ADD with high registers need 32-bit encoding
                ArmOp::Sub { rd, rn, op2: Operand2::Reg(rm) } => {
                    if reg_num(rd) > 7 || reg_num(rn) > 7 || reg_num(rm) > 7 { 4 } else { 2 }
                }
                ArmOp::Add { rd, rn, op2: Operand2::Reg(rm) } => {
                    if reg_num(rd) > 7 || reg_num(rn) > 7 || reg_num(rm) > 7 { 4 } else { 2 }
                }
                // Most 16-bit Thumb instructions (MOV low, CMP low, B, etc.)
                _ => 2,
            }
        };

        // Build byte offset table: byte_offsets[i] = byte position of instruction i
        let mut byte_offsets: Vec<usize> = Vec::with_capacity(arm_instrs.len() + 1);
        let mut current_offset = 0usize;
        for op in &arm_instrs {
            byte_offsets.push(current_offset);
            current_offset += instr_byte_size(op);
        }
        byte_offsets.push(current_offset); // End marker for target lookups

        for (branch_arm_idx, target_ir_idx, is_conditional) in pending_branches {
            // Find where the target label is in ARM instructions
            if let Some(&target_arm_idx) = ir_to_arm_idx.get(&target_ir_idx) {
                // Calculate the Thumb branch displacement
                // Formula: imm8 = (target_addr - (branch_addr + 4)) / 2
                // This is because PC points to branch_addr + 4 during execution
                let branch_byte_pos = byte_offsets[branch_arm_idx] as i32;
                let target_byte_pos = byte_offsets[target_arm_idx] as i32;

                // Halfword offset is the raw encoded value for imm8
                let halfword_offset = (target_byte_pos - branch_byte_pos - 4) / 2;

                // Patch the branch instruction
                if is_conditional {
                    arm_instrs[branch_arm_idx] = ArmOp::BCondOffset {
                        cond: crate::rules::Condition::NE,
                        offset: halfword_offset,
                    };
                } else {
                    arm_instrs[branch_arm_idx] = ArmOp::BOffset { offset: halfword_offset };
                }
            }
        }

        // Ensure return value is in R0 (skip for i64 results which are already in R0:R1)
        if !is_i64_result {
            if let Some(result_vreg) = last_result_vreg {
                if let Some(&result_reg) = vreg_to_arm.get(&result_vreg) {
                    if result_reg != Reg::R0 {
                        arm_instrs.push(ArmOp::Mov { rd: Reg::R0, op2: Operand2::Reg(result_reg) });
                    }
                }
            }
        }

        // Add return if not present
        if arm_instrs.is_empty() || !matches!(arm_instrs.last(), Some(ArmOp::Bx { .. })) {
            arm_instrs.push(ArmOp::Bx { rm: Reg::LR });
        }

        arm_instrs
    }
}

impl Default for OptimizerBridge {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_optimizer_bridge_basic() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![WasmOp::I32Const(10), WasmOp::I32Const(20), WasmOp::I32Add];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Should have run optimizations
        assert!(stats.passes_run > 0);
    }

    #[test]
    fn test_optimizer_bridge_disabled() {
        let bridge = OptimizerBridge::with_config(OptimizationConfig::none());
        let wasm_ops = vec![WasmOp::I32Const(10), WasmOp::I32Const(20), WasmOp::I32Add];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // No passes should have run
        assert_eq!(stats.passes_run, 0);
    }

    #[test]
    fn test_optimizer_bridge_fast() {
        let bridge = OptimizerBridge::with_config(OptimizationConfig::fast());
        let wasm_ops = vec![
            WasmOp::I32Const(5),
            WasmOp::I32Const(0),
            WasmOp::I32Add, // Should be simplified to just 5
        ];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Fast config should run some passes
        assert!(stats.passes_run >= 3);
    }

    #[test]
    fn test_empty_wasm() {
        let bridge = OptimizerBridge::new();
        let stats = bridge.optimize(&[]).unwrap();

        assert_eq!(stats.removed, 0);
        assert_eq!(stats.modified, 0);
        assert_eq!(stats.added, 0);
    }

    #[test]
    fn test_wasm_division() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![WasmOp::I32Const(20), WasmOp::I32Const(4), WasmOp::I32DivS];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Should have run optimizations
        assert!(stats.passes_run > 0);
    }

    #[test]
    fn test_wasm_bitwise() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![
            WasmOp::I32Const(15),
            WasmOp::I32Const(7),
            WasmOp::I32And,
            WasmOp::I32Const(8),
            WasmOp::I32Or,
        ];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Should have run optimizations
        assert!(stats.passes_run > 0);
    }

    #[test]
    fn test_wasm_shifts() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![
            WasmOp::I32Const(1),
            WasmOp::I32Const(3),
            WasmOp::I32Shl, // 1 << 3 = 8
        ];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Should have run optimizations
        assert!(stats.passes_run > 0);
    }

    #[test]
    fn test_wasm_comparison() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![
            WasmOp::I32Const(10),
            WasmOp::I32Const(5),
            WasmOp::I32LtS, // 10 < 5 = 0
            WasmOp::I32Const(3),
            WasmOp::I32Const(7),
            WasmOp::I32GtU, // 3 > 7 = 0
        ];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Should have run optimizations
        assert!(stats.passes_run > 0);
    }

    #[test]
    fn test_wasm_complex_program() {
        let bridge = OptimizerBridge::with_config(OptimizationConfig::all());
        let wasm_ops = vec![
            // Compute (a & b) | (c << 2)
            WasmOp::LocalGet(0), // a
            WasmOp::LocalGet(1), // b
            WasmOp::I32And,      // a & b
            WasmOp::LocalGet(2), // c
            WasmOp::I32Const(2),
            WasmOp::I32Shl,      // c << 2
            WasmOp::I32Or,       // (a & b) | (c << 2)
            WasmOp::LocalSet(3), // store result
        ];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Should have run all passes
        assert_eq!(stats.passes_run, 5);
    }

    // ========================================================================
    // Branchless Control Flow Pattern Tests
    // ========================================================================

    #[test]
    fn test_simple_if_else_to_select() {
        let bridge = OptimizerBridge::new();

        // Pattern: cond, If, val1, Else, val2, End
        // Should become: val1, val2, cond, Select
        let wasm_ops = vec![
            WasmOp::LocalGet(0),   // condition
            WasmOp::If,
            WasmOp::I32Const(10),  // then value
            WasmOp::Else,
            WasmOp::I32Const(20),  // else value
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Should be transformed to: val1, val2, cond, Select
        assert_eq!(preprocessed.len(), 4);
        assert_eq!(preprocessed[0], WasmOp::I32Const(10));  // then value
        assert_eq!(preprocessed[1], WasmOp::I32Const(20));  // else value
        assert_eq!(preprocessed[2], WasmOp::LocalGet(0));   // condition
        assert_eq!(preprocessed[3], WasmOp::Select);
    }

    #[test]
    fn test_nested_if_else_to_nested_select() {
        let bridge = OptimizerBridge::new();

        // Pattern: outer_cond, If, inner_cond, If, val1, Else, val2, End, Else, val3, End
        // Should become two nested selects
        let wasm_ops = vec![
            WasmOp::LocalGet(0),   // outer condition
            WasmOp::If,
            WasmOp::LocalGet(1),   // inner condition
            WasmOp::If,
            WasmOp::I32Const(10),  // val1 (both true)
            WasmOp::Else,
            WasmOp::I32Const(20),  // val2 (outer true, inner false)
            WasmOp::End,
            WasmOp::Else,
            WasmOp::I32Const(30),  // val3 (outer false)
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Should be transformed to: val1, val2, inner_cond, Select, val3, outer_cond, Select
        assert_eq!(preprocessed.len(), 7);
        assert_eq!(preprocessed[0], WasmOp::I32Const(10));  // val1
        assert_eq!(preprocessed[1], WasmOp::I32Const(20));  // val2
        assert_eq!(preprocessed[2], WasmOp::LocalGet(1));   // inner condition
        assert_eq!(preprocessed[3], WasmOp::Select);        // inner select
        assert_eq!(preprocessed[4], WasmOp::I32Const(30));  // val3
        assert_eq!(preprocessed[5], WasmOp::LocalGet(0));   // outer condition
        assert_eq!(preprocessed[6], WasmOp::Select);        // outer select
    }

    #[test]
    fn test_br_if_block_to_select() {
        let bridge = OptimizerBridge::new();

        // Pattern: Block, val1, cond, BrIf(0), Drop, val2, End
        // Should become: val1, val2, cond, Select
        let wasm_ops = vec![
            WasmOp::Block,
            WasmOp::I32Const(10),  // val1 (early exit value)
            WasmOp::LocalGet(0),   // condition
            WasmOp::BrIf(0),       // if cond, exit with val1
            WasmOp::Drop,
            WasmOp::I32Const(20),  // val2 (fallthrough value)
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Should be transformed to: val1, val2, cond, Select
        assert_eq!(preprocessed.len(), 4);
        assert_eq!(preprocessed[0], WasmOp::I32Const(10));  // val1
        assert_eq!(preprocessed[1], WasmOp::I32Const(20));  // val2
        assert_eq!(preprocessed[2], WasmOp::LocalGet(0));   // condition
        assert_eq!(preprocessed[3], WasmOp::Select);
    }

    #[test]
    fn test_br_if_block_with_local_values() {
        let bridge = OptimizerBridge::new();

        // br_if pattern with LocalGet values
        let wasm_ops = vec![
            WasmOp::Block,
            WasmOp::LocalGet(1),   // val1 from local
            WasmOp::LocalGet(0),   // condition
            WasmOp::BrIf(0),
            WasmOp::Drop,
            WasmOp::LocalGet(2),   // val2 from local
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Should be transformed to: val1, val2, cond, Select
        assert_eq!(preprocessed.len(), 4);
        assert_eq!(preprocessed[0], WasmOp::LocalGet(1));   // val1
        assert_eq!(preprocessed[1], WasmOp::LocalGet(2));   // val2
        assert_eq!(preprocessed[2], WasmOp::LocalGet(0));   // condition
        assert_eq!(preprocessed[3], WasmOp::Select);
    }

    #[test]
    fn test_no_transformation_for_non_matching_pattern() {
        let bridge = OptimizerBridge::new();

        // A pattern that doesn't match - if with complex then block
        let wasm_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::If,
            WasmOp::I32Const(10),
            WasmOp::I32Const(5),
            WasmOp::I32Add,        // Complex then block (not a simple value)
            WasmOp::Else,
            WasmOp::I32Const(20),
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Should NOT be transformed - pattern doesn't match
        assert_eq!(preprocessed.len(), 8);
        assert_eq!(preprocessed[0], WasmOp::LocalGet(0));
        assert_eq!(preprocessed[1], WasmOp::If);
    }

    #[test]
    fn test_is_condition_producer() {
        // Test the helper function
        assert!(OptimizerBridge::is_condition_producer(&WasmOp::LocalGet(0)));
        assert!(OptimizerBridge::is_condition_producer(&WasmOp::I32Const(1)));
        assert!(OptimizerBridge::is_condition_producer(&WasmOp::I32Eqz));
        assert!(OptimizerBridge::is_condition_producer(&WasmOp::I32Eq));
        assert!(OptimizerBridge::is_condition_producer(&WasmOp::I32LtS));
        assert!(OptimizerBridge::is_condition_producer(&WasmOp::I32GtU));

        // These should NOT be condition producers
        assert!(!OptimizerBridge::is_condition_producer(&WasmOp::I32Add));
        assert!(!OptimizerBridge::is_condition_producer(&WasmOp::If));
        assert!(!OptimizerBridge::is_condition_producer(&WasmOp::Block));
    }

    #[test]
    fn test_is_simple_value() {
        // Test the helper function
        assert!(OptimizerBridge::is_simple_value(&WasmOp::I32Const(42)));
        assert!(OptimizerBridge::is_simple_value(&WasmOp::LocalGet(0)));
        assert!(OptimizerBridge::is_simple_value(&WasmOp::GlobalGet(1)));

        // These should NOT be simple values
        assert!(!OptimizerBridge::is_simple_value(&WasmOp::I32Add));
        assert!(!OptimizerBridge::is_simple_value(&WasmOp::If));
        assert!(!OptimizerBridge::is_simple_value(&WasmOp::Select));
    }

    #[test]
    fn test_multiple_sequential_patterns() {
        let bridge = OptimizerBridge::new();

        // Two sequential simple if-else patterns
        let wasm_ops = vec![
            // First if-else
            WasmOp::LocalGet(0),
            WasmOp::If,
            WasmOp::I32Const(1),
            WasmOp::Else,
            WasmOp::I32Const(2),
            WasmOp::End,
            // Store first result
            WasmOp::LocalSet(2),
            // Second if-else
            WasmOp::LocalGet(1),
            WasmOp::If,
            WasmOp::I32Const(3),
            WasmOp::Else,
            WasmOp::I32Const(4),
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Both patterns should be transformed
        // First: 1, 2, local.get(0), select
        // LocalSet(2)
        // Second: 3, 4, local.get(1), select
        assert_eq!(preprocessed.len(), 9);
        assert_eq!(preprocessed[3], WasmOp::Select);
        assert_eq!(preprocessed[4], WasmOp::LocalSet(2));
        assert_eq!(preprocessed[8], WasmOp::Select);
    }
}
