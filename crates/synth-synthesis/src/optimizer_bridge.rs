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

use crate::Condition;
use crate::rules::ArmOp;
use synth_cfg::{Cfg, CfgBuilder};
use synth_core::Result;
use synth_core::WasmOp;
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
            WasmOp::I32Const(_) | WasmOp::LocalGet(_) | WasmOp::GlobalGet(_)
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
                        // I64ExtendI32U/S consume an i32 LocalGet and produce an
                        // i64 — so they account for one i64 operand and we must
                        // skip the i32 LocalGet that immediately precedes them
                        // (otherwise we'd mistakenly mark that i32 LocalGet as
                        // i64, double-loading the local). See issue #93.
                        WasmOp::I64ExtendI32U | WasmOp::I64ExtendI32S => {
                            found += 1;
                            // Skip the i32 producer that fed this extend.
                            if j > 0
                                && matches!(
                                    &wasm_ops[j - 1],
                                    WasmOp::LocalGet(_) | WasmOp::I32Const(_)
                                )
                            {
                                j -= 1;
                            }
                        }
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
                // i64 binary arithmetic ops (consume 2 i64 pairs, produce 1 i64 pair).
                //
                // Slot accounting: each i64 occupies 2 consecutive vreg slots
                // (lo, hi). Consuming 2 i64s reads slots [inst_id-4..inst_id-1];
                // producing 1 i64 reserves slots [inst_id, inst_id+1]. So the
                // next op must see the new i64 at slots [next_inst_id-2,
                // next_inst_id-1], which requires `inst_id += 2`.
                //
                // Previously these arms fell through to the wildcard `inst_id
                // += 1`, leaving `dest_hi` at slot `inst_id+1 = next_inst_id`
                // — i.e. the very slot the NEXT wasm op was about to use as a
                // fresh dest. The next op clobbered `dest_hi`, and any later
                // op trying to read `(prev.dest_lo, prev.dest_hi)` would look
                // at `(next_inst_id-2, next_inst_id-1)` which pointed to the
                // hi half of the previously consumed src2 and the just-written
                // current dest_lo — total slot scramble. In some cases the lookup
                // would find no mapping at all and `get_arm_reg` would silently
                // return R0 (issue #93 root cause). See PR #100 fuzz harness
                // and PR #101 defensive panic for the diagnostic plumbing.
                WasmOp::I64Add
                | WasmOp::I64Sub
                | WasmOp::I64And
                | WasmOp::I64Or
                | WasmOp::I64Xor
                | WasmOp::I64Mul
                | WasmOp::I64DivS
                | WasmOp::I64DivU
                | WasmOp::I64RemS
                | WasmOp::I64RemU
                | WasmOp::I64Shl
                | WasmOp::I64ShrS
                | WasmOp::I64ShrU
                | WasmOp::I64Rotl
                | WasmOp::I64Rotr => {
                    let dest_lo = OptReg(inst_id as u32);
                    let dest_hi = OptReg((inst_id + 1) as u32);
                    let src1_lo = OptReg(inst_id.saturating_sub(4) as u32);
                    let src1_hi = OptReg(inst_id.saturating_sub(3) as u32);
                    let src2_lo = OptReg(inst_id.saturating_sub(2) as u32);
                    let src2_hi = OptReg(inst_id.saturating_sub(1) as u32);
                    let opcode = match wasm_op {
                        WasmOp::I64Add => Opcode::I64Add {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Sub => Opcode::I64Sub {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64And => Opcode::I64And {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Or => Opcode::I64Or {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Xor => Opcode::I64Xor {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Mul => Opcode::I64Mul {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64DivS => Opcode::I64DivS {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64DivU => Opcode::I64DivU {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64RemS => Opcode::I64RemS {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64RemU => Opcode::I64RemU {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Shl => Opcode::I64Shl {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64ShrS => Opcode::I64ShrS {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64ShrU => Opcode::I64ShrU {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Rotl => Opcode::I64Rotl {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Rotr => Opcode::I64Rotr {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        _ => unreachable!(),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    inst_id += 2; // produces i64 = 2 slots
                    builder.add_instruction();
                    continue;
                }

                // i64 comparisons (consume 2 i64 pairs, produce single i32 result)
                WasmOp::I64Eq
                | WasmOp::I64Ne
                | WasmOp::I64LtS
                | WasmOp::I64LtU
                | WasmOp::I64GtS
                | WasmOp::I64GtU
                | WasmOp::I64LeS
                | WasmOp::I64LeU
                | WasmOp::I64GeS
                | WasmOp::I64GeU => {
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

                // i64 sign extension (takes i64, produces i64).
                //
                // Slot accounting: consume 1 i64 (slots [inst_id-2, inst_id-1]),
                // produce 1 i64 (slots [inst_id, inst_id+1]). `inst_id += 2`
                // so the next op's `inst_id-2`/`inst_id-1` lookup lands on
                // dest_lo/dest_hi. Was `+= 1` which left dest_hi at the slot
                // the next wasm op would claim as its own dest — clobber.
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
                    inst_id += 2;
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
                    inst_id += 2;
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
                    inst_id += 2;
                    builder.add_instruction();
                    continue;
                }

                // i32 -> i64 zero-extend.
                //
                // Net stack effect: pop 1 i32 slot, push i64 (= 2 slots).
                // We REUSE the consumed i32 slot for `dest_lo` (same vreg,
                // same value semantically) and add 1 fresh slot for
                // `dest_hi`. This keeps the `inst_id.saturating_sub(K)`
                // arithmetic in subsequent i64 ops correct without any
                // off-by-one shift in slot numbering.
                //
                // Pre-fix this op fell through to the catch-all `_ =>
                // Opcode::Nop` arm; subsequent `Opcode::I64ShrU` /
                // `Opcode::I64Shl` source-vreg lookups missed `vreg_to_arm`
                // and `get_arm_reg` returned `Reg::R0` as a silent fallback,
                // causing the i64-shift emitter to clobber AAPCS param R0
                // (the memset destination pointer). See issue #93.
                WasmOp::I64ExtendI32U => {
                    let src_slot = inst_id.saturating_sub(1) as u32;
                    let opcode = Opcode::I64ExtendI32U {
                        dest_lo: OptReg(src_slot),
                        dest_hi: OptReg(inst_id as u32),
                        src: OptReg(src_slot),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    inst_id += 1; // +1 slot net (dest_hi only; dest_lo reuses src)
                    builder.add_instruction();
                    continue;
                }

                // i32 -> i64 sign-extend. Same slot accounting as
                // `I64ExtendI32U` — see comment there.
                WasmOp::I64ExtendI32S => {
                    let src_slot = inst_id.saturating_sub(1) as u32;
                    let opcode = Opcode::I64ExtendI32S {
                        dest_lo: OptReg(src_slot),
                        dest_hi: OptReg(inst_id as u32),
                        src: OptReg(src_slot),
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

                // i64 -> i32 wrap (truncate). Net stack effect: pop i64
                // (2 slots), push i32 (1 slot) = -1 slot. The result IS
                // the low 32 bits of the input i64, so `dest` aliases
                // `src_lo` by IR convention. We don't increment `inst_id`
                // (the natural +1 from the wildcard fallthrough cancels
                // with the -1 i64-pop, net 0 fresh slot).
                WasmOp::I32WrapI64 => {
                    // src_lo is at inst_id-2 (lo of the popped i64),
                    // src_hi is at inst_id-1 (hi, discarded).
                    let src_lo_slot = inst_id.saturating_sub(2) as u32;
                    let opcode = Opcode::I32WrapI64 {
                        dest: OptReg(src_lo_slot),
                        src_lo: OptReg(src_lo_slot),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    // No inst_id increment: the wildcard `inst_id += 1`
                    // is balanced by the -1 net slot delta of the wrap.
                    // We `continue` to skip the wildcard's +1 and emit nothing extra.
                    inst_id = inst_id.saturating_sub(1);
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
                        let (_block_type, target_inst) = block_stack[target_idx];
                        // For loops, branch to start; for blocks, target will be resolved later
                        Opcode::Branch {
                            target: target_inst,
                        }
                    } else {
                        Opcode::Branch { target: 0 }
                    }
                }

                // BrIf: conditional branch - branch if top of stack is non-zero
                WasmOp::BrIf(depth) => {
                    // Find the target block at given depth
                    let target_idx = block_stack.len().saturating_sub(1 + *depth as usize);
                    let target = if target_idx < block_stack.len() {
                        let (_block_type, target_inst) = block_stack[target_idx];
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

                // ===== Sub-word linear-memory ops =====
                //
                // Pop addr (and value for stores), push value (for loads).
                // Pre-fix, these fell through to `Opcode::Nop` — their dest
                // vreg never got mapped to an ARM register, and any
                // consumer of the loaded value triggered the PR #101
                // defensive panic (or, pre-PR-101, silently consumed R0).
                WasmOp::I32Load8S { offset, .. } => Opcode::MemLoadSubword {
                    dest: OptReg(inst_id as u32),
                    addr: OptReg(inst_id.saturating_sub(1) as u32),
                    offset: *offset,
                    width: 1,
                    signed: true,
                },
                WasmOp::I32Load8U { offset, .. } => Opcode::MemLoadSubword {
                    dest: OptReg(inst_id as u32),
                    addr: OptReg(inst_id.saturating_sub(1) as u32),
                    offset: *offset,
                    width: 1,
                    signed: false,
                },
                WasmOp::I32Load16S { offset, .. } => Opcode::MemLoadSubword {
                    dest: OptReg(inst_id as u32),
                    addr: OptReg(inst_id.saturating_sub(1) as u32),
                    offset: *offset,
                    width: 2,
                    signed: true,
                },
                WasmOp::I32Load16U { offset, .. } => Opcode::MemLoadSubword {
                    dest: OptReg(inst_id as u32),
                    addr: OptReg(inst_id.saturating_sub(1) as u32),
                    offset: *offset,
                    width: 2,
                    signed: false,
                },
                WasmOp::I32Store8 { offset, .. } => Opcode::MemStoreSubword {
                    src: OptReg(inst_id.saturating_sub(1) as u32),
                    addr: OptReg(inst_id.saturating_sub(2) as u32),
                    offset: *offset,
                    width: 1,
                },
                WasmOp::I32Store16 { offset, .. } => Opcode::MemStoreSubword {
                    src: OptReg(inst_id.saturating_sub(1) as u32),
                    addr: OptReg(inst_id.saturating_sub(2) as u32),
                    offset: *offset,
                    width: 2,
                },

                // ===== Globals =====
                //
                // GlobalGet pushes a fresh i32; GlobalSet pops one. Without
                // explicit IR ops these silently produced unmapped vregs.
                WasmOp::GlobalGet(idx) => Opcode::GlobalGet {
                    dest: OptReg(inst_id as u32),
                    idx: *idx,
                },
                WasmOp::GlobalSet(idx) => Opcode::GlobalSet {
                    src: OptReg(inst_id.saturating_sub(1) as u32),
                    idx: *idx,
                },

                // ===== Memory size / grow =====
                //
                // Both push an i32 result. On bare-metal targets with fixed
                // memory, grow is a stub (returns the size or -1), but the
                // dest vreg still needs allocation.
                WasmOp::MemorySize(_) => Opcode::MemorySize {
                    dest: OptReg(inst_id as u32),
                },
                WasmOp::MemoryGrow(_) => Opcode::MemoryGrow {
                    dest: OptReg(inst_id as u32),
                    delta: OptReg(inst_id.saturating_sub(1) as u32),
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
            return Ok((
                Vec::new(),
                CfgBuilder::new().build(),
                OptimizationStats::default(),
            ));
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

        Ok((
            live_instructions,
            cfg,
            OptimizationStats {
                removed: result.removed_count,
                modified: result.modified_count,
                added: result.added_count,
                passes_run: self.count_enabled_passes(),
            },
        ))
    }

    /// Count how many passes are enabled
    fn count_enabled_passes(&self) -> usize {
        let mut count = 0;
        if self.config.enable_peephole {
            count += 1;
        }
        if self.config.enable_constant_folding {
            count += 1;
        }
        if self.config.enable_algebraic {
            count += 1;
        }
        if self.config.enable_cse {
            count += 1;
        }
        if self.config.enable_dce {
            count += 1;
        }
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

        // Reserved param registers: R0..R(min(num_params,4)). These hold incoming
        // AAPCS arguments that must NOT be clobbered by i64 op handlers — at least
        // until the user's WASM has done a `local.get` of each. Using Vec because
        // `Reg` does not derive Hash (matches `instruction_selector::alloc_consecutive_pair`).
        let param_reserved_regs: Vec<Reg> = param_regs[..num_params.min(4)].to_vec();

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
        // For i64 returns, also track the hi-half vreg so the epilogue can move
        // the pair into R0:R1 regardless of where regalloc placed it. Was previously
        // unnecessary because every i64 op pinned its result to R0:R1 — that's the
        // bug we're fixing here.
        let mut last_result_vreg_hi: Option<u32> = None;
        // For i64 ops whose IR Opcode only tracks a single `dest` vreg (Clz / Ctz /
        // Popcnt), the hi half lives in a register chosen at lowering time but has
        // no IR vreg pointing at it. Stash that physical reg directly so the
        // epilogue can still emit the correct (R0, R1) move.
        let mut last_result_vreg_hi_reg: Option<Reg> = None;
        // Track whether the last result is an i64 (return value occupies a pair).
        let mut is_i64_result = false;
        // WASM operand value stack - tracks vreg IDs for correct stack semantics
        // Used to restore last_result_vreg after br_if pops its condition
        let mut value_stack: Vec<u32> = Vec::new();

        // Register spilling support: when all temp registers are in use,
        // spill least-recently-used values to the stack frame
        let mut spilled_vregs: HashMap<u32, i32> = HashMap::new();
        let mut next_spill_offset: i32 = 4; // first spill at [SP, #4], etc.
        // Insertion order tracking for LRU eviction
        let mut vreg_alloc_order: Vec<u32> = Vec::new();

        // Known i64 constant values keyed by their `dest_lo` vreg id. Populated
        // when we lower `Opcode::I64Const`; consulted by i64 shift / mask
        // handlers to detect compile-time-constant operands and avoid emitting
        // the full 38-byte runtime shift sequence.
        //
        // Issue #94: when a u64-packed FFI return is split via `i64.shr_u 32`
        // followed by `i32.wrap_i64`, the hi32 field is already in the high
        // register of the i64 pair — no shift instructions are needed, just a
        // vreg rename plus a single `mov rd_hi, #0` for the (now-zero) hi half.
        let mut known_i64_consts: HashMap<u32, i64> = HashMap::new();

        // Helper to get ARM reg from virtual reg.
        // Also checks spill slots — if a vreg was spilled, returns R12 (IP scratch).
        // Callers should also call `reload_spill` to emit the actual load instruction.
        //
        // PANICS if the vreg is neither mapped nor spilled. The previous behavior was
        // a silent `Reg::R0` fallback, which produced miscompilation: a downstream
        // instruction reading the "unknown" vreg would silently consume whatever
        // R0 happens to hold (often a live caller param or memset's dest pointer).
        // Issue #93 was exactly this — `wasm_to_ir` had no handler for
        // `I64ExtendI32U`/`I64ExtendI32S`/`I32WrapI64`, so the IR they should have
        // produced never got mapped to ARM regs, and downstream i64 shifts read R0
        // as their `rm_lo`/`rm_hi`, destroying the loop counter on real silicon.
        // A loud panic here is strictly better than a quiet miscompilation —
        // crash the compiler, not the firmware.
        let get_arm_reg =
            |vreg: &OptReg, map: &HashMap<u32, Reg>, spills: &HashMap<u32, i32>| -> Reg {
                if let Some(&r) = map.get(&vreg.0) {
                    r
                } else if spills.contains_key(&vreg.0) {
                    // Will be reloaded into R12 by reload_spill
                    Reg::R12
                } else {
                    panic!(
                        "synth internal compiler error: vreg v{} has no assigned \
                         ARM register and no spill slot. This is a wasm_to_ir bug — \
                         likely a wasm op whose result is unmapped (see issue #93).",
                        vreg.0
                    );
                }
            };

        // Allocate a CONSECUTIVE callee-saved register pair for an i64 destination.
        //
        // Searches `[(R4,R5), (R6,R7), (R8,R9), (R10,R11)]` for a pair where neither
        // register is currently:
        //   - holding a live vreg (`vreg_to_arm.values()`)
        //   - bound to a non-param local (`local_to_reg.values()`)
        //   - one of the AAPCS param registers we must preserve on entry
        //     (`param_reserved_regs`)
        //
        // Falls back to `(R4, R5)` if no pair is free — preserves prior behaviour
        // for very-pressured functions, but at least keeps params intact in the
        // common case. Per `instruction_selector::alloc_consecutive_pair`, callers
        // who hit the fallback in real workloads will need spill support; that's
        // out of scope for this fix.
        let alloc_i64_pair = |vreg_to_arm: &HashMap<u32, Reg>,
                              local_to_reg: &HashMap<u32, Reg>,
                              param_reserved_regs: &[Reg]|
         -> (Reg, Reg) {
            const CANDIDATES: &[(Reg, Reg)] = &[
                (Reg::R4, Reg::R5),
                (Reg::R6, Reg::R7),
                (Reg::R8, Reg::R9),
                (Reg::R10, Reg::R11),
            ];
            let is_in_use = |r: Reg| -> bool {
                vreg_to_arm.values().any(|&v| v == r)
                    || local_to_reg.values().any(|&v| v == r)
                    || param_reserved_regs.contains(&r)
            };
            for &(lo, hi) in CANDIDATES {
                if !is_in_use(lo) && !is_in_use(hi) {
                    return (lo, hi);
                }
            }
            // Fallback — same hardcoded pair the buggy code used. Better than crashing,
            // and matches existing behaviour when the caller is so pressured that
            // even R8..R11 are occupied. (Empirically this never triggers for
            // workloads we care about; if it does, the architectural fix is
            // proper spilling, not a wider search.)
            (Reg::R4, Reg::R5)
        };

        // Allocate a SINGLE callee-saved register for an i32 destination.
        //
        // Searches `[R4, R5, R6, R7, R8]` for a register not currently held
        // by a live vreg, bound to a non-param local, or reserved as an
        // AAPCS param. The extra_avoid list is honoured for transient
        // operand-region exclusions (e.g. addresses-of operands that must
        // outlive the destination allocation).
        //
        // Falls back to R12 (IP, the universal scratch) if every callee-
        // saved register is taken — matches the prior pressure-relief
        // behaviour. R12 is intentionally NOT in the search list because
        // it's used as a transient by MemLoad/MemStore for the base+offset
        // pointer math, and would be clobbered before the destination is
        // read.
        let alloc_i32_scratch = |vreg_to_arm: &HashMap<u32, Reg>,
                                 local_to_reg: &HashMap<u32, Reg>,
                                 param_reserved_regs: &[Reg],
                                 extra_avoid: &[Reg]|
         -> Reg {
            const CANDIDATES: &[Reg] = &[Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8];
            let is_in_use = |r: Reg| -> bool {
                vreg_to_arm.values().any(|&v| v == r)
                    || local_to_reg.values().any(|&v| v == r)
                    || param_reserved_regs.contains(&r)
                    || extra_avoid.contains(&r)
            };
            for &r in CANDIDATES {
                if !is_in_use(r) {
                    return r;
                }
            }
            // Pressure-relief fallback. R12 is acceptable here because
            // the call sites that use this helper write the destination
            // BEFORE using R12 as scratch (e.g. MemLoad emits the LDR
            // last, after the address math).
            Reg::R12
        };

        // Emit a reload instruction if the vreg was spilled to stack.
        // Must be called before the instruction that uses the register.
        let reload_spill = |vreg: &OptReg, spills: &HashMap<u32, i32>, instrs: &mut Vec<ArmOp>| {
            if let Some(&offset) = spills.get(&vreg.0) {
                instrs.push(ArmOp::Ldr {
                    rd: Reg::R12,
                    addr: crate::rules::MemAddr::imm(Reg::SP, offset),
                });
            }
        };

        // Pre-pass for issue #94: find i64 constants whose ONLY use is as the
        // shift amount of a shr_u/shr_s where the value is 32, or as the mask
        // operand of an `i64.and 0xFFFFFFFF` — those constants are folded away
        // by the shift / and handlers below, so the MOVs that load them into
        // registers are dead. This skip set is consulted in the I64Const
        // handler to bypass emitting those MOVs (saves ~4 bytes per fold).
        let mut skip_const_dest_lo: std::collections::HashSet<u32> =
            std::collections::HashSet::new();
        {
            // First, collect simple constant values produced by I64Const (we
            // only need their `value` and `dest_lo` here — the rest is
            // determined by the consumer instruction below).
            let mut const_values: HashMap<u32, i64> = HashMap::new();
            // Count uses of each const dest_lo across the IR. A const is
            // skip-eligible only if it has exactly one use and that use is the
            // folded shift / and pattern.
            let mut use_count: HashMap<u32, u32> = HashMap::new();
            for inst in instructions {
                if let Opcode::I64Const { dest_lo, value, .. } = &inst.opcode {
                    const_values.insert(dest_lo.0, *value);
                }
                let mut bump = |v: u32| {
                    *use_count.entry(v).or_insert(0) += 1;
                };
                match &inst.opcode {
                    Opcode::I64Add {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Sub {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Or {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Xor {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Mul {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64DivS {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64DivU {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64RemS {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64RemU {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Shl {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64ShrU {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64ShrS {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64And {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Eq {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Ne {
                        src1_lo, src2_lo, ..
                    } => {
                        bump(src1_lo.0);
                        bump(src2_lo.0);
                    }
                    _ => {}
                }
            }
            // Now mark constants whose only use is the folded pattern.
            for inst in instructions {
                match &inst.opcode {
                    Opcode::I64ShrU { src2_lo, .. } | Opcode::I64ShrS { src2_lo, .. } => {
                        if use_count.get(&src2_lo.0).copied() == Some(1)
                            && let Some(v) = const_values.get(&src2_lo.0)
                            && (*v as u64) & 0x3F == 32
                        {
                            skip_const_dest_lo.insert(src2_lo.0);
                        }
                    }
                    Opcode::I64And { src2_lo, .. } => {
                        if use_count.get(&src2_lo.0).copied() == Some(1)
                            && let Some(v) = const_values.get(&src2_lo.0)
                            && (*v as u64) == 0xFFFF_FFFF
                        {
                            skip_const_dest_lo.insert(src2_lo.0);
                        }
                    }
                    _ => {}
                }
            }
        }

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
                    let rs = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);
                    // Track which register holds this local's value
                    // Special case: synthetic local 255 is used for preserving conditions
                    // across nested selects - use R11 which is rarely used elsewhere
                    if *addr == 255 {
                        let local_reg = Reg::R11;
                        if rs != local_reg {
                            arm_instrs.push(ArmOp::Mov {
                                rd: local_reg,
                                op2: Operand2::Reg(rs),
                            });
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
                            arm_instrs.push(ArmOp::Mov {
                                rd: local_reg,
                                op2: Operand2::Reg(rs),
                            });
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
                        let used: Vec<_> = vreg_to_arm
                            .iter()
                            .filter(|(k, _)| !dead_vregs.contains(k))
                            .map(|(_, v)| *v)
                            .chain(local_to_reg.values().copied())
                            .collect();
                        // Expanded temp register pool: R4-R11 (callee-saved) plus R3
                        // Note: R0-R2 are reserved for params/return, R12 is IP, R13 is SP, R14 is LR, R15 is PC
                        let temp_regs = [
                            Reg::R4,
                            Reg::R5,
                            Reg::R6,
                            Reg::R7,
                            Reg::R8,
                            Reg::R9,
                            Reg::R10,
                            Reg::R11,
                            Reg::R3,
                        ];
                        let rd = match temp_regs.iter().find(|r| !used.contains(r)).copied() {
                            Some(r) => r,
                            None => {
                                // All registers exhausted — spill the oldest live
                                // non-local vreg to the stack to free a register.
                                // Find oldest live vreg by allocation order
                                let evict_vreg = vreg_alloc_order
                                    .iter()
                                    .find(|v| {
                                        !dead_vregs.contains(v)
                                            && !local_vregs.contains(v)
                                            && vreg_to_arm.contains_key(v)
                                    })
                                    .copied();
                                if let Some(victim) = evict_vreg {
                                    let victim_reg = vreg_to_arm[&victim];
                                    // Spill: STR victim_reg, [SP, #offset]
                                    let offset = next_spill_offset;
                                    next_spill_offset += 4;
                                    arm_instrs.push(ArmOp::Str {
                                        rd: victim_reg,
                                        addr: crate::rules::MemAddr::imm(Reg::SP, offset),
                                    });
                                    spilled_vregs.insert(victim, offset);
                                    vreg_to_arm.remove(&victim);
                                    victim_reg
                                } else {
                                    // Last resort: reuse R3 (scratch)
                                    Reg::R3
                                }
                            }
                        };
                        vreg_to_arm.insert(dest.0, rd);
                        vreg_alloc_order.push(dest.0);
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
                        arm_instrs.push(ArmOp::Mov {
                            rd,
                            op2: Operand2::Imm(*value),
                        });
                    }
                }

                // Arithmetic operations
                //
                // Pre-fix these hardcoded `rd = Reg::R3`, clobbering the 4th
                // AAPCS argument on every i32 arith in 4-param functions.
                // Use `alloc_i32_scratch` so the destination is picked from
                // the callee-saved bank; sources are added to `extra_avoid`
                // so a 3-operand op doesn't pick its own input as dest while
                // it's still live in `vreg_to_arm`.
                Opcode::Add { dest, src1, src2 } => {
                    reload_spill(src1, &spilled_vregs, &mut arm_instrs);
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    reload_spill(src2, &spilled_vregs, &mut arm_instrs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Add {
                        rd,
                        rn,
                        op2: Operand2::Reg(rm),
                    });
                    last_result_vreg = Some(dest.0);
                    // Mark source vregs as dead (unless they're local vregs)
                    if !local_vregs.contains(&src1.0) {
                        dead_vregs.insert(src1.0);
                    }
                    if !local_vregs.contains(&src2.0) {
                        dead_vregs.insert(src2.0);
                    }
                }

                Opcode::Sub { dest, src1, src2 } => {
                    reload_spill(src1, &spilled_vregs, &mut arm_instrs);
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    reload_spill(src2, &spilled_vregs, &mut arm_instrs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Sub {
                        rd,
                        rn,
                        op2: Operand2::Reg(rm),
                    });
                    last_result_vreg = Some(dest.0);
                    if !local_vregs.contains(&src1.0) {
                        dead_vregs.insert(src1.0);
                    }
                    if !local_vregs.contains(&src2.0) {
                        dead_vregs.insert(src2.0);
                    }
                }

                Opcode::Mul { dest, src1, src2 } => {
                    reload_spill(src1, &spilled_vregs, &mut arm_instrs);
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    reload_spill(src2, &spilled_vregs, &mut arm_instrs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Mul { rd, rn, rm });
                    last_result_vreg = Some(dest.0);
                    if !local_vregs.contains(&src1.0) {
                        dead_vregs.insert(src1.0);
                    }
                    if !local_vregs.contains(&src2.0) {
                        dead_vregs.insert(src2.0);
                    }
                }

                Opcode::DivS { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);

                    // Trap check 1: divide by zero
                    arm_instrs.push(ArmOp::Cmp {
                        rn: rm,
                        op2: Operand2::Imm(0),
                    });
                    arm_instrs.push(ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 0,
                    });
                    arm_instrs.push(ArmOp::Udf { imm: 0 });

                    // Trap check 2: signed overflow (INT_MIN / -1)
                    // Load INT_MIN (0x80000000) into R12
                    arm_instrs.push(ArmOp::Movw {
                        rd: Reg::R12,
                        imm16: 0,
                    });
                    arm_instrs.push(ArmOp::Movt {
                        rd: Reg::R12,
                        imm16: 0x8000,
                    });
                    // CMP dividend, INT_MIN
                    arm_instrs.push(ArmOp::Cmp {
                        rn,
                        op2: Operand2::Reg(Reg::R12),
                    });
                    // BNE.N +3 (skip overflow check if dividend != INT_MIN)
                    // Skip 8 bytes: CMN.W(4) + BNE(2) + UDF(2)
                    // Branch target = PC + (imm8 << 1) = B+4 + 6 = B+10 (SDIV)
                    arm_instrs.push(ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 3,
                    });
                    // CMN divisor, #1 (check if divisor == -1: -1 + 1 = 0 sets Z flag)
                    // CMN.W is 4 bytes
                    arm_instrs.push(ArmOp::Cmn {
                        rn: rm,
                        op2: Operand2::Imm(1),
                    });
                    // BNE.N +0 (skip UDF if divisor != -1)
                    arm_instrs.push(ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 0,
                    });
                    // UDF #1 (trap on overflow)
                    arm_instrs.push(ArmOp::Udf { imm: 1 });

                    arm_instrs.push(ArmOp::Sdiv { rd, rn, rm });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::DivU { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);

                    // Trap check: divide by zero
                    arm_instrs.push(ArmOp::Cmp {
                        rn: rm,
                        op2: Operand2::Imm(0),
                    });
                    arm_instrs.push(ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 0,
                    });
                    arm_instrs.push(ArmOp::Udf { imm: 0 });

                    arm_instrs.push(ArmOp::Udiv { rd, rn, rm });
                    last_result_vreg = Some(dest.0);
                }

                // Remainder: rd = rn - (rn / rm) * rm
                Opcode::RemS { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);

                    // Trap check: divide by zero (rem_s doesn't trap on INT_MIN % -1)
                    arm_instrs.push(ArmOp::Cmp {
                        rn: rm,
                        op2: Operand2::Imm(0),
                    });
                    arm_instrs.push(ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 0,
                    });
                    arm_instrs.push(ArmOp::Udf { imm: 0 });

                    // Use MLS: rd = ra - rn * rm, where ra = dividend, result of div in temp
                    arm_instrs.push(ArmOp::Sdiv {
                        rd: Reg::R12,
                        rn,
                        rm,
                    }); // R12 = rn / rm
                    arm_instrs.push(ArmOp::Mls {
                        rd,
                        rn: Reg::R12,
                        rm,
                        ra: rn,
                    }); // rd = rn - R12 * rm
                    last_result_vreg = Some(dest.0);
                }

                Opcode::RemU { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);

                    // Trap check: divide by zero
                    arm_instrs.push(ArmOp::Cmp {
                        rn: rm,
                        op2: Operand2::Imm(0),
                    });
                    arm_instrs.push(ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 0,
                    });
                    arm_instrs.push(ArmOp::Udf { imm: 0 });

                    arm_instrs.push(ArmOp::Udiv {
                        rd: Reg::R12,
                        rn,
                        rm,
                    });
                    arm_instrs.push(ArmOp::Mls {
                        rd,
                        rn: Reg::R12,
                        rm,
                        ra: rn,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Bitwise operations
                Opcode::And { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::And {
                        rd,
                        rn,
                        op2: Operand2::Reg(rm),
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Or { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Orr {
                        rd,
                        rn,
                        op2: Operand2::Reg(rm),
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Xor { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Eor {
                        rd,
                        rn,
                        op2: Operand2::Reg(rm),
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Shifts - WASM spec: shift amount masked to 5 bits (& 31)
                // ARM LSL/LSR/ASR by register use low byte, so shift >= 32
                // produces 0 (not wrapping). We must mask first.
                Opcode::Shl { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    // Mask shift amount: R12 = rm & 31
                    arm_instrs.push(ArmOp::And {
                        rd: Reg::R12,
                        rn: rm,
                        op2: Operand2::Imm(31),
                    });
                    arm_instrs.push(ArmOp::LslReg {
                        rd,
                        rn,
                        rm: Reg::R12,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::ShrS { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::And {
                        rd: Reg::R12,
                        rn: rm,
                        op2: Operand2::Imm(31),
                    });
                    arm_instrs.push(ArmOp::AsrReg {
                        rd,
                        rn,
                        rm: Reg::R12,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::ShrU { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::And {
                        rd: Reg::R12,
                        rn: rm,
                        op2: Operand2::Imm(31),
                    });
                    arm_instrs.push(ArmOp::LsrReg {
                        rd,
                        rn,
                        rm: Reg::R12,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Rotate right: WASM masks to 5 bits, ARM ROR by register
                // uses low byte (ROR by 32 = no-op on ARM, but WASM wants same)
                // Actually ROR wraps naturally, but we mask for consistency
                Opcode::Rotr { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::And {
                        rd: Reg::R12,
                        rn: rm,
                        op2: Operand2::Imm(31),
                    });
                    arm_instrs.push(ArmOp::RorReg {
                        rd,
                        rn,
                        rm: Reg::R12,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Rotate left: ROTL(x, n) = ROR(x, 32 - (n & 31))
                // Emit: AND R12, Rm, #31; RSB R12, R12, #32; ROR.W Rd, Rn, R12
                Opcode::Rotl { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    // R12 = rm & 31
                    arm_instrs.push(ArmOp::And {
                        rd: Reg::R12,
                        rn: rm,
                        op2: Operand2::Imm(31),
                    });
                    // R12 = 32 - R12
                    arm_instrs.push(ArmOp::Rsb {
                        rd: Reg::R12,
                        rn: Reg::R12,
                        imm: 32,
                    });
                    // rd = ROR(rn, R12)
                    arm_instrs.push(ArmOp::RorReg {
                        rd,
                        rn,
                        rm: Reg::R12,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Bit count operations (unary)
                Opcode::Clz { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rm]);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Clz { rd, rm });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Ctz { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rm]);
                    vreg_to_arm.insert(dest.0, rd);
                    // CTZ = CLZ(RBIT(x)) - reverse bits, then count leading zeros
                    arm_instrs.push(ArmOp::Rbit { rd, rm });
                    arm_instrs.push(ArmOp::Clz { rd, rm: rd });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Popcnt { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rm]);
                    vreg_to_arm.insert(dest.0, rd);
                    // Popcnt - no direct instruction, use Popcnt pseudo-op
                    arm_instrs.push(ArmOp::Popcnt { rd, rm });
                    last_result_vreg = Some(dest.0);
                }

                // Sign extension operations (unary)
                Opcode::Extend8S { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rm]);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Sxtb { rd, rm });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Extend16S { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rm]);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Sxth { rd, rm });
                    last_result_vreg = Some(dest.0);
                }

                // Eqz - compare with zero (unary)
                Opcode::Eqz { dest, src } => {
                    let rn = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rn]);
                    vreg_to_arm.insert(dest.0, rd);

                    // CMP rn, #0; SetCond rd, EQ
                    arm_instrs.push(ArmOp::Cmp {
                        rn,
                        op2: Operand2::Imm(0),
                    });
                    arm_instrs.push(ArmOp::SetCond {
                        rd,
                        cond: crate::rules::Condition::EQ,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Comparisons - set result to 0 or 1
                Opcode::Eq { dest, src1, src2 }
                | Opcode::Ne { dest, src1, src2 }
                | Opcode::LtS { dest, src1, src2 }
                | Opcode::LtU { dest, src1, src2 }
                | Opcode::LeS { dest, src1, src2 }
                | Opcode::LeU { dest, src1, src2 }
                | Opcode::GtS { dest, src1, src2 }
                | Opcode::GtU { dest, src1, src2 }
                | Opcode::GeS { dest, src1, src2 }
                | Opcode::GeU { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs);
                    // Pre-fix this hardcoded `Reg::R7` to keep the SetCond
                    // encodable as 16-bit Thumb (which can only address R0-R7).
                    // R7 is callee-saved (no AAPCS clobber) but the hardcode
                    // collided with non-param locals stored in R7. Use
                    // `alloc_i32_scratch` constrained to the R4..R7 lower-
                    // bank candidates so SetCond keeps its 16-bit encoding
                    // when possible. (R4..R7 are all in the helper's
                    // search list and all 16-bit-MOV-addressable.)
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
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

                    arm_instrs.push(ArmOp::Cmp {
                        rn,
                        op2: Operand2::Reg(rm),
                    });
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
                    let rcond = get_arm_reg(cond, &vreg_to_arm, &spilled_vregs);
                    arm_instrs.push(ArmOp::Cmp {
                        rn: rcond,
                        op2: Operand2::Imm(0),
                    });
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
                        let rv = get_arm_reg(v, &vreg_to_arm, &spilled_vregs);
                        if rv != Reg::R0 {
                            arm_instrs.push(ArmOp::Mov {
                                rd: Reg::R0,
                                op2: Operand2::Reg(rv),
                            });
                        }
                    }
                    arm_instrs.push(ArmOp::Bx { rm: Reg::LR });
                }

                // Select: dest = cond != 0 ? val_true : val_false
                // Implementation: CMP cond, #0; IT EQ; MOVEQ dest, val_false
                // (if cond==0, move val_false to dest; otherwise val_true is already in position)
                Opcode::Select {
                    dest,
                    val_true,
                    val_false,
                    cond,
                } => {
                    let r_cond = get_arm_reg(cond, &vreg_to_arm, &spilled_vregs);
                    let r_true = get_arm_reg(val_true, &vreg_to_arm, &spilled_vregs);
                    let r_false = get_arm_reg(val_false, &vreg_to_arm, &spilled_vregs);

                    // Pre-fix this hardcoded R3, clobbering the 4th AAPCS
                    // arg on every Select. Use `alloc_i32_scratch` so the
                    // destination is callee-saved by construction.
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[r_cond, r_true, r_false],
                    );
                    vreg_to_arm.insert(dest.0, rd);

                    // CRITICAL: If condition is in rd and we need to move val_true to rd,
                    // we must save the condition first to avoid clobbering it
                    let actual_cond = if r_cond == rd && r_true != rd {
                        // Save condition to R12 (IP) before overwriting rd
                        arm_instrs.push(ArmOp::Mov {
                            rd: Reg::R12,
                            op2: Operand2::Reg(r_cond),
                        });
                        Reg::R12
                    } else {
                        r_cond
                    };

                    // Move val_true to result (it will be overwritten if cond==0)
                    if r_true != rd {
                        arm_instrs.push(ArmOp::Mov {
                            rd,
                            op2: Operand2::Reg(r_true),
                        });
                    }

                    // Compare condition with 0
                    arm_instrs.push(ArmOp::Cmp {
                        rn: actual_cond,
                        op2: Operand2::Imm(0),
                    });

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
                Opcode::I64Load {
                    dest_lo,
                    dest_hi,
                    addr,
                } => {
                    // Map local index to register pair
                    // Per AAPCS: i64 uses consecutive even/odd register pairs
                    let (lo_reg, hi_reg) = if *addr == 0 && num_params >= 2 {
                        (Reg::R0, Reg::R1) // First i64 param
                    } else if *addr == 1 && num_params >= 4 {
                        (Reg::R2, Reg::R3) // Second i64 param
                    } else {
                        // Non-param i64 local: pick a free callee-saved pair so we
                        // don't clobber AAPCS arg regs that haven't been read yet.
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs)
                    };
                    vreg_to_arm.insert(dest_lo.0, lo_reg);
                    vreg_to_arm.insert(dest_hi.0, hi_reg);
                    // No ARM instructions needed - values are already in registers for params
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Const {
                    dest_lo,
                    dest_hi,
                    value,
                } => {
                    // Record the constant value so downstream i64 shift / mask
                    // handlers can detect and special-case constant operands.
                    // See `known_i64_consts` declaration for the rationale (issue #94).
                    known_i64_consts.insert(dest_lo.0, *value);
                    // Issue #94: if the pre-pass marked this constant as
                    // dead-on-arrival (its sole use is folded by the
                    // shift/and handler), skip emitting it entirely.
                    if skip_const_dest_lo.contains(&dest_lo.0) {
                        continue;
                    }
                    // Load 64-bit constant into register pair
                    let lo = (*value & 0xFFFFFFFF) as u32;
                    let hi = ((*value >> 32) & 0xFFFFFFFF) as u32;
                    // Choose a free callee-saved pair so we don't trample params still
                    // sitting in R0..R3. The earlier heuristic (vreg-id → R0:R1 / R2:R3)
                    // ignored AAPCS, breaking any function that issued an i64.const
                    // before reading its i32 params.
                    let (lo_reg, hi_reg) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, lo_reg);
                    vreg_to_arm.insert(dest_hi.0, hi_reg);
                    // Load low word
                    if lo <= 255 {
                        arm_instrs.push(ArmOp::Mov {
                            rd: lo_reg,
                            op2: Operand2::Imm(lo as i32),
                        });
                    } else {
                        arm_instrs.push(ArmOp::Movw {
                            rd: lo_reg,
                            imm16: (lo & 0xFFFF) as u16,
                        });
                        if lo > 0xFFFF {
                            arm_instrs.push(ArmOp::Movt {
                                rd: lo_reg,
                                imm16: ((lo >> 16) & 0xFFFF) as u16,
                            });
                        }
                    }
                    // Load high word
                    if hi <= 255 {
                        arm_instrs.push(ArmOp::Mov {
                            rd: hi_reg,
                            op2: Operand2::Imm(hi as i32),
                        });
                    } else {
                        arm_instrs.push(ArmOp::Movw {
                            rd: hi_reg,
                            imm16: (hi & 0xFFFF) as u16,
                        });
                        if hi > 0xFFFF {
                            arm_instrs.push(ArmOp::Movt {
                                rd: hi_reg,
                                imm16: ((hi >> 16) & 0xFFFF) as u16,
                            });
                        }
                    }
                    // If this i64 const is the final return value, the epilogue
                    // needs to know which pair holds it (for the move into R0:R1).
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Add {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    // i64.add: rd = rn + rm using the actual operand regs from
                    // vreg_to_arm — NOT hardcoded R0:R1/R2:R3 (which would clobber
                    // AAPCS param regs).
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::Adds {
                        rd: rd_lo,
                        rn: rn_lo,
                        op2: Operand2::Reg(rm_lo),
                    });
                    arm_instrs.push(ArmOp::Adc {
                        rd: rd_hi,
                        rn: rn_hi,
                        op2: Operand2::Reg(rm_hi),
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Sub {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::Subs {
                        rd: rd_lo,
                        rn: rn_lo,
                        op2: Operand2::Reg(rm_lo),
                    });
                    arm_instrs.push(ArmOp::Sbc {
                        rd: rd_hi,
                        rn: rn_hi,
                        op2: Operand2::Reg(rm_hi),
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64And {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    // Issue #94: `i64.and` against a constant low-half mask
                    // (typically `0xFFFFFFFF` to extract the lo32 of a u64-packed
                    // FFI return). The lo half collapses to a no-op rename, the
                    // hi half collapses to MOV #0 — saving the two AND.W
                    // instructions (8 bytes total) plus the MOVW/MOVT for the
                    // mask constant itself (deduped by ConstantFolding/CSE in
                    // most cases, but the ANDs always remain).
                    let mask = known_i64_consts.get(&src2_lo.0).copied();
                    if let Some(m) = mask {
                        let m_u64 = m as u64;
                        if m_u64 == 0xFFFF_FFFF {
                            // Low 32 bits unchanged, high 32 bits zeroed.
                            let rd_hi =
                                alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs).1;
                            vreg_to_arm.insert(dest_lo.0, rn_lo);
                            vreg_to_arm.insert(dest_hi.0, rd_hi);
                            arm_instrs.push(ArmOp::Mov {
                                rd: rd_hi,
                                op2: Operand2::Imm(0),
                            });
                            last_result_vreg = Some(dest_lo.0);
                            last_result_vreg_hi = Some(dest_hi.0);
                            is_i64_result = true;
                            // Skip the generic AND emit below.
                            continue;
                        }
                    }
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::And {
                        rd: rd_lo,
                        rn: rn_lo,
                        op2: Operand2::Reg(rm_lo),
                    });
                    arm_instrs.push(ArmOp::And {
                        rd: rd_hi,
                        rn: rn_hi,
                        op2: Operand2::Reg(rm_hi),
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Or {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::Orr {
                        rd: rd_lo,
                        rn: rn_lo,
                        op2: Operand2::Reg(rm_lo),
                    });
                    arm_instrs.push(ArmOp::Orr {
                        rd: rd_hi,
                        rn: rn_hi,
                        op2: Operand2::Reg(rm_hi),
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Xor {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::Eor {
                        rd: rd_lo,
                        rn: rn_lo,
                        op2: Operand2::Reg(rm_lo),
                    });
                    arm_instrs.push(ArmOp::Eor {
                        rd: rd_hi,
                        rn: rn_hi,
                        op2: Operand2::Reg(rm_hi),
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // ========================================================================
                // i64 Comparisons (result is single i32)
                //
                // Sources are read from `vreg_to_arm[src*]` rather than hardcoded
                // R0:R1/R2:R3 — the latter would mean "i64 ops always assume their
                // operands materialised at the AAPCS arg slots", which is false:
                // operand registers come from whatever the upstream IR producers
                // (I64Const, I64Load, prior i64 ops) chose. Result lands on the lo
                // half of a freshly allocated callee-saved pair so we don't smash
                // any AAPCS arg reg the user hasn't read yet.
                // ========================================================================
                Opcode::I64Eq {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::EQ,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64Ne {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::NE,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64LtS {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::LT,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64GtS {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::GT,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64LeS {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::LE,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64GeS {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::GE,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Unsigned i64 comparisons
                Opcode::I64LtU {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::LO,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64GtU {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::HI,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64LeU {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::LS,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64GeU {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::HS,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64Eqz {
                    dest,
                    src_lo,
                    src_hi,
                } => {
                    let rn_lo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCondZ { rd, rn_lo, rn_hi });
                    last_result_vreg = Some(dest.0);
                }

                // i64 count leading zeros (i64 result: lo gets count, hi must be 0).
                //
                // The ArmOp::I64Clz encoder writes the count into `rd` AND zeroes
                // `rnhi` in-place — so `rnhi` doubles as the result's hi half. To
                // keep the upstream src_hi register intact and avoid clobbering
                // unrelated AAPCS regs, we copy src_hi into a freshly allocated
                // callee-saved hi slot and pass that as `rnhi`. After the encoded
                // sequence, the i64 result lives in (rd_lo, rd_hi).
                //
                // The IR Opcode only carries a single `dest` vreg (the lo half);
                // we register dest.0 → rd_lo. The hi-zero is implicit and used by
                // the function epilogue when this is the i64 return value (see
                // last_result_vreg_hi_reg below).
                Opcode::I64Clz {
                    dest,
                    src_lo,
                    src_hi,
                } => {
                    let rnlo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs);
                    let rnhi_src = get_arm_reg(src_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    if rd_hi != rnhi_src {
                        arm_instrs.push(ArmOp::Mov {
                            rd: rd_hi,
                            op2: Operand2::Reg(rnhi_src),
                        });
                    }
                    vreg_to_arm.insert(dest.0, rd_lo);
                    arm_instrs.push(ArmOp::I64Clz {
                        rd: rd_lo,
                        rnlo,
                        rnhi: rd_hi,
                    });
                    last_result_vreg = Some(dest.0);
                    last_result_vreg_hi_reg = Some(rd_hi);
                    is_i64_result = true;
                }

                // i64 count trailing zeros — same pattern as I64Clz above.
                Opcode::I64Ctz {
                    dest,
                    src_lo,
                    src_hi,
                } => {
                    let rnlo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs);
                    let rnhi_src = get_arm_reg(src_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    if rd_hi != rnhi_src {
                        arm_instrs.push(ArmOp::Mov {
                            rd: rd_hi,
                            op2: Operand2::Reg(rnhi_src),
                        });
                    }
                    vreg_to_arm.insert(dest.0, rd_lo);
                    arm_instrs.push(ArmOp::I64Ctz {
                        rd: rd_lo,
                        rnlo,
                        rnhi: rd_hi,
                    });
                    last_result_vreg = Some(dest.0);
                    last_result_vreg_hi_reg = Some(rd_hi);
                    is_i64_result = true;
                }

                // i64 population count — same pattern as I64Clz above.
                Opcode::I64Popcnt {
                    dest,
                    src_lo,
                    src_hi,
                } => {
                    let rnlo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs);
                    let rnhi_src = get_arm_reg(src_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    if rd_hi != rnhi_src {
                        arm_instrs.push(ArmOp::Mov {
                            rd: rd_hi,
                            op2: Operand2::Reg(rnhi_src),
                        });
                    }
                    vreg_to_arm.insert(dest.0, rd_lo);
                    arm_instrs.push(ArmOp::I64Popcnt {
                        rd: rd_lo,
                        rnlo,
                        rnhi: rd_hi,
                    });
                    last_result_vreg = Some(dest.0);
                    last_result_vreg_hi_reg = Some(rd_hi);
                    is_i64_result = true;
                }

                // i64 sign extension operations
                Opcode::I64Extend8S {
                    dest_lo,
                    dest_hi,
                    src_lo,
                } => {
                    let rnlo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs);
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64Extend8S { rdlo, rdhi, rnlo });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Extend16S {
                    dest_lo,
                    dest_hi,
                    src_lo,
                } => {
                    let rnlo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs);
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64Extend16S { rdlo, rdhi, rnlo });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Extend32S {
                    dest_lo,
                    dest_hi,
                    src_lo,
                } => {
                    let rnlo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs);
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64Extend32S { rdlo, rdhi, rnlo });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i32 -> i64 zero-extension (issue #93 fix).
                //
                // Critical: we MUST move `src` into a callee-saved register
                // pair, even if `src` was already in a non-param register.
                // The downstream `I64Shl/ShrU/ShrS` ARM emitter writes to
                // both `rm_lo` and `rm_hi` (see `arm_encoder.rs:2872`,
                // `:2954`, `:3036` — `AND.W rm_lo, rm_lo, #63;
                // SUBS.W rm_hi, rm_lo, #32; ...`). Pre-fix, `src` could be
                // an AAPCS param register (R0..R3) and the shift would
                // clobber the caller's argument. By Mov'ing into a fresh
                // pair from `alloc_i64_pair` (which excludes params and
                // live vregs), we guarantee `rm_lo`/`rm_hi` are scratch.
                Opcode::I64ExtendI32U {
                    dest_lo,
                    dest_hi,
                    src,
                } => {
                    let src_arm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);
                    let (new_lo, new_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    if src_arm != new_lo {
                        arm_instrs.push(ArmOp::Mov {
                            rd: new_lo,
                            op2: crate::rules::Operand2::Reg(src_arm),
                        });
                    }
                    arm_instrs.push(ArmOp::Movw {
                        rd: new_hi,
                        imm16: 0,
                    });
                    // Re-map dest_lo (which IS the src vreg by IR convention)
                    // to the new lo arm reg, AND map dest_hi to the new hi.
                    vreg_to_arm.insert(dest_lo.0, new_lo);
                    vreg_to_arm.insert(dest_hi.0, new_hi);
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i32 -> i64 sign-extension. Same scratch-pair discipline as
                // I64ExtendI32U; the high half is `src ASR #31`.
                Opcode::I64ExtendI32S {
                    dest_lo,
                    dest_hi,
                    src,
                } => {
                    let src_arm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);
                    let (new_lo, new_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    if src_arm != new_lo {
                        arm_instrs.push(ArmOp::Mov {
                            rd: new_lo,
                            op2: crate::rules::Operand2::Reg(src_arm),
                        });
                    }
                    // hi = src ASR #31 — sign bit replicated across all 32 bits.
                    arm_instrs.push(ArmOp::Asr {
                        rd: new_hi,
                        rn: new_lo,
                        shift: 31,
                    });
                    vreg_to_arm.insert(dest_lo.0, new_lo);
                    vreg_to_arm.insert(dest_hi.0, new_hi);
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 -> i32 wrap. The result IS the low 32 bits of the
                // input — by IR convention `dest == src_lo` (same vreg),
                // so the lookup of `dest` is already correctly mapped to
                // the i64 lo half's ARM register. Emit no ARM code.
                Opcode::I32WrapI64 { dest, src_lo } => {
                    let src_arm = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs);
                    vreg_to_arm.insert(dest.0, src_arm);
                    last_result_vreg = Some(dest.0);
                    is_i64_result = false;
                }

                // i64 multiply: UMULL + MLA cross products
                Opcode::I64Mul {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::I64Mul {
                        rd_lo,
                        rd_hi,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 shift left
                Opcode::I64Shl {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::I64Shl {
                        rd_lo,
                        rd_hi,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 arithmetic shift right
                Opcode::I64ShrS {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    // Issue #94 (signed variant): `i64.shr_s 32; i32.wrap_i64`
                    // also extracts the upper 32 bits unchanged. dest_lo = rn_hi,
                    // dest_hi = sign-extension of rn_hi (ASR #31 of rn_hi).
                    let shr_const = known_i64_consts
                        .get(&src2_lo.0)
                        .copied()
                        .map(|v| (v as u64) & 0x3F);
                    if shr_const == Some(32) {
                        let rd_hi =
                            alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs).1;
                        vreg_to_arm.insert(dest_lo.0, rn_hi);
                        vreg_to_arm.insert(dest_hi.0, rd_hi);
                        // ASR rd_hi, rn_hi, #31 — replicate the sign bit across
                        // the new hi half. 4-byte Thumb-2 encoding via Asr-imm.
                        arm_instrs.push(ArmOp::Asr {
                            rd: rd_hi,
                            rn: rn_hi,
                            shift: 31,
                        });
                        last_result_vreg = Some(dest_lo.0);
                        last_result_vreg_hi = Some(dest_hi.0);
                        is_i64_result = true;
                    } else {
                        let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                        let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                        let (rd_lo, rd_hi) =
                            alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                        vreg_to_arm.insert(dest_lo.0, rd_lo);
                        vreg_to_arm.insert(dest_hi.0, rd_hi);
                        arm_instrs.push(ArmOp::I64ShrS {
                            rd_lo,
                            rd_hi,
                            rn_lo,
                            rn_hi,
                            rm_lo,
                            rm_hi,
                        });
                        last_result_vreg = Some(dest_lo.0);
                        last_result_vreg_hi = Some(dest_hi.0);
                        is_i64_result = true;
                    }
                }

                // i64 logical shift right
                Opcode::I64ShrU {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    // Issue #94: u64-packed FFI return — `i64.shr_u 32` extracts
                    // the high 32 bits, which are already sitting in `rn_hi`. Skip
                    // the 38-byte runtime shift sequence; just rename `dest_lo`
                    // onto `rn_hi` and zero `dest_hi`. Total cost: a single
                    // `mov rd_hi, #0` (2-4 bytes) instead of 38 bytes.
                    //
                    // Per WASM semantics the shift amount is taken modulo 64, so
                    // any constant whose low 6 bits == 32 hits this fast path.
                    let shr_const = known_i64_consts
                        .get(&src2_lo.0)
                        .copied()
                        .map(|v| (v as u64) & 0x3F);
                    if shr_const == Some(32) {
                        let rd_hi =
                            alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs).1;
                        // dest_lo aliases the source's hi register (no instruction).
                        vreg_to_arm.insert(dest_lo.0, rn_hi);
                        // dest_hi is zero — emit a single MOV rd_hi, #0.
                        vreg_to_arm.insert(dest_hi.0, rd_hi);
                        arm_instrs.push(ArmOp::Mov {
                            rd: rd_hi,
                            op2: Operand2::Imm(0),
                        });
                        last_result_vreg = Some(dest_lo.0);
                        last_result_vreg_hi = Some(dest_hi.0);
                        is_i64_result = true;
                    } else {
                        let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                        let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                        let (rd_lo, rd_hi) =
                            alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                        vreg_to_arm.insert(dest_lo.0, rd_lo);
                        vreg_to_arm.insert(dest_hi.0, rd_hi);
                        arm_instrs.push(ArmOp::I64ShrU {
                            rd_lo,
                            rd_hi,
                            rn_lo,
                            rn_hi,
                            rm_lo,
                            rm_hi,
                        });
                        last_result_vreg = Some(dest_lo.0);
                        last_result_vreg_hi = Some(dest_hi.0);
                        is_i64_result = true;
                    }
                }

                // i64 rotate left
                Opcode::I64Rotl {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    ..
                } => {
                    let rnlo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rnhi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let shift = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64Rotl {
                        rdlo,
                        rdhi,
                        rnlo,
                        rnhi,
                        shift,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 rotate right
                Opcode::I64Rotr {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    ..
                } => {
                    let rnlo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rnhi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let shift = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64Rotr {
                        rdlo,
                        rdhi,
                        rnlo,
                        rnhi,
                        shift,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 signed division
                Opcode::I64DivS {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rnlo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rnhi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rmlo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rmhi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64DivS {
                        rdlo,
                        rdhi,
                        rnlo,
                        rnhi,
                        rmlo,
                        rmhi,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 unsigned division
                Opcode::I64DivU {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rnlo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rnhi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rmlo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rmhi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64DivU {
                        rdlo,
                        rdhi,
                        rnlo,
                        rnhi,
                        rmlo,
                        rmhi,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 signed remainder
                Opcode::I64RemS {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rnlo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rnhi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rmlo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rmhi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64RemS {
                        rdlo,
                        rdhi,
                        rnlo,
                        rnhi,
                        rmlo,
                        rmhi,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 unsigned remainder
                Opcode::I64RemU {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rnlo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs);
                    let rnhi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs);
                    let rmlo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs);
                    let rmhi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs);
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64RemU {
                        rdlo,
                        rdhi,
                        rnlo,
                        rnhi,
                        rmlo,
                        rmhi,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
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
                //
                // Pre-fix hardcoded `rd = Reg::R0`, which clobbered the
                // first AAPCS param on every local.tee even when neither
                // src nor dest had anything to do with R0.
                Opcode::Copy { dest, src } => {
                    let rs = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rs]);
                    vreg_to_arm.insert(dest.0, rd);
                    if rs != rd {
                        arm_instrs.push(ArmOp::Mov {
                            rd,
                            op2: Operand2::Reg(rs),
                        });
                    }
                    last_result_vreg = Some(dest.0);
                }

                // TeeStore: Store to local AND keep value on stack (local.tee)
                Opcode::TeeStore { dest, src, addr } => {
                    let rs = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);

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
                            arm_instrs.push(ArmOp::Mov {
                                rd: local_reg,
                                op2: Operand2::Reg(rs),
                            });
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
                            arm_instrs.push(ArmOp::Mov {
                                rd: param_reg,
                                op2: Operand2::Reg(rs),
                            });
                        }
                        vreg_to_arm.insert(dest.0, param_reg);
                    }
                    // TeeStore produces a value that may be the function result
                    last_result_vreg = Some(dest.0);
                }

                // ========================================================================
                // Linear Memory Operations
                // ========================================================================

                // MemLoad: load 32-bit value from linear memory.
                //
                // Generates: MOVW R12, #base_lo; MOVT R12, #base_hi;
                //            ADD R12, R12, Raddr; LDR Rd, [R12, #offset]
                //
                // `Rd` MUST NOT alias an AAPCS param register (R0..R3) — a
                // `local.get` of param N anywhere downstream would otherwise
                // observe whatever the MemLoad just wrote. Pre-fix this was
                // hardcoded to `Reg::R3`, which clobbered the 4th AAPCS
                // argument on every `i32.load`. Use the scratch helper so
                // the destination is picked from the callee-saved bank.
                Opcode::MemLoad { dest, addr, offset } => {
                    let r_addr = get_arm_reg(addr, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[r_addr],
                    );
                    vreg_to_arm.insert(dest.0, rd);

                    // Linear memory base address: 0x20000100 (in SRAM, above stack area)
                    let base: u32 = 0x20000100;
                    let base_lo = (base & 0xFFFF) as u16;
                    let base_hi = ((base >> 16) & 0xFFFF) as u16;

                    // Load base address into R12 (scratch register)
                    arm_instrs.push(ArmOp::Movw {
                        rd: Reg::R12,
                        imm16: base_lo,
                    });
                    arm_instrs.push(ArmOp::Movt {
                        rd: Reg::R12,
                        imm16: base_hi,
                    });
                    // Add WASM address offset
                    arm_instrs.push(ArmOp::Add {
                        rd: Reg::R12,
                        rn: Reg::R12,
                        op2: Operand2::Reg(r_addr),
                    });
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
                    let r_addr = get_arm_reg(addr, &vreg_to_arm, &spilled_vregs);
                    let r_src = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);

                    // Linear memory base address: 0x20000100 (in SRAM, above stack area)
                    let base: u32 = 0x20000100;
                    let base_lo = (base & 0xFFFF) as u16;
                    let base_hi = ((base >> 16) & 0xFFFF) as u16;

                    // Load base address into R12 (scratch register)
                    arm_instrs.push(ArmOp::Movw {
                        rd: Reg::R12,
                        imm16: base_lo,
                    });
                    arm_instrs.push(ArmOp::Movt {
                        rd: Reg::R12,
                        imm16: base_hi,
                    });
                    // Add WASM address offset
                    arm_instrs.push(ArmOp::Add {
                        rd: Reg::R12,
                        rn: Reg::R12,
                        op2: Operand2::Reg(r_addr),
                    });
                    // Store to [base + wasm_addr + static_offset]
                    arm_instrs.push(ArmOp::Str {
                        rd: r_src,
                        addr: crate::rules::MemAddr::imm(Reg::R12, *offset as i32),
                    });
                    // MemStore does not produce a value
                }

                // Sub-word linear memory load (i32.load8_s/u, i32.load16_s/u).
                //
                // Generates the same base+addr math as MemLoad, then LDRB/
                // LDRH/LDRSB/LDRSH into a non-param destination register
                // chosen by `alloc_i32_scratch`. Pre-fix these wasm ops
                // had no IR handler; the optimizer pipeline left the
                // produced vreg unmapped → defensive panic (or pre-PR-101
                // silent R0 alias).
                Opcode::MemLoadSubword {
                    dest,
                    addr,
                    offset,
                    width,
                    signed,
                } => {
                    let r_addr = get_arm_reg(addr, &vreg_to_arm, &spilled_vregs);
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[r_addr],
                    );
                    vreg_to_arm.insert(dest.0, rd);

                    let base: u32 = 0x20000100;
                    let base_lo = (base & 0xFFFF) as u16;
                    let base_hi = ((base >> 16) & 0xFFFF) as u16;
                    arm_instrs.push(ArmOp::Movw {
                        rd: Reg::R12,
                        imm16: base_lo,
                    });
                    arm_instrs.push(ArmOp::Movt {
                        rd: Reg::R12,
                        imm16: base_hi,
                    });
                    arm_instrs.push(ArmOp::Add {
                        rd: Reg::R12,
                        rn: Reg::R12,
                        op2: Operand2::Reg(r_addr),
                    });
                    let addr_mem = crate::rules::MemAddr::imm(Reg::R12, *offset as i32);
                    let sub_op = match (*width, *signed) {
                        (1, false) => ArmOp::Ldrb { rd, addr: addr_mem },
                        (1, true) => ArmOp::Ldrsb { rd, addr: addr_mem },
                        (2, false) => ArmOp::Ldrh { rd, addr: addr_mem },
                        (2, true) => ArmOp::Ldrsh { rd, addr: addr_mem },
                        // Width 4 is impossible here (caller would use
                        // `Opcode::MemLoad`); fall through to plain Ldr
                        // rather than panicking — that keeps the lowering
                        // total, and the encoder will validate.
                        _ => ArmOp::Ldr { rd, addr: addr_mem },
                    };
                    arm_instrs.push(sub_op);
                    last_result_vreg = Some(dest.0);
                }

                // Sub-word linear memory store (i32.store8, i32.store16,
                // i64.store8/16/32). Generates address math + STRB/STRH/STR.
                Opcode::MemStoreSubword {
                    src,
                    addr,
                    offset,
                    width,
                } => {
                    let r_addr = get_arm_reg(addr, &vreg_to_arm, &spilled_vregs);
                    let r_src = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);

                    let base: u32 = 0x20000100;
                    let base_lo = (base & 0xFFFF) as u16;
                    let base_hi = ((base >> 16) & 0xFFFF) as u16;
                    arm_instrs.push(ArmOp::Movw {
                        rd: Reg::R12,
                        imm16: base_lo,
                    });
                    arm_instrs.push(ArmOp::Movt {
                        rd: Reg::R12,
                        imm16: base_hi,
                    });
                    arm_instrs.push(ArmOp::Add {
                        rd: Reg::R12,
                        rn: Reg::R12,
                        op2: Operand2::Reg(r_addr),
                    });
                    let addr_mem = crate::rules::MemAddr::imm(Reg::R12, *offset as i32);
                    let sub_op = match *width {
                        1 => ArmOp::Strb {
                            rd: r_src,
                            addr: addr_mem,
                        },
                        2 => ArmOp::Strh {
                            rd: r_src,
                            addr: addr_mem,
                        },
                        _ => ArmOp::Str {
                            rd: r_src,
                            addr: addr_mem,
                        },
                    };
                    arm_instrs.push(sub_op);
                }

                // `global.get N` — load global N into a fresh non-param
                // scratch. ARM convention: R9 is the globals base, globals
                // are packed as 4-byte slots.
                Opcode::GlobalGet { dest, idx } => {
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[]);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Ldr {
                        rd,
                        addr: crate::rules::MemAddr::imm(Reg::R9, (*idx as i32) * 4),
                    });
                    last_result_vreg = Some(dest.0);
                }

                // `global.set N` — store the popped i32 to global N.
                Opcode::GlobalSet { src, idx } => {
                    let r_src = get_arm_reg(src, &vreg_to_arm, &spilled_vregs);
                    arm_instrs.push(ArmOp::Str {
                        rd: r_src,
                        addr: crate::rules::MemAddr::imm(Reg::R9, (*idx as i32) * 4),
                    });
                }

                // `memory.size` — current memory size in pages. Convention:
                // R10 holds the memory size word. Emit `MOV dest, R10`.
                Opcode::MemorySize { dest } => {
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[]);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Mov {
                        rd,
                        op2: Operand2::Reg(Reg::R10),
                    });
                    last_result_vreg = Some(dest.0);
                }

                // `memory.grow` — embedded targets have fixed memory; emit
                // a stub that returns -1 (the wasm spec's "grow failed"
                // sentinel). The `delta` is read but discarded.
                Opcode::MemoryGrow { dest, delta } => {
                    let _ = get_arm_reg(delta, &vreg_to_arm, &spilled_vregs);
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[]);
                    vreg_to_arm.insert(dest.0, rd);
                    // mov rd, #-1  →  MOVW rd, #0xFFFF; MOVT rd, #0xFFFF
                    arm_instrs.push(ArmOp::Movw { rd, imm16: 0xFFFF });
                    arm_instrs.push(ArmOp::Movt { rd, imm16: 0xFFFF });
                    last_result_vreg = Some(dest.0);
                }
            }

            // Track WASM operand value stack for correct br_if semantics.
            // br_if pops the condition; the value underneath is the result.
            match &inst.opcode {
                // Binary ops: consume 2, produce 1
                Opcode::Add { dest, .. }
                | Opcode::Sub { dest, .. }
                | Opcode::Mul { dest, .. }
                | Opcode::DivS { dest, .. }
                | Opcode::DivU { dest, .. }
                | Opcode::RemS { dest, .. }
                | Opcode::RemU { dest, .. }
                | Opcode::And { dest, .. }
                | Opcode::Or { dest, .. }
                | Opcode::Xor { dest, .. }
                | Opcode::Shl { dest, .. }
                | Opcode::ShrS { dest, .. }
                | Opcode::ShrU { dest, .. }
                | Opcode::Rotl { dest, .. }
                | Opcode::Rotr { dest, .. }
                | Opcode::Eq { dest, .. }
                | Opcode::Ne { dest, .. }
                | Opcode::LtS { dest, .. }
                | Opcode::LtU { dest, .. }
                | Opcode::LeS { dest, .. }
                | Opcode::LeU { dest, .. }
                | Opcode::GtS { dest, .. }
                | Opcode::GtU { dest, .. }
                | Opcode::GeS { dest, .. }
                | Opcode::GeU { dest, .. } => {
                    value_stack.pop();
                    value_stack.pop();
                    value_stack.push(dest.0);
                }
                // Unary ops: consume 1, produce 1
                Opcode::Clz { dest, .. }
                | Opcode::Ctz { dest, .. }
                | Opcode::Popcnt { dest, .. }
                | Opcode::Eqz { dest, .. }
                | Opcode::Copy { dest, .. }
                | Opcode::Extend8S { dest, .. }
                | Opcode::Extend16S { dest, .. } => {
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
                Reg::R0 => 0,
                Reg::R1 => 1,
                Reg::R2 => 2,
                Reg::R3 => 3,
                Reg::R4 => 4,
                Reg::R5 => 5,
                Reg::R6 => 6,
                Reg::R7 => 7,
                Reg::R8 => 8,
                Reg::R9 => 9,
                Reg::R10 => 10,
                Reg::R11 => 11,
                Reg::R12 => 12,
                Reg::SP => 13,
                Reg::LR => 14,
                Reg::PC => 15,
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
                ArmOp::LslReg { .. }
                | ArmOp::LsrReg { .. }
                | ArmOp::AsrReg { .. }
                | ArmOp::RorReg { .. }
                | ArmOp::Rsb { .. } => 4,
                // MUL, MLS, SDIV, UDIV are always 32-bit Thumb-2
                ArmOp::Mul { .. } | ArmOp::Mls { .. } | ArmOp::Sdiv { .. } | ArmOp::Udiv { .. } => {
                    4
                }
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
                    if rd_bits < 8 && base_bits < 8 && (offset & 0x3) == 0 && offset <= 124 {
                        2
                    } else {
                        4
                    }
                }
                ArmOp::Str { rd, addr } => {
                    let rd_bits = reg_num(rd);
                    let base_bits = reg_num(&addr.base);
                    let offset = addr.offset as u32;
                    if rd_bits < 8 && base_bits < 8 && (offset & 0x3) == 0 && offset <= 124 {
                        2
                    } else {
                        4
                    }
                }
                // BL is always 32-bit
                ArmOp::Bl { .. } => 4,
                // MOV with high register (R8-R15) or large immediate needs MOVW (4 bytes)
                ArmOp::Mov {
                    rd,
                    op2: Operand2::Imm(v),
                } if reg_num(rd) > 7 || *v > 255 || *v < 0 => 4,
                ArmOp::Mov { .. } => 2,
                // SUB/ADD with high registers need 32-bit encoding
                ArmOp::Sub {
                    rd,
                    rn,
                    op2: Operand2::Reg(rm),
                } if reg_num(rd) > 7 || reg_num(rn) > 7 || reg_num(rm) > 7 => 4,
                ArmOp::Add {
                    rd,
                    rn,
                    op2: Operand2::Reg(rm),
                } if reg_num(rd) > 7 || reg_num(rn) > 7 || reg_num(rm) > 7 => 4,
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
                    arm_instrs[branch_arm_idx] = ArmOp::BOffset {
                        offset: halfword_offset,
                    };
                }
            }
        }

        // Ensure the return value is in R0 (i32 result) or R0:R1 (i64 result).
        //
        // Pre-fix, every i64 op pinned its result at R0:R1 so this could be a
        // no-op for is_i64_result. After the fix, the result pair may live in
        // any callee-saved pair (R4:R5..R10:R11), and we need an explicit move.
        // The order matters: copy hi → R1 first, then lo → R0, so we don't
        // clobber the lo value if the source happens to be R1.
        if is_i64_result {
            // Resolve the lo half from vreg_to_arm.
            let lo_reg = last_result_vreg.and_then(|v| vreg_to_arm.get(&v).copied());
            // Resolve the hi half: prefer an explicit vreg id, else fall back to
            // the physical reg stash used by Clz/Ctz/Popcnt.
            let hi_reg = last_result_vreg_hi
                .and_then(|v| vreg_to_arm.get(&v).copied())
                .or(last_result_vreg_hi_reg);

            if let (Some(lo), Some(hi)) = (lo_reg, hi_reg) {
                // Move hi first (so we don't clobber lo if hi's source is R1).
                if hi != Reg::R1 {
                    arm_instrs.push(ArmOp::Mov {
                        rd: Reg::R1,
                        op2: Operand2::Reg(hi),
                    });
                }
                // Now move lo. If lo was R1 originally, it just got smashed by
                // the hi-move above; but R1's prior contents are now in R1
                // (the hi value), so we'd actually have wanted to save lo first.
                // Handle that case explicitly: save lo to R12 (IP scratch) first.
                if lo == Reg::R1 && hi != Reg::R1 {
                    // lo was in R1, which we just overwrote. We can't recover it
                    // unless we saved earlier. The clean fix: detect this
                    // arrangement up front. For now, swap order via R12.
                    // (This is reached only on bizarre regalloc choices; the
                    // common case is lo in R4..R10, which doesn't hit it.)
                    arm_instrs.pop(); // remove the hi-move we just emitted
                    arm_instrs.push(ArmOp::Mov {
                        rd: Reg::R12,
                        op2: Operand2::Reg(lo),
                    });
                    if hi != Reg::R1 {
                        arm_instrs.push(ArmOp::Mov {
                            rd: Reg::R1,
                            op2: Operand2::Reg(hi),
                        });
                    }
                    arm_instrs.push(ArmOp::Mov {
                        rd: Reg::R0,
                        op2: Operand2::Reg(Reg::R12),
                    });
                } else if lo != Reg::R0 {
                    arm_instrs.push(ArmOp::Mov {
                        rd: Reg::R0,
                        op2: Operand2::Reg(lo),
                    });
                }
            } else if let Some(lo) = lo_reg
                && lo != Reg::R0
            {
                // Hi is unknown — fall back to single-register move (caller of
                // this function may have set is_i64_result without populating
                // the hi tracker; preserve old behaviour rather than crash).
                arm_instrs.push(ArmOp::Mov {
                    rd: Reg::R0,
                    op2: Operand2::Reg(lo),
                });
            }
        } else if let Some(result_vreg) = last_result_vreg
            && let Some(&result_reg) = vreg_to_arm.get(&result_vreg)
            && result_reg != Reg::R0
        {
            arm_instrs.push(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Reg(result_reg),
            });
        }

        // If any registers were spilled, insert stack frame setup/teardown.
        // Prologue: SUB SP, SP, #frame_size at the beginning
        // Epilogue: ADD SP, SP, #frame_size before every BX LR
        if !spilled_vregs.is_empty() {
            // Round frame size up to 8-byte alignment (AAPCS requirement)
            let frame_size = ((next_spill_offset as u32 + 7) & !7) as i32;
            // Insert prologue at position 0
            arm_instrs.insert(
                0,
                ArmOp::Sub {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    op2: Operand2::Imm(frame_size),
                },
            );
            // Add epilogue before each BX LR (scan for existing returns)
            let mut i = 1; // skip the prologue we just inserted
            while i < arm_instrs.len() {
                if matches!(&arm_instrs[i], ArmOp::Bx { rm: Reg::LR }) {
                    arm_instrs.insert(
                        i,
                        ArmOp::Add {
                            rd: Reg::SP,
                            rn: Reg::SP,
                            op2: Operand2::Imm(frame_size),
                        },
                    );
                    i += 2; // skip both the ADD and the BX
                } else {
                    i += 1;
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
            WasmOp::LocalGet(0), // condition
            WasmOp::If,
            WasmOp::I32Const(10), // then value
            WasmOp::Else,
            WasmOp::I32Const(20), // else value
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Should be transformed to: val1, val2, cond, Select
        assert_eq!(preprocessed.len(), 4);
        assert_eq!(preprocessed[0], WasmOp::I32Const(10)); // then value
        assert_eq!(preprocessed[1], WasmOp::I32Const(20)); // else value
        assert_eq!(preprocessed[2], WasmOp::LocalGet(0)); // condition
        assert_eq!(preprocessed[3], WasmOp::Select);
    }

    #[test]
    fn test_nested_if_else_to_nested_select() {
        let bridge = OptimizerBridge::new();

        // Pattern: outer_cond, If, inner_cond, If, val1, Else, val2, End, Else, val3, End
        // Should become two nested selects
        let wasm_ops = vec![
            WasmOp::LocalGet(0), // outer condition
            WasmOp::If,
            WasmOp::LocalGet(1), // inner condition
            WasmOp::If,
            WasmOp::I32Const(10), // val1 (both true)
            WasmOp::Else,
            WasmOp::I32Const(20), // val2 (outer true, inner false)
            WasmOp::End,
            WasmOp::Else,
            WasmOp::I32Const(30), // val3 (outer false)
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // The outer condition (LocalGet 0 → R0) must be saved before the inner select
        // runs, because the inner select overwrites R0 with its result.
        // Expected: save outer_cond, inner select, then outer select using saved cond.
        // outer_cond, LocalSet(255), val1, val2, inner_cond, Select, val3, LocalGet(255), Select
        assert_eq!(preprocessed.len(), 9);
        assert_eq!(preprocessed[0], WasmOp::LocalGet(0)); // outer condition (to save)
        assert_eq!(preprocessed[1], WasmOp::LocalSet(255)); // save to synthetic local
        assert_eq!(preprocessed[2], WasmOp::I32Const(10)); // val1
        assert_eq!(preprocessed[3], WasmOp::I32Const(20)); // val2
        assert_eq!(preprocessed[4], WasmOp::LocalGet(1)); // inner condition
        assert_eq!(preprocessed[5], WasmOp::Select); // inner select
        assert_eq!(preprocessed[6], WasmOp::I32Const(30)); // val3
        assert_eq!(preprocessed[7], WasmOp::LocalGet(255)); // load saved outer condition
        assert_eq!(preprocessed[8], WasmOp::Select); // outer select
    }

    #[test]
    fn test_br_if_block_to_select() {
        let bridge = OptimizerBridge::new();

        // Pattern: Block, val1, cond, BrIf(0), Drop, val2, End
        // Should become: val1, val2, cond, Select
        let wasm_ops = vec![
            WasmOp::Block,
            WasmOp::I32Const(10), // val1 (early exit value)
            WasmOp::LocalGet(0),  // condition
            WasmOp::BrIf(0),      // if cond, exit with val1
            WasmOp::Drop,
            WasmOp::I32Const(20), // val2 (fallthrough value)
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Should be transformed to: val1, val2, cond, Select
        assert_eq!(preprocessed.len(), 4);
        assert_eq!(preprocessed[0], WasmOp::I32Const(10)); // val1
        assert_eq!(preprocessed[1], WasmOp::I32Const(20)); // val2
        assert_eq!(preprocessed[2], WasmOp::LocalGet(0)); // condition
        assert_eq!(preprocessed[3], WasmOp::Select);
    }

    #[test]
    fn test_br_if_block_with_local_values() {
        let bridge = OptimizerBridge::new();

        // br_if pattern with LocalGet values
        let wasm_ops = vec![
            WasmOp::Block,
            WasmOp::LocalGet(1), // val1 from local
            WasmOp::LocalGet(0), // condition
            WasmOp::BrIf(0),
            WasmOp::Drop,
            WasmOp::LocalGet(2), // val2 from local
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Should be transformed to: val1, val2, cond, Select
        assert_eq!(preprocessed.len(), 4);
        assert_eq!(preprocessed[0], WasmOp::LocalGet(1)); // val1
        assert_eq!(preprocessed[1], WasmOp::LocalGet(2)); // val2
        assert_eq!(preprocessed[2], WasmOp::LocalGet(0)); // condition
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
            WasmOp::I32Add, // Complex then block (not a simple value)
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

    // =========================================================================
    // PR #86 patch coverage: ir_to_arm i64 regalloc respects AAPCS params.
    //
    // Pre-fix, the i64 lowering hardcoded R0:R1 / R2:R3 for the destination
    // pair which clobbered incoming AAPCS arg regs. The fix routes every
    // i64 dest through alloc_i64_pair so callee-saved (R4..R11) pairs are
    // preferred when params are still live. These tests exercise that path.
    // =========================================================================

    #[test]
    fn test_ir_to_arm_i64_const_with_params_does_not_clobber_r0_r3() {
        // Pretend the function has 4 i32 params live in R0..R3, and emit
        // an I64Const. The new alloc_i64_pair must pick a callee-saved pair
        // (R4..R11), not R0:R1 — for the I64Const itself. The epilogue is
        // ALLOWED to copy the result into R0:R1 (that's the AAPCS return
        // convention), so we exclude trailing Mov-to-R0/R1 with a
        // callee-saved source from the assertion.
        let bridge = OptimizerBridge::new();
        let instrs = vec![Instruction {
            id: 0,
            opcode: Opcode::I64Const {
                dest_lo: OptReg(100),
                dest_hi: OptReg(101),
                value: 0x1122_3344_5566_7788,
            },
            block_id: 0,
            is_dead: false,
        }];
        let arm = bridge.ir_to_arm(&instrs, 4);
        // The I64Const itself is encoded with Movw/Movt — those MUST NOT
        // target R0..R3. The epilogue Mov-into-R0/R1 is part of the AAPCS
        // return convention and is correct.
        for op in &arm {
            if let ArmOp::Movw { rd, .. } | ArmOp::Movt { rd, .. } = op {
                let is_param = matches!(
                    rd,
                    crate::rules::Reg::R0
                        | crate::rules::Reg::R1
                        | crate::rules::Reg::R2
                        | crate::rules::Reg::R3
                );
                assert!(
                    !is_param,
                    "I64Const with num_params=4 clobbered AAPCS param via Movw/Movt: {:?}",
                    op
                );
            }
        }
        // And we should have produced *some* code that loads the value.
        assert!(!arm.is_empty(), "I64Const should emit instructions");
    }

    #[test]
    fn test_ir_to_arm_i64_const_zero_params_can_use_callee_saved() {
        // With zero params, alloc_i64_pair should still pick a callee-saved
        // pair (R4:R5 first), since param_reserved_regs is empty.
        let bridge = OptimizerBridge::new();
        let instrs = vec![Instruction {
            id: 0,
            opcode: Opcode::I64Const {
                dest_lo: OptReg(0),
                dest_hi: OptReg(1),
                value: 0xdead_beefu64 as i64,
            },
            block_id: 0,
            is_dead: false,
        }];
        let arm = bridge.ir_to_arm(&instrs, 0);
        assert!(!arm.is_empty());
    }

    #[test]
    fn test_ir_to_arm_i64_add_uses_operand_regs() {
        // Build IR that loads two i64 params (R0:R1 and R2:R3 via I64Load
        // with addr=0/1 and num_params >= 4), then adds them. The fix should
        // emit Adds/Adc that use the operand registers, NOT hardcoded ones.
        let bridge = OptimizerBridge::new();
        let instrs = vec![
            // I64Load addr=0 → R0:R1
            Instruction {
                id: 0,
                opcode: Opcode::I64Load {
                    dest_lo: OptReg(10),
                    dest_hi: OptReg(11),
                    addr: 0,
                },
                block_id: 0,
                is_dead: false,
            },
            // I64Load addr=1 → R2:R3
            Instruction {
                id: 1,
                opcode: Opcode::I64Load {
                    dest_lo: OptReg(12),
                    dest_hi: OptReg(13),
                    addr: 1,
                },
                block_id: 0,
                is_dead: false,
            },
            // I64Add of the two pairs.
            Instruction {
                id: 2,
                opcode: Opcode::I64Add {
                    dest_lo: OptReg(14),
                    dest_hi: OptReg(15),
                    src1_lo: OptReg(10),
                    src1_hi: OptReg(11),
                    src2_lo: OptReg(12),
                    src2_hi: OptReg(13),
                },
                block_id: 0,
                is_dead: false,
            },
        ];
        let arm = bridge.ir_to_arm(&instrs, 4);
        // We must see at least one Adds and at least one Adc — that's the
        // characteristic shape of a 64-bit add on 32-bit ARM.
        let has_adds = arm.iter().any(|op| matches!(op, ArmOp::Adds { .. }));
        let has_adc = arm.iter().any(|op| matches!(op, ArmOp::Adc { .. }));
        assert!(has_adds, "i64.add should emit ADDS for the low half");
        assert!(has_adc, "i64.add should emit ADC for the high half");
    }

    #[test]
    fn test_ir_to_arm_i64_sub_emits_subs_sbc() {
        // I64Sub characteristic: SUBS for low + SBC for high.
        let bridge = OptimizerBridge::new();
        let instrs = vec![
            Instruction {
                id: 0,
                opcode: Opcode::I64Const {
                    dest_lo: OptReg(0),
                    dest_hi: OptReg(1),
                    value: 100,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::I64Const {
                    dest_lo: OptReg(2),
                    dest_hi: OptReg(3),
                    value: 50,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::I64Sub {
                    dest_lo: OptReg(4),
                    dest_hi: OptReg(5),
                    src1_lo: OptReg(0),
                    src1_hi: OptReg(1),
                    src2_lo: OptReg(2),
                    src2_hi: OptReg(3),
                },
                block_id: 0,
                is_dead: false,
            },
        ];
        let arm = bridge.ir_to_arm(&instrs, 0);
        let has_subs = arm.iter().any(|op| matches!(op, ArmOp::Subs { .. }));
        let has_sbc = arm.iter().any(|op| matches!(op, ArmOp::Sbc { .. }));
        assert!(has_subs, "i64.sub should emit SUBS for the low half");
        assert!(has_sbc, "i64.sub should emit SBC for the high half");
    }

    #[test]
    fn test_ir_to_arm_i64_or_emits_two_orr() {
        // I64Or → two ORR (low-half and high-half).
        let bridge = OptimizerBridge::new();
        let instrs = vec![
            Instruction {
                id: 0,
                opcode: Opcode::I64Const {
                    dest_lo: OptReg(0),
                    dest_hi: OptReg(1),
                    value: 0x0F,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::I64Const {
                    dest_lo: OptReg(2),
                    dest_hi: OptReg(3),
                    value: 0xF0,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::I64Or {
                    dest_lo: OptReg(4),
                    dest_hi: OptReg(5),
                    src1_lo: OptReg(0),
                    src1_hi: OptReg(1),
                    src2_lo: OptReg(2),
                    src2_hi: OptReg(3),
                },
                block_id: 0,
                is_dead: false,
            },
        ];
        let arm = bridge.ir_to_arm(&instrs, 0);
        let orr_count = arm
            .iter()
            .filter(|op| matches!(op, ArmOp::Orr { .. }))
            .count();
        assert!(orr_count >= 2, "i64.or should emit ORR twice (lo and hi)");
    }

    #[test]
    fn test_ir_to_arm_i64_const_with_2_params_uses_first_callee_saved() {
        // With num_params=2, R0/R1 are reserved. alloc_i64_pair starts from
        // (R4,R5) which is unconditionally free here.
        let bridge = OptimizerBridge::new();
        let instrs = vec![Instruction {
            id: 0,
            opcode: Opcode::I64Const {
                dest_lo: OptReg(0),
                dest_hi: OptReg(1),
                value: 1,
            },
            block_id: 0,
            is_dead: false,
        }];
        let arm = bridge.ir_to_arm(&instrs, 2);
        // Should not have written to R0 or R1 (the reserved param regs).
        for op in &arm {
            if let ArmOp::Mov {
                rd: crate::rules::Reg::R0,
                ..
            }
            | ArmOp::Mov {
                rd: crate::rules::Reg::R1,
                ..
            }
            | ArmOp::Movw {
                rd: crate::rules::Reg::R0,
                ..
            }
            | ArmOp::Movw {
                rd: crate::rules::Reg::R1,
                ..
            }
            | ArmOp::Movt {
                rd: crate::rules::Reg::R0,
                ..
            }
            | ArmOp::Movt {
                rd: crate::rules::Reg::R1,
                ..
            } = op
            {
                // The i64-result epilogue moves the result into R0:R1 AT THE
                // END — so a single Mov-to-R0 from the result pair is fine,
                // but Movw/Movt-to-R0/R1 means the I64Const itself clobbered
                // the param. Filter out the epilogue Movs by looking at
                // their position and source pattern: an epilogue Mov uses
                // Operand2::Reg(callee-saved). For this test, we simply
                // assert no Movw/Movt targets the reserved set.
                if matches!(op, ArmOp::Movw { .. } | ArmOp::Movt { .. }) {
                    panic!(
                        "I64Const with num_params=2 clobbered AAPCS register: {:?}",
                        op
                    );
                }
            }
        }
    }

    // ========================================================================
    // Issue #94: u64-packed FFI return — direct hi/lo extraction
    // ========================================================================
    //
    // The canonical wasm sequence emitted by Rust → wasm for extracting the
    // upper 32 bits of a u64-packed return value is:
    //
    //     local.get $packed_i64    ;; the packed u64 in an i64 local
    //     i64.const 32
    //     i64.shr_u
    //     i32.wrap_i64
    //
    // Pre-fix, synth lowered this to ~38 bytes of generic 64-bit shift
    // emulation. After the fix, it should collapse to a single
    // `mov rd_hi, #0` plus a vreg rename — the hi half of the input pair
    // is already in a register.

    #[cfg(test)]
    fn count_arm_byte_size(arm: &[ArmOp]) -> usize {
        use crate::rules::Operand2;
        // Mirror the size table in OptimizerBridge::estimate_arm_byte_size
        // for the ops we care about in these tests. Keep this small and
        // local so the tests don't depend on encoder reachability — only
        // a regression in the optimizer bridge should change these counts.
        arm.iter()
            .map(|op| match op {
                ArmOp::I64ShrU { .. } | ArmOp::I64Shl { .. } => 38,
                ArmOp::I64ShrS { .. } => 40,
                ArmOp::And { .. }
                | ArmOp::Orr { .. }
                | ArmOp::Eor { .. }
                | ArmOp::Asr { .. }
                | ArmOp::Adc { .. }
                | ArmOp::Sbc { .. } => 4,
                ArmOp::Mov { rd, op2 } => {
                    // 16-bit Thumb encoding for MOV rd, #imm8 is available
                    // when rd is a low register (R0..R7) and the immediate
                    // fits in 8 bits. MOV rd, rm (register form) is 2 bytes
                    // for low-register destinations.
                    let rd_n = reg_idx(*rd);
                    match op2 {
                        Operand2::Imm(v) if rd_n < 8 && (0..=255).contains(v) => 2,
                        Operand2::Reg(_) if rd_n < 8 => 2,
                        _ => 4,
                    }
                }
                ArmOp::Movw { .. } | ArmOp::Movt { .. } => 4,
                _ => 4,
            })
            .sum()
    }

    #[cfg(test)]
    fn reg_idx(r: crate::rules::Reg) -> u32 {
        match r {
            crate::rules::Reg::R0 => 0,
            crate::rules::Reg::R1 => 1,
            crate::rules::Reg::R2 => 2,
            crate::rules::Reg::R3 => 3,
            crate::rules::Reg::R4 => 4,
            crate::rules::Reg::R5 => 5,
            crate::rules::Reg::R6 => 6,
            crate::rules::Reg::R7 => 7,
            crate::rules::Reg::R8 => 8,
            crate::rules::Reg::R9 => 9,
            crate::rules::Reg::R10 => 10,
            crate::rules::Reg::R11 => 11,
            crate::rules::Reg::R12 => 12,
            crate::rules::Reg::SP => 13,
            crate::rules::Reg::LR => 14,
            crate::rules::Reg::PC => 15,
        }
    }

    /// Print before/after sizes for the canonical issue #94 pattern. This
    /// "test" is informational — it passes regardless and is intended to be
    /// run with `cargo test ... -- --nocapture` to surface the win in CI logs.
    #[test]
    fn test_issue94_size_demo() {
        let bridge = OptimizerBridge::new();

        // After-fix: shift-by-32 hits the constant-aware fast path.
        let after_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I64Const(32),
            WasmOp::I64ShrU,
            WasmOp::I32WrapI64,
        ];
        let (instrs, _, _) = bridge.optimize_full(&after_ops).unwrap();
        let arm_after = bridge.ir_to_arm(&instrs, 2);
        let bytes_after = count_arm_byte_size(&arm_after);

        // Pre-fix proxy: shift-by-7 takes the generic ArmOp::I64ShrU path,
        // which is byte-identical to the unoptimized shift-by-32 emit.
        let before_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I64Const(7),
            WasmOp::I64ShrU,
            WasmOp::I32WrapI64,
        ];
        let (instrs, _, _) = bridge.optimize_full(&before_ops).unwrap();
        let arm_before = bridge.ir_to_arm(&instrs, 2);
        let bytes_before = count_arm_byte_size(&arm_before);

        println!(
            "\n[issue #94 demo] hi32 extract: BEFORE = {} bytes, AFTER = {} bytes (saved {})",
            bytes_before,
            bytes_after,
            bytes_before.saturating_sub(bytes_after)
        );
        println!("[issue #94 demo] AFTER ops emitted = {}", arm_after.len());
        for op in &arm_after {
            println!("[issue #94 demo]   {:?}", op);
        }
    }

    /// Issue #94: `i64.shr_u 32` followed by `i32.wrap_i64` should NOT emit
    /// a runtime 64-bit shift. The hi half of the source pair is already in
    /// a register; we just need to rename + zero out the (now-unused) hi half.
    #[test]
    fn test_issue94_shr_u_32_lowers_to_register_rename() {
        let bridge = OptimizerBridge::new();
        // (i64) -> i32, body = `local.get 0; i64.const 32; i64.shr_u; i32.wrap_i64`
        let wasm_ops = vec![
            WasmOp::LocalGet(0),  // i64 param in R0:R1
            WasmOp::I64Const(32), // shift amount
            WasmOp::I64ShrU,
            WasmOp::I32WrapI64,
        ];

        let (instrs, _, _) = bridge.optimize_full(&wasm_ops).unwrap();
        // num_params = 1 (one i64 param occupies R0:R1 per AAPCS — but we
        // pass 2 to ir_to_arm because each i64 counts as two AAPCS slots
        // in the codegen's accounting).
        let arm = bridge.ir_to_arm(&instrs, 2);

        // After fix: NO ArmOp::I64ShrU should be emitted. The 38-byte runtime
        // shift sequence is the bug we're fixing.
        let has_runtime_shift = arm.iter().any(|op| matches!(op, ArmOp::I64ShrU { .. }));
        assert!(
            !has_runtime_shift,
            "i64.shr_u with constant 32 should NOT emit ArmOp::I64ShrU; got: {:#?}",
            arm
        );

        // Total emitted byte size should drop well below the 38-byte runtime
        // shift alone. The pre-fix lower bound was 38 bytes for the shift
        // plus several bytes for the constant-32 load and epilogue moves.
        let bytes = count_arm_byte_size(&arm);
        assert!(
            bytes < 30,
            "expected < 30 bytes after fix; got {} bytes: {:#?}",
            bytes,
            arm
        );
    }

    /// Issue #94: signed variant. `i64.shr_s 32` extracts the upper 32 bits
    /// just like `shr_u`, but the result is sign-extended into the (still-
    /// unused) hi half via a single `asr rd_hi, rn_hi, #31`.
    #[test]
    fn test_issue94_shr_s_32_lowers_to_register_rename_with_sign_extend() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I64Const(32),
            WasmOp::I64ShrS,
            WasmOp::I32WrapI64,
        ];

        let (instrs, _, _) = bridge.optimize_full(&wasm_ops).unwrap();
        let arm = bridge.ir_to_arm(&instrs, 2);

        let has_runtime_shift = arm.iter().any(|op| matches!(op, ArmOp::I64ShrS { .. }));
        assert!(
            !has_runtime_shift,
            "i64.shr_s with constant 32 should NOT emit ArmOp::I64ShrS; got: {:#?}",
            arm
        );

        // We expect exactly one ASR (for the sign-extend of the hi half).
        let asr_count = arm
            .iter()
            .filter(|op| matches!(op, ArmOp::Asr { .. }))
            .count();
        assert_eq!(
            asr_count, 1,
            "expected one ASR for sign extend; got: {:#?}",
            arm
        );

        let bytes = count_arm_byte_size(&arm);
        assert!(
            bytes < 30,
            "expected < 30 bytes after fix; got {} bytes: {:#?}",
            bytes,
            arm
        );
    }

    /// Issue #94: `i64.and 0xFFFFFFFF` (lo32 mask) followed by `i32.wrap_i64`
    /// should NOT emit two AND.W instructions; the lo half is unchanged and
    /// the hi half is zero. Becomes a register rename + `mov rd_hi, #0`.
    #[test]
    fn test_issue94_and_mask_low32_lowers_to_register_rename() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I64Const(0xFFFF_FFFF),
            WasmOp::I64And,
            WasmOp::I32WrapI64,
        ];

        let (instrs, _, _) = bridge.optimize_full(&wasm_ops).unwrap();
        let arm = bridge.ir_to_arm(&instrs, 2);

        // After fix: at most one AND should remain, and it shouldn't be the
        // pair of ANDs from the generic i64.and lowering. (We allow zero ANDs
        // because the lo half is unchanged via vreg rename.)
        let and_count = arm
            .iter()
            .filter(|op| matches!(op, ArmOp::And { .. }))
            .count();
        assert!(
            and_count == 0,
            "i64.and 0xFFFFFFFF should not emit any AND.W; got {} ANDs in {:#?}",
            and_count,
            arm
        );
    }

    /// Sanity: a non-32 shift constant should still emit the full ArmOp::I64ShrU
    /// (we don't want to silently regress the general case).
    #[test]
    fn test_issue94_shr_u_non_32_still_emits_runtime_shift() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I64Const(7), // not 32 — generic path
            WasmOp::I64ShrU,
            WasmOp::I32WrapI64,
        ];

        let (instrs, _, _) = bridge.optimize_full(&wasm_ops).unwrap();
        let arm = bridge.ir_to_arm(&instrs, 2);

        let has_runtime_shift = arm.iter().any(|op| matches!(op, ArmOp::I64ShrU { .. }));
        assert!(
            has_runtime_shift,
            "i64.shr_u with non-32 constant must still emit ArmOp::I64ShrU; got: {:#?}",
            arm
        );
    }

    /// Direct IR-level test (independent of wasm_to_ir's vreg numbering):
    /// construct the IR by hand and verify the lowering eliminates I64ShrU.
    #[test]
    fn test_issue94_ir_level_shr_u_32() {
        let bridge = OptimizerBridge::new();
        // Pattern:
        //   v0:v1 = I64Const 0x0123_4567_89AB_CDEF
        //   v2:v3 = I64Const 32
        //   v4:v5 = I64ShrU v0:v1, v2:v3
        //
        // Expected: no ArmOp::I64ShrU is emitted; v4 maps to the same ARM
        // register as v1 (the hi of the source pair).
        let instrs = vec![
            Instruction {
                id: 0,
                opcode: Opcode::I64Const {
                    dest_lo: OptReg(0),
                    dest_hi: OptReg(1),
                    value: 0x0123_4567_89AB_CDEFi64,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::I64Const {
                    dest_lo: OptReg(2),
                    dest_hi: OptReg(3),
                    value: 32,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 4,
                opcode: Opcode::I64ShrU {
                    dest_lo: OptReg(4),
                    dest_hi: OptReg(5),
                    src1_lo: OptReg(0),
                    src1_hi: OptReg(1),
                    src2_lo: OptReg(2),
                    src2_hi: OptReg(3),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let arm = bridge.ir_to_arm(&instrs, 0);
        let has_runtime_shift = arm.iter().any(|op| matches!(op, ArmOp::I64ShrU { .. }));
        assert!(
            !has_runtime_shift,
            "IR-level: i64.shr_u with constant 32 should NOT emit ArmOp::I64ShrU; got: {:#?}",
            arm
        );
    }
}
