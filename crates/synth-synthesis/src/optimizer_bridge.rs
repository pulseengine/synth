//! Optimizer Bridge - Integrates optimization passes with instruction selection
//!
//! This module bridges the synthesis engine with the optimization framework,
//! allowing WASM-level and IR-level optimizations before final code generation.

use synth_cfg::{Cfg, CfgBuilder};
use synth_opt::{
    AlgebraicSimplification, CommonSubexpressionElimination, ConstantFolding,
    DeadCodeElimination, Instruction, Opcode, PassManager, PeepholeOptimization, Reg as OptReg,
};
use crate::rules::WasmOp;
use synth_core::Result;

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

    /// Convert WASM operations to optimization IR
    fn wasm_to_ir(&self, wasm_ops: &[WasmOp]) -> (Vec<Instruction>, Cfg) {
        let mut builder = CfgBuilder::new();
        let mut instructions = Vec::new();
        let mut inst_id: usize = 0;

        for wasm_op in wasm_ops {
            builder.add_instruction();

            let opcode = match wasm_op {
                WasmOp::I32Const(val) => Opcode::Const {
                    dest: OptReg(inst_id as u32),
                    value: *val,
                },
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
                WasmOp::LocalGet(idx) => Opcode::Load {
                    dest: OptReg(inst_id as u32),
                    addr: *idx as u32,
                },
                WasmOp::LocalSet(idx) => Opcode::Store {
                    src: OptReg(inst_id.saturating_sub(1) as u32),
                    addr: *idx as u32,
                },
                _ => Opcode::Nop, // Fallback for unsupported ops
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

    /// Optimize WASM operation sequence
    pub fn optimize(&self, wasm_ops: &[WasmOp]) -> Result<OptimizationStats> {
        if wasm_ops.is_empty() {
            return Ok(OptimizationStats::default());
        }

        // Convert to IR
        let (mut instructions, mut cfg) = self.wasm_to_ir(wasm_ops);

        // Build optimization pipeline
        let mut manager = PassManager::new().with_max_iterations(self.config.max_iterations);

        let mut passes_added = 0;

        if self.config.enable_peephole {
            let pass = if self.config.verbose {
                PeepholeOptimization::new().with_verbose()
            } else {
                PeepholeOptimization::new()
            };
            manager = manager.add_pass(pass);
            passes_added += 1;
        }

        if self.config.enable_constant_folding {
            let pass = if self.config.verbose {
                ConstantFolding::new().with_verbose()
            } else {
                ConstantFolding::new()
            };
            manager = manager.add_pass(pass);
            passes_added += 1;
        }

        if self.config.enable_algebraic {
            let pass = if self.config.verbose {
                AlgebraicSimplification::new().with_verbose()
            } else {
                AlgebraicSimplification::new()
            };
            manager = manager.add_pass(pass);
            passes_added += 1;
        }

        if self.config.enable_cse {
            let pass = if self.config.verbose {
                CommonSubexpressionElimination::new().with_verbose()
            } else {
                CommonSubexpressionElimination::new()
            };
            manager = manager.add_pass(pass);
            passes_added += 1;
        }

        if self.config.enable_dce {
            let pass = if self.config.verbose {
                DeadCodeElimination::new().with_verbose()
            } else {
                DeadCodeElimination::new()
            };
            manager = manager.add_pass(pass);
            passes_added += 1;
        }

        // Run optimizations
        let result = manager.run(&mut cfg, &mut instructions);

        Ok(OptimizationStats {
            removed: result.removed_count,
            modified: result.modified_count,
            added: result.added_count,
            passes_run: passes_added,
        })
    }

    /// Get the current configuration
    pub fn config(&self) -> &OptimizationConfig {
        &self.config
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
        let wasm_ops = vec![
            WasmOp::I32Const(10),
            WasmOp::I32Const(20),
            WasmOp::I32Add,
        ];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Should have run optimizations
        assert!(stats.passes_run > 0);
    }

    #[test]
    fn test_optimizer_bridge_disabled() {
        let bridge = OptimizerBridge::with_config(OptimizationConfig::none());
        let wasm_ops = vec![
            WasmOp::I32Const(10),
            WasmOp::I32Const(20),
            WasmOp::I32Add,
        ];

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
}
