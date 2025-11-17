//! Optimization passes for Synth compiler
//!
//! This crate provides optimization passes that improve generated code quality.
//!
//! ## Pass Types
//!
//! - **Analysis Passes**: Gather information without modifying code
//! - **Transform Passes**: Modify code to improve quality
//! - **Cleanup Passes**: Remove dead/redundant code
//!
//! ## Available Passes
//!
//! - Dead Code Elimination (DCE)
//! - Constant Folding
//! - Common Subexpression Elimination (CSE)
//! - Loop-Invariant Code Motion (LICM)

use std::collections::{HashMap, HashSet};
use synth_cfg::{Cfg, BlockId};

/// Optimization pass trait
pub trait OptimizationPass {
    /// Name of this pass
    fn name(&self) -> &'static str;

    /// Run the optimization pass
    fn run(&mut self, cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult;
}

/// Result of an optimization pass
#[derive(Debug, Clone)]
pub struct OptResult {
    /// Whether any changes were made
    pub changed: bool,

    /// Number of instructions removed
    pub removed_count: usize,

    /// Number of instructions added
    pub added_count: usize,

    /// Number of instructions modified
    pub modified_count: usize,
}

impl OptResult {
    pub fn no_change() -> Self {
        Self {
            changed: false,
            removed_count: 0,
            added_count: 0,
            modified_count: 0,
        }
    }

    pub fn merge(&mut self, other: OptResult) {
        self.changed |= other.changed;
        self.removed_count += other.removed_count;
        self.added_count += other.added_count;
        self.modified_count += other.modified_count;
    }
}

/// Instruction placeholder (would be actual IR in real implementation)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instruction {
    pub id: usize,
    pub opcode: Opcode,
    pub block_id: BlockId,
    pub is_dead: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Opcode {
    Nop,
    Add { dest: Reg, src1: Reg, src2: Reg },
    Sub { dest: Reg, src1: Reg, src2: Reg },
    Mul { dest: Reg, src1: Reg, src2: Reg },
    Load { dest: Reg, addr: u32 },
    Store { src: Reg, addr: u32 },
    Branch { target: BlockId },
    CondBranch { cond: Reg, target: BlockId },
    Return { value: Option<Reg> },
    Const { dest: Reg, value: i32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Reg(pub u32);

/// Dead Code Elimination pass
pub struct DeadCodeElimination {
    /// Verbose output
    verbose: bool,
}

impl DeadCodeElimination {
    pub fn new() -> Self {
        Self { verbose: false }
    }

    pub fn with_verbose(mut self) -> Self {
        self.verbose = true;
        self
    }

    /// Mark reachable blocks via CFG traversal
    fn mark_reachable_blocks(&self, cfg: &Cfg) -> HashSet<BlockId> {
        let mut reachable = HashSet::new();
        let mut worklist = vec![cfg.entry];

        while let Some(block_id) = worklist.pop() {
            if reachable.contains(&block_id) {
                continue;
            }

            reachable.insert(block_id);

            if let Some(block) = cfg.block(block_id) {
                for &succ in &block.successors {
                    if !reachable.contains(&succ) {
                        worklist.push(succ);
                    }
                }
            }
        }

        reachable
    }

    /// Remove instructions in unreachable blocks
    fn remove_unreachable(&self, cfg: &Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        let reachable = self.mark_reachable_blocks(cfg);

        let mut removed = 0;
        for inst in instructions.iter_mut() {
            if !reachable.contains(&inst.block_id) && !inst.is_dead {
                inst.is_dead = true;
                removed += 1;
            }
        }

        if self.verbose && removed > 0 {
            eprintln!("DCE: Removed {} unreachable instructions", removed);
        }

        OptResult {
            changed: removed > 0,
            removed_count: removed,
            added_count: 0,
            modified_count: 0,
        }
    }
}

impl Default for DeadCodeElimination {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for DeadCodeElimination {
    fn name(&self) -> &'static str {
        "dead-code-elimination"
    }

    fn run(&mut self, cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        self.remove_unreachable(cfg, instructions)
    }
}

/// Constant Folding pass
pub struct ConstantFolding {
    verbose: bool,
}

impl ConstantFolding {
    pub fn new() -> Self {
        Self { verbose: false }
    }

    pub fn with_verbose(mut self) -> Self {
        self.verbose = true;
        self
    }

    /// Fold constant operations
    fn fold_constants(&mut self, instructions: &mut Vec<Instruction>) -> OptResult {
        // Build a map of registers to their constant values
        let mut const_values: HashMap<Reg, i32> = HashMap::new();
        let mut modified = 0;

        for inst in instructions.iter_mut() {
            if inst.is_dead {
                continue;
            }

            // Clone the opcode to avoid borrow checker issues
            let opcode = inst.opcode.clone();

            match opcode {
                // Track constant definitions
                Opcode::Const { dest, value } => {
                    const_values.insert(dest, value);
                }

                // Fold Add if both operands are constant
                Opcode::Add { dest, src1, src2 } => {
                    if let (Some(&val1), Some(&val2)) = (const_values.get(&src1), const_values.get(&src2)) {
                        let result = val1.wrapping_add(val2);
                        inst.opcode = Opcode::Const { dest, value: result };
                        const_values.insert(dest, result);
                        modified += 1;

                        if self.verbose {
                            eprintln!("Folded: add {} = {} + {} -> const {} = {}",
                                dest.0, val1, val2, dest.0, result);
                        }
                    }
                }

                // Fold Sub if both operands are constant
                Opcode::Sub { dest, src1, src2 } => {
                    if let (Some(&val1), Some(&val2)) = (const_values.get(&src1), const_values.get(&src2)) {
                        let result = val1.wrapping_sub(val2);
                        inst.opcode = Opcode::Const { dest, value: result };
                        const_values.insert(dest, result);
                        modified += 1;

                        if self.verbose {
                            eprintln!("Folded: sub {} = {} - {} -> const {} = {}",
                                dest.0, val1, val2, dest.0, result);
                        }
                    }
                }

                // Fold Mul if both operands are constant
                Opcode::Mul { dest, src1, src2 } => {
                    if let (Some(&val1), Some(&val2)) = (const_values.get(&src1), const_values.get(&src2)) {
                        let result = val1.wrapping_mul(val2);
                        inst.opcode = Opcode::Const { dest, value: result };
                        const_values.insert(dest, result);
                        modified += 1;

                        if self.verbose {
                            eprintln!("Folded: mul {} = {} * {} -> const {} = {}",
                                dest.0, val1, val2, dest.0, result);
                        }
                    }
                }

                _ => {}
            }
        }

        if self.verbose && modified > 0 {
            eprintln!("Constant folding: {} operations folded", modified);
        }

        OptResult {
            changed: modified > 0,
            removed_count: 0,
            added_count: 0,
            modified_count: modified,
        }
    }
}

impl Default for ConstantFolding {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for ConstantFolding {
    fn name(&self) -> &'static str {
        "constant-folding"
    }

    fn run(&mut self, _cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        self.fold_constants(instructions)
    }
}

/// Optimization pass manager
pub struct PassManager {
    passes: Vec<Box<dyn OptimizationPass>>,
    max_iterations: usize,
}

impl PassManager {
    pub fn new() -> Self {
        Self {
            passes: Vec::new(),
            max_iterations: 10,
        }
    }

    pub fn add_pass<P: OptimizationPass + 'static>(mut self, pass: P) -> Self {
        self.passes.push(Box::new(pass));
        self
    }

    pub fn with_max_iterations(mut self, max: usize) -> Self {
        self.max_iterations = max;
        self
    }

    pub fn run(&mut self, cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        let mut total_result = OptResult::no_change();
        let mut iteration = 0;

        loop {
            iteration += 1;
            if iteration > self.max_iterations {
                break;
            }

            let mut iteration_result = OptResult::no_change();

            for pass in &mut self.passes {
                let result = pass.run(cfg, instructions);
                iteration_result.merge(result);
            }

            total_result.merge(iteration_result.clone());

            // Stop if no changes in this iteration
            if !iteration_result.changed {
                break;
            }
        }

        total_result
    }
}

impl Default for PassManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use synth_cfg::CfgBuilder;

    #[test]
    fn test_dce_removes_unreachable() {
        // Build a CFG with unreachable block
        let mut builder = CfgBuilder::new();

        // Entry block
        builder.add_instruction();

        // Reachable block
        let reachable = builder.start_block();
        builder.add_instruction();

        // Unreachable block
        let unreachable = builder.start_block();
        builder.add_instruction();

        // Connect entry to reachable only
        builder.set_current_block(0);
        builder.add_branch(reachable);

        let mut cfg = builder.build();

        // Create instructions
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Nop,
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Nop,
                block_id: reachable,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::Nop,
                block_id: unreachable,
                is_dead: false,
            },
        ];

        // Run DCE
        let mut dce = DeadCodeElimination::new();
        let result = dce.run(&mut cfg, &mut instructions);

        // Should remove unreachable instruction
        assert!(result.changed);
        assert_eq!(result.removed_count, 1);
        assert!(instructions[2].is_dead);
        assert!(!instructions[0].is_dead);
        assert!(!instructions[1].is_dead);
    }

    #[test]
    fn test_dce_keeps_reachable() {
        let mut builder = CfgBuilder::new();
        builder.add_instruction();

        let block1 = builder.start_block();
        builder.add_instruction();

        builder.set_current_block(0);
        builder.add_branch(block1);

        let mut cfg = builder.build();

        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Nop,
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Nop,
                block_id: block1,
                is_dead: false,
            },
        ];

        let mut dce = DeadCodeElimination::new();
        let result = dce.run(&mut cfg, &mut instructions);

        // Should not remove anything
        assert!(!result.changed);
        assert_eq!(result.removed_count, 0);
        assert!(!instructions[0].is_dead);
        assert!(!instructions[1].is_dead);
    }

    #[test]
    fn test_pass_manager() {
        let mut builder = CfgBuilder::new();
        builder.add_instruction();

        let mut cfg = builder.build();
        let mut instructions = vec![Instruction {
            id: 0,
            opcode: Opcode::Nop,
            block_id: 0,
            is_dead: false,
        }];

        let mut manager = PassManager::new()
            .add_pass(DeadCodeElimination::new())
            .add_pass(ConstantFolding::new());

        let result = manager.run(&mut cfg, &mut instructions);

        // Should complete without errors
        assert_eq!(result.removed_count, 0); // Nothing to remove
    }

    #[test]
    fn test_opt_result_merge() {
        let mut result1 = OptResult {
            changed: true,
            removed_count: 5,
            added_count: 2,
            modified_count: 3,
        };

        let result2 = OptResult {
            changed: false,
            removed_count: 1,
            added_count: 1,
            modified_count: 2,
        };

        result1.merge(result2);

        assert!(result1.changed);
        assert_eq!(result1.removed_count, 6);
        assert_eq!(result1.added_count, 3);
        assert_eq!(result1.modified_count, 5);
    }

    #[test]
    fn test_constant_folding_add() {
        let mut builder = CfgBuilder::new();
        builder.add_instruction();
        builder.add_instruction();
        builder.add_instruction();

        let mut cfg = builder.build();

        // Create: r0 = const 10, r1 = const 20, r2 = r0 + r1
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 10 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Const { dest: Reg(1), value: 20 },
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

        let mut folder = ConstantFolding::new();
        let result = folder.run(&mut cfg, &mut instructions);

        // Should fold add to const 30
        assert!(result.changed);
        assert_eq!(result.modified_count, 1);
        assert_eq!(instructions[2].opcode, Opcode::Const { dest: Reg(2), value: 30 });
    }

    #[test]
    fn test_constant_folding_multiple_ops() {
        let mut builder = CfgBuilder::new();
        for _ in 0..6 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r0 = 5, r1 = 3, r2 = r0 + r1, r3 = r0 - r1, r4 = r0 * r1
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 5 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Const { dest: Reg(1), value: 3 },
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
            Instruction {
                id: 3,
                opcode: Opcode::Sub {
                    dest: Reg(3),
                    src1: Reg(0),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 4,
                opcode: Opcode::Mul {
                    dest: Reg(4),
                    src1: Reg(0),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut folder = ConstantFolding::new();
        let result = folder.run(&mut cfg, &mut instructions);

        // Should fold all three operations
        assert!(result.changed);
        assert_eq!(result.modified_count, 3);
        assert_eq!(instructions[2].opcode, Opcode::Const { dest: Reg(2), value: 8 });  // 5 + 3
        assert_eq!(instructions[3].opcode, Opcode::Const { dest: Reg(3), value: 2 });  // 5 - 3
        assert_eq!(instructions[4].opcode, Opcode::Const { dest: Reg(4), value: 15 }); // 5 * 3
    }

    #[test]
    fn test_constant_folding_chained() {
        let mut builder = CfgBuilder::new();
        for _ in 0..4 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r0 = 2, r1 = 3, r2 = r0 + r1, r3 = r2 * r0
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 2 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Const { dest: Reg(1), value: 3 },
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
            Instruction {
                id: 3,
                opcode: Opcode::Mul {
                    dest: Reg(3),
                    src1: Reg(2),
                    src2: Reg(0),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut folder = ConstantFolding::new();
        let result = folder.run(&mut cfg, &mut instructions);

        // First pass should fold r2 = 5
        assert!(result.changed);
        assert_eq!(result.modified_count, 2); // Both add and mul should fold
        assert_eq!(instructions[2].opcode, Opcode::Const { dest: Reg(2), value: 5 });  // 2 + 3
        assert_eq!(instructions[3].opcode, Opcode::Const { dest: Reg(3), value: 10 }); // 5 * 2
    }

    #[test]
    fn test_constant_folding_no_change() {
        let mut builder = CfgBuilder::new();
        builder.add_instruction();

        let mut cfg = builder.build();

        // Create: r2 = r0 + r1 (no constants defined)
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Add {
                    dest: Reg(2),
                    src1: Reg(0),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut folder = ConstantFolding::new();
        let result = folder.run(&mut cfg, &mut instructions);

        // Should not change anything
        assert!(!result.changed);
        assert_eq!(result.modified_count, 0);
    }
}
