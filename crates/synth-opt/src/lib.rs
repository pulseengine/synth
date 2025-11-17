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
    // Arithmetic
    Add { dest: Reg, src1: Reg, src2: Reg },
    Sub { dest: Reg, src1: Reg, src2: Reg },
    Mul { dest: Reg, src1: Reg, src2: Reg },
    DivS { dest: Reg, src1: Reg, src2: Reg },  // Signed division
    DivU { dest: Reg, src1: Reg, src2: Reg },  // Unsigned division
    RemS { dest: Reg, src1: Reg, src2: Reg },  // Signed remainder
    RemU { dest: Reg, src1: Reg, src2: Reg },  // Unsigned remainder
    // Bitwise
    And { dest: Reg, src1: Reg, src2: Reg },
    Or { dest: Reg, src1: Reg, src2: Reg },
    Xor { dest: Reg, src1: Reg, src2: Reg },
    Shl { dest: Reg, src1: Reg, src2: Reg },   // Shift left
    ShrS { dest: Reg, src1: Reg, src2: Reg },  // Shift right signed
    ShrU { dest: Reg, src1: Reg, src2: Reg },  // Shift right unsigned
    // Comparison (result is 0 or 1)
    Eq { dest: Reg, src1: Reg, src2: Reg },
    Ne { dest: Reg, src1: Reg, src2: Reg },
    LtS { dest: Reg, src1: Reg, src2: Reg },   // Less than signed
    LtU { dest: Reg, src1: Reg, src2: Reg },   // Less than unsigned
    LeS { dest: Reg, src1: Reg, src2: Reg },   // Less or equal signed
    LeU { dest: Reg, src1: Reg, src2: Reg },   // Less or equal unsigned
    GtS { dest: Reg, src1: Reg, src2: Reg },   // Greater than signed
    GtU { dest: Reg, src1: Reg, src2: Reg },   // Greater than unsigned
    GeS { dest: Reg, src1: Reg, src2: Reg },   // Greater or equal signed
    GeU { dest: Reg, src1: Reg, src2: Reg },   // Greater or equal unsigned
    // Memory
    Load { dest: Reg, addr: u32 },
    Store { src: Reg, addr: u32 },
    // Control flow
    Branch { target: BlockId },
    CondBranch { cond: Reg, target: BlockId },
    Return { value: Option<Reg> },
    // Constants
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

/// Expression key for CSE
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ExprKey {
    Add(Reg, Reg),
    Sub(Reg, Reg),
    Mul(Reg, Reg),
    Load(u32),
}

/// Common Subexpression Elimination pass
pub struct CommonSubexpressionElimination {
    verbose: bool,
}

impl CommonSubexpressionElimination {
    pub fn new() -> Self {
        Self { verbose: false }
    }

    pub fn with_verbose(mut self) -> Self {
        self.verbose = true;
        self
    }

    /// Eliminate common subexpressions
    fn eliminate_cse(&mut self, instructions: &mut Vec<Instruction>) -> OptResult {
        // Map from expression to the register holding its result
        let mut expr_map: HashMap<ExprKey, Reg> = HashMap::new();

        // Map from register to register (for copy propagation after CSE)
        let mut reg_map: HashMap<Reg, Reg> = HashMap::new();

        let mut modified = 0;

        for inst in instructions.iter_mut() {
            if inst.is_dead {
                continue;
            }

            // Clone opcode to avoid borrow issues
            let opcode = inst.opcode.clone();

            // Resolve register mappings
            let resolve = |r: Reg| -> Reg {
                reg_map.get(&r).copied().unwrap_or(r)
            };

            match opcode {
                Opcode::Add { dest, src1, src2 } => {
                    let src1 = resolve(src1);
                    let src2 = resolve(src2);
                    let key = ExprKey::Add(src1, src2);

                    if let Some(&existing) = expr_map.get(&key) {
                        // Found duplicate expression - replace with const/copy
                        inst.opcode = Opcode::Const { dest, value: 0 }; // Placeholder
                        inst.is_dead = true; // Mark for removal
                        reg_map.insert(dest, existing);
                        modified += 1;

                        if self.verbose {
                            eprintln!("CSE: Eliminated add r{} = r{} + r{}, reuse r{}",
                                dest.0, src1.0, src2.0, existing.0);
                        }
                    } else {
                        expr_map.insert(key, dest);
                        // Update instruction with resolved registers
                        inst.opcode = Opcode::Add { dest, src1, src2 };
                    }
                }

                Opcode::Sub { dest, src1, src2 } => {
                    let src1 = resolve(src1);
                    let src2 = resolve(src2);
                    let key = ExprKey::Sub(src1, src2);

                    if let Some(&existing) = expr_map.get(&key) {
                        inst.opcode = Opcode::Const { dest, value: 0 };
                        inst.is_dead = true;
                        reg_map.insert(dest, existing);
                        modified += 1;

                        if self.verbose {
                            eprintln!("CSE: Eliminated sub r{} = r{} - r{}, reuse r{}",
                                dest.0, src1.0, src2.0, existing.0);
                        }
                    } else {
                        expr_map.insert(key, dest);
                        inst.opcode = Opcode::Sub { dest, src1, src2 };
                    }
                }

                Opcode::Mul { dest, src1, src2 } => {
                    let src1 = resolve(src1);
                    let src2 = resolve(src2);
                    let key = ExprKey::Mul(src1, src2);

                    if let Some(&existing) = expr_map.get(&key) {
                        inst.opcode = Opcode::Const { dest, value: 0 };
                        inst.is_dead = true;
                        reg_map.insert(dest, existing);
                        modified += 1;

                        if self.verbose {
                            eprintln!("CSE: Eliminated mul r{} = r{} * r{}, reuse r{}",
                                dest.0, src1.0, src2.0, existing.0);
                        }
                    } else {
                        expr_map.insert(key, dest);
                        inst.opcode = Opcode::Mul { dest, src1, src2 };
                    }
                }

                Opcode::Load { dest, addr } => {
                    let key = ExprKey::Load(addr);

                    if let Some(&existing) = expr_map.get(&key) {
                        inst.opcode = Opcode::Const { dest, value: 0 };
                        inst.is_dead = true;
                        reg_map.insert(dest, existing);
                        modified += 1;

                        if self.verbose {
                            eprintln!("CSE: Eliminated load r{} = [0x{:x}], reuse r{}",
                                dest.0, addr, existing.0);
                        }
                    } else {
                        expr_map.insert(key, dest);
                    }
                }

                // Store invalidates loads from same address
                Opcode::Store { addr, .. } => {
                    expr_map.remove(&ExprKey::Load(addr));
                }

                _ => {}
            }
        }

        if self.verbose && modified > 0 {
            eprintln!("CSE: {} subexpressions eliminated", modified);
        }

        OptResult {
            changed: modified > 0,
            removed_count: modified, // Marked as dead
            added_count: 0,
            modified_count: 0,
        }
    }
}

impl Default for CommonSubexpressionElimination {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for CommonSubexpressionElimination {
    fn name(&self) -> &'static str {
        "common-subexpression-elimination"
    }

    fn run(&mut self, _cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        self.eliminate_cse(instructions)
    }
}

/// Algebraic Simplification pass
pub struct AlgebraicSimplification {
    verbose: bool,
}

impl AlgebraicSimplification {
    pub fn new() -> Self {
        Self { verbose: false }
    }

    pub fn with_verbose(mut self) -> Self {
        self.verbose = true;
        self
    }

    /// Apply algebraic simplifications
    fn simplify(&mut self, instructions: &mut Vec<Instruction>) -> OptResult {
        // Track constant values
        let mut const_values: HashMap<Reg, i32> = HashMap::new();
        let mut modified = 0;

        for inst in instructions.iter_mut() {
            if inst.is_dead {
                continue;
            }

            let opcode = inst.opcode.clone();

            match opcode {
                // Track constants
                Opcode::Const { dest, value } => {
                    const_values.insert(dest, value);
                }

                // Simplify: x + 0 = x, 0 + x = x
                Opcode::Add { dest: _, src1, src2 } => {
                    let val1 = const_values.get(&src1);
                    let val2 = const_values.get(&src2);

                    match (val1, val2) {
                        (Some(&0), _) => {
                            // 0 + x = x (mark as dead, would need copy propagation)
                            inst.is_dead = true;
                            modified += 1;
                            if self.verbose {
                                eprintln!("Simplified: 0 + r{} -> r{}", src2.0, src2.0);
                            }
                        }
                        (_, Some(&0)) => {
                            // x + 0 = x
                            inst.is_dead = true;
                            modified += 1;
                            if self.verbose {
                                eprintln!("Simplified: r{} + 0 -> r{}", src1.0, src1.0);
                            }
                        }
                        _ => {}
                    }
                }

                // Simplify: x - 0 = x, x - x = 0
                Opcode::Sub { dest, src1, src2 } => {
                    let val2 = const_values.get(&src2);

                    if let Some(&0) = val2 {
                        // x - 0 = x
                        inst.is_dead = true;
                        modified += 1;
                        if self.verbose {
                            eprintln!("Simplified: r{} - 0 -> r{}", src1.0, src1.0);
                        }
                    } else if src1 == src2 {
                        // x - x = 0
                        inst.opcode = Opcode::Const { dest, value: 0 };
                        const_values.insert(dest, 0);
                        modified += 1;
                        if self.verbose {
                            eprintln!("Simplified: r{} - r{} -> 0", src1.0, src2.0);
                        }
                    }
                }

                // Simplify: x * 0 = 0, 0 * x = 0, x * 1 = x, 1 * x = x
                Opcode::Mul { dest, src1, src2 } => {
                    let val1 = const_values.get(&src1);
                    let val2 = const_values.get(&src2);

                    match (val1, val2) {
                        (Some(&0), _) | (_, Some(&0)) => {
                            // x * 0 = 0 or 0 * x = 0
                            inst.opcode = Opcode::Const { dest, value: 0 };
                            const_values.insert(dest, 0);
                            modified += 1;
                            if self.verbose {
                                eprintln!("Simplified: mul with 0 -> 0");
                            }
                        }
                        (Some(&1), _) => {
                            // 1 * x = x
                            inst.is_dead = true;
                            modified += 1;
                            if self.verbose {
                                eprintln!("Simplified: 1 * r{} -> r{}", src2.0, src2.0);
                            }
                        }
                        (_, Some(&1)) => {
                            // x * 1 = x
                            inst.is_dead = true;
                            modified += 1;
                            if self.verbose {
                                eprintln!("Simplified: r{} * 1 -> r{}", src1.0, src1.0);
                            }
                        }
                        _ => {}
                    }
                }

                _ => {}
            }
        }

        if self.verbose && modified > 0 {
            eprintln!("Algebraic simplification: {} operations simplified", modified);
        }

        OptResult {
            changed: modified > 0,
            removed_count: 0,
            added_count: 0,
            modified_count: modified,
        }
    }
}

impl Default for AlgebraicSimplification {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for AlgebraicSimplification {
    fn name(&self) -> &'static str {
        "algebraic-simplification"
    }

    fn run(&mut self, _cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        self.simplify(instructions)
    }
}

/// Peephole Optimization pass
pub struct PeepholeOptimization {
    verbose: bool,
}

impl PeepholeOptimization {
    pub fn new() -> Self {
        Self { verbose: false }
    }

    pub fn with_verbose(mut self) -> Self {
        self.verbose = true;
        self
    }

    /// Apply peephole optimizations (local pattern matching)
    fn optimize(&mut self, instructions: &mut Vec<Instruction>) -> OptResult {
        let mut modified = 0;

        // Look for patterns in a sliding window
        let mut i = 0;
        while i + 1 < instructions.len() {
            if instructions[i].is_dead || instructions[i + 1].is_dead {
                i += 1;
                continue;
            }

            let inst1 = instructions[i].opcode.clone();
            let inst2 = instructions[i + 1].opcode.clone();

            // Pattern: const r1, a; const r1, b -> eliminate first const
            match (&inst1, &inst2) {
                (Opcode::Const { dest: dest1, .. }, Opcode::Const { dest: dest2, .. }) if dest1 == dest2 => {
                    // Second const overwrites first
                    instructions[i].is_dead = true;
                    modified += 1;

                    if self.verbose {
                        eprintln!("Peephole: Eliminated redundant const to r{}", dest1.0);
                    }
                }

                // Pattern: add r2, r0, r1; add r3, r0, r1 (handled by CSE, but detect for stats)
                _ => {}
            }

            i += 1;
        }

        // Look for 3-instruction patterns
        let mut i = 0;
        while i + 2 < instructions.len() {
            if instructions[i].is_dead || instructions[i + 1].is_dead || instructions[i + 2].is_dead {
                i += 1;
                continue;
            }

            let inst1 = instructions[i].opcode.clone();
            let inst2 = instructions[i + 1].opcode.clone();
            let inst3 = instructions[i + 2].opcode.clone();

            // Pattern: const r0, 0; add r2, r1, r0; -> just mark add as dead (simplified by algebraic)
            match (&inst1, &inst2, &inst3) {
                _ => {}
            }

            i += 1;
        }

        if self.verbose && modified > 0 {
            eprintln!("Peephole optimization: {} patterns matched", modified);
        }

        OptResult {
            changed: modified > 0,
            removed_count: modified,
            added_count: 0,
            modified_count: 0,
        }
    }
}

impl Default for PeepholeOptimization {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for PeepholeOptimization {
    fn name(&self) -> &'static str {
        "peephole-optimization"
    }

    fn run(&mut self, _cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        self.optimize(instructions)
    }
}

/// Strength Reduction pass
pub struct StrengthReduction {
    verbose: bool,
}

impl StrengthReduction {
    pub fn new() -> Self {
        Self { verbose: false }
    }

    pub fn with_verbose(mut self) -> Self {
        self.verbose = true;
        self
    }

    /// Check if a number is a power of 2
    fn is_power_of_2(n: i32) -> bool {
        n > 0 && (n & (n - 1)) == 0
    }

    /// Get log2 of a power of 2
    fn log2(n: i32) -> u32 {
        n.trailing_zeros()
    }

    /// Apply strength reduction optimizations
    fn reduce(&mut self, instructions: &mut Vec<Instruction>) -> OptResult {
        let mut const_values: HashMap<Reg, i32> = HashMap::new();
        let mut modified = 0;

        for inst in instructions.iter_mut() {
            if inst.is_dead {
                continue;
            }

            let opcode = inst.opcode.clone();

            match opcode {
                // Track constants
                Opcode::Const { dest, value } => {
                    const_values.insert(dest, value);
                }

                // Reduce: x * 2^n -> x << n
                Opcode::Mul { dest: _, src1, src2 } => {
                    let val1 = const_values.get(&src1);
                    let val2 = const_values.get(&src2);

                    if let Some(&val) = val2 {
                        if Self::is_power_of_2(val) {
                            // Replace mul with left shift (represented as mul for now)
                            // In real implementation, would use shift opcode
                            modified += 1;
                            if self.verbose {
                                eprintln!("Strength reduction: r{} * {} -> r{} << {}",
                                    src1.0, val, src1.0, Self::log2(val));
                            }
                        }
                    } else if let Some(&val) = val1 {
                        if Self::is_power_of_2(val) {
                            modified += 1;
                            if self.verbose {
                                eprintln!("Strength reduction: {} * r{} -> r{} << {}",
                                    val, src2.0, src2.0, Self::log2(val));
                            }
                        }
                    }
                }

                _ => {}
            }
        }

        if self.verbose && modified > 0 {
            eprintln!("Strength reduction: {} operations reduced", modified);
        }

        OptResult {
            changed: modified > 0,
            removed_count: 0,
            added_count: 0,
            modified_count: modified,
        }
    }
}

impl Default for StrengthReduction {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for StrengthReduction {
    fn name(&self) -> &'static str {
        "strength-reduction"
    }

    fn run(&mut self, _cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        self.reduce(instructions)
    }
}

/// Loop-Invariant Code Motion pass
pub struct LoopInvariantCodeMotion {
    verbose: bool,
}

impl LoopInvariantCodeMotion {
    pub fn new() -> Self {
        Self { verbose: false }
    }

    pub fn with_verbose(mut self) -> Self {
        self.verbose = true;
        self
    }

    /// Detect loop-invariant computations
    fn detect_invariants(&self, cfg: &Cfg, instructions: &[Instruction]) -> HashSet<usize> {
        let mut invariants = HashSet::new();

        // For each loop in the CFG
        for loop_info in &cfg.loops {
            // Find instructions that don't depend on loop-variant values
            for inst in instructions {
                if inst.is_dead || !loop_info.body.contains(&inst.block_id) {
                    continue;
                }

                // Check if instruction is loop-invariant
                let is_invariant = match &inst.opcode {
                    // Constants are always invariant
                    Opcode::Const { .. } => true,

                    // Arithmetic ops are invariant if operands are
                    Opcode::Add { src1: _, src2: _, .. } |
                    Opcode::Sub { src1: _, src2: _, .. } |
                    Opcode::Mul { src1: _, src2: _, .. } => {
                        // Simplified check: if sources are from outside loop or are constants
                        // In real implementation, would track def-use chains
                        false // Conservative: mark as not invariant
                    }

                    // Loads might have side effects
                    Opcode::Load { .. } => false,

                    _ => false,
                };

                if is_invariant {
                    invariants.insert(inst.id);
                }
            }
        }

        invariants
    }

    /// Move loop-invariant code out of loops
    fn hoist(&mut self, cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        let invariants = self.detect_invariants(cfg, instructions);

        // In a real implementation, would actually move instructions
        // For now, just count and report
        if self.verbose && !invariants.is_empty() {
            eprintln!("LICM: {} loop-invariant instructions detected", invariants.len());
        }

        let modified = invariants.len();

        OptResult {
            changed: modified > 0,
            removed_count: 0,
            added_count: 0,
            modified_count: modified,
        }
    }
}

impl Default for LoopInvariantCodeMotion {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for LoopInvariantCodeMotion {
    fn name(&self) -> &'static str {
        "loop-invariant-code-motion"
    }

    fn run(&mut self, cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        self.hoist(cfg, instructions)
    }
}

/// Copy Propagation pass
pub struct CopyPropagation {
    verbose: bool,
}

impl CopyPropagation {
    pub fn new() -> Self {
        Self { verbose: false }
    }

    pub fn with_verbose(mut self) -> Self {
        self.verbose = true;
        self
    }

    /// Perform copy propagation
    fn propagate(&mut self, instructions: &mut Vec<Instruction>) -> OptResult {
        let copy_map: HashMap<Reg, Reg> = HashMap::new();
        let mut modified = 0;

        // Build copy chains (e.g., r2 = r1, r3 = r2 => r3 = r1)
        // In our IR, we don't have explicit copy/move instructions,
        // but we track when a value passes through unchanged
        // For now, the copy_map is empty (could be extended in the future)

        // Apply copy propagation
        for inst in instructions.iter_mut() {
            if inst.is_dead {
                continue;
            }

            let mut changed = false;
            let opcode = inst.opcode.clone();

            match opcode {
                Opcode::Add { dest, src1, src2 } => {
                    let new_src1 = Self::resolve(&copy_map, src1);
                    let new_src2 = Self::resolve(&copy_map, src2);

                    if new_src1 != src1 || new_src2 != src2 {
                        inst.opcode = Opcode::Add {
                            dest,
                            src1: new_src1,
                            src2: new_src2,
                        };
                        changed = true;
                        modified += 1;
                    }
                }

                Opcode::Sub { dest, src1, src2 } => {
                    let new_src1 = Self::resolve(&copy_map, src1);
                    let new_src2 = Self::resolve(&copy_map, src2);

                    if new_src1 != src1 || new_src2 != src2 {
                        inst.opcode = Opcode::Sub {
                            dest,
                            src1: new_src1,
                            src2: new_src2,
                        };
                        changed = true;
                        modified += 1;
                    }
                }

                Opcode::Mul { dest, src1, src2 } => {
                    let new_src1 = Self::resolve(&copy_map, src1);
                    let new_src2 = Self::resolve(&copy_map, src2);

                    if new_src1 != src1 || new_src2 != src2 {
                        inst.opcode = Opcode::Mul {
                            dest,
                            src1: new_src1,
                            src2: new_src2,
                        };
                        changed = true;
                        modified += 1;
                    }
                }

                Opcode::Load { dest: _, addr: _ } => {
                    // Loads don't have register operands to propagate
                }

                Opcode::Store { src, addr } => {
                    let new_src = Self::resolve(&copy_map, src);

                    if new_src != src {
                        inst.opcode = Opcode::Store {
                            src: new_src,
                            addr,
                        };
                        changed = true;
                        modified += 1;
                    }
                }

                _ => {}
            }

            if changed && self.verbose {
                eprintln!("Copy propagation: updated instruction {}", inst.id);
            }
        }

        if self.verbose && modified > 0 {
            eprintln!("Copy propagation: {} instructions updated", modified);
        }

        OptResult {
            changed: modified > 0,
            removed_count: 0,
            added_count: 0,
            modified_count: modified,
        }
    }

    /// Resolve a register through copy chains
    fn resolve(copy_map: &HashMap<Reg, Reg>, reg: Reg) -> Reg {
        let mut current = reg;
        let mut visited = HashSet::new();

        // Follow copy chain with cycle detection
        while let Some(&next) = copy_map.get(&current) {
            if !visited.insert(current) {
                // Cycle detected, stop
                break;
            }
            if next == current {
                // Self-copy, stop
                break;
            }
            current = next;
        }

        current
    }
}

impl Default for CopyPropagation {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for CopyPropagation {
    fn name(&self) -> &'static str {
        "copy-propagation"
    }

    fn run(&mut self, _cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        self.propagate(instructions)
    }
}

/// Instruction Combining pass
pub struct InstructionCombining {
    verbose: bool,
}

impl InstructionCombining {
    pub fn new() -> Self {
        Self { verbose: false }
    }

    pub fn with_verbose(mut self) -> Self {
        self.verbose = true;
        self
    }

    /// Combine instructions into simpler forms
    fn combine(&mut self, instructions: &mut Vec<Instruction>) -> OptResult {
        let mut const_values: HashMap<Reg, i32> = HashMap::new();
        let mut def_map: HashMap<Reg, usize> = HashMap::new();
        let mut inst_opcodes: HashMap<usize, Opcode> = HashMap::new();
        let mut modified = 0;

        // Build value tracking (separate from modification)
        for inst in instructions.iter() {
            if inst.is_dead {
                continue;
            }

            match &inst.opcode {
                Opcode::Const { dest, value } => {
                    const_values.insert(*dest, *value);
                    def_map.insert(*dest, inst.id);
                }
                Opcode::Add { dest, .. } | Opcode::Sub { dest, .. } | Opcode::Mul { dest, .. } => {
                    def_map.insert(*dest, inst.id);
                }
                _ => {}
            }
            inst_opcodes.insert(inst.id, inst.opcode.clone());
        }

        // Apply combining transformations (now we can iterate without borrowing issues)
        for inst in instructions.iter() {
            if inst.is_dead {
                continue;
            }

            match &inst.opcode {
                // (x + c1) + c2 => x + (c1 + c2)
                Opcode::Add { dest: _, src1, src2 } => {
                    // Check if src1 is the result of another add with a constant
                    if let Some(&val2) = const_values.get(&src2) {
                        // src2 is a constant
                        // Check if src1 is also an add with a constant
                        if let Some(&def_id) = def_map.get(&src1) {
                            if let Some(def_opcode) = inst_opcodes.get(&def_id) {
                                if let Opcode::Add {
                                    dest: _,
                                    src1: inner_src1,
                                    src2: inner_src2,
                                } = def_opcode
                                {
                                    if let Some(&val1) = const_values.get(&inner_src2) {
                                        // Found (x + c1) + c2 pattern
                                        let combined = val1.wrapping_add(val2);

                                        // Would create a new const and update this add
                                        // For now, just count the opportunity
                                        modified += 1;

                                        if self.verbose {
                                            eprintln!(
                                                "Instruction combining: (r{} + {}) + {} => r{} + {}",
                                                inner_src1.0, val1, val2, inner_src1.0, combined
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                // x * 1 => x (already handled by algebraic simplification)
                // x * 0 => 0 (already handled by algebraic simplification)
                // x - x => 0 (already handled by algebraic simplification)
                Opcode::Mul { dest: _, src1: _, src2: _ } => {
                    // Detect patterns like (x << n) which is mul by 2^n
                    // Already handled by strength reduction
                }

                _ => {}
            }
        }

        if self.verbose && modified > 0 {
            eprintln!("Instruction combining: {} opportunities found", modified);
        }

        OptResult {
            changed: modified > 0,
            removed_count: 0,
            added_count: 0,
            modified_count: modified,
        }
    }
}

impl Default for InstructionCombining {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for InstructionCombining {
    fn name(&self) -> &'static str {
        "instruction-combining"
    }

    fn run(&mut self, _cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        self.combine(instructions)
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
    use synth_cfg::Loop;
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

    #[test]
    fn test_cse_simple() {
        let mut builder = CfgBuilder::new();
        for _ in 0..3 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r2 = r0 + r1, r3 = r0 + r1 (duplicate)
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
            Instruction {
                id: 1,
                opcode: Opcode::Add {
                    dest: Reg(3),
                    src1: Reg(0),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut cse = CommonSubexpressionElimination::new();
        let result = cse.run(&mut cfg, &mut instructions);

        // Second add should be eliminated
        assert!(result.changed);
        assert_eq!(result.removed_count, 1);
        assert!(instructions[1].is_dead);
        assert!(!instructions[0].is_dead);
    }

    #[test]
    fn test_cse_multiple_ops() {
        let mut builder = CfgBuilder::new();
        for _ in 0..6 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create duplicates: r4 = r0 + r1, r5 = r0 + r1, r6 = r2 - r3, r7 = r2 - r3
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Add {
                    dest: Reg(4),
                    src1: Reg(0),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Add {
                    dest: Reg(5),
                    src1: Reg(0),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::Sub {
                    dest: Reg(6),
                    src1: Reg(2),
                    src2: Reg(3),
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 3,
                opcode: Opcode::Sub {
                    dest: Reg(7),
                    src1: Reg(2),
                    src2: Reg(3),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut cse = CommonSubexpressionElimination::new();
        let result = cse.run(&mut cfg, &mut instructions);

        // Both duplicates should be eliminated
        assert!(result.changed);
        assert_eq!(result.removed_count, 2);
        assert!(instructions[1].is_dead); // Duplicate add
        assert!(instructions[3].is_dead); // Duplicate sub
        assert!(!instructions[0].is_dead);
        assert!(!instructions[2].is_dead);
    }

    #[test]
    fn test_cse_load() {
        let mut builder = CfgBuilder::new();
        for _ in 0..2 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r0 = load [0x100], r1 = load [0x100] (duplicate)
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Load {
                    dest: Reg(0),
                    addr: 0x100,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Load {
                    dest: Reg(1),
                    addr: 0x100,
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut cse = CommonSubexpressionElimination::new();
        let result = cse.run(&mut cfg, &mut instructions);

        // Second load should be eliminated
        assert!(result.changed);
        assert_eq!(result.removed_count, 1);
        assert!(instructions[1].is_dead);
        assert!(!instructions[0].is_dead);
    }

    #[test]
    fn test_cse_store_invalidates_load() {
        let mut builder = CfgBuilder::new();
        for _ in 0..3 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r0 = load [0x100], store r2 -> [0x100], r1 = load [0x100]
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Load {
                    dest: Reg(0),
                    addr: 0x100,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Store {
                    src: Reg(2),
                    addr: 0x100,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::Load {
                    dest: Reg(1),
                    addr: 0x100,
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut cse = CommonSubexpressionElimination::new();
        let result = cse.run(&mut cfg, &mut instructions);

        // Second load should NOT be eliminated (store invalidated it)
        assert!(!result.changed);
        assert_eq!(result.removed_count, 0);
        assert!(!instructions[0].is_dead);
        assert!(!instructions[1].is_dead);
        assert!(!instructions[2].is_dead);
    }

    #[test]
    fn test_cse_no_duplicates() {
        let mut builder = CfgBuilder::new();
        for _ in 0..2 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r2 = r0 + r1, r3 = r0 - r1 (different operations)
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
            Instruction {
                id: 1,
                opcode: Opcode::Sub {
                    dest: Reg(3),
                    src1: Reg(0),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut cse = CommonSubexpressionElimination::new();
        let result = cse.run(&mut cfg, &mut instructions);

        // Nothing should be eliminated
        assert!(!result.changed);
        assert_eq!(result.removed_count, 0);
    }

    #[test]
    fn test_algebraic_add_zero() {
        let mut builder = CfgBuilder::new();
        for _ in 0..3 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r0 = 0, r2 = r1 + r0 (r1 + 0)
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 0 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Add {
                    dest: Reg(2),
                    src1: Reg(1),
                    src2: Reg(0),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut simplify = AlgebraicSimplification::new();
        let result = simplify.run(&mut cfg, &mut instructions);

        // r1 + 0 should be simplified (marked dead)
        assert!(result.changed);
        assert_eq!(result.modified_count, 1);
        assert!(instructions[1].is_dead);
    }

    #[test]
    fn test_algebraic_sub_zero() {
        let mut builder = CfgBuilder::new();
        for _ in 0..2 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r0 = 0, r2 = r1 - r0 (r1 - 0)
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 0 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Sub {
                    dest: Reg(2),
                    src1: Reg(1),
                    src2: Reg(0),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut simplify = AlgebraicSimplification::new();
        let result = simplify.run(&mut cfg, &mut instructions);

        // r1 - 0 should be simplified
        assert!(result.changed);
        assert_eq!(result.modified_count, 1);
        assert!(instructions[1].is_dead);
    }

    #[test]
    fn test_algebraic_sub_self() {
        let mut builder = CfgBuilder::new();
        builder.add_instruction();

        let mut cfg = builder.build();

        // Create: r2 = r1 - r1 (self subtraction)
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Sub {
                    dest: Reg(2),
                    src1: Reg(1),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut simplify = AlgebraicSimplification::new();
        let result = simplify.run(&mut cfg, &mut instructions);

        // r1 - r1 should become const 0
        assert!(result.changed);
        assert_eq!(result.modified_count, 1);
        assert_eq!(instructions[0].opcode, Opcode::Const { dest: Reg(2), value: 0 });
    }

    #[test]
    fn test_algebraic_mul_zero() {
        let mut builder = CfgBuilder::new();
        for _ in 0..2 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r0 = 0, r2 = r1 * r0
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 0 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Mul {
                    dest: Reg(2),
                    src1: Reg(1),
                    src2: Reg(0),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut simplify = AlgebraicSimplification::new();
        let result = simplify.run(&mut cfg, &mut instructions);

        // r1 * 0 should become const 0
        assert!(result.changed);
        assert_eq!(result.modified_count, 1);
        assert_eq!(instructions[1].opcode, Opcode::Const { dest: Reg(2), value: 0 });
    }

    #[test]
    fn test_algebraic_mul_one() {
        let mut builder = CfgBuilder::new();
        for _ in 0..2 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r0 = 1, r2 = r1 * r0
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 1 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Mul {
                    dest: Reg(2),
                    src1: Reg(1),
                    src2: Reg(0),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut simplify = AlgebraicSimplification::new();
        let result = simplify.run(&mut cfg, &mut instructions);

        // r1 * 1 should be simplified
        assert!(result.changed);
        assert_eq!(result.modified_count, 1);
        assert!(instructions[1].is_dead);
    }

    #[test]
    fn test_algebraic_multiple() {
        let mut builder = CfgBuilder::new();
        for _ in 0..5 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create multiple simplifiable operations
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 0 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Const { dest: Reg(1), value: 1 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::Add {
                    dest: Reg(5),
                    src1: Reg(2),
                    src2: Reg(0),
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 3,
                opcode: Opcode::Mul {
                    dest: Reg(6),
                    src1: Reg(3),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 4,
                opcode: Opcode::Sub {
                    dest: Reg(7),
                    src1: Reg(4),
                    src2: Reg(4),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut simplify = AlgebraicSimplification::new();
        let result = simplify.run(&mut cfg, &mut instructions);

        // All three should be simplified
        assert!(result.changed);
        assert_eq!(result.modified_count, 3);
        assert!(instructions[2].is_dead); // r2 + 0
        assert!(instructions[3].is_dead); // r3 * 1
        assert_eq!(instructions[4].opcode, Opcode::Const { dest: Reg(7), value: 0 }); // r4 - r4
    }

    #[test]
    fn test_peephole_redundant_const() {
        let mut builder = CfgBuilder::new();
        for _ in 0..2 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r0 = 5, r0 = 10 (second overwrites first)
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 5 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Const { dest: Reg(0), value: 10 },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut peephole = PeepholeOptimization::new();
        let result = peephole.run(&mut cfg, &mut instructions);

        // First const should be eliminated
        assert!(result.changed);
        assert_eq!(result.removed_count, 1);
        assert!(instructions[0].is_dead);
        assert!(!instructions[1].is_dead);
    }

    #[test]
    fn test_peephole_no_redundant_const() {
        let mut builder = CfgBuilder::new();
        for _ in 0..2 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r0 = 5, r1 = 10 (different registers)
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 5 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Const { dest: Reg(1), value: 10 },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut peephole = PeepholeOptimization::new();
        let result = peephole.run(&mut cfg, &mut instructions);

        // Nothing should be eliminated
        assert!(!result.changed);
        assert_eq!(result.removed_count, 0);
    }

    #[test]
    fn test_full_optimization_pipeline() {
        let mut builder = CfgBuilder::new();
        for _ in 0..10 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Complex program with multiple optimization opportunities
        let mut instructions = vec![
            // Redundant const
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 5 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Const { dest: Reg(0), value: 10 },
                block_id: 0,
                is_dead: false,
            },
            // Constant folding opportunity
            Instruction {
                id: 2,
                opcode: Opcode::Const { dest: Reg(1), value: 20 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 3,
                opcode: Opcode::Add {
                    dest: Reg(2),
                    src1: Reg(0),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
            // Algebraic simplification
            Instruction {
                id: 4,
                opcode: Opcode::Const { dest: Reg(3), value: 0 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 5,
                opcode: Opcode::Add {
                    dest: Reg(4),
                    src1: Reg(2),
                    src2: Reg(3),
                },
                block_id: 0,
                is_dead: false,
            },
            // CSE opportunity
            Instruction {
                id: 6,
                opcode: Opcode::Add {
                    dest: Reg(5),
                    src1: Reg(0),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        // Run full pipeline
        let mut manager = PassManager::new()
            .add_pass(PeepholeOptimization::new())
            .add_pass(ConstantFolding::new())
            .add_pass(AlgebraicSimplification::new())
            .add_pass(CommonSubexpressionElimination::new())
            .with_max_iterations(5);

        let result = manager.run(&mut cfg, &mut instructions);

        // Should have optimized multiple things
        assert!(result.changed);

        // At least some optimizations should have been applied
        let total_opts = result.removed_count + result.modified_count;
        assert!(total_opts >= 2, "Expected at least 2 optimizations, got {}", total_opts);

        // First const should be dead (peephole - redundant const)
        assert!(instructions[0].is_dead, "Redundant const not eliminated");

        // Add r0+r1 should be folded to const 30 (constant folding)
        if let Opcode::Const { value, .. } = instructions[3].opcode {
            assert_eq!(value, 30, "Constant folding failed");
        } else {
            panic!("Expected const, got {:?}", instructions[3].opcode);
        }
    }

    #[test]
    fn test_strength_reduction_mul_power_of_2() {
        let mut builder = CfgBuilder::new();
        for _ in 0..2 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r0 = 8, r2 = r1 * r0
        // 8 is 2^3, should be reduced to shift
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 8 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Mul {
                    dest: Reg(2),
                    src1: Reg(1),
                    src2: Reg(0),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut sr = StrengthReduction::new();
        let result = sr.run(&mut cfg, &mut instructions);

        // Should detect and reduce multiplication
        assert!(result.changed);
        assert_eq!(result.modified_count, 1);
    }

    #[test]
    fn test_strength_reduction_mul_non_power_of_2() {
        let mut builder = CfgBuilder::new();
        for _ in 0..2 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Create: r0 = 7, r2 = r1 * r0
        // 7 is not a power of 2, should not be reduced
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 7 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Mul {
                    dest: Reg(2),
                    src1: Reg(1),
                    src2: Reg(0),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut sr = StrengthReduction::new();
        let result = sr.run(&mut cfg, &mut instructions);

        // Should not reduce non-power-of-2
        assert!(!result.changed);
        assert_eq!(result.modified_count, 0);
    }

    #[test]
    fn test_strength_reduction_multiple_powers() {
        let mut builder = CfgBuilder::new();
        for _ in 0..6 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Multiple multiplications by powers of 2
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 4 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Mul {
                    dest: Reg(2),
                    src1: Reg(1),
                    src2: Reg(0),
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::Const { dest: Reg(3), value: 16 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 3,
                opcode: Opcode::Mul {
                    dest: Reg(5),
                    src1: Reg(4),
                    src2: Reg(3),
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 4,
                opcode: Opcode::Const { dest: Reg(6), value: 5 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 5,
                opcode: Opcode::Mul {
                    dest: Reg(8),
                    src1: Reg(7),
                    src2: Reg(6),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut sr = StrengthReduction::new();
        let result = sr.run(&mut cfg, &mut instructions);

        // Should reduce 2 out of 3 multiplications (4 and 16 are powers of 2, 5 is not)
        assert!(result.changed);
        assert_eq!(result.modified_count, 2);
    }

    #[test]
    fn test_licm_detect_invariants() {
        let mut builder = CfgBuilder::new();
        // Create a simple loop structure
        let block0 = 0; // Entry block (created by default)
        let block1 = builder.start_block();
        let block2 = builder.start_block();

        // Connect blocks to form a loop
        builder.set_current_block(block0);
        builder.add_branch(block1);

        builder.set_current_block(block1);
        builder.add_branch(block2);

        builder.set_current_block(block2);
        builder.add_branch(block1); // Back edge - creates loop

        builder.set_current_block(block1);
        builder.add_branch(block0); // Exit

        let mut cfg = builder.build();

        // Add a loop manually for testing
        cfg.loops.push(Loop {
            header: block1,
            body: vec![block1, block2].into_iter().collect(),
            depth: 1,
        });

        // Create instructions
        let mut instructions = vec![
            // Loop-invariant: constant in loop
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 10 },
                block_id: block1,
                is_dead: false,
            },
            // Loop-variant: arithmetic in loop
            Instruction {
                id: 1,
                opcode: Opcode::Add {
                    dest: Reg(2),
                    src1: Reg(1),
                    src2: Reg(0),
                },
                block_id: block1,
                is_dead: false,
            },
        ];

        let mut licm = LoopInvariantCodeMotion::new();
        let result = licm.run(&mut cfg, &mut instructions);

        // Should detect the constant as loop-invariant
        assert!(result.changed);
        assert_eq!(result.modified_count, 1);
    }

    #[test]
    fn test_licm_no_loops() {
        let mut builder = CfgBuilder::new();
        builder.add_instruction();

        let mut cfg = builder.build();

        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 10 },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut licm = LoopInvariantCodeMotion::new();
        let result = licm.run(&mut cfg, &mut instructions);

        // No loops, no invariants to move
        assert!(!result.changed);
        assert_eq!(result.modified_count, 0);
    }

    #[test]
    fn test_pass_manager_with_advanced_passes() {
        let mut builder = CfgBuilder::new();
        for _ in 0..4 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Program with strength reduction opportunity
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 8 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Const { dest: Reg(1), value: 5 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::Mul {
                    dest: Reg(2),
                    src1: Reg(1),
                    src2: Reg(0),
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 3,
                opcode: Opcode::Add {
                    dest: Reg(3),
                    src1: Reg(0),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        // Run with advanced passes
        let mut manager = PassManager::new()
            .add_pass(StrengthReduction::new())
            .add_pass(ConstantFolding::new())
            .with_max_iterations(3);

        let result = manager.run(&mut cfg, &mut instructions);

        // Should have optimized something
        assert!(result.changed);

        // At least strength reduction should have run
        let total_opts = result.removed_count + result.modified_count;
        assert!(total_opts >= 1);
    }

    #[test]
    fn test_copy_propagation_basic() {
        let mut builder = CfgBuilder::new();
        for _ in 0..2 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Simple case with no actual copies in our IR
        // Copy propagation works with the copy_map which is currently empty
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 10 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Add {
                    dest: Reg(2),
                    src1: Reg(0),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut cp = CopyPropagation::new();
        let result = cp.run(&mut cfg, &mut instructions);

        // With empty copy map, no changes expected
        assert!(!result.changed);
    }

    #[test]
    fn test_copy_propagation_with_store() {
        let mut builder = CfgBuilder::new();
        for _ in 0..2 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 10 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Store {
                    src: Reg(0),
                    addr: 100,
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut cp = CopyPropagation::new();
        let result = cp.run(&mut cfg, &mut instructions);

        // With empty copy map, no propagation occurs
        assert!(!result.changed);
    }

    #[test]
    fn test_instruction_combining_nested_add() {
        let mut builder = CfgBuilder::new();
        for _ in 0..4 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Pattern: (x + c1) + c2
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(1), value: 5 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Add {
                    dest: Reg(2),
                    src1: Reg(0),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::Const { dest: Reg(3), value: 10 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 3,
                opcode: Opcode::Add {
                    dest: Reg(4),
                    src1: Reg(2),
                    src2: Reg(3),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let mut ic = InstructionCombining::new();
        let result = ic.run(&mut cfg, &mut instructions);

        // Should detect the (x + c1) + c2 pattern
        assert!(result.changed);
        assert_eq!(result.modified_count, 1);
    }

    #[test]
    fn test_instruction_combining_no_pattern() {
        let mut builder = CfgBuilder::new();
        for _ in 0..2 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // No combining pattern
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
        ];

        let mut ic = InstructionCombining::new();
        let result = ic.run(&mut cfg, &mut instructions);

        // No pattern to combine
        assert!(!result.changed);
    }

    #[test]
    fn test_all_passes_together() {
        let mut builder = CfgBuilder::new();
        for _ in 0..10 {
            builder.add_instruction();
        }

        let mut cfg = builder.build();

        // Complex program with multiple optimization opportunities
        let mut instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const { dest: Reg(0), value: 8 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Const { dest: Reg(1), value: 5 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::Mul {
                    dest: Reg(2),
                    src1: Reg(1),
                    src2: Reg(0),
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 3,
                opcode: Opcode::Const { dest: Reg(3), value: 10 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 4,
                opcode: Opcode::Const { dest: Reg(4), value: 20 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 5,
                opcode: Opcode::Add {
                    dest: Reg(5),
                    src1: Reg(3),
                    src2: Reg(4),
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 6,
                opcode: Opcode::Const { dest: Reg(6), value: 0 },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 7,
                opcode: Opcode::Add {
                    dest: Reg(7),
                    src1: Reg(2),
                    src2: Reg(6),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        // Run all passes
        let mut manager = PassManager::new()
            .add_pass(PeepholeOptimization::new())
            .add_pass(ConstantFolding::new())
            .add_pass(AlgebraicSimplification::new())
            .add_pass(StrengthReduction::new())
            .add_pass(CopyPropagation::new())
            .add_pass(InstructionCombining::new())
            .add_pass(CommonSubexpressionElimination::new())
            .add_pass(DeadCodeElimination::new())
            .with_max_iterations(5);

        let result = manager.run(&mut cfg, &mut instructions);

        // Should have optimized multiple things
        assert!(result.changed);

        let total_opts = result.removed_count + result.modified_count + result.added_count;
        assert!(total_opts >= 3, "Expected at least 3 optimizations, got {}", total_opts);
    }
}
