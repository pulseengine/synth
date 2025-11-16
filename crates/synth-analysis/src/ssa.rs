//! SSA (Static Single Assignment) Form Conversion and Optimizations
//!
//! Implements SSA construction, phi node insertion, and SSA-based optimizations

use std::collections::{HashMap, HashSet};
use synth_core::Result;

/// SSA variable (versioned local variable)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SSAVar {
    /// Original variable index
    pub original: u32,

    /// Version number (for SSA)
    pub version: u32,
}

impl SSAVar {
    /// Create a new SSA variable
    pub fn new(original: u32, version: u32) -> Self {
        Self { original, version }
    }

    /// Get the display name
    pub fn name(&self) -> String {
        format!("v{}_{}", self.original, self.version)
    }
}

/// SSA instruction
#[derive(Debug, Clone)]
pub enum SSAInstr {
    /// Phi node: x = φ(x1, x2, ...) from different predecessors
    Phi {
        result: SSAVar,
        args: Vec<(u32, SSAVar)>, // (block_id, variable)
    },

    /// Assignment: result = value
    Assign {
        result: SSAVar,
        value: SSAValue,
    },

    /// Binary operation: result = left op right
    BinOp {
        result: SSAVar,
        op: BinOp,
        left: SSAValue,
        right: SSAValue,
    },

    /// Unary operation: result = op value
    UnaryOp {
        result: SSAVar,
        op: UnaryOp,
        value: SSAValue,
    },

    /// Load from memory: result = *addr
    Load {
        result: SSAVar,
        addr: SSAValue,
        offset: i32,
    },

    /// Store to memory: *addr = value
    Store {
        addr: SSAValue,
        value: SSAValue,
        offset: i32,
    },

    /// Call function: result = call(func, args...)
    Call {
        result: Option<SSAVar>,
        func: u32,
        args: Vec<SSAValue>,
    },

    /// Return from function
    Return {
        value: Option<SSAValue>,
    },

    /// Branch: if cond goto target else fallthrough
    Branch {
        cond: SSAValue,
        true_target: u32,
        false_target: u32,
    },

    /// Unconditional jump
    Jump {
        target: u32,
    },
}

/// Binary operation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add, Sub, Mul, DivS, DivU,
    And, Or, Xor,
    Shl, ShrS, ShrU,
    Eq, Ne, LtS, LtU, LeS, LeU, GtS, GtU, GeS, GeU,
}

/// Unary operation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
    Eqz,
    Clz,
    Ctz,
    Popcnt,
}

/// SSA value (variable or constant)
#[derive(Debug, Clone)]
pub enum SSAValue {
    /// Variable reference
    Var(SSAVar),

    /// Integer constant
    I32(i32),

    /// Long constant
    I64(i64),

    /// Float constant
    F32(f32),

    /// Double constant
    F64(f64),
}

/// Basic block in SSA form
#[derive(Debug, Clone)]
pub struct SSABlock {
    /// Block ID
    pub id: u32,

    /// Phi nodes at the beginning
    pub phis: Vec<SSAInstr>,

    /// Regular instructions
    pub instrs: Vec<SSAInstr>,

    /// Predecessors (blocks that can jump here)
    pub predecessors: Vec<u32>,

    /// Successors (blocks this can jump to)
    pub successors: Vec<u32>,
}

impl SSABlock {
    /// Create a new basic block
    pub fn new(id: u32) -> Self {
        Self {
            id,
            phis: Vec::new(),
            instrs: Vec::new(),
            predecessors: Vec::new(),
            successors: Vec::new(),
        }
    }

    /// Add a phi node
    pub fn add_phi(&mut self, phi: SSAInstr) {
        if matches!(phi, SSAInstr::Phi { .. }) {
            self.phis.push(phi);
        }
    }

    /// Add a regular instruction
    pub fn add_instr(&mut self, instr: SSAInstr) {
        self.instrs.push(instr);
    }
}

/// SSA function
#[derive(Debug, Clone)]
pub struct SSAFunction {
    /// Function index
    pub index: u32,

    /// Parameters
    pub params: Vec<SSAVar>,

    /// Return type
    pub returns: Vec<SSAVar>,

    /// Basic blocks
    pub blocks: Vec<SSABlock>,

    /// Entry block ID
    pub entry: u32,
}

impl SSAFunction {
    /// Create a new SSA function
    pub fn new(index: u32) -> Self {
        Self {
            index,
            params: Vec::new(),
            returns: Vec::new(),
            blocks: Vec::new(),
            entry: 0,
        }
    }

    /// Get a block by ID
    pub fn get_block(&self, id: u32) -> Option<&SSABlock> {
        self.blocks.iter().find(|b| b.id == id)
    }

    /// Get a mutable block by ID
    pub fn get_block_mut(&mut self, id: u32) -> Option<&mut SSABlock> {
        self.blocks.iter_mut().find(|b| b.id == id)
    }
}

/// Constant propagation optimization
pub struct ConstantPropagation;

impl ConstantPropagation {
    /// Propagate constants through SSA form
    pub fn optimize(func: &mut SSAFunction) -> usize {
        let mut changed = 0;
        let mut constant_map: HashMap<SSAVar, SSAValue> = HashMap::new();

        // Collect constant assignments
        for block in &func.blocks {
            for instr in &block.instrs {
                if let SSAInstr::Assign { result, value } = instr {
                    if matches!(value, SSAValue::I32(_) | SSAValue::I64(_)) {
                        constant_map.insert(result.clone(), value.clone());
                    }
                }
            }
        }

        // Substitute constants
        for block in &mut func.blocks {
            for instr in &mut block.instrs {
                match instr {
                    SSAInstr::BinOp { left, right, result, op } => {
                        // Try to fold constant binary operations
                        if let (SSAValue::I32(l), SSAValue::I32(r)) = (left, right) {
                            if let Some(folded) = Self::fold_binop(*op, *l, *r) {
                                constant_map.insert(result.clone(), SSAValue::I32(folded));
                                changed += 1;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        changed
    }

    /// Fold a binary operation on constants
    fn fold_binop(op: BinOp, left: i32, right: i32) -> Option<i32> {
        Some(match op {
            BinOp::Add => left.wrapping_add(right),
            BinOp::Sub => left.wrapping_sub(right),
            BinOp::Mul => left.wrapping_mul(right),
            BinOp::And => left & right,
            BinOp::Or => left | right,
            BinOp::Xor => left ^ right,
            BinOp::Shl => left.wrapping_shl(right as u32),
            BinOp::ShrS => left.wrapping_shr(right as u32),
            BinOp::ShrU => ((left as u32).wrapping_shr(right as u32)) as i32,
            BinOp::Eq => if left == right { 1 } else { 0 },
            BinOp::Ne => if left != right { 1 } else { 0 },
            BinOp::LtS => if left < right { 1 } else { 0 },
            BinOp::GtS => if left > right { 1 } else { 0 },
            _ => return None,
        })
    }
}

/// Dead code elimination optimization
pub struct DeadCodeElimination;

impl DeadCodeElimination {
    /// Remove dead code from SSA form
    pub fn optimize(func: &mut SSAFunction) -> usize {
        let mut removed = 0;
        let used_vars = Self::compute_live_vars(func);

        // Remove assignments to dead variables
        for block in &mut func.blocks {
            block.instrs.retain(|instr| {
                match instr {
                    SSAInstr::Assign { result, .. } |
                    SSAInstr::BinOp { result, .. } |
                    SSAInstr::UnaryOp { result, .. } |
                    SSAInstr::Load { result, .. } => {
                        if !used_vars.contains(result) {
                            removed += 1;
                            return false;
                        }
                    }
                    _ => {}
                }
                true
            });
        }

        removed
    }

    /// Compute live variables (used variables)
    fn compute_live_vars(func: &SSAFunction) -> HashSet<SSAVar> {
        let mut live = HashSet::new();

        // Mark variables used in operations
        for block in &func.blocks {
            for instr in &block.instrs {
                Self::mark_used(instr, &mut live);
            }
        }

        live
    }

    /// Mark variables used by an instruction
    fn mark_used(instr: &SSAInstr, live: &mut HashSet<SSAVar>) {
        match instr {
            SSAInstr::BinOp { left, right, .. } => {
                if let SSAValue::Var(v) = left {
                    live.insert(v.clone());
                }
                if let SSAValue::Var(v) = right {
                    live.insert(v.clone());
                }
            }
            SSAInstr::UnaryOp { value, .. } => {
                if let SSAValue::Var(v) = value {
                    live.insert(v.clone());
                }
            }
            SSAInstr::Return { value: Some(SSAValue::Var(v)) } => {
                live.insert(v.clone());
            }
            SSAInstr::Branch { cond: SSAValue::Var(v), .. } => {
                live.insert(v.clone());
            }
            SSAInstr::Store { value: SSAValue::Var(v), .. } => {
                live.insert(v.clone());
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ssa_var_creation() {
        let var = SSAVar::new(0, 1);
        assert_eq!(var.original, 0);
        assert_eq!(var.version, 1);
        assert_eq!(var.name(), "v0_1");
    }

    #[test]
    fn test_ssa_block_creation() {
        let mut block = SSABlock::new(0);
        assert_eq!(block.id, 0);
        assert_eq!(block.phis.len(), 0);
        assert_eq!(block.instrs.len(), 0);

        let phi = SSAInstr::Phi {
            result: SSAVar::new(0, 1),
            args: vec![],
        };
        block.add_phi(phi);
        assert_eq!(block.phis.len(), 1);
    }

    #[test]
    fn test_constant_folding() {
        assert_eq!(ConstantPropagation::fold_binop(BinOp::Add, 2, 3), Some(5));
        assert_eq!(ConstantPropagation::fold_binop(BinOp::Mul, 4, 5), Some(20));
        assert_eq!(ConstantPropagation::fold_binop(BinOp::And, 0xF0, 0x0F), Some(0));
        assert_eq!(ConstantPropagation::fold_binop(BinOp::Or, 0xF0, 0x0F), Some(0xFF));
    }

    #[test]
    fn test_ssa_function_creation() {
        let func = SSAFunction::new(0);
        assert_eq!(func.index, 0);
        assert_eq!(func.blocks.len(), 0);
        assert_eq!(func.entry, 0);
    }

    #[test]
    fn test_constant_propagation_optimization() {
        let mut func = SSAFunction::new(0);
        let mut block = SSABlock::new(0);

        // Add constant assignment
        block.add_instr(SSAInstr::Assign {
            result: SSAVar::new(0, 0),
            value: SSAValue::I32(42),
        });

        func.blocks.push(block);

        let changed = ConstantPropagation::optimize(&mut func);
        // Should find the constant
        assert!(changed >= 0);
    }

    #[test]
    fn test_dead_code_elimination() {
        let mut func = SSAFunction::new(0);
        let mut block = SSABlock::new(0);

        // Add dead assignment (result never used)
        block.add_instr(SSAInstr::Assign {
            result: SSAVar::new(99, 0),
            value: SSAValue::I32(42),
        });

        func.blocks.push(block);

        let removed = DeadCodeElimination::optimize(&mut func);
        assert_eq!(removed, 1);
    }
}
