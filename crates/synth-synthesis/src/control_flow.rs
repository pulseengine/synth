//! Control Flow Management for WASM → ARM Compilation
//!
//! WASM uses structured control flow (block/loop/if with explicit nesting).
//! ARM uses flat control flow (labels + jumps). This module bridges them.
//!
//! ## Multi-Pass Architecture
//!
//! 1. **Parse pass**: Build control flow structure from WASM ops
//! 2. **Code gen pass**: Generate ARM with placeholder branch offsets
//! 3. **Layout pass**: Compute instruction sizes and positions
//! 4. **Resolution pass**: Patch branch offsets (may iterate until stable)
//!
//! ## WASM Control Flow Model
//!
//! - `block...end` - Label at END (br jumps forward, exits block)
//! - `loop...end` - Label at START (br jumps backward, repeats loop)
//! - `if...else...end` - Conditional execution
//! - `br N` - Jump to Nth enclosing label
//! - `br_if N` - Conditional jump

use std::collections::HashMap;

/// A label in the generated code
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Label(pub u32);

/// Control flow block type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockType {
    /// Regular block - label at end (forward branch target)
    Block,
    /// Loop - label at start (backward branch target)
    Loop,
    /// If block - has conditional branch at start
    If,
    /// Function - implicit outermost block
    Function,
}

/// A control flow block on the stack
#[derive(Debug, Clone)]
pub struct ControlBlock {
    /// Type of this block
    pub block_type: BlockType,
    /// Label for this block's branch target
    pub label: Label,
    /// Instruction index where block starts
    pub start_index: usize,
    /// Instruction index where block ends (filled in when we see End)
    pub end_index: Option<usize>,
    /// For If blocks: index of the conditional branch instruction
    pub branch_index: Option<usize>,
    /// For If blocks with Else: index of the unconditional branch at end of then
    pub else_branch_index: Option<usize>,
    /// Index where Else starts (if present)
    pub else_index: Option<usize>,
}

/// Branch instruction with placeholder offset
#[derive(Debug, Clone)]
pub struct PendingBranch {
    /// Index in the instruction list
    pub instr_index: usize,
    /// Target label
    pub target_label: Label,
    /// Is this a conditional branch?
    pub is_conditional: bool,
    /// For conditional: which condition (true = taken if condition true)
    pub condition_true: bool,
}

/// Manages control flow during compilation
#[derive(Debug)]
pub struct ControlFlowManager {
    /// Stack of active control blocks (innermost last)
    block_stack: Vec<ControlBlock>,
    /// Next label ID
    next_label: u32,
    /// All pending branches that need offset resolution
    pending_branches: Vec<PendingBranch>,
    /// Label positions (instruction index where each label points)
    label_positions: HashMap<Label, usize>,
    /// Current instruction index
    current_index: usize,
}

impl ControlFlowManager {
    pub fn new() -> Self {
        Self {
            block_stack: Vec::new(),
            next_label: 0,
            pending_branches: Vec::new(),
            label_positions: HashMap::new(),
            current_index: 0,
        }
    }

    /// Start a new function (implicit outermost block)
    pub fn enter_function(&mut self) {
        let label = self.alloc_label();
        self.block_stack.push(ControlBlock {
            block_type: BlockType::Function,
            label,
            start_index: self.current_index,
            end_index: None,
            branch_index: None,
            else_branch_index: None,
            else_index: None,
        });
    }

    /// Allocate a new label
    fn alloc_label(&mut self) -> Label {
        let label = Label(self.next_label);
        self.next_label += 1;
        label
    }

    /// Enter a block (block, loop, or if)
    pub fn enter_block(&mut self, block_type: BlockType) -> Label {
        let label = self.alloc_label();

        // For loops, the label points to the START
        if block_type == BlockType::Loop {
            self.label_positions.insert(label, self.current_index);
        }

        self.block_stack.push(ControlBlock {
            block_type,
            label,
            start_index: self.current_index,
            end_index: None,
            branch_index: None,
            else_branch_index: None,
            else_index: None,
        });

        label
    }

    /// Record a conditional branch at the start of an If block
    pub fn record_if_branch(&mut self, instr_index: usize) {
        if let Some(block) = self.block_stack.last_mut() {
            if block.block_type == BlockType::If {
                block.branch_index = Some(instr_index);
            }
        }
    }

    /// Handle Else - record the jump from then-block and start else-block
    pub fn handle_else(&mut self, jump_instr_index: usize) {
        if let Some(block) = self.block_stack.last_mut() {
            if block.block_type == BlockType::If {
                block.else_branch_index = Some(jump_instr_index);
                block.else_index = Some(self.current_index);
            }
        }
    }

    /// Exit current block (End instruction)
    pub fn exit_block(&mut self) -> Option<ControlBlock> {
        if let Some(mut block) = self.block_stack.pop() {
            block.end_index = Some(self.current_index);

            // For blocks (not loops), the label points to the END
            if block.block_type != BlockType::Loop {
                self.label_positions.insert(block.label, self.current_index);
            }

            Some(block)
        } else {
            None
        }
    }

    /// Record a branch instruction that needs offset resolution
    pub fn record_branch(&mut self, instr_index: usize, relative_depth: u32, is_conditional: bool) {
        // Find the target block (relative_depth 0 = innermost)
        let stack_len = self.block_stack.len();
        if relative_depth as usize >= stack_len {
            return; // Invalid depth
        }

        let target_idx = stack_len - 1 - relative_depth as usize;
        let target_label = self.block_stack[target_idx].label;

        self.pending_branches.push(PendingBranch {
            instr_index,
            target_label,
            is_conditional,
            condition_true: true, // br/br_if branch when condition is non-zero
        });
    }

    /// Increment instruction counter
    pub fn add_instruction(&mut self) {
        self.current_index += 1;
    }

    /// Add multiple instructions
    pub fn add_instructions(&mut self, count: usize) {
        self.current_index += count;
    }

    /// Get the current instruction index
    pub fn current_index(&self) -> usize {
        self.current_index
    }

    /// Get all pending branches for resolution
    pub fn pending_branches(&self) -> &[PendingBranch] {
        &self.pending_branches
    }

    /// Get label position
    pub fn label_position(&self, label: Label) -> Option<usize> {
        self.label_positions.get(&label).copied()
    }

    /// Get current block depth
    pub fn depth(&self) -> usize {
        self.block_stack.len()
    }

    /// Get the innermost block
    pub fn current_block(&self) -> Option<&ControlBlock> {
        self.block_stack.last()
    }
}

impl Default for ControlFlowManager {
    fn default() -> Self {
        Self::new()
    }
}

/// Resolve branch offsets in generated code
///
/// This is the "fixed-point iteration" pass that resolves all branch offsets.
/// Returns true if all branches were resolved successfully.
pub fn resolve_branches<T: BranchableInstruction>(
    instructions: &mut [T],
    pending: &[PendingBranch],
    label_positions: &HashMap<Label, usize>,
) -> bool {
    let mut all_resolved = true;

    for branch in pending {
        if let Some(&target_pos) = label_positions.get(&branch.target_label) {
            // Calculate offset from branch instruction to target
            // In ARM, offset is relative to PC+4 (pipeline)
            let branch_pos = branch.instr_index;
            let offset = target_pos as i32 - branch_pos as i32;

            if branch_pos < instructions.len() {
                instructions[branch_pos].set_branch_offset(offset);
            } else {
                all_resolved = false;
            }
        } else {
            all_resolved = false;
        }
    }

    all_resolved
}

/// Trait for instructions that can have branch offsets
pub trait BranchableInstruction {
    fn set_branch_offset(&mut self, offset: i32);
    fn is_branch(&self) -> bool;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_block_stack() {
        let mut cf = ControlFlowManager::new();
        cf.enter_function();

        // Enter a block
        let block_label = cf.enter_block(BlockType::Block);
        assert_eq!(cf.depth(), 2); // Function + Block

        cf.add_instruction(); // Some code in block
        cf.add_instruction();

        // Exit block
        let block = cf.exit_block().unwrap();
        assert_eq!(block.block_type, BlockType::Block);
        assert_eq!(block.label, block_label);

        // Label should point to end
        assert!(cf.label_position(block_label).is_some());
    }

    #[test]
    fn test_loop_label_at_start() {
        let mut cf = ControlFlowManager::new();
        cf.enter_function();

        let start_idx = cf.current_index();
        let loop_label = cf.enter_block(BlockType::Loop);

        // Loop label should be set immediately (at start)
        assert_eq!(cf.label_position(loop_label), Some(start_idx));

        cf.add_instruction();
        cf.add_instruction();
        cf.exit_block();

        // Label should still point to start
        assert_eq!(cf.label_position(loop_label), Some(start_idx));
    }

    #[test]
    fn test_nested_blocks() {
        let mut cf = ControlFlowManager::new();
        cf.enter_function();

        let outer = cf.enter_block(BlockType::Block);
        cf.add_instruction();

        let _inner = cf.enter_block(BlockType::Block);
        cf.add_instruction();

        // Record a branch to outer block (depth 1)
        cf.record_branch(cf.current_index(), 1, false);
        cf.add_instruction();

        cf.exit_block(); // inner
        cf.add_instruction();
        cf.exit_block(); // outer

        // Check pending branches
        assert_eq!(cf.pending_branches().len(), 1);
        assert_eq!(cf.pending_branches()[0].target_label, outer);
    }
}
