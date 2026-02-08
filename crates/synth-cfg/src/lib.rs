//! Control Flow Graph (CFG) for WebAssembly Functions
//!
//! This crate provides CFG construction and analysis for WebAssembly functions,
//! enabling proper branch target resolution and optimization.
//!
//! ## Key Concepts
//!
//! - **Basic Block**: A maximal sequence of instructions with single entry and exit
//! - **CFG Edge**: Control flow from one basic block to another
//! - **Dominance**: Block A dominates B if all paths to B go through A
//! - **Loop**: A strongly connected component in the CFG
//!
//! ## Usage
//!
//! ```ignore
//! use synth_cfg::{CfgBuilder, BasicBlock};
//!
//! let mut builder = CfgBuilder::new();
//! builder.add_instruction(/* ... */);
//! let cfg = builder.build();
//! ```

use std::collections::{HashMap, HashSet, VecDeque};

/// A basic block in the CFG
#[derive(Debug, Clone)]
pub struct BasicBlock {
    /// Unique ID for this block
    pub id: BlockId,

    /// Start index in instruction stream
    pub start: usize,

    /// End index (exclusive) in instruction stream
    pub end: usize,

    /// Successor blocks (control flow targets)
    pub successors: Vec<BlockId>,

    /// Predecessor blocks (blocks that jump here)
    pub predecessors: Vec<BlockId>,

    /// Label depth (for structured control flow)
    pub label_depth: usize,

    /// Whether this block is a loop header
    pub is_loop_header: bool,
}

/// Block identifier
pub type BlockId = usize;

/// Control Flow Graph
#[derive(Debug, Clone)]
pub struct Cfg {
    /// All basic blocks
    pub blocks: HashMap<BlockId, BasicBlock>,

    /// Entry block ID
    pub entry: BlockId,

    /// Exit block ID (if function has explicit return)
    pub exit: Option<BlockId>,

    /// Loop information
    pub loops: Vec<Loop>,
}

/// Loop information
#[derive(Debug, Clone)]
pub struct Loop {
    /// Loop header block
    pub header: BlockId,

    /// Blocks in the loop body
    pub body: HashSet<BlockId>,

    /// Loop depth (nested loops have higher depth)
    pub depth: usize,
}

impl Cfg {
    /// Get a basic block by ID
    pub fn block(&self, id: BlockId) -> Option<&BasicBlock> {
        self.blocks.get(&id)
    }

    /// Get a mutable basic block by ID
    pub fn block_mut(&mut self, id: BlockId) -> Option<&mut BasicBlock> {
        self.blocks.get_mut(&id)
    }

    /// Iterate over all blocks in RPO (Reverse Post-Order)
    pub fn blocks_rpo(&self) -> Vec<BlockId> {
        let mut visited = HashSet::new();
        let mut post_order = Vec::new();

        self.dfs_post_order(self.entry, &mut visited, &mut post_order);

        post_order.reverse();
        post_order
    }

    fn dfs_post_order(
        &self,
        block_id: BlockId,
        visited: &mut HashSet<BlockId>,
        post_order: &mut Vec<BlockId>,
    ) {
        if visited.contains(&block_id) {
            return;
        }
        visited.insert(block_id);

        if let Some(block) = self.blocks.get(&block_id) {
            for &succ in &block.successors {
                self.dfs_post_order(succ, visited, post_order);
            }
        }

        post_order.push(block_id);
    }

    /// Compute dominator tree
    pub fn dominators(&self) -> HashMap<BlockId, BlockId> {
        let mut doms = HashMap::new();
        doms.insert(self.entry, self.entry);

        let rpo = self.blocks_rpo();
        let mut changed = true;

        while changed {
            changed = false;
            for &block_id in &rpo {
                if block_id == self.entry {
                    continue;
                }

                let block = self.blocks.get(&block_id).unwrap();

                // Find immediate dominator
                let mut new_idom = None;
                for &pred in &block.predecessors {
                    if doms.contains_key(&pred) {
                        new_idom = Some(if let Some(curr_idom) = new_idom {
                            self.intersect(curr_idom, pred, &doms, &rpo)
                        } else {
                            pred
                        });
                    }
                }

                if let Some(new_idom) = new_idom {
                    if doms.get(&block_id) != Some(&new_idom) {
                        doms.insert(block_id, new_idom);
                        changed = true;
                    }
                }
            }
        }

        doms
    }

    fn intersect(
        &self,
        mut b1: BlockId,
        mut b2: BlockId,
        doms: &HashMap<BlockId, BlockId>,
        rpo: &[BlockId],
    ) -> BlockId {
        let rpo_map: HashMap<BlockId, usize> =
            rpo.iter().enumerate().map(|(i, &b)| (b, i)).collect();

        while b1 != b2 {
            while rpo_map[&b1] > rpo_map[&b2] {
                b1 = doms[&b1];
            }
            while rpo_map[&b2] > rpo_map[&b1] {
                b2 = doms[&b2];
            }
        }

        b1
    }

    /// Detect natural loops in the CFG
    pub fn detect_loops(&mut self) {
        let doms = self.dominators();
        let mut loops = Vec::new();

        // Find back edges (edges where target dominates source)
        for (block_id, block) in &self.blocks {
            for &succ in &block.successors {
                if doms.contains_key(block_id) && self.dominates(succ, *block_id, &doms) {
                    // Back edge found: block_id -> succ is a back edge
                    // succ is the loop header
                    let body = self.find_loop_body(succ, *block_id);
                    loops.push(Loop {
                        header: succ,
                        body,
                        depth: 0, // Will be computed later
                    });
                }
            }
        }

        // Compute loop depths
        for i in 0..loops.len() {
            let mut depth = 1;
            for j in 0..loops.len() {
                if i != j && loops[j].body.contains(&loops[i].header) {
                    depth += 1;
                }
            }
            loops[i].depth = depth;
        }

        self.loops = loops;
    }

    fn dominates(
        &self,
        dominator: BlockId,
        block: BlockId,
        doms: &HashMap<BlockId, BlockId>,
    ) -> bool {
        let mut current = block;
        loop {
            if current == dominator {
                return true;
            }
            if let Some(&idom) = doms.get(&current) {
                if idom == current {
                    return false; // Reached entry
                }
                current = idom;
            } else {
                return false;
            }
        }
    }

    fn find_loop_body(&self, header: BlockId, back_edge_source: BlockId) -> HashSet<BlockId> {
        let mut body = HashSet::new();
        body.insert(header);

        let mut worklist = VecDeque::new();
        worklist.push_back(back_edge_source);

        while let Some(block_id) = worklist.pop_front() {
            if !body.contains(&block_id) {
                body.insert(block_id);

                if let Some(block) = self.blocks.get(&block_id) {
                    for &pred in &block.predecessors {
                        worklist.push_back(pred);
                    }
                }
            }
        }

        body
    }

    /// Find all blocks reachable from entry (helper for optimization)
    pub fn reachable_blocks(&self) -> HashSet<BlockId> {
        let mut reachable = HashSet::new();
        let mut worklist = VecDeque::new();
        worklist.push_back(self.entry);

        while let Some(block_id) = worklist.pop_front() {
            if reachable.contains(&block_id) {
                continue;
            }
            reachable.insert(block_id);

            if let Some(block) = self.blocks.get(&block_id) {
                for &succ in &block.successors {
                    worklist.push_back(succ);
                }
            }
        }

        reachable
    }

    /// Merge basic blocks (CFG optimization)
    /// Merge block B into block A if:
    /// - A has only one successor (B)
    /// - B has only one predecessor (A)
    /// - B is not the entry block
    ///
    /// Returns the number of blocks merged
    pub fn merge_blocks(&mut self) -> usize {
        let mut merged_count = 0;
        let mut changed = true;

        while changed {
            changed = false;
            let blocks: Vec<BlockId> = self.blocks.keys().copied().collect();

            for block_a_id in blocks {
                let can_merge = {
                    let block_a = match self.blocks.get(&block_a_id) {
                        Some(b) => b,
                        None => continue,
                    };

                    if block_a.successors.len() != 1 {
                        continue;
                    }

                    let block_b_id = block_a.successors[0];
                    if block_b_id == self.entry {
                        continue;
                    }

                    let block_b = match self.blocks.get(&block_b_id) {
                        Some(b) => b,
                        None => continue,
                    };

                    if block_b.predecessors.len() != 1 {
                        continue;
                    }

                    Some((block_a_id, block_b_id, block_b.successors.clone()))
                };

                if let Some((a_id, b_id, b_successors)) = can_merge {
                    // Get the end position from block B before borrowing A mutably
                    let b_end = self.blocks.get(&b_id).unwrap().end;

                    // Merge B into A
                    if let Some(block_a) = self.blocks.get_mut(&a_id) {
                        block_a.end = b_end;
                        block_a.successors = b_successors.clone();
                    }

                    // Update successors' predecessors
                    for succ_id in &b_successors {
                        if let Some(succ) = self.blocks.get_mut(succ_id) {
                            succ.predecessors.retain(|&p| p != b_id);
                            if !succ.predecessors.contains(&a_id) {
                                succ.predecessors.push(a_id);
                            }
                        }
                    }

                    // Remove block B
                    self.blocks.remove(&b_id);
                    merged_count += 1;
                    changed = true;
                    break; // Restart to avoid concurrent modification issues
                }
            }
        }

        merged_count
    }

    /// Eliminate unreachable blocks (CFG optimization)
    /// Removes blocks that cannot be reached from the entry block
    /// Returns the number of blocks eliminated
    pub fn eliminate_unreachable(&mut self) -> usize {
        let reachable = self.reachable_blocks();
        let all_blocks: Vec<BlockId> = self.blocks.keys().copied().collect();

        let mut removed_count = 0;
        for block_id in all_blocks {
            if !reachable.contains(&block_id) {
                // Remove unreachable block
                if let Some(block) = self.blocks.remove(&block_id) {
                    // Clean up references from other blocks
                    for succ_id in &block.successors {
                        if let Some(succ) = self.blocks.get_mut(succ_id) {
                            succ.predecessors.retain(|&p| p != block_id);
                        }
                    }
                    for pred_id in &block.predecessors {
                        if let Some(pred) = self.blocks.get_mut(pred_id) {
                            pred.successors.retain(|&s| s != block_id);
                        }
                    }
                    removed_count += 1;
                }
            }
        }

        removed_count
    }

    /// Simplify branches (CFG optimization)
    /// Simplifies control flow by:
    /// - Removing branches to the immediate next block (fall-through)
    /// - Collapsing chains of unconditional branches
    ///
    /// Returns the number of branches simplified
    pub fn simplify_branches(&mut self) -> usize {
        let mut simplified_count = 0;
        let blocks: Vec<BlockId> = self.blocks.keys().copied().collect();

        for block_id in blocks {
            let block = match self.blocks.get(&block_id) {
                Some(b) => b,
                None => continue,
            };

            // Check if this block has a single successor that is just a trampoline
            if block.successors.len() == 1 {
                let succ_id = block.successors[0];
                let succ = match self.blocks.get(&succ_id) {
                    Some(b) => b,
                    None => continue,
                };

                // If successor is an empty trampoline with one successor, bypass it
                if succ.start == succ.end && succ.successors.len() == 1 && succ_id != self.entry {
                    let final_target = succ.successors[0];

                    // Update current block to point to final target
                    if let Some(block_mut) = self.blocks.get_mut(&block_id) {
                        block_mut.successors = vec![final_target];
                    }

                    // Update final target's predecessors
                    if let Some(final_block) = self.blocks.get_mut(&final_target) {
                        if !final_block.predecessors.contains(&block_id) {
                            final_block.predecessors.push(block_id);
                        }
                        final_block.predecessors.retain(|&p| p != succ_id);
                    }

                    simplified_count += 1;
                }
            }
        }

        simplified_count
    }
}

/// Builder for constructing CFGs
pub struct CfgBuilder {
    blocks: Vec<BasicBlock>,
    current_block: Option<BlockId>,
    next_block_id: BlockId,
    instruction_count: usize,
    block_starts: HashMap<usize, BlockId>,
    _pending_branches: Vec<(BlockId, usize)>, // (source block, target instruction)
}

impl CfgBuilder {
    pub fn new() -> Self {
        let entry_block = BasicBlock {
            id: 0,
            start: 0,
            end: 0,
            successors: Vec::new(),
            predecessors: Vec::new(),
            label_depth: 0,
            is_loop_header: false,
        };

        Self {
            blocks: vec![entry_block],
            current_block: Some(0),
            next_block_id: 1,
            instruction_count: 0,
            block_starts: HashMap::from([(0, 0)]),
            _pending_branches: Vec::new(),
        }
    }

    /// Add an instruction to the current block
    pub fn add_instruction(&mut self) {
        if let Some(current_id) = self.current_block {
            if let Some(block) = self.blocks.get_mut(current_id) {
                block.end = self.instruction_count + 1;
            }
        }
        self.instruction_count += 1;
    }

    /// Start a new basic block
    pub fn start_block(&mut self) -> BlockId {
        let block_id = self.next_block_id;
        self.next_block_id += 1;

        let block = BasicBlock {
            id: block_id,
            start: self.instruction_count,
            end: self.instruction_count,
            successors: Vec::new(),
            predecessors: Vec::new(),
            label_depth: 0,
            is_loop_header: false,
        };

        self.blocks.push(block);
        self.block_starts.insert(self.instruction_count, block_id);
        self.current_block = Some(block_id);

        block_id
    }

    /// Add a branch from current block to target block
    pub fn add_branch(&mut self, target: BlockId) {
        if let Some(current_id) = self.current_block {
            if let Some(current_block) = self.blocks.iter_mut().find(|b| b.id == current_id) {
                if !current_block.successors.contains(&target) {
                    current_block.successors.push(target);
                }
            }

            if let Some(target_block) = self.blocks.iter_mut().find(|b| b.id == target) {
                if !target_block.predecessors.contains(&current_id) {
                    target_block.predecessors.push(current_id);
                }
            }
        }
    }

    /// Set the current block (for test purposes)
    pub fn set_current_block(&mut self, block_id: BlockId) {
        self.current_block = Some(block_id);
    }

    /// Mark current block as ending with a terminator
    pub fn terminate_block(&mut self) {
        self.current_block = None;
    }

    /// Build the final CFG
    pub fn build(self) -> Cfg {
        let blocks: HashMap<BlockId, BasicBlock> =
            self.blocks.into_iter().map(|b| (b.id, b)).collect();

        let mut cfg = Cfg {
            blocks,
            entry: 0,
            exit: None,
            loops: Vec::new(),
        };

        cfg.detect_loops();
        cfg
    }
}

impl Default for CfgBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_cfg() {
        let builder = CfgBuilder::new();
        let cfg = builder.build();

        assert_eq!(cfg.blocks.len(), 1);
        assert_eq!(cfg.entry, 0);
    }

    #[test]
    fn test_simple_cfg() {
        let mut builder = CfgBuilder::new();

        // Block 0: entry
        builder.add_instruction(); // inst 0
        builder.add_instruction(); // inst 1

        // Block 1: body
        let block1 = builder.start_block();
        builder.add_instruction(); // inst 2
        builder.add_instruction(); // inst 3

        // Add branch from entry to block1
        builder.current_block = Some(0);
        builder.add_branch(block1);

        let cfg = builder.build();

        assert_eq!(cfg.blocks.len(), 2);
        assert_eq!(cfg.block(0).unwrap().successors, vec![1]);
        assert_eq!(cfg.block(1).unwrap().predecessors, vec![0]);
    }

    #[test]
    fn test_loop_detection() {
        let mut builder = CfgBuilder::new();

        // Entry block
        builder.add_instruction();

        // Loop header
        let loop_header = builder.start_block();
        builder.add_instruction();

        // Loop body
        let loop_body = builder.start_block();
        builder.add_instruction();

        // Exit block
        let exit = builder.start_block();
        builder.add_instruction();

        // Connect blocks
        builder.current_block = Some(0);
        builder.add_branch(loop_header);

        builder.current_block = Some(loop_header);
        builder.add_branch(loop_body);
        builder.add_branch(exit);

        builder.current_block = Some(loop_body);
        builder.add_branch(loop_header); // Back edge

        let cfg = builder.build();

        // Loop detection should find one loop
        assert_eq!(cfg.loops.len(), 1);
        assert_eq!(cfg.loops[0].header, loop_header);
        assert!(cfg.loops[0].body.contains(&loop_header));
        assert!(cfg.loops[0].body.contains(&loop_body));
    }

    #[test]
    fn test_rpo_order() {
        let mut builder = CfgBuilder::new();

        let b1 = builder.start_block();
        let b2 = builder.start_block();

        builder.current_block = Some(0);
        builder.add_branch(b1);

        builder.current_block = Some(b1);
        builder.add_branch(b2);

        let cfg = builder.build();
        let rpo = cfg.blocks_rpo();

        // Entry should come first in RPO
        assert_eq!(rpo[0], 0);
    }

    #[test]
    fn test_dominators() {
        let mut builder = CfgBuilder::new();

        let b1 = builder.start_block();
        let b2 = builder.start_block();

        builder.current_block = Some(0);
        builder.add_branch(b1);

        builder.current_block = Some(b1);
        builder.add_branch(b2);

        let cfg = builder.build();
        let doms = cfg.dominators();

        // Entry dominates itself
        assert_eq!(doms[&0], 0);

        // Entry dominates b1
        assert_eq!(doms[&b1], 0);

        // b1 dominates b2
        assert_eq!(doms[&b2], b1);
    }

    #[test]
    fn test_merge_blocks() {
        let mut builder = CfgBuilder::new();
        builder.add_instruction();

        // Create a chain: entry -> b1 -> b2
        let b1 = builder.start_block();
        builder.add_instruction();

        let b2 = builder.start_block();
        builder.add_instruction();

        builder.current_block = Some(0);
        builder.add_branch(b1);

        builder.current_block = Some(b1);
        builder.add_branch(b2);

        let mut cfg = builder.build();
        assert_eq!(cfg.blocks.len(), 3);

        // Merge blocks
        let merged = cfg.merge_blocks();
        assert_eq!(merged, 2); // b1 and b2 should be merged into entry
        assert_eq!(cfg.blocks.len(), 1);
    }

    #[test]
    fn test_eliminate_unreachable() {
        let mut builder = CfgBuilder::new();
        builder.add_instruction();

        // Create reachable blocks
        let b1 = builder.start_block();
        builder.add_instruction();

        // Create unreachable block
        let b2 = builder.start_block();
        builder.add_instruction();

        // Only connect entry to b1 (b2 is unreachable)
        builder.current_block = Some(0);
        builder.add_branch(b1);

        let mut cfg = builder.build();
        assert_eq!(cfg.blocks.len(), 3);

        // Eliminate unreachable blocks
        let removed = cfg.eliminate_unreachable();
        assert_eq!(removed, 1); // b2 should be removed
        assert_eq!(cfg.blocks.len(), 2);
        assert!(cfg.blocks.contains_key(&0));
        assert!(cfg.blocks.contains_key(&b1));
        assert!(!cfg.blocks.contains_key(&b2));
    }

    #[test]
    fn test_simplify_branches() {
        let mut builder = CfgBuilder::new();
        builder.add_instruction();

        // Create entry -> trampoline -> target
        let trampoline = builder.start_block();
        // Empty trampoline (no instructions)

        let target = builder.start_block();
        builder.add_instruction();

        builder.current_block = Some(0);
        builder.add_branch(trampoline);

        builder.current_block = Some(trampoline);
        builder.add_branch(target);

        let mut cfg = builder.build();

        // Simplify branches
        let simplified = cfg.simplify_branches();
        assert_eq!(simplified, 1);

        // Entry should now point directly to target
        assert_eq!(cfg.block(0).unwrap().successors, vec![target]);
    }

    #[test]
    fn test_reachable_blocks() {
        let mut builder = CfgBuilder::new();
        builder.add_instruction();

        let b1 = builder.start_block();
        builder.add_instruction();

        let b2 = builder.start_block();
        builder.add_instruction();

        let b3 = builder.start_block();
        builder.add_instruction();

        // Connect: entry -> b1 -> b2 (b3 unreachable)
        builder.current_block = Some(0);
        builder.add_branch(b1);

        builder.current_block = Some(b1);
        builder.add_branch(b2);

        let cfg = builder.build();
        let reachable = cfg.reachable_blocks();

        assert_eq!(reachable.len(), 3);
        assert!(reachable.contains(&0));
        assert!(reachable.contains(&b1));
        assert!(reachable.contains(&b2));
        assert!(!reachable.contains(&b3));
    }

    #[test]
    fn test_optimization_pipeline() {
        let mut builder = CfgBuilder::new();
        builder.add_instruction();

        // Create a complex CFG with optimization opportunities
        let b1 = builder.start_block();
        builder.add_instruction();

        let b2 = builder.start_block();
        builder.add_instruction();

        let _unreachable = builder.start_block();
        builder.add_instruction();

        let trampoline = builder.start_block();
        // Empty trampoline

        let target = builder.start_block();
        builder.add_instruction();

        builder.current_block = Some(0);
        builder.add_branch(b1);

        builder.current_block = Some(b1);
        builder.add_branch(b2);

        builder.current_block = Some(b2);
        builder.add_branch(trampoline);

        builder.current_block = Some(trampoline);
        builder.add_branch(target);

        let mut cfg = builder.build();
        let initial_blocks = cfg.blocks.len();

        // Run optimization pipeline
        let eliminated = cfg.eliminate_unreachable();
        let simplified = cfg.simplify_branches();
        let merged = cfg.merge_blocks();

        assert!(eliminated > 0 || simplified > 0 || merged > 0);
        assert!(cfg.blocks.len() < initial_blocks);
    }
}
