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

    fn dfs_post_order(&self, block_id: BlockId, visited: &mut HashSet<BlockId>, post_order: &mut Vec<BlockId>) {
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

    fn intersect(&self, mut b1: BlockId, mut b2: BlockId, doms: &HashMap<BlockId, BlockId>, rpo: &[BlockId]) -> BlockId {
        let rpo_map: HashMap<BlockId, usize> = rpo.iter().enumerate().map(|(i, &b)| (b, i)).collect();

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
                if let Some(&idom) = doms.get(block_id) {
                    if self.dominates(succ, *block_id, &doms) {
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

    fn dominates(&self, dominator: BlockId, block: BlockId, doms: &HashMap<BlockId, BlockId>) -> bool {
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
}

/// Builder for constructing CFGs
pub struct CfgBuilder {
    blocks: Vec<BasicBlock>,
    current_block: Option<BlockId>,
    next_block_id: BlockId,
    instruction_count: usize,
    block_starts: HashMap<usize, BlockId>,
    pending_branches: Vec<(BlockId, usize)>, // (source block, target instruction)
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
            pending_branches: Vec::new(),
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
        let blocks: HashMap<BlockId, BasicBlock> = self.blocks.into_iter().map(|b| (b.id, b)).collect();

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

        let mut cfg = builder.build();

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
}
