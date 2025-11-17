//! Register Allocation for ARM Cortex-M
//!
//! This module implements register allocation using graph coloring for ARM Cortex-M processors.
//! It handles the mapping of virtual registers to physical ARM registers (R0-R12).

use std::collections::{HashMap, HashSet};
use synth_opt::{Instruction, Opcode, Reg};

/// Physical ARM registers available for allocation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PhysicalReg {
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
    R11,
    R12,
    SP,  // Stack Pointer (R13) - reserved
    LR,  // Link Register (R14) - reserved
    PC,  // Program Counter (R15) - reserved
}

impl PhysicalReg {
    /// Get all allocatable registers (R0-R12)
    pub fn allocatable() -> Vec<PhysicalReg> {
        vec![
            PhysicalReg::R0,
            PhysicalReg::R1,
            PhysicalReg::R2,
            PhysicalReg::R3,
            PhysicalReg::R4,
            PhysicalReg::R5,
            PhysicalReg::R6,
            PhysicalReg::R7,
            PhysicalReg::R8,
            PhysicalReg::R9,
            PhysicalReg::R10,
            PhysicalReg::R11,
            PhysicalReg::R12,
        ]
    }

    /// Get caller-saved registers (R0-R3, R12)
    pub fn caller_saved() -> Vec<PhysicalReg> {
        vec![
            PhysicalReg::R0,
            PhysicalReg::R1,
            PhysicalReg::R2,
            PhysicalReg::R3,
            PhysicalReg::R12,
        ]
    }

    /// Get callee-saved registers (R4-R11)
    pub fn callee_saved() -> Vec<PhysicalReg> {
        vec![
            PhysicalReg::R4,
            PhysicalReg::R5,
            PhysicalReg::R6,
            PhysicalReg::R7,
            PhysicalReg::R8,
            PhysicalReg::R9,
            PhysicalReg::R10,
            PhysicalReg::R11,
        ]
    }

    pub fn to_str(&self) -> &'static str {
        match self {
            PhysicalReg::R0 => "r0",
            PhysicalReg::R1 => "r1",
            PhysicalReg::R2 => "r2",
            PhysicalReg::R3 => "r3",
            PhysicalReg::R4 => "r4",
            PhysicalReg::R5 => "r5",
            PhysicalReg::R6 => "r6",
            PhysicalReg::R7 => "r7",
            PhysicalReg::R8 => "r8",
            PhysicalReg::R9 => "r9",
            PhysicalReg::R10 => "r10",
            PhysicalReg::R11 => "r11",
            PhysicalReg::R12 => "r12",
            PhysicalReg::SP => "sp",
            PhysicalReg::LR => "lr",
            PhysicalReg::PC => "pc",
        }
    }
}

/// Live interval for a virtual register
#[derive(Debug, Clone)]
pub struct LiveInterval {
    pub vreg: Reg,
    pub start: usize,
    pub end: usize,
    pub uses: Vec<usize>,
}

/// Interference graph for register allocation
#[derive(Debug, Clone)]
pub struct InterferenceGraph {
    /// Adjacency list: vreg -> set of interfering vregs
    edges: HashMap<Reg, HashSet<Reg>>,
    /// Degree of each node (number of neighbors)
    degree: HashMap<Reg, usize>,
}

impl InterferenceGraph {
    pub fn new() -> Self {
        Self {
            edges: HashMap::new(),
            degree: HashMap::new(),
        }
    }

    /// Add an interference edge between two virtual registers
    pub fn add_interference(&mut self, vreg1: Reg, vreg2: Reg) {
        if vreg1 == vreg2 {
            return;
        }

        // Add edge vreg1 -> vreg2
        self.edges.entry(vreg1).or_insert_with(HashSet::new).insert(vreg2);
        *self.degree.entry(vreg1).or_insert(0) += 1;

        // Add edge vreg2 -> vreg1 (undirected graph)
        self.edges.entry(vreg2).or_insert_with(HashSet::new).insert(vreg1);
        *self.degree.entry(vreg2).or_insert(0) += 1;
    }

    /// Get neighbors of a virtual register
    pub fn neighbors(&self, vreg: &Reg) -> HashSet<Reg> {
        self.edges.get(vreg).cloned().unwrap_or_default()
    }

    /// Get degree of a virtual register
    pub fn degree(&self, vreg: &Reg) -> usize {
        *self.degree.get(vreg).unwrap_or(&0)
    }

    /// Remove a node from the graph
    pub fn remove_node(&mut self, vreg: &Reg) {
        if let Some(neighbors) = self.edges.remove(vreg) {
            for neighbor in neighbors {
                if let Some(neighbor_edges) = self.edges.get_mut(&neighbor) {
                    neighbor_edges.remove(vreg);
                    if let Some(deg) = self.degree.get_mut(&neighbor) {
                        *deg = deg.saturating_sub(1);
                    }
                }
            }
        }
        self.degree.remove(vreg);
    }

    /// Get all nodes in the graph
    pub fn nodes(&self) -> HashSet<Reg> {
        self.edges.keys().cloned().collect()
    }
}

/// Register allocator using graph coloring
pub struct RegisterAllocator {
    /// Number of available physical registers
    num_colors: usize,
    /// Interference graph
    graph: InterferenceGraph,
    /// Live intervals for each virtual register
    live_intervals: HashMap<Reg, LiveInterval>,
    /// Allocation result: vreg -> physical register
    allocation: HashMap<Reg, PhysicalReg>,
    /// Spilled registers (couldn't allocate)
    spills: HashSet<Reg>,
}

impl RegisterAllocator {
    pub fn new() -> Self {
        Self {
            num_colors: PhysicalReg::allocatable().len(),
            graph: InterferenceGraph::new(),
            live_intervals: HashMap::new(),
            allocation: HashMap::new(),
            spills: HashSet::new(),
        }
    }

    /// Compute live intervals using linear scan
    pub fn compute_live_intervals(&mut self, instructions: &[Instruction]) {
        let mut intervals: HashMap<Reg, LiveInterval> = HashMap::new();

        for (idx, inst) in instructions.iter().enumerate() {
            if inst.is_dead {
                continue;
            }

            // Get defined and used registers
            let (defs, uses) = Self::get_def_use(&inst.opcode);

            // Update intervals for used registers
            for &vreg in &uses {
                intervals
                    .entry(vreg)
                    .and_modify(|interval| {
                        interval.end = idx;
                        interval.uses.push(idx);
                    })
                    .or_insert_with(|| LiveInterval {
                        vreg,
                        start: idx,
                        end: idx,
                        uses: vec![idx],
                    });
            }

            // Update intervals for defined registers
            for &vreg in &defs {
                intervals
                    .entry(vreg)
                    .and_modify(|interval| {
                        interval.end = idx;
                    })
                    .or_insert_with(|| LiveInterval {
                        vreg,
                        start: idx,
                        end: idx,
                        uses: vec![idx],
                    });
            }
        }

        self.live_intervals = intervals;
    }

    /// Build interference graph from live intervals
    pub fn build_interference_graph(&mut self) {
        let intervals: Vec<_> = self.live_intervals.values().cloned().collect();

        // Two intervals interfere if they overlap
        for i in 0..intervals.len() {
            for j in (i + 1)..intervals.len() {
                let interval1 = &intervals[i];
                let interval2 = &intervals[j];

                // Check if intervals overlap
                if Self::intervals_overlap(interval1, interval2) {
                    self.graph.add_interference(interval1.vreg, interval2.vreg);
                }
            }
        }
    }

    /// Check if two live intervals overlap
    fn intervals_overlap(i1: &LiveInterval, i2: &LiveInterval) -> bool {
        !(i1.end < i2.start || i2.end < i1.start)
    }

    /// Allocate registers using graph coloring
    pub fn allocate(&mut self) -> Result<(), String> {
        let k = self.num_colors;
        let mut stack: Vec<Reg> = Vec::new();
        let mut graph = self.graph.clone();

        // Simplification: remove nodes with degree < k
        loop {
            let nodes: Vec<Reg> = graph.nodes().into_iter().collect();
            if nodes.is_empty() {
                break;
            }

            let mut removed_any = false;

            for node in nodes {
                if graph.degree(&node) < k {
                    stack.push(node);
                    graph.remove_node(&node);
                    removed_any = true;
                }
            }

            if !removed_any {
                // Spill heuristic: remove node with highest degree
                if let Some(&node) = graph.nodes().iter().max_by_key(|n| graph.degree(n)) {
                    self.spills.insert(node);
                    stack.push(node);
                    graph.remove_node(&node);
                } else {
                    break;
                }
            }
        }

        // Selection: assign colors
        let available_regs = PhysicalReg::allocatable();

        while let Some(vreg) = stack.pop() {
            if self.spills.contains(&vreg) {
                continue; // Skip spilled registers
            }

            // Find colors used by neighbors
            let mut used_colors: HashSet<PhysicalReg> = HashSet::new();
            for neighbor in self.graph.neighbors(&vreg) {
                if let Some(&color) = self.allocation.get(&neighbor) {
                    used_colors.insert(color);
                }
            }

            // Find first available color
            let color = available_regs
                .iter()
                .find(|&reg| !used_colors.contains(reg))
                .ok_or_else(|| format!("Cannot allocate register for {:?}", vreg))?;

            self.allocation.insert(vreg, *color);
        }

        Ok(())
    }

    /// Get the physical register allocated to a virtual register
    pub fn get_allocation(&self, vreg: &Reg) -> Option<PhysicalReg> {
        self.allocation.get(vreg).copied()
    }

    /// Check if a virtual register was spilled
    pub fn is_spilled(&self, vreg: &Reg) -> bool {
        self.spills.contains(vreg)
    }

    /// Get all allocations
    pub fn allocations(&self) -> &HashMap<Reg, PhysicalReg> {
        &self.allocation
    }

    /// Get spilled registers
    pub fn spilled_registers(&self) -> &HashSet<Reg> {
        &self.spills
    }

    /// Extract def and use registers from an opcode
    fn get_def_use(opcode: &Opcode) -> (Vec<Reg>, Vec<Reg>) {
        match opcode {
            Opcode::Const { dest, .. } => (vec![*dest], vec![]),
            Opcode::Add { dest, src1, src2 }
            | Opcode::Sub { dest, src1, src2 }
            | Opcode::Mul { dest, src1, src2 }
            | Opcode::DivS { dest, src1, src2 }
            | Opcode::DivU { dest, src1, src2 }
            | Opcode::RemS { dest, src1, src2 }
            | Opcode::RemU { dest, src1, src2 }
            | Opcode::And { dest, src1, src2 }
            | Opcode::Or { dest, src1, src2 }
            | Opcode::Xor { dest, src1, src2 }
            | Opcode::Shl { dest, src1, src2 }
            | Opcode::ShrS { dest, src1, src2 }
            | Opcode::ShrU { dest, src1, src2 }
            | Opcode::Eq { dest, src1, src2 }
            | Opcode::Ne { dest, src1, src2 }
            | Opcode::LtS { dest, src1, src2 }
            | Opcode::LtU { dest, src1, src2 }
            | Opcode::LeS { dest, src1, src2 }
            | Opcode::LeU { dest, src1, src2 }
            | Opcode::GtS { dest, src1, src2 }
            | Opcode::GtU { dest, src1, src2 }
            | Opcode::GeS { dest, src1, src2 }
            | Opcode::GeU { dest, src1, src2 } => (vec![*dest], vec![*src1, *src2]),
            Opcode::Load { dest, .. } => (vec![*dest], vec![]),
            Opcode::Store { src, .. } => (vec![], vec![*src]),
            Opcode::Return { value } => (vec![], value.map(|v| vec![v]).unwrap_or_default()),
            Opcode::Branch { .. } => (vec![], vec![]),
            Opcode::CondBranch { cond, .. } => (vec![], vec![*cond]),
            Opcode::Nop => (vec![], vec![]),
        }
    }
}

impl Default for RegisterAllocator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_physical_reg_count() {
        assert_eq!(PhysicalReg::allocatable().len(), 13);
        assert_eq!(PhysicalReg::caller_saved().len(), 5);
        assert_eq!(PhysicalReg::callee_saved().len(), 8);
    }

    #[test]
    fn test_interference_graph() {
        let mut graph = InterferenceGraph::new();

        let r0 = Reg(0);
        let r1 = Reg(1);
        let r2 = Reg(2);

        graph.add_interference(r0, r1);
        graph.add_interference(r1, r2);

        assert_eq!(graph.degree(&r0), 1);
        assert_eq!(graph.degree(&r1), 2);
        assert_eq!(graph.degree(&r2), 1);

        assert!(graph.neighbors(&r0).contains(&r1));
        assert!(graph.neighbors(&r1).contains(&r0));
        assert!(graph.neighbors(&r1).contains(&r2));
    }

    #[test]
    fn test_live_intervals_overlap() {
        let i1 = LiveInterval {
            vreg: Reg(0),
            start: 0,
            end: 5,
            uses: vec![],
        };
        let i2 = LiveInterval {
            vreg: Reg(1),
            start: 3,
            end: 8,
            uses: vec![],
        };
        let i3 = LiveInterval {
            vreg: Reg(2),
            start: 6,
            end: 10,
            uses: vec![],
        };

        assert!(RegisterAllocator::intervals_overlap(&i1, &i2));
        assert!(!RegisterAllocator::intervals_overlap(&i1, &i3));
        assert!(RegisterAllocator::intervals_overlap(&i2, &i3));
    }

    #[test]
    fn test_simple_allocation() {
        let mut allocator = RegisterAllocator::new();

        // Simple program: r0 = 1, r1 = 2, r2 = r0 + r1
        let instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const {
                    dest: Reg(0),
                    value: 1,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Const {
                    dest: Reg(1),
                    value: 2,
                },
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

        allocator.compute_live_intervals(&instructions);
        allocator.build_interference_graph();
        allocator.allocate().unwrap();

        // All registers should be allocated
        assert!(allocator.get_allocation(&Reg(0)).is_some());
        assert!(allocator.get_allocation(&Reg(1)).is_some());
        assert!(allocator.get_allocation(&Reg(2)).is_some());

        // r0 and r1 should have different physical registers (they interfere)
        assert_ne!(
            allocator.get_allocation(&Reg(0)),
            allocator.get_allocation(&Reg(1))
        );
    }

    #[test]
    fn test_register_reuse() {
        let mut allocator = RegisterAllocator::new();

        // r0 = 1, r1 = r0 + r0, r2 = r1 + r1
        // r0 can be reused for r2 since it's dead after use
        let instructions = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const {
                    dest: Reg(0),
                    value: 1,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Add {
                    dest: Reg(1),
                    src1: Reg(0),
                    src2: Reg(0),
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::Add {
                    dest: Reg(2),
                    src1: Reg(1),
                    src2: Reg(1),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        allocator.compute_live_intervals(&instructions);
        allocator.build_interference_graph();
        allocator.allocate().unwrap();

        // All registers should be allocated
        assert!(allocator.get_allocation(&Reg(0)).is_some());
        assert!(allocator.get_allocation(&Reg(1)).is_some());
        assert!(allocator.get_allocation(&Reg(2)).is_some());

        // Potentially r0 and r2 could share same physical register
        // (but not guaranteed by current simple allocator)
    }
}
