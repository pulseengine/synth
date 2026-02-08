//! Peephole Optimizer - Local optimizations on ARM instruction sequences
//!
//! Performs pattern-based optimizations on small windows of instructions

use crate::rules::{ArmOp, Operand2};

/// Peephole optimizer for ARM instructions
pub struct PeepholeOptimizer {
    /// Window size for pattern matching
    #[allow(dead_code)]
    window_size: usize,
}

impl PeepholeOptimizer {
    /// Create a new peephole optimizer
    pub fn new() -> Self {
        Self { window_size: 3 }
    }

    /// Optimize a sequence of ARM instructions
    pub fn optimize(&self, instrs: &[ArmOp]) -> Vec<ArmOp> {
        let mut result = Vec::new();
        let mut i = 0;

        while i < instrs.len() {
            // Try to apply optimizations with different window sizes
            let mut optimized = false;

            // Try 3-instruction patterns
            if i + 2 < instrs.len() {
                if let Some(replacement) =
                    self.try_optimize_3(&instrs[i], &instrs[i + 1], &instrs[i + 2])
                {
                    result.extend(replacement);
                    i += 3;
                    optimized = true;
                }
            }

            // Try 2-instruction patterns
            if !optimized && i + 1 < instrs.len() {
                if let Some(replacement) = self.try_optimize_2(&instrs[i], &instrs[i + 1]) {
                    result.extend(replacement);
                    i += 2;
                    optimized = true;
                }
            }

            // Try 1-instruction patterns
            if !optimized {
                if let Some(replacement) = self.try_optimize_1(&instrs[i]) {
                    result.extend(replacement);
                    i += 1;
                    optimized = true;
                }
            }

            // No optimization found, keep original
            if !optimized {
                result.push(instrs[i].clone());
                i += 1;
            }
        }

        result
    }

    /// Try to optimize a single instruction
    fn try_optimize_1(&self, instr: &ArmOp) -> Option<Vec<ArmOp>> {
        match instr {
            // Remove redundant MOV R0, R0
            ArmOp::Mov {
                rd,
                op2: Operand2::Reg(rs),
            } if rd == rs => Some(vec![]),

            // Remove NOP instructions
            ArmOp::Nop => Some(vec![]),

            // MOV Rd, #0 → better encoded as other instruction if beneficial
            // For now, keep as is
            _ => None,
        }
    }

    /// Try to optimize a pair of instructions
    fn try_optimize_2(&self, instr1: &ArmOp, instr2: &ArmOp) -> Option<Vec<ArmOp>> {
        match (instr1, instr2) {
            // MOV Rd, Rs followed by MOV Rs, Rd → eliminate second if Rd != used after
            // This is simplified - would need liveness analysis
            (
                ArmOp::Mov {
                    rd: rd1,
                    op2: Operand2::Reg(rs1),
                },
                ArmOp::Mov {
                    rd: rd2,
                    op2: Operand2::Reg(rs2),
                },
            ) if rd1 == rs2 && rs1 == rd2 => {
                // Keep only first MOV
                Some(vec![instr1.clone()])
            }

            // ADD Rd, Rn, #0 followed by anything → eliminate ADD
            (
                ArmOp::Add {
                    rd,
                    rn,
                    op2: Operand2::Imm(0),
                },
                _,
            ) if rd == rn => Some(vec![instr2.clone()]),

            // SUB Rd, Rn, #0 → same as above
            (
                ArmOp::Sub {
                    rd,
                    rn,
                    op2: Operand2::Imm(0),
                },
                _,
            ) if rd == rn => Some(vec![instr2.clone()]),

            // STR followed by LDR from same location → eliminate LDR if registers match
            (
                ArmOp::Str {
                    rd: rd1,
                    addr: addr1,
                },
                ArmOp::Ldr {
                    rd: rd2,
                    addr: addr2,
                },
            ) if rd1 == rd2 && addr1 == addr2 => {
                // Keep only STR, value is already in register
                Some(vec![instr1.clone()])
            }

            _ => None,
        }
    }

    /// Try to optimize a triple of instructions
    fn try_optimize_3(&self, instr1: &ArmOp, instr2: &ArmOp, instr3: &ArmOp) -> Option<Vec<ArmOp>> {
        match (instr1, instr2, instr3) {
            // Constant propagation: MOV R0, #X; ADD R1, R0, #Y; → MOV R0, #X; MOV R1, #(X+Y)
            (
                ArmOp::Mov {
                    rd: rd1,
                    op2: Operand2::Imm(val1),
                },
                ArmOp::Add {
                    rd: rd2,
                    rn,
                    op2: Operand2::Imm(val2),
                },
                _,
            ) if rn == rd1 => {
                let new_val = val1.wrapping_add(*val2);
                Some(vec![
                    instr1.clone(),
                    ArmOp::Mov {
                        rd: *rd2,
                        op2: Operand2::Imm(new_val),
                    },
                    instr3.clone(),
                ])
            }

            // Strength reduction: MUL by power of 2 → LSL
            // MOV R0, #2; MUL R1, R2, R0 → MOV R0, #2; LSL R1, R2, #1
            (
                ArmOp::Mov {
                    rd: rd1,
                    op2: Operand2::Imm(val),
                },
                ArmOp::Mul {
                    rd: rd2,
                    rn: rn1,
                    rm: rm1,
                },
                _,
            ) if rm1 == rd1 && is_power_of_2(*val) => {
                let shift = log2_power_of_2(*val);
                Some(vec![
                    instr1.clone(),
                    ArmOp::Lsl {
                        rd: *rd2,
                        rn: *rn1,
                        shift,
                    },
                    instr3.clone(),
                ])
            }

            _ => None,
        }
    }

    /// Optimize with statistics
    pub fn optimize_with_stats(&self, instrs: &[ArmOp]) -> (Vec<ArmOp>, OptimizationStats) {
        let original_count = instrs.len();
        let optimized = self.optimize(instrs);
        let final_count = optimized.len();

        let stats = OptimizationStats {
            original_instructions: original_count,
            optimized_instructions: final_count,
            instructions_removed: original_count.saturating_sub(final_count),
            instructions_replaced: 0, // Would track this with more detailed analysis
        };

        (optimized, stats)
    }
}

impl Default for PeepholeOptimizer {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics from peephole optimization
#[derive(Debug, Clone, Default)]
pub struct OptimizationStats {
    /// Number of instructions before optimization
    pub original_instructions: usize,
    /// Number of instructions after optimization
    pub optimized_instructions: usize,
    /// Number of instructions removed
    pub instructions_removed: usize,
    /// Number of instructions replaced
    pub instructions_replaced: usize,
}

impl OptimizationStats {
    /// Calculate reduction percentage
    pub fn reduction_percentage(&self) -> f64 {
        if self.original_instructions == 0 {
            0.0
        } else {
            (self.instructions_removed as f64 / self.original_instructions as f64) * 100.0
        }
    }
}

/// Check if a number is a power of 2
fn is_power_of_2(n: i32) -> bool {
    n > 0 && (n & (n - 1)) == 0
}

/// Calculate log2 of a power of 2
fn log2_power_of_2(n: i32) -> u32 {
    if n <= 0 {
        return 0;
    }
    let mut count = 0;
    let mut val = n;
    while val > 1 {
        val >>= 1;
        count += 1;
    }
    count
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::Reg;

    #[test]
    fn test_peephole_creation() {
        let optimizer = PeepholeOptimizer::new();
        assert_eq!(optimizer.window_size, 3);
    }

    #[test]
    fn test_remove_redundant_mov() {
        let optimizer = PeepholeOptimizer::new();
        let instrs = vec![
            ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Reg(Reg::R0),
            }, // Redundant
            ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Imm(42),
            },
        ];

        let optimized = optimizer.optimize(&instrs);
        assert_eq!(optimized.len(), 1); // Redundant MOV removed
    }

    #[test]
    fn test_remove_nop() {
        let optimizer = PeepholeOptimizer::new();
        let instrs = vec![
            ArmOp::Nop,
            ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(10),
            },
            ArmOp::Nop,
        ];

        let optimized = optimizer.optimize(&instrs);
        assert_eq!(optimized.len(), 1); // Both NOPs removed
    }

    #[test]
    fn test_eliminate_add_zero() {
        let optimizer = PeepholeOptimizer::new();
        let instrs = vec![
            ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            },
            ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Imm(42),
            },
        ];

        let optimized = optimizer.optimize(&instrs);
        assert_eq!(optimized.len(), 1); // ADD R0, R0, #0 eliminated
    }

    #[test]
    fn test_strength_reduction_mul_to_shift() {
        let optimizer = PeepholeOptimizer::new();
        let instrs = vec![
            ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(4), // Power of 2
            },
            ArmOp::Mul {
                rd: Reg::R1,
                rn: Reg::R2,
                rm: Reg::R0,
            },
            ArmOp::Mov {
                rd: Reg::R3,
                op2: Operand2::Imm(10),
            },
        ];

        let optimized = optimizer.optimize(&instrs);

        // Should have LSL instead of MUL
        match &optimized[1] {
            ArmOp::Lsl { rd, rn, shift } => {
                assert_eq!(*rd, Reg::R1);
                assert_eq!(*rn, Reg::R2);
                assert_eq!(*shift, 2); // log2(4) = 2
            }
            _ => panic!("Expected LSL instruction"),
        }
    }

    #[test]
    fn test_store_load_elimination() {
        let optimizer = PeepholeOptimizer::new();
        let addr = crate::rules::MemAddr::imm(Reg::SP, 0);

        let instrs = vec![
            ArmOp::Str {
                rd: Reg::R0,
                addr: addr.clone(),
            },
            ArmOp::Ldr {
                rd: Reg::R0,
                addr: addr.clone(),
            },
        ];

        let optimized = optimizer.optimize(&instrs);
        assert_eq!(optimized.len(), 1); // LDR eliminated, value already in R0
    }

    #[test]
    fn test_optimize_with_stats() {
        let optimizer = PeepholeOptimizer::new();
        let instrs = vec![
            ArmOp::Nop,
            ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(10),
            },
            ArmOp::Nop,
            ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Reg(Reg::R1),
            }, // Redundant
        ];

        let (_optimized, stats) = optimizer.optimize_with_stats(&instrs);

        assert_eq!(stats.original_instructions, 4);
        assert!(stats.optimized_instructions < 4);
        assert!(stats.instructions_removed > 0);
        assert!(stats.reduction_percentage() > 0.0);
    }

    #[test]
    fn test_is_power_of_2() {
        assert!(is_power_of_2(1));
        assert!(is_power_of_2(2));
        assert!(is_power_of_2(4));
        assert!(is_power_of_2(8));
        assert!(is_power_of_2(16));
        assert!(!is_power_of_2(3));
        assert!(!is_power_of_2(5));
        assert!(!is_power_of_2(0));
        assert!(!is_power_of_2(-2));
    }

    #[test]
    fn test_log2_power_of_2() {
        assert_eq!(log2_power_of_2(1), 0);
        assert_eq!(log2_power_of_2(2), 1);
        assert_eq!(log2_power_of_2(4), 2);
        assert_eq!(log2_power_of_2(8), 3);
        assert_eq!(log2_power_of_2(16), 4);
        assert_eq!(log2_power_of_2(32), 5);
    }

    #[test]
    fn test_no_optimization_needed() {
        let optimizer = PeepholeOptimizer::new();
        let instrs = vec![
            ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            },
            ArmOp::Sub {
                rd: Reg::R3,
                rn: Reg::R4,
                op2: Operand2::Reg(Reg::R5),
            },
        ];

        let optimized = optimizer.optimize(&instrs);
        assert_eq!(optimized.len(), instrs.len()); // No changes
    }

    #[test]
    fn test_reciprocal_moves() {
        let optimizer = PeepholeOptimizer::new();
        let instrs = vec![
            ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            },
            ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Reg(Reg::R0),
            },
        ];

        let optimized = optimizer.optimize(&instrs);
        assert_eq!(optimized.len(), 1); // Second MOV eliminated
    }
}
