//! Synthesis Rules for WebAssembly→ARM Optimization
//!
//! ISLE-inspired declarative transformation rules

use serde::{Deserialize, Serialize};

/// Synthesis rule for pattern-based transformations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SynthesisRule {
    /// Rule name/identifier
    pub name: String,

    /// Priority (higher = applied first)
    pub priority: i32,

    /// Pattern to match
    pub pattern: Pattern,

    /// Replacement/transformation
    pub replacement: Replacement,

    /// Cost model (lower is better)
    pub cost: Cost,
}

/// Pattern to match in IR
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Pattern {
    /// Match a WebAssembly instruction
    WasmInstr(WasmOp),

    /// Match a sequence of instructions
    Sequence(Vec<Pattern>),

    /// Match with variable binding
    Var(String, Box<Pattern>),

    /// Match any instruction (wildcard)
    Any,
}

/// WebAssembly operation patterns
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum WasmOp {
    // Arithmetic
    I32Add,
    I32Sub,
    I32Mul,
    I32DivS,
    I32DivU,
    I32RemS,
    I32RemU,

    // Bitwise
    I32And,
    I32Or,
    I32Xor,
    I32Shl,
    I32ShrS,
    I32ShrU,

    // Comparison
    I32Eq,
    I32Ne,
    I32LtS,
    I32LtU,
    I32LeS,
    I32LeU,
    I32GtS,
    I32GtU,
    I32GeS,
    I32GeU,

    // Constants
    I32Const(i32),

    // Memory
    I32Load { offset: u32, align: u32 },
    I32Store { offset: u32, align: u32 },

    // Control flow
    Call(u32),
    LocalGet(u32),
    LocalSet(u32),
}

/// Replacement/transformation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Replacement {
    /// Generate ARM instruction
    ArmInstr(ArmOp),

    /// Sequence of ARM instructions
    ArmSequence(Vec<ArmOp>),

    /// Use a variable from pattern
    Var(String),

    /// Inline function call
    Inline,

    /// No transformation (identity)
    Identity,
}

/// ARM instruction operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ArmOp {
    // Data processing
    Add { rd: Reg, rn: Reg, op2: Operand2 },
    Sub { rd: Reg, rn: Reg, op2: Operand2 },
    Mul { rd: Reg, rn: Reg, rm: Reg },
    And { rd: Reg, rn: Reg, op2: Operand2 },
    Orr { rd: Reg, rn: Reg, op2: Operand2 },
    Eor { rd: Reg, rn: Reg, op2: Operand2 },
    Lsl { rd: Reg, rn: Reg, shift: u32 },
    Lsr { rd: Reg, rn: Reg, shift: u32 },
    Asr { rd: Reg, rn: Reg, shift: u32 },

    // Move
    Mov { rd: Reg, op2: Operand2 },
    Mvn { rd: Reg, op2: Operand2 },

    // Compare
    Cmp { rn: Reg, op2: Operand2 },

    // Load/Store
    Ldr { rd: Reg, addr: MemAddr },
    Str { rd: Reg, addr: MemAddr },

    // Branch
    B { label: String },
    Bl { label: String },
    Bx { rm: Reg },
}

/// ARM register
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Reg {
    R0, R1, R2, R3, R4, R5, R6, R7,
    R8, R9, R10, R11, R12,
    SP,  // Stack pointer (R13)
    LR,  // Link register (R14)
    PC,  // Program counter (R15)
}

/// ARM operand 2 (flexible second operand)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Operand2 {
    /// Immediate value
    Imm(i32),

    /// Register
    Reg(Reg),

    /// Register with shift
    RegShift { rm: Reg, shift: ShiftType, amount: u32 },
}

/// ARM shift types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ShiftType {
    LSL, // Logical shift left
    LSR, // Logical shift right
    ASR, // Arithmetic shift right
    ROR, // Rotate right
}

/// Memory address
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemAddr {
    /// Base register
    pub base: Reg,

    /// Offset
    pub offset: i32,
}

/// Cost model for transformations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Cost {
    /// Cycles (estimated)
    pub cycles: u32,

    /// Code size in bytes
    pub code_size: u32,

    /// Register pressure
    pub registers: u32,
}

impl Cost {
    /// Calculate total cost with weights
    pub fn total(&self) -> u32 {
        // Weight: 1 cycle = 10, 1 byte = 1, 1 register = 5
        self.cycles * 10 + self.code_size + self.registers * 5
    }
}

/// Rule database
pub struct RuleDatabase {
    rules: Vec<SynthesisRule>,
}

impl RuleDatabase {
    /// Create a new empty rule database
    pub fn new() -> Self {
        Self { rules: Vec::new() }
    }

    /// Add a rule
    pub fn add_rule(&mut self, rule: SynthesisRule) {
        self.rules.push(rule);
        // Sort by priority (highest first)
        self.rules.sort_by(|a, b| b.priority.cmp(&a.priority));
    }

    /// Get all rules
    pub fn rules(&self) -> &[SynthesisRule] {
        &self.rules
    }

    /// Create a database with standard optimizations
    pub fn with_standard_rules() -> Self {
        let mut db = Self::new();

        // Rule 1: Strength reduction (mul by power of 2 → shift)
        db.add_rule(SynthesisRule {
            name: "mul_pow2_to_shift".to_string(),
            priority: 100,
            pattern: Pattern::WasmInstr(WasmOp::I32Mul),
            replacement: Replacement::ArmInstr(ArmOp::Lsl {
                rd: Reg::R0,
                rn: Reg::R0,
                shift: 0, // Would be computed from constant
            }),
            cost: Cost {
                cycles: 1,
                code_size: 2,
                registers: 1,
            },
        });

        // Rule 2: Constant folding
        db.add_rule(SynthesisRule {
            name: "const_add_fold".to_string(),
            priority: 90,
            pattern: Pattern::Sequence(vec![
                Pattern::WasmInstr(WasmOp::I32Const(0)),
                Pattern::WasmInstr(WasmOp::I32Const(0)),
                Pattern::WasmInstr(WasmOp::I32Add),
            ]),
            replacement: Replacement::ArmInstr(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(0), // Would be sum of constants
            }),
            cost: Cost {
                cycles: 1,
                code_size: 2,
                registers: 1,
            },
        });

        // Rule 3: ARM instruction fusion (add with shift)
        db.add_rule(SynthesisRule {
            name: "add_with_shift".to_string(),
            priority: 80,
            pattern: Pattern::Sequence(vec![
                Pattern::WasmInstr(WasmOp::I32Shl),
                Pattern::WasmInstr(WasmOp::I32Add),
            ]),
            replacement: Replacement::ArmInstr(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::RegShift {
                    rm: Reg::R2,
                    shift: ShiftType::LSL,
                    amount: 2, // Would be extracted from pattern
                },
            }),
            cost: Cost {
                cycles: 1,
                code_size: 2,
                registers: 3,
            },
        });

        db
    }
}

impl Default for RuleDatabase {
    fn default() -> Self {
        Self::with_standard_rules()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rule_database_creation() {
        let db = RuleDatabase::new();
        assert_eq!(db.rules().len(), 0);
    }

    #[test]
    fn test_standard_rules() {
        let db = RuleDatabase::with_standard_rules();
        assert!(db.rules().len() > 0);

        // Rules should be sorted by priority
        for i in 1..db.rules().len() {
            assert!(db.rules()[i - 1].priority >= db.rules()[i].priority);
        }
    }

    #[test]
    fn test_cost_calculation() {
        let cost = Cost {
            cycles: 2,
            code_size: 4,
            registers: 1,
        };

        // 2*10 + 4 + 1*5 = 29
        assert_eq!(cost.total(), 29);
    }

    #[test]
    fn test_rule_priority_sorting() {
        let mut db = RuleDatabase::new();

        db.add_rule(SynthesisRule {
            name: "low".to_string(),
            priority: 10,
            pattern: Pattern::Any,
            replacement: Replacement::Identity,
            cost: Cost { cycles: 1, code_size: 1, registers: 1 },
        });

        db.add_rule(SynthesisRule {
            name: "high".to_string(),
            priority: 100,
            pattern: Pattern::Any,
            replacement: Replacement::Identity,
            cost: Cost { cycles: 1, code_size: 1, registers: 1 },
        });

        // High priority rule should come first
        assert_eq!(db.rules()[0].name, "high");
        assert_eq!(db.rules()[1].name, "low");
    }
}
