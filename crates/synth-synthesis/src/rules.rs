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
    I32Rotl,      // Rotate left
    I32Rotr,      // Rotate right
    I32Clz,       // Count leading zeros
    I32Ctz,       // Count trailing zeros
    I32Popcnt,    // Population count (count 1 bits)

    // Comparison
    I32Eqz,       // Equal to zero (unary)
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
    Block,
    Loop,
    Br(u32),      // Branch to label
    BrIf(u32),    // Conditional branch
    BrTable { targets: Vec<u32>, default: u32 },
    Return,
    Call(u32),
    CallIndirect(u32),
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    GlobalGet(u32),
    GlobalSet(u32),

    // More ops
    Drop,
    Select,
    If,
    Else,
    End,
    Unreachable,
    Nop,

    // ========================================================================
    // i64 Operations (Phase 2)
    // ========================================================================

    // i64 Arithmetic
    I64Add,
    I64Sub,
    I64Mul,
    I64DivS,
    I64DivU,
    I64RemS,
    I64RemU,

    // i64 Bitwise
    I64And,
    I64Or,
    I64Xor,
    I64Shl,
    I64ShrS,
    I64ShrU,
    I64Rotl,
    I64Rotr,
    I64Clz,
    I64Ctz,
    I64Popcnt,

    // i64 Comparison
    I64Eqz,
    I64Eq,
    I64Ne,
    I64LtS,
    I64LtU,
    I64LeS,
    I64LeU,
    I64GtS,
    I64GtU,
    I64GeS,
    I64GeU,

    // i64 Constants and Memory
    I64Const(i64),
    I64Load { offset: u32, align: u32 },
    I64Store { offset: u32, align: u32 },

    // Conversion operations
    I64ExtendI32S,  // Sign-extend i32 to i64
    I64ExtendI32U,  // Zero-extend i32 to i64
    I32WrapI64,     // Wrap i64 to i32 (truncate)
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
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ArmOp {
    // Data processing
    Add { rd: Reg, rn: Reg, op2: Operand2 },
    Sub { rd: Reg, rn: Reg, op2: Operand2 },
    Mul { rd: Reg, rn: Reg, rm: Reg },
    Sdiv { rd: Reg, rn: Reg, rm: Reg },    // Signed division (ARMv7-M+)
    Udiv { rd: Reg, rn: Reg, rm: Reg },    // Unsigned division (ARMv7-M+)
    Mls { rd: Reg, rn: Reg, rm: Reg, ra: Reg },  // Multiply and subtract (for modulo)
    And { rd: Reg, rn: Reg, op2: Operand2 },
    Orr { rd: Reg, rn: Reg, op2: Operand2 },
    Eor { rd: Reg, rn: Reg, op2: Operand2 },
    Lsl { rd: Reg, rn: Reg, shift: u32 },
    Lsr { rd: Reg, rn: Reg, shift: u32 },
    Asr { rd: Reg, rn: Reg, shift: u32 },
    Ror { rd: Reg, rn: Reg, shift: u32 },  // Rotate right

    // Bit manipulation (ARMv6T2+)
    Clz { rd: Reg, rm: Reg },              // Count leading zeros
    Rbit { rd: Reg, rm: Reg },             // Reverse bits (for CTZ)
    Popcnt { rd: Reg, rm: Reg },           // Population count (pseudo-instruction for verification)

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

    // No operation
    Nop,

    // Conditional execution (for verification)
    // SetCond evaluates a condition based on NZCV flags and sets register to 0 or 1
    SetCond { rd: Reg, cond: Condition },

    // Select operation (for verification)
    // Selects between two values based on condition
    // If rcond != 0, select rval1, else select rval2
    Select { rd: Reg, rval1: Reg, rval2: Reg, rcond: Reg },

    // Local/Global variable access (pseudo-instructions for verification)
    LocalGet { rd: Reg, index: u32 },
    LocalSet { rs: Reg, index: u32 },
    LocalTee { rd: Reg, rs: Reg, index: u32 },
    GlobalGet { rd: Reg, index: u32 },
    GlobalSet { rs: Reg, index: u32 },

    // Control flow operations (pseudo-instructions for verification)
    // These model WASM control flow semantics for verification purposes
    BrTable { rd: Reg, index_reg: Reg, targets: Vec<u32>, default: u32 },
    Call { rd: Reg, func_idx: u32 },
    CallIndirect { rd: Reg, type_idx: u32, table_index_reg: Reg },

    // ========================================================================
    // i64 Operations (Phase 2) - Pseudo-instructions for verification
    // ========================================================================
    // 64-bit operations on ARM32 use register pairs (low:high)
    // These pseudo-instructions abstract multi-register operations
    // Actual compiler would expand these to instruction sequences

    // i64 Arithmetic (register pairs)
    I64Add { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64Sub { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64Mul { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64DivS { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64DivU { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64RemS { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64RemU { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },

    // i64 Bitwise (register pairs)
    I64And { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64Or { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64Xor { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },

    // i64 Shift operations (register pairs, shift amount in single register)
    I64Shl { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, shift: Reg },
    I64ShrS { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, shift: Reg },
    I64ShrU { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, shift: Reg },
    I64Rotl { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, shift: Reg },
    I64Rotr { rdlo: Reg, rdhi: Reg, rnlo: Reg, rnhi: Reg, shift: Reg },

    // i64 Bit manipulation (register pairs)
    I64Clz { rd: Reg, rnlo: Reg, rnhi: Reg },    // Count leading zeros (result is 32-bit)
    I64Ctz { rd: Reg, rnlo: Reg, rnhi: Reg },    // Count trailing zeros
    I64Popcnt { rd: Reg, rnlo: Reg, rnhi: Reg }, // Population count

    // i64 Comparison (register pairs, result in single register)
    I64Eqz { rd: Reg, rnlo: Reg, rnhi: Reg },
    I64Eq { rd: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64Ne { rd: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64LtS { rd: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64LtU { rd: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64LeS { rd: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64LeU { rd: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64GtS { rd: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64GtU { rd: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64GeS { rd: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },
    I64GeU { rd: Reg, rnlo: Reg, rnhi: Reg, rmlo: Reg, rmhi: Reg },

    // i64 Constants (load 64-bit immediate into register pair)
    I64Const { rdlo: Reg, rdhi: Reg, value: i64 },

    // i64 Memory operations (load/store with register pairs)
    I64Ldr { rdlo: Reg, rdhi: Reg, addr: MemAddr },
    I64Str { rdlo: Reg, rdhi: Reg, addr: MemAddr },

    // i64 Conversion operations
    I64ExtendI32S { rdlo: Reg, rdhi: Reg, rn: Reg },  // Sign-extend i32 to i64
    I64ExtendI32U { rdlo: Reg, rdhi: Reg, rn: Reg },  // Zero-extend i32 to i64
    I32WrapI64 { rd: Reg, rnlo: Reg },                // Wrap i64 to i32 (take low 32 bits)
}

/// ARM condition codes (based on NZCV flags)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Condition {
    EQ,  // Equal (Z == 1)
    NE,  // Not equal (Z == 0)
    LT,  // Less than signed (N != V)
    LE,  // Less than or equal signed (Z == 1 || N != V)
    GT,  // Greater than signed (Z == 0 && N == V)
    GE,  // Greater than or equal signed (N == V)
    LO,  // Less than unsigned (C == 0)
    LS,  // Less than or equal unsigned (C == 0 || Z == 1)
    HI,  // Greater than unsigned (C == 1 && Z == 0)
    HS,  // Greater than or equal unsigned (C == 1)
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
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
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
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
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
