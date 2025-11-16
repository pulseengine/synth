//! Intermediate Representation for synthesis

use serde::{Deserialize, Serialize};

/// Synthesis Intermediate Representation
///
/// This is a simplified IR for the PoC. In production, this would be much more
/// sophisticated, potentially using e-graphs for optimization.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SynthIR {
    /// Functions in IR form
    pub functions: Vec<IRFunction>,

    /// Global data
    pub globals: Vec<IRGlobal>,

    /// Memory regions
    pub memories: Vec<IRMemory>,
}

/// IR Function
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IRFunction {
    /// Function name
    pub name: String,

    /// Parameters
    pub params: Vec<IRValue>,

    /// Results
    pub results: Vec<IRValue>,

    /// Basic blocks
    pub blocks: Vec<IRBlock>,
}

/// IR Basic Block
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IRBlock {
    /// Block label
    pub label: String,

    /// Instructions in this block
    pub instructions: Vec<IRInstruction>,

    /// Terminator instruction
    pub terminator: IRTerminator,
}

/// IR Instruction
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum IRInstruction {
    /// Binary operation
    BinOp {
        op: BinOp,
        dest: IRValue,
        left: IRValue,
        right: IRValue,
    },

    /// Unary operation
    UnOp {
        op: UnOp,
        dest: IRValue,
        operand: IRValue,
    },

    /// Load from memory
    Load {
        dest: IRValue,
        address: IRValue,
        offset: i32,
    },

    /// Store to memory
    Store {
        address: IRValue,
        value: IRValue,
        offset: i32,
    },

    /// Call function
    Call {
        function: String,
        args: Vec<IRValue>,
        dest: Option<IRValue>,
    },
}

/// IR Terminator (ends a basic block)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum IRTerminator {
    /// Return from function
    Return(Option<IRValue>),

    /// Branch to block
    Branch(String),

    /// Conditional branch
    BranchIf {
        condition: IRValue,
        true_block: String,
        false_block: String,
    },

    /// Unreachable code
    Unreachable,
}

/// Binary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinOp {
    // Integer arithmetic
    IAdd,
    ISub,
    IMul,
    IDivS,
    IDivU,
    IRemS,
    IRemU,

    // Integer bitwise
    IAnd,
    IOr,
    IXor,
    IShl,
    IShrS,
    IShrU,
    IRotl,
    IRotr,

    // Integer comparison
    IEq,
    INe,
    ILtS,
    ILtU,
    ILeS,
    ILeU,
    IGtS,
    IGtU,
    IGeS,
    IGeU,

    // Float arithmetic
    FAdd,
    FSub,
    FMul,
    FDiv,
    FMin,
    FMax,

    // Float comparison
    FEq,
    FNe,
    FLt,
    FLe,
    FGt,
    FGe,
}

/// Unary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnOp {
    // Integer
    IClz,
    ICtz,
    IPopcnt,
    IEqz,

    // Float
    FAbs,
    FNeg,
    FSqrt,
    FCeil,
    FFloor,
    FTrunc,
    FNearest,

    // Conversions
    I32WrapI64,
    I64ExtendI32S,
    I64ExtendI32U,
    F32DemoteF64,
    F64PromoteF32,
}

/// IR Value
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum IRValue {
    /// Local variable
    Local(u32),

    /// Constant integer
    ConstI32(i32),
    ConstI64(i64),

    /// Constant float
    ConstF32(f32),
    ConstF64(f64),

    /// Global variable
    Global(u32),
}

/// IR Global
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IRGlobal {
    /// Global index
    pub index: u32,

    /// Initial value
    pub init: IRValue,

    /// Is mutable
    pub mutable: bool,
}

/// IR Memory
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IRMemory {
    /// Memory index
    pub index: u32,

    /// Initial size in pages
    pub initial: u32,

    /// Maximum size in pages (if limited)
    pub maximum: Option<u32>,
}

impl SynthIR {
    /// Create empty IR
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
            globals: Vec::new(),
            memories: Vec::new(),
        }
    }
}

impl Default for SynthIR {
    fn default() -> Self {
        Self::new()
    }
}
