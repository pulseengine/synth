//! WebAssembly operation patterns — universal input IR for all backends
//!
//! Every backend (ARM, aWsm, wasker, w2c2) consumes `WasmOp` sequences.
//! This enum lives in synth-core so backends can depend on it without
//! pulling in ARM-specific synthesis types.

use serde::{Deserialize, Serialize};

/// WebAssembly operation patterns
/// Note: Cannot derive Eq because f32/f64 don't implement Eq (NaN != NaN)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
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
    I32Rotl,   // Rotate left
    I32Rotr,   // Rotate right
    I32Clz,    // Count leading zeros
    I32Ctz,    // Count trailing zeros
    I32Popcnt, // Population count (count 1 bits)

    // Sign extension
    I32Extend8S,  // Sign-extend low 8 bits to 32 bits
    I32Extend16S, // Sign-extend low 16 bits to 32 bits

    // Comparison
    I32Eqz, // Equal to zero (unary)
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
    Br(u32),   // Branch to label
    BrIf(u32), // Conditional branch
    BrTable { targets: Vec<u32>, default: u32 },
    Return,
    Call(u32),
    CallIndirect { type_index: u32, table_index: u32 },
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
    // i64 Operations
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
    I64ExtendI32S, // Sign-extend i32 to i64
    I64ExtendI32U, // Zero-extend i32 to i64
    I32WrapI64,    // Wrap i64 to i32 (truncate)

    // i64 In-place sign extension
    I64Extend8S,  // Sign-extend low 8 bits to 64 bits
    I64Extend16S, // Sign-extend low 16 bits to 64 bits
    I64Extend32S, // Sign-extend low 32 bits to 64 bits

    // ========================================================================
    // f32 Operations
    // ========================================================================

    // f32 Arithmetic
    F32Add,
    F32Sub,
    F32Mul,
    F32Div,

    // f32 Comparisons
    F32Eq,
    F32Ne,
    F32Lt,
    F32Le,
    F32Gt,
    F32Ge,

    // f32 Math Functions
    F32Abs,
    F32Neg,
    F32Ceil,
    F32Floor,
    F32Trunc,
    F32Nearest,
    F32Sqrt,
    F32Min,
    F32Max,
    F32Copysign,

    // f32 Constants and Memory
    F32Const(f32),
    F32Load { offset: u32, align: u32 },
    F32Store { offset: u32, align: u32 },

    // f32 Conversions
    F32ConvertI32S,    // Convert signed i32 to f32
    F32ConvertI32U,    // Convert unsigned i32 to f32
    F32ConvertI64S,    // Convert signed i64 to f32
    F32ConvertI64U,    // Convert unsigned i64 to f32
    F32DemoteF64,      // Convert f64 to f32
    F32ReinterpretI32, // Reinterpret i32 bits as f32
    I32ReinterpretF32, // Reinterpret f32 bits as i32
    I32TruncF32S,      // Truncate f32 to signed i32
    I32TruncF32U,      // Truncate f32 to unsigned i32

    // ========================================================================
    // f64 Operations
    // ========================================================================

    // f64 Arithmetic
    F64Add,
    F64Sub,
    F64Mul,
    F64Div,

    // f64 Comparisons
    F64Eq,
    F64Ne,
    F64Lt,
    F64Le,
    F64Gt,
    F64Ge,

    // f64 Math Functions
    F64Abs,
    F64Neg,
    F64Ceil,
    F64Floor,
    F64Trunc,
    F64Nearest,
    F64Sqrt,
    F64Min,
    F64Max,
    F64Copysign,

    // f64 Constants and Memory
    F64Const(f64),
    F64Load { offset: u32, align: u32 },
    F64Store { offset: u32, align: u32 },

    // f64 Conversions
    F64ConvertI32S,    // Convert signed i32 to f64
    F64ConvertI32U,    // Convert unsigned i32 to f64
    F64ConvertI64S,    // Convert signed i64 to f64
    F64ConvertI64U,    // Convert unsigned i64 to f64
    F64PromoteF32,     // Convert f32 to f64
    F64ReinterpretI64, // Reinterpret i64 bits as f64
    I64ReinterpretF64, // Reinterpret f64 bits as i64
    I64TruncF64S,      // Truncate f64 to signed i64
    I64TruncF64U,      // Truncate f64 to unsigned i64
    I32TruncF64S,      // Truncate f64 to signed i32
    I32TruncF64U,      // Truncate f64 to unsigned i32
}
