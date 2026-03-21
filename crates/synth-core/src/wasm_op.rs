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

    // Sub-word loads (i32)
    I32Load8S { offset: u32, align: u32 }, // byte load, sign-extend to i32
    I32Load8U { offset: u32, align: u32 }, // byte load, zero-extend to i32
    I32Load16S { offset: u32, align: u32 }, // halfword load, sign-extend to i32
    I32Load16U { offset: u32, align: u32 }, // halfword load, zero-extend to i32

    // Sub-word stores (i32)
    I32Store8 { offset: u32, align: u32 },  // store low byte
    I32Store16 { offset: u32, align: u32 }, // store low halfword

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

    // Memory management
    MemorySize(u32), // returns current memory size in pages (memory index)
    MemoryGrow(u32), // grow memory by N pages, returns previous size or -1 (memory index)

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

    // Sub-word loads (i64) — load sub-word, extend to i64
    I64Load8S { offset: u32, align: u32 },
    I64Load8U { offset: u32, align: u32 },
    I64Load16S { offset: u32, align: u32 },
    I64Load16U { offset: u32, align: u32 },
    I64Load32S { offset: u32, align: u32 },
    I64Load32U { offset: u32, align: u32 },

    // Sub-word stores (i64) — store low N bits
    I64Store8 { offset: u32, align: u32 },
    I64Store16 { offset: u32, align: u32 },
    I64Store32 { offset: u32, align: u32 },

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

    // ========================================================================
    // v128 SIMD Operations (WASM SIMD proposal)
    // ========================================================================
    // Targets ARM Cortex-M55 Helium MVE (M-Profile Vector Extension)

    // v128 Constants and Memory
    V128Const([u8; 16]),                   // 128-bit constant
    V128Load { offset: u32, align: u32 },  // v128.load
    V128Store { offset: u32, align: u32 }, // v128.store

    // v128 Bitwise operations
    V128And,    // v128.and
    V128Or,     // v128.or
    V128Xor,    // v128.xor
    V128Not,    // v128.not
    V128AndNot, // v128.andnot

    // i8x16 integer SIMD
    I8x16Add,               // i8x16.add
    I8x16Sub,               // i8x16.sub
    I8x16Neg,               // i8x16.neg
    I8x16Eq,                // i8x16.eq
    I8x16Ne,                // i8x16.ne
    I8x16LtS,               // i8x16.lt_s
    I8x16LtU,               // i8x16.lt_u
    I8x16GtS,               // i8x16.gt_s
    I8x16GtU,               // i8x16.gt_u
    I8x16LeS,               // i8x16.le_s
    I8x16LeU,               // i8x16.le_u
    I8x16GeS,               // i8x16.ge_s
    I8x16GeU,               // i8x16.ge_u
    I8x16Splat,             // i8x16.splat
    I8x16ExtractLaneS(u8),  // i8x16.extract_lane_s
    I8x16ExtractLaneU(u8),  // i8x16.extract_lane_u
    I8x16ReplaceLane(u8),   // i8x16.replace_lane
    I8x16Shuffle([u8; 16]), // i8x16.shuffle
    I8x16Swizzle,           // i8x16.swizzle

    // i16x8 integer SIMD
    I16x8Add,              // i16x8.add
    I16x8Sub,              // i16x8.sub
    I16x8Mul,              // i16x8.mul
    I16x8Neg,              // i16x8.neg
    I16x8Eq,               // i16x8.eq
    I16x8Ne,               // i16x8.ne
    I16x8LtS,              // i16x8.lt_s
    I16x8LtU,              // i16x8.lt_u
    I16x8GtS,              // i16x8.gt_s
    I16x8GtU,              // i16x8.gt_u
    I16x8LeS,              // i16x8.le_s
    I16x8LeU,              // i16x8.le_u
    I16x8GeS,              // i16x8.ge_s
    I16x8GeU,              // i16x8.ge_u
    I16x8Splat,            // i16x8.splat
    I16x8ExtractLaneS(u8), // i16x8.extract_lane_s
    I16x8ExtractLaneU(u8), // i16x8.extract_lane_u
    I16x8ReplaceLane(u8),  // i16x8.replace_lane

    // i32x4 integer SIMD
    I32x4Add,             // i32x4.add
    I32x4Sub,             // i32x4.sub
    I32x4Mul,             // i32x4.mul
    I32x4Neg,             // i32x4.neg
    I32x4Eq,              // i32x4.eq
    I32x4Ne,              // i32x4.ne
    I32x4LtS,             // i32x4.lt_s
    I32x4LtU,             // i32x4.lt_u
    I32x4GtS,             // i32x4.gt_s
    I32x4GtU,             // i32x4.gt_u
    I32x4LeS,             // i32x4.le_s
    I32x4LeU,             // i32x4.le_u
    I32x4GeS,             // i32x4.ge_s
    I32x4GeU,             // i32x4.ge_u
    I32x4Splat,           // i32x4.splat
    I32x4ExtractLane(u8), // i32x4.extract_lane
    I32x4ReplaceLane(u8), // i32x4.replace_lane

    // i64x2 integer SIMD
    I64x2Add,             // i64x2.add
    I64x2Sub,             // i64x2.sub
    I64x2Mul,             // i64x2.mul
    I64x2Neg,             // i64x2.neg
    I64x2Eq,              // i64x2.eq
    I64x2Ne,              // i64x2.ne
    I64x2LtS,             // i64x2.lt_s
    I64x2GtS,             // i64x2.gt_s
    I64x2LeS,             // i64x2.le_s
    I64x2GeS,             // i64x2.ge_s
    I64x2Splat,           // i64x2.splat
    I64x2ExtractLane(u8), // i64x2.extract_lane
    I64x2ReplaceLane(u8), // i64x2.replace_lane

    // f32x4 floating-point SIMD
    F32x4Add,             // f32x4.add
    F32x4Sub,             // f32x4.sub
    F32x4Mul,             // f32x4.mul
    F32x4Div,             // f32x4.div
    F32x4Abs,             // f32x4.abs
    F32x4Neg,             // f32x4.neg
    F32x4Sqrt,            // f32x4.sqrt
    F32x4Eq,              // f32x4.eq
    F32x4Ne,              // f32x4.ne
    F32x4Lt,              // f32x4.lt
    F32x4Le,              // f32x4.le
    F32x4Gt,              // f32x4.gt
    F32x4Ge,              // f32x4.ge
    F32x4Splat,           // f32x4.splat
    F32x4ExtractLane(u8), // f32x4.extract_lane
    F32x4ReplaceLane(u8), // f32x4.replace_lane
}
