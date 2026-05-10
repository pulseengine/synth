//! Compact `Arbitrary`-able mirror of `synth_core::WasmOp`.
//!
//! The full `WasmOp` enum has ~250 variants and contains `f32`/`f64`
//! payloads, which complicate `Arbitrary` derivation. We instead define a
//! curated subset that targets the most-bug-prone instruction surfaces:
//!
//! * i32 + i64 arithmetic / bitwise / shift / rotate / comparison
//! * i32 ↔ i64 conversions (`I64ExtendI32U`, `I64ExtendI32S`, `I32WrapI64`)
//!   — the exact ops that issue #93 silently dropped
//! * `LocalGet` / `LocalSet` / `LocalTee` (i32 + i64 locals)
//! * `Drop` / `Nop` / `Return`
//!
//! Each `FuzzOp` lowers to exactly one `synth_core::WasmOp`, so a libfuzzer
//! crash gives you a deterministic, replayable WASM op sequence.

use arbitrary::Arbitrary;
use synth_core::WasmOp;

/// Top-level fuzz input: a parameter count and a vector of ops.
#[derive(Arbitrary, Debug, Clone)]
pub struct FuzzInput {
    /// AAPCS param count (R0..R3, capped at 4 in lowering).
    pub num_params: u32,
    /// Sequence of operations to feed the lowering pipeline.
    pub ops: Vec<FuzzOp>,
}

/// Curated subset of `WasmOp` (see module docs for rationale).
///
/// `Arbitrary`-derived: libfuzzer generates these directly.
#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum FuzzOp {
    // ---- i32 arithmetic / bitwise ------------------------------------
    I32Const(i32),
    I32Add,
    I32Sub,
    I32Mul,
    I32And,
    I32Or,
    I32Xor,
    I32Shl,
    I32ShrS,
    I32ShrU,
    I32Rotl,
    I32Rotr,
    I32Clz,
    I32Ctz,
    I32Popcnt,
    I32Eqz,
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
    I32Extend8S,
    I32Extend16S,
    I32DivS,
    I32DivU,
    I32RemS,
    I32RemU,

    // ---- i64 — the AAPCS / register-pair surface ---------------------
    I64Const(i64),
    I64Add,
    I64Sub,
    I64Mul,
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

    // ---- i32 ↔ i64 conversion — issue #93 root cause -----------------
    I64ExtendI32S,
    I64ExtendI32U,
    I32WrapI64,
    I64Extend8S,
    I64Extend16S,
    I64Extend32S,

    // ---- locals (param register reads + writes) ----------------------
    LocalGet(u8),
    LocalSet(u8),
    LocalTee(u8),

    // ---- misc --------------------------------------------------------
    Drop,
    Nop,
    Return,
    Unreachable,
}

impl FuzzOp {
    /// Whether this op pushes a *value* onto the wasm value stack.
    ///
    /// Used by `wasm_to_ir_roundtrip_op_coverage` to assert that every
    /// value-producing op leaves at least one IR instruction behind.
    /// Issue #93 was caused by `wasm_to_ir` silently emitting `Opcode::Nop`
    /// for I64ExtendI32U / I64ExtendI32S / I32WrapI64 — i.e. value-producing
    /// ops that became no-ops in IR.
    pub fn produces_value(&self) -> bool {
        use FuzzOp::*;
        match self {
            // Pushes a value on the wasm stack.
            I32Const(_) | I64Const(_) | I32Add | I32Sub | I32Mul | I32And | I32Or | I32Xor
            | I32Shl | I32ShrS | I32ShrU | I32Rotl | I32Rotr | I32Clz | I32Ctz | I32Popcnt
            | I32Eqz | I32Eq | I32Ne | I32LtS | I32LtU | I32LeS | I32LeU | I32GtS | I32GtU
            | I32GeS | I32GeU | I32Extend8S | I32Extend16S | I32DivS | I32DivU | I32RemS
            | I32RemU | I64Add | I64Sub | I64Mul | I64And | I64Or | I64Xor | I64Shl | I64ShrS
            | I64ShrU | I64Rotl | I64Rotr | I64Clz | I64Ctz | I64Popcnt | I64Eqz | I64Eq
            | I64Ne | I64LtS | I64LtU | I64LeS | I64LeU | I64GtS | I64GtU | I64GeS | I64GeU
            | I64ExtendI32S | I64ExtendI32U | I32WrapI64 | I64Extend8S | I64Extend16S
            | I64Extend32S | LocalGet(_) | LocalTee(_) => true,
            // No value pushed.
            LocalSet(_) | Drop | Nop | Return | Unreachable => false,
        }
    }

    /// Whether this op is one of the i32↔i64 conversions that issue #93
    /// silently dropped.
    pub fn is_issue_93_conversion(&self) -> bool {
        matches!(
            self,
            FuzzOp::I64ExtendI32S | FuzzOp::I64ExtendI32U | FuzzOp::I32WrapI64
        )
    }

    /// Convert to the canonical `synth_core::WasmOp`.
    pub fn to_wasm_op(self, num_params: u32) -> WasmOp {
        let local_max = num_params.max(1);
        match self {
            FuzzOp::I32Const(v) => WasmOp::I32Const(v),
            FuzzOp::I32Add => WasmOp::I32Add,
            FuzzOp::I32Sub => WasmOp::I32Sub,
            FuzzOp::I32Mul => WasmOp::I32Mul,
            FuzzOp::I32And => WasmOp::I32And,
            FuzzOp::I32Or => WasmOp::I32Or,
            FuzzOp::I32Xor => WasmOp::I32Xor,
            FuzzOp::I32Shl => WasmOp::I32Shl,
            FuzzOp::I32ShrS => WasmOp::I32ShrS,
            FuzzOp::I32ShrU => WasmOp::I32ShrU,
            FuzzOp::I32Rotl => WasmOp::I32Rotl,
            FuzzOp::I32Rotr => WasmOp::I32Rotr,
            FuzzOp::I32Clz => WasmOp::I32Clz,
            FuzzOp::I32Ctz => WasmOp::I32Ctz,
            FuzzOp::I32Popcnt => WasmOp::I32Popcnt,
            FuzzOp::I32Eqz => WasmOp::I32Eqz,
            FuzzOp::I32Eq => WasmOp::I32Eq,
            FuzzOp::I32Ne => WasmOp::I32Ne,
            FuzzOp::I32LtS => WasmOp::I32LtS,
            FuzzOp::I32LtU => WasmOp::I32LtU,
            FuzzOp::I32LeS => WasmOp::I32LeS,
            FuzzOp::I32LeU => WasmOp::I32LeU,
            FuzzOp::I32GtS => WasmOp::I32GtS,
            FuzzOp::I32GtU => WasmOp::I32GtU,
            FuzzOp::I32GeS => WasmOp::I32GeS,
            FuzzOp::I32GeU => WasmOp::I32GeU,
            FuzzOp::I32Extend8S => WasmOp::I32Extend8S,
            FuzzOp::I32Extend16S => WasmOp::I32Extend16S,
            FuzzOp::I32DivS => WasmOp::I32DivS,
            FuzzOp::I32DivU => WasmOp::I32DivU,
            FuzzOp::I32RemS => WasmOp::I32RemS,
            FuzzOp::I32RemU => WasmOp::I32RemU,
            FuzzOp::I64Const(v) => WasmOp::I64Const(v),
            FuzzOp::I64Add => WasmOp::I64Add,
            FuzzOp::I64Sub => WasmOp::I64Sub,
            FuzzOp::I64Mul => WasmOp::I64Mul,
            FuzzOp::I64And => WasmOp::I64And,
            FuzzOp::I64Or => WasmOp::I64Or,
            FuzzOp::I64Xor => WasmOp::I64Xor,
            FuzzOp::I64Shl => WasmOp::I64Shl,
            FuzzOp::I64ShrS => WasmOp::I64ShrS,
            FuzzOp::I64ShrU => WasmOp::I64ShrU,
            FuzzOp::I64Rotl => WasmOp::I64Rotl,
            FuzzOp::I64Rotr => WasmOp::I64Rotr,
            FuzzOp::I64Clz => WasmOp::I64Clz,
            FuzzOp::I64Ctz => WasmOp::I64Ctz,
            FuzzOp::I64Popcnt => WasmOp::I64Popcnt,
            FuzzOp::I64Eqz => WasmOp::I64Eqz,
            FuzzOp::I64Eq => WasmOp::I64Eq,
            FuzzOp::I64Ne => WasmOp::I64Ne,
            FuzzOp::I64LtS => WasmOp::I64LtS,
            FuzzOp::I64LtU => WasmOp::I64LtU,
            FuzzOp::I64LeS => WasmOp::I64LeS,
            FuzzOp::I64LeU => WasmOp::I64LeU,
            FuzzOp::I64GtS => WasmOp::I64GtS,
            FuzzOp::I64GtU => WasmOp::I64GtU,
            FuzzOp::I64GeS => WasmOp::I64GeS,
            FuzzOp::I64GeU => WasmOp::I64GeU,
            FuzzOp::I64ExtendI32S => WasmOp::I64ExtendI32S,
            FuzzOp::I64ExtendI32U => WasmOp::I64ExtendI32U,
            FuzzOp::I32WrapI64 => WasmOp::I32WrapI64,
            FuzzOp::I64Extend8S => WasmOp::I64Extend8S,
            FuzzOp::I64Extend16S => WasmOp::I64Extend16S,
            FuzzOp::I64Extend32S => WasmOp::I64Extend32S,
            FuzzOp::LocalGet(idx) => WasmOp::LocalGet((idx as u32) % local_max),
            FuzzOp::LocalSet(idx) => WasmOp::LocalSet((idx as u32) % local_max),
            FuzzOp::LocalTee(idx) => WasmOp::LocalTee((idx as u32) % local_max),
            FuzzOp::Drop => WasmOp::Drop,
            FuzzOp::Nop => WasmOp::Nop,
            FuzzOp::Return => WasmOp::Return,
            FuzzOp::Unreachable => WasmOp::Unreachable,
        }
    }
}

/// Lower a slice of `FuzzOp` into a `Vec<WasmOp>` suitable for the
/// instruction selector. `num_params` is clamped to `[0, 4]` (the AAPCS
/// register-passing limit) so the lowering stays inside the regime the
/// backends actually exercise.
pub fn lower_arbitrary_to_wasm_ops(ops: &[FuzzOp], num_params: u32) -> Vec<WasmOp> {
    let np = num_params.min(4);
    ops.iter().map(|op| op.to_wasm_op(np)).collect()
}
