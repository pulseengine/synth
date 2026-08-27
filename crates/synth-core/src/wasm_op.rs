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
    I32Load {
        offset: u32,
        align: u32,
    },
    I32Store {
        offset: u32,
        align: u32,
    },

    // Sub-word loads (i32)
    I32Load8S {
        offset: u32,
        align: u32,
    }, // byte load, sign-extend to i32
    I32Load8U {
        offset: u32,
        align: u32,
    }, // byte load, zero-extend to i32
    I32Load16S {
        offset: u32,
        align: u32,
    }, // halfword load, sign-extend to i32
    I32Load16U {
        offset: u32,
        align: u32,
    }, // halfword load, zero-extend to i32

    // Sub-word stores (i32)
    I32Store8 {
        offset: u32,
        align: u32,
    }, // store low byte
    I32Store16 {
        offset: u32,
        align: u32,
    }, // store low halfword

    // Control flow
    Block,
    Loop,
    Br(u32),   // Branch to label
    BrIf(u32), // Conditional branch
    BrTable {
        targets: Vec<u32>,
        default: u32,
    },
    Return,
    Call(u32),
    CallIndirect {
        type_index: u32,
        table_index: u32,
    },
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    GlobalGet(u32),
    GlobalSet(u32),

    // Memory management
    MemorySize(u32), // returns current memory size in pages (memory index)
    MemoryGrow(u32), // grow memory by N pages, returns previous size or -1 (memory index)

    // Bulk memory (#374) — single linear memory (memory 0) only; the decoder
    // loud-skips any non-zero memory index. Each pops (dst, src/val, len) = 3
    // i32 operands and pushes nothing.
    MemoryCopy, // memory.copy: copy `len` bytes from `src` to `dst` (memmove semantics)
    MemoryFill, // memory.fill: set `len` bytes at `dst` to the low byte of `val`

    /// VCR-MEM-002 phase 1 (#406): a load/store whose `memarg` targets a
    /// NON-DEFAULT linear memory (`memidx > 0`, multi-memory proposal). The
    /// decoder wraps the plain memory-0 variant instead of DROPPING the index
    /// (the pre-#406 silent aliasing: every memory lowered to the one R11
    /// base, so a store to memory `$b` clobbered memory `$a`). Keeping
    /// memory-0 ops as the bare variants means every existing single-memory
    /// match arm — and therefore every frozen fixture byte — is untouched by
    /// construction; the multi-memory-aware path (the `--relocatable` direct
    /// selector) unwraps this and addresses via the per-memory base symbol
    /// (`__synth_wasm_data_<k>`), and every other path declines LOUDLY
    /// (never a silent alias).
    ///
    /// `memory.size`/`memory.grow` are NOT wrapped — their variants already
    /// carry the memory index. Invariant (decoder-enforced): `memory > 0` and
    /// `op` is never itself a `MultiMemory`.
    MultiMemory {
        memory: u32,
        op: Box<WasmOp>,
    },

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
    I64Load {
        offset: u32,
        align: u32,
    },
    I64Store {
        offset: u32,
        align: u32,
    },

    // Sub-word loads (i64) — load sub-word, extend to i64
    I64Load8S {
        offset: u32,
        align: u32,
    },
    I64Load8U {
        offset: u32,
        align: u32,
    },
    I64Load16S {
        offset: u32,
        align: u32,
    },
    I64Load16U {
        offset: u32,
        align: u32,
    },
    I64Load32S {
        offset: u32,
        align: u32,
    },
    I64Load32U {
        offset: u32,
        align: u32,
    },

    // Sub-word stores (i64) — store low N bits
    I64Store8 {
        offset: u32,
        align: u32,
    },
    I64Store16 {
        offset: u32,
        align: u32,
    },
    I64Store32 {
        offset: u32,
        align: u32,
    },

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
    F32Load {
        offset: u32,
        align: u32,
    },
    F32Store {
        offset: u32,
        align: u32,
    },

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

    // Nontrapping float→int (WASM saturating-float-to-int proposal, 0xFC
    // prefix). TOTAL ops — never trap: NaN → 0, below INT_MIN → INT_MIN,
    // above INT_MAX → INT_MAX, else truncate toward zero (§4.3.2 trunc_sat).
    // Rust emits these for `as` casts, so real modules (falcon, #782) carry
    // them even when the trapping forms are absent.
    I32TruncSatF32S, // Saturating truncate f32 to signed i32
    I32TruncSatF32U, // Saturating truncate f32 to unsigned i32
    I64TruncSatF32S, // Saturating truncate f32 to signed i64
    I64TruncSatF32U, // Saturating truncate f32 to unsigned i64

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
    F64Load {
        offset: u32,
        align: u32,
    },
    F64Store {
        offset: u32,
        align: u32,
    },

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
    // #869: the f32-source i64-target TRAPPING truncations — the only two
    // members of the 64-bit integer<->float conversion family that had no
    // WasmOp variant at all (the rest existed but were dropped at decode).
    I64TruncF32S, // Truncate f32 to signed i64 (traps on NaN/out-of-range)
    I64TruncF32U, // Truncate f32 to unsigned i64 (traps on NaN/out-of-range)

    // Nontrapping f64→int (saturating-float-to-int, §4.3.2 trunc_sat — see
    // the f32 group above for the semantics).
    I32TruncSatF64S, // Saturating truncate f64 to signed i32
    I32TruncSatF64U, // Saturating truncate f64 to unsigned i32
    I64TruncSatF64S, // Saturating truncate f64 to signed i64
    I64TruncSatF64U, // Saturating truncate f64 to unsigned i64

    // ========================================================================
    // v128 SIMD Operations (WASM SIMD proposal)
    // ========================================================================
    // Targets ARM Cortex-M55 Helium MVE (M-Profile Vector Extension)

    // v128 Constants and Memory
    V128Const([u8; 16]), // 128-bit constant
    V128Load {
        offset: u32,
        align: u32,
    }, // v128.load
    V128Store {
        offset: u32,
        align: u32,
    }, // v128.store

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

/// The highest local index the body references, +1 (0 when it touches none).
///
/// #970 (RQ-57-CONDPARAM): this is the param-count bound every backend uses
/// when the driver SUPPLIED a declared count, because `min(referenced,
/// declared)` is EXACT — it names every index that is really a param, and the
/// clamp means a genuine non-param local can never be mistaken for one.
///
/// It replaces the `count_params` access-pattern heuristic on that path, which
/// was UNSOUND: that heuristic counts only indices READ BEFORE WRITTEN in
/// LINEAR op order, so a param written before it is read — but only
/// CONDITIONALLY — was reclassified as a non-param local. Worse, its first
/// access being a WRITE meant the read-before-write zero-init (#457) skipped it
/// too, so the branch that does NOT write it read an UNINITIALISED frame slot:
///
/// ```wat
/// (func (export "f") (param i32 i32) (result i32)
///   (if (local.get 0) (then (local.set 1 (i32.const 5))))
///   (local.get 1))          ;; f(0, 42): wasmtime 42, synth <previous frame>
/// ```
///
/// Measured on cb80e60c under unicorn with the sub-SP stack poisoned, BOTH the
/// ARM and RV32 backends returned the poison word rather than 42 — an
/// information-disclosure shape, not merely a wrong value.
///
/// Using `min(referenced, declared)` rather than plain `declared` PRESERVES the
/// leniency for a function with more declared params than the backend can
/// register-home that only touches the first few: such a body still lowers,
/// exactly as before.
///
/// Shared by the ARM (`synth-backend`), RISC-V (`synth-backend-riscv`) and
/// AArch64 (`synth-backend-aarch64`) backends — three private copies of the
/// same three-line rule is precisely the drift `rewrite_memory_grow_zero`
/// below was centralised to avoid (#242, VCR-SEL-005).
pub fn referenced_locals(wasm_ops: &[WasmOp]) -> u32 {
    wasm_ops
        .iter()
        .filter_map(|op| match op {
            WasmOp::LocalGet(i) | WasmOp::LocalSet(i) | WasmOp::LocalTee(i) => Some(*i + 1),
            _ => None,
        })
        .max()
        .unwrap_or(0)
}

/// The read-before-write param-count HEURISTIC, used only when the driver
/// supplied NO declared count.
///
/// RQ-58-MIRRORS (#242): this existed as THREE byte-equivalent private copies —
/// `synth-backend/src/arm_backend.rs`, `synth-backend-riscv/src/backend.rs` and
/// `synth-backend-aarch64/src/backend.rs` — differing only in local variable
/// names and rustfmt line breaks. #974 collapsed [`referenced_locals`], which
/// REPLACED this heuristic on the declared-count path, but left the heuristic
/// itself triplicated: the fix was centralised and the bug's original carrier
/// was not. Three copies of an UNSOUND rule is worse than three copies of a
/// sound one, because a correction applied to one of them silently does not
/// reach the other two.
///
/// UNSOUND, deliberately kept and deliberately named: it counts only indices
/// READ BEFORE WRITTEN in LINEAR op order, so a conditionally-written param is
/// misclassified — see [`referenced_locals`] for the measured
/// information-disclosure shape (#970). It survives ONLY on the no-declared-
/// count path (direct `compile_function` callers and hand-built op streams),
/// where there is no signature to clamp against. Every caller that HAS a
/// declared count must use `min(referenced_locals(ops), declared)` instead.
pub fn count_params_heuristic(wasm_ops: &[WasmOp]) -> u32 {
    let mut first_access: std::collections::HashMap<u32, bool> = std::collections::HashMap::new();
    for op in wasm_ops {
        match op {
            WasmOp::LocalGet(idx) => {
                first_access.entry(*idx).or_insert(true);
            }
            WasmOp::LocalSet(idx) | WasmOp::LocalTee(idx) => {
                first_access.entry(*idx).or_insert(false);
            }
            _ => {}
        }
    }
    first_access
        .iter()
        .filter_map(|(&idx, &is_read_first)| if is_read_first { Some(idx + 1) } else { None })
        .max()
        .unwrap_or(0)
}

/// Fold `i32.const 0; memory.grow` → `memory.size` up front, on every backend.
///
/// WASM Core §4.4.7: growing a memory by ZERO pages can never fail — it returns
/// the current size. But every backend's `memory.grow` lowering on FIXED
/// (non-growable) linear memory returns the "grow failed" sentinel `-1`, which
/// would wrongly report failure for the legal `memory.grow(0)` "read current
/// size" idiom. Rewriting the const-0 case to the semantically identical
/// `memory.size` BEFORE selection fixes it uniformly. (A runtime-variable page
/// count that happens to be 0 still lowers to `-1` — that is a documented
/// follow-up, not this fold's concern; only the SYNTACTIC `i32.const 0` form is
/// the well-known idiom.)
///
/// Shared by the ARM (`synth-backend`) and RISC-V (`synth-backend-riscv`)
/// backend entry points so the two cannot drift (#242, VCR-SEL-005) — it lives
/// here in `synth-core` next to `WasmOp` because both crates depend on it.
pub fn rewrite_memory_grow_zero(wasm_ops: &[WasmOp]) -> Vec<WasmOp> {
    let mut out = Vec::with_capacity(wasm_ops.len());
    let mut i = 0;
    while i < wasm_ops.len() {
        if matches!(wasm_ops[i], WasmOp::I32Const(0))
            && let Some(WasmOp::MemoryGrow(m)) = wasm_ops.get(i + 1)
        {
            out.push(WasmOp::MemorySize(*m));
            i += 2;
        } else {
            out.push(wasm_ops[i].clone());
            i += 1;
        }
    }
    out
}

/// #1093 — find the first PARAMETER-taking block type in a function's op
/// stream: the k-th `Block`/`Loop`/`If` (ordinal-keyed, matching the decoder's
/// blocktype-arity side-table `FunctionOps::block_arity` /
/// `CompileConfig::current_func_block_arity`) whose `(params, results)` arity
/// has `params != 0`. Returns `(construct, ordinal, arity)` for the decline
/// message; `None` when every block type is parameter-free — including the
/// EMPTY side-table of hand-built op streams, which reads as all-void (the
/// legacy behaviour, so nothing moves for existing callers).
///
/// WHY THIS EXISTS (the aarch64 selector's VCR-A64-CF-001 frame-open refusal,
/// ported — aarch64 was the only backend that already declined this class):
/// the ARM direct selector and the RV32 selector both checkpoint the operand
/// stack at frame ENTRY and reconcile if/else arms and branch edges against
/// that checkpoint. A parameter-taking block type consumes operands that sit
/// BELOW the checkpoint, so (all MEASURED on v0.60.0, #1093):
///  - `if (param ..) .. else ..` PANICS in both selectors — the `Else` arm's
///    `split_off(checkpoint)` walks past the shrunken vstack
///    ("`at` split index (is 2) should be <= len (is 1)", exit 101);
///  - `if (param ..)` WITHOUT an else SILENTLY returns the wrong value on the
///    false path (measured `ipe(0)` → 0, want 7, on all four ARM/RV32 legs —
///    the "implicit else has nothing to reconcile" assumption is false once
///    the frame has params);
///  - a `br_if` into a `block (param ..)` and a back-edge to a
///    `loop (param ..)` header mis-reconcile the join value on RV32
///    (measured wrong values; ARM already declined the loop case via #509).
/// Only the branch-free fall-through shape happens to compile correctly, and
/// telling it apart from the broken shapes would be a NEW predicate with its
/// own proof burden — so, exactly like aarch64, the whole class declines
/// loudly at the first parameter-taking frame.
pub fn find_param_block_type(
    wasm_ops: &[WasmOp],
    block_arity: &[(u8, u8)],
) -> Option<(&'static str, usize, (u8, u8))> {
    if block_arity.iter().all(|&(p, _)| p == 0) {
        return None; // fast path: no parameter-taking type anywhere
    }
    let mut ord = 0usize;
    for op in wasm_ops {
        let what = match op {
            WasmOp::Block => "block",
            WasmOp::Loop => "loop",
            WasmOp::If => "if",
            _ => continue,
        };
        let arity = block_arity.get(ord).copied().unwrap_or((0, 0));
        if arity.0 != 0 {
            return Some((what, ord, arity));
        }
        ord += 1;
    }
    None
}

/// #1093 — the one shared decline message for a parameter-taking block type.
/// ARM and RV32 both call this, so their refusal wording is one definition
/// with nothing to drift (the same sharing rationale as
/// [`rewrite_memory_grow_zero`] above). `backend` names the declining
/// selector; the needle "PARAMETER-taking block type" deliberately matches
/// the aarch64 VCR-A64-CF-001 message so cross-backend decline-parity probes
/// can use one predicate for all three.
pub fn param_block_decline_msg(backend: &str, what: &str, ord: usize, arity: (u8, u8)) -> String {
    format!(
        "{what} #{ord} has type {arity:?} — a PARAMETER-taking block type \
         (multi-value) is not lowered on {backend}: the operand-stack \
         checkpoint at frame entry cannot represent params consumed BELOW it \
         (with an `else` the reconciliation split panics; without one, or on \
         a branch edge, the join value is silently wrong); loud-declining \
         (#1093, the aarch64 VCR-A64-CF-001 refusal ported)"
    )
}

#[cfg(test)]
mod grow_zero_tests {
    use super::*;

    #[test]
    fn folds_const_zero_grow_to_size() {
        assert_eq!(
            rewrite_memory_grow_zero(&[WasmOp::I32Const(0), WasmOp::MemoryGrow(0)]),
            vec![WasmOp::MemorySize(0)]
        );
    }

    #[test]
    fn leaves_nonzero_grow_alone() {
        assert_eq!(
            rewrite_memory_grow_zero(&[WasmOp::I32Const(2), WasmOp::MemoryGrow(0)]),
            vec![WasmOp::I32Const(2), WasmOp::MemoryGrow(0)]
        );
    }

    #[test]
    fn leaves_variable_grow_alone() {
        assert_eq!(
            rewrite_memory_grow_zero(&[WasmOp::LocalGet(0), WasmOp::MemoryGrow(0)]),
            vec![WasmOp::LocalGet(0), WasmOp::MemoryGrow(0)]
        );
    }

    #[test]
    fn preserves_memory_index() {
        assert_eq!(
            rewrite_memory_grow_zero(&[WasmOp::I32Const(0), WasmOp::MemoryGrow(3)]),
            vec![WasmOp::MemorySize(3)]
        );
    }

    // ── #1093: find_param_block_type — the ported VCR-A64-CF-001 predicate ──

    #[test]
    fn param_block_empty_table_is_void() {
        // Hand-built op streams carry no side-table: every block reads as
        // void, the legacy behaviour — the check must never fire.
        let ops = [WasmOp::Block, WasmOp::If, WasmOp::End, WasmOp::End];
        assert_eq!(find_param_block_type(&ops, &[]), None);
    }

    #[test]
    fn param_block_all_void_is_none() {
        let ops = [WasmOp::Block, WasmOp::Loop, WasmOp::End, WasmOp::End];
        assert_eq!(find_param_block_type(&ops, &[(0, 1), (0, 0)]), None);
    }

    #[test]
    fn param_block_reports_construct_and_ordinal() {
        // The #1093 repro shape: one `if` with type (2, 1).
        let ops = [
            WasmOp::I32Const(1),
            WasmOp::I32Const(2),
            WasmOp::LocalGet(0),
            WasmOp::If,
            WasmOp::I32Add,
            WasmOp::Else,
            WasmOp::I32Sub,
            WasmOp::End,
        ];
        assert_eq!(
            find_param_block_type(&ops, &[(2, 1)]),
            Some(("if", 0, (2, 1)))
        );
    }

    #[test]
    fn param_block_ordinal_keying_matches_decoder_order() {
        // Ordinals count Block/Loop/If in op-stream order (the decoder's
        // side-table contract) — the offender here is the SECOND construct.
        let ops = [
            WasmOp::Block, // ord 0, void
            WasmOp::Loop,  // ord 1, (1, 1) — parameter-taking
            WasmOp::End,
            WasmOp::End,
        ];
        assert_eq!(
            find_param_block_type(&ops, &[(0, 0), (1, 1)]),
            Some(("loop", 1, (1, 1)))
        );
    }

    #[test]
    fn param_block_msg_carries_the_parity_needle() {
        // Cross-backend decline-parity probes match on this exact needle,
        // shared with the aarch64 VCR-A64-CF-001 message.
        let msg = param_block_decline_msg("the ARM direct selector", "if", 0, (2, 1));
        assert!(msg.contains("PARAMETER-taking block type"));
        assert!(msg.contains("if #0 has type (2, 1)"));
        assert!(msg.contains("#1093"));
    }
}
