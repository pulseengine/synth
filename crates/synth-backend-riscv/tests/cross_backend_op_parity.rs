//! VCR-SEL-005 — cross-backend op-parity oracle (North Star, epic #242).
//!
//! WHY THIS EXISTS. The "selector missed an op" bug class (#223 Select +
//! non-param locals + sign-extend; #232) was never a *silent* miscompile —
//! both selectors fail honestly on an op they don't lower (the ARM
//! `select_with_stack` selector is an exhaustive `match` over `WasmOp`; RISC-V
//! `selector.rs` ends op-dispatch with `other => Err(SelectorError::Unsupported)`).
//! The actual defect was **cross-backend divergence**: ARM lowered an op that
//! RV32 loud-declined, so a function compiled on Cortex-M but was skipped on
//! RISC-V — and nothing caught that until gale ran it on qemu. The VCR-SEL-001
//! measurement (2026-06-20) confirmed silent-drop is structurally closed on both
//! backends, which re-pointed the verified-selector value at exactly this: an
//! op-PARITY gate.
//!
//! WHAT IT ASSERTS. Every `WasmOp` variant is assigned a [`ParityClass`] by a
//! no-wildcard `match` (see [`classify`]). The `classify` match is
//! COMPILER-ENFORCED complete: a new `WasmOp` variant fails to compile until
//! someone classifies it — you cannot add an op that silently escapes
//! classification (the #615 "expand-or-loud-reject, no-wildcard tripwire"
//! discipline). The op-list fed through it (`all_wasm_op_representatives`) is
//! hand-maintained (WasmOp's `Vec`/`Box`/`f32` fields rule out a derive-based
//! iterator), but a new variant's compile error lands in `classify` and points
//! the author to add both the arm and its representative — see that function's
//! note. Two classes:
//!   * [`ParityClass::IntegerCore`] — the integer op core where the #223/#232
//!     gaps lived. Each carries a self-contained, minimally-valid probe
//!     sequence; both backends are lowered against it and the result must be at
//!     PARITY (both Ok, both Err, OR a ledgered one-sided divergence with a
//!     written reason). This is the ASSERTED core.
//!   * [`ParityClass::StructurallyExcluded`] — an op the selector-level probe
//!     cannot faithfully classify against a fixed target (float/f64 lower on ARM
//!     ONLY when an FPU precision is configured — `arm_single`/`arm_double` — so
//!     "ARM lowers float" is target-parameterized, not an unconditional fact;
//!     SIMD needs Helium/MVE; a few ops need module context the selector-only
//!     probe does not supply). These are NOT asserted here; each carries a
//!     reason and a pointer to where its parity IS tracked. Excluding rather
//!     than asserting a verdict we cannot stand behind is the honest choice —
//!     and it is still universe-complete, because a new variant must be
//!     explicitly placed in one class or the other.
//!
//! The gate fails in BOTH directions on the asserted core:
//!   * a divergence NOT in the ledger  → a new #223-class op-gap, surfaced as a
//!     gate here instead of by gale on silicon;
//!   * a ledgered divergence that has CLOSED → stale entry, delete it (keeps the
//!     ledger honest — a parity claim must not outlive the gap it documents).
//!
//! TARGET NOTE. The ARM probe pins a no-FPU Cortex-M4 target
//! (`thumbv7em-none-eabi`, `fpu = None`); integer lowering is FPU-independent
//! (verified empirically 2026-07-17: the integer core lowers identically with
//! and without an FPU precision configured), so the classification is
//! deterministic. Float/SIMD are `StructurallyExcluded` precisely BECAUSE their
//! ARM lowering IS target-dependent (measured: `f32.add` declines with
//! `fpu=None`, lowers with `Single`/`Double`; `f64.add` needs `Double`).
//!
//! ASYMMETRY NOTE (measured 2026-06-24): i64.rotl / i64.rotr lower on RV32
//! (sequence-composed in the i64 path) while i32.rotl / i32.rotr are ledgered as
//! RV32 declines (Zbb absent). That the i64 rotate already sequence-lowers on
//! RV32 is evidence the i32 Zbb deferral is closable by routing i32 rotate
//! through the same shift+or sequence — the concrete next VCR-SEL-005 codegen
//! step (byte-changing, gated; not asserted here).

use synth_backend_riscv::selector::select as riscv_select;
use synth_synthesis::{BoundsCheckConfig, InstructionSelector, RuleDatabase, WasmOp, WasmOp::*};

/// Does the ARM (Thumb-2) stack-tracking selector lower this sequence?
///
/// Construction mirrors the real call site (`arm_backend.rs`): standard rule DB,
/// no inline bounds guard, no-FPU Cortex-M4 target (integer lowering is
/// FPU-independent; pinning the target keeps the classification deterministic).
fn arm_lowers(ops: &[WasmOp], num_params: u32) -> bool {
    let db = RuleDatabase::with_standard_rules();
    let mut sel =
        InstructionSelector::with_bounds_check(db.rules().to_vec(), BoundsCheckConfig::None);
    sel.set_target(None, "thumbv7em-none-eabi");
    sel.select_with_stack(ops, num_params).is_ok()
}

/// Does the RISC-V (RV32IMAC) selector lower this sequence?
fn riscv_lowers(ops: &[WasmOp], num_params: u32) -> bool {
    riscv_select(ops, num_params).is_ok()
}

/// The parity class of a `WasmOp` — assigned by the no-wildcard [`classify`]
/// match so the WASM-op universe is compiler-enforced complete.
enum ParityClass {
    /// An integer-core op whose ARM/RV32 lowering is FPU-independent and probe-
    /// able from a self-contained sequence. `label` names it for the ledger;
    /// `num_params` + `ops` is the minimally-valid probe. ASSERTED at parity.
    IntegerCore {
        label: &'static str,
        num_params: u32,
        ops: Vec<WasmOp>,
    },
    /// An op the selector-only probe cannot faithfully classify against a fixed
    /// target. NOT asserted; the `&'static str` reason says why and points at
    /// where its parity is tracked (retained for documentation / future audit).
    StructurallyExcluded(#[allow(dead_code)] &'static str),
}

/// Assign EVERY `WasmOp` variant a [`ParityClass`]. NO wildcard arm: a new
/// variant added to `WasmOp` fails to compile here until it is classified —
/// that is the universe-completeness guarantee (the #615 no-wildcard tripwire).
fn classify(op: &WasmOp) -> ParityClass {
    use ParityClass::StructurallyExcluded;
    // A tiny helper: an IntegerCore probe.
    fn core(label: &'static str, num_params: u32, ops: Vec<WasmOp>) -> ParityClass {
        ParityClass::IntegerCore {
            label,
            num_params,
            ops,
        }
    }
    // Float/SIMD are excluded for a shared, documented reason.
    const FLOAT: &str = "float lowering is target-parameterized on ARM (declines with fpu=None, \
         lowers with FPUPrecision::Single/Double) — RV32 has no VFP; parity is \
         tracked as a separate large gap, NOT asserted by this integer oracle";
    const SIMD: &str = "v128/SIMD lowering needs ARM Helium/MVE (Cortex-M55) with no RV32IMAC \
         analogue; separate SIMD-parity gap, NOT asserted here";

    match op {
        // ─── i32 arithmetic / bitwise ────────────────────────────────────
        I32Add => core("i32.add", 0, vec![I32Const(3), I32Const(5), I32Add]),
        I32Sub => core("i32.sub", 0, vec![I32Const(9), I32Const(4), I32Sub]),
        I32Mul => core("i32.mul", 0, vec![I32Const(3), I32Const(5), I32Mul]),
        I32DivS => core("i32.div_s", 0, vec![I32Const(-9), I32Const(2), I32DivS]),
        I32DivU => core("i32.div_u", 0, vec![I32Const(9), I32Const(2), I32DivU]),
        I32RemS => core("i32.rem_s", 0, vec![I32Const(-9), I32Const(2), I32RemS]),
        I32RemU => core("i32.rem_u", 0, vec![I32Const(9), I32Const(2), I32RemU]),
        I32And => core("i32.and", 0, vec![I32Const(6), I32Const(3), I32And]),
        I32Or => core("i32.or", 0, vec![I32Const(6), I32Const(3), I32Or]),
        I32Xor => core("i32.xor", 0, vec![I32Const(6), I32Const(3), I32Xor]),
        I32Shl => core("i32.shl", 0, vec![I32Const(1), I32Const(4), I32Shl]),
        I32ShrS => core("i32.shr_s", 0, vec![I32Const(-16), I32Const(2), I32ShrS]),
        I32ShrU => core("i32.shr_u", 0, vec![I32Const(16), I32Const(2), I32ShrU]),
        I32Rotl => core("i32.rotl", 0, vec![I32Const(1), I32Const(3), I32Rotl]),
        I32Rotr => core("i32.rotr", 0, vec![I32Const(1), I32Const(3), I32Rotr]),
        I32Clz => core("i32.clz", 0, vec![I32Const(1), I32Clz]),
        I32Ctz => core("i32.ctz", 0, vec![I32Const(8), I32Ctz]),
        I32Popcnt => core("i32.popcnt", 0, vec![I32Const(7), I32Popcnt]),
        I32Extend8S => core("i32.extend8_s", 0, vec![I32Const(200), I32Extend8S]),
        I32Extend16S => core("i32.extend16_s", 0, vec![I32Const(40000), I32Extend16S]),
        // ─── i32 comparison ──────────────────────────────────────────────
        I32Eqz => core("i32.eqz", 0, vec![I32Const(0), I32Eqz]),
        I32Eq => core("i32.eq", 0, vec![I32Const(3), I32Const(3), I32Eq]),
        I32Ne => core("i32.ne", 0, vec![I32Const(3), I32Const(4), I32Ne]),
        I32LtS => core("i32.lt_s", 0, vec![I32Const(-1), I32Const(1), I32LtS]),
        I32LtU => core("i32.lt_u", 0, vec![I32Const(1), I32Const(2), I32LtU]),
        I32LeS => core("i32.le_s", 0, vec![I32Const(-1), I32Const(1), I32LeS]),
        I32LeU => core("i32.le_u", 0, vec![I32Const(1), I32Const(2), I32LeU]),
        I32GtS => core("i32.gt_s", 0, vec![I32Const(2), I32Const(1), I32GtS]),
        I32GtU => core("i32.gt_u", 0, vec![I32Const(2), I32Const(1), I32GtU]),
        I32GeS => core("i32.ge_s", 0, vec![I32Const(2), I32Const(1), I32GeS]),
        I32GeU => core("i32.ge_u", 0, vec![I32Const(2), I32Const(2), I32GeU]),
        // ─── i32 const / memory ──────────────────────────────────────────
        I32Const(_) => core("i32.const", 0, vec![I32Const(1)]),
        I32Load { .. } => core(
            "i32.load",
            0,
            vec![
                I32Const(0),
                I32Load {
                    offset: 0,
                    align: 2,
                },
            ],
        ),
        I32Store { .. } => core(
            "i32.store",
            0,
            vec![
                I32Const(0),
                I32Const(42),
                I32Store {
                    offset: 0,
                    align: 2,
                },
            ],
        ),
        I32Load8S { .. } => core(
            "i32.load8_s",
            0,
            vec![
                I32Const(0),
                I32Load8S {
                    offset: 0,
                    align: 0,
                },
            ],
        ),
        I32Load8U { .. } => core(
            "i32.load8_u",
            0,
            vec![
                I32Const(0),
                I32Load8U {
                    offset: 0,
                    align: 0,
                },
            ],
        ),
        I32Load16S { .. } => core(
            "i32.load16_s",
            0,
            vec![
                I32Const(0),
                I32Load16S {
                    offset: 0,
                    align: 1,
                },
            ],
        ),
        I32Load16U { .. } => core(
            "i32.load16_u",
            0,
            vec![
                I32Const(0),
                I32Load16U {
                    offset: 0,
                    align: 1,
                },
            ],
        ),
        I32Store8 { .. } => core(
            "i32.store8",
            0,
            vec![
                I32Const(0),
                I32Const(42),
                I32Store8 {
                    offset: 0,
                    align: 0,
                },
            ],
        ),
        I32Store16 { .. } => core(
            "i32.store16",
            0,
            vec![
                I32Const(0),
                I32Const(42),
                I32Store16 {
                    offset: 0,
                    align: 1,
                },
            ],
        ),
        // ─── Control flow (structured; self-contained) ───────────────────
        Block => core("block", 0, vec![Block, End]),
        Loop => core("loop", 0, vec![Loop, End]),
        Br(_) => core("br", 0, vec![Block, Br(0), End]),
        BrIf(_) => core("br_if", 0, vec![Block, I32Const(1), BrIf(0), End]),
        BrTable { .. } => core(
            "br_table",
            1,
            vec![
                Block,
                Block,
                LocalGet(0),
                BrTable {
                    targets: vec![0],
                    default: 1,
                },
                End,
                End,
            ],
        ),
        Return => core("return", 0, vec![Return]),
        If => core("if", 0, vec![I32Const(1), If, End]),
        Else => core("if_else", 0, vec![I32Const(1), If, Else, End]),
        End => core("end", 0, vec![Block, End]),
        Call(_) => core("call", 0, vec![Call(0)]),
        // ─── Locals ──────────────────────────────────────────────────────
        LocalGet(_) => core("local.get(param)", 1, vec![LocalGet(0)]),
        LocalSet(_) => core(
            "local.set+get(param)",
            1,
            vec![I32Const(42), LocalSet(0), LocalGet(0)],
        ),
        LocalTee(_) => core("local.tee(param)", 1, vec![I32Const(42), LocalTee(0)]),
        // ─── Globals ─────────────────────────────────────────────────────
        GlobalGet(_) => core("global.get", 0, vec![GlobalGet(0)]),
        GlobalSet(_) => core("global.set", 0, vec![I32Const(1), GlobalSet(0)]),
        // ─── Memory management / bulk memory ─────────────────────────────
        MemorySize(_) => core("memory.size", 0, vec![MemorySize(0)]),
        MemoryGrow(_) => core("memory.grow", 0, vec![I32Const(1), MemoryGrow(0)]),
        MemoryCopy => core(
            "memory.copy",
            0,
            vec![I32Const(0), I32Const(0), I32Const(0), MemoryCopy],
        ),
        MemoryFill => core(
            "memory.fill",
            0,
            vec![I32Const(0), I32Const(0), I32Const(0), MemoryFill],
        ),
        // A MultiMemory-wrapped op is a decoder-side wrapper for a non-default
        // linear memory; its parity follows the wrapped op and the multi-memory
        // decline discipline (#406), which is a separate lane. Exclude the
        // wrapper itself from the integer probe (constructing a valid multi-mem
        // module is module-level, not a self-contained op sequence).
        MultiMemory { .. } => StructurallyExcluded(
            "multi-memory wrapper (#406) — parity follows the wrapped op + the \
             multi-memory decline discipline; module-level, not a self-contained \
             op-sequence probe",
        ),
        // ─── Stack manipulation / misc ───────────────────────────────────
        Drop => core("drop", 0, vec![I32Const(1), Drop]),
        Select => core(
            "select",
            0,
            vec![I32Const(10), I32Const(20), I32Const(1), Select],
        ),
        Unreachable => core("unreachable", 0, vec![Unreachable]),
        Nop => core("nop", 0, vec![Nop]),
        // ─── Indirect call (needs a table/type-section; module-level) ────
        CallIndirect { .. } => StructurallyExcluded(
            "call_indirect needs a table + type section (module context); the \
             self-contained dispatch is a separate loud-decline lane (#275)",
        ),

        // ─── i64 arithmetic / bitwise ────────────────────────────────────
        I64Add => core("i64.add", 0, vec![I64Const(3), I64Const(5), I64Add]),
        I64Sub => core("i64.sub", 0, vec![I64Const(9), I64Const(4), I64Sub]),
        I64Mul => core("i64.mul", 0, vec![I64Const(3), I64Const(5), I64Mul]),
        I64DivS => core("i64.div_s", 0, vec![I64Const(-9), I64Const(2), I64DivS]),
        I64DivU => core("i64.div_u", 0, vec![I64Const(9), I64Const(2), I64DivU]),
        I64RemS => core("i64.rem_s", 0, vec![I64Const(-9), I64Const(2), I64RemS]),
        I64RemU => core("i64.rem_u", 0, vec![I64Const(9), I64Const(2), I64RemU]),
        I64And => core("i64.and", 0, vec![I64Const(6), I64Const(3), I64And]),
        I64Or => core("i64.or", 0, vec![I64Const(6), I64Const(3), I64Or]),
        I64Xor => core("i64.xor", 0, vec![I64Const(6), I64Const(3), I64Xor]),
        I64Shl => core("i64.shl", 0, vec![I64Const(1), I64Const(4), I64Shl]),
        I64ShrS => core("i64.shr_s", 0, vec![I64Const(-16), I64Const(2), I64ShrS]),
        I64ShrU => core("i64.shr_u", 0, vec![I64Const(16), I64Const(2), I64ShrU]),
        I64Rotl => core("i64.rotl", 0, vec![I64Const(1), I64Const(3), I64Rotl]),
        I64Rotr => core("i64.rotr", 0, vec![I64Const(1), I64Const(3), I64Rotr]),
        I64Clz => core("i64.clz", 0, vec![I64Const(1), I64Clz]),
        I64Ctz => core("i64.ctz", 0, vec![I64Const(8), I64Ctz]),
        I64Popcnt => core("i64.popcnt", 0, vec![I64Const(7), I64Popcnt]),
        // ─── i64 comparison ──────────────────────────────────────────────
        I64Eqz => core("i64.eqz", 0, vec![I64Const(0), I64Eqz]),
        I64Eq => core("i64.eq", 0, vec![I64Const(3), I64Const(3), I64Eq]),
        I64Ne => core("i64.ne", 0, vec![I64Const(3), I64Const(4), I64Ne]),
        I64LtS => core("i64.lt_s", 0, vec![I64Const(-1), I64Const(1), I64LtS]),
        I64LtU => core("i64.lt_u", 0, vec![I64Const(1), I64Const(2), I64LtU]),
        I64LeS => core("i64.le_s", 0, vec![I64Const(-1), I64Const(1), I64LeS]),
        I64LeU => core("i64.le_u", 0, vec![I64Const(1), I64Const(2), I64LeU]),
        I64GtS => core("i64.gt_s", 0, vec![I64Const(2), I64Const(1), I64GtS]),
        I64GtU => core("i64.gt_u", 0, vec![I64Const(2), I64Const(1), I64GtU]),
        I64GeS => core("i64.ge_s", 0, vec![I64Const(2), I64Const(1), I64GeS]),
        I64GeU => core("i64.ge_u", 0, vec![I64Const(2), I64Const(2), I64GeU]),
        // ─── i64 const / memory ──────────────────────────────────────────
        I64Const(_) => core("i64.const", 0, vec![I64Const(1)]),
        I64Load { .. } => core(
            "i64.load",
            0,
            vec![
                I32Const(0),
                I64Load {
                    offset: 0,
                    align: 3,
                },
            ],
        ),
        I64Store { .. } => core(
            "i64.store",
            0,
            vec![
                I32Const(0),
                I64Const(42),
                I64Store {
                    offset: 0,
                    align: 3,
                },
            ],
        ),
        I64Load8S { .. } => core(
            "i64.load8_s",
            0,
            vec![
                I32Const(0),
                I64Load8S {
                    offset: 0,
                    align: 0,
                },
            ],
        ),
        I64Load8U { .. } => core(
            "i64.load8_u",
            0,
            vec![
                I32Const(0),
                I64Load8U {
                    offset: 0,
                    align: 0,
                },
            ],
        ),
        I64Load16S { .. } => core(
            "i64.load16_s",
            0,
            vec![
                I32Const(0),
                I64Load16S {
                    offset: 0,
                    align: 1,
                },
            ],
        ),
        I64Load16U { .. } => core(
            "i64.load16_u",
            0,
            vec![
                I32Const(0),
                I64Load16U {
                    offset: 0,
                    align: 1,
                },
            ],
        ),
        I64Load32S { .. } => core(
            "i64.load32_s",
            0,
            vec![
                I32Const(0),
                I64Load32S {
                    offset: 0,
                    align: 2,
                },
            ],
        ),
        I64Load32U { .. } => core(
            "i64.load32_u",
            0,
            vec![
                I32Const(0),
                I64Load32U {
                    offset: 0,
                    align: 2,
                },
            ],
        ),
        I64Store8 { .. } => core(
            "i64.store8",
            0,
            vec![
                I32Const(0),
                I64Const(42),
                I64Store8 {
                    offset: 0,
                    align: 0,
                },
            ],
        ),
        I64Store16 { .. } => core(
            "i64.store16",
            0,
            vec![
                I32Const(0),
                I64Const(42),
                I64Store16 {
                    offset: 0,
                    align: 1,
                },
            ],
        ),
        I64Store32 { .. } => core(
            "i64.store32",
            0,
            vec![
                I32Const(0),
                I64Const(42),
                I64Store32 {
                    offset: 0,
                    align: 2,
                },
            ],
        ),
        // ─── i64 <-> i32 width conversions ───────────────────────────────
        I64ExtendI32S => core("i64.extend_i32_s", 0, vec![I32Const(-1), I64ExtendI32S]),
        I64ExtendI32U => core("i64.extend_i32_u", 0, vec![I32Const(-1), I64ExtendI32U]),
        I32WrapI64 => core("i32.wrap_i64", 0, vec![I64Const(0x1_0000_0001), I32WrapI64]),
        // ─── i64 in-place sign extension ─────────────────────────────────
        I64Extend8S => core("i64.extend8_s", 0, vec![I64Const(200), I64Extend8S]),
        I64Extend16S => core("i64.extend16_s", 0, vec![I64Const(40000), I64Extend16S]),
        I64Extend32S => core(
            "i64.extend32_s",
            0,
            vec![I64Const(0x1_0000_0001), I64Extend32S],
        ),

        // ─── f32 (StructurallyExcluded — target-parameterized) ───────────
        F32Add
        | F32Sub
        | F32Mul
        | F32Div
        | F32Eq
        | F32Ne
        | F32Lt
        | F32Le
        | F32Gt
        | F32Ge
        | F32Abs
        | F32Neg
        | F32Ceil
        | F32Floor
        | F32Trunc
        | F32Nearest
        | F32Sqrt
        | F32Min
        | F32Max
        | F32Copysign
        | F32Const(_)
        | F32Load { .. }
        | F32Store { .. }
        | F32ConvertI32S
        | F32ConvertI32U
        | F32ConvertI64S
        | F32ConvertI64U
        | F32DemoteF64
        | F32ReinterpretI32
        | I32ReinterpretF32
        | I32TruncF32S
        | I32TruncF32U
        | I32TruncSatF32S
        | I32TruncSatF32U
        | I64TruncSatF32S
        | I64TruncSatF32U => StructurallyExcluded(FLOAT),
        // ─── f64 (StructurallyExcluded — target-parameterized) ───────────
        F64Add
        | F64Sub
        | F64Mul
        | F64Div
        | F64Eq
        | F64Ne
        | F64Lt
        | F64Le
        | F64Gt
        | F64Ge
        | F64Abs
        | F64Neg
        | F64Ceil
        | F64Floor
        | F64Trunc
        | F64Nearest
        | F64Sqrt
        | F64Min
        | F64Max
        | F64Copysign
        | F64Const(_)
        | F64Load { .. }
        | F64Store { .. }
        | F64ConvertI32S
        | F64ConvertI32U
        | F64ConvertI64S
        | F64ConvertI64U
        | F64PromoteF32
        | F64ReinterpretI64
        | I64ReinterpretF64
        | I64TruncF64S
        | I64TruncF64U
        | I32TruncF64S
        | I32TruncF64U
        | I32TruncSatF64S
        | I32TruncSatF64U
        | I64TruncSatF64S
        | I64TruncSatF64U => StructurallyExcluded(FLOAT),

        // ─── v128 / SIMD (StructurallyExcluded — Helium/MVE, no RV32) ─────
        V128Const(_)
        | V128Load { .. }
        | V128Store { .. }
        | V128And
        | V128Or
        | V128Xor
        | V128Not
        | V128AndNot => StructurallyExcluded(SIMD),
        I8x16Add | I8x16Sub | I8x16Neg | I8x16Eq | I8x16Ne | I8x16LtS | I8x16LtU | I8x16GtS
        | I8x16GtU | I8x16LeS | I8x16LeU | I8x16GeS | I8x16GeU | I8x16Splat
        | I8x16ExtractLaneS(_) | I8x16ExtractLaneU(_) | I8x16ReplaceLane(_) | I8x16Shuffle(_)
        | I8x16Swizzle => StructurallyExcluded(SIMD),
        I16x8Add | I16x8Sub | I16x8Mul | I16x8Neg | I16x8Eq | I16x8Ne | I16x8LtS | I16x8LtU
        | I16x8GtS | I16x8GtU | I16x8LeS | I16x8LeU | I16x8GeS | I16x8GeU | I16x8Splat
        | I16x8ExtractLaneS(_) | I16x8ExtractLaneU(_) | I16x8ReplaceLane(_) => {
            StructurallyExcluded(SIMD)
        }
        I32x4Add | I32x4Sub | I32x4Mul | I32x4Neg | I32x4Eq | I32x4Ne | I32x4LtS | I32x4LtU
        | I32x4GtS | I32x4GtU | I32x4LeS | I32x4LeU | I32x4GeS | I32x4GeU | I32x4Splat
        | I32x4ExtractLane(_) | I32x4ReplaceLane(_) => StructurallyExcluded(SIMD),
        I64x2Add | I64x2Sub | I64x2Mul | I64x2Neg | I64x2Eq | I64x2Ne | I64x2LtS | I64x2GtS
        | I64x2LeS | I64x2GeS | I64x2Splat | I64x2ExtractLane(_) | I64x2ReplaceLane(_) => {
            StructurallyExcluded(SIMD)
        }
        F32x4Add | F32x4Sub | F32x4Mul | F32x4Div | F32x4Abs | F32x4Neg | F32x4Sqrt | F32x4Eq
        | F32x4Ne | F32x4Lt | F32x4Le | F32x4Gt | F32x4Ge | F32x4Splat | F32x4ExtractLane(_)
        | F32x4ReplaceLane(_) => StructurallyExcluded(SIMD),
    }
}

/// The complete universe of `WasmOp` variants, one representative each, fed
/// through the no-wildcard [`classify`].
///
/// HONEST completeness story: the [`classify`] match is COMPILER-ENFORCED
/// complete (no wildcard — a new `WasmOp` variant fails to compile there until
/// classified). This `Vec`, by contrast, is HAND-MAINTAINED: `WasmOp` carries
/// `Vec`/`Box`/`f32` fields so a derive-based `EnumIter` cannot drop in. The two
/// compose safely because a new variant's compile error lands in `classify()`,
/// which points the author HERE to add both the arm and the representative — you
/// cannot add a silently-unclassified op, and the natural fix adds its probe.
///
/// Note the representative values are irrelevant to classification (the match
/// ignores payloads); they exist only so the vector enumerates every variant.
#[rustfmt::skip]
fn all_wasm_op_representatives() -> Vec<WasmOp> {
    vec![
        // i32
        I32Add, I32Sub, I32Mul, I32DivS, I32DivU, I32RemS, I32RemU, I32And, I32Or, I32Xor,
        I32Shl, I32ShrS, I32ShrU, I32Rotl, I32Rotr, I32Clz, I32Ctz, I32Popcnt, I32Extend8S,
        I32Extend16S, I32Eqz, I32Eq, I32Ne, I32LtS, I32LtU, I32LeS, I32LeU, I32GtS, I32GtU,
        I32GeS, I32GeU, I32Const(0),
        I32Load { offset: 0, align: 2 }, I32Store { offset: 0, align: 2 },
        I32Load8S { offset: 0, align: 0 }, I32Load8U { offset: 0, align: 0 },
        I32Load16S { offset: 0, align: 1 }, I32Load16U { offset: 0, align: 1 },
        I32Store8 { offset: 0, align: 0 }, I32Store16 { offset: 0, align: 1 },
        // control flow
        Block, Loop, Br(0), BrIf(0), BrTable { targets: vec![0], default: 0 }, Return,
        Call(0), CallIndirect { type_index: 0, table_index: 0 },
        LocalGet(0), LocalSet(0), LocalTee(0), GlobalGet(0), GlobalSet(0),
        MemorySize(0), MemoryGrow(0), MemoryCopy, MemoryFill,
        MultiMemory { memory: 1, op: Box::new(I32Add) },
        Drop, Select, If, Else, End, Unreachable, Nop,
        // i64
        I64Add, I64Sub, I64Mul, I64DivS, I64DivU, I64RemS, I64RemU, I64And, I64Or, I64Xor,
        I64Shl, I64ShrS, I64ShrU, I64Rotl, I64Rotr, I64Clz, I64Ctz, I64Popcnt, I64Eqz,
        I64Eq, I64Ne, I64LtS, I64LtU, I64LeS, I64LeU, I64GtS, I64GtU, I64GeS, I64GeU,
        I64Const(0),
        I64Load { offset: 0, align: 3 }, I64Store { offset: 0, align: 3 },
        I64Load8S { offset: 0, align: 0 }, I64Load8U { offset: 0, align: 0 },
        I64Load16S { offset: 0, align: 1 }, I64Load16U { offset: 0, align: 1 },
        I64Load32S { offset: 0, align: 2 }, I64Load32U { offset: 0, align: 2 },
        I64Store8 { offset: 0, align: 0 }, I64Store16 { offset: 0, align: 1 },
        I64Store32 { offset: 0, align: 2 },
        I64ExtendI32S, I64ExtendI32U, I32WrapI64, I64Extend8S, I64Extend16S, I64Extend32S,
        // f32
        F32Add, F32Sub, F32Mul, F32Div, F32Eq, F32Ne, F32Lt, F32Le, F32Gt, F32Ge, F32Abs,
        F32Neg, F32Ceil, F32Floor, F32Trunc, F32Nearest, F32Sqrt, F32Min, F32Max,
        F32Copysign, F32Const(0.0),
        F32Load { offset: 0, align: 2 }, F32Store { offset: 0, align: 2 },
        F32ConvertI32S, F32ConvertI32U, F32ConvertI64S, F32ConvertI64U, F32DemoteF64,
        F32ReinterpretI32, I32ReinterpretF32, I32TruncF32S, I32TruncF32U, I32TruncSatF32S,
        I32TruncSatF32U, I64TruncSatF32S, I64TruncSatF32U,
        // f64
        F64Add, F64Sub, F64Mul, F64Div, F64Eq, F64Ne, F64Lt, F64Le, F64Gt, F64Ge, F64Abs,
        F64Neg, F64Ceil, F64Floor, F64Trunc, F64Nearest, F64Sqrt, F64Min, F64Max,
        F64Copysign, F64Const(0.0),
        F64Load { offset: 0, align: 3 }, F64Store { offset: 0, align: 3 },
        F64ConvertI32S, F64ConvertI32U, F64ConvertI64S, F64ConvertI64U, F64PromoteF32,
        F64ReinterpretI64, I64ReinterpretF64, I64TruncF64S, I64TruncF64U, I32TruncF64S,
        I32TruncF64U, I32TruncSatF64S, I32TruncSatF64U, I64TruncSatF64S, I64TruncSatF64U,
        // v128 / SIMD
        V128Const([0; 16]), V128Load { offset: 0, align: 4 }, V128Store { offset: 0, align: 4 },
        V128And, V128Or, V128Xor, V128Not, V128AndNot,
        I8x16Add, I8x16Sub, I8x16Neg, I8x16Eq, I8x16Ne, I8x16LtS, I8x16LtU, I8x16GtS,
        I8x16GtU, I8x16LeS, I8x16LeU, I8x16GeS, I8x16GeU, I8x16Splat, I8x16ExtractLaneS(0),
        I8x16ExtractLaneU(0), I8x16ReplaceLane(0), I8x16Shuffle([0; 16]), I8x16Swizzle,
        I16x8Add, I16x8Sub, I16x8Mul, I16x8Neg, I16x8Eq, I16x8Ne, I16x8LtS, I16x8LtU,
        I16x8GtS, I16x8GtU, I16x8LeS, I16x8LeU, I16x8GeS, I16x8GeU, I16x8Splat,
        I16x8ExtractLaneS(0), I16x8ExtractLaneU(0), I16x8ReplaceLane(0),
        I32x4Add, I32x4Sub, I32x4Mul, I32x4Neg, I32x4Eq, I32x4Ne, I32x4LtS, I32x4LtU,
        I32x4GtS, I32x4GtU, I32x4LeS, I32x4LeU, I32x4GeS, I32x4GeU, I32x4Splat,
        I32x4ExtractLane(0), I32x4ReplaceLane(0),
        I64x2Add, I64x2Sub, I64x2Mul, I64x2Neg, I64x2Eq, I64x2Ne, I64x2LtS, I64x2GtS,
        I64x2LeS, I64x2GeS, I64x2Splat, I64x2ExtractLane(0), I64x2ReplaceLane(0),
        F32x4Add, F32x4Sub, F32x4Mul, F32x4Div, F32x4Abs, F32x4Neg, F32x4Sqrt, F32x4Eq,
        F32x4Ne, F32x4Lt, F32x4Le, F32x4Gt, F32x4Ge, F32x4Splat, F32x4ExtractLane(0),
        F32x4ReplaceLane(0),
    ]
}

/// Ledger of KNOWN ARM-vs-RISC-V parity differences among the INTEGER-CORE ops.
/// Key = the `IntegerCore::label`; value = WHY the two backends disagree today.
/// Two legitimate entry kinds — both must carry a concrete reason, never a
/// hand-wave:
///   * PERMANENT ISA divergence — one ISA structurally cannot express the op in
///     this target slice. (None among integer-core ops today.)
///   * TRACKED DEFERRAL — a #223-class op-gap that is named, reasoned, and
///     pointed at a tracking requirement. The ledger entry IS the "file it": it
///     makes the gap a gated, owned fact instead of a silicon surprise. When the
///     RV32 lowering lands, the stale-entry check FAILS until this line is
///     deleted — so a deferral cannot quietly outlive its fix.
///
/// MEASURED 2026-06-20: the RV32 selector loud-declines five integer bit-
/// manipulation ops the ARM selector lowers — the Zbb class (rotate / clz / ctz
/// / popcount). RV32IMAC/rv32imc do NOT include Zbb, so no single native
/// instruction; ARM lowers them via sequences (ROR/CLZ/RBIT + software popcount).
///
/// MEASURED 2026-07-17 (universe-completeness upgrade #242): making the probe
/// enumerate the FULL `WasmOp` universe (not a curated integer list) surfaced
/// SIXTEEN more integer-core one-sided gaps the old curated set never probed —
/// ARM lowers, RV32 loud-declines (`unsupported wasm op for RV32 skeleton: …`),
/// confirmed end-to-end via `synth compile -b riscv`. These are exactly the
/// #223 silent-cross-backend-divergence class the oracle exists to surface:
/// globals (get/set), memory management (size/grow), bulk memory (copy/fill),
/// br_table, and the nine sub-word i64 loads/stores (load8/16/32_s/u,
/// store8/16/32 — the full-word i64.load/i64.store DO lower on both; only the
/// sub-word extend/truncate variants are the gap). Each is a TRACKED
/// RV32-selector DEFERRAL under VCR-SEL-005, not a permanent ISA limit. Ledger
/// total: 5 Zbb + 16 new = 21 entries.
fn known_divergences() -> &'static [(&'static str, &'static str)] {
    &[
        // ---- Zbb bit-manipulation class (measured 2026-06-20) ----
        (
            "i32.rotl",
            "Zbb rol absent on RV32IMAC/rv32imc; RV32 seq-lowering deferred — VCR-SEL-005",
        ),
        (
            "i32.rotr",
            "Zbb ror absent on RV32IMAC/rv32imc; RV32 seq-lowering deferred — VCR-SEL-005",
        ),
        (
            "i32.clz",
            "Zbb clz absent on RV32IMAC/rv32imc; RV32 seq-lowering deferred — VCR-SEL-005",
        ),
        (
            "i32.ctz",
            "Zbb ctz absent on RV32IMAC/rv32imc; RV32 seq-lowering deferred — VCR-SEL-005",
        ),
        (
            "i32.popcnt",
            "Zbb cpop absent on RV32IMAC/rv32imc; RV32 seq-lowering deferred — VCR-SEL-005",
        ),
        // ---- globals (measured 2026-07-17, universe-completeness) ----
        (
            "global.get",
            "RV32 selector has no GlobalGet arm (loud Unsupported); WASM globals \
             not yet lowered on RV32 — deferred, VCR-SEL-005",
        ),
        (
            "global.set",
            "RV32 selector has no GlobalSet arm (loud Unsupported); WASM globals \
             not yet lowered on RV32 — deferred, VCR-SEL-005",
        ),
        // ---- memory management / bulk memory (measured 2026-07-17) ----
        (
            "memory.size",
            "RV32 selector has no MemorySize arm (loud Unsupported); RV32 memory \
             intrinsics not yet lowered — deferred, VCR-SEL-005",
        ),
        (
            "memory.grow",
            "RV32 selector has no MemoryGrow arm (loud Unsupported); RV32 memory \
             intrinsics not yet lowered — deferred, VCR-SEL-005",
        ),
        (
            "memory.copy",
            "RV32 selector has no MemoryCopy arm (loud Unsupported); RV32 bulk-memory \
             (#374) not yet lowered — deferred, VCR-SEL-005",
        ),
        (
            "memory.fill",
            "RV32 selector has no MemoryFill arm (loud Unsupported); RV32 bulk-memory \
             (#374) not yet lowered — deferred, VCR-SEL-005",
        ),
        // ---- structured control-flow multi-target branch (measured 2026-07-17) ----
        (
            "br_table",
            "RV32 selector has no BrTable arm (loud Unsupported); the jump-table \
             dispatch is not yet lowered on RV32 — deferred, VCR-SEL-005",
        ),
        // ---- sub-word i64 memory (measured 2026-07-17; the full-word i64.load /
        //      i64.store DO lower on both — only the sub-word extend/truncate
        //      variants are the gap) ----
        (
            "i64.load8_s",
            "RV32 selector has no I64Load8S arm (loud Unsupported); sub-word→i64 \
             load-extend not yet lowered on RV32 — deferred, VCR-SEL-005",
        ),
        (
            "i64.load8_u",
            "RV32 selector has no I64Load8U arm (loud Unsupported); sub-word→i64 \
             load-extend not yet lowered on RV32 — deferred, VCR-SEL-005",
        ),
        (
            "i64.load16_s",
            "RV32 selector has no I64Load16S arm (loud Unsupported); sub-word→i64 \
             load-extend not yet lowered on RV32 — deferred, VCR-SEL-005",
        ),
        (
            "i64.load16_u",
            "RV32 selector has no I64Load16U arm (loud Unsupported); sub-word→i64 \
             load-extend not yet lowered on RV32 — deferred, VCR-SEL-005",
        ),
        (
            "i64.load32_s",
            "RV32 selector has no I64Load32S arm (loud Unsupported); sub-word→i64 \
             load-extend not yet lowered on RV32 — deferred, VCR-SEL-005",
        ),
        (
            "i64.load32_u",
            "RV32 selector has no I64Load32U arm (loud Unsupported); sub-word→i64 \
             load-extend not yet lowered on RV32 — deferred, VCR-SEL-005",
        ),
        (
            "i64.store8",
            "RV32 selector has no I64Store8 arm (loud Unsupported); i64 sub-word \
             store not yet lowered on RV32 — deferred, VCR-SEL-005",
        ),
        (
            "i64.store16",
            "RV32 selector has no I64Store16 arm (loud Unsupported); i64 sub-word \
             store not yet lowered on RV32 — deferred, VCR-SEL-005",
        ),
        (
            "i64.store32",
            "RV32 selector has no I64Store32 arm (loud Unsupported); i64 sub-word \
             store not yet lowered on RV32 — deferred, VCR-SEL-005",
        ),
    ]
}

/// The classification core, factored out so the red-first companion test can
/// drive it with a mutated ledger. Returns (at_parity_count, unexpected, stale).
///
/// `ledger` maps `IntegerCore::label` → reason. An IntegerCore op is:
///   * at parity (both lower or both decline) and NOT ledgered → counted;
///   * at parity but ledgered → STALE (delete the entry);
///   * divergent and ledgered → OK (a known, explained gap);
///   * divergent and NOT ledgered → UNEXPECTED (the #223 class).
fn run_parity(ledger: &std::collections::HashMap<&str, &str>) -> (usize, Vec<String>, Vec<String>) {
    let mut unexpected: Vec<String> = Vec::new();
    let mut stale: Vec<String> = Vec::new();
    let mut at_parity = 0usize;

    for op in all_wasm_op_representatives() {
        let (label, num_params, ops) = match classify(&op) {
            ParityClass::IntegerCore {
                label,
                num_params,
                ops,
            } => (label, num_params, ops),
            // Not asserted — universe-complete by classification, not by probe.
            ParityClass::StructurallyExcluded(_) => continue,
        };

        let a = arm_lowers(&ops, num_params);
        let r = riscv_lowers(&ops, num_params);
        let ledgered = ledger.get(label);

        match (a == r, ledgered) {
            (true, None) => at_parity += 1,
            (true, Some(_reason)) => stale.push(format!(
                "  {label} — ledgered as a divergence but BOTH backends now agree \
                 (arm_ok={a}, riscv_ok={r}); delete the known-divergence entry"
            )),
            (false, Some(_reason)) => { /* known, explained divergence — OK */ }
            (false, None) => unexpected.push(format!(
                "  {label} — arm_lowers={a}, riscv_lowers={r} (cross-backend op-gap; \
                 the #223 class). Either implement the missing lowering, or add a \
                 known-divergence entry with a reason."
            )),
        }
    }
    (at_parity, unexpected, stale)
}

#[test]
fn cross_backend_integer_op_parity_242() {
    let ledger: std::collections::HashMap<&str, &str> =
        known_divergences().iter().copied().collect();

    let (at_parity, unexpected, stale) = run_parity(&ledger);

    // Floor: the universe-complete probe must actually be exercising both
    // backends across the integer core, so a construction regression (e.g. every
    // case erroring on a stack-underflow artifact) can't masquerade as parity.
    assert!(
        at_parity >= 65,
        "parity oracle exercised too few common-core ops ({at_parity}); the \
         classifier or the selector construction regressed"
    );

    assert!(
        unexpected.is_empty() && stale.is_empty(),
        "cross-backend op-parity ledger is out of date:\n\
         NEW UNEXPLAINED DIVERGENCES (the #223 op-gap class):\n{}\n\
         STALE LEDGER ENTRIES (close them):\n{}",
        if unexpected.is_empty() {
            "  (none)".into()
        } else {
            unexpected.join("\n")
        },
        if stale.is_empty() {
            "  (none)".into()
        } else {
            stale.join("\n")
        },
    );
}

/// RED-FIRST non-vacuity proof. Remove a KNOWN, REAL one-sided gap (`i32.rotl`,
/// which ARM lowers and RV32 loud-declines) from the ledger and assert the gate
/// FAILS — i.e. reports `i32.rotl` as an unexpected divergence. This proves the
/// gate genuinely detects a one-sided op-gap on the REAL backends (not a
/// synthetic op, and touching no shipping code): with the correct ledger the
/// main test is green; drop one load-bearing entry and it goes red.
#[test]
fn red_first_unledgered_one_sided_gap_is_caught() {
    // The real ledger MINUS i32.rotl.
    let ledger: std::collections::HashMap<&str, &str> = known_divergences()
        .iter()
        .copied()
        .filter(|(label, _)| *label != "i32.rotl")
        .collect();

    let (_at_parity, unexpected, _stale) = run_parity(&ledger);

    assert!(
        unexpected.iter().any(|line| line.contains("i32.rotl")),
        "RED-FIRST vacuity check FAILED: dropping the i32.rotl ledger entry did \
         NOT surface it as an unexpected cross-backend divergence — the parity \
         gate is not actually detecting the real ARM-lowers/RV32-declines gap. \
         unexpected = {unexpected:?}"
    );
}

/// Every ledgered divergence must name a REAL integer-core op (a live
/// `IntegerCore` label), so the ledger cannot drift to reference an op that no
/// longer exists or was reclassified as StructurallyExcluded.
#[test]
fn ledger_labels_are_live_integer_core_ops() {
    let live: std::collections::HashSet<&str> = all_wasm_op_representatives()
        .iter()
        .filter_map(|op| match classify(op) {
            ParityClass::IntegerCore { label, .. } => Some(label),
            ParityClass::StructurallyExcluded(_) => None,
        })
        .collect();

    let dangling: Vec<&str> = known_divergences()
        .iter()
        .map(|(label, _)| *label)
        .filter(|label| !live.contains(label))
        .collect();

    assert!(
        dangling.is_empty(),
        "known-divergence ledger references labels that are not live \
         IntegerCore ops (typo, removed op, or reclassified): {dangling:?}"
    );
}
