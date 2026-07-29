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

/// Does the AArch64 (A64 host-native) selector lower this sequence? (#851 —
/// the THIRD backend in the VCR-SEL-005 enumeration.)
///
/// Construction mirrors the real call site (`synth-backend-aarch64/backend.rs`):
/// no imports, a single void 0-arg local function `func_0` as call metadata (so
/// the `call` probe resolves), and the SHIPPING default bounds mode
/// (`MemBounds::Software` with a 1-page limit — the `--safety-bounds software`
/// CLI default). Unlike ARM, the aarch64 float lowering is NOT
/// target-parameterized (one fixed host profile), so the float surface is
/// probe-able here too — see [`a64_extended_surface`].
fn aarch64_lowers(ops: &[WasmOp], num_params: u32) -> bool {
    synth_backend_aarch64::selector::select_typed_cf_calls(
        ops,
        num_params,
        &[],
        &[],
        &[],
        0,
        &[0],
        &[0],
        &[false],
        synth_backend_aarch64::selector::MemBounds::Software { limit_bytes: 65536 },
    )
    .is_ok()
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
        | I64TruncSatF32U
        // #869: the f32-source i64-target TRAPPING truncations (ARM32 m7dp
        // lowers them via the i64 domain guard + #782 decompose; RV32 has no
        // floats — target-parameterized like the rest of the float surface).
        | I64TruncF32S
        | I64TruncF32U => StructurallyExcluded(FLOAT),
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
        I32TruncSatF32U, I64TruncSatF32S, I64TruncSatF32U, I64TruncF32S, I64TruncF32U,
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
/// RV32-selector DEFERRAL under VCR-SEL-005, not a permanent ISA limit.
///
/// CLOSED v0.50 (#242): `memory.size` + `memory.grow` now lower on RV32
/// (fixed-memory page-count constant + fixed-memory `-1` grow, shared
/// `rewrite_memory_grow_zero` fold; execution differential
/// `rv32_mem_size_grow_242_differential.py`). Ledger total: 5 Zbb + 16 −
/// 2 closed = 19 entries.
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
        // ---- globals (measured 2026-07-17; root-caused v0.50) ----
        // NOT a missing selector arm — a missing SUBSTRATE. ARM addresses
        // globals via a `__synth_globals` symbol + data reloc (R9-relative or
        // emit_sym_addr); the RV32 encoder has NO data-symbol reloc path (Call
        // is local-label-only, no %hi/%lo/%pcrel), and RV32 emits ET_REL only,
        // so an absolute-constant address is unsound (the linker places the
        // region). The reloc-free path — a linker-reserved region past linear
        // memory, addressed `s11 + linear_memory_bytes + slot_off` — is sound
        // and reuses the memory.size plumbing, BUT a HONEST landing needs the
        // full #798-sized stack: CLI global-init emission + a startup init loop
        // + a linker `.wasm_globals` region + a FULL-BOOT differential (a
        // hand-initialized-region harness would be VACUOUS — the pre-#798
        // control_step lesson). Deferred as that piece, VCR-SEL-005.
        (
            "global.get",
            "RV32 globals need a base-relative region + startup init + linker \
             wiring (#798-class), not a selector arm: the RV32 encoder has no \
             data-symbol reloc and emits ET_REL only — deferred, VCR-SEL-005",
        ),
        (
            "global.set",
            "RV32 globals need a base-relative region + startup init + linker \
             wiring (#798-class), not a selector arm: the RV32 encoder has no \
             data-symbol reloc and emits ET_REL only — deferred, VCR-SEL-005",
        ),
        // ---- bulk memory (measured 2026-07-17) ----
        // (memory.size / memory.grow CLOSED v0.50, #242 — RV32 now lowers both:
        //  fixed-memory page-count constant + fixed-memory `-1` grow, with the
        //  shared `rewrite_memory_grow_zero` fold so grow(0)≡size. Execution
        //  differential: scripts/repro/rv32_mem_size_grow_242_differential.py.)
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

/// Ledger of KNOWN AArch64-vs-ARM divergences among the INTEGER-CORE ops (#851
/// — the third-backend leg of VCR-SEL-005). ARM (the most complete backend) is
/// the reference: an entry means "ARM lowers this, the aarch64 selector
/// loud-declines it" (or, exceptionally, the reverse — the reason must say so).
/// Same contract as [`known_divergences`]: every entry carries a concrete
/// reason; when the aarch64 lowering lands the stale-entry check FAILS until
/// the line is deleted, so a deferral cannot quietly outlive its fix.
///
/// MEASURED 2026-07-29 (this file's aarch64 leg, probing the real selector):
/// the initial enumeration surfaced TWENTY ARM-lowers/aarch64-declines gaps.
/// Thirteen were closed in the same change (v0.53 #851: `select` via
/// CSEL/FCSEL, `drop`, `nop`, `i32.wrap_i64`, `i64.extend_i32_{s,u}`, the five
/// `extend8/16/32_s` forms, fixed-memory `memory.size`/`memory.grow`), leaving
/// the SEVEN below. This ledger — the COMPLEMENT of what aarch64 lowers — is
/// the mechanically-derived answer to "what is missing on armv8?" (#851); the
/// float-surface complement lives in [`a64_extended_surface`].
fn aarch64_known_divergences() -> &'static [(&'static str, &'static str)] {
    &[
        (
            "br_table",
            "aarch64 selector has no BrTable arm (loud decline); the jump-table \
             dispatch is not yet lowered — deferred, VCR-SEL-005/#851",
        ),
        (
            "local.set+get(param)",
            "aarch64 declines WRITING a parameter: params live in arg registers \
             by reference on the value stack, so a param write could alias a \
             stacked value; param HOMING (to callee-saved regs or slots) is the \
             prerequisite — deferred, #851",
        ),
        (
            "local.tee(param)",
            "aarch64 declines writing a parameter (same homing prerequisite as \
             local.set) — deferred, #851",
        ),
        (
            "global.get",
            "aarch64 has no globals substrate (no data section / global-region \
             addressing convention beyond the x28 linear-memory base); the \
             RV32 ledger entry above documents the same #798-class stack needed \
             — deferred, #851",
        ),
        (
            "global.set",
            "aarch64 has no globals substrate (see global.get) — deferred, #851",
        ),
        (
            "memory.copy",
            "aarch64 selector has no MemoryCopy arm (loud decline); bulk-memory \
             (#374) not yet lowered on aarch64 — deferred, #851",
        ),
        (
            "memory.fill",
            "aarch64 selector has no MemoryFill arm (loud decline); bulk-memory \
             (#374) not yet lowered on aarch64 — deferred, #851",
        ),
    ]
}

/// The aarch64 leg of the parity gate: probe every INTEGER-CORE op on the
/// AArch64 selector against the ARM reference. Same both-direction contract as
/// [`run_parity`]: an unledgered divergence is a #223-class gap (red); a
/// ledgered entry whose gap has closed is stale (red until deleted).
fn run_a64_parity(
    ledger: &std::collections::HashMap<&str, &str>,
) -> (usize, Vec<String>, Vec<String>) {
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
            ParityClass::StructurallyExcluded(_) => continue,
        };

        let arm = arm_lowers(&ops, num_params);
        let a64 = aarch64_lowers(&ops, num_params);
        let ledgered = ledger.get(label);

        match (arm == a64, ledgered) {
            (true, None) => at_parity += 1,
            (true, Some(_reason)) => stale.push(format!(
                "  {label} — ledgered as an ARM/aarch64 divergence but both now \
                 agree (arm_ok={arm}, aarch64_ok={a64}); delete the entry"
            )),
            (false, Some(_reason)) => { /* known, explained divergence — OK */ }
            (false, None) => unexpected.push(format!(
                "  {label} — arm_lowers={arm}, aarch64_lowers={a64} (cross-backend \
                 op-gap; the #223 class, third backend). Either implement the \
                 missing aarch64 lowering or ledger it with a reason."
            )),
        }
    }
    (at_parity, unexpected, stale)
}

/// The aarch64 surface for the ops [`classify`] marks `StructurallyExcluded`
/// (#851). Those exclusions exist because the ARM float lowering is
/// TARGET-PARAMETERIZED and RV32 has no FPU — but the aarch64 backend has ONE
/// fixed host profile, so its float surface IS probe-able and deserves the same
/// no-gap-can-hide treatment. NO wildcard arm: a new `WasmOp` variant fails to
/// compile here too until placed.
///
/// Returns `None` for ops handled by the IntegerCore parity leg
/// ([`run_a64_parity`]), `Some((label, num_params, probe, expect))` otherwise,
/// where `expect` is `Ok(())` when the aarch64 selector MUST lower the probe
/// and `Err(reason)` when it MUST decline (the reason documents the gap — the
/// valuable complement). Both directions are asserted: a decline where lowering
/// is expected is a regression; a lowering where a decline is recorded is a
/// stale entry that must be flipped (a gap claim must not outlive the gap).
#[allow(clippy::type_complexity)]
fn a64_extended_surface(
    op: &WasmOp,
) -> Option<(&'static str, u32, Vec<WasmOp>, Result<(), &'static str>)> {
    // Gap reasons, shared per class.
    const ROUNDING: &str = "aarch64 selector has no ceil/floor/trunc/nearest arm (A64 FRINTP/FRINTM/\
         FRINTZ/FRINTN exist; encoder support not yet landed) — deferred, #851";
    const FP_MEM: &str = "aarch64 selector has no f32/f64 load/store arm (linear-memory FP access \
         needs LDR/STR (SIMD&FP) forms) — deferred, #851";
    const I64_TO_FP: &str = "aarch64 selector has no i64→float convert arm (SCVTF/UCVTF x-forms not \
         yet landed; only the i32-source forms are) — deferred, #851";
    const TRAP_TRUNC_I64: &str = "aarch64 selector has no TRAPPING i64-target truncation arm (needs the \
         #709-class i64 domain guard; the SATURATING i64 forms do lower) — \
         deferred, #851";
    const SIMD: &str = "v128/SIMD is not lowered on aarch64 (Advanced-SIMD lowering is a separate \
         lane, mirroring the ARM Helium/MVE exclusion) — deferred, #851";
    const MULTI_MEM: &str = "multi-memory wrapper (#406): the aarch64 backend has no per-memory base \
         lowering (single x28 base only) — declines, #851";
    const CALL_INDIRECT: &str = "call_indirect needs a function table + type/null/OOB trap guards \
         (§4.4.8); no aarch64 table substrate yet — loud-declined, #851";

    let some =
        |label: &'static str,
         num_params: u32,
         ops: Vec<WasmOp>,
         expect: Result<(), &'static str>| Some((label, num_params, ops, expect));

    match op {
        // ─── handled by the IntegerCore parity leg ───────────────────────
        I32Add
        | I32Sub
        | I32Mul
        | I32DivS
        | I32DivU
        | I32RemS
        | I32RemU
        | I32And
        | I32Or
        | I32Xor
        | I32Shl
        | I32ShrS
        | I32ShrU
        | I32Rotl
        | I32Rotr
        | I32Clz
        | I32Ctz
        | I32Popcnt
        | I32Extend8S
        | I32Extend16S
        | I32Eqz
        | I32Eq
        | I32Ne
        | I32LtS
        | I32LtU
        | I32LeS
        | I32LeU
        | I32GtS
        | I32GtU
        | I32GeS
        | I32GeU
        | I32Const(_)
        | I32Load { .. }
        | I32Store { .. }
        | I32Load8S { .. }
        | I32Load8U { .. }
        | I32Load16S { .. }
        | I32Load16U { .. }
        | I32Store8 { .. }
        | I32Store16 { .. }
        | Block
        | Loop
        | Br(_)
        | BrIf(_)
        | BrTable { .. }
        | Return
        | If
        | Else
        | End
        | Call(_)
        | LocalGet(_)
        | LocalSet(_)
        | LocalTee(_)
        | GlobalGet(_)
        | GlobalSet(_)
        | MemorySize(_)
        | MemoryGrow(_)
        | MemoryCopy
        | MemoryFill
        | Drop
        | Select
        | Unreachable
        | Nop
        | I64Add
        | I64Sub
        | I64Mul
        | I64DivS
        | I64DivU
        | I64RemS
        | I64RemU
        | I64And
        | I64Or
        | I64Xor
        | I64Shl
        | I64ShrS
        | I64ShrU
        | I64Rotl
        | I64Rotr
        | I64Clz
        | I64Ctz
        | I64Popcnt
        | I64Eqz
        | I64Eq
        | I64Ne
        | I64LtS
        | I64LtU
        | I64LeS
        | I64LeU
        | I64GtS
        | I64GtU
        | I64GeS
        | I64GeU
        | I64Const(_)
        | I64Load { .. }
        | I64Store { .. }
        | I64Load8S { .. }
        | I64Load8U { .. }
        | I64Load16S { .. }
        | I64Load16U { .. }
        | I64Load32S { .. }
        | I64Load32U { .. }
        | I64Store8 { .. }
        | I64Store16 { .. }
        | I64Store32 { .. }
        | I64ExtendI32S
        | I64ExtendI32U
        | I32WrapI64
        | I64Extend8S
        | I64Extend16S
        | I64Extend32S => None,

        // ─── f32 arithmetic / compares — lower (m3/m4, #538) ─────────────
        F32Add => some(
            "f32.add",
            0,
            vec![F32Const(1.5), F32Const(2.5), F32Add],
            Ok(()),
        ),
        F32Sub => some(
            "f32.sub",
            0,
            vec![F32Const(1.5), F32Const(2.5), F32Sub],
            Ok(()),
        ),
        F32Mul => some(
            "f32.mul",
            0,
            vec![F32Const(1.5), F32Const(2.5), F32Mul],
            Ok(()),
        ),
        F32Div => some(
            "f32.div",
            0,
            vec![F32Const(1.5), F32Const(2.5), F32Div],
            Ok(()),
        ),
        F32Eq => some(
            "f32.eq",
            0,
            vec![F32Const(1.0), F32Const(2.0), F32Eq],
            Ok(()),
        ),
        F32Ne => some(
            "f32.ne",
            0,
            vec![F32Const(1.0), F32Const(2.0), F32Ne],
            Ok(()),
        ),
        F32Lt => some(
            "f32.lt",
            0,
            vec![F32Const(1.0), F32Const(2.0), F32Lt],
            Ok(()),
        ),
        F32Le => some(
            "f32.le",
            0,
            vec![F32Const(1.0), F32Const(2.0), F32Le],
            Ok(()),
        ),
        F32Gt => some(
            "f32.gt",
            0,
            vec![F32Const(1.0), F32Const(2.0), F32Gt],
            Ok(()),
        ),
        F32Ge => some(
            "f32.ge",
            0,
            vec![F32Const(1.0), F32Const(2.0), F32Ge],
            Ok(()),
        ),
        F32Abs => some("f32.abs", 0, vec![F32Const(-1.5), F32Abs], Ok(())),
        F32Neg => some("f32.neg", 0, vec![F32Const(1.5), F32Neg], Ok(())),
        F32Sqrt => some("f32.sqrt", 0, vec![F32Const(2.0), F32Sqrt], Ok(())),
        F32Min => some(
            "f32.min",
            0,
            vec![F32Const(1.0), F32Const(2.0), F32Min],
            Ok(()),
        ),
        F32Max => some(
            "f32.max",
            0,
            vec![F32Const(1.0), F32Const(2.0), F32Max],
            Ok(()),
        ),
        F32Copysign => some(
            "f32.copysign",
            0,
            vec![F32Const(1.0), F32Const(-2.0), F32Copysign],
            Ok(()),
        ),
        F32Const(_) => some("f32.const", 0, vec![F32Const(1.0)], Ok(())),
        // ─── f32 rounding — GAP ──────────────────────────────────────────
        F32Ceil => some("f32.ceil", 0, vec![F32Const(1.5), F32Ceil], Err(ROUNDING)),
        F32Floor => some("f32.floor", 0, vec![F32Const(1.5), F32Floor], Err(ROUNDING)),
        F32Trunc => some("f32.trunc", 0, vec![F32Const(1.5), F32Trunc], Err(ROUNDING)),
        F32Nearest => some(
            "f32.nearest",
            0,
            vec![F32Const(1.5), F32Nearest],
            Err(ROUNDING),
        ),
        // ─── f32 memory — GAP ────────────────────────────────────────────
        F32Load { .. } => some(
            "f32.load",
            0,
            vec![
                I32Const(0),
                F32Load {
                    offset: 0,
                    align: 2,
                },
            ],
            Err(FP_MEM),
        ),
        F32Store { .. } => some(
            "f32.store",
            0,
            vec![
                I32Const(0),
                F32Const(1.0),
                F32Store {
                    offset: 0,
                    align: 2,
                },
            ],
            Err(FP_MEM),
        ),
        // ─── f32 conversions ─────────────────────────────────────────────
        F32ConvertI32S => some(
            "f32.convert_i32_s",
            0,
            vec![I32Const(5), F32ConvertI32S],
            Ok(()),
        ),
        F32ConvertI32U => some(
            "f32.convert_i32_u",
            0,
            vec![I32Const(5), F32ConvertI32U],
            Ok(()),
        ),
        F32ConvertI64S => some(
            "f32.convert_i64_s",
            0,
            vec![I64Const(5), F32ConvertI64S],
            Err(I64_TO_FP),
        ),
        F32ConvertI64U => some(
            "f32.convert_i64_u",
            0,
            vec![I64Const(5), F32ConvertI64U],
            Err(I64_TO_FP),
        ),
        F32DemoteF64 => some(
            "f32.demote_f64",
            0,
            vec![F64Const(1.5), F32DemoteF64],
            Ok(()),
        ),
        F32ReinterpretI32 => some(
            "f32.reinterpret_i32",
            0,
            vec![I32Const(1), F32ReinterpretI32],
            Ok(()),
        ),
        I32ReinterpretF32 => some(
            "i32.reinterpret_f32",
            0,
            vec![F32Const(1.0), I32ReinterpretF32],
            Ok(()),
        ),
        I32TruncF32S => some(
            "i32.trunc_f32_s",
            0,
            vec![F32Const(1.5), I32TruncF32S],
            Ok(()),
        ),
        I32TruncF32U => some(
            "i32.trunc_f32_u",
            0,
            vec![F32Const(1.5), I32TruncF32U],
            Ok(()),
        ),
        I32TruncSatF32S => some(
            "i32.trunc_sat_f32_s",
            0,
            vec![F32Const(1.5), I32TruncSatF32S],
            Ok(()),
        ),
        I32TruncSatF32U => some(
            "i32.trunc_sat_f32_u",
            0,
            vec![F32Const(1.5), I32TruncSatF32U],
            Ok(()),
        ),
        I64TruncSatF32S => some(
            "i64.trunc_sat_f32_s",
            0,
            vec![F32Const(1.5), I64TruncSatF32S],
            Ok(()),
        ),
        I64TruncSatF32U => some(
            "i64.trunc_sat_f32_u",
            0,
            vec![F32Const(1.5), I64TruncSatF32U],
            Ok(()),
        ),
        I64TruncF32S => some(
            "i64.trunc_f32_s",
            0,
            vec![F32Const(1.5), I64TruncF32S],
            Err(TRAP_TRUNC_I64),
        ),
        I64TruncF32U => some(
            "i64.trunc_f32_u",
            0,
            vec![F32Const(1.5), I64TruncF32U],
            Err(TRAP_TRUNC_I64),
        ),

        // ─── f64 arithmetic / compares — lower (m3/m4, #538) ─────────────
        F64Add => some(
            "f64.add",
            0,
            vec![F64Const(1.5), F64Const(2.5), F64Add],
            Ok(()),
        ),
        F64Sub => some(
            "f64.sub",
            0,
            vec![F64Const(1.5), F64Const(2.5), F64Sub],
            Ok(()),
        ),
        F64Mul => some(
            "f64.mul",
            0,
            vec![F64Const(1.5), F64Const(2.5), F64Mul],
            Ok(()),
        ),
        F64Div => some(
            "f64.div",
            0,
            vec![F64Const(1.5), F64Const(2.5), F64Div],
            Ok(()),
        ),
        F64Eq => some(
            "f64.eq",
            0,
            vec![F64Const(1.0), F64Const(2.0), F64Eq],
            Ok(()),
        ),
        F64Ne => some(
            "f64.ne",
            0,
            vec![F64Const(1.0), F64Const(2.0), F64Ne],
            Ok(()),
        ),
        F64Lt => some(
            "f64.lt",
            0,
            vec![F64Const(1.0), F64Const(2.0), F64Lt],
            Ok(()),
        ),
        F64Le => some(
            "f64.le",
            0,
            vec![F64Const(1.0), F64Const(2.0), F64Le],
            Ok(()),
        ),
        F64Gt => some(
            "f64.gt",
            0,
            vec![F64Const(1.0), F64Const(2.0), F64Gt],
            Ok(()),
        ),
        F64Ge => some(
            "f64.ge",
            0,
            vec![F64Const(1.0), F64Const(2.0), F64Ge],
            Ok(()),
        ),
        F64Abs => some("f64.abs", 0, vec![F64Const(-1.5), F64Abs], Ok(())),
        F64Neg => some("f64.neg", 0, vec![F64Const(1.5), F64Neg], Ok(())),
        F64Sqrt => some("f64.sqrt", 0, vec![F64Const(2.0), F64Sqrt], Ok(())),
        F64Min => some(
            "f64.min",
            0,
            vec![F64Const(1.0), F64Const(2.0), F64Min],
            Ok(()),
        ),
        F64Max => some(
            "f64.max",
            0,
            vec![F64Const(1.0), F64Const(2.0), F64Max],
            Ok(()),
        ),
        F64Copysign => some(
            "f64.copysign",
            0,
            vec![F64Const(1.0), F64Const(-2.0), F64Copysign],
            Ok(()),
        ),
        F64Const(_) => some("f64.const", 0, vec![F64Const(1.0)], Ok(())),
        // ─── f64 rounding — GAP ──────────────────────────────────────────
        F64Ceil => some("f64.ceil", 0, vec![F64Const(1.5), F64Ceil], Err(ROUNDING)),
        F64Floor => some("f64.floor", 0, vec![F64Const(1.5), F64Floor], Err(ROUNDING)),
        F64Trunc => some("f64.trunc", 0, vec![F64Const(1.5), F64Trunc], Err(ROUNDING)),
        F64Nearest => some(
            "f64.nearest",
            0,
            vec![F64Const(1.5), F64Nearest],
            Err(ROUNDING),
        ),
        // ─── f64 memory — GAP ────────────────────────────────────────────
        F64Load { .. } => some(
            "f64.load",
            0,
            vec![
                I32Const(0),
                F64Load {
                    offset: 0,
                    align: 3,
                },
            ],
            Err(FP_MEM),
        ),
        F64Store { .. } => some(
            "f64.store",
            0,
            vec![
                I32Const(0),
                F64Const(1.0),
                F64Store {
                    offset: 0,
                    align: 3,
                },
            ],
            Err(FP_MEM),
        ),
        // ─── f64 conversions ─────────────────────────────────────────────
        F64ConvertI32S => some(
            "f64.convert_i32_s",
            0,
            vec![I32Const(5), F64ConvertI32S],
            Ok(()),
        ),
        F64ConvertI32U => some(
            "f64.convert_i32_u",
            0,
            vec![I32Const(5), F64ConvertI32U],
            Ok(()),
        ),
        F64ConvertI64S => some(
            "f64.convert_i64_s",
            0,
            vec![I64Const(5), F64ConvertI64S],
            Err(I64_TO_FP),
        ),
        F64ConvertI64U => some(
            "f64.convert_i64_u",
            0,
            vec![I64Const(5), F64ConvertI64U],
            Err(I64_TO_FP),
        ),
        F64PromoteF32 => some(
            "f64.promote_f32",
            0,
            vec![F32Const(1.5), F64PromoteF32],
            Ok(()),
        ),
        F64ReinterpretI64 => some(
            "f64.reinterpret_i64",
            0,
            vec![I64Const(1), F64ReinterpretI64],
            Ok(()),
        ),
        I64ReinterpretF64 => some(
            "i64.reinterpret_f64",
            0,
            vec![F64Const(1.0), I64ReinterpretF64],
            Ok(()),
        ),
        I32TruncF64S => some(
            "i32.trunc_f64_s",
            0,
            vec![F64Const(1.5), I32TruncF64S],
            Ok(()),
        ),
        I32TruncF64U => some(
            "i32.trunc_f64_u",
            0,
            vec![F64Const(1.5), I32TruncF64U],
            Ok(()),
        ),
        I32TruncSatF64S => some(
            "i32.trunc_sat_f64_s",
            0,
            vec![F64Const(1.5), I32TruncSatF64S],
            Ok(()),
        ),
        I32TruncSatF64U => some(
            "i32.trunc_sat_f64_u",
            0,
            vec![F64Const(1.5), I32TruncSatF64U],
            Ok(()),
        ),
        I64TruncSatF64S => some(
            "i64.trunc_sat_f64_s",
            0,
            vec![F64Const(1.5), I64TruncSatF64S],
            Ok(()),
        ),
        I64TruncSatF64U => some(
            "i64.trunc_sat_f64_u",
            0,
            vec![F64Const(1.5), I64TruncSatF64U],
            Ok(()),
        ),
        I64TruncF64S => some(
            "i64.trunc_f64_s",
            0,
            vec![F64Const(1.5), I64TruncF64S],
            Err(TRAP_TRUNC_I64),
        ),
        I64TruncF64U => some(
            "i64.trunc_f64_u",
            0,
            vec![F64Const(1.5), I64TruncF64U],
            Err(TRAP_TRUNC_I64),
        ),

        // ─── module-context ops — declines with named reasons ────────────
        MultiMemory { .. } => some(
            "multi-memory wrapper",
            0,
            vec![
                I32Const(0),
                MultiMemory {
                    memory: 1,
                    op: Box::new(I32Load {
                        offset: 0,
                        align: 2,
                    }),
                },
            ],
            Err(MULTI_MEM),
        ),
        CallIndirect { .. } => some(
            "call_indirect",
            0,
            vec![
                I32Const(0),
                CallIndirect {
                    type_index: 0,
                    table_index: 0,
                },
            ],
            Err(CALL_INDIRECT),
        ),

        // ─── v128 / SIMD — GAP (all decline) ─────────────────────────────
        V128Const(_) => some("v128.const", 0, vec![V128Const([0; 16])], Err(SIMD)),
        V128Load { .. } => some(
            "v128.load",
            0,
            vec![
                I32Const(0),
                V128Load {
                    offset: 0,
                    align: 4,
                },
            ],
            Err(SIMD),
        ),
        V128Store { .. } => some(
            "v128.store",
            0,
            vec![
                I32Const(0),
                V128Const([0; 16]),
                V128Store {
                    offset: 0,
                    align: 4,
                },
            ],
            Err(SIMD),
        ),
        V128And => some(
            "v128.and",
            0,
            vec![V128Const([0; 16]), V128Const([0; 16]), V128And],
            Err(SIMD),
        ),
        V128Or => some(
            "v128.or",
            0,
            vec![V128Const([0; 16]), V128Const([0; 16]), V128Or],
            Err(SIMD),
        ),
        V128Xor => some(
            "v128.xor",
            0,
            vec![V128Const([0; 16]), V128Const([0; 16]), V128Xor],
            Err(SIMD),
        ),
        V128Not => some("v128.not", 0, vec![V128Const([0; 16]), V128Not], Err(SIMD)),
        V128AndNot => some(
            "v128.andnot",
            0,
            vec![V128Const([0; 16]), V128Const([0; 16]), V128AndNot],
            Err(SIMD),
        ),
        I8x16Add | I8x16Sub | I8x16Neg | I8x16Eq | I8x16Ne | I8x16LtS | I8x16LtU | I8x16GtS
        | I8x16GtU | I8x16LeS | I8x16LeU | I8x16GeS | I8x16GeU | I8x16Splat
        | I8x16ExtractLaneS(_) | I8x16ExtractLaneU(_) | I8x16ReplaceLane(_) | I8x16Shuffle(_)
        | I8x16Swizzle | I16x8Add | I16x8Sub | I16x8Mul | I16x8Neg | I16x8Eq | I16x8Ne
        | I16x8LtS | I16x8LtU | I16x8GtS | I16x8GtU | I16x8LeS | I16x8LeU | I16x8GeS | I16x8GeU
        | I16x8Splat | I16x8ExtractLaneS(_) | I16x8ExtractLaneU(_) | I16x8ReplaceLane(_)
        | I32x4Add | I32x4Sub | I32x4Mul | I32x4Neg | I32x4Eq | I32x4Ne | I32x4LtS | I32x4LtU
        | I32x4GtS | I32x4GtU | I32x4LeS | I32x4LeU | I32x4GeS | I32x4GeU | I32x4Splat
        | I32x4ExtractLane(_) | I32x4ReplaceLane(_) | I64x2Add | I64x2Sub | I64x2Mul | I64x2Neg
        | I64x2Eq | I64x2Ne | I64x2LtS | I64x2GtS | I64x2LeS | I64x2GeS | I64x2Splat
        | I64x2ExtractLane(_) | I64x2ReplaceLane(_) | F32x4Add | F32x4Sub | F32x4Mul | F32x4Div
        | F32x4Abs | F32x4Neg | F32x4Sqrt | F32x4Eq | F32x4Ne | F32x4Lt | F32x4Le | F32x4Gt
        | F32x4Ge | F32x4Splat | F32x4ExtractLane(_) | F32x4ReplaceLane(_) => some(
            "simd (grouped)",
            0,
            vec![V128Const([0; 16]), V128Const([0; 16]), op.clone()],
            Err(SIMD),
        ),
    }
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

/// #851 — the aarch64 (third-backend) integer-core parity gate. Same shape as
/// [`cross_backend_integer_op_parity_242`]: an unledgered ARM/aarch64
/// divergence is red (the #223 class on the third backend); a ledgered entry
/// whose gap closed is red until deleted.
#[test]
fn aarch64_integer_op_parity_851() {
    let ledger: std::collections::HashMap<&str, &str> =
        aarch64_known_divergences().iter().copied().collect();

    let (at_parity, unexpected, stale) = run_a64_parity(&ledger);

    // Non-vacuity floor: the probe must actually exercise the aarch64 selector
    // across the shared integer core.
    assert!(
        at_parity >= 60,
        "aarch64 parity leg exercised too few common-core ops ({at_parity}); \
         the classifier or the aarch64 probe construction regressed"
    );

    assert!(
        unexpected.is_empty() && stale.is_empty(),
        "ARM/aarch64 op-parity ledger is out of date:\n\
         NEW UNEXPLAINED DIVERGENCES (the #223 op-gap class, third backend):\n{}\n\
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

/// #851 — the aarch64 EXTENDED surface (the ops the ARM/RV32 integer oracle
/// structurally excludes: floats, SIMD, module-context wrappers). Asserts, for
/// every such op, that the aarch64 selector's probe outcome MATCHES the
/// recorded expectation in BOTH directions:
///   * expected-Lowers but declines → capability regression (red);
///   * expected-Declines but lowers → stale gap entry (red until the entry is
///     flipped to `Ok(())` — a gap claim must not outlive the gap).
///
/// The `Err(reason)` entries of [`a64_extended_surface`], together with the
/// [`aarch64_known_divergences`] ledger, ARE the definitive mechanically-
/// derived "what aarch64 does not lower" list.
#[test]
fn aarch64_extended_surface_851() {
    let mut mismatches: Vec<String> = Vec::new();
    let mut probed = 0usize;

    for op in all_wasm_op_representatives() {
        let Some((label, num_params, ops, expect)) = a64_extended_surface(&op) else {
            continue;
        };
        probed += 1;
        let lowered = aarch64_lowers(&ops, num_params);
        match (lowered, expect) {
            (true, Ok(())) | (false, Err(_)) => {}
            (false, Ok(())) => mismatches.push(format!(
                "  {label} — expected the aarch64 selector to LOWER this probe, \
                 but it declined (capability regression)"
            )),
            (true, Err(reason)) => mismatches.push(format!(
                "  {label} — recorded as an aarch64 gap ({reason}) but the \
                 selector now LOWERS the probe; flip the entry to Ok(())"
            )),
        }
    }

    // Non-vacuity floor: the extended surface spans the float + SIMD universe.
    assert!(
        probed >= 100,
        "aarch64 extended-surface probe exercised too few ops ({probed})"
    );
    assert!(
        mismatches.is_empty(),
        "aarch64 extended-surface expectations are out of date:\n{}",
        mismatches.join("\n")
    );
}

/// RED-FIRST non-vacuity proof for the aarch64 leg: drop a KNOWN, REAL
/// ARM-lowers/aarch64-declines entry from the ledger and assert the gate goes
/// red — proving [`run_a64_parity`] genuinely detects a one-sided gap on the
/// real selectors.
#[test]
fn red_first_unledgered_aarch64_gap_is_caught() {
    let (probe_label, _) = aarch64_known_divergences()[0];
    let ledger: std::collections::HashMap<&str, &str> = aarch64_known_divergences()
        .iter()
        .copied()
        .filter(|(label, _)| *label != probe_label)
        .collect();

    let (_at_parity, unexpected, _stale) = run_a64_parity(&ledger);

    assert!(
        unexpected.iter().any(|line| line.contains(probe_label)),
        "RED-FIRST vacuity check FAILED: dropping the '{probe_label}' ledger \
         entry did NOT surface it as an unexpected ARM/aarch64 divergence. \
         unexpected = {unexpected:?}"
    );
}

/// Every aarch64-ledgered divergence must name a live `IntegerCore` label
/// (same anti-drift rule as [`ledger_labels_are_live_integer_core_ops`]).
#[test]
fn aarch64_ledger_labels_are_live_integer_core_ops() {
    let live: std::collections::HashSet<&str> = all_wasm_op_representatives()
        .iter()
        .filter_map(|op| match classify(op) {
            ParityClass::IntegerCore { label, .. } => Some(label),
            ParityClass::StructurallyExcluded(_) => None,
        })
        .collect();

    let dangling: Vec<&str> = aarch64_known_divergences()
        .iter()
        .map(|(label, _)| *label)
        .filter(|label| !live.contains(label))
        .collect();

    assert!(
        dangling.is_empty(),
        "aarch64 known-divergence ledger references labels that are not live \
         IntegerCore ops: {dangling:?}"
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
