//! VCR-SEL-005 — cross-backend op-parity oracle (North Star, epic #242).
//!
//! WHY THIS EXISTS. The "selector missed an op" bug class (#223 Select +
//! non-param locals + sign-extend; #232) was never a *silent* miscompile —
//! both selectors fail honestly on an op they don't lower (ARM `select_default`
//! is an exhaustive `match` over `WasmOp`; RISC-V `selector.rs` ends op-dispatch
//! with `other => Err(SelectorError::Unsupported)`). The actual defect was
//! **cross-backend divergence**: ARM lowered an op that RV32 loud-declined, so a
//! function compiled on Cortex-M but was skipped on RISC-V — and nothing caught
//! that until gale ran it on qemu. The VCR-SEL-001 measurement (2026-06-20)
//! confirmed silent-drop is structurally closed on both backends, which
//! re-pointed the verified-selector value at exactly this: an op-PARITY gate.
//!
//! WHAT IT ASSERTS. For a curated set of self-contained, minimally-valid
//! `WasmOp` sequences, lower each on BOTH backends and classify Ok / Err. The
//! common integer core must be at **parity** (both Ok or both Err). Every
//! legitimate difference lives in [`KNOWN_DIVERGENCES`] with a written reason.
//! The test fails in BOTH directions:
//!   * a divergence NOT in the ledger  → a new #223-class op-gap, surfaced as a
//!     gate here instead of by gale on silicon;
//!   * a ledgered divergence that has CLOSED → stale entry, delete it (keeps the
//!     ledger honest — a parity claim must not outlive the gap it documents).
//!
//! SCOPE (no silent cap — the divergence is recorded, not hidden). This oracle
//! covers the INTEGER core where the #223/#232 op-gaps lived: i32/i64
//! arithmetic, bitwise, shift/rotate, compare, sign-extend, Select, the
//! width conversions, locals, and integer memory. Float (f32/f64) and SIMD
//! (v128) parity is a separate, large, known gap (ARM has VFP/Helium lowerings
//! RV32 does not); it is intentionally out of this first oracle's scope and is
//! tracked separately, NOT asserted here.

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

/// One parity probe: a human label, the parameter count, and a self-contained
/// minimally-valid op sequence that exercises the op named by `label`.
struct Case {
    label: &'static str,
    num_params: u32,
    ops: Vec<WasmOp>,
}

fn c(label: &'static str, num_params: u32, ops: Vec<WasmOp>) -> Case {
    Case {
        label,
        num_params,
        ops,
    }
}

/// Ledger of KNOWN ARM-vs-RISC-V parity differences. Key = the `Case::label`;
/// value = WHY the two backends disagree today. Two legitimate entry kinds —
/// both must carry a concrete reason, never a hand-wave:
///   * PERMANENT ISA divergence — one ISA structurally cannot express the op
///     in this target slice (e.g. ARM Helium SIMD has no RV32IMAC analogue).
///     Out of this integer oracle's scope; none here.
///   * TRACKED DEFERRAL — a #223-class op-gap that is named, reasoned, and
///     pointed at a tracking requirement. The ledger entry IS the "file it":
///     it makes the gap a gated, owned fact instead of a silicon surprise.
///     When the RV32 lowering lands, the stale-entry check (below) FAILS until
///     this line is deleted — so a deferral cannot quietly outlive its fix.
///
/// MEASURED 2026-06-20 (first oracle run): the RV32 selector loud-declines five
/// integer bit-manipulation ops the ARM selector lowers. All five are the Zbb
/// class (rotate / count-leading-zeros / count-trailing-zeros / popcount); the
/// RV32IMAC and rv32imc target slices do NOT include Zbb, so there is no single
/// native instruction. ARM lowers them via sequences (ROR/CLZ/RBIT — and a
/// software sequence for popcount, which ARMv7-M also lacks natively), proving
/// they are sequence-lowerable on RV32 too (as `Select` already is). Tracked as
/// deferrals under VCR-SEL-005 (artifacts/verified-codegen-roadmap.yaml) — the
/// concrete op-by-op follow-up this oracle exists to drive.
fn known_divergences() -> &'static [(&'static str, &'static str)] {
    &[
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
    ]
}

/// The curated integer-core parity set. Each sequence is valid in isolation:
/// constants supply every operand the op pops, so a lowering failure is an
/// op-coverage fact, not a stack-underflow artifact.
fn cases() -> Vec<Case> {
    vec![
        // ---- i32 arithmetic / bitwise (single-instruction binops) ----
        c("i32.add", 0, vec![I32Const(3), I32Const(5), I32Add]),
        c("i32.sub", 0, vec![I32Const(9), I32Const(4), I32Sub]),
        c("i32.mul", 0, vec![I32Const(3), I32Const(5), I32Mul]),
        c("i32.and", 0, vec![I32Const(6), I32Const(3), I32And]),
        c("i32.or", 0, vec![I32Const(6), I32Const(3), I32Or]),
        c("i32.xor", 0, vec![I32Const(6), I32Const(3), I32Xor]),
        // ---- i32 shift / rotate (rotate is the scratch-using class) ----
        c("i32.shl", 0, vec![I32Const(1), I32Const(4), I32Shl]),
        c("i32.shr_s", 0, vec![I32Const(-16), I32Const(2), I32ShrS]),
        c("i32.shr_u", 0, vec![I32Const(16), I32Const(2), I32ShrU]),
        c("i32.rotl", 0, vec![I32Const(1), I32Const(3), I32Rotl]),
        c("i32.rotr", 0, vec![I32Const(1), I32Const(3), I32Rotr]),
        // ---- i32 unary bit-counts ----
        c("i32.clz", 0, vec![I32Const(1), I32Clz]),
        c("i32.ctz", 0, vec![I32Const(8), I32Ctz]),
        c("i32.popcnt", 0, vec![I32Const(7), I32Popcnt]),
        // ---- i32 sign-extend (the #223 class) ----
        c("i32.extend8_s", 0, vec![I32Const(200), I32Extend8S]),
        c("i32.extend16_s", 0, vec![I32Const(40000), I32Extend16S]),
        // ---- i32 div / rem (trap-guarded) ----
        c("i32.div_s", 0, vec![I32Const(-9), I32Const(2), I32DivS]),
        c("i32.div_u", 0, vec![I32Const(9), I32Const(2), I32DivU]),
        c("i32.rem_s", 0, vec![I32Const(-9), I32Const(2), I32RemS]),
        c("i32.rem_u", 0, vec![I32Const(9), I32Const(2), I32RemU]),
        // ---- i32 comparison ----
        c("i32.eqz", 0, vec![I32Const(0), I32Eqz]),
        c("i32.eq", 0, vec![I32Const(3), I32Const(3), I32Eq]),
        c("i32.ne", 0, vec![I32Const(3), I32Const(4), I32Ne]),
        c("i32.lt_s", 0, vec![I32Const(-1), I32Const(1), I32LtS]),
        c("i32.lt_u", 0, vec![I32Const(1), I32Const(2), I32LtU]),
        c("i32.gt_s", 0, vec![I32Const(2), I32Const(1), I32GtS]),
        c("i32.ge_u", 0, vec![I32Const(2), I32Const(2), I32GeU]),
        // ---- Select (the #223 class) ----
        c(
            "select",
            0,
            vec![I32Const(10), I32Const(20), I32Const(1), Select],
        ),
        // ---- locals (the #223 non-param-local class) ----
        c("local.get(param)", 1, vec![LocalGet(0)]),
        c(
            "local.set+get(param)",
            1,
            vec![I32Const(42), LocalSet(0), LocalGet(0)],
        ),
        c("local.tee(param)", 1, vec![I32Const(42), LocalTee(0)]),
        // ---- integer memory (i32, sub-word) ----
        c(
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
        c(
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
        c(
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
        c(
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
        // ---- i64 arithmetic / bitwise ----
        c("i64.add", 0, vec![I64Const(3), I64Const(5), I64Add]),
        c("i64.sub", 0, vec![I64Const(9), I64Const(4), I64Sub]),
        c("i64.mul", 0, vec![I64Const(3), I64Const(5), I64Mul]),
        c("i64.and", 0, vec![I64Const(6), I64Const(3), I64And]),
        c("i64.or", 0, vec![I64Const(6), I64Const(3), I64Or]),
        c("i64.xor", 0, vec![I64Const(6), I64Const(3), I64Xor]),
        // ---- i64 shift ----
        c("i64.shl", 0, vec![I64Const(1), I64Const(4), I64Shl]),
        c("i64.shr_u", 0, vec![I64Const(16), I64Const(2), I64ShrU]),
        // ---- i64 unary / compare ----
        c("i64.clz", 0, vec![I64Const(1), I64Clz]),
        c("i64.popcnt", 0, vec![I64Const(7), I64Popcnt]),
        c("i64.eqz", 0, vec![I64Const(0), I64Eqz]),
        c("i64.eq", 0, vec![I64Const(3), I64Const(3), I64Eq]),
        c("i64.lt_s", 0, vec![I64Const(-1), I64Const(1), I64LtS]),
        // ---- width conversions (i32<->i64) ----
        c("i64.extend_i32_s", 0, vec![I32Const(-1), I64ExtendI32S]),
        c("i64.extend_i32_u", 0, vec![I32Const(-1), I64ExtendI32U]),
        c("i32.wrap_i64", 0, vec![I64Const(0x1_0000_0001), I32WrapI64]),
    ]
}

#[test]
fn cross_backend_integer_op_parity_242() {
    let ledger: std::collections::HashMap<&str, &str> =
        known_divergences().iter().copied().collect();

    let mut unexpected: Vec<String> = Vec::new(); // diverged but not ledgered
    let mut stale: Vec<String> = Vec::new(); // ledgered but no longer diverging
    let mut at_parity = 0usize;

    for case in cases() {
        let a = arm_lowers(&case.ops, case.num_params);
        let r = riscv_lowers(&case.ops, case.num_params);
        let ledgered = ledger.get(case.label);

        match (a == r, ledgered) {
            (true, None) => at_parity += 1,
            (true, Some(_reason)) => stale.push(format!(
                "  {} — ledgered as a divergence but BOTH backends now agree \
                 (arm_ok={a}, riscv_ok={r}); delete the KNOWN_DIVERGENCES entry",
                case.label
            )),
            (false, Some(_reason)) => { /* known, explained divergence — OK */ }
            (false, None) => unexpected.push(format!(
                "  {} — arm_lowers={a}, riscv_lowers={r} (cross-backend op-gap; \
                 the #223 class). Either implement the missing lowering, or add a \
                 KNOWN_DIVERGENCES entry with a reason.",
                case.label
            )),
        }
    }

    // Floor: the curated set must actually be exercising both backends, so a
    // construction regression (e.g. every case erroring on a stack-underflow
    // artifact) can't masquerade as "all at parity".
    assert!(
        at_parity >= 30,
        "parity oracle exercised too few common-core ops ({at_parity}); the \
         curated set or the selector construction regressed"
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
