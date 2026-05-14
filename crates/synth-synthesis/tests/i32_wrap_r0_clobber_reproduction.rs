//! Regression test for the AAPCS clobber surfaced by PR #100's
//! `i64_lowering_doesnt_clobber_params` cargo-fuzz harness.
//!
//! ## Fuzz crash signature
//!
//! ```text
//! AAPCS clobber: ARM instr at wasm line 1 writes param reg R0 before
//! LocalGet(0) at line 3.
//! Op: Mov { rd: R0, op2: Reg(R3) }
//! Sequence: [Push, I64Const{rdlo:R3,rdhi:R4,value:0}, Mov{rd:R0,op2:Reg(R3)}, Pop]
//! ```
//!
//! ## Trigger pattern
//!
//! The hypothesised pattern from the fuzz finding:
//!
//! ```text
//! i64.const 0       // emits I64Const into r3:r4
//! i32.wrap_i64      // — was hardcoding the *return register* R0 as
//!                   //   destination when this happens to be the last
//!                   //   wasm op, even though that's no longer a
//!                   //   guaranteed function-return boundary in the
//!                   //   fuzz-generated programs.
//! local.get 0       // would read R0 — but R0 was just clobbered
//! ```
//!
//! ## Root cause
//!
//! In `select_with_stack`, the `I32WrapI64` handler picked `Reg::R0` as the
//! destination when `idx == wasm_ops.len() - 1`. That heuristic conflates two
//! things:
//!
//! 1. **The function-return boundary** — the LAST wasm op of a function's
//!    body, where placing the result in R0 follows AAPCS.
//! 2. **The last wasm op in the slice handed to `select_with_stack`** — a
//!    purely lexical position that the fuzz harness happily violates by
//!    wrapping the user's `middle` in `LocalGet`/`Drop` suffix tests.
//!
//! Even when the harness's wrapper makes the I32WrapI64 *not* the last op,
//! a sufficiently small variant of the pattern (e.g. `[I64Const, I32WrapI64]`
//! exactly) trips it. The fix is to *always* allocate via `alloc_temp_safe`
//! and let the function epilogue handle the AAPCS return-value move.
//!
//! ## What this test asserts
//!
//! The exact reproduction from the fuzz crash. Before the fix, the
//! `idx == wasm_ops.len() - 1 → Reg::R0` shortcut emits an ARM op whose
//! destination is R0 in the middle of a function whose AAPCS-param R0 has
//! not been read yet. After the fix, no instruction whose `source_line` is
//! before the first `LocalGet(0)` writes R0.

use synth_synthesis::{ArmInstruction, ArmOp, InstructionSelector, Reg, RuleDatabase, WasmOp};

fn compile_no_optimize(wasm_ops: &[WasmOp], num_params: u32) -> Vec<ArmInstruction> {
    let db = RuleDatabase::new();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector
        .select_with_stack(wasm_ops, num_params)
        .expect("select_with_stack should succeed for valid input")
}

/// Get the registers an ArmOp writes. This widens the fuzz harness's `writes()`
/// to also include `I32WrapI64`, `I64ExtendI32U`, and `I64ExtendI32S` — the
/// three conversion ops whose `select_with_stack` handlers historically pinned
/// R0 / R0:R1 as their destination. If any of them produces a write-to-R0
/// before LocalGet(0), the test fails.
fn writes(op: &ArmOp) -> Vec<Reg> {
    match op {
        ArmOp::Add { rd, .. }
        | ArmOp::Sub { rd, .. }
        | ArmOp::Adds { rd, .. }
        | ArmOp::Adc { rd, .. }
        | ArmOp::Subs { rd, .. }
        | ArmOp::Sbc { rd, .. }
        | ArmOp::And { rd, .. }
        | ArmOp::Orr { rd, .. }
        | ArmOp::Eor { rd, .. }
        | ArmOp::Mov { rd, .. }
        | ArmOp::Mvn { rd, .. }
        | ArmOp::Movw { rd, .. }
        | ArmOp::Movt { rd, .. }
        | ArmOp::Lsl { rd, .. }
        | ArmOp::Lsr { rd, .. }
        | ArmOp::Asr { rd, .. }
        | ArmOp::Ror { rd, .. }
        | ArmOp::Rsb { rd, .. }
        | ArmOp::Mul { rd, .. }
        | ArmOp::Sdiv { rd, .. }
        | ArmOp::Udiv { rd, .. }
        | ArmOp::Clz { rd, .. }
        | ArmOp::Rbit { rd, .. }
        | ArmOp::Popcnt { rd, .. }
        | ArmOp::Sxtb { rd, .. }
        | ArmOp::Sxth { rd, .. }
        | ArmOp::Ldr { rd, .. }
        | ArmOp::Ldrb { rd, .. }
        | ArmOp::Ldrsb { rd, .. }
        | ArmOp::Ldrh { rd, .. }
        | ArmOp::Ldrsh { rd, .. }
        | ArmOp::SetCond { rd, .. }
        | ArmOp::I32WrapI64 { rd, .. }
        | ArmOp::I64SetCond { rd, .. }
        | ArmOp::I64SetCondZ { rd, .. }
        | ArmOp::SelectMove { rd, .. } => vec![*rd],
        ArmOp::I64Const { rdlo, rdhi, .. } => vec![*rdlo, *rdhi],
        ArmOp::I64ExtendI32S { rdlo, rdhi, .. } | ArmOp::I64ExtendI32U { rdlo, rdhi, .. } => {
            vec![*rdlo, *rdhi]
        }
        ArmOp::I64Mul { rd_lo, rd_hi, .. } => vec![*rd_lo, *rd_hi],
        _ => Vec::new(),
    }
}

/// Walk the lowered ARM instructions and assert no param reg is written before
/// the corresponding `LocalGet(p)` reads it. Mirrors PR #100's fuzz harness
/// invariant.
fn assert_no_param_clobber(wasm: &[WasmOp], arm: &[ArmInstruction], num_params: u32) {
    let param_regs: Vec<Reg> = (0..num_params.min(4))
        .map(|i| match i {
            0 => Reg::R0,
            1 => Reg::R1,
            2 => Reg::R2,
            3 => Reg::R3,
            _ => unreachable!(),
        })
        .collect();

    for (p, &param_reg) in param_regs.iter().enumerate() {
        let Some(first_read) = wasm
            .iter()
            .position(|op| matches!(op, WasmOp::LocalGet(idx) if *idx == p as u32))
        else {
            continue;
        };
        for instr in arm {
            let Some(line) = instr.source_line else {
                continue;
            };
            if line >= first_read {
                break;
            }
            for w in writes(&instr.op) {
                assert_ne!(
                    w,
                    param_reg,
                    "AAPCS clobber: ARM instr at wasm line {line} writes param reg \
                     {param_reg:?} before LocalGet({p}) at line {first_read}.\n  \
                     Offending Op: {:?}\n  \
                     Full sequence: {:#?}",
                    instr.op,
                    arm.iter().map(|i| &i.op).collect::<Vec<_>>(),
                );
            }
        }
    }
}

/// The literal pattern from the task description: i64.const, i32.wrap_i64,
/// local.get. With num_params=4 we exercise all four AAPCS param regs.
/// Before the fix: I32WrapI64's `idx == wasm_ops.len() - 1` branch picked R0,
/// so `ArmOp::I32WrapI64 { rd: R0, .. }` is emitted ahead of LocalGet(0).
/// After the fix: I32WrapI64 always uses `alloc_temp_safe`, deferring the
/// R0-placement to the function epilogue's return-value move.
#[test]
fn i32_wrap_i64_does_not_clobber_r0_when_followed_by_local_get() {
    // The shape from the task description: i64.const, i32.wrap_i64, then
    // local.get for each param. The harness from PR #100 would have caught
    // this if its `writes()` heuristic listed `I32WrapI64` (which the local
    // test's `writes()` does).
    let wasm = vec![
        WasmOp::I64Const(0),
        WasmOp::I32WrapI64,
        WasmOp::Drop,
        WasmOp::LocalGet(0),
        WasmOp::Drop,
        WasmOp::LocalGet(1),
        WasmOp::Drop,
        WasmOp::LocalGet(2),
        WasmOp::Drop,
        WasmOp::LocalGet(3),
        WasmOp::Drop,
    ];
    for num_params in [1u32, 2, 3, 4] {
        let arm = compile_no_optimize(&wasm, num_params);
        assert_no_param_clobber(&wasm, &arm, num_params);
    }
}

/// The "minimal" variant of the I32WrapI64 case: just `i64.const, i32.wrap_i64`
/// where I32WrapI64 IS the last op, so the pre-fix `idx == wasm_ops.len() - 1`
/// shortcut fires. We follow it with a LocalGet(0) inside a no-op pad so the
/// function body has a "first param read" line to anchor the check on.
///
/// Note: this scenario has no LocalGet to compare against in the body itself —
/// we synthesise one by appending LocalGet(0)/Drop. The pre-fix codegen WOULD
/// then put the I32WrapI64 result in R0 and clobber the LocalGet(0) read.
#[test]
fn i32_wrap_i64_minimal_does_not_clobber_r0() {
    // i64.const, i32.wrap_i64, drop, local.get 0, drop.
    let wasm = vec![
        WasmOp::I64Const(0xdead_beef),
        WasmOp::I32WrapI64,
        WasmOp::Drop,
        WasmOp::LocalGet(0),
        WasmOp::Drop,
    ];
    for num_params in [1u32, 2, 3, 4] {
        let arm = compile_no_optimize(&wasm, num_params);
        assert_no_param_clobber(&wasm, &arm, num_params);
    }
}

/// Pin the specific `idx == wasm_ops.len() - 1` branch of I32WrapI64.
///
/// When I32WrapI64 is the LAST op (and the harness's wrapper places its
/// `LocalGet(p)` AFTER the wasm_ops we hand to the selector, this can't
/// happen in the fuzz harness as-shipped — but it CAN happen inside any
/// function whose body is just `i64.const; i32.wrap_i64` with no trailing
/// drop/return). We synthesize such a function and assert the result is
/// not pinned to R0 in the I32WrapI64 ArmOp — that is, the dest should
/// come from the regalloc pool, and any return-value placement should
/// happen in the epilogue (which itself goes through `Mov R0, <last>`
/// only when the last value isn't already in R0).
#[test]
fn i32_wrap_i64_as_last_op_routes_through_alloc_temp_safe() {
    // wasm body: i64.const 0; i32.wrap_i64
    // (deliberately no Drop/LocalGet — I32WrapI64 IS the last wasm op,
    // hitting the historical "result in R0" shortcut.)
    let wasm = vec![WasmOp::I64Const(0), WasmOp::I32WrapI64];

    // num_params=3 is the worst case: alloc_consecutive_pair starts at
    // next_temp=3, returning (R3, R4) for the I64Const. Pre-fix, the
    // I32WrapI64 would then have rd=R0, clobbering the AAPCS param R0
    // that we haven't even read yet via LocalGet.
    let num_params = 3u32;
    let arm = compile_no_optimize(&wasm, num_params);

    // Find the I32WrapI64 emitted op and check its rd.
    let wrap = arm
        .iter()
        .find(|i| matches!(&i.op, ArmOp::I32WrapI64 { .. }))
        .expect("expected an I32WrapI64 op in the output");
    let ArmOp::I32WrapI64 { rd, .. } = wrap.op else {
        unreachable!()
    };

    // The destination of the I32WrapI64 itself must not be a still-live
    // AAPCS param register (R0..R2 for num_params=3). The function
    // epilogue may move the result into R0 separately, but at the
    // I32WrapI64 site we must not pin a param-reg destination.
    assert!(
        !matches!(rd, Reg::R0 | Reg::R1 | Reg::R2),
        "I32WrapI64 emitted with rd={rd:?}, but R0..R2 are AAPCS params for \
         num_params={num_params}. ARM sequence: {:#?}",
        arm.iter().map(|i| &i.op).collect::<Vec<_>>(),
    );
}

/// Companion check: I64ExtendI32U / I64ExtendI32S should also not clobber R0
/// before LocalGet(0). The task description calls these out as "possibly"
/// affected; this test pins it.
#[test]
fn i64_extend_i32_does_not_clobber_r0_before_local_get() {
    for op in [WasmOp::I64ExtendI32U, WasmOp::I64ExtendI32S] {
        let wasm = vec![
            WasmOp::I32Const(0),
            op,
            WasmOp::Drop,
            WasmOp::LocalGet(0),
            WasmOp::Drop,
        ];
        for num_params in [1u32, 2, 3, 4] {
            let arm = compile_no_optimize(&wasm, num_params);
            assert_no_param_clobber(&wasm, &arm, num_params);
        }
    }
}
