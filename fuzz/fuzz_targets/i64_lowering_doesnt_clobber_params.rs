//! Fuzz target: AAPCS param register preservation across i64 lowering.
//!
//! Run with: `cargo +nightly fuzz run i64_lowering_doesnt_clobber_params -- -max_total_time=60`
//!
//! ## What this catches — the v0.1.1 AAPCS-clobber class
//!
//! AAPCS passes the first four i32 function arguments in `r0`..`r3`. The
//! synth backends had two consecutive bugs in this area:
//!
//! * #85 (no-optimize path): i64 op handlers picked dst register pairs
//!   without honoring already-allocated param regs.
//! * #86 (optimized path): the regalloc inside `optimizer_bridge::ir_to_arm`
//!   could pick `r0`:`r1` for an `I64Const` even when `r0` and `r1` held
//!   incoming i32 params, clobbering them before the user's wasm did its
//!   first `local.get`.
//!
//! The invariant a correct lowering must satisfy:
//!
//!   *Before each parameter `p ∈ [0,num_params)` is first **read** as a
//!   source by an ARM instruction emitted from a `LocalGet(p)`, no earlier
//!   ARM instruction may write to `R{p}`.*
//!
//! This harness builds a fuzz-driven program that mixes i32 params with
//! i64 ops, runs it through `select_with_stack`, and asserts the invariant.
//! A clobber is a libfuzzer crash.

#![no_main]

use libfuzzer_sys::fuzz_target;
use synth_core::WasmOp;
use synth_fuzz::{FuzzInput, lower_arbitrary_to_wasm_ops};
use synth_synthesis::{ArmOp, InstructionSelector, Reg, RuleDatabase};

fuzz_target!(|input: FuzzInput| {
    let num_params = input.num_params % 5; // 0..=4
    if num_params == 0 {
        return; // No params to clobber.
    }

    // Build a wasm program shape: mandatory `LocalGet(p)` for each param p
    // (so the harness can find each param's first-read site), then the
    // arbitrary ops, then a final `LocalGet(0)` to keep the stack
    // non-empty for return.
    //
    // Crucially we put the LocalGets *after* the arbitrary ops so any
    // i64 op that runs first has a chance to clobber the param regs
    // before anything reads them. (If we read params first the bug
    // can't manifest.)
    let mut wasm_ops: Vec<WasmOp> = Vec::new();
    let mut middle = lower_arbitrary_to_wasm_ops(&input.ops, num_params);
    // Skip control-flow ops we can't easily balance in this minimal harness.
    middle.retain(|op| !is_unbalanced_control_flow(op));
    if middle.is_empty() || middle.len() > 64 {
        return;
    }
    // Bias toward i64 ops by injecting at least one I64Const at the start.
    wasm_ops.push(WasmOp::I64Const(0));
    wasm_ops.extend(middle);
    wasm_ops.push(WasmOp::Drop); // drop the i64 const we pushed
    // Now do the param reads.
    for p in 0..num_params {
        wasm_ops.push(WasmOp::LocalGet(p));
        wasm_ops.push(WasmOp::Drop);
    }

    // Lower via the non-optimized path. (The optimized path takes a
    // different code route; harness 1 covers both for panic-freedom.
    // Here we focus on `select_with_stack` because its source_line
    // information makes the param-first-read site unambiguous.)
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = match selector.select_with_stack(&wasm_ops, num_params) {
        Ok(v) => v,
        Err(_) => return,
    };

    // For each param p, find the wasm index of its first LocalGet.
    let mut first_read_wasm_idx: [Option<usize>; 4] = [None; 4];
    for (idx, op) in wasm_ops.iter().enumerate() {
        if let WasmOp::LocalGet(p) = op {
            let p = *p as usize;
            if p < 4 && first_read_wasm_idx[p].is_none() {
                first_read_wasm_idx[p] = Some(idx);
            }
        }
    }

    // For each param p, walk the lowered ARM instructions in order. Any
    // instruction whose `source_line` is < first_read_wasm_idx[p] AND
    // writes R{p} is a clobber — UNLESS the source wasm op is
    // `LocalSet(p)` or `LocalTee(p)`, in which case the write to R{p}
    // is wasm-program-intended (the user explicitly asked to store into
    // param-local p). Without this carve-out the harness false-positives
    // on every `LocalSet(p); ...; LocalGet(p)` pattern, since the
    // LocalSet legitimately emits a Mov writing R{p}.
    for (p, &first_read_idx) in first_read_wasm_idx
        .iter()
        .take(num_params as usize)
        .enumerate()
    {
        let first_read = match first_read_idx {
            Some(i) => i,
            None => continue,
        };
        let param_reg = match p {
            0 => Reg::R0,
            1 => Reg::R1,
            2 => Reg::R2,
            3 => Reg::R3,
            _ => continue,
        };
        for instr in &arm_instrs {
            // The function prologue (Push, Sub from SP) has source_line None.
            // We only care about instructions that flow from user-level wasm ops.
            let line = match instr.source_line {
                Some(l) => l,
                None => continue,
            };
            if line >= first_read {
                break; // Past the param's first read — out of the window.
            }
            // Skip the wasm-program-intended write: LocalSet(p) and
            // LocalTee(p) MAY semantically write R{p} (it's where the
            // wasm local lives). The compiler is just honoring the wasm
            // program. A real compiler bug here would be a write from a
            // different wasm op (e.g., I32WrapI64 hardcoding R0 as its
            // destination — the bug PR #111 fixed).
            if let Some(WasmOp::LocalSet(p_op)) | Some(WasmOp::LocalTee(p_op)) =
                wasm_ops.get(line)
                && *p_op as usize == p
            {
                continue;
            }
            for w in writes(&instr.op) {
                assert_ne!(
                    w,
                    param_reg,
                    "AAPCS clobber: ARM instr at wasm line {line} writes param reg {param_reg:?} \
                     before LocalGet({p}) at line {first_read}. Op: {:?}. Sequence: {:?}",
                    instr.op,
                    arm_instrs
                        .iter()
                        .take(20)
                        .map(|i| &i.op)
                        .collect::<Vec<_>>(),
                );
            }
        }
    }
});

fn is_unbalanced_control_flow(op: &WasmOp) -> bool {
    matches!(
        op,
        WasmOp::Block
            | WasmOp::Loop
            | WasmOp::Br(_)
            | WasmOp::BrIf(_)
            | WasmOp::BrTable { .. }
            | WasmOp::Return
            | WasmOp::If
            | WasmOp::Else
            | WasmOp::End
            | WasmOp::Call(_)
            | WasmOp::CallIndirect { .. }
            | WasmOp::Unreachable
    )
}

/// Return the set of ARM registers an instruction writes.
///
/// Heuristic: covers the variants the i64-lowering stack actually produces.
/// Any ArmOp not listed is conservatively treated as writing nothing — that
/// gives this harness a soundness floor of "false negatives possible, false
/// positives impossible". Per-issue regression tests still pin down the
/// specific bugs; this harness's job is to surface *new* clobbers.
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
        | ArmOp::Lsl { rd, .. }
        | ArmOp::Lsr { rd, .. }
        | ArmOp::Asr { rd, .. }
        | ArmOp::Ror { rd, .. }
        | ArmOp::LslReg { rd, .. }
        | ArmOp::LsrReg { rd, .. }
        | ArmOp::AsrReg { rd, .. }
        | ArmOp::RorReg { rd, .. }
        | ArmOp::Rsb { rd, .. }
        | ArmOp::Mul { rd, .. }
        | ArmOp::Sdiv { rd, .. }
        | ArmOp::Udiv { rd, .. }
        | ArmOp::Mls { rd, .. }
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
        | ArmOp::I64SetCond { rd, .. }
        | ArmOp::I64SetCondZ { rd, .. }
        | ArmOp::SelectMove { rd, .. }
        | ArmOp::Select { rd, .. }
        | ArmOp::LocalGet { rd, .. }
        | ArmOp::GlobalGet { rd, .. }
        | ArmOp::MemorySize { rd }
        | ArmOp::MemoryGrow { rd, .. } => vec![*rd],

        // Movt preserves the low 16 bits but writes the high 16 — for the
        // purposes of "did we touch this register" we count it as a write.
        ArmOp::Movt { rd, .. } => vec![*rd],

        // i64 register-pair writes — the AAPCS bugs lived right here.
        ArmOp::I64Add { rdlo, rdhi, .. }
        | ArmOp::I64Sub { rdlo, rdhi, .. }
        | ArmOp::I64DivS { rdlo, rdhi, .. }
        | ArmOp::I64DivU { rdlo, rdhi, .. }
        | ArmOp::I64RemS { rdlo, rdhi, .. }
        | ArmOp::I64RemU { rdlo, rdhi, .. }
        | ArmOp::I64And { rdlo, rdhi, .. }
        | ArmOp::I64Or { rdlo, rdhi, .. }
        | ArmOp::I64Xor { rdlo, rdhi, .. } => vec![*rdlo, *rdhi],

        ArmOp::I64Mul { rd_lo, rd_hi, .. }
        | ArmOp::I64Shl { rd_lo, rd_hi, .. }
        | ArmOp::I64ShrS { rd_lo, rd_hi, .. }
        | ArmOp::I64ShrU { rd_lo, rd_hi, .. } => vec![*rd_lo, *rd_hi],

        // Cmp/Cmn/Str/Strb/Strh/Push/Pop/B/Bl/Bx/Blx/branches/labels/Nop/Udf/LocalSet/GlobalSet/etc.
        // — none of these modify a register-file value relevant to the
        // AAPCS-clobber check, so report no writes. This is conservative.
        _ => Vec::new(),
    }
}
