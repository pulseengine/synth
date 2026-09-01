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
//! The invariant a correct lowering must satisfy (#1055, RQ-61-FUZZWINDOW —
//! strengthened from "before the FIRST read" to "while the param is LIVE"):
//!
//!   *While a later `LocalGet(p)` can still observe parameter
//!   `p ∈ [0,num_params)` — i.e. anywhere strictly before `p`'s LAST
//!   `LocalGet` — no ARM instruction may write to `R{p}` (unless the wasm
//!   program itself asked for the write via `LocalSet(p)`/`LocalTee(p)`).*
//!
//! The predecessor predicate computed `earliest_read` (the FIRST `LocalGet`)
//! and flagged only writes BEFORE it, which exempted a write BETWEEN TWO
//! READS by construction — exactly the #1048 shift-amount clobber and the
//! Clz/Ctz/Popcnt operand-hi clear (#1054), defects this harness's own #103
//! audit had named and the window could not see. Writes AFTER the last read
//! stay exempt: the param is dead and reusing its home register is
//! legitimate (the selector really does it — flagging it would be a false
//! positive; the property is liveness, not ordering).
//!
//! Bounds, stated: declared `ArmOp` destinations only — a write hidden
//! inside an encoder expansion is invisible at this tier no matter how the
//! window is phrased. That axis is owned by the #1054 operand-preservation
//! clause of `synth_verify::validate_expansion` (which rejects the pre-fix
//! bytes) and by `crates/synth-backend/tests/issue_1055_reread_window.rs`,
//! which composes that clause with this window over the same re-read shapes.
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

    // Build a wasm program shape: the arbitrary ops first, then a mandatory
    // `LocalGet(p)` for each param p.
    //
    // The trailing LocalGets define the WINDOW END: they are each param's
    // last (often only) read, so every param is live across the entire
    // middle and any write to a param's home register anywhere in the
    // middle is a flaggable clobber. When the arbitrary middle contains its
    // own `LocalGet(p)` (the generator emits them), the program is the
    // read -> op -> re-read shape of #1048 — the exact posture the old
    // first-read window exempted.
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

    // For each param p, find the wasm index of its LAST LocalGet (#1055:
    // the window runs to the last read, not the first).
    let mut last_read_wasm_idx: [Option<usize>; 4] = [None; 4];
    for (idx, op) in wasm_ops.iter().enumerate() {
        if let WasmOp::LocalGet(p) = op {
            let p = *p as usize;
            if p < 4 {
                last_read_wasm_idx[p] = Some(idx); // later reads overwrite
            }
        }
    }

    // For each param p, walk the lowered ARM instructions in order. Any
    // instruction whose `source_line` is < last_read_wasm_idx[p] AND
    // writes R{p} is a clobber — UNLESS the source wasm op is
    // `LocalSet(p)` or `LocalTee(p)`, in which case the write to R{p}
    // is wasm-program-intended (the user explicitly asked to store into
    // param-local p). Without this carve-out the harness false-positives
    // on every `LocalSet(p); ...; LocalGet(p)` pattern, since the
    // LocalSet legitimately emits a Mov writing R{p}.
    for (p, &last_read_idx) in last_read_wasm_idx
        .iter()
        .take(num_params as usize)
        .enumerate()
    {
        let last_read = match last_read_idx {
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
        for (instr_idx, instr) in arm_instrs.iter().enumerate() {
            // The function prologue (Push, Sub from SP) has source_line None.
            // We only care about instructions that flow from user-level wasm ops.
            let line = match instr.source_line {
                Some(l) => l,
                None => continue,
            };
            if line >= last_read {
                continue; // At or past the param's LAST read — it is dead,
                // and home-register reuse past that point is legitimate.
            }
            // Skip the wasm-program-intended write: LocalSet(p) and
            // LocalTee(p) MAY semantically write R{p} (it's where the
            // wasm local lives). The compiler is just honoring the wasm
            // program. A real compiler bug here would be a write from a
            // different wasm op (e.g., I32WrapI64 hardcoding R0 as its
            // destination — the bug PR #111 fixed).
            if let Some(WasmOp::LocalSet(p_op)) | Some(WasmOp::LocalTee(p_op)) = wasm_ops.get(line)
                && *p_op as usize == p
            {
                continue;
            }
            // Skip return-value-placement dead stores: when the very next ARM
            // op also writes R{p}, the current write's value is dead and
            // overwritten before any observer can read it. This pattern
            // appears in the function-final return-value sequence where the
            // selector emits e.g. `Movw R0, 0` followed by `Mov R0, R8` to
            // place an i32 return value (the Movw is a redundant zero-init
            // that the second Mov immediately overwrites). The lowering is
            // suboptimal — see issue #112 option (a) for a peephole fix —
            // but the param IS already preserved at this point (the LocalGet
            // we're protecting reads from R{p} earlier in the function), so
            // this is not a real AAPCS clobber.
            //
            // Soundness note: this carve-out is safe because:
            //  1. The next-op-overwrites-same-reg condition is *local* — we
            //     don't carve out arbitrary writes, only ones whose result is
            //     provably dead at the next instruction.
            //  2. If a real bug were to emit `Movw R0, _; Mov R0, R8` in the
            //     middle of computation (not return-value placement), the
            //     param's value is already gone anyway — both writes overwrite
            //     it. The carve-out doesn't *hide* a clobber, it just suppresses
            //     a duplicate report. The single Mov R0, R8 still gets flagged
            //     if it precedes any LocalGet(0) — except its own next op is
            //     usually Pop, which doesn't write R0.
            if let Some(next) = arm_instrs.get(instr_idx + 1)
                && writes(&next.op).contains(&param_reg)
            {
                continue;
            }
            for w in writes(&instr.op) {
                assert_ne!(
                    w,
                    param_reg,
                    "AAPCS clobber: ARM instr at wasm line {line} writes param reg {param_reg:?} \
                     while LocalGet({p}) at line {last_read} still reads it. Op: {:?}. Sequence: {:?}",
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

        // #1055: the i64 unary / comparison pseudo-ops were missing from
        // this table entirely (they fell through to "writes nothing") —
        // the harness could not see a hardcoded destination on the very
        // ops #103's audit named. Single-register destinations:
        ArmOp::I64Clz { rd, .. }
        | ArmOp::I64Ctz { rd, .. }
        | ArmOp::I64Popcnt { rd, .. }
        | ArmOp::I64Eqz { rd, .. }
        | ArmOp::I64Eq { rd, .. }
        | ArmOp::I64Ne { rd, .. }
        | ArmOp::I64LtS { rd, .. }
        | ArmOp::I64LtU { rd, .. }
        | ArmOp::I64LeS { rd, .. }
        | ArmOp::I64LeU { rd, .. }
        | ArmOp::I64GtS { rd, .. }
        | ArmOp::I64GtU { rd, .. }
        | ArmOp::I64GeS { rd, .. }
        | ArmOp::I64GeU { rd, .. }
        | ArmOp::I32WrapI64 { rd, .. } => vec![*rd],

        // #1055: pair destinations that were also missing.
        ArmOp::I64Rotl { rdlo, rdhi, .. }
        | ArmOp::I64Rotr { rdlo, rdhi, .. }
        | ArmOp::I64Const { rdlo, rdhi, .. }
        | ArmOp::I64Ldr { rdlo, rdhi, .. }
        | ArmOp::I64ExtendI32S { rdlo, rdhi, .. }
        | ArmOp::I64ExtendI32U { rdlo, rdhi, .. }
        | ArmOp::I64Extend8S { rdlo, rdhi, .. }
        | ArmOp::I64Extend16S { rdlo, rdhi, .. }
        | ArmOp::I64Extend32S { rdlo, rdhi, .. } => vec![*rdlo, *rdhi],

        ArmOp::Umull { rdlo, rdhi, .. } => vec![*rdlo, *rdhi],
        ArmOp::Uxtb { rd, .. } | ArmOp::Uxth { rd, .. } | ArmOp::Mla { rd, .. } => vec![*rd],

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
