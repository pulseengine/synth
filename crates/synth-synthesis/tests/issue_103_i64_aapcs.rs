//! Regression test for issue #103: i64 ops hardcoded R0..R3, clobbering AAPCS
//! param registers before LocalGet reads them.
//!
//! The cargo-fuzz harness `i64_lowering_doesnt_clobber_params` (PR #100) caught
//! this for `I64SetCond` with the crash signature:
//!
//! ```text
//! AAPCS clobber: ARM instr at wasm line 1 writes param reg R0 before
//! LocalGet(0) at line 4.
//! Op: I64SetCond { rd: R0, rn_lo: R0, rn_hi: R1, rm_lo: R2, rm_hi: R3, cond: LT }
//! ```
//!
//! Root cause: in `instruction_selector::select_with_stack` (the `--no-optimize`
//! lowering path), the wildcard fallthrough handed every unhandled i64 op off
//! to `select_default`, which hardcodes R0:R1 / R2:R3 for the operand pairs and
//! R0 for the result. This is the same class of AAPCS-clobber bug that PR #86
//! fixed for `I64Const` in the optimizer path — applied to every other i64 op
//! that wasn't explicitly handled.
//!
//! Affected ops (all confirmed by audit):
//!   I64Eq, I64Ne, I64LtS, I64LtU, I64LeS, I64LeU, I64GtS, I64GtU, I64GeS, I64GeU
//!   I64Mul, I64DivS, I64DivU, I64RemS, I64RemU
//!   I64Rotl, I64Rotr
//!   I64Clz, I64Ctz, I64Popcnt
//!   I64Extend8S, I64Extend16S, I64Extend32S
//!   I32WrapI64
//!
//! The fix is to add explicit handlers in `select_with_stack` for each, using
//! the stack-tracked operand pairs and a fresh `alloc_temp_safe` /
//! `alloc_consecutive_pair` allocation for the destination.
//!
//! #1055 (RQ-61-FUZZWINDOW): the invariant here is strengthened from
//! "no write before the param's FIRST read" to "no write while the param is
//! LIVE" (before its LAST read) — see
//! `assert_no_param_clobber_while_param_live` and, for the executable record
//! of the old predicate's blindness plus the expansion-tier composition,
//! `crates/synth-backend/tests/issue_1055_reread_window.rs`.

use synth_synthesis::{ArmInstruction, ArmOp, InstructionSelector, Reg, RuleDatabase, WasmOp};

/// Compile the WASM op sequence through the `--no-optimize` lowering path
/// (`select_with_stack`) and return the emitted ARM ops. This is the path the
/// fuzz harness exercises.
fn compile_no_optimize(wasm_ops: &[WasmOp], num_params: u32) -> Vec<ArmInstruction> {
    let db = RuleDatabase::new();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector
        .select_with_stack(wasm_ops, num_params)
        .expect("select_with_stack should succeed for valid input")
}

/// Get the (write_set, read_set) of an ArmOp at the granularity needed for the
/// AAPCS-clobber check. write_set = registers the op writes; read_set =
/// registers the op reads. For multi-register pseudo-ops we conservatively
/// include all halves.
fn rw_sets(op: &ArmOp) -> (Vec<Reg>, Vec<Reg>) {
    match op {
        ArmOp::I64SetCond {
            rd,
            rn_lo,
            rn_hi,
            rm_lo,
            rm_hi,
            ..
        } => (vec![*rd], vec![*rn_lo, *rn_hi, *rm_lo, *rm_hi]),
        ArmOp::I64SetCondZ { rd, rn_lo, rn_hi } => (vec![*rd], vec![*rn_lo, *rn_hi]),
        ArmOp::I64Mul {
            rd_lo,
            rd_hi,
            rn_lo,
            rn_hi,
            rm_lo,
            rm_hi,
        } => (vec![*rd_lo, *rd_hi], vec![*rn_lo, *rn_hi, *rm_lo, *rm_hi]),
        ArmOp::I64DivS {
            rdlo,
            rdhi,
            rnlo,
            rnhi,
            rmlo,
            rmhi,
            ..
        }
        | ArmOp::I64DivU {
            rdlo,
            rdhi,
            rnlo,
            rnhi,
            rmlo,
            rmhi,
            ..
        }
        | ArmOp::I64RemS {
            rdlo,
            rdhi,
            rnlo,
            rnhi,
            rmlo,
            rmhi,
            ..
        }
        | ArmOp::I64RemU {
            rdlo,
            rdhi,
            rnlo,
            rnhi,
            rmlo,
            rmhi,
            ..
        } => (vec![*rdlo, *rdhi], vec![*rnlo, *rnhi, *rmlo, *rmhi]),
        ArmOp::I64Rotl {
            rdlo,
            rdhi,
            rnlo,
            rnhi,
            shift,
        }
        | ArmOp::I64Rotr {
            rdlo,
            rdhi,
            rnlo,
            rnhi,
            shift,
        } => (vec![*rdlo, *rdhi], vec![*rnlo, *rnhi, *shift]),
        ArmOp::I64Clz { rd, rnlo, rnhi }
        | ArmOp::I64Ctz { rd, rnlo, rnhi }
        | ArmOp::I64Popcnt { rd, rnlo, rnhi } => (vec![*rd], vec![*rnlo, *rnhi]),
        ArmOp::I64Extend8S { rdlo, rdhi, rnlo }
        | ArmOp::I64Extend16S { rdlo, rdhi, rnlo }
        | ArmOp::I64Extend32S { rdlo, rdhi, rnlo } => (vec![*rdlo, *rdhi], vec![*rnlo]),
        ArmOp::I32WrapI64 { rd, rnlo } => (vec![*rd], vec![*rnlo]),
        // For ops we don't specifically encode, be conservative: assume
        // nothing is read or written. The harness's purpose is to catch
        // I64-op clobber regressions; if other ops sneak in we miss them
        // here but they're outside this issue's scope.
        _ => (vec![], vec![]),
    }
}

/// Check that no ARM instruction writes an AAPCS param register R0..
/// R{num_params-1} WHILE THE PARAM IS STILL LIVE — i.e. anywhere strictly
/// before that param's LAST `LocalGet`.
///
/// #1055 (RQ-61-FUZZWINDOW): this predicate used to compute `earliest_read`
/// (the FIRST `LocalGet` per param) and flag only writes BEFORE it, which
/// exempted a write BETWEEN TWO READS by construction — exactly the shape of
/// the #1048 shift-amount clobber and the Clz/Ctz/Popcnt operand-hi clear
/// (#1054) that this harness family had itself named in #103's audit and
/// then could not see. The window now runs to the LAST read: any earlier
/// write to the param's home register is a clobber some later `LocalGet`
/// observes. Writes AFTER the last read stay exempt — the param is dead and
/// reusing its home is legitimate (flagging it would be a false positive;
/// liveness, not ordering, is the property).
///
/// Carve-out shared with the fuzz harness: an instruction whose SOURCE wasm
/// op is `LocalSet(p)`/`LocalTee(p)` may write R{p} — the wasm program
/// itself asked for the write, and the subsequent reads see the new value by
/// design.
///
/// Bounds (unchanged from the predecessor, stated rather than implied):
/// straight-line streams only (textual order = execution order; the fuzz
/// harness filters control flow), declared `ArmOp` destinations only (a
/// write hidden inside an encoder expansion is invisible at this tier — that
/// axis is owned by `synth_verify::validate_expansion`'s operand-preservation
/// clause (#1054) and the `issue_1055_reread_window.rs` composition test,
/// whose clause P replays the pre-#1054 bytes red), and i32 params only
/// (i64 params' pair homes are execution-pinned by
/// `scripts/repro/i64_operand_clobber_1048_differential.py`).
fn assert_no_param_clobber_while_param_live(
    wasm_ops: &[WasmOp],
    arm: &[ArmInstruction],
    num_params: u32,
) {
    let param_regs: Vec<Reg> = (0..num_params.min(4))
        .map(|i| match i {
            0 => Reg::R0,
            1 => Reg::R1,
            2 => Reg::R2,
            3 => Reg::R3,
            _ => unreachable!(),
        })
        .collect();

    // For each param i, find the LAST WASM line that does LocalGet(i).
    let mut last_read: std::collections::HashMap<u32, usize> = std::collections::HashMap::new();
    for (idx, op) in wasm_ops.iter().enumerate() {
        if let WasmOp::LocalGet(p) = op
            && *p < num_params
        {
            last_read.insert(*p, idx); // later lines overwrite earlier ones
        }
    }

    // Walk every emitted ARM instruction. For each instruction whose
    // `source_line` is earlier than the LAST LocalGet for some param,
    // assert it does NOT write that param's reg.
    for instr in arm {
        let Some(wasm_line) = instr.source_line else {
            // Prologue / epilogue ops without source_line are exempt.
            continue;
        };
        let (writes, _reads) = rw_sets(&instr.op);
        for (param_idx, &param_reg) in param_regs.iter().enumerate() {
            // If the param is never read there is no observer: every write
            // to its home is dead reuse, which is legal.
            let Some(last_read_line) = last_read.get(&(param_idx as u32)).copied() else {
                continue;
            };
            if wasm_line >= last_read_line {
                continue; // at or past the last read — the param is dead
            }
            // The wasm program's own write to the param local is intended.
            if matches!(
                wasm_ops.get(wasm_line),
                Some(WasmOp::LocalSet(p)) | Some(WasmOp::LocalTee(p))
                    if *p as usize == param_idx
            ) {
                continue;
            }
            if writes.contains(&param_reg) {
                panic!(
                    "AAPCS clobber: ARM instr at wasm line {wasm_line} writes \
                     param reg {:?} while LocalGet({param_idx}) at line {last_read_line} \
                     still reads it. Op: {:?}",
                    param_reg, instr.op
                );
            }
        }
    }
}

/// The exact reproducer from issue #103: an i64 LtS op runs before LocalGet(0)
/// reads the first param. Pre-fix, `select_default` emits I64SetCond with
/// `rd: R0, rn_lo: R0, rn_hi: R1, rm_lo: R2, rm_hi: R3`, clobbering R0.
#[test]
fn issue_103_i64_lt_s_does_not_clobber_r0() {
    let wasm = vec![
        WasmOp::I64Const(0),
        WasmOp::I64Const(1),
        WasmOp::I64LtS,
        WasmOp::Drop,
        WasmOp::LocalGet(0),
        WasmOp::Drop,
    ];
    let arm = compile_no_optimize(&wasm, /*num_params=*/ 1);
    assert_no_param_clobber_while_param_live(&wasm, &arm, 1);
}

/// Each entry: (label, wasm-op sequence that puts the i64 op's result on
/// the stack). For binary i64 ops we push two i64 consts; for unary i64 ops
/// one; for I32WrapI64 we push one i64 const. Shared by the op-before-read
/// matrix (#103) and the op-between-two-reads matrix (#1055).
fn i64_op_cases() -> Vec<(&'static str, Vec<WasmOp>)> {
    vec![
        (
            "I64Eq",
            vec![WasmOp::I64Const(0), WasmOp::I64Const(0), WasmOp::I64Eq],
        ),
        (
            "I64Ne",
            vec![WasmOp::I64Const(0), WasmOp::I64Const(1), WasmOp::I64Ne],
        ),
        (
            "I64LtS",
            vec![WasmOp::I64Const(0), WasmOp::I64Const(1), WasmOp::I64LtS],
        ),
        (
            "I64LtU",
            vec![WasmOp::I64Const(0), WasmOp::I64Const(1), WasmOp::I64LtU],
        ),
        (
            "I64LeS",
            vec![WasmOp::I64Const(0), WasmOp::I64Const(1), WasmOp::I64LeS],
        ),
        (
            "I64LeU",
            vec![WasmOp::I64Const(0), WasmOp::I64Const(1), WasmOp::I64LeU],
        ),
        (
            "I64GtS",
            vec![WasmOp::I64Const(1), WasmOp::I64Const(0), WasmOp::I64GtS],
        ),
        (
            "I64GtU",
            vec![WasmOp::I64Const(1), WasmOp::I64Const(0), WasmOp::I64GtU],
        ),
        (
            "I64GeS",
            vec![WasmOp::I64Const(1), WasmOp::I64Const(0), WasmOp::I64GeS],
        ),
        (
            "I64GeU",
            vec![WasmOp::I64Const(1), WasmOp::I64Const(0), WasmOp::I64GeU],
        ),
        (
            "I64Mul",
            vec![WasmOp::I64Const(2), WasmOp::I64Const(3), WasmOp::I64Mul],
        ),
        (
            "I64DivS",
            vec![WasmOp::I64Const(10), WasmOp::I64Const(3), WasmOp::I64DivS],
        ),
        (
            "I64DivU",
            vec![WasmOp::I64Const(10), WasmOp::I64Const(3), WasmOp::I64DivU],
        ),
        (
            "I64RemS",
            vec![WasmOp::I64Const(10), WasmOp::I64Const(3), WasmOp::I64RemS],
        ),
        (
            "I64RemU",
            vec![WasmOp::I64Const(10), WasmOp::I64Const(3), WasmOp::I64RemU],
        ),
        (
            "I64Rotl",
            vec![
                WasmOp::I64Const(0x123),
                WasmOp::I64Const(4),
                WasmOp::I64Rotl,
            ],
        ),
        (
            "I64Rotr",
            vec![
                WasmOp::I64Const(0x123),
                WasmOp::I64Const(4),
                WasmOp::I64Rotr,
            ],
        ),
        ("I64Clz", vec![WasmOp::I64Const(0x123), WasmOp::I64Clz]),
        ("I64Ctz", vec![WasmOp::I64Const(0x123), WasmOp::I64Ctz]),
        (
            "I64Popcnt",
            vec![WasmOp::I64Const(0x123), WasmOp::I64Popcnt],
        ),
        (
            "I64Extend8S",
            vec![WasmOp::I64Const(0x7f), WasmOp::I64Extend8S],
        ),
        (
            "I64Extend16S",
            vec![WasmOp::I64Const(0x7fff), WasmOp::I64Extend16S],
        ),
        (
            "I64Extend32S",
            vec![WasmOp::I64Const(0x7fff_ffff), WasmOp::I64Extend32S],
        ),
        (
            "I32WrapI64",
            vec![WasmOp::I64Const(0xdead_beef), WasmOp::I32WrapI64],
        ),
    ]
}

/// Class-level audit: every i64 op the fuzz harness flags should pass the
/// no-clobber invariant. We run each in isolation against a function with
/// `num_params=4` (worst case — all of R0..R3 are reserved AAPCS params).
#[test]
fn issue_103_all_i64_ops_preserve_params() {
    let cases = i64_op_cases();

    for num_params in [1u32, 2, 3, 4] {
        for (label, prefix) in &cases {
            // Build a function:
            //   <push i64 operands>
            //   <i64 op>     (computes result, may produce i32 or i64)
            //   drop         (may need to drop more than once for i64 result;
            //                 we use multiple Drops in a forgiving way below)
            //   local.get 0  (would surface a clobber of R0)
            //   drop
            //
            // We avoid trying to size Drop precisely — the select_with_stack
            // path will pop whatever's on the wasm stack and stop. The
            // AAPCS-clobber invariant only depends on what's BETWEEN line 0
            // and the LocalGet line.
            let mut wasm = prefix.clone();
            // Drop the result (could be i32 or i64; one Drop handles either
            // because select_with_stack's Drop only pops one stack slot).
            // For i64 producers we add a second Drop guarded by a stack-len
            // check — simpler to just push the local AFTER drops which the
            // unused stack contents won't perturb because all ops here
            // produce a deterministic stack delta.
            wasm.push(WasmOp::Drop);
            // For binary i64 ops that produce an i64 result we drop the hi
            // half too. Unary ops with i32 result (cmp / clz / etc.) leave
            // an empty stack after one Drop. To stay safe we always emit a
            // LocalGet just to compute the AAPCS invariant — extra stack
            // items don't change reg writes.
            wasm.push(WasmOp::LocalGet(0));
            wasm.push(WasmOp::Drop);

            let arm = compile_no_optimize(&wasm, num_params);
            // We use catch_unwind so we report which case failed, not just
            // the first.
            let result = std::panic::catch_unwind(|| {
                assert_no_param_clobber_while_param_live(&wasm, &arm, num_params);
            });
            if let Err(payload) = result {
                let msg = payload
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_else(|| "<unknown panic>".to_string());
                panic!("issue #103 regression for {label} with num_params={num_params}:\n{msg}");
            }
        }
    }
}

/// Sanity check: the I64Eqz op (already handled correctly in select_with_stack
/// pre-fix per PR #86's vicinity) still passes the invariant. Guards against
/// accidentally regressing the working case.
#[test]
fn i64_eqz_still_preserves_params() {
    let wasm = vec![
        WasmOp::I64Const(42),
        WasmOp::I64Eqz,
        WasmOp::Drop,
        WasmOp::LocalGet(0),
        WasmOp::Drop,
    ];
    for num_params in [1u32, 4] {
        let arm = compile_no_optimize(&wasm, num_params);
        assert_no_param_clobber_while_param_live(&wasm, &arm, num_params);
    }
}

/// #1055 (RQ-61-FUZZWINDOW): the BETWEEN-TWO-READS matrix. Every op from the
/// #103 audit runs with a `LocalGet(0)` BEFORE it and a `LocalGet(0)` AFTER
/// it — the read → op → re-read shape that the old first-read window
/// exempted by construction (#1048's exact posture). The strengthened
/// invariant must hold: nothing may write R0..R{num_params-1} anywhere
/// before the final read.
///
/// (Params 1..3 are deliberately NOT re-read: the probe for #1055 showed the
/// selector legitimately reuses a DEAD param's home for an i64 destination
/// pair — e.g. rd = R1:R2 with four params of which only param 0 is ever
/// read. The last-read window correctly ignores those; re-reading all four
/// params around i64 traffic makes the selector loud-decline on pair
/// exhaustion instead of clobbering, which the probe also confirmed.)
#[test]
fn issue_1055_all_i64_ops_preserve_params_between_reads() {
    let cases = i64_op_cases();

    for num_params in [1u32, 2, 3, 4] {
        for (label, op_seq) in &cases {
            let mut wasm = vec![WasmOp::LocalGet(0), WasmOp::Drop]; // first read
            wasm.extend(op_seq.iter().cloned()); // the op under test
            wasm.push(WasmOp::Drop);
            wasm.push(WasmOp::LocalGet(0)); // re-read — the observer
            wasm.push(WasmOp::Drop);

            let arm = compile_no_optimize(&wasm, num_params);
            let result = std::panic::catch_unwind(|| {
                assert_no_param_clobber_while_param_live(&wasm, &arm, num_params);
            });
            if let Err(payload) = result {
                let msg = payload
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_else(|| "<unknown panic>".to_string());
                panic!(
                    "issue #1055 between-reads regression for {label} with \
                     num_params={num_params}:\n{msg}"
                );
            }
        }
    }
}
