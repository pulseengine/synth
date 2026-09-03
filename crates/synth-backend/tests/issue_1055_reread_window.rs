//! #1055 (RQ-61-FUZZWINDOW) — the param-clobber window, strengthened from
//! "before FIRST read" to "while the param is LIVE", and composed with the
//! #1054 expansion-level operand-preservation oracle.
//!
//! ## The hole this file records and closes
//!
//! `i64_lowering_doesnt_clobber_params` (the PR #100 cargo-fuzz harness) and
//! its companion `assert_no_param_clobber_before_localget`
//! (`crates/synth-synthesis/tests/issue_103_i64_aapcs.rs`) computed
//! `earliest_read` — the FIRST `LocalGet` per param — and flagged only writes
//! BEFORE it. A write BETWEEN TWO READS was exempt by construction:
//!
//! ```wat
//! local.get $amt   ;; earliest_read for $amt is HERE
//! i64.shl          ;; expansion clobbers $amt's home high register — AFTER
//! local.get $amt   ;; reads back a mangled value
//! ```
//!
//! That window is exactly the shape of #1048 (i64 variable shifts destroying
//! the amount pair) and the `I64Clz`/`I64Ctz`/`I64Popcnt` operand-hi clear
//! fixed alongside it (PR #1054) — executed miscompiles the harness had
//! itself named (#103's audit) and could not see.
//!
//! ## The strengthened invariant — stated precisely
//!
//! Two clauses, each owning one tier of the defect:
//!
//! **(W) WINDOW, selector tier.** For every register-homed param `p` with
//! home register(s) `H(p)` and LAST textual `LocalGet(p)` at wasm index
//! `last`: no ARM instruction with `source_line = Some(L)`, `L < last`, may
//! carry a DECLARED write (its `ArmOp` destination fields) to any register in
//! `H(p)` — unless the wasm op at `L` is `LocalSet(p)`/`LocalTee(p)` (the
//! wasm program itself asked for the write).
//!
//! **(P) PRESERVATION, expansion tier.** Every covered i64 pseudo-op in the
//! stream must certify OPERAND PRESERVATION over its emitted bytes
//! (`synth_verify::validate_expansion`, #1054): the expansion writes nothing
//! but its declared result registers and R12 (encoder scratch, never
//! allocatable, never a param home — #212). Clause P is what makes the
//! DECLARED write set in clause W sound for the machine: without it, a
//! write hidden inside an encoder expansion (the actual #1048/#1054
//! mechanism) is invisible at the `ArmOp` tier no matter how the window is
//! phrased.
//!
//! ## What the invariant still does NOT cover — honest bounds
//!
//! * Writes AFTER the last textual read: legitimate reuse of a dead param's
//!   home (the probe for this issue showed the selector hands out R1:R2 for
//!   an i64 destination when params 1..2 are never read again — correct, and
//!   flagging it would be a false positive; that is why the window ends at
//!   the LAST read, not at function end).
//! * Control flow: with branches, textual order is not execution order (a
//!   read inside a loop can execute after a textually later write). The fuzz
//!   harness filters unbalanced control flow; this file's fixtures are
//!   straight-line. A CF-aware window needs real liveness analysis
//!   (`liveness::reg_effect` deliberately returns `None` for the i64-pair
//!   pseudo-ops precisely so nothing consumes an unmodeled effect; extending
//!   it changes optimization reachability, i.e. emitted bytes, and is out of
//!   scope for a checker fix).
//! * `ArmOp` variants missing from `declared_writes`: conservative —
//!   a missing variant declares nothing, giving false NEGATIVES only, never
//!   false positives (the fuzz harness's stated soundness floor).
//! * Pseudo-ops outside `CERTIFIABLE` (notably the i64 div/rem family, whose
//!   long-division loops the expansion validator holds out loudly): clause P
//!   does not run for them; their operand preservation is execution-pinned
//!   by `scripts/repro/i64_operand_clobber_1048_differential.py` (CI-wired,
//!   105 emulations, all three backend legs).
//! * The optimized path (`optimizer_bridge::ir_to_arm`) — unchanged scope;
//!   this checker targets `select_with_stack`, same as its predecessors.
//!
//! ## Red-first provenance
//!
//! The ops themselves were fixed by PR #1054 before this issue was filed, so
//! the blindness is demonstrated STRUCTURALLY (the ledger variant permitted
//! by RQ-61-FUZZWINDOW): `blindness_record_*` reconstructs the legacy
//! first-read predicate verbatim and shows it ACCEPTS a stream that writes a
//! live param home between two reads, while the strengthened clause W
//! rejects the same stream. The `pre_1054_*` tests replay the REAL pre-fix
//! encoder bytes — dumped from commit 1fe1ad22, the parent of #1054's merge,
//! for the exact register assignments today's selector emits for the #1048
//! re-read shapes — through clause P, which rejects both. Execution
//! ground-truth for the same shapes (the mangled re-read values) is the
//! #1054 red transcript and the CI-wired differential named above.

use synth_backend::ArmEncoder;
use synth_synthesis::{ArmInstruction, ArmOp, InstructionSelector, Reg, RuleDatabase, WasmOp};
use synth_verify::{ExpansionError, validate_expansion, with_verification_context};

// ===========================================================================
// The strengthened checker
// ===========================================================================

/// A register-homed parameter: wasm local index -> AAPCS home register(s).
/// Spelled out per fixture (the homes for a fixed signature are AAPCS-
/// determined constants) rather than re-deriving them from a second copy of
/// `aapcs_param_layout` — the checker takes the contract as stated input.
struct ParamHome {
    idx: u32,
    regs: &'static [Reg],
}

/// Declared (ArmOp-tier) write set. Checker-local table, conservative in the
/// stated direction: an unlisted variant declares nothing — false negatives
/// possible, false positives impossible. Clause P is what entitles this tier
/// to trust the declaration for the covered i64 pseudo-ops.
fn declared_writes(op: &ArmOp) -> Vec<Reg> {
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
        | ArmOp::I64Clz { rd, .. }
        | ArmOp::I64Ctz { rd, .. }
        | ArmOp::I64Popcnt { rd, .. }
        | ArmOp::I32WrapI64 { rd, .. } => vec![*rd],

        ArmOp::I64Add { rdlo, rdhi, .. }
        | ArmOp::I64Sub { rdlo, rdhi, .. }
        | ArmOp::I64DivS { rdlo, rdhi, .. }
        | ArmOp::I64DivU { rdlo, rdhi, .. }
        | ArmOp::I64RemS { rdlo, rdhi, .. }
        | ArmOp::I64RemU { rdlo, rdhi, .. }
        | ArmOp::I64And { rdlo, rdhi, .. }
        | ArmOp::I64Or { rdlo, rdhi, .. }
        | ArmOp::I64Xor { rdlo, rdhi, .. }
        | ArmOp::I64Rotl { rdlo, rdhi, .. }
        | ArmOp::I64Rotr { rdlo, rdhi, .. }
        | ArmOp::I64Const { rdlo, rdhi, .. }
        | ArmOp::I64Ldr { rdlo, rdhi, .. }
        | ArmOp::I64ExtendI32S { rdlo, rdhi, .. }
        | ArmOp::I64ExtendI32U { rdlo, rdhi, .. }
        | ArmOp::I64Extend8S { rdlo, rdhi, .. }
        | ArmOp::I64Extend16S { rdlo, rdhi, .. }
        | ArmOp::I64Extend32S { rdlo, rdhi, .. } => vec![*rdlo, *rdhi],

        ArmOp::I64Mul { rd_lo, rd_hi, .. }
        | ArmOp::I64Shl { rd_lo, rd_hi, .. }
        | ArmOp::I64ShrS { rd_lo, rd_hi, .. }
        | ArmOp::I64ShrU { rd_lo, rd_hi, .. } => vec![*rd_lo, *rd_hi],

        ArmOp::Umull { rdlo, rdhi, .. } => vec![*rdlo, *rdhi],
        ArmOp::Pop { regs } => regs.clone(),

        // Cmp/Cmn/Str*/Push/branches/labels/Nop/Udf/etc.: no GP destination.
        _ => Vec::new(),
    }
}

/// Clause P surface: pseudo-ops whose emitted expansion the #1054 validator
/// can certify (branch-free / forward-branch families). The i64 div/rem
/// family is EXCLUDED here because its long-division loops are held out by
/// the validator (loud decode error, never a silent accept) — see the module
/// docs for where its operand preservation is pinned instead.
fn is_certifiable(op: &ArmOp) -> bool {
    matches!(
        op,
        ArmOp::I64Mul { .. }
            | ArmOp::I64SetCond { .. }
            | ArmOp::I64SetCondZ { .. }
            | ArmOp::I64Clz { .. }
            | ArmOp::I64Ctz { .. }
            | ArmOp::I64Popcnt { .. }
            | ArmOp::I64Shl { .. }
            | ArmOp::I64ShrU { .. }
            | ArmOp::I64ShrS { .. }
            | ArmOp::I64Rotl { .. }
            | ArmOp::I64Rotr { .. }
    )
}

/// The #1055 strengthened invariant. See the module docs for the precise
/// statement and bounds. `bytes_for(i, op)` supplies the machine bytes for
/// instruction `i` (tests pass the shipped encoder; the potency tests splice
/// the banked pre-#1054 bytes). Returns the number of clause-P
/// certifications performed, so callers can pin a non-vacuity floor.
fn assert_no_param_clobber_while_live(
    wasm_ops: &[WasmOp],
    arm: &[ArmInstruction],
    param_homes: &[ParamHome],
    bytes_for: &dyn Fn(usize, &ArmOp) -> Vec<u8>,
) -> usize {
    // ---- Clause W: no declared write into a live param home ---------------
    for home in param_homes {
        let Some(last_read) = wasm_ops
            .iter()
            .rposition(|op| matches!(op, WasmOp::LocalGet(p) if *p == home.idx))
        else {
            continue; // never read — every write to its home is dead reuse
        };
        for instr in arm {
            let Some(line) = instr.source_line else {
                continue; // prologue / epilogue / return-value placement
            };
            if line >= last_read {
                continue; // at or past the last read — the param is dead
            }
            if matches!(
                wasm_ops.get(line),
                Some(WasmOp::LocalSet(p)) | Some(WasmOp::LocalTee(p)) if *p == home.idx
            ) {
                continue; // wasm-program-intended write to the param local
            }
            for w in declared_writes(&instr.op) {
                assert!(
                    !home.regs.contains(&w),
                    "clause W: instr from wasm line {line} declares a write to \
                     {w:?} — param {}'s home — while a later LocalGet({}) at \
                     line {last_read} still reads it. Op: {:?}",
                    home.idx,
                    home.idx,
                    instr.op,
                );
            }
        }
    }

    // ---- Clause P: emitted bytes preserve every non-result operand --------
    // Unconditional over the stream (not window-gated): a clobbered operand
    // register is a live value regardless of whether it is a param home.
    let mut certified = 0;
    for (i, instr) in arm.iter().enumerate() {
        if !is_certifiable(&instr.op) {
            continue;
        }
        let line = instr
            .source_line
            .unwrap_or_else(|| panic!("certifiable pseudo-op without source_line: {:?}", instr.op));
        let wasm = &wasm_ops[line];
        let code = bytes_for(i, &instr.op);
        match validate_expansion(wasm, &instr.op, &code) {
            Ok(_) => certified += 1,
            Err(e) => panic!(
                "clause P: expansion for {wasm:?} / {:?} (wasm line {line}) \
                 failed operand-preservation certification: {e}",
                instr.op
            ),
        }
    }
    certified
}

/// The LEGACY predicate, reconstructed verbatim from
/// `assert_no_param_clobber_before_localget` (issue_103_i64_aapcs.rs as of
/// #1055): first-read window over the same declared write sets. Kept ONLY as
/// the negative control for the blindness record below — it must ACCEPT the
/// stream the strengthened clause W rejects, or the strengthening claim is
/// hollow.
fn legacy_first_read_window_accepts(
    wasm_ops: &[WasmOp],
    arm: &[ArmInstruction],
    param_homes: &[ParamHome],
) -> bool {
    for home in param_homes {
        let Some(first_read) = wasm_ops
            .iter()
            .position(|op| matches!(op, WasmOp::LocalGet(p) if *p == home.idx))
        else {
            continue;
        };
        for instr in arm {
            let Some(line) = instr.source_line else {
                continue;
            };
            if line >= first_read {
                continue;
            }
            if declared_writes(&instr.op)
                .iter()
                .any(|w| home.regs.contains(w))
            {
                return false;
            }
        }
    }
    true
}

// ===========================================================================
// Fixtures
// ===========================================================================

fn lower(wasm: &[WasmOp], num_params: u32, params_i64: Vec<bool>) -> Vec<ArmInstruction> {
    let db = RuleDatabase::new();
    let mut sel = InstructionSelector::new(db.rules().to_vec());
    sel.set_params_i64(params_i64);
    sel.select_with_stack(wasm, num_params)
        .expect("fixture must lower")
}

fn shipped_bytes(_i: usize, op: &ArmOp) -> Vec<u8> {
    ArmEncoder::new_thumb2()
        .encode(op)
        .expect("shipped encoder must encode the pseudo-op")
}

/// The #1048 repro shape: `(param $x i64) (param $amt i64) (result i64)`
/// `x shl amt`, then the amount is read AGAIN. Homes: $x = R0:R1,
/// $amt = R2:R3 (AAPCS even-aligned pairs).
fn shl_reread_wasm(shift: WasmOp) -> Vec<WasmOp> {
    vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        shift,
        WasmOp::LocalGet(1), // re-read of the amount — AFTER the expansion ran
        WasmOp::I64Add,
    ]
}

/// The #1054 bit-count repro shape: `(param $x i64) (result i64)` — count is
/// computed and dropped, then $x is read AGAIN (returned). Home: R0:R1.
fn bitcount_reread_wasm(op: WasmOp) -> Vec<WasmOp> {
    vec![
        WasmOp::LocalGet(0),
        op,
        WasmOp::Drop,
        WasmOp::LocalGet(0), // re-read of the operand — AFTER the expansion
    ]
}

const I64_PAIR_HOMES: &[ParamHome] = &[
    ParamHome {
        idx: 0,
        regs: &[Reg::R0, Reg::R1],
    },
    ParamHome {
        idx: 1,
        regs: &[Reg::R2, Reg::R3],
    },
];

const ONE_I64_HOME: &[ParamHome] = &[ParamHome {
    idx: 0,
    regs: &[Reg::R0, Reg::R1],
}];

// ===========================================================================
// 1. The blindness record — executable, not prose
// ===========================================================================

/// The stream is the selector-tier IMAGE of #1048: a declared write into a
/// live param home BETWEEN two reads. The legacy first-read predicate
/// accepts it BY CONSTRUCTION (there is no instruction before the first
/// read); the strengthened clause W rejects it. Both facts are asserted, so
/// the hole and its closure are one committed artifact.
///
/// (Why the write is DECLARED here: the live #1048/#1054 instances hid the
/// write inside the encoder expansion, one tier below any ArmOp-level
/// predicate — first-read or last-read. Clause P is the tier that sees
/// those; the `pre_1054_*` tests below replay them. Post-#1054, an
/// expansion write that is not declared fails clause P, so the declared
/// tier is exactly where a surviving between-reads clobber would appear.)
#[test]
fn blindness_record_first_read_window_accepts_between_reads_clobber() {
    // (param $a i32 ... $d i32): four i32 params homed R0..R3.
    let wasm = vec![
        WasmOp::LocalGet(3), // first (and earliest) read of param 3
        WasmOp::Drop,
        WasmOp::I32Const(0), // some op whose lowering clobbers R3...
        WasmOp::LocalGet(3), // ...and param 3 is read AGAIN
        WasmOp::Drop,
    ];
    let homes: &[ParamHome] = &[ParamHome {
        idx: 3,
        regs: &[Reg::R3],
    }];
    let arm = vec![
        ArmInstruction {
            op: ArmOp::Mov {
                rd: Reg::R4,
                op2: synth_synthesis::rules::Operand2::Reg(Reg::R3),
            },
            source_line: Some(0),
        },
        // The clobber: a declared write to R3 at line 2 — strictly BETWEEN
        // the reads at lines 0 and 3.
        ArmInstruction {
            op: ArmOp::Movw {
                rd: Reg::R3,
                imm16: 0,
            },
            source_line: Some(2),
        },
        ArmInstruction {
            op: ArmOp::Mov {
                rd: Reg::R5,
                op2: synth_synthesis::rules::Operand2::Reg(Reg::R3),
            },
            source_line: Some(3),
        },
    ];

    // Fact (a): the legacy first-read window ACCEPTS the clobbering stream.
    assert!(
        legacy_first_read_window_accepts(&wasm, &arm, homes),
        "the legacy predicate was supposed to be blind to this stream — if \
         it now rejects it, the blindness record is stale; update it"
    );

    // Fact (b): the strengthened clause W REJECTS the same stream.
    let err = std::panic::catch_unwind(|| {
        assert_no_param_clobber_while_live(&wasm, &arm, homes, &shipped_bytes);
    })
    .expect_err("clause W must reject a declared write into a live param home");
    let msg = panic_msg(err);
    assert!(
        msg.contains("clause W") && msg.contains("R3"),
        "wrong rejection: {msg}"
    );
}

// ===========================================================================
// 2. Green on main — the strengthened invariant holds for the re-read shapes
// ===========================================================================

/// Every #1048/#1054 re-read shape, lowered by today's selector and encoded
/// by today's encoder, satisfies BOTH clauses. A floor on the number of
/// clause-P certifications pins the test against going vacuous (the v0.59
/// lesson: a checker must be shown to have done work, not just to have
/// not failed).
#[test]
fn reread_shapes_hold_on_shipped_encoder() {
    with_verification_context(|| {
        let mut certified = 0;

        // The three variable shifts — the #1048 class itself.
        for shift in [WasmOp::I64Shl, WasmOp::I64ShrU, WasmOp::I64ShrS] {
            let wasm = shl_reread_wasm(shift);
            let arm = lower(&wasm, 2, vec![true, true]);
            certified +=
                assert_no_param_clobber_while_live(&wasm, &arm, I64_PAIR_HOMES, &shipped_bytes);
        }

        // The three bit-counts — the #1054 sibling class.
        for op in [WasmOp::I64Clz, WasmOp::I64Ctz, WasmOp::I64Popcnt] {
            let wasm = bitcount_reread_wasm(op);
            let arm = lower(&wasm, 1, vec![true]);
            certified +=
                assert_no_param_clobber_while_live(&wasm, &arm, ONE_I64_HOME, &shipped_bytes);
        }

        // Rotates and multiply (the #610 wrapper / branch-free families) in
        // the same operand-re-read posture.
        for op in [WasmOp::I64Rotl, WasmOp::I64Rotr, WasmOp::I64Mul] {
            let wasm = shl_reread_wasm(op);
            let arm = lower(&wasm, 2, vec![true, true]);
            certified +=
                assert_no_param_clobber_while_live(&wasm, &arm, I64_PAIR_HOMES, &shipped_bytes);
        }

        // A comparison (I64SetCond) between two reads of its own operand.
        {
            let wasm = vec![
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I64LtS,
                WasmOp::Drop,
                WasmOp::LocalGet(1),
                WasmOp::Drop,
            ];
            let arm = lower(&wasm, 2, vec![true, true]);
            certified +=
                assert_no_param_clobber_while_live(&wasm, &arm, I64_PAIR_HOMES, &shipped_bytes);
        }

        // i32 params with i64 traffic between two reads (the fuzz harness's
        // own program family).
        {
            let wasm = vec![
                WasmOp::LocalGet(0),
                WasmOp::Drop,
                WasmOp::I64Const(5),
                WasmOp::I64Const(3),
                WasmOp::I64Shl,
                WasmOp::Drop,
                WasmOp::LocalGet(0),
            ];
            let arm = lower(&wasm, 1, vec![]);
            let homes: &[ParamHome] = &[ParamHome {
                idx: 0,
                regs: &[Reg::R0],
            }];
            certified += assert_no_param_clobber_while_live(&wasm, &arm, homes, &shipped_bytes);
        }

        // LocalSet carve-out: the wasm program itself overwrites param 0
        // between two reads — intended, must stay green.
        {
            let wasm = vec![
                WasmOp::LocalGet(0),
                WasmOp::Drop,
                WasmOp::I32Const(5),
                WasmOp::LocalSet(0),
                WasmOp::LocalGet(0),
                WasmOp::Drop,
            ];
            let arm = lower(&wasm, 1, vec![]);
            let homes: &[ParamHome] = &[ParamHome {
                idx: 0,
                regs: &[Reg::R0],
            }];
            certified += assert_no_param_clobber_while_live(&wasm, &arm, homes, &shipped_bytes);
        }

        // Non-vacuity floor: the eleven certifiable pseudo-ops above (3
        // shifts + 3 bit-counts + 2 rotates + 1 mul + 1 setcond + 1
        // shl-from-consts) must all have gone through clause P.
        assert!(
            certified >= 11,
            "clause P certified only {certified} expansions — the floor is 11; \
             the checker went vacuous or a fixture stopped emitting its pseudo-op"
        );
    });
}

// ===========================================================================
// 3. Potency — the strengthened checker catches the historical instances
// ===========================================================================

/// PRE-#1054 encoder bytes, dumped from commit 1fe1ad22 (the parent of PR
/// #1054's merge) with `ArmEncoder::new_thumb2().encode(..)` for the EXACT
/// register assignments today's selector emits for the re-read shapes above.
/// Halfword form, little-endian bytes.
fn halfwords(hws: &[u16]) -> Vec<u8> {
    hws.iter().flat_map(|h| h.to_le_bytes()).collect()
}

/// I64Shl { rd:(R4,R5), rn:(R0,R1), rm:(R2,R3) } as v0.58 shipped it:
/// opens `AND.W R2, R2, #63` (amount masked IN PLACE) and scratches
/// `SUBS.W R3, R2, #32` through the amount's home high register.
fn pre_1054_shl_bytes() -> Vec<u8> {
    halfwords(&[
        0xF002, 0x023F, // AND.W  R2, R2, #63   — operand clobber #1
        0xF1B2, 0x0320, // SUBS.W R3, R2, #32   — operand clobber #2
        0xD50A, //         BPL    .large
        0xF1C2, 0x0320, // RSB.W  R3, R2, #32
        0xFA20, 0xF303, // LSR.W  R3, R0, R3
        0xFA01, 0xF502, // LSL.W  R5, R1, R2
        0xEA45, 0x0503, // ORR.W  R5, R5, R3
        0xFA00, 0xF402, // LSL.W  R4, R0, R2
        0xE002, //         B      .done
        0xFA00, 0xF503, // .large: LSL.W R5, R0, R3
        0x2400, //         MOVS   R4, #0
    ])
}

/// I64Clz { rd: R2, rn:(R0,R1) } as v0.58 shipped it: the trailing
/// `MOVS R1, #0` zeroes the OPERAND's home high register (the write that
/// wiped clz_reread's hi limb — `clz_reread(0xDEADBEEF00000001)` returned
/// 0x1 on the pre-fix binary, all three backend legs).
fn pre_1054_clz_bytes() -> Vec<u8> {
    halfwords(&[
        0xF1B1, 0x0F00, // CMP.W R1, #0
        0xD003, //         BEQ .hi_zero
        0xFAB1, 0xF281, // CLZ.W R2, R1
        0xE004, //         B .done
        0xBF00, //         NOP
        0xFAB0, 0xF280, // .hi_zero: CLZ.W R2, R0
        0xF102, 0x0220, // ADD.W R2, R2, #32
        0x2100, //         .done: MOVS R1, #0  — operand hi DESTROYED
    ])
}

/// Splice `bytes` in for the single instruction matching `pred`; shipped
/// encoder for everything else. Panics if the stream does not contain
/// exactly one match — the potency test must not silently test nothing.
fn splice_bytes<'a>(
    arm: &[ArmInstruction],
    pred: fn(&ArmOp) -> bool,
    bytes: &'a [u8],
) -> impl Fn(usize, &ArmOp) -> Vec<u8> + 'a {
    let matches: Vec<usize> = arm
        .iter()
        .enumerate()
        .filter(|(_, ins)| pred(&ins.op))
        .map(|(i, _)| i)
        .collect();
    assert_eq!(
        matches.len(),
        1,
        "splice target must appear exactly once, found {matches:?}"
    );
    let target = matches[0];
    move |i, op| {
        if i == target {
            bytes.to_vec()
        } else {
            shipped_bytes(i, op)
        }
    }
}

/// #1048 caught: the shl_reread stream with the REAL pre-#1054 I64Shl bytes
/// spliced in fails clause P with a counterexample. The same stream with the
/// shipped bytes is green (asserted by `reread_shapes_hold_on_shipped_encoder`),
/// so the red is attributable to the pre-fix bytes alone.
#[test]
fn pre_1054_shl_amount_clobber_caught() {
    with_verification_context(|| {
        let wasm = shl_reread_wasm(WasmOp::I64Shl);
        let arm = lower(&wasm, 2, vec![true, true]);

        // Pin the register assignment the banked bytes were dumped for. If
        // the selector's allocation ever drifts, fail HERE with a re-bank
        // instruction — not downstream with a wrong-reason counterexample.
        let shl = arm
            .iter()
            .find(|ins| matches!(ins.op, ArmOp::I64Shl { .. }))
            .expect("stream must contain the I64Shl pseudo-op");
        assert_eq!(
            shl.op,
            ArmOp::I64Shl {
                rd_lo: Reg::R4,
                rd_hi: Reg::R5,
                rn_lo: Reg::R0,
                rn_hi: Reg::R1,
                rm_lo: Reg::R2,
                rm_hi: Reg::R3,
            },
            "selector register assignment drifted — re-dump pre_1054_shl_bytes \
             from commit 1fe1ad22 for the new assignment"
        );

        let bytes = pre_1054_shl_bytes();
        let bytes_for = splice_bytes(&arm, |op| matches!(op, ArmOp::I64Shl { .. }), &bytes);
        let err = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            assert_no_param_clobber_while_live(&wasm, &arm, I64_PAIR_HOMES, &bytes_for);
        }))
        .expect_err("pre-#1054 shl bytes must fail the strengthened checker");
        let msg = panic_msg(err);
        assert!(
            msg.contains("clause P") && msg.contains("counterexample"),
            "wrong rejection: {msg}"
        );
    });
}

/// The Clz/Ctz/Popcnt instance (#103's audit named them; #1054 found them
/// still clobbering): the clz_reread stream with the REAL pre-#1054 I64Clz
/// bytes spliced in fails clause P.
#[test]
fn pre_1054_clz_operand_hi_clear_caught() {
    with_verification_context(|| {
        let wasm = bitcount_reread_wasm(WasmOp::I64Clz);
        let arm = lower(&wasm, 1, vec![true]);

        let clz = arm
            .iter()
            .find(|ins| matches!(ins.op, ArmOp::I64Clz { .. }))
            .expect("stream must contain the I64Clz pseudo-op");
        assert_eq!(
            clz.op,
            ArmOp::I64Clz {
                rd: Reg::R2,
                rnlo: Reg::R0,
                rnhi: Reg::R1,
            },
            "selector register assignment drifted — re-dump pre_1054_clz_bytes \
             from commit 1fe1ad22 for the new assignment"
        );

        let bytes = pre_1054_clz_bytes();
        let bytes_for = splice_bytes(&arm, |op| matches!(op, ArmOp::I64Clz { .. }), &bytes);
        let err = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            assert_no_param_clobber_while_live(&wasm, &arm, ONE_I64_HOME, &bytes_for);
        }))
        .expect_err("pre-#1054 clz bytes must fail the strengthened checker");
        let msg = panic_msg(err);
        assert!(
            msg.contains("clause P") && msg.contains("counterexample"),
            "wrong rejection: {msg}"
        );
    });
}

/// Sanity for the banked bytes themselves: straight through the #1054
/// validator (no window machinery), both pre-fix sequences are rejected with
/// a COUNTEREXAMPLE — i.e. they decode fine and compute the right result;
/// only the operand-preservation clause sees the defect. Guards the banked
/// bytes against rot (a typo would surface as a Decode error here).
#[test]
fn banked_pre_1054_bytes_are_counterexamples_not_decode_errors() {
    with_verification_context(|| {
        let shl = ArmOp::I64Shl {
            rd_lo: Reg::R4,
            rd_hi: Reg::R5,
            rn_lo: Reg::R0,
            rn_hi: Reg::R1,
            rm_lo: Reg::R2,
            rm_hi: Reg::R3,
        };
        match validate_expansion(&WasmOp::I64Shl, &shl, &pre_1054_shl_bytes()) {
            Err(ExpansionError::Counterexample { .. }) => {}
            other => panic!("expected Counterexample for pre-1054 shl bytes, got {other:?}"),
        }
        let clz = ArmOp::I64Clz {
            rd: Reg::R2,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
        };
        match validate_expansion(&WasmOp::I64Clz, &clz, &pre_1054_clz_bytes()) {
            Err(ExpansionError::Counterexample { .. }) => {}
            other => panic!("expected Counterexample for pre-1054 clz bytes, got {other:?}"),
        }
    });
}

fn panic_msg(payload: Box<dyn std::any::Any + Send>) -> String {
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_else(|| "<unknown panic>".to_string())
}
