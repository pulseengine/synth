//! Register def/use + liveness analysis — foundation for VCR-RA-001.
//!
//! This is the reusable primitive a spill-capable register allocator (and DCE,
//! and peephole-safety checks) is built on: for each ARM instruction, which
//! registers it *reads* (uses) and which it *writes* (defs). The current
//! codegen has no such analysis — `select_with_stack` tracks a virtual stack and
//! hard-fails on exhaustion (instruction_selector.rs:330/356/577/4667) rather
//! than reasoning over live ranges. Per the verified-codegen roadmap
//! (`artifacts/verified-codegen-roadmap.yaml`, VCR-RA-001) we build that
//! reasoning up incrementally; this module is step one.
//!
//! **Soundness discipline.** Instructions whose register effect is not yet
//! modeled precisely — high-level pseudo-ops (`LocalGet`, `Select`, …), the
//! 64-bit register-pair ops, the FP ops, and anything that clobbers a
//! caller-saved set (`Bl`, `Call`, …) — return `None` from [`reg_effect`]. Every
//! analysis here returns `None` for a stream it cannot *fully* model, so a
//! non-`None` result is always trustworthy. Nothing in this module is wired into
//! codegen yet: it is pure analysis, so it cannot change emitted bytes.

use crate::instruction_selector::ArmInstruction;
use crate::rules::{ArmOp, MemAddr, Operand2, Reg};

/// The register read/write effect of a single instruction.
///
/// `defs` are registers fully written (their previous value is dead after this
/// instruction); `uses` are registers read. An instruction that both reads and
/// writes a register (e.g. `Movt`, which preserves the low half) lists it in
/// both.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct RegEffect {
    pub defs: Vec<Reg>,
    pub uses: Vec<Reg>,
}

fn op2_uses(op2: &Operand2) -> Vec<Reg> {
    match op2 {
        Operand2::Reg(r) => vec![*r],
        Operand2::RegShift { rm, .. } => vec![*rm],
        Operand2::Imm(_) => vec![],
    }
}

fn addr_uses(a: &MemAddr) -> Vec<Reg> {
    let mut v = vec![a.base];
    if let Some(r) = a.offset_reg {
        v.push(r);
    }
    v
}

/// The register def/use effect of `op`, or `None` if `op` is not yet modeled
/// precisely (pseudo-ops, i64-pair ops, FP, calls, control flow). Callers that
/// need soundness must treat `None` as "unknown" and bail.
pub fn reg_effect(op: &ArmOp) -> Option<RegEffect> {
    use ArmOp::*;
    let def_use = |defs: Vec<Reg>, uses: Vec<Reg>| Some(RegEffect { defs, uses });

    match op {
        // rd = rn <op> op2
        Add { rd, rn, op2 }
        | Sub { rd, rn, op2 }
        | Adds { rd, rn, op2 }
        | Subs { rd, rn, op2 }
        | Adc { rd, rn, op2 }
        | Sbc { rd, rn, op2 }
        | And { rd, rn, op2 }
        | Orr { rd, rn, op2 }
        | Eor { rd, rn, op2 } => {
            let mut uses = vec![*rn];
            uses.extend(op2_uses(op2));
            def_use(vec![*rd], uses)
        }

        // rd = imm - rn (reverse subtract; second operand is an immediate)
        Rsb { rd, rn, .. } => def_use(vec![*rd], vec![*rn]),

        // rd = <op> op2
        Mov { rd, op2 } | Mvn { rd, op2 } => def_use(vec![*rd], op2_uses(op2)),

        // rd = imm (low half); upper half zeroed — no use
        Movw { rd, .. } | MovwSym { rd, .. } => def_use(vec![*rd], vec![]),
        // rd[31:16] = imm, rd[15:0] preserved — reads and writes rd
        Movt { rd, .. } | MovtSym { rd, .. } => def_use(vec![*rd], vec![*rd]),

        // rd = rn <op> rm
        Mul { rd, rn, rm }
        | Sdiv { rd, rn, rm }
        | Udiv { rd, rn, rm }
        | LslReg { rd, rn, rm }
        | LsrReg { rd, rn, rm }
        | AsrReg { rd, rn, rm }
        | RorReg { rd, rn, rm } => def_use(vec![*rd], vec![*rn, *rm]),

        // {rdhi:rdlo} = rn * rm
        Umull { rdlo, rdhi, rn, rm } => def_use(vec![*rdlo, *rdhi], vec![*rn, *rm]),

        // rd = rn*rm - ra
        Mls { rd, rn, rm, ra } => def_use(vec![*rd], vec![*rn, *rm, *ra]),

        // rd = rn <shift> #imm
        Lsl { rd, rn, .. } | Lsr { rd, rn, .. } | Asr { rd, rn, .. } | Ror { rd, rn, .. } => {
            def_use(vec![*rd], vec![*rn])
        }

        // rd = <unary> rm
        Clz { rd, rm }
        | Rbit { rd, rm }
        | Popcnt { rd, rm }
        | Sxtb { rd, rm }
        | Sxth { rd, rm } => def_use(vec![*rd], vec![*rm]),

        // flag-setting compares: read operands, write no GP register
        Cmp { rn, op2 } | Cmn { rn, op2 } => {
            let mut uses = vec![*rn];
            uses.extend(op2_uses(op2));
            def_use(vec![], uses)
        }

        // rd = cond (materialize a flag) — writes rd, reads flags only
        SetCond { rd, .. } => def_use(vec![*rd], vec![]),

        // loads: rd = mem[addr]
        Ldr { rd, addr }
        | Ldrb { rd, addr }
        | Ldrsb { rd, addr }
        | Ldrh { rd, addr }
        | Ldrsh { rd, addr } => def_use(vec![*rd], addr_uses(addr)),

        // stores: mem[addr] = rd — rd is a SOURCE (use), addr regs are uses
        Str { rd, addr } | Strb { rd, addr } | Strh { rd, addr } => {
            let mut uses = vec![*rd];
            uses.extend(addr_uses(addr));
            def_use(vec![], uses)
        }

        // register lists
        Pop { regs } => def_use(regs.clone(), vec![]),
        Push { regs } => def_use(vec![], regs.clone()),

        // no register effect
        Nop | Udf { .. } => def_use(vec![], vec![]),

        // Everything else is not modeled precisely here: control flow
        // (B/BOffset/BCondOffset/Bhs/Blo/Bcc/Bx), calls and clobbers
        // (Bl/Blx/Call/CallIndirect), memory builtins, the high-level pseudo-ops
        // (Local*/Global*/Select*/BrTable), and the i64-pair + FP families.
        // Returning None keeps every downstream analysis sound.
        _ => None,
    }
}

/// True if `op` is straight-line (no branch / label / call) and therefore safe
/// to include in a local, single-block analysis.
fn is_straight_line(op: &ArmOp) -> bool {
    use ArmOp::*;
    !matches!(
        op,
        Label { .. }
            | B { .. }
            | BOffset { .. }
            | BCondOffset { .. }
            | Bhs { .. }
            | Blo { .. }
            | Bcc { .. }
            | Bl { .. }
            | Bx { .. }
            | Blx { .. }
            | BrTable { .. }
            | Call { .. }
            | CallIndirect { .. }
    )
}

/// Indices of instructions in `instrs` whose destination register is a **dead
/// store**: written here and then *overwritten* later in the same straight-line
/// region before any intervening read. Such an instruction's result is provably
/// unused regardless of what is live on exit, so it is a sound dead-code
/// candidate — the generic form of the hand-rolled dead-divisor-const peephole
/// (#221, `drop_prev_const_materialization`).
///
/// Returns `None` (declines to analyze) if the region is not a single
/// straight-line block of fully-modeled instructions — never a wrong answer.
/// A single-`def`, no-`use` instruction (a pure materialization like `Movw`) is
/// required for a candidate, so we never flag a read-modify-write as dead.
pub fn local_dead_defs(instrs: &[ArmInstruction]) -> Option<Vec<usize>> {
    // Pre-compute effects; bail if anything is unmodeled or not straight-line.
    let mut effects: Vec<RegEffect> = Vec::with_capacity(instrs.len());
    for instr in instrs {
        if !is_straight_line(&instr.op) {
            return None;
        }
        effects.push(reg_effect(&instr.op)?);
    }

    let mut dead = Vec::new();
    for (i, eff) in effects.iter().enumerate() {
        // Only consider a pure single-register materialization (def, no use of
        // that same reg): a read-modify-write (e.g. Movt) is never a dead store.
        if eff.defs.len() != 1 {
            continue;
        }
        let d = eff.defs[0];
        if eff.uses.contains(&d) {
            continue;
        }
        // Scan forward: is `d` read before it is written again?
        let mut overwritten_before_use = false;
        for later in &effects[i + 1..] {
            if later.uses.contains(&d) {
                break; // used → live → not dead
            }
            if later.defs.contains(&d) {
                overwritten_before_use = true; // redefined unused → dead store
                break;
            }
        }
        if overwritten_before_use {
            dead.push(i);
        }
    }
    Some(dead)
}

/// A constant materialization whose value is **already available** in a live
/// register at that point — a redundant re-derivation (const-CSE opportunity).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RedundantConst {
    /// Index of the redundant materialization in the instruction stream.
    pub index: usize,
    /// The constant value being (re-)materialized.
    pub value: i32,
    /// A register that already holds `value` at this point.
    pub available_in: Reg,
}

/// If `op` is a single-instruction constant materialization, the `(rd, value)`
/// it produces. Only the 16-bit `Movw` / immediate `Mov` forms are recognized —
/// these are the ones the hot paths re-materialize (saturation clamps `#0x7e` /
/// `#0x7f`, shift amounts, `#0`). A `Movt` builds the high half of a 32-bit
/// constant; it is deliberately *not* recognized here and instead invalidates
/// the tracked value (handled by the caller via `reg_effect`), so a
/// `Movw;Movt` pair is never mistaken for a pure 16-bit constant.
fn const_materialization(op: &ArmOp) -> Option<(Reg, i32)> {
    match op {
        ArmOp::Movw { rd, imm16 } => Some((*rd, *imm16 as i32)),
        ArmOp::Mov {
            rd,
            op2: Operand2::Imm(v),
        } => Some((*rd, *v)),
        _ => None,
    }
}

/// Redundant constant materializations within a straight-line block: each
/// instruction that re-derives a constant **already resident** in a register
/// (not clobbered since). This is the analysis behind const-CSE /
/// rematerialization-avoidance — the dominant hot-path waste gale measured on
/// `flat_flight` (the int8 clamps `#0x7e` / `#0x7f` materialized 6× each,
/// 61% of all constant loads redundant, #209). It is the *forward* dual of
/// [`local_dead_defs`]: that finds a write with no later read; this finds a
/// write whose value was already computed.
///
/// Pure detection — it reports the opportunity; the eventual fix (keep the
/// constant resident across its uses) is the register allocator's job
/// (VCR-RA-001). Returns `None` if the region is not a single straight-line
/// block of fully-modeled instructions, so a result is never a wrong answer.
pub fn redundant_const_defs(instrs: &[ArmInstruction]) -> Option<Vec<RedundantConst>> {
    let mut held: Vec<(Reg, i32)> = Vec::new(); // registers with a known constant
    let mut out = Vec::new();

    for (i, instr) in instrs.iter().enumerate() {
        if !is_straight_line(&instr.op) {
            return None;
        }
        let eff = reg_effect(&instr.op)?;

        if let Some((rd, v)) = const_materialization(&instr.op) {
            // Already available in some register? → redundant re-derivation.
            if let Some(&(r, _)) = held.iter().find(|&&(_, val)| val == v) {
                out.push(RedundantConst {
                    index: i,
                    value: v,
                    available_in: r,
                });
            }
            // `rd` now holds `v` (drop any prior fact about rd first).
            held.retain(|&(r, _)| r != rd);
            held.push((rd, v));
        } else {
            // Any register this instruction writes loses its known constant.
            for d in &eff.defs {
                held.retain(|&(r, _)| r != *d);
            }
        }
    }
    Some(out)
}

/// Aggregate analysis of a whole (possibly branchy) function.
///
/// The per-block detectors ([`local_dead_defs`], [`redundant_const_defs`]) only
/// reason over a single straight-line block and decline (`None`) on any branch.
/// Real functions (e.g. `flat_flight`, with its `br_table` clamps) are a
/// sequence of such blocks separated by control flow. This splits the stream
/// into **maximal straight-line, fully-modeled segments** — a non-straight-line
/// op (branch/call) or an op with no precise [`reg_effect`] ends the current
/// segment — runs both detectors per segment, and reports global indices.
///
/// This is **sound by construction**: a constant resident at the end of one
/// segment is *not* assumed resident in the next (state is reset at every
/// boundary), so cross-block redundancy is under-reported rather than
/// over-reported, and an instruction that can't be modeled never lands inside a
/// segment. It never returns `None` — it analyzes whatever is analyzable and
/// counts the rest as skipped.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FunctionAnalysis {
    /// Global indices of dead stores (overwritten before use within a segment).
    pub dead_defs: Vec<usize>,
    /// Redundant constant materializations (value already resident), global idx.
    pub redundant_consts: Vec<RedundantConst>,
    /// Number of maximal straight-line analyzable segments found.
    pub segments: usize,
    /// Instructions that ended a segment (branch/call/unmodeled) — not analyzed.
    pub skipped: usize,
}

pub fn analyze_function(instrs: &[ArmInstruction]) -> FunctionAnalysis {
    let mut report = FunctionAnalysis::default();
    let mut seg_start = 0usize;

    // Flush [seg_start, end) as one segment, offsetting indices to global.
    let flush = |report: &mut FunctionAnalysis, start: usize, end: usize| {
        if end <= start {
            return;
        }
        let seg = &instrs[start..end];
        report.segments += 1;
        if let Some(d) = local_dead_defs(seg) {
            report.dead_defs.extend(d.into_iter().map(|i| i + start));
        }
        if let Some(rc) = redundant_const_defs(seg) {
            report.redundant_consts.extend(rc.into_iter().map(|mut c| {
                c.index += start;
                c
            }));
        }
    };

    for (i, instr) in instrs.iter().enumerate() {
        let analyzable = is_straight_line(&instr.op) && reg_effect(&instr.op).is_some();
        if !analyzable {
            flush(&mut report, seg_start, i);
            report.skipped += 1;
            seg_start = i + 1;
        }
    }
    flush(&mut report, seg_start, instrs.len());
    report
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instruction_selector::ArmInstruction;
    use crate::rules::{ArmOp, Operand2, Reg};

    fn ins(op: ArmOp) -> ArmInstruction {
        ArmInstruction {
            op,
            source_line: None,
        }
    }

    #[test]
    fn reg_effect_models_three_operand_alu() {
        let e = reg_effect(&ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        })
        .unwrap();
        assert_eq!(e.defs, vec![Reg::R0]);
        assert_eq!(e.uses, vec![Reg::R1, Reg::R2]);
    }

    #[test]
    fn reg_effect_store_source_is_a_use_not_a_def() {
        // STR R3, [R11, R4] — R3 is read (the value stored), R11+R4 addressing.
        let e = reg_effect(&ArmOp::Str {
            rd: Reg::R3,
            addr: crate::rules::MemAddr::reg(Reg::R11, Reg::R4),
        })
        .unwrap();
        assert!(e.defs.is_empty(), "a store defines no register");
        assert_eq!(e.uses, vec![Reg::R3, Reg::R11, Reg::R4]);
    }

    #[test]
    fn reg_effect_movt_reads_and_writes_rd() {
        let e = reg_effect(&ArmOp::Movt {
            rd: Reg::R5,
            imm16: 0x1234,
        })
        .unwrap();
        assert_eq!(e.defs, vec![Reg::R5]);
        assert_eq!(e.uses, vec![Reg::R5], "Movt preserves the low half");
    }

    #[test]
    fn reg_effect_declines_pseudo_and_call_ops() {
        assert!(
            reg_effect(&ArmOp::LocalGet {
                rd: Reg::R0,
                index: 0
            })
            .is_none()
        );
        assert!(
            reg_effect(&ArmOp::Bl {
                label: String::new()
            })
            .is_none()
        );
    }

    #[test]
    fn dead_def_detects_overwrite_before_use() {
        // Movw R0,#7  ;  Movw R0,#9  ;  Add R1,R0,#0
        // The first Movw is a dead store (R0 overwritten before any read).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 9,
            }),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            }),
        ];
        assert_eq!(local_dead_defs(&seq), Some(vec![0]));
    }

    #[test]
    fn dead_def_respects_intervening_use() {
        // Movw R0,#7  ;  Add R1,R0,#0  ;  Movw R0,#9
        // The first Movw is NOT dead: R0 is read by the Add before being rewritten.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 9,
            }),
        ];
        assert_eq!(local_dead_defs(&seq), Some(vec![]));
    }

    #[test]
    fn redundant_const_flags_rematerialization_while_resident() {
        // movw r0,#0x7e ; add r2,r1,r0 ; movw r3,#0x7e
        // The second 0x7e is redundant — r0 still holds it.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x7e,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R3,
                imm16: 0x7e,
            }),
        ];
        let r = redundant_const_defs(&seq).unwrap();
        assert_eq!(r.len(), 1);
        assert_eq!(r[0].index, 2);
        assert_eq!(r[0].value, 0x7e);
        assert_eq!(r[0].available_in, Reg::R0);
    }

    #[test]
    fn redundant_const_respects_clobber() {
        // movw r0,#0x7e ; movw r0,#0x10 ; movw r1,#0x7e
        // r0 was overwritten, so 0x7e is NOT resident → the last is not redundant.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x7e,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x10,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 0x7e,
            }),
        ];
        assert_eq!(redundant_const_defs(&seq), Some(vec![]));
    }

    #[test]
    fn redundant_const_counts_flat_flight_clamp_pattern() {
        // The measured flat_flight waste: one int8 clamp bound (#0x7e) loaded
        // into a fresh register 6 times with the first still live throughout.
        // 5 of the 6 are redundant.
        let mut seq = Vec::new();
        for k in 0..6u32 {
            seq.push(ins(ArmOp::Movw {
                rd: [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5][k as usize],
                imm16: 0x7e,
            }));
            // a consumer that keeps the earlier value live (reads R0)
            seq.push(ins(ArmOp::Add {
                rd: Reg::R6,
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R0),
            }));
        }
        let r = redundant_const_defs(&seq).unwrap();
        assert_eq!(r.len(), 5, "5 of 6 clamp materializations are redundant");
        assert!(
            r.iter()
                .all(|c| c.value == 0x7e && c.available_in == Reg::R0)
        );
    }

    #[test]
    fn redundant_const_movt_pair_is_not_a_pure_const() {
        // movw r0,#7 ; movt r0,#1  (r0 = 0x10007) ; movw r1,#7
        // After Movt, r0 no longer holds the pure 16-bit 7 → last is NOT redundant.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Movt {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 7,
            }),
        ];
        assert_eq!(redundant_const_defs(&seq), Some(vec![]));
    }

    #[test]
    fn analyze_function_segments_across_a_branch() {
        // Segment 1: movw r0,#0x7e ; movw r1,#0x7e (r1 redundant)
        // <branch boundary>
        // Segment 2: movw r2,#0x7e ; movw r3,#0x7e (r3 redundant — fresh state)
        // The per-block detector would decline on the whole stream (branch);
        // analyze_function finds the redundancy in BOTH segments.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x7e,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 0x7e,
            }),
            ins(ArmOp::BOffset { offset: 8 }),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 0x7e,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R3,
                imm16: 0x7e,
            }),
        ];
        // whole-stream per-block detector declines:
        assert_eq!(redundant_const_defs(&seq), None);
        // function-wide analysis finds both:
        let a = analyze_function(&seq);
        assert_eq!(a.segments, 2);
        assert_eq!(a.skipped, 1, "the branch is the skipped boundary");
        let idxs: Vec<usize> = a.redundant_consts.iter().map(|c| c.index).collect();
        assert_eq!(
            idxs,
            vec![1, 4],
            "global indices of the two redundant loads"
        );
    }

    #[test]
    fn analyze_function_resets_state_at_boundary() {
        // movw r0,#5 ; <branch> ; movw r1,#5
        // r0's #5 must NOT be considered resident after the branch → not redundant.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 5,
            }),
            ins(ArmOp::BOffset { offset: 4 }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 5,
            }),
        ];
        let a = analyze_function(&seq);
        assert!(
            a.redundant_consts.is_empty(),
            "no cross-boundary redundancy may be claimed"
        );
        assert_eq!(a.segments, 2);
    }

    #[test]
    fn redundant_const_declines_on_branch() {
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x7e,
            }),
            ins(ArmOp::BOffset { offset: 4 }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 0x7e,
            }),
        ];
        assert_eq!(redundant_const_defs(&seq), None);
    }

    #[test]
    fn dead_def_declines_on_branch_or_unmodeled() {
        // A branch in the region → cannot soundly analyze a single block.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::BOffset { offset: 4 }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 9,
            }),
        ];
        assert_eq!(local_dead_defs(&seq), None);
    }
}
