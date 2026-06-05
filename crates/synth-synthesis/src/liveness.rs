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
use std::collections::{BTreeMap, BTreeSet};

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

        // rd = ra -/+ rn*rm
        Mls { rd, rn, rm, ra } | Mla { rd, rn, rm, ra } => def_use(vec![*rd], vec![*rn, *rm, *ra]),

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

        // conditional move (IT-block clamp form): rd = rm if cond, else rd
        // unchanged → rd is both read (preserved branch) and written; rm read.
        // Modeling this keeps the int8-clamp sequences (the #209 const-CSE
        // target) inside one analyzable segment instead of breaking at each
        // predicated move, so the allocator analysis can see the resident
        // clamp-bound constants across the whole clamp chain.
        SelectMove { rd, rm, .. } => def_use(vec![*rd], vec![*rd, *rm]),

        // rd = rcond != 0 ? rval1 : rval2 — writes rd, reads all three inputs.
        Select {
            rd,
            rval1,
            rval2,
            rcond,
        } => def_use(vec![*rd], vec![*rval1, *rval2, *rcond]),

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

/// Remove provably-dead stores from an instruction stream, returning the
/// rewritten stream and the count removed.
///
/// "Dead" here is exactly [`analyze_function`]'s `dead_defs`: a register write
/// that is *overwritten before any use within its straight-line segment*. Such
/// a write is dead regardless of cross-block liveness (the in-segment redefine
/// proves it), so deleting it preserves observable behavior. This is the
/// generic, function-wide form of the hand-rolled #221 peephole
/// (`drop_prev_const_materialization`), and the first **transform** on the
/// allocator track — the migration of the merged analyses into a codegen pass.
///
/// **Branch-offset safety:** this is intended to run on the `select_with_stack`
/// output *before* `resolve_label_branches` (arm_backend), where branches are
/// still symbolic labels — removing a non-branch instruction cannot perturb a
/// label-relative target, which is resolved to bytes afterward. The dead
/// instructions are always interior to a straight-line segment and are never
/// branch targets, so the rewrite is offset-neutral by construction.
///
/// Pure function: callers opt in. Not wired into codegen by this change — the
/// wiring is a separate, fully oracle-gated step (every differential fixture
/// must stay result-identical + a measured size/cycle delta + fuzz).
pub fn eliminate_dead_stores(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    let dead: std::collections::BTreeSet<usize> =
        analyze_function(instrs).dead_defs.into_iter().collect();
    if dead.is_empty() {
        return (instrs.to_vec(), 0);
    }
    let kept: Vec<ArmInstruction> = instrs
        .iter()
        .enumerate()
        .filter(|(i, _)| !dead.contains(i))
        .map(|(_, ins)| ins.clone())
        .collect();
    (kept, dead.len())
}

/// Fuse `mul` + `add` into `mla` (#257): for an `Add rD, x, Reg(y)` where one
/// operand is the destination of an earlier `Mul rM, rn, rm`, the result is
/// `mla rD, rn, rm, other`, and the now-redundant `Mul` is removed. Returns the
/// rewritten stream and the number of fusions.
///
/// Soundness conditions (all checked via [`reg_effect`]; any unmodeled
/// instruction conservatively blocks a fusion across it):
///  - the mul result `rM`'s value is **consumed only by the add** — dead after
///    the add until `rM` is next redefined. This is a precise *live-range*
///    check, NOT "rM is read nowhere in the function": the single-pass allocator
///    reuses `rM` for unrelated later values, and reads of those reincarnations
///    must not block the fusion (#257: the whole-function scan fired zero times
///    on the real `flat_flight`, where `r8` is recycled across axes),
///  - between the mul and the add, `rM` and the mul inputs `rn`/`rm` are
///    **neither redefined nor** (for `rM`) **read** — so the `mla` reading
///    `rn`/`rm` at the add's position sees the same values,
///  - `rM` and the other add operand are distinct, and the mul inputs are not
///    `rM` itself.
///
/// Pure function: callers opt in.
pub fn fuse_mul_add(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    let n = instrs.len();
    let mut removed = vec![false; n];
    let mut rewritten: Vec<Option<ArmOp>> = vec![None; n];

    for j in 0..n {
        let (rd, x, y) = match &instrs[j].op {
            ArmOp::Add {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            } => (*rd, *rn, *rm),
            _ => continue,
        };
        for (rmul, rother) in [(x, y), (y, x)] {
            if rmul == rother {
                continue;
            }
            // Most recent live `Mul rmul, mn, mm` before j.
            let Some(i) = (0..j).rev().find(|&k| {
                !removed[k] && matches!(&instrs[k].op, ArmOp::Mul { rd, .. } if *rd == rmul)
            }) else {
                continue;
            };
            let ArmOp::Mul { rn: mn, rm: mm, .. } = instrs[i].op else {
                continue;
            };
            if mn == rmul || mm == rmul {
                continue;
            }
            // Between i and j: no redef of rmul/mn/mm, no read of rmul.
            let between_ok = ((i + 1)..j).all(|k| {
                removed[k]
                    || reg_effect(&instrs[k].op).is_some_and(|e| {
                        !e.defs.contains(&rmul)
                            && !e.defs.contains(&mn)
                            && !e.defs.contains(&mm)
                            && !e.uses.contains(&rmul)
                    })
            });
            if !between_ok {
                continue;
            }
            // The mul result must be consumed ONLY by this add: dead after `j`
            // until `rmul` is next redefined. `between_ok` already proved no read
            // in (i, j). A whole-function "is rmul read anywhere" scan is WRONG —
            // the single-pass allocator REUSES `rmul` for unrelated later values,
            // whose reads would falsely block the fusion (#257: this is exactly
            // why fusion fired zero times on the real flat_flight, where r8 is
            // recycled). Scan forward from j+1: a read of `rmul` before any redef
            // means our value is still live → unsafe; a redef ends its live range
            // → safe; an op we cannot see through (branch/call/pseudo) is treated
            // conservatively as a possible later read → unsafe. When `rmul == rd`
            // the add overwrites it with the (correct) result, so later reads are
            // of the result, not the dangling product — always safe.
            if rmul != rd {
                let mut consumed_only_here = true;
                for k in (j + 1)..n {
                    if removed[k] {
                        continue;
                    }
                    match reg_effect(&instrs[k].op) {
                        Some(e) if e.uses.contains(&rmul) => {
                            consumed_only_here = false; // still live → unsafe
                            break;
                        }
                        Some(e) if e.defs.contains(&rmul) => break, // redef → dead → safe
                        Some(_) => {}                               // unrelated → keep scanning
                        None => {
                            // Unmodeled (branch/call/pseudo): cannot prove the
                            // value is dead past it → bail to stay sound.
                            consumed_only_here = false;
                            break;
                        }
                    }
                }
                if !consumed_only_here {
                    continue;
                }
            }
            rewritten[j] = Some(ArmOp::Mla {
                rd,
                rn: mn,
                rm: mm,
                ra: rother,
            });
            removed[i] = true;
            break;
        }
    }

    let mut fused = 0;
    let mut out = Vec::with_capacity(n);
    for k in 0..n {
        if removed[k] {
            continue;
        }
        match &rewritten[k] {
            Some(op) => {
                fused += 1;
                out.push(ArmInstruction {
                    op: op.clone(),
                    source_line: instrs[k].source_line,
                });
            }
            None => out.push(instrs[k].clone()),
        }
    }
    (out, fused)
}

// ============================================================================
// CFG-aware liveness (VCR-RA-001 substrate)
//
// The per-segment detectors above reset all state at every control-flow
// boundary — sound, but they cannot reason *across* blocks. A spill-capable
// register allocator needs the real thing: for each basic block, the set of
// registers live on entry (`live_in`) and exit (`live_out`), computed by the
// classic backward dataflow fixpoint
//
//     live_in[B]  = use[B] ∪ (live_out[B] − def[B])
//     live_out[B] = ⋃ { live_in[S] : S ∈ succ(B) }
//
// The interference graph an allocator colours is read directly off these sets
// (two registers interfere iff both are live at some common point). This is
// pure analysis — nothing here is wired into codegen, so it cannot change a
// single emitted byte; the fixtures stay bit-identical by construction.
// ============================================================================

/// A basic block of the label-form CFG: the maximal instruction run
/// `[start, end)` with a single entry (its first instruction) and the block
/// indices it can transfer control to (`succ`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BasicBlock {
    /// Global index of the first instruction (inclusive).
    pub start: usize,
    /// Global index one past the last instruction (exclusive).
    pub end: usize,
    /// Successor block indices.
    pub succ: Vec<usize>,
}

/// A function's CFG plus per-block liveness.
///
/// **Scope / soundness.** Built only for functions whose every branch is in the
/// resolvable *label form* (`B`/`Bhs`/`Blo`/`Bcc` targeting a `Label`) and whose
/// every other instruction has a precise [`reg_effect`]. Any numeric-offset
/// branch (`BOffset`/`BCondOffset`), computed/return branch (`Bx`/`Blx`), call
/// (`Bl`/`Call`/`CallIndirect`), `BrTable`, or unmodeled-effect op makes
/// [`cfg_liveness`] return `None` — it never produces a partial or guessed CFG.
/// This is the leaf-function, label-form stage that `select_with_stack` emits
/// before `resolve_label_branches`.
///
/// **Exit liveness caveat (read before driving allocation).** A block with no
/// successors gets `live_out = ∅`. The ABI return-value registers (`R0`, and
/// `R1` for an `i64` result) are therefore *not* counted live at the function
/// exit — that liveness is an external fact the caller must union in before this
/// graph drives spilling, or a return value could be wrongly treated as dead.
/// As pure analysis this is correct w.r.t. the stream's own reads; the ABI
/// augmentation is a deliberately separate, later step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CfgLiveness {
    pub blocks: Vec<BasicBlock>,
    /// `live_in[b]` — registers live entering block `b`.
    pub live_in: Vec<BTreeSet<Reg>>,
    /// `live_out[b]` — registers live leaving block `b`.
    pub live_out: Vec<BTreeSet<Reg>>,
}

/// How a block's final instruction transfers control.
enum Term<'a> {
    /// Unconditional branch to a label — single successor, no fallthrough.
    Uncond(&'a str),
    /// Conditional branch to a label — target plus fallthrough.
    Cond(&'a str),
    /// Straight-line / label-only — falls through to the next block (if any).
    Fall,
    /// Cannot be modeled (numeric-offset branch, computed/return branch, call,
    /// `BrTable`) — the whole analysis declines.
    Unsupported,
}

fn classify(op: &ArmOp) -> Term<'_> {
    use ArmOp::*;
    match op {
        B { label } => Term::Uncond(label),
        Bhs { label } | Blo { label } | Bcc { label, .. } => Term::Cond(label),
        BOffset { .. }
        | BCondOffset { .. }
        | Bx { .. }
        | Blx { .. }
        | Bl { .. }
        | BrTable { .. }
        | Call { .. }
        | CallIndirect { .. } => Term::Unsupported,
        _ => Term::Fall,
    }
}

/// `use`/`def` of one block: registers read before any write in the block
/// (`use`), and registers written anywhere in it (`def`). Branch and `Label`
/// instructions contribute an empty GP-register effect (a conditional branch
/// reads the flags, not a general register).
fn block_use_def(instrs: &[ArmInstruction], b: &BasicBlock) -> (BTreeSet<Reg>, BTreeSet<Reg>) {
    let mut used = BTreeSet::new();
    let mut defined = BTreeSet::new();
    for ins in &instrs[b.start..b.end] {
        let eff = reg_effect(&ins.op).unwrap_or_default();
        for u in &eff.uses {
            if !defined.contains(u) {
                used.insert(*u);
            }
        }
        for d in &eff.defs {
            defined.insert(*d);
        }
    }
    (used, defined)
}

/// Build the label-form CFG of `instrs` and solve per-block liveness, or `None`
/// if the stream contains a construct outside the modeled scope (see
/// [`CfgLiveness`]). Sound by construction: a non-`None` result is a complete,
/// trustworthy CFG + fixpoint, never a partial guess.
pub fn cfg_liveness(instrs: &[ArmInstruction]) -> Option<CfgLiveness> {
    let n = instrs.len();
    if n == 0 {
        return Some(CfgLiveness {
            blocks: vec![],
            live_in: vec![],
            live_out: vec![],
        });
    }

    // 1. Validate every instruction is within the modeled scope.
    for ins in instrs {
        match classify(&ins.op) {
            Term::Unsupported => return None,
            Term::Uncond(_) | Term::Cond(_) => {}
            Term::Fall => {
                if !matches!(ins.op, ArmOp::Label { .. }) && reg_effect(&ins.op).is_none() {
                    return None;
                }
            }
        }
    }

    // 2. Leaders: instruction 0, every `Label`, and every instruction that
    //    follows a branch. (Branch targets are `Label`s, already leaders.)
    let mut is_leader = vec![false; n];
    is_leader[0] = true;
    for i in 0..n {
        if matches!(instrs[i].op, ArmOp::Label { .. }) {
            is_leader[i] = true;
        }
        if matches!(classify(&instrs[i].op), Term::Uncond(_) | Term::Cond(_)) && i + 1 < n {
            is_leader[i + 1] = true;
        }
    }
    let leaders: Vec<usize> = (0..n).filter(|&i| is_leader[i]).collect();

    // 3. Blocks span `[leader, next_leader)`.
    let mut blocks: Vec<BasicBlock> = leaders
        .iter()
        .enumerate()
        .map(|(bi, &start)| BasicBlock {
            start,
            end: leaders.get(bi + 1).copied().unwrap_or(n),
            succ: vec![],
        })
        .collect();

    let block_of_start: BTreeMap<usize, usize> = blocks
        .iter()
        .enumerate()
        .map(|(bi, b)| (b.start, bi))
        .collect();
    let mut block_of_label: BTreeMap<&str, usize> = BTreeMap::new();
    for (bi, b) in blocks.iter().enumerate() {
        if let ArmOp::Label { name } = &instrs[b.start].op {
            block_of_label.insert(name.as_str(), bi);
        }
    }

    // 4. Successors from each block's final instruction. Compute into a side
    //    vector first (immutable borrow of `blocks` for the label lookups),
    //    then write them back.
    let mut succs: Vec<Vec<usize>> = Vec::with_capacity(blocks.len());
    for b in &blocks {
        let last = b.end - 1;
        let fallthrough = block_of_start.get(&b.end).copied();
        let succ = match classify(&instrs[last].op) {
            Term::Uncond(label) => vec![*block_of_label.get(label)?],
            Term::Cond(label) => {
                let t = *block_of_label.get(label)?;
                let mut s = vec![t];
                if let Some(f) = fallthrough
                    && f != t
                {
                    s.push(f);
                }
                s
            }
            Term::Fall => fallthrough.into_iter().collect(),
            Term::Unsupported => return None, // validated above; defensive
        };
        succs.push(succ);
    }
    for (b, succ) in blocks.iter_mut().zip(succs) {
        b.succ = succ;
    }

    // 5. Backward dataflow fixpoint. Sets only grow and are bounded by the
    //    finite register set, so the loop terminates.
    let nb = blocks.len();
    let (use_b, def_b): (Vec<_>, Vec<_>) = blocks.iter().map(|b| block_use_def(instrs, b)).unzip();
    let mut live_in = vec![BTreeSet::<Reg>::new(); nb];
    let mut live_out = vec![BTreeSet::<Reg>::new(); nb];
    let mut changed = true;
    while changed {
        changed = false;
        for bi in (0..nb).rev() {
            let mut out = BTreeSet::new();
            for &s in &blocks[bi].succ {
                out.extend(live_in[s].iter().copied());
            }
            let mut in_ = use_b[bi].clone();
            in_.extend(out.difference(&def_b[bi]).copied());
            if out != live_out[bi] {
                live_out[bi] = out;
                changed = true;
            }
            if in_ != live_in[bi] {
                live_in[bi] = in_;
                changed = true;
            }
        }
    }

    Some(CfgLiveness {
        blocks,
        live_in,
        live_out,
    })
}

// ============================================================================
// Interference graph (VCR-RA-001 — the colouring input)
//
// A graph-colouring register allocator asks: which registers are *simultaneously
// live*, and therefore cannot share one physical register? That relation is the
// interference graph, read directly off the per-instruction liveness derived
// from [`cfg_liveness`]. Walking each block backward from its `live_out`, a
// register *defined* at an instruction interferes with everything live
// immediately *after* that instruction (they coexist), and co-defined registers
// (e.g. `Umull`'s `rdlo`/`rdhi`) interfere with each other. The precision payoff:
// in `add r3, r1, r2` the inputs die at the add, so `r3` does NOT interfere with
// `r1`/`r2` and may reuse one of their registers — a naive "all operands
// interfere" graph would forbid that.
//
// Pure analysis, no codegen callers: it informs a future allocator, it does not
// (yet) drive one, so emitted bytes are unchanged.
// ============================================================================

/// Undirected register interference graph: `a` and `b` are adjacent iff they are
/// ever simultaneously live (so a colouring must give them different physical
/// registers).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InterferenceGraph {
    adj: BTreeMap<Reg, BTreeSet<Reg>>,
}

impl InterferenceGraph {
    fn node(&mut self, r: Reg) {
        self.adj.entry(r).or_default();
    }

    fn add_edge(&mut self, a: Reg, b: Reg) {
        if a == b {
            return;
        }
        self.adj.entry(a).or_default().insert(b);
        self.adj.entry(b).or_default().insert(a);
    }

    /// Do `a` and `b` interfere (cannot share a physical register)?
    pub fn interferes(&self, a: Reg, b: Reg) -> bool {
        self.adj.get(&a).is_some_and(|s| s.contains(&b))
    }

    /// Registers that interfere with `r`.
    pub fn neighbors(&self, r: Reg) -> impl Iterator<Item = Reg> + '_ {
        self.adj.get(&r).into_iter().flat_map(|s| s.iter().copied())
    }

    /// Interference degree of `r` — the lower bound on distinct registers its
    /// neighbourhood needs; `degree(r) < k` guarantees `r` is `k`-colourable
    /// (the Chaitin/Briggs simplify criterion).
    pub fn degree(&self, r: Reg) -> usize {
        self.adj.get(&r).map_or(0, |s| s.len())
    }

    /// All registers mentioned in the graph (interfering or not).
    pub fn nodes(&self) -> impl Iterator<Item = Reg> + '_ {
        self.adj.keys().copied()
    }

    /// Total number of (undirected) interference edges.
    pub fn edge_count(&self) -> usize {
        self.adj.values().map(|s| s.len()).sum::<usize>() / 2
    }
}

/// Build the interference graph of `instrs`, or `None` if [`cfg_liveness`]
/// declines (a construct outside the modeled leaf-only, label-form scope). Sound
/// by construction: a non-`None` graph is complete for the whole function.
pub fn interference_graph(instrs: &[ArmInstruction]) -> Option<InterferenceGraph> {
    let cfg = cfg_liveness(instrs)?;
    let mut g = InterferenceGraph::default();

    for (bi, b) in cfg.blocks.iter().enumerate() {
        // `live` = registers live immediately AFTER the instruction being
        // processed; seeded with the block's live-out and walked backward.
        let mut live = cfg.live_out[bi].clone();
        for idx in (b.start..b.end).rev() {
            let eff = reg_effect(&instrs[idx].op).unwrap_or_default();
            // Each def interferes with everything live after this instruction
            // and with its co-defs; record defs/uses as nodes regardless.
            for (i, d) in eff.defs.iter().enumerate() {
                g.node(*d);
                for r in &live {
                    g.add_edge(*d, *r);
                }
                for d2 in &eff.defs[i + 1..] {
                    g.add_edge(*d, *d2);
                }
            }
            // live_before = (live − defs) ∪ uses
            for d in &eff.defs {
                live.remove(d);
            }
            for u in &eff.uses {
                g.node(*u);
                live.insert(*u);
            }
        }
    }
    Some(g)
}

// ============================================================================
// Graph colouring (VCR-RA-001 — the allocation decision)
//
// Colouring the interference graph with `k` colours IS register allocation:
// assign every node (value) a colour (physical register) so interfering values
// differ. Chaitin/Briggs:
//   1. SIMPLIFY — repeatedly remove a node of degree < k onto a stack (it can
//      always be coloured after its neighbours, which use ≤ k−1 colours).
//   2. SPILL    — if every remaining node has degree ≥ k, optimistically push
//      one anyway (Briggs: it is often still colourable in practice).
//   3. SELECT   — pop in reverse, giving each node the lowest colour not used by
//      an already-coloured neighbour. A node that finds NO free colour is an
//      actual spill.
//
// This is exactly the decision synth's single-pass allocator cannot make — it
// hard-fails on exhaustion instead of spilling. Pure algorithm over the graph;
// nothing here is wired into codegen.
// ============================================================================

/// Outcome of a `k`-colouring attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ColorResult {
    /// A valid assignment: every node → a colour in `0..k`, adjacent nodes
    /// differ. (Colours map to physical registers at the wiring step.)
    Colored(BTreeMap<Reg, usize>),
    /// Not `k`-colourable by the heuristic; these nodes are the spill set a real
    /// allocator would rewrite to stack slots and then re-attempt.
    Spilled(BTreeSet<Reg>),
}

/// Chaitin/Briggs `k`-colouring of an interference graph with optimistic spill.
/// Returns [`ColorResult::Colored`] with a full assignment, or
/// [`ColorResult::Spilled`] with the nodes that could not be coloured.
///
/// `k == 0` with a non-empty graph is trivially uncolourable (every node
/// spills). Pure function: it computes a decision, it does not mutate codegen.
pub fn color_graph(g: &InterferenceGraph, k: usize) -> ColorResult {
    color_graph_precolored(g, k, &BTreeMap::new())
}

/// `k`-colouring with **precoloured** nodes pinned to fixed colours — the
/// mechanism for honouring synth's reserved registers and ABI pins. Each entry
/// `(reg → colour)` in `precolored` keeps that colour and is never simplified or
/// spilled; it only *constrains* its neighbours (occupying a colour they cannot
/// reuse). Free nodes are coloured/​spilled by the same Chaitin/Briggs pass.
///
/// To reserve physical registers (e.g. keep `R11` = memory base), pin the
/// corresponding node to its colour and treat that colour as taken for the pool;
/// to force args, pin `R0..=R3`. Precoloured colours should be in `0..k`
/// (out-of-range pins are ignored for conflict purposes rather than panicking).
/// Pure function: a decision, not a codegen mutation.
pub fn color_graph_precolored(
    g: &InterferenceGraph,
    k: usize,
    precolored: &BTreeMap<Reg, usize>,
) -> ColorResult {
    // Working adjacency over the FREE (non-precoloured) nodes only; precoloured
    // nodes are fixed, so they never enter the simplify worklist — but they
    // remain in every free node's neighbourhood (via `g.neighbors`) so they
    // still constrain colouring.
    let mut adj: BTreeMap<Reg, BTreeSet<Reg>> = g
        .nodes()
        .filter(|n| !precolored.contains_key(n))
        .map(|n| (n, g.neighbors(n).collect()))
        .collect();
    let mut stack: Vec<Reg> = Vec::with_capacity(adj.len());

    // SIMPLIFY / SPILL: push every free node, preferring low-degree (< k) nodes;
    // when none qualify, optimistically push the highest-degree node.
    while !adj.is_empty() {
        let pick = adj
            .iter()
            .find(|(_, nbrs)| nbrs.len() < k)
            .map(|(r, _)| *r)
            .unwrap_or_else(|| {
                // No simplifiable node → optimistic spill candidate: highest
                // degree (ties broken by register order for determinism).
                adj.iter()
                    .max_by(|a, b| a.1.len().cmp(&b.1.len()).then(b.0.cmp(a.0)))
                    .map(|(r, _)| *r)
                    .unwrap()
            });
        // Remove `pick` from the working graph.
        let nbrs = adj.remove(&pick).unwrap_or_default();
        for n in &nbrs {
            if let Some(s) = adj.get_mut(n) {
                s.remove(&pick);
            }
        }
        stack.push(pick);
    }

    // SELECT: pop in reverse, assign the lowest free colour using the ORIGINAL
    // neighbourhood. Seeded with the precoloured pins, so a free node avoids
    // both its precoloured and its already-selected neighbours. A node with no
    // free colour in 0..k is an actual spill.
    let mut colour: BTreeMap<Reg, usize> = precolored.clone();
    let mut spilled: BTreeSet<Reg> = BTreeSet::new();
    while let Some(n) = stack.pop() {
        let mut used = vec![false; k];
        for nb in g.neighbors(n) {
            if let Some(&c) = colour.get(&nb)
                && c < k
            {
                used[c] = true;
            }
        }
        match (0..k).find(|&c| !used[c]) {
            Some(c) => {
                colour.insert(n, c);
            }
            None => {
                spilled.insert(n);
            }
        }
    }

    if spilled.is_empty() {
        ColorResult::Colored(colour)
    } else {
        ColorResult::Spilled(spilled)
    }
}

// ============================================================================
// Allocation verifier (VCR-RA-001 wiring step 1 — the self-check oracle)
//
// `color_graph` PRODUCES an assignment; `verify_allocation` CHECKS one. The two
// are independent code paths, so running the checker on the producer's output
// (or on any externally-supplied assignment — the current physical-register
// layout, or a future allocator's result) is genuine defense-in-depth. Per the
// wiring plan (`docs/design/vcr-ra-allocator-wiring.md`) the wired allocator
// runs this on its own output and refuses to emit on a conflict, so a bad
// allocation can never be silently lowered. Building the oracle FIRST means
// every later wiring sub-step lands already gated. Pure check, no codegen.
// ============================================================================

/// Why an assignment is not a valid colouring of an interference graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AllocationConflict {
    /// Two interfering registers were assigned the same colour — they would
    /// clobber each other if both lived in that physical register.
    SameColor { a: Reg, b: Reg, color: usize },
    /// A graph node has no colour in the assignment.
    Unassigned(Reg),
}

/// Verify that `assignment` is a valid colouring of `g`: every node is assigned,
/// and no two interfering nodes share a colour. `Ok(())` means the assignment is
/// safe to lower; `Err` pinpoints the first violation (deterministic in register
/// order). The checker an allocator runs on its own output before emitting.
pub fn verify_allocation(
    g: &InterferenceGraph,
    assignment: &BTreeMap<Reg, usize>,
) -> Result<(), AllocationConflict> {
    // Every node must have a colour.
    for n in g.nodes() {
        if !assignment.contains_key(&n) {
            return Err(AllocationConflict::Unassigned(n));
        }
    }
    // No interfering pair may share a colour.
    for n in g.nodes() {
        let cn = assignment[&n];
        for m in g.neighbors(n) {
            if let Some(&cm) = assignment.get(&m)
                && cn == cm
            {
                return Err(AllocationConflict::SameColor {
                    a: n,
                    b: m,
                    color: cn,
                });
            }
        }
    }
    Ok(())
}

// ============================================================================
// Allocator driver (VCR-RA-001 — the entry point the codegen wiring calls)
//
// Assembles the layer into one call: interference graph → k-colouring (reserved
// registers precoloured) → self-check, plus the rematerialization-avoidance
// opportunity count (the #209 const-CSE headroom). This is the function the
// virtual-register selector output will hand a function to; today it runs on the
// existing physical-register stream as a *shadow* allocation — it computes the
// decision without yet mutating codegen, so it can be measured on the real
// gale benches before anything is wired.
// ============================================================================

/// What the allocator decided for a function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AllocationOutcome {
    /// A valid physical-register assignment (colour = allocatable-pool index).
    Allocated {
        coloring: BTreeMap<Reg, usize>,
        /// Redundant constant materializations the allocator would avoid by
        /// keeping one copy resident — the #209 const-CSE / rematerialization
        /// headroom, measured on this function.
        remat_opportunities: usize,
    },
    /// `k`-colouring failed under the pool budget; these values must spill.
    NeedsSpill(BTreeSet<Reg>),
    /// The function contains a construct the analysis cannot model precisely
    /// (calls, numeric-offset/computed branches, i64-pair / FP ops). The
    /// allocator declines and codegen keeps the existing single-pass path.
    Declined,
}

/// One virtual register: a single def-to-last-use value range that the greedy
/// selector packed into physical register `reg`. `def`/`last_use` are indices
/// into the straight-line segment (a `def == 0` with no instruction-0 def marks
/// a segment input). This is the explicit form of the value the allocator
/// colours — the renaming a re-allocation pass assigns physical registers to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueRange {
    pub vreg: usize,
    pub reg: Reg,
    pub def: usize,
    pub last_use: usize,
}

/// Split each physical register's def-use chains in a straight-line segment into
/// distinct **virtual registers** (value ranges). Returns `None` if the segment
/// is not straight-line / fully modeled. Sound for straight-line code (the
/// reaching definition of every use is unambiguous — the most recent def);
/// cross-block web merging is a separate step. The number of ranges a physical
/// register splits into is exactly the overloading that inflates the physical
/// interference graph (e.g. `R1` → a dozen ranges, one spurious spill); colouring
/// *these* ranges instead is what removes the spurious spill. This is the
/// renaming the eventual virtual-register output / re-allocation consumes.
pub fn straight_line_value_ranges(instrs: &[ArmInstruction]) -> Option<Vec<ValueRange>> {
    let mut current: BTreeMap<Reg, usize> = BTreeMap::new(); // reg → open vreg index
    let mut ranges: Vec<ValueRange> = Vec::new();
    for (i, ins) in instrs.iter().enumerate() {
        if !is_straight_line(&ins.op) {
            return None;
        }
        let eff = reg_effect(&ins.op)?;
        for u in &eff.uses {
            let idx = *current.entry(*u).or_insert_with(|| {
                ranges.push(ValueRange {
                    vreg: ranges.len(),
                    reg: *u,
                    def: 0, // input: live from the segment start
                    last_use: i,
                });
                ranges.len() - 1
            });
            ranges[idx].last_use = i;
        }
        for d in &eff.defs {
            let vreg = ranges.len();
            ranges.push(ValueRange {
                vreg,
                reg: *d,
                def: i,
                last_use: i, // dead-on-arrival until a later use extends it
            });
            current.insert(*d, vreg);
        }
    }
    Some(ranges)
}

/// Peak **virtual-register pressure** of a straight-line segment: the maximum
/// number of distinct *values* live on any instruction edge — where a value is a
/// single def-to-last-use range, NOT a reused physical-register name. This is
/// the true register requirement the spurious physical-register interference
/// hides: the greedy selector reuses one physical register for many values, so
/// counting physical registers (the shadow pass's "would spill R1") overstates
/// the need. If this is ≤ the pool size, the segment fits with no spill once
/// virtually allocated. Returns `None` if the segment is not straight-line /
/// fully modeled. A register used before any def is an input, live from the
/// segment start.
pub fn straight_line_peak_pressure(instrs: &[ArmInstruction]) -> Option<usize> {
    let n = instrs.len();
    let mut current: BTreeMap<Reg, usize> = BTreeMap::new(); // reg → live value id
    let mut def_at: Vec<usize> = Vec::new(); // value id → def edge (0 for inputs)
    let mut last_use: Vec<usize> = Vec::new(); // value id → last-use index
    for (i, ins) in instrs.iter().enumerate() {
        if !is_straight_line(&ins.op) {
            return None;
        }
        let eff = reg_effect(&ins.op)?;
        for u in &eff.uses {
            let vid = *current.entry(*u).or_insert_with(|| {
                def_at.push(0); // input: live from the segment start
                last_use.push(0);
                def_at.len() - 1
            });
            last_use[vid] = i;
        }
        for d in &eff.defs {
            def_at.push(i);
            last_use.push(i); // dead-on-arrival until a later use extends it
            current.insert(*d, def_at.len() - 1);
        }
    }
    // A value used after its def occupies a register on edges [def, last_use).
    let mut delta = vec![0i32; n + 1];
    for vid in 0..def_at.len() {
        let (d, l) = (def_at[vid], last_use[vid]);
        if l > d {
            delta[d] += 1;
            delta[l] -= 1;
        }
    }
    let (mut cur, mut peak) = (0i32, 0i32);
    for d in delta.iter().take(n) {
        cur += *d;
        peak = peak.max(cur);
    }
    Some(peak as usize)
}

/// Peak virtual-register pressure across a whole (possibly branchy) function:
/// the max [`straight_line_peak_pressure`] over its straight-line segments (a
/// lower bound on the true register need). If ≤ the pool size, no segment forces
/// a spill once virtually allocated — so a physical-register "spill" is spurious.
pub fn function_peak_pressure(instrs: &[ArmInstruction]) -> usize {
    let mut peak = 0;
    let mut seg_start = 0;
    let flush = |start: usize, end: usize, peak: &mut usize| {
        if end > start
            && let Some(p) = straight_line_peak_pressure(&instrs[start..end])
        {
            *peak = (*peak).max(p);
        }
    };
    for (i, ins) in instrs.iter().enumerate() {
        if !is_straight_line(&ins.op) || reg_effect(&ins.op).is_none() {
            flush(seg_start, i, &mut peak);
            seg_start = i + 1;
        }
    }
    flush(seg_start, instrs.len(), &mut peak);
    peak
}

fn op2_rename(op2: &Operand2, from: Reg, to: Reg) -> Operand2 {
    let sub = |r: Reg| if r == from { to } else { r };
    match op2 {
        Operand2::Reg(r) => Operand2::Reg(sub(*r)),
        Operand2::RegShift { rm, shift, amount } => Operand2::RegShift {
            rm: sub(*rm),
            shift: *shift,
            amount: *amount,
        },
        Operand2::Imm(v) => Operand2::Imm(*v),
    }
}

fn addr_rename(a: &MemAddr, from: Reg, to: Reg) -> MemAddr {
    let sub = |r: Reg| if r == from { to } else { r };
    MemAddr {
        base: sub(a.base),
        offset: a.offset,
        offset_reg: a.offset_reg.map(sub),
    }
}

/// Rewrite every *use* of `from` to `to` in `op`, leaving definitions untouched.
/// Returns `None` for ops where a use of `from` cannot be rewritten without
/// ambiguity (e.g. a read-modify-write of `from` itself, like `Movt`/`SelectMove`
/// where `from == rd`) — the caller then declines the fold, staying sound.
fn rename_use(op: &ArmOp, from: Reg, to: Reg) -> Option<ArmOp> {
    use ArmOp::*;
    let sub = |r: Reg| if r == from { to } else { r };
    Some(match op {
        Add { rd, rn, op2 } => Add {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Sub { rd, rn, op2 } => Sub {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Adds { rd, rn, op2 } => Adds {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Subs { rd, rn, op2 } => Subs {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Adc { rd, rn, op2 } => Adc {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Sbc { rd, rn, op2 } => Sbc {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        And { rd, rn, op2 } => And {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Orr { rd, rn, op2 } => Orr {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Eor { rd, rn, op2 } => Eor {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Rsb { rd, rn, imm } => Rsb {
            rd: *rd,
            rn: sub(*rn),
            imm: *imm,
        },
        Mov { rd, op2 } => Mov {
            rd: *rd,
            op2: op2_rename(op2, from, to),
        },
        Mvn { rd, op2 } => Mvn {
            rd: *rd,
            op2: op2_rename(op2, from, to),
        },
        Mul { rd, rn, rm } => Mul {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        Sdiv { rd, rn, rm } => Sdiv {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        Udiv { rd, rn, rm } => Udiv {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        LslReg { rd, rn, rm } => LslReg {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        LsrReg { rd, rn, rm } => LsrReg {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        AsrReg { rd, rn, rm } => AsrReg {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        RorReg { rd, rn, rm } => RorReg {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        Umull { rdlo, rdhi, rn, rm } => Umull {
            rdlo: *rdlo,
            rdhi: *rdhi,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        Mls { rd, rn, rm, ra } => Mls {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
            ra: sub(*ra),
        },
        Mla { rd, rn, rm, ra } => Mla {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
            ra: sub(*ra),
        },
        Lsl { rd, rn, shift } => Lsl {
            rd: *rd,
            rn: sub(*rn),
            shift: *shift,
        },
        Lsr { rd, rn, shift } => Lsr {
            rd: *rd,
            rn: sub(*rn),
            shift: *shift,
        },
        Asr { rd, rn, shift } => Asr {
            rd: *rd,
            rn: sub(*rn),
            shift: *shift,
        },
        Ror { rd, rn, shift } => Ror {
            rd: *rd,
            rn: sub(*rn),
            shift: *shift,
        },
        Clz { rd, rm } => Clz {
            rd: *rd,
            rm: sub(*rm),
        },
        Rbit { rd, rm } => Rbit {
            rd: *rd,
            rm: sub(*rm),
        },
        Popcnt { rd, rm } => Popcnt {
            rd: *rd,
            rm: sub(*rm),
        },
        Sxtb { rd, rm } => Sxtb {
            rd: *rd,
            rm: sub(*rm),
        },
        Sxth { rd, rm } => Sxth {
            rd: *rd,
            rm: sub(*rm),
        },
        Cmp { rn, op2 } => Cmp {
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Cmn { rn, op2 } => Cmn {
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Ldr { rd, addr } => Ldr {
            rd: *rd,
            addr: addr_rename(addr, from, to),
        },
        Ldrb { rd, addr } => Ldrb {
            rd: *rd,
            addr: addr_rename(addr, from, to),
        },
        Ldrsb { rd, addr } => Ldrsb {
            rd: *rd,
            addr: addr_rename(addr, from, to),
        },
        Ldrh { rd, addr } => Ldrh {
            rd: *rd,
            addr: addr_rename(addr, from, to),
        },
        Ldrsh { rd, addr } => Ldrsh {
            rd: *rd,
            addr: addr_rename(addr, from, to),
        },
        Str { rd, addr } => Str {
            rd: sub(*rd),
            addr: addr_rename(addr, from, to),
        },
        Strb { rd, addr } => Strb {
            rd: sub(*rd),
            addr: addr_rename(addr, from, to),
        },
        Strh { rd, addr } => Strh {
            rd: sub(*rd),
            addr: addr_rename(addr, from, to),
        },
        // Read-modify-write of the renamed reg, register lists, or unmodeled ops:
        // cannot rewrite a use of `from` here without ambiguity → decline.
        _ => return None,
    })
}

/// Find the in-segment reads of `rd` that can be safely retargeted to `ra` after
/// dropping a redundant `movw rd, #v` at `def_i` (where `ra` already holds `v`).
/// Safe only if `ra` still holds `v` at every such read AND `rd`'s value is
/// provably local — i.e. `rd` is redefined within `[def_i, seg_end)` so the
/// dropped value never escapes the segment. Returns `None` (decline) otherwise.
fn safe_cse_uses(
    instrs: &[ArmInstruction],
    def_i: usize,
    rd: Reg,
    ra: Reg,
    seg_end: usize,
) -> Option<Vec<usize>> {
    let mut uses = Vec::new();
    let mut ra_holds_v = true;
    for (offset, ins) in instrs[(def_i + 1)..seg_end].iter().enumerate() {
        let j = def_i + 1 + offset;
        let eff = reg_effect(&ins.op)?;
        if eff.uses.contains(&rd) {
            if !ra_holds_v {
                return None; // ra no longer holds v but rd is read → unsafe
            }
            rename_use(&ins.op, rd, ra)?; // the use must be rewritable to ra
            uses.push(j);
        }
        if eff.defs.contains(&ra) {
            ra_holds_v = false;
        }
        if eff.defs.contains(&rd) {
            return Some(uses); // rd redefined → its v dies here → local → safe
        }
    }
    None // rd not redefined in the segment → may be live-out → decline
}

/// Const-CSE / rematerialization-avoidance driven by the value-range analysis:
/// where a `movw rd, #v` re-materializes a constant already resident in `ra`,
/// and `ra` provably still holds `v` through every later read of `rd` (until
/// `rd` is redefined within the segment), drop the `movw` and retarget those
/// reads to `ra`. This is the allocator's rematerialization-avoidance applied as
/// a targeted transform — every rewrite is *proven* by liveness, and it only
/// ever REMOVES a materialization (register pressure never rises), so it cannot
/// trigger the #277-class on-target regression. Returns the rewritten stream and
/// the count removed. Pure; callers opt in (flag-gated, differential-verified).
pub fn apply_const_cse(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    let n = instrs.len();
    let mut removed = vec![false; n];
    let mut rewrites: Vec<(usize, Reg, Reg)> = Vec::new(); // (use_index, from, to)

    // Process each maximal straight-line, fully-modeled segment independently.
    let mut seg_start = 0;
    let mut process_segment = |start: usize, end: usize| {
        let mut held: Vec<(Reg, i32)> = Vec::new(); // reg → resident constant
        for i in start..end {
            if let Some((rd, v)) = const_materialization(&instrs[i].op) {
                if let Some(&(ra, _)) = held.iter().find(|&&(_, val)| val == v)
                    && ra != rd
                    && let Some(use_indices) = safe_cse_uses(instrs, i, rd, ra, end)
                {
                    removed[i] = true;
                    for j in use_indices {
                        rewrites.push((j, rd, ra));
                    }
                    continue; // movw dropped; rd not added to `held`
                }
                held.retain(|&(r, _)| r != rd);
                held.push((rd, v));
            } else if let Some(eff) = reg_effect(&instrs[i].op) {
                for d in &eff.defs {
                    held.retain(|&(r, _)| r != *d);
                }
            }
        }
    };
    for (i, ins) in instrs.iter().enumerate() {
        if !is_straight_line(&ins.op) || reg_effect(&ins.op).is_none() {
            if i > seg_start {
                process_segment(seg_start, i);
            }
            seg_start = i + 1;
        }
    }
    if instrs.len() > seg_start {
        process_segment(seg_start, instrs.len());
    }

    if rewrites.is_empty() && !removed.iter().any(|&r| r) {
        return (instrs.to_vec(), 0);
    }
    // Apply: per-index rename map (an index may need multiple renames if several
    // folded consts share a consumer — apply each in turn).
    let mut renames_at: BTreeMap<usize, Vec<(Reg, Reg)>> = BTreeMap::new();
    for (j, from, to) in rewrites {
        renames_at.entry(j).or_default().push((from, to));
    }
    let mut out = Vec::with_capacity(n);
    let mut count = 0;
    for (i, ins) in instrs.iter().enumerate() {
        if removed[i] {
            count += 1;
            continue;
        }
        let mut op = ins.op.clone();
        if let Some(rs) = renames_at.get(&i) {
            for &(from, to) in rs {
                op = rename_use(&op, from, to).unwrap_or(op);
            }
        }
        out.push(ArmInstruction {
            op,
            source_line: ins.source_line,
        });
    }
    (out, count)
}

/// Run the register-allocator pipeline on a function: interference graph →
/// `k`-colouring with `precolored` reserved registers pinned → result. `k` is
/// the allocatable-pool size (e.g. 9 for synth's R0–R8). Pure: it computes a
/// decision and does not mutate the instruction stream — the call the codegen
/// wiring (VCR-RA-001) makes, runnable today as a shadow pass.
pub fn allocate_function(
    instrs: &[ArmInstruction],
    k: usize,
    precolored: &BTreeMap<Reg, usize>,
) -> AllocationOutcome {
    let Some(graph) = interference_graph(instrs) else {
        return AllocationOutcome::Declined;
    };
    let remat_opportunities = analyze_function(instrs).redundant_consts.len();
    match color_graph_precolored(&graph, k, precolored) {
        ColorResult::Colored(coloring) => AllocationOutcome::Allocated {
            coloring,
            remat_opportunities,
        },
        ColorResult::Spilled(s) => AllocationOutcome::NeedsSpill(s),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instruction_selector::ArmInstruction;
    use crate::rules::{ArmOp, Condition, Operand2, Reg};

    fn ins(op: ArmOp) -> ArmInstruction {
        ArmInstruction {
            op,
            source_line: None,
        }
    }

    #[test]
    fn fuse_mul_add_reproduces_gale_filter_pattern() {
        // gale #257 flat_flight filter: gyro*980 + accel*20
        //   movw r4,#980 ; mul r5,r3,r4 ; movw r7,#20 ; mul r8,r6,r7 ; add r2,r5,r8
        // → the first mul (r5=r3*r4) fuses into the add: mla r2,r3,r4,r8 (mul r5 gone).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R4,
                imm16: 980,
            }),
            ins(ArmOp::Mul {
                rd: Reg::R5,
                rn: Reg::R3,
                rm: Reg::R4,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 20,
            }),
            ins(ArmOp::Mul {
                rd: Reg::R8,
                rn: Reg::R6,
                rm: Reg::R7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R8),
            }),
        ];
        let (out, fused) = fuse_mul_add(&seq);
        assert_eq!(fused, 1);
        assert_eq!(out.len(), 4, "one mul removed (5 → 4 instrs)");
        // The add became mla r2, r3, r4, r8; mul r5 is gone; mul r8 stays.
        assert!(out.iter().any(|i| matches!(
            &i.op,
            ArmOp::Mla {
                rd: Reg::R2,
                rn: Reg::R3,
                rm: Reg::R4,
                ra: Reg::R8
            }
        )));
        assert!(
            !out.iter()
                .any(|i| matches!(&i.op, ArmOp::Mul { rd: Reg::R5, .. })),
            "the fused mul is removed"
        );
        assert!(
            out.iter()
                .any(|i| matches!(&i.op, ArmOp::Mul { rd: Reg::R8, .. })),
            "the non-fused mul stays"
        );
    }

    #[test]
    fn fuse_mul_add_declines_when_mul_result_used_again() {
        // mul r5,r3,r4 ; add r2,r5,r8 ; str r5,[r0]  — r5 read after the add → no fuse.
        let seq = vec![
            ins(ArmOp::Mul {
                rd: Reg::R5,
                rn: Reg::R3,
                rm: Reg::R4,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R8),
            }),
            ins(ArmOp::Str {
                rd: Reg::R5,
                addr: crate::rules::MemAddr::imm(Reg::R0, 0),
            }),
        ];
        let (out, fused) = fuse_mul_add(&seq);
        assert_eq!(fused, 0, "mul result is live after the add → not fusable");
        assert_eq!(out.len(), 3);
    }

    #[test]
    fn fuse_mul_add_fires_when_mul_result_is_reused_for_a_new_value_later() {
        // #257 real flat_flight shape: r8 = r6*r7 is consumed ONLY by the add,
        // then r8 is REDEFINED (movw) and reused for an unrelated value. The
        // greedy allocator's reuse of r8 must NOT block the fusion — the old
        // whole-function "r8 read anywhere?" scan wrongly counted the reads of
        // the *new* r8 and fired zero times on the deployed object.
        //   mul r8,r6,r7 ; add r2,r5,r8 ; movw r8,#980 ; mul r2,r7,r8
        let seq = vec![
            ins(ArmOp::Mul {
                rd: Reg::R8,
                rn: Reg::R6,
                rm: Reg::R7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R8),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R8,
                imm16: 980,
            }), // r8 redefined → unrelated value
            ins(ArmOp::Mul {
                rd: Reg::R2,
                rn: Reg::R7,
                rm: Reg::R8,
            }), // reads the NEW r8
        ];
        let (out, fused) = fuse_mul_add(&seq);
        assert_eq!(
            fused, 1,
            "reuse of r8 for a new value must not block fusion"
        );
        assert!(
            out.iter().any(|i| matches!(
                &i.op,
                ArmOp::Mla {
                    rd: Reg::R2,
                    rn: Reg::R6,
                    rm: Reg::R7,
                    ra: Reg::R5
                }
            )),
            "the op2-operand mul fuses with r5 as the accumulator"
        );
    }

    #[test]
    fn fuse_mul_add_declines_when_mul_input_clobbered_between() {
        // mul r5,r3,r4 ; movw r4,#1 (clobbers mul input r4) ; add r2,r5,r8
        // → mla would read the WRONG r4 → must NOT fuse.
        let seq = vec![
            ins(ArmOp::Mul {
                rd: Reg::R5,
                rn: Reg::R3,
                rm: Reg::R4,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R4,
                imm16: 1,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R8),
            }),
        ];
        let (_out, fused) = fuse_mul_add(&seq);
        assert_eq!(
            fused, 0,
            "mul input r4 clobbered before the add → not fusable"
        );
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
    fn reg_effect_models_conditional_move_as_read_modify_write() {
        // SelectMove rd, rm, cond — rd preserved on the false branch → both a
        // def and a use of rd; rm is a use. (Keeps clamp chains in one segment.)
        let e = reg_effect(&ArmOp::SelectMove {
            rd: Reg::R2,
            rm: Reg::R3,
            cond: Condition::EQ,
        })
        .unwrap();
        assert_eq!(e.defs, vec![Reg::R2]);
        assert_eq!(e.uses, vec![Reg::R2, Reg::R3]);
    }

    #[test]
    fn reg_effect_models_select_reads_all_three_inputs() {
        let e = reg_effect(&ArmOp::Select {
            rd: Reg::R0,
            rval1: Reg::R1,
            rval2: Reg::R2,
            rcond: Reg::R3,
        })
        .unwrap();
        assert_eq!(e.defs, vec![Reg::R0]);
        assert_eq!(e.uses, vec![Reg::R1, Reg::R2, Reg::R3]);
    }

    #[test]
    fn redundant_const_seen_across_a_conditional_move_now_that_it_is_modeled() {
        // movw r0,#0x7e ; selectmove r1,r2,EQ ; movw r3,#0x7e
        // The SelectMove no longer breaks the segment, so the second 0x7e is
        // detected as redundant (r0 still resident) — the #209 clamp pattern.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x7e,
            }),
            ins(ArmOp::SelectMove {
                rd: Reg::R1,
                rm: Reg::R2,
                cond: Condition::EQ,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R3,
                imm16: 0x7e,
            }),
        ];
        let r = redundant_const_defs(&seq).expect("SelectMove is now modeled, no segment break");
        assert_eq!(
            r.len(),
            1,
            "the clamp bound is seen as redundant across the IT move"
        );
        assert_eq!(r[0].available_in, Reg::R0);
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
    fn eliminate_dead_stores_removes_overwritten_def() {
        // movw r0,#7 ; movw r0,#9 ; add r1,r0,#0
        // The first movw is a dead store → removed; result keeps 2 instructions.
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
        let (out, removed) = eliminate_dead_stores(&seq);
        assert_eq!(removed, 1);
        assert_eq!(out.len(), 2);
        // The surviving movw is the live one (#9), then the add.
        assert!(matches!(out[0].op, ArmOp::Movw { imm16: 9, .. }));
        assert!(matches!(out[1].op, ArmOp::Add { .. }));
    }

    #[test]
    fn eliminate_dead_stores_is_noop_when_nothing_dead() {
        // A clean sequence (each def used) is returned byte-for-byte unchanged.
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
        ];
        let (out, removed) = eliminate_dead_stores(&seq);
        assert_eq!(removed, 0);
        assert_eq!(out.len(), seq.len());
        assert_eq!(out, seq, "no dead stores → identical stream");
    }

    #[test]
    fn eliminate_dead_stores_never_crosses_a_branch() {
        // movw r0,#7 ; <branch> ; movw r0,#9
        // The first movw is the END of segment 1 (no in-segment overwrite), so it
        // is NOT dead (its value could be live past the branch) → nothing removed.
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
        let (out, removed) = eliminate_dead_stores(&seq);
        assert_eq!(
            removed, 0,
            "a def at a segment boundary is never dead-removed"
        );
        assert_eq!(out.len(), 3);
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

    // ---- CFG-aware liveness (cfg_liveness) ---------------------------------

    #[test]
    fn cfg_liveness_straight_line_block_identifies_inputs() {
        // movw r0,#1 ; add r2,r0,r1
        // One block. r0 is defined locally (not live-in); r1 is read without a
        // prior def → it is a function input, live on entry. live_out = ∅.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
        ];
        let cfg = cfg_liveness(&seq).expect("straight-line stream is analyzable");
        assert_eq!(cfg.blocks.len(), 1);
        assert!(cfg.blocks[0].succ.is_empty(), "no branch → no successor");
        assert_eq!(
            cfg.live_in[0],
            BTreeSet::from([Reg::R1]),
            "only r1 (a read-before-write input) is live on entry"
        );
        assert!(
            cfg.live_out[0].is_empty(),
            "exit block live_out is empty (ABI return-liveness is layered in later)"
        );
    }

    #[test]
    fn cfg_liveness_propagates_across_conditional_branch() {
        // B0: movw r5,#42 ; bcc NE,"skip"   (succ: skip-block + fallthrough)
        // B1: mov r6,r5                       (fallthrough; reads r5)
        // B2: Label "skip" ; add r7,r5,r5     (target; reads r5)
        //
        // r5 is defined in B0 and read on *both* paths → it must be live OUT of
        // B0 and live IN of both successors, but NOT live-in of B0 (defined there).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R5,
                imm16: 42,
            }),
            ins(ArmOp::Bcc {
                cond: Condition::NE,
                label: "skip".into(),
            }),
            ins(ArmOp::Mov {
                rd: Reg::R6,
                op2: Operand2::Reg(Reg::R5),
            }),
            ins(ArmOp::Label {
                name: "skip".into(),
            }),
            ins(ArmOp::Add {
                rd: Reg::R7,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R5),
            }),
        ];
        let cfg = cfg_liveness(&seq).expect("label-form branch is analyzable");
        assert_eq!(cfg.blocks.len(), 3, "three basic blocks");
        // B0 ends in a conditional branch → two successors.
        assert_eq!(cfg.blocks[0].succ.len(), 2);
        // r5 is born in B0: live-out yes, live-in no.
        assert!(cfg.live_out[0].contains(&Reg::R5));
        assert!(
            !cfg.live_in[0].contains(&Reg::R5),
            "r5 is defined in B0, so it is not an entry input"
        );
        // Both successors see r5 live on entry.
        for &s in &cfg.blocks[0].succ {
            assert!(
                cfg.live_in[s].contains(&Reg::R5),
                "r5 must be live entering successor block {s}"
            );
        }
    }

    #[test]
    fn cfg_liveness_unconditional_branch_has_single_successor() {
        // b "join" ; <unreachable filler> ; Label "join" ; nop
        let seq = vec![
            ins(ArmOp::B {
                label: "join".into(),
            }),
            ins(ArmOp::Label {
                name: "join".into(),
            }),
            ins(ArmOp::Nop),
        ];
        let cfg = cfg_liveness(&seq).expect("unconditional label branch is analyzable");
        assert_eq!(
            cfg.blocks[0].succ.len(),
            1,
            "an unconditional branch has exactly one successor (no fallthrough)"
        );
    }

    // ---- Interference graph (interference_graph) ---------------------------

    #[test]
    fn interference_simultaneously_live_regs_interfere() {
        // movw r1,#5 ; movw r2,#7 ; add r3,r1,r2
        // r1 and r2 are both live at the add → they interfere. r3 is defined
        // when nothing else is live-out → it interferes with NOTHING (it may
        // reuse r1's or r2's register: the precision a naive graph would lose).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 5,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R3,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            }),
        ];
        let g = interference_graph(&seq).expect("analyzable");
        assert!(g.interferes(Reg::R1, Reg::R2), "r1,r2 overlap at the add");
        assert!(
            !g.interferes(Reg::R1, Reg::R3),
            "r3 is defined after r1 dies → no interference (reuse allowed)"
        );
        assert!(!g.interferes(Reg::R2, Reg::R3));
        assert_eq!(g.edge_count(), 1, "the only edge is r1—r2");
        assert_eq!(g.degree(Reg::R1), 1);
        assert_eq!(g.degree(Reg::R3), 0);
    }

    #[test]
    fn interference_sequential_reuse_does_not_interfere() {
        // movw r1,#5 ; mov r0,r1 ; movw r1,#9 ; mov r2,r1
        // The first r1 dies into r0 before r1 is redefined → the two distinct
        // live ranges of r1 don't add a self-edge, and r0/r2 never coexist.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 5,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 9,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R2,
                op2: Operand2::Reg(Reg::R1),
            }),
        ];
        let g = interference_graph(&seq).expect("analyzable");
        assert!(
            !g.interferes(Reg::R0, Reg::R2),
            "r0 and r2 have disjoint live ranges"
        );
    }

    #[test]
    fn interference_co_defs_interfere() {
        // umull r0,r1,r2,r3 — the two result registers must be distinct, so the
        // co-defined r0 and r1 interfere even though neither is otherwise live.
        let seq = vec![ins(ArmOp::Umull {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rn: Reg::R2,
            rm: Reg::R3,
        })];
        let g = interference_graph(&seq).expect("analyzable");
        assert!(
            g.interferes(Reg::R0, Reg::R1),
            "umull's rdlo and rdhi must not share a register"
        );
    }

    #[test]
    fn interference_value_live_across_a_branch_interferes_with_both_paths() {
        // r5 live across a conditional; a fresh def on each path while r5 is
        // still live must interfere with r5.
        //   movw r5,#42 ; bcc NE,"skip"
        //   mov r6,r5            (r6 defined while r5 live → interfere)
        //   Label skip ; add r7,r5,r5
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R5,
                imm16: 42,
            }),
            ins(ArmOp::Bcc {
                cond: Condition::NE,
                label: "skip".into(),
            }),
            ins(ArmOp::Mov {
                rd: Reg::R6,
                op2: Operand2::Reg(Reg::R5),
            }),
            ins(ArmOp::Label {
                name: "skip".into(),
            }),
            ins(ArmOp::Add {
                rd: Reg::R7,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R5),
            }),
        ];
        let g = interference_graph(&seq).expect("analyzable");
        // r6 is defined where r5 is still live (r5 reaches the add on the other
        // path) → they interfere.
        assert!(g.interferes(Reg::R5, Reg::R6), "r6 defined while r5 live");
    }

    #[test]
    fn interference_declines_when_liveness_declines() {
        // A call is outside the CFG scope → cfg_liveness declines → so does this.
        let seq = vec![ins(ArmOp::Bl { label: "f".into() })];
        assert_eq!(interference_graph(&seq), None);
    }

    #[test]
    fn cfg_liveness_declines_on_call_and_offset_branch() {
        // A direct call is outside the modeled (leaf-only) scope → decline.
        let with_call = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Bl { label: "f".into() }),
        ];
        assert_eq!(cfg_liveness(&with_call), None, "calls are not yet modeled");

        // A numeric-offset branch is not label-resolvable → decline.
        let with_offset = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::BOffset { offset: -2 }),
        ];
        assert_eq!(
            cfg_liveness(&with_offset),
            None,
            "numeric-offset branches are not CFG-resolvable here"
        );
    }

    // ---- Graph colouring (color_graph) -------------------------------------

    /// Assert `colour` is a valid `k`-colouring of `g`: every node has a colour
    /// in `0..k` and no edge joins two equally-coloured nodes.
    fn assert_valid_coloring(g: &InterferenceGraph, colour: &BTreeMap<Reg, usize>, k: usize) {
        for n in g.nodes() {
            let c = *colour.get(&n).expect("every node is coloured");
            assert!(c < k, "colour in range");
            for m in g.neighbors(n) {
                assert_ne!(colour[&n], colour[&m], "adjacent nodes differ");
            }
        }
    }

    fn clique(regs: &[Reg]) -> InterferenceGraph {
        let mut g = InterferenceGraph::default();
        for (i, a) in regs.iter().enumerate() {
            g.node(*a);
            for b in &regs[i + 1..] {
                g.add_edge(*a, *b);
            }
        }
        g
    }

    #[test]
    fn color_graph_empty_is_colored() {
        let g = InterferenceGraph::default();
        assert_eq!(color_graph(&g, 3), ColorResult::Colored(BTreeMap::new()));
    }

    #[test]
    fn color_graph_colors_a_path_with_two_colors() {
        // R0—R1—R2 (a path): 2-colourable (R0,R2 share, R1 differs).
        let mut g = InterferenceGraph::default();
        g.add_edge(Reg::R0, Reg::R1);
        g.add_edge(Reg::R1, Reg::R2);
        match color_graph(&g, 2) {
            ColorResult::Colored(c) => assert_valid_coloring(&g, &c, 2),
            ColorResult::Spilled(s) => panic!("path is 2-colourable, got spill {s:?}"),
        }
    }

    #[test]
    fn color_graph_k4_clique_spills_at_k3() {
        // K4 needs 4 colours; with k=3 the heuristic must report a spill.
        let g = clique(&[Reg::R0, Reg::R1, Reg::R2, Reg::R3]);
        match color_graph(&g, 3) {
            ColorResult::Spilled(s) => assert!(!s.is_empty(), "K4 is not 3-colourable"),
            ColorResult::Colored(_) => panic!("K4 cannot be 3-coloured"),
        }
    }

    #[test]
    fn color_graph_k4_clique_colors_at_k4() {
        // With enough colours, the same clique colours with all distinct values.
        let g = clique(&[Reg::R0, Reg::R1, Reg::R2, Reg::R3]);
        match color_graph(&g, 4) {
            ColorResult::Colored(c) => {
                assert_valid_coloring(&g, &c, 4);
                let distinct: BTreeSet<usize> = c.values().copied().collect();
                assert_eq!(distinct.len(), 4, "a clique uses all colours");
            }
            ColorResult::Spilled(s) => panic!("K4 is 4-colourable, got spill {s:?}"),
        }
    }

    #[test]
    fn color_graph_k0_spills_any_node() {
        let mut g = InterferenceGraph::default();
        g.node(Reg::R0);
        assert!(matches!(color_graph(&g, 0), ColorResult::Spilled(_)));
    }

    #[test]
    fn precolored_node_keeps_its_colour_and_constrains_neighbours() {
        // Triangle R0—R1—R2; pin R0 to colour 2. With k=3, R1/R2 must avoid 2
        // (and each other), so they take {0,1}.
        let g = clique(&[Reg::R0, Reg::R1, Reg::R2]);
        let pre = BTreeMap::from([(Reg::R0, 2usize)]);
        match color_graph_precolored(&g, 3, &pre) {
            ColorResult::Colored(c) => {
                assert_eq!(c[&Reg::R0], 2, "precoloured node keeps its colour");
                assert_ne!(c[&Reg::R1], 2);
                assert_ne!(c[&Reg::R2], 2);
                assert_ne!(c[&Reg::R1], c[&Reg::R2]);
            }
            ColorResult::Spilled(s) => panic!("3-colourable with the pin, got {s:?}"),
        }
    }

    #[test]
    fn precoloring_can_force_a_spill_by_exhausting_colours() {
        // R2 interferes with R0 and R1; pin R0=0, R1=1. With only k=2 colours
        // both are taken in R2's neighbourhood → R2 must spill, even though the
        // bare graph (a path) is 2-colourable without the pins.
        let mut g = InterferenceGraph::default();
        g.add_edge(Reg::R2, Reg::R0);
        g.add_edge(Reg::R2, Reg::R1);
        let pre = BTreeMap::from([(Reg::R0, 0usize), (Reg::R1, 1usize)]);
        match color_graph_precolored(&g, 2, &pre) {
            ColorResult::Spilled(s) => assert!(s.contains(&Reg::R2)),
            ColorResult::Colored(c) => panic!("R2 has no free colour, got {c:?}"),
        }
        // One more colour resolves it: R2 takes colour 2.
        match color_graph_precolored(&g, 3, &pre) {
            ColorResult::Colored(c) => assert_eq!(c[&Reg::R2], 2),
            ColorResult::Spilled(s) => panic!("k=3 leaves a free colour, got {s:?}"),
        }
    }

    #[test]
    fn color_graph_delegates_to_empty_precoloring() {
        // The plain entry point must agree with the precoloured one given no pins.
        let g = clique(&[Reg::R0, Reg::R1, Reg::R2, Reg::R3]);
        assert_eq!(
            color_graph(&g, 4),
            color_graph_precolored(&g, 4, &BTreeMap::new())
        );
    }

    // ---- Allocation verifier (verify_allocation) ---------------------------

    #[test]
    fn verify_allocation_accepts_color_graph_output() {
        // The producer and the checker must agree: any colouring color_graph
        // returns verifies clean. (Independent code paths → real cross-check.)
        for regs in [
            vec![Reg::R0, Reg::R1, Reg::R2],
            vec![Reg::R0, Reg::R1, Reg::R2, Reg::R3],
        ] {
            let g = clique(&regs);
            let k = regs.len();
            match color_graph(&g, k) {
                ColorResult::Colored(c) => {
                    assert_eq!(verify_allocation(&g, &c), Ok(()));
                }
                ColorResult::Spilled(s) => panic!("clique is k-colourable, got {s:?}"),
            }
        }
    }

    #[test]
    fn verify_allocation_rejects_interfering_same_colour() {
        // R0—R1 interfere but are both assigned colour 0 → SameColor.
        let mut g = InterferenceGraph::default();
        g.add_edge(Reg::R0, Reg::R1);
        let bad = BTreeMap::from([(Reg::R0, 0usize), (Reg::R1, 0usize)]);
        match verify_allocation(&g, &bad) {
            Err(AllocationConflict::SameColor { color, .. }) => assert_eq!(color, 0),
            other => panic!("expected SameColor, got {other:?}"),
        }
    }

    #[test]
    fn verify_allocation_rejects_unassigned_node() {
        // R1 is in the graph but missing from the assignment → Unassigned.
        let mut g = InterferenceGraph::default();
        g.add_edge(Reg::R0, Reg::R1);
        let partial = BTreeMap::from([(Reg::R0, 0usize)]);
        assert_eq!(
            verify_allocation(&g, &partial),
            Err(AllocationConflict::Unassigned(Reg::R1))
        );
    }

    // ---- Allocator driver (allocate_function) ------------------------------

    #[test]
    fn allocate_function_produces_a_valid_allocation_and_counts_remat() {
        // movw r0,#7 ; mov r1,r0 ; movw r2,#7  — r2's #7 is redundant (resident
        // in r0). The driver allocates a valid colouring and reports 1 remat
        // opportunity (the #209 const-CSE headroom).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 7,
            }),
        ];
        match allocate_function(&seq, 9, &BTreeMap::new()) {
            AllocationOutcome::Allocated {
                coloring,
                remat_opportunities,
            } => {
                let g = interference_graph(&seq).unwrap();
                assert_eq!(verify_allocation(&g, &coloring), Ok(()));
                assert_eq!(remat_opportunities, 1, "the resident #7 is CSE-able");
            }
            other => panic!("expected Allocated, got {other:?}"),
        }
    }

    #[test]
    fn peak_pressure_counts_simultaneously_live_values_not_physical_regs() {
        // movw r0,#1 ; movw r1,#2 ; movw r2,#3 ; add r3,r0,r1 ; add r4,r2,r3
        // At the third movw, v0/v1/v2 are all live → peak 3. (The point: this is
        // value pressure; physical-register reuse would not change it.)
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 2,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 3,
            }),
            ins(ArmOp::Add {
                rd: Reg::R3,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Add {
                rd: Reg::R4,
                rn: Reg::R2,
                op2: Operand2::Reg(Reg::R3),
            }),
        ];
        assert_eq!(straight_line_peak_pressure(&seq), Some(3));
        assert_eq!(function_peak_pressure(&seq), 3);
    }

    #[test]
    fn const_cse_folds_a_redundant_clamp_bound_into_the_resident_register() {
        // movw r0,#0x7e ; cmp r5,r0 ; movw r1,#0x7e ; cmp r6,r1 ; movw r1,#99
        // r1's #0x7e is redundant (r0 holds it); r1 is redefined (movw #99) so its
        // value is local → fold: drop `movw r1,#0x7e`, rewrite `cmp r6,r1`→`cmp r6,r0`.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x7e,
            }),
            ins(ArmOp::Cmp {
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 0x7e,
            }),
            ins(ArmOp::Cmp {
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 99,
            }),
        ];
        let (out, removed) = apply_const_cse(&seq);
        assert_eq!(removed, 1, "the redundant movw r1,#0x7e is dropped");
        assert_eq!(out.len(), 4);
        // The cmp on r6 now reads the resident r0.
        assert!(out.iter().any(|i| matches!(
            &i.op,
            ArmOp::Cmp {
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R0)
            }
        )));
        // The original movw r1,#0x7e is gone; the later movw r1,#99 stays.
        assert!(!out.iter().any(|i| matches!(
            &i.op,
            ArmOp::Movw {
                rd: Reg::R1,
                imm16: 0x7e
            }
        )));
        assert!(out.iter().any(|i| matches!(
            &i.op,
            ArmOp::Movw {
                rd: Reg::R1,
                imm16: 99
            }
        )));
    }

    #[test]
    fn const_cse_declines_when_resident_register_is_clobbered_before_use() {
        // movw r0,#7 ; movw r1,#7 ; movw r0,#3 (clobbers r0) ; add r2,r4,r1 ; movw r1,#9
        // r1's #7 is "resident in r0" at def, but r0 is overwritten before r1's
        // use → folding would read the wrong r0 → must NOT fold.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 7,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 3,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R4,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 9,
            }),
        ];
        let (_out, removed) = apply_const_cse(&seq);
        assert_eq!(removed, 0, "resident reg clobbered before use → no fold");
    }

    #[test]
    fn const_cse_declines_when_value_may_be_live_out_of_segment() {
        // movw r0,#7 ; movw r1,#7 ; add r2,r4,r1   (r1 never redefined → its #7
        // may be live past the segment) → conservatively do not fold.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R4,
                op2: Operand2::Reg(Reg::R1),
            }),
        ];
        let (_out, removed) = apply_const_cse(&seq);
        assert_eq!(
            removed, 0,
            "rd not redefined in segment → may be live-out → no fold"
        );
    }

    #[test]
    fn value_ranges_split_a_reused_physical_register_into_distinct_vregs() {
        // movw r1,#1 ; mov r0,r1 ; movw r1,#2 ; mov r2,r1
        // R1 holds two unrelated values → two distinct virtual registers. This
        // is the split that turns the overloaded physical-reg node (one spurious
        // spill) into separately-colourable values.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 1,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 2,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R2,
                op2: Operand2::Reg(Reg::R1),
            }),
        ];
        let ranges = straight_line_value_ranges(&seq).expect("straight-line");
        let r1_ranges: Vec<_> = ranges.iter().filter(|r| r.reg == Reg::R1).collect();
        assert_eq!(
            r1_ranges.len(),
            2,
            "R1 splits into two virtual registers (one per value)"
        );
        // First R1 range: def 0, last-used at 1 (the mov r0,r1).
        assert_eq!((r1_ranges[0].def, r1_ranges[0].last_use), (0, 1));
        // Second R1 range: def 2, last-used at 3 (the mov r2,r1).
        assert_eq!((r1_ranges[1].def, r1_ranges[1].last_use), (2, 3));
    }

    #[test]
    fn peak_pressure_unaffected_by_physical_register_reuse() {
        // The same value churned through ONE physical register has pressure 1 —
        // exactly the case the physical-register interference graph overstates.
        // movw r0,#1 ; mov r1,r0 ; movw r0,#2 ; mov r2,r0  → never >1 live at once
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 2,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R2,
                op2: Operand2::Reg(Reg::R0),
            }),
        ];
        // r0 holds two different values sequentially; peak simultaneous = 1.
        assert_eq!(straight_line_peak_pressure(&seq), Some(1));
    }

    #[test]
    fn allocate_function_declines_on_unmodeled_construct() {
        let seq = vec![ins(ArmOp::Bl { label: "f".into() })];
        assert_eq!(
            allocate_function(&seq, 9, &BTreeMap::new()),
            AllocationOutcome::Declined
        );
    }

    #[test]
    fn allocate_function_spills_when_pool_too_small() {
        // A K4 clique of registers needs 4 colours; with k=3 the driver reports
        // a spill rather than hard-failing (the whole point of VCR-RA-001).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 2,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 3,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R3,
                imm16: 4,
            }),
            // one instruction reading all four → all four simultaneously live
            ins(ArmOp::Add {
                rd: Reg::R4,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Add {
                rd: Reg::R4,
                rn: Reg::R2,
                op2: Operand2::Reg(Reg::R3),
            }),
        ];
        // k=2 cannot colour 3+ simultaneously-live values → spill, not crash.
        assert!(matches!(
            allocate_function(&seq, 2, &BTreeMap::new()),
            AllocationOutcome::NeedsSpill(_)
        ));
    }

    #[test]
    fn verify_allocation_accepts_a_nonadjacent_shared_colour() {
        // R0 and R2 do NOT interfere (a path R0—R1—R2), so they may share a
        // colour: {R0:0, R1:1, R2:0} is valid.
        let mut g = InterferenceGraph::default();
        g.add_edge(Reg::R0, Reg::R1);
        g.add_edge(Reg::R1, Reg::R2);
        let ok = BTreeMap::from([(Reg::R0, 0usize), (Reg::R1, 1usize), (Reg::R2, 0usize)]);
        assert_eq!(verify_allocation(&g, &ok), Ok(()));
    }
}
