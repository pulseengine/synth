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

/// Conservative "does `op` possibly read `reg`": precise via [`reg_effect`] when
/// modeled; a pure branch/label reads no GP register; a call (`Bl`/`Blx`/…) may
/// read the AAPCS argument registers `R0..=R3`; anything else unmodeled (`Bx`,
/// the i64-pair / FP families) is conservatively assumed to read `reg`.
fn op_may_use(op: &ArmOp, reg: Reg) -> bool {
    if let Some(e) = reg_effect(op) {
        return e.uses.contains(&reg);
    }
    use ArmOp::*;
    match op {
        Label { .. }
        | B { .. }
        | BOffset { .. }
        | BCondOffset { .. }
        | Bhs { .. }
        | Blo { .. }
        | Bcc { .. } => false,
        Bl { .. } | Blx { .. } | Call { .. } | CallIndirect { .. } => {
            matches!(reg, Reg::R0 | Reg::R1 | Reg::R2 | Reg::R3)
        }
        _ => true,
    }
}

/// Fuse `mul` + `add` into `mla` (#257): for an `Add rD, x, Reg(y)` where one
/// operand is the destination of an earlier `Mul rM, rn, rm`, the result is
/// `mla rD, rn, rm, other`, and the now-redundant `Mul` is removed. Returns the
/// rewritten stream and the number of fusions.
///
/// Soundness conditions (all checked via [`reg_effect`]; any unmodeled
/// instruction conservatively blocks a fusion across it):
///  - the mul result `rM` is **not read** anywhere after the add (its value is
///    consumed only by the add → the mul is dead once fused),
///  - between the mul and the add, `rM` and the mul inputs `rn`/`rm` are
///    **neither redefined nor** (for `rM`) **read** — so the `mla` reading
///    `rn`/`rm` at the add's position sees the same values,
///  - `rM` and the other add operand are distinct, and the mul inputs are not
///    `rM` itself.
///
/// Pure function: callers opt in. Not wired into codegen by this change.
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
            // The mul result must be read *only* by this add anywhere in the
            // function — then removing the mul and folding into the mla is sound
            // regardless of control flow. `op_may_use` is call/branch-aware
            // (calls may read R0-R3; pure branches read nothing).
            let used_elsewhere =
                (0..n).any(|k| k != j && !removed[k] && op_may_use(&instrs[k].op, rmul));
            if used_elsewhere {
                continue;
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
}
