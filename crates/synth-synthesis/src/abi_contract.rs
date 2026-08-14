//! **VCR-VER-004 — the ABI observable-contract validator.**
//!
//! # Why this module exists
//!
//! v0.53's VCR-DEC-001 lane proved BY MUTATION that emptying
//! [`crate::liveness::cfg_exit_observable`] — the exit contract the join-aware
//! graph allocator and its own CFG validator SHARE — makes the compiler emit
//! code that leaves the function's return value **in the wrong register**, and
//! that BOTH per-compilation validators accept it:
//!
//! * [`crate::liveness::validate_cfg_rewrite`] (the pass's acceptance oracle)
//!   returns `Ok`, and
//! * [`crate::liveness::validate_final_allocation`] (VCR-RA-003, the
//!   whole-function allocation validator) returns `Consistent`.
//!
//! Only *execution* caught it. Two independent-*looking* instruments, one
//! shared blind spot — the #872 shape ("a validator that shares its pass's
//! dataflow is necessary, not sufficient") one level up, and a direct
//! counterexample to the claim that per-compilation validation is an
//! independent check on the code generator.
//!
//! # The thesis
//!
//! **Independence is not obtained by writing a second checker, only by checking
//! a different WAY.** Both existing instruments reason about *liveness/dataflow
//! equations over register names*, backward, seeded from a table. Agreeing costs
//! them almost nothing, so their agreement carries little information.
//!
//! This validator is deliberately built on a different axis in four respects.
//!
//! 1. **Its obligation cannot be emptied.** The exit obligation is the AAPCS
//!    return register set ([`RETURN_CONTRACT_REGS`]) — a constant of the ABI,
//!    hard-named HERE. It is not read from `cfg_exit_observable`, not supplied
//!    by the caller, and not derived from "what either side writes". Deleting
//!    `cfg_exit_observable` outright would not change one line of this check.
//!
//! 2. **It is FORWARD, and a forward value analysis is structurally incapable of
//!    the fail-open mode that bit v0.53.** `validate_cfg_rewrite` is a backward
//!    MUST-analysis: its obligation set is a *variable*, and the empty set is a
//!    fixpoint — an empty seed means zero obligations means vacuous `Ok`. A
//!    forward symbolic evaluation always produces *exactly one* value for `R0`
//!    at each return, so there is always exactly one obligation per sink. There
//!    is no seed to shrink.
//!
//! 3. **Its evidence is a VALUE, not a name-pair.** The two existing checks can
//!    only see a wrong-register return as a *disagreement between register
//!    names* — and only if something told them to look at that name. This one
//!    computes what `R0` actually *holds*: a symbolic term rooted at the
//!    ABI-anchored entry symbols and the producing instruction indices, then
//!    asks whether the two streams' terms are the same value.
//!
//! 4. **It takes nothing from the pass.** The signature is `(orig, rewritten)`.
//!    The CFG is re-derived HERE from the label-form branch structure of BOTH
//!    streams and the two must agree — the pass never hands this checker an
//!    artifact of its own (the v0.50 join-enforcement attempt failed exactly
//!    there, and v0.53's own doc comment names it as the anti-pattern).
//!
//! # The check
//!
//! For a **renames-only** rewrite (same length, same ops modulo register
//! operands, identical control flow — all re-verified here) build, **per side
//! independently**, a value graph whose nodes are:
//!
//! ```text
//!   Init(r)      the entry value of register r      — SHARED between the sides
//!   Def(i, k)    the k-th result of instruction i    (operands: the use-values)
//!   Phi(b, n)    block b's entry value of a register (operands: preds' values)
//! ```
//!
//! `Init(r)` being one shared node per register *is* the AAPCS **parameter**
//! contract: arguments arrive in `R0`–`R3` on both sides, so a rewrite that
//! reads a parameter out of the wrong register produces a different term.
//!
//! ## Calls (VCR-DEC-001 increment 3, #896)
//!
//! A `bl`/`blx` is **not** effect-free, and treating it as one would be exactly
//! the fail-open mode this module exists to eliminate. It gets the ONE shared
//! AAPCS definition, [`crate::liveness::call_effect`] — the same
//! `defs = {R0..R3, R12, LR}` / `uses = {R0..R3}` (+ the `blx` target) that the
//! pass and `validate_cfg_rewrite` consume — deliberately reused rather than
//! restated, because two divergent call models would be a fresh instance of the
//! shared-blind-spot class this module attacks.
//!
//! In the forward walk that falls out naturally: each clobbered register is
//! rebound to a **fresh** `Def(call_i, k)` node whose operands are the *pre-call*
//! argument values, and `R4`–`R11`/`SP` flow through untouched. So
//!
//! * a call result is an opaque value, equal across the two sides exactly when
//!   the same callee was handed the same arguments — a rewrite that renames what
//!   feeds an argument is caught;
//! * a value the rewrite parked in caller-saved scratch *across* the call is
//!   rebound to the call's own node, so it can no longer bisimulate with the
//!   value the original delivers at the return — the "recoloured across a call"
//!   miscompile is caught as a **value** disagreement, without any liveness
//!   reasoning.
//!
//! The `Call`/`CallIndirect` **pseudo**-ops still decline: they expand downstream
//! into a guard + table load + `blx`, so this stream's register footprint is not
//! the final code's.
//!
//! Values are compared by **greatest-fixpoint bisimulation** (partition
//! refinement over the two graphs at once). On a deterministic term graph
//! bisimilarity is exactly equality of the infinite unfoldings, so loops and
//! back edges are handled coinductively rather than by unrolling. The obligation
//! is then, at **every** return sink:
//!
//! ```text
//!   value_rewritten(R0) ≡ value_orig(R0)   and   value_rewritten(R1) ≡ value_orig(R1)
//! ```
//!
//! # Why there is no SMT solver here
//!
//! The natural home for a value-level VC in this repo is `synth-verify`'s
//! ordeal QF_BV pipeline (the trap-preservation VC's shape). It is deliberately
//! *not* used, for two reasons that are worth stating rather than hiding:
//!
//! * **A solver would add no discrimination.** A renames-only rewrite changes no
//!   opcode and no immediate, so the two sides' terms are ground applications of
//!   the *same* uninterpreted operators. Deciding equality of such terms is
//!   congruence closure with no side conditions — i.e. exactly structural
//!   equality, which is what the refinement computes. The solver would cost a
//!   dependency and a per-function query to decide the same thing.
//! * **The dependency runs the wrong way.** `synth-verify` depends on
//!   `synth-synthesis`, not the reverse, so an in-allocator SMT gate would need
//!   the edge inverted or the check hoisted out of the pass it guards.
//!
//! The residual is recorded honestly in the module's limitations below.
//!
//! # Known limitations (named, not hidden)
//!
//! * **Memory is not in the obligation.** The contract checked is the *register*
//!   half of the ABI. A mis-renamed store address that a later load reads back is
//!   a false NEGATIVE here (the load's value node is keyed on its instruction
//!   index and address operands, not on a memory chain). That class IS covered by
//!   `validate_cfg_rewrite`'s use-equations when its seed is intact — the two
//!   instruments are complementary, which is what independence is supposed to
//!   look like. Extending the obligation to a store chain is a named follow-up.
//! * **The op model is still shared.** Def/use extraction goes through
//!   [`crate::liveness::reg_effect`], so a *mismodeled op* remains a blind spot
//!   common to all three instruments. This validator closes the shared-*contract*
//!   hole, not the shared-*op-model* hole. `synth-verify`'s
//!   `ArmSemantics::encode_op` is a genuinely second model of the same ops, and
//!   pinning the two against each other is the obvious next rung. #923 measured
//!   how second: `encode_op`'s default arm was a silent no-op covering 87 of
//!   `ArmOp`'s 222 variants (now 73, and they DECLINE instead of passing), so
//!   the second model is second for the i32/i64/VFP core and explicit about the
//!   rest.
//! * **Scope is the label-form shape.** `BrTable`, numeric-offset branches,
//!   computed `Bx`, the `Call`/`CallIndirect` pseudo-ops,
//!   duplicate/unresolvable labels and any op `reg_effect` does not model produce
//!   a loud [`AbiContractVerdict::NotAttempted`] naming the construct. There is
//!   no silent pass on a shape this cannot analyze.
//! * **A call's MEMORY effect is not modeled** — a consequence of the memory
//!   limitation above, restated because a call is where it is easiest to forget:
//!   the callee may write memory, and a later load is keyed on its instruction
//!   index and address operands rather than on a store chain. Sound for a
//!   renames-only rewrite (both sides execute the same callee at the same point);
//!   not a claim about the callee's effects.

use crate::instruction_selector::ArmInstruction;
use crate::liveness::{call_effect, is_straight_line, pair_effect, reg_effect};
use crate::rules::{ArmOp, Reg};
use std::collections::BTreeMap;

/// The AAPCS registers that carry a wasm function's result, and therefore the
/// registers whose VALUE this validator requires a rewrite to preserve at every
/// return: `R0` (an `i32`/`f32`-in-core result) and `R1` (the high half of an
/// `i64`/`f64`-in-core result — the selector's "result in (R0,R1)" convention).
///
/// **This constant is the whole point of the module.** It is the obligation
/// source, and it is a fact about the *ABI*, not about the rewrite, not about
/// the pass, and not about any table the pass also reads. Compare
/// [`crate::liveness::cfg_exit_observable`], which the v0.53 mutation emptied:
/// emptying that changed what `validate_cfg_rewrite` demanded; nothing can empty
/// this without editing this line, and editing this line is visible in review as
/// "we stopped checking the return value".
///
/// It is deliberately the CONSERVATIVE over-approximation: both result registers
/// are required for every function, because this validator is not told the
/// function's wasm result arity. Requiring `R1` of an `i32`-returning function
/// can only cost a DECLINE (the caller falls back to the shipping allocator), it
/// can never cost soundness — and on the unmutated compiler it costs nothing at
/// all, because the intact exit contract already pins both.
pub const RETURN_CONTRACT_REGS: [Reg; 2] = [Reg::R0, Reg::R1];

/// The verdict of [`validate_abi_contract`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbiContractVerdict {
    /// Every return sink delivers the same symbolic value in every ABI result
    /// register on both sides.
    Holds,
    /// At the return terminator with instruction index `sink`, ABI result
    /// register `reg` holds a DIFFERENT symbolic value after the rewrite.
    Violated { sink: usize, reg: Reg },
    /// Loud honest decline: a construct the value graph cannot model. NEVER a
    /// silent pass.
    NotAttempted { reason: &'static str },
}

impl AbiContractVerdict {
    /// True only for [`AbiContractVerdict::Violated`] — a decline is not a
    /// failure, and callers that gate on this must not treat it as one.
    pub fn is_violation(&self) -> bool {
        matches!(self, AbiContractVerdict::Violated { .. })
    }
}

/// Number of modeled core registers (`R0`–`R12`, `SP`, `LR`, `PC`).
const NREG: usize = 16;

fn reg_ix(r: Reg) -> usize {
    match r {
        Reg::R0 => 0,
        Reg::R1 => 1,
        Reg::R2 => 2,
        Reg::R3 => 3,
        Reg::R4 => 4,
        Reg::R5 => 5,
        Reg::R6 => 6,
        Reg::R7 => 7,
        Reg::R8 => 8,
        Reg::R9 => 9,
        Reg::R10 => 10,
        Reg::R11 => 11,
        Reg::R12 => 12,
        Reg::SP => 13,
        Reg::LR => 14,
        Reg::PC => 15,
    }
}

/// A basic block of the INDEPENDENTLY re-derived label-form CFG.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Blk {
    start: usize,
    end: usize,
    succ: Vec<usize>,
}

fn is_return_term(op: &ArmOp) -> bool {
    match op {
        ArmOp::Bx { rm } => *rm == Reg::LR,
        ArmOp::Pop { regs } => regs.contains(&Reg::PC),
        _ => false,
    }
}

/// How an instruction participates in the CFG.
///
/// **Every** instruction is classified, wherever it sits — not just block
/// enders. An op that merely *fails* to be a recognized branch would otherwise
/// fall through the forward walk with no register effect, which is precisely the
/// fail-open mode this module exists to eliminate: a `bl` in the middle of a
/// block destroys `R0`–`R3`/`R12` and defines `R0`, and silently modeling it as
/// a no-op would let the checker certify a rewrite it cannot see through.
enum Cf<'a> {
    /// Straight-line: [`reg_effect`] must model it.
    Straight,
    /// A direct or indirect CALL (`bl` / `blx`). Falls through like a
    /// straight-line op, but its register effect is the AAPCS
    /// [`call_effect`] rather than [`reg_effect`].
    CallOp,
    /// A `Label` — starts a block, no effect.
    Label,
    /// Unconditional branch to a label.
    Uncond(&'a str),
    /// Conditional branch to a label (fallthrough is the other successor).
    Cond(&'a str),
    /// `bx lr` — a return sink with no register effect.
    Return,
    /// Outside the analyzable label-form leaf shape: loud decline.
    Reject(&'static str),
}

fn classify(op: &ArmOp) -> Cf<'_> {
    use ArmOp::*;
    match op {
        Label { .. } => Cf::Label,
        B { label } => Cf::Uncond(label.as_str()),
        Bhs { label } | Blo { label } | Bcc { label, .. } => Cf::Cond(label.as_str()),
        BOffset { .. } | BCondOffset { .. } => Cf::Reject("numeric-offset-branch"),
        BrTable { .. } => Cf::Reject("br-table"),
        Bx { rm } if *rm == Reg::LR => Cf::Return,
        Bx { .. } => Cf::Reject("computed-branch"),
        // VCR-DEC-001 increment 3 (#896): a `bl`/`blx` is MODELED, using the ONE
        // shared AAPCS definition. Keyed on `call_effect` returning `Some`
        // rather than on a variant list, so this classifier and the pass's
        // notion of "a call this allocator may colour across" cannot drift
        // apart — two divergent call models would be a fresh instance of the
        // shared-blind-spot class this module exists to attack. The `Call` /
        // `CallIndirect` PSEUDO-ops get `None` (they expand downstream into a
        // guard + table load + `blx`, so this stream's register footprint is not
        // the final code's) and fall through to the loud declines below.
        op if call_effect(op).is_some() => Cf::CallOp,
        Bl { .. } | Call { .. } => Cf::Reject("call-pseudo-op"),
        Blx { .. } | CallIndirect { .. } => Cf::Reject("indirect-call-pseudo-op"),
        // Anything left must be straight-line; `is_straight_line` is the shared
        // predicate and this arm asserts the two classifications agree, so a new
        // control-flow variant added to `ArmOp` without a case here cannot slip
        // through as "straight-line with no effect".
        other if is_straight_line(other) => Cf::Straight,
        _ => Cf::Reject("unclassified-control-flow"),
    }
}

/// An instruction's register effect: `(defs, uses)`, in the order
/// [`reg_effect`] / [`call_effect`] report them. `None` = carries no register
/// effect at all (pure control flow).
type Effect = Option<(Vec<Reg>, Vec<Reg>)>;

/// The register effect of instruction `op`, or `None` if it carries none
/// (pure control flow: `Label` / `B` / `Bcc` / `bx lr`).
///
/// `Err` means "this checker cannot model it" — a loud decline, never a silent
/// no-effect walk-past.
fn effect_of(op: &ArmOp) -> Result<Effect, &'static str> {
    match classify(op) {
        Cf::Reject(why) => Err(why),
        Cf::Straight => reg_effect(op)
            .or_else(|| pair_effect(op))
            .map(|e| Some((e.defs, e.uses)))
            .ok_or("unmodeled-op"),
        Cf::CallOp => call_effect(op)
            .map(|e| Some((e.defs, e.uses)))
            .ok_or("unmodeled-call"),
        Cf::Label | Cf::Uncond(_) | Cf::Cond(_) | Cf::Return => Ok(None),
    }
}

/// Re-derive the label-form CFG from an instruction stream.
///
/// Built HERE rather than accepted from the caller: a validator that consumes
/// the pass's own CFG can be made vacuous by a wrong CFG (a missing edge hides a
/// path). Blocks start at index 0, at every `Label`, and immediately after every
/// branch or return. Successors come from the block's last instruction. Any
/// construct outside the label-form leaf shape is a loud decline.
fn derive_cfg(instrs: &[ArmInstruction]) -> Result<Vec<Blk>, &'static str> {
    use ArmOp::*;
    if instrs.is_empty() {
        return Err("empty-stream");
    }

    // Label name -> instruction index. Duplicates make targets ambiguous.
    let mut labels: BTreeMap<&str, usize> = BTreeMap::new();
    for (i, ins) in instrs.iter().enumerate() {
        if let Label { name } = &ins.op
            && labels.insert(name.as_str(), i).is_some()
        {
            return Err("duplicate-label");
        }
    }

    // Leaders. EVERY instruction is classified here, so an op outside the
    // analyzable shape is rejected wherever it sits — not only when it happens
    // to end a block.
    let mut is_leader = vec![false; instrs.len()];
    is_leader[0] = true;
    for (i, ins) in instrs.iter().enumerate() {
        let ends_block = match classify(&ins.op) {
            Cf::Reject(why) => return Err(why),
            Cf::Label => {
                is_leader[i] = true;
                false
            }
            Cf::Uncond(_) | Cf::Cond(_) | Cf::Return => true,
            // A call FALLS THROUGH: it does not end a basic block.
            Cf::Straight | Cf::CallOp => is_return_term(&ins.op),
        };
        if ends_block && i + 1 < instrs.len() {
            is_leader[i + 1] = true;
        }
    }
    let starts: Vec<usize> = (0..instrs.len()).filter(|&i| is_leader[i]).collect();
    let block_of: BTreeMap<usize, usize> =
        starts.iter().enumerate().map(|(b, &s)| (s, b)).collect();

    let mut blocks: Vec<Blk> = Vec::with_capacity(starts.len());
    for (b, &s) in starts.iter().enumerate() {
        let e = starts.get(b + 1).copied().unwrap_or(instrs.len());
        blocks.push(Blk {
            start: s,
            end: e,
            succ: Vec::new(),
        });
    }

    for b in 0..blocks.len() {
        let last = &instrs[blocks[b].end - 1].op;
        let fallthrough = block_of.get(&blocks[b].end).copied();
        let target = |name: &str| block_of.get(labels.get(name)?).copied();
        let succ: Vec<usize> = match classify(last) {
            Cf::Reject(why) => return Err(why),
            Cf::Uncond(l) => vec![target(l).ok_or("unresolved-label")?],
            Cf::Cond(l) => vec![
                target(l).ok_or("unresolved-label")?,
                fallthrough.ok_or("cond-branch-falls-off-end")?,
            ],
            Cf::Return => Vec::new(),
            Cf::Label | Cf::Straight | Cf::CallOp => {
                if is_return_term(last) {
                    Vec::new()
                } else {
                    vec![fallthrough.ok_or("falls-off-end")?]
                }
            }
        };
        blocks[b].succ = succ;
    }
    Ok(blocks)
}

/// A value-graph node tag. Deliberately keyed on the SHARED SKELETON (the
/// instruction index / block index), never on the side, so the two streams'
/// corresponding nodes start out assumed-equal and are split only by evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Tag {
    /// Entry value of register `r` — ONE node shared by both sides (the AAPCS
    /// parameter anchor).
    Init(u8),
    /// The `k`-th result of instruction `i`.
    Def(u32, u8),
    /// Block `b`'s entry value of some register; `n` = operand count.
    Phi(u32, u8),
}

struct Graph {
    tag: Vec<Tag>,
    ops: Vec<Vec<usize>>,
}

impl Graph {
    fn push(&mut self, tag: Tag, ops: Vec<usize>) -> usize {
        self.tag.push(tag);
        self.ops.push(ops);
        self.tag.len() - 1
    }
}

/// Prove that a renames-only rewrite preserves the ABI observable contract.
///
/// Takes ONLY the two instruction streams — no CFG, no live-out set, no seed
/// from the caller. See the module documentation for the independence argument.
pub fn validate_abi_contract(
    orig: &[ArmInstruction],
    rewritten: &[ArmInstruction],
) -> AbiContractVerdict {
    use AbiContractVerdict::*;

    if orig.len() != rewritten.len() {
        return NotAttempted {
            reason: "length-mismatch",
        };
    }
    if orig.is_empty() {
        return NotAttempted {
            reason: "empty-stream",
        };
    }

    // ---- The CFG, re-derived from BOTH streams; they must agree ----------
    let blocks = match derive_cfg(orig) {
        Ok(b) => b,
        Err(reason) => return NotAttempted { reason },
    };
    match derive_cfg(rewritten) {
        Ok(b) if b == blocks => {}
        Ok(_) => {
            return NotAttempted {
                reason: "control-flow-rewritten",
            };
        }
        Err(reason) => return NotAttempted { reason },
    }

    // ---- Renames-only precondition, re-checked here ----------------------
    // Control flow AND calls must be literally identical (a register allocator
    // renames operands; it never rewrites control flow, and — the increment-3
    // rule `validate_cfg_rewrite` also enforces — never rewrites a call's
    // architectural operands, `blx`'s target register included). Every
    // straight-line pair must be the same operation with matching def/use arity.
    let mut eff: Vec<Effect> = Vec::with_capacity(orig.len());
    let mut eff_r: Vec<Effect> = Vec::with_capacity(orig.len());
    for (o, r) in orig.iter().zip(rewritten) {
        if !is_straight_line(&o.op) || !is_straight_line(&r.op) {
            if o.op != r.op {
                return NotAttempted {
                    reason: "control-flow-rewritten",
                };
            }
            // Identical ops, so the SAME effect twice — and for a `bl`/`blx`
            // that effect is the AAPCS clobber, not nothing.
            let e = match effect_of(&o.op) {
                Ok(e) => e,
                Err(reason) => return NotAttempted { reason },
            };
            eff.push(e.clone());
            eff_r.push(e);
            continue;
        }
        // VCR-REACH-001 (increment 4, #242): an i64 register-PAIR pseudo-op is
        // straight-line with no `reg_effect` (deliberately — the shipping
        // pipeline depends on that `None`) but a modeled [`pair_effect`]. This
        // validator must see it, and must see it through the SAME definition:
        // its `NotAttempted` counts as a DECLINE at the `abi_gate`, so leaving
        // it out here would not be "safe", it would silently switch the
        // instrument OFF for the whole family this increment exists to reach —
        // and a check that declines everything is the vacuity failure this
        // module was written to prevent.
        let (Some(eo), Some(er)) = (
            reg_effect(&o.op).or_else(|| pair_effect(&o.op)),
            reg_effect(&r.op).or_else(|| pair_effect(&r.op)),
        ) else {
            return NotAttempted {
                reason: "unmodeled-op",
            };
        };
        if eo.defs.len() != er.defs.len() || eo.uses.len() != er.uses.len() {
            return NotAttempted {
                reason: "shape-mismatch",
            };
        }
        eff.push(Some((eo.defs, eo.uses)));
        eff_r.push(Some((er.defs, er.uses)));
    }

    // ---- Predecessors -----------------------------------------------------
    let nb = blocks.len();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); nb];
    for (b, blk) in blocks.iter().enumerate() {
        for &s in &blk.succ {
            if s >= nb {
                return NotAttempted {
                    reason: "bad-cfg-edge",
                };
            }
            preds[s].push(b);
        }
    }

    // ---- Build the value graph -------------------------------------------
    let mut g = Graph {
        tag: Vec::new(),
        ops: Vec::new(),
    };
    // Entry symbols: ONE node per register, SHARED by both sides.
    let init: Vec<usize> = (0..NREG)
        .map(|r| g.push(Tag::Init(r as u8), Vec::new()))
        .collect();

    // Phi placeholders, per side / block / register.
    // side 0 = orig, side 1 = rewritten.
    let mut phi = [
        vec![[0usize; NREG]; nb], // orig
        vec![[0usize; NREG]; nb], // rewritten
    ];
    for b in 0..nb {
        let n_ops = preds[b].len() + usize::from(b == 0);
        if n_ops > u8::MAX as usize {
            return NotAttempted {
                reason: "phi-arity",
            };
        }
        for item in phi.iter_mut() {
            for slot in item[b].iter_mut() {
                *slot = g.push(Tag::Phi(b as u32, n_ops as u8), Vec::new());
            }
        }
    }

    // Forward walk, per side, per block.
    let mut out = [vec![[0usize; NREG]; nb], vec![[0usize; NREG]; nb]];
    for side in 0..2 {
        let effects = if side == 0 { &eff } else { &eff_r };
        for (b, blk) in blocks.iter().enumerate() {
            let mut env = phi[side][b];
            // The effect vector is total: `None` means "carries no register
            // effect" and is reached ONLY for pure control flow
            // (`Label`/`B`/`Bcc`/`bx lr`), because `effect_of` turned every
            // other unmodeled shape into a decline above. A `bl`/`blx` is
            // `Some(call_effect)`, so it is NEVER walked past as a no-op — its
            // clobbered registers get FRESH nodes below and its callee-saved
            // registers flow through untouched.
            for (i, e) in effects.iter().enumerate().take(blk.end).skip(blk.start) {
                let Some((defs, uses)) = e else {
                    continue;
                };
                let operands: Vec<usize> = uses.iter().map(|u| env[reg_ix(*u)]).collect();
                for (k, d) in defs.iter().enumerate() {
                    if k > u8::MAX as usize {
                        return NotAttempted {
                            reason: "def-arity",
                        };
                    }
                    let n = g.push(Tag::Def(i as u32, k as u8), operands.clone());
                    env[reg_ix(*d)] = n;
                }
            }
            out[side][b] = env;
        }
    }

    // Wire the phi operands now that every block's exit state is known.
    for b in 0..nb {
        for side in 0..2 {
            for r in 0..NREG {
                let mut o: Vec<usize> = Vec::with_capacity(preds[b].len() + 1);
                if b == 0 {
                    o.push(init[r]);
                }
                for &p in &preds[b] {
                    o.push(out[side][p][r]);
                }
                let id = phi[side][b][r];
                g.ops[id] = o;
            }
        }
    }

    // ---- Greatest-fixpoint bisimulation (partition refinement) -----------
    //
    // Start from the coarsest partition consistent with the tags (so the two
    // sides' corresponding nodes are assumed EQUAL) and split whenever two
    // nodes' operand classes differ. Refinement only ever splits, the class
    // count is bounded by the node count, so this terminates; the limit is the
    // coarsest stable partition, i.e. the greatest bisimulation. On a
    // deterministic term graph that is exactly equality of the infinite
    // unfoldings — which is why back edges need no unrolling.
    let n = g.tag.len();
    let mut class: Vec<usize> = {
        let mut ids: BTreeMap<Tag, usize> = BTreeMap::new();
        g.tag
            .iter()
            .map(|t| {
                let next = ids.len();
                *ids.entry(*t).or_insert(next)
            })
            .collect()
    };
    let mut n_classes = class.iter().copied().max().map_or(0, |m| m + 1);
    for _ in 0..=n {
        let mut sigs: BTreeMap<(usize, Vec<usize>), usize> = BTreeMap::new();
        let mut next_class = vec![0usize; n];
        for (i, next_item) in next_class.iter_mut().enumerate() {
            let key = (
                class[i],
                g.ops[i].iter().map(|&o| class[o]).collect::<Vec<_>>(),
            );
            let next = sigs.len();
            *next_item = *sigs.entry(key).or_insert(next);
        }
        class = next_class;
        if sigs.len() == n_classes {
            break;
        }
        n_classes = sigs.len();
    }

    // ---- The obligation: the AAPCS result registers, at every return -----
    let mut sinks = 0usize;
    for (b, blk) in blocks.iter().enumerate() {
        if !blk.succ.is_empty() {
            continue;
        }
        let term = &orig[blk.end - 1].op;
        if !is_return_term(term) {
            return NotAttempted {
                reason: "unrecognized-return",
            };
        }
        // A return terminator that itself WRITES a result register would make
        // the comparison read a value this model does not track (a `pop` loads
        // from the stack, which is outside the register value graph) — that
        // would be a silent vacuous pass, so decline instead.
        if let ArmOp::Pop { regs } = term
            && regs.iter().any(|r| RETURN_CONTRACT_REGS.contains(r))
        {
            return NotAttempted {
                reason: "return-restores-result-register",
            };
        }
        sinks += 1;
        for reg in RETURN_CONTRACT_REGS {
            let lo = out[0][b][reg_ix(reg)];
            let hi = out[1][b][reg_ix(reg)];
            if class[lo] != class[hi] {
                return Violated {
                    sink: blk.end - 1,
                    reg,
                };
            }
        }
    }
    if sinks == 0 {
        // No reachable return at all: nothing to certify. A vacuous `Holds`
        // here would be exactly the failure this module exists to prevent.
        return NotAttempted {
            reason: "no-return-sink",
        };
    }

    Holds
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::{Condition, MemAddr, Operand2, VfpReg};

    fn ins(op: ArmOp) -> ArmInstruction {
        ArmInstruction {
            op,
            source_line: None,
        }
    }

    fn mov(rd: Reg, rm: Reg) -> ArmInstruction {
        ins(ArmOp::Mov {
            rd,
            op2: Operand2::Reg(rm),
        })
    }

    fn movw(rd: Reg, imm16: u16) -> ArmInstruction {
        ins(ArmOp::Movw { rd, imm16 })
    }

    fn add(rd: Reg, rn: Reg, rm: Reg) -> ArmInstruction {
        ins(ArmOp::Add {
            rd,
            rn,
            op2: Operand2::Reg(rm),
        })
    }

    fn label(n: &str) -> ArmInstruction {
        ins(ArmOp::Label {
            name: n.to_string(),
        })
    }

    fn bx_lr() -> ArmInstruction {
        ins(ArmOp::Bx { rm: Reg::LR })
    }

    // ---- straight-line ---------------------------------------------------

    #[test]
    fn identity_rewrite_holds() {
        let s = vec![add(Reg::R0, Reg::R0, Reg::R1), bx_lr()];
        assert_eq!(validate_abi_contract(&s, &s), AbiContractVerdict::Holds);
    }

    #[test]
    fn renaming_a_dead_temp_holds() {
        // r2 is a scratch; renaming it to r3 must not disturb the contract.
        let o = vec![movw(Reg::R2, 7), add(Reg::R0, Reg::R0, Reg::R2), bx_lr()];
        let r = vec![movw(Reg::R3, 7), add(Reg::R0, Reg::R0, Reg::R3), bx_lr()];
        assert_eq!(validate_abi_contract(&o, &r), AbiContractVerdict::Holds);
    }

    #[test]
    fn result_left_in_the_wrong_register_is_violated() {
        // The v0.53 class, minimal: the sum lands in r4 instead of r0.
        let o = vec![add(Reg::R0, Reg::R0, Reg::R1), bx_lr()];
        let r = vec![add(Reg::R4, Reg::R0, Reg::R1), bx_lr()];
        assert_eq!(
            validate_abi_contract(&o, &r),
            AbiContractVerdict::Violated {
                sink: 1,
                reg: Reg::R0
            }
        );
    }

    #[test]
    fn reading_a_parameter_from_the_wrong_register_is_violated() {
        // The AAPCS parameter half of the anchor: `Init(R1)` and `Init(R0)` are
        // distinct shared symbols, so swapping the source is a value change.
        let o = vec![mov(Reg::R0, Reg::R1), bx_lr()];
        let r = vec![mov(Reg::R0, Reg::R2), bx_lr()];
        assert_eq!(
            validate_abi_contract(&o, &r),
            AbiContractVerdict::Violated {
                sink: 1,
                reg: Reg::R0
            }
        );
    }

    #[test]
    fn high_half_of_an_i64_result_is_in_the_contract() {
        let o = vec![movw(Reg::R1, 9), bx_lr()];
        let r = vec![movw(Reg::R5, 9), bx_lr()];
        assert_eq!(
            validate_abi_contract(&o, &r),
            AbiContractVerdict::Violated {
                sink: 1,
                reg: Reg::R1
            }
        );
    }

    // ---- across a join ---------------------------------------------------

    fn ifelse(then_dst: Reg, else_dst: Reg, join_src: Reg) -> Vec<ArmInstruction> {
        vec![
            ins(ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            }),
            ins(ArmOp::Bcc {
                cond: Condition::EQ,
                label: ".Lelse".to_string(),
            }),
            movw(then_dst, 1),
            ins(ArmOp::B {
                label: ".Ljoin".to_string(),
            }),
            label(".Lelse"),
            movw(else_dst, 2),
            label(".Ljoin"),
            mov(Reg::R0, join_src),
            bx_lr(),
        ]
    }

    #[test]
    fn consistent_cross_arm_rename_across_a_join_holds() {
        let o = ifelse(Reg::R4, Reg::R4, Reg::R4);
        let r = ifelse(Reg::R6, Reg::R6, Reg::R6);
        assert_eq!(validate_abi_contract(&o, &r), AbiContractVerdict::Holds);
    }

    #[test]
    fn one_armed_rename_across_a_join_is_violated() {
        // Only the THEN arm is renamed: on the else path r6 is not the value the
        // join consumes. A straight-line walk structurally cannot see this.
        let o = ifelse(Reg::R4, Reg::R4, Reg::R4);
        let r = ifelse(Reg::R6, Reg::R4, Reg::R6);
        assert_eq!(
            validate_abi_contract(&o, &r),
            AbiContractVerdict::Violated {
                sink: 8,
                reg: Reg::R0
            }
        );
    }

    // ---- loops (coinduction, no unrolling) --------------------------------

    fn counted_loop(acc: Reg) -> Vec<ArmInstruction> {
        vec![
            movw(acc, 0),
            label(".Lhead"),
            ins(ArmOp::Add {
                rd: acc,
                rn: acc,
                op2: Operand2::Imm(1),
            }),
            ins(ArmOp::Sub {
                rd: Reg::R1,
                rn: Reg::R1,
                op2: Operand2::Imm(1),
            }),
            ins(ArmOp::Cmp {
                rn: Reg::R1,
                op2: Operand2::Imm(0),
            }),
            ins(ArmOp::Bcc {
                cond: Condition::NE,
                label: ".Lhead".to_string(),
            }),
            mov(Reg::R0, acc),
            bx_lr(),
        ]
    }

    #[test]
    fn loop_carried_rename_holds_by_coinduction() {
        let o = counted_loop(Reg::R4);
        let r = counted_loop(Reg::R7);
        assert_eq!(validate_abi_contract(&o, &r), AbiContractVerdict::Holds);
    }

    #[test]
    fn loop_result_left_in_the_wrong_register_is_violated() {
        let o = counted_loop(Reg::R4);
        let mut r = counted_loop(Reg::R4);
        // Return the loop COUNTER instead of the accumulator.
        r[6] = mov(Reg::R0, Reg::R1);
        assert_eq!(
            validate_abi_contract(&o, &r),
            AbiContractVerdict::Violated {
                sink: 7,
                reg: Reg::R0
            }
        );
    }

    // ---- loud declines, never a silent pass -------------------------------

    // ---- calls (VCR-DEC-001 increment 3, #896) ---------------------------

    fn bl(f: &str) -> ArmInstruction {
        ins(ArmOp::Bl {
            label: f.to_string(),
        })
    }

    /// `held` carries a value across a call, then it is returned:
    ///   movw held,#7 ; bl f ; mov r0,held ; bx lr
    fn across_call(held: Reg) -> Vec<ArmInstruction> {
        vec![movw(held, 7), bl("f"), mov(Reg::R0, held), bx_lr()]
    }

    #[test]
    fn a_call_is_modeled_not_declined() {
        let s = across_call(Reg::R4);
        assert_eq!(validate_abi_contract(&s, &s), AbiContractVerdict::Holds);
    }

    #[test]
    fn recolouring_a_callee_saved_value_to_another_callee_saved_holds() {
        let o = across_call(Reg::R4);
        let r = across_call(Reg::R7);
        assert_eq!(validate_abi_contract(&o, &r), AbiContractVerdict::Holds);
    }

    #[test]
    fn recolouring_a_live_value_into_caller_saved_across_a_call_is_violated() {
        // THE miscompile increment 3 must not commit: the value is parked in
        // R2, which the AAPCS destroys at the call. The forward walk rebinds R2
        // to the CALL's own node, so it can no longer bisimulate with the
        // original's `movw` — caught as a VALUE disagreement, with no liveness
        // reasoning anywhere.
        let o = across_call(Reg::R4);
        let r = across_call(Reg::R2);
        assert_eq!(
            validate_abi_contract(&o, &r),
            AbiContractVerdict::Violated {
                sink: 3,
                reg: Reg::R0
            }
        );
    }

    #[test]
    fn returning_the_call_result_directly_holds() {
        // r0 after `bl` is the callee's result on both sides.
        let s = vec![bl("f"), bx_lr()];
        assert_eq!(validate_abi_contract(&s, &s), AbiContractVerdict::Holds);
    }

    #[test]
    fn renaming_what_feeds_a_call_argument_is_violated() {
        // Same callee, DIFFERENT argument value ⇒ the result node's operands
        // differ ⇒ the returned value differs. `call_effect`'s `uses` are what
        // make this visible; without them the two calls would look identical.
        let o = vec![mov(Reg::R0, Reg::R4), bl("f"), bx_lr()];
        let r = vec![mov(Reg::R0, Reg::R5), bl("f"), bx_lr()];
        assert_eq!(
            validate_abi_contract(&o, &r),
            AbiContractVerdict::Violated {
                sink: 2,
                reg: Reg::R0
            }
        );
    }

    #[test]
    fn a_rewritten_call_target_declines_loudly() {
        // A register allocator never rewrites a call's architectural operands —
        // the rule `validate_cfg_rewrite` enforces too. A stream where one did
        // must decline, not be analyzed under the shared-skeleton assumption.
        let o = vec![bl("f"), bx_lr()];
        let r = vec![bl("g"), bx_lr()];
        assert_eq!(
            validate_abi_contract(&o, &r),
            AbiContractVerdict::NotAttempted {
                reason: "control-flow-rewritten"
            }
        );
    }

    #[test]
    fn the_call_pseudo_op_still_declines_loudly() {
        // `Call` expands downstream into a guard + table load + `blx`, so this
        // stream's register footprint is not the final code's.
        let s = vec![
            ins(ArmOp::Call {
                rd: Reg::R0,
                func_idx: 3,
            }),
            bx_lr(),
        ];
        assert_eq!(
            validate_abi_contract(&s, &s),
            AbiContractVerdict::NotAttempted {
                reason: "call-pseudo-op"
            }
        );
    }

    #[test]
    fn a_rewritten_branch_declines_loudly() {
        let o = ifelse(Reg::R4, Reg::R4, Reg::R4);
        let mut r = o.clone();
        r[1] = ins(ArmOp::Bcc {
            cond: Condition::NE,
            label: ".Lelse".to_string(),
        });
        assert_eq!(
            validate_abi_contract(&o, &r),
            AbiContractVerdict::NotAttempted {
                reason: "control-flow-rewritten"
            }
        );
    }

    #[test]
    fn an_endless_loop_with_no_return_declines_rather_than_passing() {
        let s = vec![
            label(".Lhead"),
            ins(ArmOp::B {
                label: ".Lhead".to_string(),
            }),
        ];
        assert_eq!(
            validate_abi_contract(&s, &s),
            AbiContractVerdict::NotAttempted {
                reason: "no-return-sink"
            }
        );
    }

    #[test]
    fn a_pop_that_restores_a_result_register_declines_rather_than_passing() {
        let s = vec![
            ins(ArmOp::Push {
                regs: vec![Reg::R0, Reg::LR],
            }),
            ins(ArmOp::Pop {
                regs: vec![Reg::R0, Reg::PC],
            }),
        ];
        assert_eq!(
            validate_abi_contract(&s, &s),
            AbiContractVerdict::NotAttempted {
                reason: "return-restores-result-register"
            }
        );
    }

    #[test]
    fn a_normal_prologue_epilogue_is_analyzed_not_declined() {
        let s = vec![
            ins(ArmOp::Push {
                regs: vec![Reg::R4, Reg::LR],
            }),
            add(Reg::R0, Reg::R0, Reg::R1),
            ins(ArmOp::Pop {
                regs: vec![Reg::R4, Reg::PC],
            }),
        ];
        assert_eq!(validate_abi_contract(&s, &s), AbiContractVerdict::Holds);
    }

    #[test]
    fn an_unmodeled_straight_line_op_declines_loudly() {
        // An FP op is straight-line but has no `reg_effect` model. It must
        // DECLINE, not be walked past as a no-op.
        let s = vec![
            ins(ArmOp::F32Add {
                sd: VfpReg::S0,
                sn: VfpReg::S1,
                sm: VfpReg::S2,
            }),
            add(Reg::R0, Reg::R0, Reg::R1),
            bx_lr(),
        ];
        assert_eq!(
            validate_abi_contract(&s, &s),
            AbiContractVerdict::NotAttempted {
                reason: "unmodeled-op"
            }
        );
    }

    #[test]
    fn an_unanalyzable_op_in_the_middle_of_a_block_declines() {
        // The fail-open bug this module's own red-first testing found: a `bl`
        // that is not a block ENDER must still be rejected. Modeling it as a
        // no-op would hide the AAPCS clobber of R0-R3/R12 — the same
        // "unmodeled construct silently certified" shape as #872.
        let s = vec![
            add(Reg::R0, Reg::R0, Reg::R1),
            ins(ArmOp::BrTable {
                rd: Reg::R0,
                index_reg: Reg::R1,
                targets: vec![],
                default: 0,
            }),
            add(Reg::R0, Reg::R0, Reg::R1),
            bx_lr(),
        ];
        assert_eq!(
            validate_abi_contract(&s, &s),
            AbiContractVerdict::NotAttempted { reason: "br-table" }
        );
    }

    #[test]
    fn a_length_mismatch_declines() {
        let o = vec![add(Reg::R0, Reg::R0, Reg::R1), bx_lr()];
        let r = vec![bx_lr()];
        assert_eq!(
            validate_abi_contract(&o, &r),
            AbiContractVerdict::NotAttempted {
                reason: "length-mismatch"
            }
        );
    }

    #[test]
    fn a_store_only_rewrite_is_a_named_false_negative() {
        // DOCUMENTED LIMITATION, pinned so it cannot drift silently: memory is
        // not in the obligation, so a mis-renamed store address that no register
        // value depends on is invisible here. `validate_cfg_rewrite`'s
        // use-equations cover this class when its seed is intact — the two
        // instruments are COMPLEMENTARY, which is what independence looks like.
        let st = |base: Reg| {
            ins(ArmOp::Str {
                rd: Reg::R0,
                addr: MemAddr {
                    base,
                    offset: 4,
                    offset_reg: None,
                },
            })
        };
        let o = vec![st(Reg::R11), bx_lr()];
        let r = vec![st(Reg::R10), bx_lr()];
        assert_eq!(validate_abi_contract(&o, &r), AbiContractVerdict::Holds);
    }
}
