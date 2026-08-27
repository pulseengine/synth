//! VCR-DEC-001 — whole-function graph-colouring register allocator SPIKE.
//!
//! **The North Star, first foothold.** synth's shipping register allocator is a
//! greedy single-pass component (`optimizer_bridge::ir_to_arm_impl`) plus the
//! verified segment-based re-allocation pass (`liveness::reallocate_function`).
//! The whole VCR program (epic #242) exists to REPLACE the greedy allocator with
//! a from-construction-correct one. This module is the bounded first increment of
//! that replacement: a Chaitin/Briggs graph-colouring allocator built AGAINST the
//! acceptance oracles the verified path already runs, so any code it emits is
//! provably allocation-sound.
//!
//! **Flag-gated, decline-to-shipping.** Everything here fires only under
//! `SYNTH_GRAPH_ALLOC=1`. With the flag unset the shipping path is byte-for-byte
//! untouched (the caller never calls into this module) — the GOLDEN trick: the
//! frozen fixtures stay bit-identical. When the flag is set and this allocator
//! cannot handle a function within its bounded scope, it returns `None` and the
//! caller falls back to the shipping `reallocate_function` — never a hard-fail.
//!
//! **Increment 1 (v0.50) — whole straight-line functions.** A function whose
//! entire body is one straight-line segment (no branches, no calls, no i64-pair /
//! FP ops — anything [`crate::liveness::straight_line_value_ranges`] or
//! [`crate::liveness::reg_effect`] declines) is coloured as a SINGLE
//! whole-function interference graph over the R0-R8 pool, with segment inputs and
//! live-outs pinned to their incoming/outgoing registers and reserved registers
//! (R9-R12) identity-assigned. Tried FIRST and left bit-for-bit as it shipped.
//!
//! **Increment 2 (v0.53) — colouring ACROSS if/else joins.** The `joins`
//! submodule builds the function's label-form CFG, splits each register's def-use
//! chains into cross-block *webs* (a reaching-def fixpoint), takes interference
//! from CFG liveness and colours the whole branchy function at once — so two
//! arms' values, never simultaneously live, share one register. See that module's
//! own docs for the scope (label-form branches; no pre-resolved numeric branches)
//! and for why each exclusion is a DECLINE rather than a guess.
//!
//! **Increment 3 (v0.54) — colouring ACROSS CALLS.** Increment 2's biggest
//! decline bucket after unmodeled ops was `call` / `call-indirect` (68 of the
//! measured corpus): a `bl` had no modeled effect, so the CFG builder refused the
//! whole function. Increment 3 models the AAPCS call boundary — ONE definition,
//! [`crate::liveness::call_effect`], consumed by BOTH this pass (liveness,
//! interference, identity pins) and its oracle
//! ([`crate::liveness::validate_cfg_rewrite`]'s backward transfer). Modeling it
//! in the pass alone would have been the #872 defect verbatim: a validator that
//! treats `bl` as effect-free accepts a non-identity equation across it, i.e. it
//! certifies its own pass's "live value parked in call-clobbered scratch"
//! miscompile. Single-block functions containing a call are taken here too
//! (increment 1 structurally cannot, since a call is not `is_straight_line`).
//! Still declined, by name: the high-level `Call` / `CallIndirect` PSEUDO-ops
//! (expanded downstream, so their final register footprint is not this stream's).
//!
//! **The oracle IS the point (red-first).** A straight-line rewrite is proven
//! semantics-preserving by [`crate::liveness::validate_segment_rewrite`] (the
//! Rideau/Leroy pairwise trace-equality validator — the SAME acceptance gate
//! `reallocate_function` uses); a branchy one by
//! [`crate::liveness::validate_cfg_rewrite`], the same argument lifted to a
//! backward must-fixpoint over the CFG. A rewrite either validator rejects is
//! dropped and the function declines. Downstream, the unconditional VCR-RA-003
//! [`crate::liveness::validate_final_allocation`] re-checks the final stream
//! through an INDEPENDENTLY written CFG builder.
//!
//! **And the dataflow validators are not sufficient.** `validate_cfg_rewrite`
//! shares the CFG shape AND the exit contract with the pass it validates, so —
//! #872's standing lesson — it cannot catch an error in what they share. v0.53
//! measured exactly what that costs: emptying [`crate::liveness::cfg_exit_observable`]
//! emits code that leaves the return value in the wrong register, and BOTH
//! `validate_cfg_rewrite` and VCR-RA-003 accept it. Increment 2's divergent bytes
//! are therefore also EXECUTED against wasmtime by
//! `scripts/repro/vcr_dec_001_join_alloc_execution_differential.py`.
//!
//! **VCR-VER-004 (v0.54) closes that specific hole statically.** Every rewrite
//! this module emits must ALSO satisfy
//! [`crate::abi_contract::validate_abi_contract`] — a forward, value-level check
//! whose obligation is the AAPCS result registers rather than a table the pass
//! reads, and which takes NOTHING from this pass (not the CFG, not a seed). Its
//! `NotAttempted` is treated as a DECLINE here, not as a pass: a function this
//! module applies to has been ABI-contract-certified, or it was not applied.

use crate::abi_contract::{AbiContractVerdict, validate_abi_contract};
use crate::instruction_selector::ArmInstruction;
use crate::liveness::{
    apply_range_coloring, is_straight_line, range_interference, reg_effect, rewrite_op_maps,
    straight_line_value_ranges, validate_segment_rewrite,
};
use crate::rules::{ArmOp, Reg};
use std::collections::{BTreeMap, BTreeSet};

/// Cap on the 10^loop_depth occurrence weight (10^4 = a 4-deep nest; deeper
/// nests saturate so a pathological CFG cannot overflow the u64 sums).
const MAX_LOOP_DEPTH_EXP: u32 = 4;

/// The classic Chaitin frequency estimate — 10 per loop-nesting level —
/// applied to MEASURED bytes rather than occurrence counts.
fn loop_weight(depth: u32) -> u64 {
    10u64.pow(depth.min(MAX_LOOP_DEPTH_EXP))
}

/// The caller-saved prefix of the pool (R0-R3): the registers a value can
/// move INTO for free, because they need no prologue save. The tie-break
/// input of [`color_webs_costed`].
fn caller_saved_prefix(pool: &[Reg]) -> usize {
    pool.iter()
        .take_while(|r| matches!(r, Reg::R0 | Reg::R1 | Reg::R2 | Reg::R3))
        .count()
}

/// The VCR-VER-004 acceptance gate, applied on top of whichever dataflow
/// validator the caller already discharged.
///
/// Returns the rewrite only if the ABI observable contract is PROVEN preserved.
/// A [`AbiContractVerdict::NotAttempted`] is a decline, deliberately: if a
/// decline counted as acceptance, a change that made this check universally
/// inapplicable would disable it silently — the vacuity failure this whole lane
/// exists to prevent.
fn abi_gate(orig: &[ArmInstruction], new: Vec<ArmInstruction>) -> Option<Vec<ArmInstruction>> {
    match validate_abi_contract(orig, &new) {
        AbiContractVerdict::Holds => Some(new),
        v => {
            if std::env::var("SYNTH_GRAPH_ALLOC_STATS").is_ok() {
                eprintln!(
                    "[graph-alloc] REJECTED by the ABI observable contract (VCR-VER-004): {v:?}"
                );
            }
            None
        }
    }
}

/// The `ArmOp` variant name, derived from `Debug` rather than a match table
/// (the same no-second-source-of-truth choice as `wcet::op_mnemonic`): a new
/// variant gets a correct census name for free, and nothing can drift.
fn variant_name(op: &crate::rules::ArmOp) -> String {
    let s = format!("{op:?}");
    s.split([' ', '{', '(']).next().unwrap_or("").to_string()
}

/// Is `SYNTH_GRAPH_ALLOC` enabled? Any value other than `0` turns the spike on;
/// unset or `0` keeps the shipping path (byte-identical).
pub fn enabled() -> bool {
    std::env::var("SYNTH_GRAPH_ALLOC").is_ok_and(|v| v != "0")
}

/// Whole-function graph-colouring re-allocation of `instrs` over `pool`
/// (the R0-R8 allocatable set), or `None` to DECLINE (the caller keeps the
/// shipping path). Declines whenever the function is not a single whole-function
/// straight-line segment, the colouring spills, the independent edge re-check
/// fails, or the trace-equality validator rejects the rewrite. A `Some` result is
/// a rewrite PROVEN to preserve the function's dataflow.
///
/// This is the surgical entry point the flag-gated hook calls in place of
/// `reallocate_function` step 1; the caller's later prologue / dead-frame passes
/// run on the output unchanged (so a value homed in R4-R8 still gets its
/// callee-saved push — the invariant VCR-RA-003 guards).
pub fn reallocate(
    instrs: &[ArmInstruction],
    pool: &[Reg],
    enc: &dyn Fn(&ArmOp) -> Option<usize>,
) -> Option<Vec<ArmInstruction>> {
    if std::env::var("SYNTH_GRAPH_ALLOC_DUMP").is_ok() {
        eprintln!("[ga-dump] ---- function, {} instrs ----", instrs.len());
        for (i, ins) in instrs.iter().enumerate() {
            eprintln!("[ga-dump] {i:3}: {:?}", ins.op);
        }
    }
    // INCREMENT 1 (v0.50) — whole straight-line functions, tried FIRST.
    if let Some(out) = reallocate_straight_line(instrs, pool, enc) {
        return Some(out);
    }
    // INCREMENT 2 (v0.53, this lane) — colour ACROSS if/else joins.
    joins::reallocate_across_joins(instrs, pool, enc)
}

/// Increment 1: the whole-straight-line-function colouring. Since RQ-60-RACOST
/// increment 2 its select is priced by `enc` — the caller-supplied REAL
/// encoder — instead of being cost-blind.
fn reallocate_straight_line(
    instrs: &[ArmInstruction],
    pool: &[Reg],
    enc: &dyn Fn(&ArmOp) -> Option<usize>,
) -> Option<Vec<ArmInstruction>> {
    // BOUNDED SCOPE: the whole function must be ONE straight-line segment. Any
    // control-flow / call / unmodeled op → decline (increment 2 below takes the
    // branchy ones; anything neither handles falls back to the shipping path).
    if instrs.is_empty() {
        return None;
    }
    for ins in instrs {
        if !is_straight_line(&ins.op) || reg_effect(&ins.op).is_none() {
            return None;
        }
    }

    // Diagnostics only (flag-gated, stderr): increment 1 declines SILENTLY, so
    // every straight-line function it refuses surfaces downstream as an opaque
    // `single-block` — the RQ-59-REACH census found that bucket had quietly
    // become the LARGEST reach failure while carrying no sub-reason at all.
    // Name the reason at each post-prescan decline point so the histogram can
    // say WHAT limits increment 1 (spill? validator? no ranges?), the same
    // "never mistake 'did nothing' for 'nothing to do'" rule as `decline()`.
    let sub = |reason: &str| {
        if std::env::var("SYNTH_GRAPH_ALLOC_STATS").is_ok() {
            eprintln!("[graph-alloc] increment-1 declined: {reason}");
        }
    };

    let Some(ranges) = straight_line_value_ranges(instrs) else {
        sub("no-value-ranges");
        return None;
    };
    if ranges.is_empty() {
        sub("no-value-ranges");
        return None;
    }

    let pool_index: BTreeMap<Reg, usize> = pool.iter().enumerate().map(|(i, r)| (*r, i)).collect();
    let adj = range_interference(&ranges);

    // RQ-60-RACOST increment 1 (#242) — TIED use/def webs. A read-modify-write
    // FIELD (`Movt`/`MovtSym`/`SelectMove` `rd`) reads and writes ONE register
    // slot, so the value range CONSUMED there and the range BORN there must
    // occupy the same physical register. Before this merge the two ranges were
    // coloured independently and a disagreement was only CAUGHT afterwards by
    // `rewrite_op`'s RMW check (`/rmw-colour-mismatch` — re-measured on main
    // as the largest attributed `single-block` bucket, 26 of 42 on the
    // relocatable corpus); folding them into one colouring node makes the
    // mismatch UNREPRESENTABLE instead. Which fields are tied is PROBED from
    // the shipped rewriter itself (`tied_range_pairs` asks `rewrite_op_maps`
    // whether a use/def disagreement is refused), never from a hand-kept op
    // list that could drift — and the joins path's `build_webs` has unified
    // tied webs since increment 2, so this brings the two paths to one
    // convention. The merge only re-imposes an assignment the ORIGINAL stream
    // already had (both ranges live in the same register there), so it can
    // force a decline-to-spill but never a wrong colouring; a function with no
    // tied ops has no pairs and colours EXACTLY as before.
    let Some(tied) = tied_range_pairs(instrs) else {
        // Unreachable after the prescan (every op has a `reg_effect`), but a
        // silent None here would be the "did nothing" ≠ "nothing to do" trap.
        sub("tied-scan");
        return None;
    };
    let rep = web_reps(ranges.len(), &tied);

    // Pins: segment inputs (def == 0) and each register's LAST-opened range
    // (the whole-function live-out) keep their original register — the function
    // must return its result registers unchanged. Reserved registers (R9-R12,
    // SP, LR, PC) are identity-assigned outside the colouring. Pins land on
    // the tied-web REPRESENTATIVE: every member of a web shares one original
    // register (a tie relates a use and a def of the same register), so two
    // pins on one web always agree — declined defensively if that invariant is
    // ever broken, never coloured through.
    let mut last_opened: BTreeMap<Reg, usize> = BTreeMap::new();
    for r in &ranges {
        last_opened.insert(r.reg, r.vreg); // ranges are in creation order
    }
    let mut pins: BTreeMap<usize, usize> = BTreeMap::new();
    let mut assignment: BTreeMap<usize, Reg> = BTreeMap::new();
    let mut pool_vregs: BTreeSet<usize> = BTreeSet::new(); // raw range ids
    let mut pool_webs: BTreeSet<usize> = BTreeSet::new(); // tied-web representatives
    for r in &ranges {
        match pool_index.get(&r.reg) {
            None => {
                // Reserved register: identity, never coloured.
                assignment.insert(r.vreg, r.reg);
            }
            Some(&idx) => {
                pool_vregs.insert(r.vreg);
                let w = rep[r.vreg];
                pool_webs.insert(w);
                let exit_pinned = last_opened.get(&r.reg) == Some(&r.vreg);
                if r.def == 0 || exit_pinned {
                    if let Some(&prev) = pins.get(&w)
                        && prev != idx
                    {
                        sub("tied-pin-conflict");
                        return None;
                    }
                    pins.insert(w, idx);
                }
            }
        }
    }

    // Colouring input: pool ranges only, folded onto their tied-web
    // representatives. An edge INTERNAL to one web vanishes — its endpoints
    // are one value by construction and REQUIRED to share a register (the
    // instruction-0 corner, where an input is consumed by an RMW def it is
    // tied to, makes such an edge representable). Reserved registers cannot
    // collide with pool colours, so their edges are irrelevant here.
    let mut pool_adj: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    for w in &pool_webs {
        pool_adj.entry(*w).or_default();
    }
    for (n, nbrs) in &adj {
        if !pool_vregs.contains(n) {
            continue;
        }
        for m in nbrs {
            if pool_vregs.contains(m) && rep[*n] != rep[*m] {
                pool_adj.entry(rep[*n]).or_default().insert(rep[*m]);
            }
        }
    }

    // #677 soundness: a pool register with NO range in this function is not
    // thereby FREE for a rename target — but for a WHOLE-FUNCTION straight-line
    // segment there is nothing "outside" it, so an absent pool register is
    // genuinely free. We still block absent colours defensively (an
    // identity-shaped colouring within the present registers always exists, so
    // this never costs a recoloring the original had), matching the shipping
    // pass's #677 discipline exactly.
    let present: BTreeSet<Reg> = ranges.iter().map(|r| r.reg).collect();
    let mut next_blocker = ranges.len();
    for (idx, reg) in pool.iter().enumerate() {
        if present.contains(reg) {
            continue;
        }
        let blocker = next_blocker;
        next_blocker += 1;
        pins.insert(blocker, idx);
        for nbrs in pool_adj.values_mut() {
            nbrs.insert(blocker);
        }
        pool_adj.insert(blocker, pool_webs.iter().copied().collect());
    }

    // RQ-60-RACOST increment 2 (#242) — the REAL-ENCODER COST MODEL. Build the
    // occurrence index with the same vreg replay as
    // `straight_line_value_ranges` (folded onto tied-web representatives);
    // both the spill-order metric and the select price colours from the
    // caller-supplied encoder's OWN byte lengths (a straight-line segment has
    // no loops, so every occurrence weight is 1). Cost-blind selects churned
    // registers for nothing and defeated downstream passes
    // (controller_step.wasm 144->156 B under increment 1's unbiased trial,
    // caught by the wired vcr_dec_001_graph_alloc_differential no-growth
    // check); the measured-cost ranking plus the synth-backend final-byte
    // arbiter replace that gamble with a guarantee.
    let Some(ix) = straight_line_occurrence_index(instrs, &rep) else {
        sub("no-occurrence-costs");
        return None;
    };
    let (web_w, web_span) = web_weights(&ix, instrs, enc);
    let orig_colour: BTreeMap<usize, usize> = ranges
        .iter()
        .filter_map(|r| pool_index.get(&r.reg).map(|&c| (rep[r.vreg], c)))
        .collect();
    let mut occ = |w: usize, c: usize, assigned: &BTreeMap<usize, usize>| {
        occurrence_bytes(&ix, instrs, pool, w, c, assigned, enc)
    };
    let (coloring, spilled) = color_webs_costed(
        &pool_adj,
        pool.len(),
        &pins,
        &web_w,
        &web_span,
        &orig_colour,
        caller_saved_prefix(pool),
        &mut occ,
    );
    if !spilled.is_empty() {
        // Spill code insertion is increment 2+ (reuse the Belady machinery).
        // For now a function that does not fit the pool declines to the shipping
        // path — which HAS spill support.
        sub("needs-spill");
        return None;
    }
    for v in &pool_vregs {
        let Some(&c) = coloring.get(&rep[*v]) else {
            sub("web-uncoloured");
            return None;
        };
        assignment.insert(*v, pool[c]);
    }

    // Defense-in-depth: independently of the colourer, re-check every
    // interference edge against the final assignment (cf.
    // `liveness::verify_allocation`, but keyed on value ranges). An edge whose
    // endpoints share a tied web is exempt from the inequality requirement —
    // they are one value living in one register; equality is asserted instead.
    for (n, nbrs) in &adj {
        for m in nbrs {
            let same_web = pool_vregs.contains(n) && pool_vregs.contains(m) && rep[*n] == rep[*m];
            match (assignment.get(n), assignment.get(m)) {
                (Some(a), Some(b)) if !same_web && a != b => {}
                (Some(a), Some(b)) if same_web && a == b => {}
                _ => {
                    sub("edge-recheck");
                    return None;
                }
            }
        }
    }

    // Apply the colouring, then PROVE it preserves the function's dataflow with
    // the trace-equality validator (whole-function live-outs + entry inputs
    // pinned; no exemptions — a whole straight-line function's exit registers are
    // all observable). This is the acceptance oracle; a reject → decline (the
    // red-first teeth are the unit probe `graph_alloc_bad_rename_rejected_by_\
    // segment_validator` in liveness.rs: it shows validate_segment_rewrite
    // rejects a value-flow-breaking merge-rename and accepts the identity — the
    // exact Err/Ok this match discharges to decline/accept).
    let Some(new) = apply_range_coloring(instrs, &assignment) else {
        // In stats mode `apply_range_coloring` itself prints the COMPLETE set
        // of refused ops with causes (rmw-colour-mismatch / no-rewrite-arm)
        // just before this decline line.
        sub("apply-colouring");
        return None;
    };
    match validate_segment_rewrite(instrs, &new) {
        // TWO instruments, on different axes: the backward name-equation trace
        // check, and the forward ABI value contract (VCR-VER-004). Both must
        // hold.
        Ok(()) => abi_gate(instrs, new),
        Err(v) => {
            // Include the violation VARIANT (not the full payload) so the
            // census can split "shape outside the validated class" from a
            // genuine equation failure.
            let s = format!("{v:?}");
            let variant = s.split([' ', '{', '(']).next().unwrap_or("");
            sub(&format!("trace-validator-reject/{variant}"));
            None
        }
    }
}

/// RQ-60-RACOST increment 2 (#242) — the occurrence index the REAL-ENCODER
/// cost model prices colours against.
///
/// One entry per effectful instruction: its stream index plus the
/// register→web operand maps on the use side and the def side. `occs` inverts
/// it (web → entries touching it) and `weight` carries the entry's loop-depth
/// scale (`10^depth`; a straight-line segment is all 1) — the classic Chaitin
/// frequency estimate, applied to MEASURED bytes rather than occurrence
/// counts.
struct OccurrenceIndex {
    entries: Vec<Occurrence>,
    occs: BTreeMap<usize, Vec<usize>>,
    weight: Vec<u64>,
}

/// One effectful instruction: stream index + register→web maps per side.
type Occurrence = (usize, BTreeMap<Reg, usize>, BTreeMap<Reg, usize>);

/// The select's pricing oracle: (web, colour, partial assignment) → measured
/// bytes, `None` when an occurrence is unencodable under the candidate.
type OccCostFn<'a> = dyn FnMut(usize, usize, &BTreeMap<usize, usize>) -> Option<u64> + 'a;

impl OccurrenceIndex {
    fn new() -> Self {
        OccurrenceIndex {
            entries: Vec::new(),
            occs: BTreeMap::new(),
            weight: Vec::new(),
        }
    }
    fn push(&mut self, i: usize, uses: BTreeMap<Reg, usize>, defs: BTreeMap<Reg, usize>, w: u64) {
        let pi = self.entries.len();
        let webs: BTreeSet<usize> = uses.values().chain(defs.values()).copied().collect();
        for web in webs {
            self.occs.entry(web).or_default().push(pi);
        }
        self.entries.push((i, uses, defs));
        self.weight.push(w);
    }
}

/// The straight-line occurrence index: the same replay discipline (and
/// therefore the same vreg numbering) as [`straight_line_value_ranges`], with
/// every vreg folded onto its tied-web representative via `rep`. `None` on an
/// unmodeled op or a numbering drift (both excluded by the caller's pre-scan,
/// but kept total — a silent partial index would misprice every web after the
/// gap).
fn straight_line_occurrence_index(
    instrs: &[ArmInstruction],
    rep: &[usize],
) -> Option<OccurrenceIndex> {
    let mut ix = OccurrenceIndex::new();
    let mut current: BTreeMap<Reg, usize> = BTreeMap::new();
    let mut next = 0usize;
    for (i, ins) in instrs.iter().enumerate() {
        let e = reg_effect(&ins.op)?;
        let mut uses: BTreeMap<Reg, usize> = BTreeMap::new();
        for u in &e.uses {
            let v = *current.entry(*u).or_insert_with(|| {
                let v = next;
                next += 1;
                v
            });
            uses.insert(*u, *rep.get(v)?);
        }
        let mut defs: BTreeMap<Reg, usize> = BTreeMap::new();
        for d in &e.defs {
            let v = next;
            next += 1;
            current.insert(*d, v);
            defs.insert(*d, *rep.get(v)?);
        }
        ix.push(i, uses, defs, 1);
    }
    Some(ix)
}

/// The MEASURED byte cost of homing `web` in `pool[colour]`: for every
/// instruction the web occurs in, rewrite the operand registers to the
/// candidate assignment (webs already coloured keep their chosen colour,
/// undecided webs their original register) and ask the encoder for the byte
/// length of the RESULT, scaled by the occurrence's loop weight. This is the
/// Fried et al. (CC 2023) `C(L, r)` compressibility probe with the encoder's
/// own bytes standing in for a hand compressibility predicate — #936 already
/// established that a hand mirror of the encoder's size behaviour was UNSOUND
/// at authoring, and asking the encoder itself cannot drift.
///
/// `None` means some occurrence became UNENCODABLE under this candidate (the
/// #180/#311 high-register class the encoder refuses): the candidate is
/// excluded rather than priced optimistically. An occurrence the REWRITER
/// cannot express at all is skipped instead — that refusal is
/// candidate-independent (the apply phase declines the whole function later),
/// so skipping it biases no comparison.
fn occurrence_bytes(
    ix: &OccurrenceIndex,
    instrs: &[ArmInstruction],
    pool: &[Reg],
    web: usize,
    colour: usize,
    assigned: &BTreeMap<usize, usize>,
    enc: &dyn Fn(&ArmOp) -> Option<usize>,
) -> Option<u64> {
    let mut total = 0u64;
    let Some(occ) = ix.occs.get(&web) else {
        return Some(0);
    };
    for &pi in occ {
        let (i, uses, defs) = &ix.entries[pi];
        let subst = |m: &BTreeMap<Reg, usize>| -> BTreeMap<Reg, Reg> {
            m.iter()
                .map(|(r, w)| {
                    let tgt = if *w == web {
                        pool[colour]
                    } else if let Some(&c) = assigned.get(w) {
                        if c < pool.len() { pool[c] } else { *r }
                    } else {
                        *r
                    };
                    (*r, tgt)
                })
                .collect()
        };
        let Some(op) = rewrite_op_maps(&instrs[*i].op, &subst(uses), &subst(defs)) else {
            continue;
        };
        total += (enc(&op)? as u64) * ix.weight[pi];
    }
    Some(total)
}

/// The Chaitin spill metric over MEASURED bytes — `W(web) = Σ_occurrences
/// enc(instruction) × 10^loop_depth` — plus each web's live span (first to
/// last occurrence), for the `W / (span × degree)` normalization the
/// optimistic-spill choice uses ("normalized by live-range length", the
/// Bernstein-area refinement of Chaitin's cost/degree). An occurrence the
/// encoder cannot size contributes 0: the metric only ORDERS the
/// optimistic-spill choice (a spill is a DECLINE in this pass), so
/// under-weighting is safe.
fn web_weights(
    ix: &OccurrenceIndex,
    instrs: &[ArmInstruction],
    enc: &dyn Fn(&ArmOp) -> Option<usize>,
) -> (BTreeMap<usize, u64>, BTreeMap<usize, usize>) {
    let mut w_map: BTreeMap<usize, u64> = BTreeMap::new();
    let mut first_last: BTreeMap<usize, (usize, usize)> = BTreeMap::new();
    for (pi, (i, uses, defs)) in ix.entries.iter().enumerate() {
        let sz = enc(&instrs[*i].op).unwrap_or(0) as u64 * ix.weight[pi];
        let webs: BTreeSet<usize> = uses.values().chain(defs.values()).copied().collect();
        for w in webs {
            *w_map.entry(w).or_insert(0) += sz;
            first_last
                .entry(w)
                .and_modify(|(f, l)| {
                    *f = (*f).min(*i);
                    *l = (*l).max(*i);
                })
                .or_insert((*i, *i));
        }
    }
    let span = first_last
        .into_iter()
        .map(|(w, (f, l))| (w, l - f + 1))
        .collect();
    (w_map, span)
}

/// Chaitin/Briggs colouring with the RQ-60-RACOST increment-2 REAL-ENCODER
/// COST MODEL in both halves (#242).
///
/// **Simplify / optimistic-spill order.** Where no node has degree < k, the
/// node minimizing `W / (span × degree)` — measured bytes × 10^loop_depth,
/// normalized by live-range length and constraint degree — is pushed as the
/// optimistic-spill candidate (cross-multiplied to stay in integers).
///
/// **Select** — Fried / Stemmer-Grabow / Wachter (CC 2023, "Register
/// Allocation for Compressed ISAs in LLVM"), Algorithm 1, adapted to a
/// rename-only pass: every free colour is priced by `occ_cost` (the
/// real-encoder `C(L, r)` probe over the web's occurrences — max
/// compressibility there is min measured bytes here), the strictly cheapest
/// wins, and among BYTE-EQUAL minima the established preference order breaks
/// the tie:
///   1. the web's ORIGINAL register when it is caller-saved (R0-R3) — churn-
///      free, and a value already in scratch has nothing to gain by moving;
///   2. the lowest caller-saved minimum — evacuate R4-R8 so the downstream
///      `shrink_callee_saved_saves` can drop prologue push/pop entries (a win
///      that lives entirely downstream, so colour-time bytes cannot see it);
///   3. the web's original register (now necessarily callee-saved) — zero
///      churn when no scratch register is free;
///   4. the lowest minimum, as a last resort.
///
/// A candidate `occ_cost` refuses (an occurrence unencodable under it) is
/// excluded outright. Fried's §4.4 hint-breaking limit is deliberately NOT
/// carried over: it bounds the cost of breaking a COPY hint, and this pass
/// inserts no copies — its analogue here is the FINAL-BYTE ARBITER in
/// `synth-backend`, which sizes the whole candidate function through the real
/// downstream pipeline and refuses any recolouring that does not strictly
/// shrink the shipped bytes. That is strictly stronger than any colour-time
/// bound: measured on `const_cse.wat::spill12`, even an IDENTITY-biased
/// colouring grew the function +96 B through a defeated downstream const-CSE,
/// with no occurrence priced differently at colour time.
///
/// History, so the previous selects are not re-invented: the first select
/// (lowest free colour) repacked whole functions into R0/R1 and put a loop's
/// compare result on top of a register `forward_stack_reloads` was forwarding
/// through (+2 B / +22 cycles on `loop_param_bound_663::sum_const`); its
/// successor (the fixed caller-saved-evacuation preference, kept above as the
/// tie-break) narrowed encodings but was byte-blind, and RQ-59-MEASURE traced
/// the colourer's entire regression tail (7 growers, one mechanism) to
/// exactly that blindness — a 2-byte register copy and a 4-byte `[sp,#imm]`
/// reload priced identically. The measured costs now rank first; the old
/// order only splits ties.
///
/// NOT implemented by changing `chaitin_core`: that core is shared with the
/// SHIPPING `reallocate_function`, so a different order there would move the
/// frozen bytes. The simplify half is deliberately mirrored, not reused.
#[allow(clippy::too_many_arguments)]
fn color_webs_costed(
    adj: &BTreeMap<usize, BTreeSet<usize>>,
    k: usize,
    precolored: &BTreeMap<usize, usize>,
    spill_w: &BTreeMap<usize, u64>,
    span: &BTreeMap<usize, usize>,
    orig_colour: &BTreeMap<usize, usize>,
    caller_saved: usize,
    occ_cost: &mut OccCostFn<'_>,
) -> (BTreeMap<usize, usize>, BTreeSet<usize>) {
    let mut work: BTreeMap<usize, BTreeSet<usize>> = adj
        .iter()
        .filter(|(n, _)| !precolored.contains_key(n))
        .map(|(n, nbrs)| (*n, nbrs.clone()))
        .collect();
    let mut stack: Vec<usize> = Vec::with_capacity(work.len());
    while !work.is_empty() {
        let pick = work
            .iter()
            .find(|(_, nbrs)| nbrs.len() < k)
            .map(|(n, _)| *n)
            .unwrap_or_else(|| {
                work.iter()
                    .min_by(|a, b| {
                        let val = |n: &usize| spill_w.get(n).copied().unwrap_or(1).max(1) as u128;
                        let sp = |n: &usize| span.get(n).copied().unwrap_or(1).max(1) as u128;
                        let deg = |s: &BTreeSet<usize>| s.len().max(1) as u128;
                        (val(a.0) * sp(b.0) * deg(b.1))
                            .cmp(&(val(b.0) * sp(a.0) * deg(a.1)))
                            .then(a.0.cmp(b.0))
                    })
                    .map(|(n, _)| *n)
                    .unwrap()
            });
        let nbrs = work.remove(&pick).unwrap_or_default();
        for n in &nbrs {
            if let Some(s) = work.get_mut(n) {
                s.remove(&pick);
            }
        }
        stack.push(pick);
    }
    let mut colour: BTreeMap<usize, usize> = precolored.clone();
    let mut spilled: BTreeSet<usize> = BTreeSet::new();
    while let Some(n) = stack.pop() {
        let mut used = vec![false; k];
        for nb in adj.get(&n).into_iter().flatten() {
            if let Some(&c) = colour.get(nb)
                && c < k
            {
                used[c] = true;
            }
        }
        // --- v053-mutation-site:select-pick BEGIN ---------------------
        // Everything from here to the matching END marker is the SELECT
        // decision (measured-cost ranking + preference order). The wired
        // `vcr_ver_004_instrument_independence.py` oracle re-plants v0.53's
        // mutation by replacing this span with a bare lowest-free pick, so
        // the markers must travel with the decision when it moves — deleting
        // them turns that oracle loudly red (marker-not-found), never
        // silently vacuous (its non-vacuity floor guards the other half).
        let own = orig_colour.get(&n).copied().filter(|&c| c < k && !used[c]);
        // Price every free candidate; keep only the strictly cheapest set.
        let mut minima: Vec<usize> = Vec::new();
        let mut min_cost: Option<u64> = None;
        for (c, taken) in used.iter().enumerate() {
            if *taken {
                continue;
            }
            let Some(cost) = occ_cost(n, c, &colour) else {
                continue; // unencodable under this candidate: excluded
            };
            match min_cost {
                Some(m) if cost > m => {}
                Some(m) if cost == m => minima.push(c),
                _ => {
                    min_cost = Some(cost);
                    minima = vec![c];
                }
            }
        }
        let pick = if minima.is_empty() {
            // Nothing sizable: own colour if free (identity is always legal —
            // the original stream encoded), else the pre-cost-model fallback
            // (lowest free colour).
            own.or_else(|| used.iter().position(|taken| !taken))
        } else {
            // Byte-equal minima split by the established preference order.
            own.filter(|o| *o < caller_saved && minima.contains(o))
                .or_else(|| minima.iter().copied().find(|&c| c < caller_saved))
                .or_else(|| own.filter(|o| minima.contains(o)))
                .or_else(|| minima.first().copied())
        };
        // --- v053-mutation-site:select-pick END -----------------------
        match pick {
            Some(c) => {
                colour.insert(n, c);
            }
            None => {
                spilled.insert(n);
            }
        }
    }
    (colour, spilled)
}

/// The TIED use/def range pairs of a straight-line segment — RQ-60-RACOST
/// increment 1 (#242). Replayed with the SAME vreg numbering as
/// [`straight_line_value_ranges`] (the [`occurrence_costs`] discipline, so the
/// ids cannot drift). A register an instruction both reads and writes is
/// probed against the SHIPPED rewriter itself: if [`rewrite_op_maps`] refuses
/// a rename in which the use side and the def side disagree on that register,
/// the field is a read-modify-write and the range consumed there must share a
/// register with the range born there. Probing the rewriter — rather than
/// keeping a second list of RMW ops — is the same no-second-source-of-truth
/// rule as `wcet::op_mnemonic`: a new RMW arm in `rewrite_op` is tied here for
/// free, and nothing can drift. An op the rewriter cannot express AT ALL also
/// probes as tied; that over-merge is conservative (it only re-imposes the
/// original stream's own assignment) and the function still declines at apply
/// time with `/no-rewrite-arm`, so no coverage gap is hidden by it.
fn tied_range_pairs(instrs: &[ArmInstruction]) -> Option<Vec<(usize, usize)>> {
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    let mut current: BTreeMap<Reg, usize> = BTreeMap::new();
    let mut next = 0usize;
    for ins in instrs {
        let e = reg_effect(&ins.op)?;
        let mut use_vreg: BTreeMap<Reg, usize> = BTreeMap::new();
        for u in &e.uses {
            let v = *current.entry(*u).or_insert_with(|| {
                let v = next;
                next += 1;
                v
            });
            use_vreg.insert(*u, v);
        }
        for d in &e.defs {
            let dv = next;
            next += 1;
            if let Some(&uv) = use_vreg.get(d) {
                // The probe: a use/def disagreement on this register alone.
                // The two probe registers are arbitrary — only the
                // disagreement matters to `rewrite_op`'s RMW check.
                let probe_use = BTreeMap::from([(*d, Reg::R0)]);
                let probe_def = BTreeMap::from([(*d, Reg::R1)]);
                if rewrite_op_maps(&ins.op, &probe_use, &probe_def).is_none() {
                    pairs.push((uv, dv));
                }
            }
            current.insert(*d, dv);
        }
    }
    Some(pairs)
}

/// Union-find over the `n` range ids: the vreg → representative map the
/// tied-web merge colours through. The smallest member id is each web's
/// representative, so the mapping is deterministic regardless of pair order.
fn web_reps(n: usize, pairs: &[(usize, usize)]) -> Vec<usize> {
    fn find(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]]; // path halving
            x = parent[x];
        }
        x
    }
    let mut parent: Vec<usize> = (0..n).collect();
    for &(a, b) in pairs {
        let (ra, rb) = (find(&mut parent, a), find(&mut parent, b));
        if ra != rb {
            let (lo, hi) = if ra < rb { (ra, rb) } else { (rb, ra) };
            parent[hi] = lo;
        }
    }
    (0..n).map(|v| find(&mut parent, v)).collect()
}

/// VCR-DEC-001 **increment 2** — colour a whole branchy function ACROSS its
/// control-flow joins.
///
/// **Why joins.** Increment 1 could only colour a function that was one
/// straight-line segment; the shipping `reallocate_function` handles branchy
/// functions by cutting them into maximal straight-line segments and pinning
/// each segment's inputs (`def == 0`) and per-register exit holders to their
/// original registers. Those pins are exactly where the greedy allocator's
/// weakness concentrates: an if/else arm's first `movw r4, #400` is a
/// segment-index-0 def, so segment-local analysis is FORCED to treat it as a
/// segment input and cannot move it — even though whole-function liveness shows
/// the value is born there, dies two instructions later, and never crosses the
/// join. Every arm therefore keeps whatever register the greedy selector
/// happened to hand it, and the callee-saved ones drag a `push {r4-r8,lr}` /
/// `pop {r4-r8,pc}` behind them.
///
/// **What this does instead.** Build the function's label-form CFG, split every
/// physical register's def-use chains into cross-block **webs** (a def site and
/// every use its definition reaches, unified through joins by a reaching-def
/// fixpoint), build interference over WEBS from CFG liveness, and colour the
/// whole function at once with Chaitin/Briggs. Two values in opposite arms of an
/// if/else are never simultaneously live, so they share one register — which is
/// how the else-arm's R4 becomes R2 and the callee-saved save/restore
/// disappears under the downstream `shrink_callee_saved_saves`.
///
/// **Acceptance oracle first (the L4/#872 lesson).** The rewrite is accepted
/// only if [`validate_cfg_rewrite`] — the CFG-lifted backward must-fixpoint
/// version of the trace-equality validator — proves it preserves dataflow on
/// EVERY path, with an exit contract the validator computes itself (the pass
/// cannot hand it a weakened seed). The pass mirrors that contract exactly in
/// its own pins, so a colouring it proposes is one the oracle can certify.
/// Downstream, the unconditional VCR-RA-003 [`validate_final_allocation`]
/// re-checks the final stream through an INDEPENDENTLY written CFG builder, and
/// the execution differential is the runtime backstop. That layering is the
/// honest answer to "a validator can share its pass's blind spot": this
/// validator shares the CFG *shape* with the pass, so it is necessary, not
/// sufficient — which is why RA-003 and unicorn execution both gate it.
///
/// **Calls (increment 3, v0.54).** A `bl`/`blx` is an interior instruction with
/// the AAPCS [`crate::liveness::call_effect`]: it DEFS `{R0..R3, R12, LR}` and
/// USES the argument registers `{R0..R3}` (conservatively all four — the callee's
/// signature is not visible here) plus a `blx`'s target register. Those defs make
/// every web live across the call interfere with the call-clobbered set, so the
/// colourer structurally CANNOT home a live value in caller-saved scratch; the
/// call's own webs are identity-pinned and the op is emitted verbatim. The SAME
/// `call_effect` drives [`validate_cfg_rewrite`]'s backward transfer, so the
/// oracle cannot be weaker than the pass on exactly the contract that matters —
/// the hazard this increment was briefed on ("a validator treating `bl` as
/// effect-free would accept a non-identity equation across it").
///
/// **Bounded scope — declines, never hard-fails.** `None` (→ the shipping
/// `reallocate_function`) on: numeric/pre-resolved branches (`BOffset`/
/// `BCondOffset` — their displacements are already baked, so a rename that
/// changes a Thumb encoding width would silently overshoot; the label form is
/// resolved AFTER this pass), the HIGH-LEVEL `Call`/`CallIndirect` pseudo-ops
/// (expanded downstream into a bounds guard + table load + result move, so the
/// register footprint here is not the one that ships), `BrTable`, computed
/// `Bx`, duplicate/unknown labels, unreachable blocks, any op without a precise
/// [`reg_effect`], any spill, and any validator rejection.
mod joins {
    use super::*;
    use crate::liveness::{
        BasicBlock, RegEffect, call_effect, cfg_exit_observable, is_straight_line,
        pair_early_clobber, pair_effect, pair_low_reg_only, reg_effect, rewrite_op_maps,
        validate_cfg_rewrite,
    };
    use crate::rules::ArmOp;

    /// Every architectural register the analysis tracks (pool + reserved).
    const ALL_REGS: [Reg; 16] = [
        Reg::R0,
        Reg::R1,
        Reg::R2,
        Reg::R3,
        Reg::R4,
        Reg::R5,
        Reg::R6,
        Reg::R7,
        Reg::R8,
        Reg::R9,
        Reg::R10,
        Reg::R11,
        Reg::R12,
        Reg::SP,
        Reg::LR,
        Reg::PC,
    ];

    /// The registers a 16-bit Thumb `rd`/`rn` field can actually name. An
    /// operand [`pair_low_reg_only`] lists must be one of these in the FINAL
    /// stream; anything else is the #180/#311 silent-transmute class.
    const LOW_REGS: [Reg; 8] = [
        Reg::R0,
        Reg::R1,
        Reg::R2,
        Reg::R3,
        Reg::R4,
        Reg::R5,
        Reg::R6,
        Reg::R7,
    ];

    /// Decline diagnostics: `SYNTH_GRAPH_ALLOC_STATS=1` names WHY a branchy
    /// function fell back to the shipping pass, so a "did nothing" result is
    /// never mistaken for "nothing to do".
    fn decline<T>(reason: &str) -> Option<T> {
        if std::env::var("SYNTH_GRAPH_ALLOC_STATS").is_ok() {
            eprintln!("[graph-alloc] join colouring DECLINED: {reason}");
        }
        None
    }

    enum Term<'a> {
        Uncond(&'a str),
        Cond(&'a str),
        Ret,
        Fall,
        /// Outside the increment-2 scope, with the reason NAMED so the corpus
        /// decline histogram is actionable evidence for the next increment
        /// rather than one opaque `cfg-unmodeled-construct` bucket.
        No(&'static str),
    }

    fn classify(op: &ArmOp) -> Term<'_> {
        use ArmOp::*;
        match op {
            B { label } => Term::Uncond(label),
            Bhs { label } | Blo { label } | Bcc { label, .. } => Term::Cond(label),
            Bx { rm: Reg::LR } => Term::Ret,
            // A `pop {…, pc}` IS a return — the #888 class. Modeling it as a
            // plain register-list def (which `reg_effect` alone would) is what
            // let the range-realloc pass recolour `pop {r4..r8,pc}` into
            // `pop {r6,r5,r4,r3,r2,pc}`.
            Pop { regs } if regs.contains(&Reg::PC) => Term::Ret,
            // Pre-resolved numeric branches: the displacement is already baked
            // into the stream, so a rename that changes a Thumb encoding width
            // would silently overshoot the target (#606). Re-resolving them is
            // the named next increment.
            BOffset { .. } | BCondOffset { .. } => Term::No("numeric-branch"),
            // INCREMENT 3 (#242): a real machine call is MODELED, not declined.
            // Its AAPCS argument + call-clobber contract comes from the single
            // shared [`call_effect`] definition, which this pass feeds into its
            // liveness / interference / pins AND `validate_cfg_rewrite` feeds
            // into its backward transfer — the "model it in one and not the
            // other and you build a validator that certifies its own pass's
            // miscompile" hazard, closed by construction. A `bl`/`blx` FALLS
            // THROUGH: it is an interior instruction, not a terminator.
            Bl { .. } | Blx { .. } => Term::Fall,
            // The HIGH-LEVEL call pseudo-ops stay out of scope: `Call` carries a
            // result register and `CallIndirect` a table-index register, and both
            // are EXPANDED downstream (bounds guard, table load, result move), so
            // the register footprint this pass would colour is not the one that
            // ships. Declined, with the reason named.
            Call { .. } => Term::No("call-pseudo"),
            CallIndirect { .. } => Term::No("call-indirect-pseudo"),
            BrTable { .. } => Term::No("br-table"),
            Bx { .. } => Term::No("computed-bx"),
            _ => Term::Fall,
        }
    }

    /// The `unmodeled-op` admission predicate, in ONE place: an interior
    /// (non-terminator, non-label, non-`bx`) instruction that NONE of the three
    /// shared effect definitions ([`reg_effect`] / [`call_effect`] /
    /// [`pair_effect`]) models. [`build_cfg`] declines on the FIRST hit; the
    /// STATS path re-scans the whole stream with this SAME predicate so the
    /// decline census names the COMPLETE blocker set per function — the
    /// first-blocker-only trap is the one `scan_for_decline` fell into (#936:
    /// three unpriced ops hid behind the first decline for a release).
    fn is_unmodeled(ins: &ArmInstruction) -> bool {
        matches!(classify(&ins.op), Term::Ret | Term::Fall)
            && !matches!(ins.op, ArmOp::Label { .. })
            && !matches!(ins.op, ArmOp::Bx { .. })
            && reg_effect(&ins.op).is_none()
            && call_effect(&ins.op).is_none()
            && pair_effect(&ins.op).is_none()
    }

    /// The label-form CFG of `instrs`, or `None` to decline. Sound by
    /// construction: a `Some` is a COMPLETE CFG (every block reachable from the
    /// entry, every terminator modeled), never a partial guess.
    pub(super) fn build_cfg(instrs: &[ArmInstruction]) -> Result<Vec<BasicBlock>, &'static str> {
        let n = instrs.len();
        if n == 0 {
            return Err("empty");
        }
        // 1. Admission.
        let mut labels: BTreeSet<&str> = BTreeSet::new();
        for ins in instrs {
            match classify(&ins.op) {
                Term::No(why) => return Err(why),
                Term::Uncond(_) | Term::Cond(_) => {}
                Term::Ret | Term::Fall => {
                    // INCREMENT 3 modeled calls (`call_effect`), INCREMENT 4 the
                    // i64 register-pair pseudo-ops (`pair_effect`) — both are
                    // deliberate non-`reg_effect` definitions the shipping
                    // pipeline never sees. The single predicate lives in
                    // [`is_unmodeled`].
                    if is_unmodeled(ins) {
                        // Diagnostics only (flag-gated, stderr): name the
                        // COMPLETE blocker set, not just this first hit, so the
                        // census stays actionable — a widening judged from the
                        // first blocker alone under-counts every op hiding
                        // behind it (the #936 `scan_for_decline` class).
                        if std::env::var("SYNTH_GRAPH_ALLOC_STATS").is_ok() {
                            let mut set: BTreeMap<String, usize> = BTreeMap::new();
                            for blocked in instrs.iter().filter(|i| is_unmodeled(i)) {
                                *set.entry(variant_name(&blocked.op)).or_insert(0) += 1;
                            }
                            let listing = set
                                .iter()
                                .map(|(k, v)| format!("{k} x{v}"))
                                .collect::<Vec<_>>()
                                .join(", ");
                            eprintln!("[graph-alloc] unmodeled-op complete blocker set: {listing}");
                        }
                        return Err("unmodeled-op");
                    }
                }
            }
            if let ArmOp::Label { name } = &ins.op
                && !labels.insert(name.as_str())
            {
                return Err("duplicate-label"); // ambiguous CFG
            }
        }
        // 2. Leaders.
        let mut leader = vec![false; n];
        leader[0] = true;
        for i in 0..n {
            if matches!(instrs[i].op, ArmOp::Label { .. }) {
                leader[i] = true;
            }
            if matches!(
                classify(&instrs[i].op),
                Term::Uncond(_) | Term::Cond(_) | Term::Ret
            ) && i + 1 < n
            {
                leader[i + 1] = true;
            }
        }
        let starts: Vec<usize> = (0..n).filter(|&i| leader[i]).collect();
        let mut blocks: Vec<BasicBlock> = starts
            .iter()
            .enumerate()
            .map(|(bi, &start)| BasicBlock {
                start,
                end: starts.get(bi + 1).copied().unwrap_or(n),
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
        // 3. Successors.
        let mut succs: Vec<Vec<usize>> = Vec::with_capacity(blocks.len());
        for b in &blocks {
            let fallthrough = block_of_start.get(&b.end).copied();
            succs.push(match classify(&instrs[b.end - 1].op) {
                Term::Uncond(l) => vec![*block_of_label.get(l).ok_or("unknown-label")?],
                Term::Cond(l) => {
                    let t = *block_of_label.get(l).ok_or("unknown-label")?;
                    let mut s = vec![t];
                    if let Some(f) = fallthrough
                        && f != t
                    {
                        s.push(f);
                    }
                    s
                }
                Term::Ret => vec![],
                // A non-return block that falls off the end of the function is
                // a stream we do not understand: decline rather than invent a
                // sink (an invented sink would silently drop its exit contract).
                Term::Fall => vec![fallthrough.ok_or("falls-off-end")?],
                Term::No(why) => return Err(why),
            });
        }
        for (b, s) in blocks.iter_mut().zip(succs) {
            b.succ = s;
        }
        // 4. Every block must be reachable from the entry — an unreachable
        //    block's demands never reach the entry check, so a CFG that hides
        //    one would validate vacuously.
        let mut seen = vec![false; blocks.len()];
        let mut work = vec![0usize];
        seen[0] = true;
        while let Some(b) = work.pop() {
            for &s in &blocks[b].succ {
                if !seen[s] {
                    seen[s] = true;
                    work.push(s);
                }
            }
        }
        if seen.iter().any(|r| !r) {
            return Err("unreachable-block");
        }
        Ok(blocks)
    }

    /// Simple union-find over web ids.
    struct Uf(Vec<usize>);
    impl Uf {
        fn new(n: usize) -> Self {
            Uf((0..n).collect())
        }
        fn find(&mut self, mut x: usize) -> usize {
            while self.0[x] != x {
                self.0[x] = self.0[self.0[x]];
                x = self.0[x];
            }
            x
        }
        fn union(&mut self, a: usize, b: usize) {
            let (a, b) = (self.find(a), self.find(b));
            if a != b {
                self.0[b] = a;
            }
        }
    }

    /// Per-instruction effect (`None` for pure control flow / labels).
    ///
    /// INCREMENT 3: a `bl`/`blx` is not straight-line but is NOT effect-free
    /// either — it gets the AAPCS [`call_effect`], the SAME definition
    /// `validate_cfg_rewrite` uses. That one line is what puts calls into this
    /// pass's liveness, webs and interference: a web live across a call now
    /// interferes with the call's `{R0..R3, R12, LR}` def webs (all
    /// identity-pinned), so the colourer structurally cannot home a live value in
    /// call-clobbered scratch.
    fn effects(instrs: &[ArmInstruction]) -> Vec<Option<RegEffect>> {
        instrs
            .iter()
            .map(|i| {
                if is_straight_line(&i.op) {
                    // INCREMENT 4: `pair_effect` is the fallback, never an
                    // override — an op with BOTH would be a contradiction in the
                    // model, and `reg_effect` is the one the shipping pipeline
                    // already agrees with.
                    reg_effect(&i.op).or_else(|| pair_effect(&i.op))
                } else {
                    call_effect(&i.op)
                }
            })
            .collect()
    }

    /// The exit contract, taken VERBATIM from the oracle
    /// ([`crate::liveness::cfg_exit_observable`]) rather than restated here.
    /// Used as `live_out` at every sink, so a register the caller can observe
    /// stays live from its last definition all the way to the return and its
    /// holder web interferes with everything in between — the pass therefore
    /// never proposes a colouring the validator would reject for clobbering an
    /// exit-observable register. A register NEITHER side defines is live from
    /// the function entry, so its entry web interferes with every web and no
    /// value can be renamed onto it (the seqblocks case: a void function's
    /// unwritten R0 is not a free rename target, because this pass cannot see
    /// the wasm signature that would prove it dead).
    fn exit_live(instrs: &[ArmInstruction], sink_end: usize) -> BTreeSet<Reg> {
        cfg_exit_observable(&instrs[sink_end - 1].op)
    }

    /// Backward per-block register liveness over the CFG.
    fn liveness(
        instrs: &[ArmInstruction],
        eff: &[Option<RegEffect>],
        blocks: &[BasicBlock],
    ) -> (Vec<BTreeSet<Reg>>, Vec<BTreeSet<Reg>>) {
        let nb = blocks.len();
        let mut use_b = vec![BTreeSet::<Reg>::new(); nb];
        let mut def_b = vec![BTreeSet::<Reg>::new(); nb];
        for (bi, b) in blocks.iter().enumerate() {
            let mut defined = BTreeSet::new();
            for e in eff[b.start..b.end].iter().flatten() {
                for u in &e.uses {
                    if !defined.contains(u) {
                        use_b[bi].insert(*u);
                    }
                }
                for d in &e.defs {
                    defined.insert(*d);
                }
            }
            def_b[bi] = defined;
        }
        let mut live_in = vec![BTreeSet::<Reg>::new(); nb];
        let mut live_out = vec![BTreeSet::<Reg>::new(); nb];
        let mut changed = true;
        while changed {
            changed = false;
            for bi in (0..nb).rev() {
                let out: BTreeSet<Reg> = if blocks[bi].succ.is_empty() {
                    exit_live(instrs, blocks[bi].end)
                } else {
                    blocks[bi]
                        .succ
                        .iter()
                        .flat_map(|&s| live_in[s].iter().copied())
                        .collect()
                };
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
        (live_in, live_out)
    }

    /// Everything the colourer needs, derived from the CFG in one pass.
    struct Webs {
        /// web id per (instruction, def register), and the entry pseudo-defs.
        def_web: BTreeMap<(usize, Reg), usize>,
        entry_web: BTreeMap<Reg, usize>,
        /// The (unique) original register of each web.
        reg_of: Vec<Reg>,
        /// `reach_before[i][r]` — the webs that may hold `r` immediately before
        /// `i`. A SET, not a single web: two definitions of one register that
        /// reach a common point but die there (each arm's own `movw r4, #k`)
        /// are genuinely SEPARATE values and must stay separately colourable.
        /// Merging them — the obvious "one holder per register per point"
        /// shortcut — silently pins every arm-local value back to the greedy
        /// selector's register and makes this whole pass an identity transform.
        /// Wherever a single holder is REQUIRED (a use, an apply-time rename)
        /// the set is a singleton by construction: `r` live at a point means
        /// some downstream use reads it, and that use unified every definition
        /// reaching it.
        reach_before: Vec<BTreeMap<Reg, BTreeSet<usize>>>,
        /// `reach_after[i][r]` — the webs that may hold `r` immediately after `i`.
        reach_after: Vec<BTreeMap<Reg, BTreeSet<usize>>>,
        n_webs: usize,
    }

    /// Split every physical register's def-use chains into cross-block webs.
    ///
    /// Because a use of `r` can only be reached by definitions OF `r`, every web
    /// carries exactly ONE original register — webs partition per-register def
    /// sites, they never merge two registers. The cross-arm sharing this pass
    /// exists for comes from ABSENCE of interference between two arms' webs, not
    /// from merging them.
    fn build_webs(
        instrs: &[ArmInstruction],
        eff: &[Option<RegEffect>],
        blocks: &[BasicBlock],
    ) -> Option<Webs> {
        // Def sites: one pseudo-def per register at function entry, then one per
        // (instruction, def register).
        let mut reg_of: Vec<Reg> = Vec::new();
        let mut entry_web: BTreeMap<Reg, usize> = BTreeMap::new();
        for r in ALL_REGS {
            entry_web.insert(r, reg_of.len());
            reg_of.push(r);
        }
        let mut def_web: BTreeMap<(usize, Reg), usize> = BTreeMap::new();
        for (i, e) in eff.iter().enumerate() {
            if let Some(e) = e {
                for d in &e.defs {
                    def_web.insert((i, *d), reg_of.len());
                    reg_of.push(*d);
                }
            }
        }
        let n_sites = reg_of.len();
        let mut uf = Uf::new(n_sites);

        // Forward reaching-def fixpoint over the CFG. `in_b[bi][r]` = the set of
        // def sites of `r` that may reach block `bi`'s entry.
        type ReachMap = BTreeMap<Reg, BTreeSet<usize>>;
        let nb = blocks.len();
        let entry_reach: ReachMap = ALL_REGS
            .iter()
            .map(|r| (*r, BTreeSet::from([entry_web[r]])))
            .collect();
        let mut in_b: Vec<ReachMap> = vec![BTreeMap::new(); nb];
        let mut out_b: Vec<ReachMap> = vec![BTreeMap::new(); nb];
        in_b[0] = entry_reach.clone();
        let transfer = |bi: usize, mut m: ReachMap| -> ReachMap {
            for i in blocks[bi].start..blocks[bi].end {
                if let Some(e) = &eff[i] {
                    for d in &e.defs {
                        m.insert(*d, BTreeSet::from([def_web[&(i, *d)]]));
                    }
                }
            }
            m
        };
        let mut changed = true;
        while changed {
            changed = false;
            for bi in 0..nb {
                let mut inm: ReachMap = if bi == 0 {
                    entry_reach.clone()
                } else {
                    BTreeMap::new()
                };
                for (pb, blk) in blocks.iter().enumerate() {
                    if blk.succ.contains(&bi) {
                        for (r, s) in &out_b[pb] {
                            inm.entry(*r).or_default().extend(s.iter().copied());
                        }
                    }
                }
                if bi == 0 {
                    for (r, s) in &entry_reach {
                        inm.entry(*r).or_default().extend(s.iter().copied());
                    }
                }
                if inm != in_b[bi] {
                    in_b[bi] = inm;
                    changed = true;
                }
                let outm = transfer(bi, in_b[bi].clone());
                if outm != out_b[bi] {
                    out_b[bi] = outm;
                    changed = true;
                }
            }
        }

        // Replay each block, unifying at uses; record per-instruction reach maps.
        let n = instrs.len();
        let mut reach_before_sets: Vec<ReachMap> = vec![BTreeMap::new(); n];
        let mut reach_after_sets: Vec<ReachMap> = vec![BTreeMap::new(); n];
        for (bi, b) in blocks.iter().enumerate() {
            let mut cur = in_b[bi].clone();
            for i in b.start..b.end {
                reach_before_sets[i] = cur.clone();
                if let Some(e) = &eff[i] {
                    for u in &e.uses {
                        let set = cur.get(u)?;
                        let mut it = set.iter().copied();
                        let first = it.next()?;
                        for d in it {
                            uf.union(first, d);
                        }
                        // A single-field RMW (`movt`, `SelectMove`) reads and
                        // writes ONE register field: its old and new webs must
                        // land on the same colour, so unify them. Doing this for
                        // every same-register def/use pair is a conservative
                        // over-approximation (it can only force an assignment
                        // the ORIGINAL already had), and `rewrite_op_maps`
                        // independently rejects any residual disagreement.
                        if e.defs.contains(u) {
                            uf.union(first, def_web[&(i, *u)]);
                        }
                    }
                    for d in &e.defs {
                        cur.insert(*d, BTreeSet::from([def_web[&(i, *d)]]));
                    }
                }
                reach_after_sets[i] = cur.clone();
            }
        }

        // Canonicalise each reaching set through union-find — WITHOUT merging
        // distinct webs. Two definitions of one register reaching a common
        // point where the register is DEAD stay separate values; that is
        // exactly the cross-arm freedom this pass exists to exploit.
        let canon = |m: &ReachMap, uf: &mut Uf| -> BTreeMap<Reg, BTreeSet<usize>> {
            m.iter()
                .map(|(r, s)| (*r, s.iter().map(|d| uf.find(*d)).collect()))
                .collect()
        };
        let mut reach_before: Vec<BTreeMap<Reg, BTreeSet<usize>>> = Vec::with_capacity(n);
        for m in &reach_before_sets {
            reach_before.push(canon(m, &mut uf));
        }
        let mut reach_after: Vec<BTreeMap<Reg, BTreeSet<usize>>> = Vec::with_capacity(n);
        for m in &reach_after_sets {
            reach_after.push(canon(m, &mut uf));
        }
        let entry_web: BTreeMap<Reg, usize> = entry_web
            .into_iter()
            .map(|(r, w)| (r, uf.find(w)))
            .collect();
        let def_web: BTreeMap<(usize, Reg), usize> =
            def_web.into_iter().map(|(k, w)| (k, uf.find(w))).collect();
        // Every web carries one register (a use of `r` only unifies defs of `r`).
        for (k, w) in &def_web {
            if reg_of[*w] != k.1 {
                return None;
            }
        }
        Some(Webs {
            def_web,
            entry_web,
            reg_of,
            reach_before,
            reach_after,
            n_webs: n_sites,
        })
    }

    /// Natural-loop nesting depth per block, from the CFG this pass already
    /// built: iterative dominators, back edges (`b → h` with `h` dominating
    /// `b`), and each back edge's natural-loop body counted once. Feeds the
    /// classic `10^depth` occurrence weight of the RQ-60-RACOST cost model
    /// ([`super::loop_weight`]). Deliberately structural — no profile exists
    /// here, and a bound-true static estimate is enough to ORDER costs.
    ///
    /// (The previous select this cost model replaced — a fixed caller-saved-
    /// evacuation preference — carried the `sum_const` +22-cycle churn story;
    /// that history now lives on [`super::color_webs_costed`].)
    pub(super) fn block_loop_depths(blocks: &[BasicBlock]) -> Vec<u32> {
        let nb = blocks.len();
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); nb];
        for (bi, b) in blocks.iter().enumerate() {
            for &s in &b.succ {
                preds[s].push(bi);
            }
        }
        // Iterative dominator sets (blocks are few; build_cfg guarantees every
        // block reachable from the entry, so the intersection converges).
        let all: BTreeSet<usize> = (0..nb).collect();
        let mut dom: Vec<BTreeSet<usize>> = vec![all; nb];
        dom[0] = BTreeSet::from([0]);
        let mut changed = true;
        while changed {
            changed = false;
            for b in 1..nb {
                let mut newd: Option<BTreeSet<usize>> = None;
                for &p in &preds[b] {
                    newd = Some(match newd {
                        None => dom[p].clone(),
                        Some(acc) => acc.intersection(&dom[p]).copied().collect(),
                    });
                }
                let mut newd = newd.unwrap_or_default();
                newd.insert(b);
                if newd != dom[b] {
                    dom[b] = newd;
                    changed = true;
                }
            }
        }
        let mut depth = vec![0u32; nb];
        for (b, blk) in blocks.iter().enumerate() {
            for &h in &blk.succ {
                if !dom[b].contains(&h) {
                    continue; // not a back edge
                }
                // Natural loop body of the back edge b → h: everything that
                // reaches b backwards without passing through h.
                let mut body: BTreeSet<usize> = BTreeSet::from([h]);
                let mut work = vec![b];
                while let Some(n) = work.pop() {
                    if body.insert(n) {
                        for &p in &preds[n] {
                            work.push(p);
                        }
                    }
                }
                for n in body {
                    depth[n] += 1;
                }
            }
        }
        depth
    }

    /// The increment-2 entry point. See the module doc for scope and oracles.
    pub(super) fn reallocate_across_joins(
        instrs: &[ArmInstruction],
        pool: &[Reg],
        enc: &dyn Fn(&ArmOp) -> Option<usize>,
    ) -> Option<Vec<ArmInstruction>> {
        let blocks = match build_cfg(instrs) {
            Ok(b) => b,
            Err(why) => return decline(why),
        };
        // A single-block function is increment 1's domain (tried first); this
        // path exists for the branchy ones. EXCEPT when it contains a call:
        // increment 1 requires every instruction to be `is_straight_line`, so it
        // structurally declines a `bl` and would leave a straight-line CALLING
        // function to the shipping pass forever. Increment 3 models calls, so a
        // single-block function that has one is THIS path's job.
        // Increment 1 requires EVERY instruction to have a `reg_effect`, so it
        // structurally declines a function containing a call (increment 3) or an
        // i64 register-pair op (increment 4) — and a SINGLE-BLOCK such function
        // would then be reachable by neither path and sit in the shipping
        // allocator forever. Measured, not hypothetical: increment 4's model
        // moved 114 relocatable functions out of `unmodeled-op`, and 96 of them
        // landed straight in `single-block` until this condition was widened.
        let has_call = instrs.iter().any(|i| call_effect(&i.op).is_some());
        let has_pair = instrs.iter().any(|i| pair_effect(&i.op).is_some());
        if blocks.len() < 2 && !has_call && !has_pair {
            return decline("single-block");
        }
        let eff = effects(instrs);
        // Every instruction is either a modeled straight-line op or pure control
        // flow the rename passes through verbatim.
        for (i, ins) in instrs.iter().enumerate() {
            if eff[i].is_none() && is_straight_line(&ins.op) {
                return decline("unmodeled-op");
            }
            // INCREMENT 4: an operand whose downstream expansion uses a 16-bit
            // Thumb register form must be in R0-R7 (see `pair_low_reg_only`). If
            // the INCOMING stream already has a high register there, the stream
            // is already mis-encoded — the allocator will not put its name to it.
            // Loud decline, not a silent recolour that would hide the defect.
            if pair_low_reg_only(&ins.op)
                .iter()
                .any(|r| !LOW_REGS.contains(r))
            {
                return decline("i64-16bit-form-high-reg");
            }
        }
        let Some(webs) = build_webs(instrs, &eff, &blocks) else {
            return decline("web-construction");
        };
        let (live_in, live_out) = liveness(instrs, &eff, &blocks);

        // ---- Interference over WEBS ------------------------------------
        let mut adj: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
        let node = |w: usize, adj: &mut BTreeMap<usize, BTreeSet<usize>>| {
            adj.entry(w).or_default();
        };
        let edge = |a: usize, b: usize, adj: &mut BTreeMap<usize, BTreeSet<usize>>| {
            if a != b {
                adj.entry(a).or_default().insert(b);
                adj.entry(b).or_default().insert(a);
            }
        };
        for w in 0..webs.n_webs {
            node(w, &mut adj);
        }
        // Live web sets at every program point; simultaneously-live webs form a
        // clique, and EVERY def (dead-on-arrival ones included — they still WRITE
        // the register) interferes with everything live immediately after it.
        let live_webs =
            |regs: &BTreeSet<Reg>, m: &BTreeMap<Reg, BTreeSet<usize>>| -> BTreeSet<usize> {
                regs.iter()
                    .filter_map(|r| m.get(r))
                    .flat_map(|s| s.iter().copied())
                    .collect()
            };
        for (bi, b) in blocks.iter().enumerate() {
            // Block entry.
            let entry_set = live_webs(&live_in[bi], &webs.reach_before[b.start]);
            for a in &entry_set {
                for c in &entry_set {
                    edge(*a, *c, &mut adj);
                }
            }
            // Per-instruction. `live` tracks registers live AFTER `i`, walked
            // backward from the block's live-out.
            let mut live_regs = live_out[bi].clone();
            for i in (b.start..b.end).rev() {
                let after = live_webs(&live_regs, &webs.reach_after[i]);
                for a in &after {
                    for c in &after {
                        edge(*a, *c, &mut adj);
                    }
                }
                if let Some(e) = &eff[i] {
                    for d in &e.defs {
                        let dw = webs.def_web[&(i, *d)];
                        for c in &after {
                            edge(dw, *c, &mut adj);
                        }
                        // Co-defined registers (Umull rdlo/rdhi, a Pop list)
                        // are simultaneously written and must stay distinct.
                        for d2 in &e.defs {
                            edge(dw, webs.def_web[&(i, *d2)], &mut adj);
                        }
                        // INCREMENT 4 — EARLY-CLOBBER (`pair_early_clobber`).
                        // An i64 pair op EXPANDS downstream into a
                        // multi-instruction sequence that re-reads its sources
                        // AFTER writing a destination: `I64Ldr` is
                        // `LDR rdlo,[base,#off]; LDR rdhi,[base,#off+4]`, so
                        // `rdlo` sharing a register with `base` makes the SECOND
                        // load read a base the FIRST one clobbered. Ordinary
                        // liveness says `base` is dead at the load and would
                        // happily coalesce them; this edge is what forbids it.
                        // Stated as an interference EDGE rather than by widening
                        // `defs`, so it costs no spurious validator rejections.
                        if pair_early_clobber(&instrs[i].op) {
                            for u in &e.uses {
                                for uw in webs.reach_before[i].get(u).into_iter().flatten() {
                                    edge(dw, *uw, &mut adj);
                                }
                            }
                        }
                    }
                    // INCREMENT 4 — the 16-bit-form REGISTER RANGE constraint.
                    // `pair_low_reg_only` names the operands whose downstream
                    // expansion encodes them with a 3-bit `rd` field, so R8
                    // TRANSMUTES the instruction (`MOVS r8,#0` -> `CMP r0,#0`,
                    // the #180/#311 class). Expressed with the machinery already
                    // here: R8's ENTRY web is identity-pinned to R8 by pin (a),
                    // so an edge to it removes R8 from the operand web's
                    // candidate colours — no new colourer concept, and it is
                    // impossible to satisfy the edge and still emit R8.
                    for r in pair_low_reg_only(&instrs[i].op) {
                        let Some(&dw) = webs.def_web.get(&(i, r)) else {
                            return decline("low-reg-operand-not-a-def");
                        };
                        let Some(&r8w) = webs.entry_web.get(&Reg::R8) else {
                            return decline("no-r8-web");
                        };
                        edge(dw, r8w, &mut adj);
                    }
                    for d in &e.defs {
                        live_regs.remove(d);
                    }
                    for u in &e.uses {
                        live_regs.insert(*u);
                    }
                }
            }
        }

        // ---- Pins ------------------------------------------------------
        let pool_index: BTreeMap<Reg, usize> =
            pool.iter().enumerate().map(|(i, r)| (*r, i)).collect();
        let mut pins: BTreeMap<usize, usize> = BTreeMap::new();
        let mut assignment: BTreeMap<usize, Reg> = BTreeMap::new();
        let mut pool_nodes: BTreeSet<usize> = BTreeSet::new();
        for w in 0..webs.n_webs {
            let r = webs.reg_of[w];
            match pool_index.get(&r) {
                None => {
                    // Reserved (R9-R12, SP, LR, PC): identity, never coloured.
                    assignment.insert(w, r);
                }
                Some(_) => {
                    pool_nodes.insert(w);
                }
            }
        }
        let pin = |w: usize, pins: &mut BTreeMap<usize, usize>| {
            if let Some(&idx) = pool_index.get(&webs.reg_of[w]) {
                pins.insert(w, idx);
            }
        };
        // (a) Function inputs arrive in their incoming registers.
        for w in webs.entry_web.values() {
            pin(*w, &mut pins);
        }
        // (b) The exit contract: whatever holds an exit-observable register at a
        //     sink keeps that register. Mirrors `validate_cfg_rewrite`'s seed.
        for b in blocks.iter() {
            if !b.succ.is_empty() {
                continue;
            }
            for r in exit_live(instrs, b.end) {
                for w in webs.reach_after[b.end - 1].get(&r).into_iter().flatten() {
                    pin(*w, &mut pins);
                }
            }
        }
        // (c) ARCHITECTURAL REGISTER OPERANDS. Two classes, one rule: these
        //     registers are fixed by the architecture or by the ABI, not chosen
        //     by the allocator, so every web feeding or produced by them is
        //     IDENTITY-pinned.
        //
        //     * `Push`/`Pop` register lists (#888): a bitmask whose stack layout
        //       is register-NUMBER order, matched pairwise between prologue and
        //       epilogue, carrying the #490 callee-saved contract. Recolouring
        //       one restores registers from a stack image laid out for different
        //       ones — a real latent miscompile found in v0.53.
        //     * CALL operands (increment 3): the argument registers a `bl`/`blx`
        //       reads and the `{R0..R3, R12, LR}` it clobbers are the AAPCS
        //       contract. The call op itself is emitted VERBATIM (the apply phase
        //       below re-checks that), so its webs must land on their own
        //       registers — pinning them here is what makes that true rather than
        //       hoped for.
        for (i, ins) in instrs.iter().enumerate() {
            if !matches!(&ins.op, ArmOp::Push { .. } | ArmOp::Pop { .. })
                && call_effect(&ins.op).is_none()
            {
                continue;
            }
            let Some(e) = &eff[i] else { return None };
            for u in &e.uses {
                for w in webs.reach_before[i].get(u).into_iter().flatten() {
                    pin(*w, &mut pins);
                }
            }
            for d in &e.defs {
                pin(webs.def_web[&(i, *d)], &mut pins);
            }
        }

        // ---- #677 absent-colour blockers -------------------------------
        // A pool register with NO web in this function is not thereby a free
        // rename target. Whole-function scope makes an absent CALLER-saved
        // register genuinely free, but introducing an absent CALLEE-saved one
        // would grow the prologue this pass exists to shrink — and on the direct
        // path the prologue push list is fixed before we run. Block every absent
        // pool colour, exactly the shipping pass's discipline: an identity-shaped
        // colouring within the PRESENT registers always exists, so this never
        // costs a recolouring the original bytes did not already have.
        let present: BTreeSet<Reg> = (0..webs.n_webs)
            .filter(|w| adj.get(w).is_some_and(|a| !a.is_empty()) || pins.contains_key(w))
            .map(|w| webs.reg_of[w])
            .chain(instrs.iter().enumerate().flat_map(|(i, _)| {
                eff[i]
                    .iter()
                    .flat_map(|e| e.defs.iter().chain(e.uses.iter()).copied())
                    .collect::<Vec<_>>()
            }))
            .collect();
        let mut next_blocker = webs.n_webs;
        for (idx, reg) in pool.iter().enumerate() {
            if present.contains(reg) {
                continue;
            }
            let blocker = next_blocker;
            next_blocker += 1;
            pins.insert(blocker, idx);
            for w in &pool_nodes {
                adj.entry(*w).or_default().insert(blocker);
            }
            adj.insert(blocker, pool_nodes.iter().copied().collect());
        }

        // ---- Colour ----------------------------------------------------
        let pool_adj: BTreeMap<usize, BTreeSet<usize>> = adj
            .iter()
            .filter(|(w, _)| pool_nodes.contains(w) || pins.contains_key(w))
            .filter(|(w, _)| **w >= webs.n_webs || pool_nodes.contains(w))
            .map(|(w, nbrs)| {
                (
                    *w,
                    nbrs.iter()
                        .copied()
                        .filter(|m| *m >= webs.n_webs || pool_nodes.contains(m))
                        .collect(),
                )
            })
            .collect();
        // RQ-60-RACOST increment 2 (#242): the REAL-ENCODER COST MODEL across
        // joins. Occurrences carry a 10^loop_depth weight (natural loops from
        // the CFG this pass already built), and every colour choice is priced
        // by the caller-supplied encoder's own byte lengths — see
        // `color_webs_costed` for the select and its history.
        let depths = block_loop_depths(&blocks);
        let mut ix = OccurrenceIndex::new();
        for (bi, b) in blocks.iter().enumerate() {
            let wgt = loop_weight(depths[bi]);
            #[allow(clippy::needless_range_loop)] // `i` is a stream index recorded in the entry
            for i in b.start..b.end {
                let Some(e) = &eff[i] else { continue };
                let mut uses: BTreeMap<Reg, usize> = BTreeMap::new();
                let mut resolved = true;
                for u in &e.uses {
                    match webs.reach_before[i].get(u) {
                        Some(s) if s.len() == 1 => {
                            uses.insert(*u, *s.iter().next()?);
                        }
                        // A non-singleton reaching set at a use means the
                        // apply phase will decline this function anyway; for
                        // PRICING, skip the instruction — the skip is
                        // candidate-independent, so no comparison tilts.
                        _ => {
                            resolved = false;
                            break;
                        }
                    }
                }
                if !resolved {
                    continue;
                }
                let defs: BTreeMap<Reg, usize> = e
                    .defs
                    .iter()
                    .map(|d| (*d, webs.def_web[&(i, *d)]))
                    .collect();
                ix.push(i, uses, defs, wgt);
            }
        }
        let (web_w, web_span) = web_weights(&ix, instrs, enc);
        // Each web's ORIGINAL colour — the identity hint's input.
        let orig_colour: BTreeMap<usize, usize> = (0..webs.n_webs)
            .filter_map(|w| pool_index.get(&webs.reg_of[w]).map(|&c| (w, c)))
            .collect();
        let mut occ = |w: usize, c: usize, assigned: &BTreeMap<usize, usize>| {
            occurrence_bytes(&ix, instrs, pool, w, c, assigned, enc)
        };
        let (coloring, spilled) = color_webs_costed(
            &pool_adj,
            pool.len(),
            &pins,
            &web_w,
            &web_span,
            &orig_colour,
            caller_saved_prefix(pool),
            &mut occ,
        );
        if !spilled.is_empty() {
            // Spill-code insertion across joins is a named follow-up; the
            // shipping path HAS spill support, so decline to it.
            return decline("needs-spill");
        }
        for (w, c) in &coloring {
            if *w < webs.n_webs {
                assignment.insert(*w, pool[*c]);
            }
        }

        // Defense in depth, independent of the colourer: re-check every
        // interference edge against the final assignment.
        for (a, nbrs) in &adj {
            if *a >= webs.n_webs {
                continue;
            }
            for b in nbrs {
                if *b >= webs.n_webs {
                    continue;
                }
                // Skip edges whose BOTH endpoints are PINNED (identity-fixed by
                // the ABI/architecture, or reserved and never coloured at all).
                // A pinned web's register is not a choice the colourer made — it
                // is the original's — so two pinned webs "sharing" a register is
                // exactly the original code's behaviour, not a conflict. The
                // edge exists only because the conservative exit contract makes
                // a register live at the return with NO unifying use, so its
                // entry web and its arm-local def web both land in the sink's
                // live set (measured: 16 corpus functions declined wholesale on
                // `1(R1)~16(R1) -> R1/R1`). The shipping pass exempts the same
                // pair class for the same reason. Pool↔pool and pinned↔free
                // edges are still enforced, and `validate_cfg_rewrite` proves
                // the dataflow either way.
                let fixed = |w: &usize| pins.contains_key(w) || !pool_nodes.contains(w);
                if fixed(a) && fixed(b) {
                    continue;
                }
                match (assignment.get(a), assignment.get(b)) {
                    (Some(x), Some(y)) if x != y => {}
                    _ => {
                        if std::env::var("SYNTH_GRAPH_ALLOC_DUMP").is_ok() {
                            eprintln!(
                                "[ga-dump] edge-recheck {a}({:?})~{b}({:?}) -> {:?}/{:?}",
                                webs.reg_of[*a],
                                webs.reg_of[*b],
                                assignment.get(a),
                                assignment.get(b)
                            );
                        }
                        return decline("edge-recheck");
                    }
                }
            }
        }

        if std::env::var("SYNTH_GRAPH_ALLOC_DUMP").is_ok() {
            for w in 0..webs.n_webs {
                if !pool_nodes.contains(&w) {
                    continue;
                }
                eprintln!(
                    "[ga-dump] web {w} reg={:?} pin={:?} -> {:?} nbrs={:?}",
                    webs.reg_of[w],
                    pins.get(&w),
                    assignment.get(&w),
                    adj.get(&w)
                );
            }
        }

        // ---- Apply -----------------------------------------------------
        let mut out: Vec<ArmInstruction> = Vec::with_capacity(instrs.len());
        for (i, ins) in instrs.iter().enumerate() {
            let Some(e) = &eff[i] else {
                out.push(ins.clone()); // control flow: verbatim
                continue;
            };
            let mut use_map: BTreeMap<Reg, Reg> = BTreeMap::new();
            for u in &e.uses {
                // A USE has exactly one reaching web: it unified every
                // definition that reaches it. A non-singleton here would mean
                // the replay disagrees with the fixpoint — decline, never guess.
                let set = webs.reach_before[i].get(u)?;
                if set.len() != 1 {
                    return decline("ambiguous-reaching-web");
                }
                let w = *set.iter().next()?;
                use_map.insert(*u, *assignment.get(&w)?);
            }
            let mut def_map: BTreeMap<Reg, Reg> = BTreeMap::new();
            for d in &e.defs {
                let w = webs.def_web[&(i, *d)];
                def_map.insert(*d, *assignment.get(&w)?);
            }
            // INCREMENT 3: a CALL is emitted VERBATIM — its operands are the
            // AAPCS contract, not a colouring choice (and `validate_cfg_rewrite`
            // requires non-straight-line ops to be identical on both sides). Pin
            // (c) above already forces both maps to the identity here; re-check
            // it rather than assume it, and DECLINE on any disagreement. A silent
            // `rewrite_op_maps` on a call would be the miscompile this increment
            // exists to make impossible.
            if !is_straight_line(&ins.op) {
                if use_map.iter().any(|(a, b)| a != b) || def_map.iter().any(|(a, b)| a != b) {
                    return decline("call-operand-recoloured");
                }
                out.push(ins.clone());
                continue;
            }
            out.push(ArmInstruction {
                op: rewrite_op_maps(&ins.op, &use_map, &def_map)?,
                source_line: ins.source_line,
            });
        }

        // ---- The acceptance oracle -------------------------------------
        // A rewrite the CFG-lifted trace-equality validator cannot justify is
        // DROPPED (the function falls back to the shipping pass) — never
        // emitted. `validate_cfg_rewrite` computes its own exit contract, so
        // this cannot be weakened from here.
        match validate_cfg_rewrite(instrs, &out, &blocks) {
            Ok(()) => {
                if out == instrs {
                    // Identity rewrite: let the shipping pass have the function
                    // (it may still find a segment-local win we did not).
                    decline("identity-colouring")
                } else {
                    // Announce the dataflow ACCEPT before the second gate runs.
                    // This line is the machine-checkable half of the v0.53
                    // finding: on the mutated compiler it is printed for the
                    // very function VCR-VER-004 then rejects, so "the two
                    // existing instruments are green on this input" is an
                    // OBSERVATION, not a claim
                    // (`scripts/repro/vcr_ver_004_instrument_independence.py`).
                    if std::env::var("SYNTH_GRAPH_ALLOC_STATS").is_ok() {
                        eprintln!(
                            "[graph-alloc] join colouring ACCEPTED by validate_cfg_rewrite (dataflow)"
                        );
                    }
                    // VCR-VER-004: and the ABI observable contract, which shares
                    // neither the exit contract nor the CFG with this pass. This
                    // is the gate that catches the v0.53 mutation the two
                    // dataflow validators both accept.
                    abi_gate(instrs, out)
                }
            }
            Err(v) => {
                if std::env::var("SYNTH_GRAPH_ALLOC_STATS").is_ok() {
                    eprintln!("[graph-alloc] join colouring REJECTED by validator: {v:?}");
                }
                None
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::{ArmOp, Operand2};

    fn ins(op: ArmOp) -> ArmInstruction {
        ArmInstruction {
            op,
            source_line: None,
        }
    }

    /// Unit-test sizer: the synthesis-side byte estimator. Production wiring
    /// passes the REAL encoder from `synth-backend` (a crate this one cannot
    /// depend on); the structural properties these tests pin are
    /// sizer-independent, and the estimator is itself oracle-pinned to the
    /// real encoder for the optimized path (`estimator_encoder_agreement`).
    fn enc_est(op: &ArmOp) -> Option<usize> {
        Some(crate::estimate_arm_byte_size(op))
    }

    const POOL: [Reg; 9] = [
        Reg::R0,
        Reg::R1,
        Reg::R2,
        Reg::R3,
        Reg::R4,
        Reg::R5,
        Reg::R6,
        Reg::R7,
        Reg::R8,
    ];

    #[test]
    fn colours_a_straight_line_function_and_validates() {
        // r2 = r0 + r1 ; r0 = r2 + r1  (all straight-line, fits the pool)
        let body = vec![
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R2,
                op2: Operand2::Reg(Reg::R1),
            }),
            // A WELL-FORMED function: it returns. VCR-VER-004 declines a stream
            // with no return sink rather than passing it vacuously, so a fixture
            // without an epilogue is not a function this pass may apply to.
            ins(ArmOp::Pop {
                regs: vec![Reg::R4, Reg::PC],
            }),
        ];
        let out = reallocate(&body, &POOL, &enc_est).expect("straight-line function colours");
        // The rewrite must pass the trace-equality validator (it did, or
        // reallocate would have returned None) — and it preserves length.
        assert_eq!(out.len(), body.len());
        assert_eq!(validate_segment_rewrite(&body, &out), Ok(()));
    }

    /// NON-VACUITY: prove the Chaitin/Briggs simplify/select core actually PLACES
    /// a FREE (unpinned) node — not that the pins alone determine everything. A
    /// register defined, used, then REDEFINED has an EARLIER range that is
    /// neither a segment input (def != 0) nor the register's last-opened range
    /// (live-out) — so it is unpinned, and the colourer must choose its register.
    /// We give a SMALL pool so a valid colouring requires reusing a colour the
    /// pins do not force: only the select phase can find it.
    #[test]
    fn simplify_select_places_a_free_interior_range() {
        // Pool = {R0, R1} — only two colours. Body (all in-pool registers):
        //   r0 = r0 + r1   ; A: r0 redefined — its INPUT range (def 0) is pinned,
        //                    this new r0 range is last-opened → pinned to colour 0
        //   r1 = r0 + r1   ; r1 redefined: its input range pinned, new one
        //                    last-opened → pinned to colour 1
        // Every range here is input-or-last-opened, so to get a genuinely FREE
        // interior range we need a THIRD def of some register that is later
        // overwritten. Use r0 defined, consumed, then r0 overwritten:
        //   0: r0 = r0 + r1   (r0 range A: def=0? no, def=0 is the INPUT range;
        //                      this DEF opens range A' — def=0 is instr 0's def,
        //                      which IS index 0 → treated as input-pinned. avoid.)
        // Cleaner: start the free range at a NON-zero instruction.
        //   0: r1 = r0 + r0     ; opens r1 range (def=0 index → but this is the
        //                         FIRST def of r1, at instr 0). To keep it
        //                         unpinned we must redefine r1 later AND it must
        //                         not be def==0. `straight_line_value_ranges`
        //                         marks def with the instruction INDEX, and the
        //                         input pin is `def == 0` meaning the range opened
        //                         at index 0. So a def at index 0 is input-pinned.
        //   Use three instructions so the middle def is at index 1 (not 0) and is
        //   overwritten at index 2 (so not last-opened):
        //   0: r1 = r0 + r0     ; r1 def@0 (input-pinned), r0 input (pinned)
        //   1: r1 = r0 + r0     ; r1 def@1 — NOT index 0, and OVERWRITTEN next →
        //                         neither input nor last-opened ⇒ FREE
        //   2: r1 = r0 + r0     ; r1 def@2 last-opened (live-out) → pinned
        let small_pool = [Reg::R0, Reg::R1];
        let body = vec![
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R0),
            }),
            // 3: the epilogue — see the note in the test above. Appending it at
            // index 3 leaves the def indices this test reasons about (0, 1, 2)
            // untouched.
            ins(ArmOp::Pop {
                regs: vec![Reg::R4, Reg::PC],
            }),
        ];
        // The r1 range opened at instruction 1 is free (def index 1, overwritten
        // at 2). It is dead-on-arrival (defined, immediately overwritten), so it
        // does not interfere with the pinned r0/r1 ranges beyond r0; the colourer
        // simplifies+selects a colour for it. A `Some` result that PASSES the
        // trace-equality validator proves the free-placement path ran soundly.
        let out = reallocate(&body, &small_pool, &enc_est).expect("free interior range colours");
        assert_eq!(out.len(), body.len());
        assert_eq!(
            validate_segment_rewrite(&body, &out),
            Ok(()),
            "the colouring of the free interior range must preserve dataflow"
        );
    }

    /// RQ-60-RACOST increment 1 (#242) — RED-FIRST. A `movw r4 / movt r4`
    /// materialization whose MOVW-side range is FREE (born mid-function,
    /// closed by the MOVT) while the MOVT-side range is r4's last-opened
    /// range and therefore exit-pinned to R4. Coloured independently, the
    /// free use-side range takes the lowest free colour (R0 — its only
    /// neighbour is the R1-pinned filler) while the def side keeps R4, and
    /// the after-the-fact RMW check refused the whole function
    /// (`SelectMove/Movt /rmw-colour-mismatch` — re-derived on main as the
    /// largest attributed `single-block` bucket, 26 of 42 on the relocatable
    /// repro corpus). BEFORE the tied-web merge this `reallocate` returned
    /// `None`; with the use/def web merged ahead of colouring the mismatch is
    /// unrepresentable — the web takes the pinned colour and the function
    /// allocates.
    #[test]
    fn tied_rmw_web_allocates_instead_of_declining() {
        let body = vec![
            // Filler at index 0 so the interesting defs are not input-pinned;
            // r1 stays live to the final add, so the movw range cannot share
            // R1 and the two sides' neighbourhoods genuinely differ.
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Imm(1),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R4,
                imm16: 7,
            }),
            ins(ArmOp::Movt {
                rd: Reg::R4,
                imm16: 3,
            }),
            ins(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R4),
            }),
            // Return sink (VCR-VER-004 needs one); pops NO pool register, so
            // the Movt-side range stays r4's last-opened range (exit-pinned).
            ins(ArmOp::Pop {
                regs: vec![Reg::PC],
            }),
        ];
        let out = reallocate(&body, &POOL, &enc_est)
            .expect("tied rmw web must colour instead of declining (red-first: was None)");
        assert_eq!(out.len(), body.len());
        assert_eq!(validate_segment_rewrite(&body, &out), Ok(()));
        // The movw/movt pair still lands on ONE register — the RMW contract
        // the merge exists to make structural.
        let (movw_rd, movt_rd) = match (&out[1].op, &out[2].op) {
            (ArmOp::Movw { rd: a, .. }, ArmOp::Movt { rd: b, .. }) => (*a, *b),
            other => panic!("movw/movt shape must be preserved, got {other:?}"),
        };
        assert_eq!(movw_rd, movt_rd, "tied use/def web split across registers");
    }

    /// The tied web is placed as ONE node when it is fully free: `pop {r4,pc}`
    /// redefines r4, so neither RMW-side range is exit-pinned and the whole
    /// web is the colourer's to place — both halves of the materialization
    /// land on the SAME register and the rewrite validates. Under the
    /// increment-2 cost model the movw/movt occurrences price byte-equal in
    /// every register, so the tie-break's caller-saved evacuation places the
    /// web in scratch (a callee-saved home would keep a prologue save alive
    /// downstream); the RMW contract — one register for both halves — is what
    /// this test pins.
    #[test]
    fn tied_rmw_web_recolours_together_and_validates() {
        let body = vec![
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Imm(1),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R4,
                imm16: 7,
            }),
            ins(ArmOp::Movt {
                rd: Reg::R4,
                imm16: 3,
            }),
            ins(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R4),
            }),
            ins(ArmOp::Pop {
                regs: vec![Reg::R4, Reg::PC],
            }),
        ];
        let out = reallocate(&body, &POOL, &enc_est).expect("free tied web colours");
        assert_eq!(validate_segment_rewrite(&body, &out), Ok(()));
        let (movw_rd, movt_rd) = match (&out[1].op, &out[2].op) {
            (ArmOp::Movw { rd: a, .. }, ArmOp::Movt { rd: b, .. }) => (*a, *b),
            other => panic!("movw/movt shape must be preserved, got {other:?}"),
        };
        assert_eq!(movw_rd, movt_rd, "tied use/def web split across registers");
        assert!(
            matches!(movw_rd, Reg::R0 | Reg::R1 | Reg::R2 | Reg::R3),
            "byte-equal minima tie-break: a fully-free tied web evacuates its \
             callee-saved home into caller-saved scratch, got {movw_rd:?}"
        );
    }

    /// The tie scan is PROBED from the shipped rewriter, so it ties exactly
    /// the fields `rewrite_op` would refuse to split — an RMW field ties, a
    /// same-register rd/rn coincidence does not (over-merging there would
    /// cost colouring freedom for nothing).
    #[test]
    fn tied_pairs_probe_ties_rmw_fields_only() {
        use crate::rules::Condition;
        // movw r4 (vreg 0) ; movt r4 (use = vreg 0, def = vreg 1): tied.
        let rmw = vec![
            ins(ArmOp::Movw {
                rd: Reg::R4,
                imm16: 1,
            }),
            ins(ArmOp::Movt {
                rd: Reg::R4,
                imm16: 2,
            }),
        ];
        assert_eq!(tied_range_pairs(&rmw), Some(vec![(0, 1)]));
        // SelectMove rd is def AND use of one field: r2-use = vreg 0,
        // r3 = vreg 1, r2-def = vreg 2 → tied (0, 2).
        let sel = vec![ins(ArmOp::SelectMove {
            rd: Reg::R2,
            rm: Reg::R3,
            cond: Condition::EQ,
        })];
        assert_eq!(tied_range_pairs(&sel), Some(vec![(0, 2)]));
        // add r0, r0, #1: r0 appears as use and def, but rd/rn are SEPARATE
        // fields a rename may legally split — not tied.
        let add = vec![ins(ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Imm(1),
        })];
        assert_eq!(tied_range_pairs(&add), Some(vec![]));
    }

    /// RQ-60-RACOST increment 2 — RED-FIRST for the measured select. Under a
    /// sizer that prices any R8-touching encoding wide (4 B) and everything
    /// else narrow (2 B) — the real Thumb-2 high-register widening in
    /// miniature — a free web homed in R8 with three occurrences must MOVE to
    /// a strictly cheaper register (6 B vs 12 B measured), where increment 1's
    /// identity bias kept it home. The def and every use land together on the
    /// new register, and the rewrite still validates.
    #[test]
    fn cost_model_moves_web_off_measured_wide_register() {
        let wide_r8 = |op: &ArmOp| -> Option<usize> {
            Some(if format!("{op:?}").contains("R8") {
                4
            } else {
                2
            })
        };
        let body = vec![
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Imm(1),
            }),
            ins(ArmOp::Mov {
                rd: Reg::R8,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R8),
            }),
            // R0 is redefined AFTER the R8 web dies, so its exit equation is
            // owned by this def and the web may legally move into R0 (every
            // register's LAST range is exit-pinned in a whole straight-line
            // segment, which is what forbids most rename targets).
            ins(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Reg(Reg::R2),
            }),
            // `pop {r8, pc}` redefines R8, so the interior web is FREE (not
            // exit-pinned) and the colourer must place it.
            ins(ArmOp::Pop {
                regs: vec![Reg::R8, Reg::PC],
            }),
        ];
        let out = reallocate(&body, &POOL, &wide_r8).expect("measured-cost function colours");
        assert_eq!(validate_segment_rewrite(&body, &out), Ok(()));
        let moved = match (&out[1].op, &out[2].op) {
            (
                ArmOp::Mov { rd, .. },
                ArmOp::Add {
                    op2: Operand2::Reg(u1),
                    ..
                },
            ) => {
                assert_eq!(rd, u1, "def and use must share the new home");
                *rd
            }
            other => panic!("shape must be preserved, got {other:?}"),
        };
        assert_ne!(
            moved,
            Reg::R8,
            "a web measured 2x wider in its own home must move (red-first: \
             the identity bias kept it in R8)"
        );
    }

    /// The dual: when the sizer refuses (None) every register EXCEPT the
    /// web's own home, the candidate set is empty and the select must fall
    /// back to the own colour — an unencodable candidate is EXCLUDED, never
    /// priced optimistically (the #180/#311 class).
    #[test]
    fn cost_model_excludes_unencodable_candidates() {
        let only_r8_encodes = |op: &ArmOp| -> Option<usize> {
            let s = format!("{op:?}");
            // Ops not touching R8 (the filler, the pop) size normally; an
            // R8-web occurrence re-homed anywhere else refuses to size.
            if s.contains("R8") || !s.contains('R') {
                Some(2)
            } else {
                None
            }
        };
        let body = vec![
            ins(ArmOp::Mov {
                rd: Reg::R8,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R8,
                op2: Operand2::Imm(1),
            }),
            ins(ArmOp::Pop {
                regs: vec![Reg::R8, Reg::PC],
            }),
        ];
        let out = reallocate(&body, &POOL, &only_r8_encodes).expect("colours");
        assert_eq!(validate_segment_rewrite(&body, &out), Ok(()));
        assert!(
            matches!(out[0].op, ArmOp::Mov { rd: Reg::R8, .. }),
            "with every other candidate unencodable the web keeps its home: {:?}",
            out[0].op
        );
    }

    /// The loop-depth input of the cost model: a self-loop diamond
    /// (0 → 1 → 2 → {1, 3}) has exactly its loop body {1, 2} at depth 1.
    #[test]
    fn block_loop_depths_counts_natural_loops() {
        use crate::liveness::BasicBlock;
        let blocks = vec![
            BasicBlock {
                start: 0,
                end: 1,
                succ: vec![1],
            },
            BasicBlock {
                start: 1,
                end: 2,
                succ: vec![2],
            },
            BasicBlock {
                start: 2,
                end: 3,
                succ: vec![1, 3],
            },
            BasicBlock {
                start: 3,
                end: 4,
                succ: vec![],
            },
        ];
        assert_eq!(joins::block_loop_depths(&blocks), vec![0, 1, 1, 0]);
        // And the weight saturates at 10^4 rather than overflowing.
        assert_eq!(loop_weight(0), 1);
        assert_eq!(loop_weight(2), 100);
        assert_eq!(loop_weight(40), 10_000);
    }

    #[test]
    fn declines_on_control_flow() {
        // A branch makes it non-straight-line → decline (None).
        let body = vec![
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::B {
                label: ".exit".into(),
            }),
        ];
        assert!(
            reallocate(&body, &POOL, &enc_est).is_none(),
            "control flow is outside the bounded whole-straight-line scope"
        );
    }

    #[test]
    fn declines_on_call() {
        let body = vec![ins(ArmOp::Bl {
            label: "func_1".into(),
        })];
        assert!(
            reallocate(&body, &POOL, &enc_est).is_none(),
            "a call is unmodeled — decline to the shipping path"
        );
    }

    #[test]
    fn declines_on_empty() {
        assert!(reallocate(&[], &POOL, &enc_est).is_none());
    }

    // ================================================================
    // VCR-DEC-001 increment 2 — colouring ACROSS if/else joins.
    // ================================================================

    use crate::liveness::{RewriteViolation, validate_cfg_rewrite};
    use crate::rules::{Condition, MemAddr};

    fn lbl(n: &str) -> ArmInstruction {
        ins(ArmOp::Label { name: n.into() })
    }
    fn mem(base: Reg, offset: i32) -> MemAddr {
        MemAddr {
            base,
            offset,
            offset_reg: None,
        }
    }

    /// The canonical diamond: `push` / `cmp` / `bcc else` / then-arm writes R2 /
    /// `b end` / else-arm writes R4 / `end:` / `pop`. The two arms' values are
    /// never simultaneously live, so a whole-function colouring may give BOTH
    /// the same register — the recolouring the segment-based shipping pass
    /// structurally cannot make (the else-arm's `movw` is its segment's
    /// instruction 0, hence pinned as a segment input).
    fn diamond() -> Vec<ArmInstruction> {
        vec![
            ins(ArmOp::Push {
                regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::LR],
            }),
            ins(ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            }),
            ins(ArmOp::Bcc {
                cond: Condition::EQ,
                label: ".else".into(),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 300,
            }),
            ins(ArmOp::Str {
                rd: Reg::R2,
                addr: mem(Reg::R11, 16),
            }),
            ins(ArmOp::B {
                label: ".end".into(),
            }),
            lbl(".else"),
            ins(ArmOp::Movw {
                rd: Reg::R4,
                imm16: 400,
            }),
            ins(ArmOp::Str {
                rd: Reg::R4,
                addr: mem(Reg::R11, 16),
            }),
            lbl(".end"),
            ins(ArmOp::Pop {
                regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::PC],
            }),
        ]
    }

    /// THE POINT OF INCREMENT 2. On the diamond the allocator must actually
    /// recolour the else-arm off its callee-saved register — that is what lets
    /// the downstream `shrink_callee_saved_saves` drop the prologue entry. A
    /// `None` here means the join path regressed to increment 1's reach.
    #[test]
    fn colours_across_an_if_else_join() {
        let body = diamond();
        let out =
            reallocate(&body, &POOL, &enc_est).expect("the diamond must colour across its join");
        assert_eq!(out.len(), body.len());
        assert_ne!(out, body, "an identity rewrite gates nothing");
        // The else-arm's R4 value moved OFF the callee-saved register.
        assert!(
            !matches!(out[7].op, ArmOp::Movw { rd: Reg::R4, .. }),
            "the else-arm value should have left R4: {:?}",
            out[7].op
        );
        // Control flow is untouched — a register allocator renames operands.
        for i in [2usize, 5, 6, 9] {
            assert_eq!(out[i].op, body[i].op, "control flow rewritten at {i}");
        }
        // The architectural register lists are identity-pinned (#888).
        assert_eq!(out[0].op, body[0].op, "prologue push list recoloured");
        assert_eq!(out[10].op, body[10].op, "epilogue pop list recoloured");
    }

    /// RED-FIRST for the CFG validator: a rewrite that renames a value in ONE
    /// arm of a join while its consumer past the join still reads the ORIGINAL
    /// register is a value-flow break on exactly one path. The straight-line
    /// validator cannot see it (each arm validates fine in isolation); the
    /// CFG-lifted must-fixpoint has to reject it.
    #[test]
    fn cfg_validator_rejects_a_one_armed_rename_across_a_join() {
        // then: r2 = 1 ; else: r2 = 2 ; end: r0 = r2 + r2
        let body = vec![
            ins(ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            }),
            ins(ArmOp::Bcc {
                cond: Condition::EQ,
                label: ".else".into(),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 1,
            }),
            ins(ArmOp::B {
                label: ".end".into(),
            }),
            lbl(".else"),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 2,
            }),
            lbl(".end"),
            ins(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R2,
                op2: Operand2::Reg(Reg::R2),
            }),
            ins(ArmOp::Bx { rm: Reg::LR }),
        ];
        let blocks = joins::build_cfg(&body).expect("label-form CFG");
        assert_eq!(
            validate_cfg_rewrite(&body, &body, &blocks),
            Ok(()),
            "the identity rewrite must be accepted (else the RED below is vacuous)"
        );
        // Rename ONLY the then-arm's definition. The join's consumer still reads
        // R2, so the then path now adds an undefined R3.
        let mut bad = body.clone();
        bad[2] = ins(ArmOp::Movw {
            rd: Reg::R3,
            imm16: 1,
        });
        assert!(
            matches!(
                validate_cfg_rewrite(&body, &bad, &blocks),
                Err(RewriteViolation::DefClobbersEquation { .. })
                    | Err(RewriteViolation::EntryNotIdentity { .. })
            ),
            "a one-armed rename across a join must be REJECTED, got {:?}",
            validate_cfg_rewrite(&body, &bad, &blocks)
        );
    }

    /// A register allocator renames operands; it never rewrites control flow.
    /// The validator enforces that structurally, so a mutated branch target or
    /// condition can never be smuggled through as "a rename".
    #[test]
    fn cfg_validator_rejects_a_rewritten_branch() {
        let body = diamond();
        let blocks = joins::build_cfg(&body).expect("label-form CFG");
        let mut bad = body.clone();
        bad[2] = ins(ArmOp::Bcc {
            cond: Condition::NE, // inverted condition
            label: ".else".into(),
        });
        assert_eq!(
            validate_cfg_rewrite(&body, &bad, &blocks),
            Err(RewriteViolation::ShapeMismatch { index: 2 })
        );
    }

    /// The exit contract has teeth: clobbering a register the caller can observe
    /// past the return must be rejected even though nothing in the function
    /// reads it again.
    #[test]
    fn cfg_validator_rejects_an_exit_observable_clobber() {
        // r0 = 7 ; bx lr   — R0 is the result register.
        let body = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 9,
            }),
            ins(ArmOp::Bx { rm: Reg::LR }),
        ];
        let blocks = joins::build_cfg(&body).expect("CFG");
        assert_eq!(validate_cfg_rewrite(&body, &body, &blocks), Ok(()));
        let mut bad = body.clone();
        bad[0] = ins(ArmOp::Movw {
            rd: Reg::R3,
            imm16: 7,
        });
        assert!(
            validate_cfg_rewrite(&body, &bad, &blocks).is_err(),
            "moving the result off R0 must be rejected"
        );
    }

    /// #888: a `pop {…, pc}` is a RETURN, not a register-list def that a
    /// segment-local view may recolour. The CFG builder must make it a sink, so
    /// a mid-stream one ends its block and the code after it is unreachable —
    /// which this pass declines rather than colour on a guessed CFG.
    #[test]
    fn mid_stream_pop_pc_is_a_return_sink() {
        let body = vec![
            ins(ArmOp::Push {
                regs: vec![Reg::R4, Reg::LR],
            }),
            ins(ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            }),
            ins(ArmOp::Bcc {
                cond: Condition::EQ,
                label: ".tail".into(),
            }),
            ins(ArmOp::Pop {
                regs: vec![Reg::R4, Reg::PC],
            }),
            lbl(".tail"),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 5,
            }),
            ins(ArmOp::Pop {
                regs: vec![Reg::R4, Reg::PC],
            }),
        ];
        let blocks = joins::build_cfg(&body).expect("CFG");
        let early = blocks
            .iter()
            .find(|b| b.end == 4)
            .expect("the mid-stream pop must END a block");
        assert!(
            early.succ.is_empty(),
            "a mid-stream `pop {{…, pc}}` must be a RETURN sink, not a fall-through"
        );
    }

    /// A validator that accepts an EMPTY CFG for a non-empty stream would
    /// certify every rewrite vacuously — the exact failure mode the v0.50 join
    /// attempt's `entry_seed` hacks had. The structural tiling check must
    /// reject it.
    #[test]
    fn cfg_validator_rejects_an_empty_cfg_for_a_nonempty_stream() {
        let body = diamond();
        assert!(
            validate_cfg_rewrite(&body, &body, &[]).is_err(),
            "an empty CFG must NOT validate a non-empty stream"
        );
        // ...and a CFG that does not tile the stream is equally rejected.
        let mut partial = joins::build_cfg(&body).expect("CFG");
        partial.pop();
        assert!(
            validate_cfg_rewrite(&body, &body, &partial).is_err(),
            "a CFG that leaves instructions unwalked must NOT validate"
        );
    }

    /// Pre-resolved NUMERIC branches carry a baked displacement, so a rename
    /// that changes a Thumb encoding width would silently overshoot (#606).
    /// Out of scope by DECLINE, with the reason named.
    #[test]
    fn declines_numeric_branches() {
        let numeric = vec![
            ins(ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            }),
            ins(ArmOp::BCondOffset {
                cond: Condition::EQ,
                offset: 2,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 1,
            }),
            ins(ArmOp::Bx { rm: Reg::LR }),
        ];
        assert_eq!(joins::build_cfg(&numeric), Err("numeric-branch"));
        assert!(reallocate(&numeric, &POOL, &enc_est).is_none());
    }

    // ================================================================
    // VCR-DEC-001 increment 3 — colouring ACROSS CALLS.
    // ================================================================

    /// A `push {r4-r8,lr}` / `pop {r4-r8,pc}`-framed body around one direct
    /// call. The R4 value is born AFTER the call and dies before the return, so
    /// whole-function liveness proves it never crosses the call boundary and it
    /// may live in call-clobbered scratch — the recolouring increment 2 could
    /// not even attempt, because the `bl` made the CFG builder decline the whole
    /// function.
    fn call_body() -> Vec<ArmInstruction> {
        vec![
            ins(ArmOp::Push {
                regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::LR],
            }),
            ins(ArmOp::Bl {
                label: "func_1".into(),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R4,
                imm16: 7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R4,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R4),
            }),
            ins(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Reg(Reg::R4),
            }),
            ins(ArmOp::Pop {
                regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::PC],
            }),
        ]
    }

    /// THE POINT OF INCREMENT 3. A function containing a call must be COLOURED,
    /// not declined — and the value that provably never crosses the call must
    /// leave its callee-saved register. A `None` here means the call model
    /// regressed to increment 2's reach.
    #[test]
    fn colours_across_a_call() {
        let body = call_body();
        let out =
            reallocate(&body, &POOL, &enc_est).expect("a call-containing function must colour");
        assert_eq!(out.len(), body.len());
        assert_ne!(out, body, "an identity rewrite gates nothing");
        // The post-call temporary moved OFF the callee-saved register...
        assert!(
            !matches!(out[2].op, ArmOp::Movw { rd: Reg::R4, .. }),
            "the post-call temporary should have left R4: {:?}",
            out[2].op
        );
        // ...and onto a register the call boundary proves is free THERE (it is
        // defined after the call and dead before the return, so R2/R3 — dead-out
        // at a `pop {…,pc}` — are legal; R0/R1 are not, they are live).
        let landed = match &out[2].op {
            ArmOp::Movw { rd, .. } => *rd,
            other => panic!("shape changed: {other:?}"),
        };
        assert!(
            matches!(landed, Reg::R2 | Reg::R3),
            "expected the temporary in call-clobbered scratch, got {landed:?}"
        );
        // The CALL is emitted verbatim and the architectural register lists are
        // identity-pinned.
        assert_eq!(out[1].op, body[1].op, "the call was rewritten");
        assert_eq!(out[0].op, body[0].op, "prologue push list recoloured");
        assert_eq!(out[5].op, body[5].op, "epilogue pop list recoloured");
        // And the rewrite is certified by the CFG-lifted oracle.
        let blocks = joins::build_cfg(&body).expect("CFG");
        assert_eq!(validate_cfg_rewrite(&body, &out, &blocks), Ok(()));
    }

    /// **RED-FIRST for the shared AAPCS contract — the hazard this increment was
    /// briefed on.** A rewrite that moves a value LIVE ACROSS a call into a
    /// call-clobbered register is a miscompile: the callee is contractually free
    /// to destroy R0-R3/R12/LR, so the value read after the call is garbage.
    ///
    /// Before increment 3 `validate_cfg_rewrite` treated a `bl` as EFFECT-FREE
    /// (a non-straight-line op was required to be identical and then given no
    /// effect), so the equation `(R4, R2)` demanded after the call sailed
    /// straight through it and was discharged by the `mov` above — the validator
    /// would have ACCEPTED this exact rewrite. The MUTATION that proves the
    /// rejection comes from the CALL MODEL and nothing else is in this same
    /// test: the identical rename over the identical instructions with the `bl`
    /// REMOVED is a legal re-colouring and must be ACCEPTED.
    #[test]
    fn cfg_validator_rejects_a_live_value_recoloured_across_a_call() {
        // BOTH R4 and R5 are saved by the prologue, so a R4->R5 re-home is a
        // legal choice for the allocator (an unsaved callee-saved register would
        // be rejected for a DIFFERENT reason — clobbering the caller's value —
        // and would muddy what this test attributes to the call).
        let frame = |mid: Vec<ArmInstruction>| {
            let mut v = vec![ins(ArmOp::Push {
                regs: vec![Reg::R4, Reg::R5, Reg::LR],
            })];
            v.extend(mid);
            v.push(ins(ArmOp::Pop {
                regs: vec![Reg::R4, Reg::R5, Reg::PC],
            }));
            v
        };
        // save an argument in R4 / call / consume the saved value after the call
        let with_call = |home: Reg| {
            frame(vec![
                ins(ArmOp::Mov {
                    rd: home,
                    op2: Operand2::Reg(Reg::R0),
                }),
                ins(ArmOp::Bl {
                    label: "func_1".into(),
                }),
                ins(ArmOp::Add {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(home),
                }),
            ])
        };
        let orig = with_call(Reg::R4);
        let blocks = joins::build_cfg(&orig).expect("a call-containing CFG is now built");
        // Non-vacuity: the identity rewrite is accepted.
        assert_eq!(validate_cfg_rewrite(&orig, &orig, &blocks), Ok(()));
        // A callee-saved -> callee-saved move across the call is legal.
        assert_eq!(
            validate_cfg_rewrite(&orig, &with_call(Reg::R5), &blocks),
            Ok(()),
            "R5 is callee-saved: the callee must preserve it, so this rename is legal"
        );
        // THE RED: R2 is call-clobbered. The value does not survive the call.
        assert!(
            matches!(
                validate_cfg_rewrite(&orig, &with_call(Reg::R2), &blocks),
                Err(RewriteViolation::DefClobbersEquation { .. })
            ),
            "a value live ACROSS a call must not be recoloured into call-clobbered \
             scratch, got {:?}",
            validate_cfg_rewrite(&orig, &with_call(Reg::R2), &blocks)
        );

        // ---- The mutation that proves the CALL MODEL is doing the work -------
        // Same instructions, same rename, `bl` DELETED. Now nothing clobbers R2
        // between the definition and the use, so the rewrite is a legal
        // re-colouring and MUST be accepted. A validator that rejected here would
        // be rejecting for some unrelated reason and the RED above would prove
        // nothing about calls.
        let no_call = |home: Reg| {
            frame(vec![
                ins(ArmOp::Mov {
                    rd: home,
                    op2: Operand2::Reg(Reg::R0),
                }),
                ins(ArmOp::Add {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(home),
                }),
            ])
        };
        let orig_nc = no_call(Reg::R4);
        let blocks_nc = joins::build_cfg(&orig_nc).expect("CFG");
        assert_eq!(
            validate_cfg_rewrite(&orig_nc, &no_call(Reg::R2), &blocks_nc),
            Ok(()),
            "without the call the SAME rename is legal — so the rejection above \
             is attributable to the call model, not to anything else"
        );
    }

    /// The other half of the AAPCS contract: a call READS its argument
    /// registers. A rewrite that renames the definition feeding an argument
    /// leaves the callee reading a stale register, and must be rejected — even
    /// though the `bl` itself is byte-identical on both sides.
    ///
    /// The shape is chosen so the ARGUMENT USE is the ONLY thing that can
    /// reject it: the staged register is R3 and the rewrite moves it to R2, and
    /// BOTH are dead-out at a `pop {…, pc}` return
    /// ([`crate::liveness::cfg_exit_observable`] exempts `{R2, R3, R12, LR}`
    /// there). So the exit contract demands nothing about either, and the
    /// rejection is attributable to `call_effect`'s `uses` alone — emptying them
    /// turns this test green, which is how it is known not to be re-testing the
    /// exit contract by accident (measured: with `uses` intact but the whole
    /// call effect emptied, the R0-staged form this replaced still passed,
    /// because `bx lr`'s STRICT exit seed demanded R0 all by itself).
    #[test]
    fn cfg_validator_rejects_a_renamed_call_argument() {
        let staged = |arg: Reg| {
            vec![
                ins(ArmOp::Push {
                    regs: vec![Reg::R4, Reg::LR],
                }),
                ins(ArmOp::Movw { rd: arg, imm16: 5 }),
                ins(ArmOp::Bl {
                    label: "func_1".into(),
                }),
                ins(ArmOp::Pop {
                    regs: vec![Reg::R4, Reg::PC],
                }),
            ]
        };
        let orig = staged(Reg::R3);
        let blocks = joins::build_cfg(&orig).expect("CFG");
        assert_eq!(validate_cfg_rewrite(&orig, &orig, &blocks), Ok(()));
        assert!(
            matches!(
                validate_cfg_rewrite(&orig, &staged(Reg::R2), &blocks),
                Err(RewriteViolation::DefClobbersEquation { .. })
            ),
            "staging the argument in R2 while the callee reads R3 must be rejected, \
             got {:?}",
            validate_cfg_rewrite(&orig, &staged(Reg::R2), &blocks)
        );
    }

    /// The pass never proposes what the previous test rejects: a value live
    /// across the call keeps a callee-saved home, because the call's
    /// identity-pinned `{R0..R3, R12, LR}` def webs interfere with everything
    /// live after it.
    #[test]
    fn a_value_live_across_a_call_stays_callee_saved() {
        let body = vec![
            ins(ArmOp::Push {
                regs: vec![Reg::R4, Reg::LR],
            }),
            ins(ArmOp::Mov {
                rd: Reg::R4,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Bl {
                label: "func_1".into(),
            }),
            ins(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R4),
            }),
            ins(ArmOp::Pop {
                regs: vec![Reg::R4, Reg::PC],
            }),
        ];
        // Either the pass declines (identity colouring) or it rewrites — but in
        // NO case may the cross-call value land in call-clobbered scratch.
        if let Some(out) = reallocate(&body, &POOL, &enc_est) {
            let home = match &out[1].op {
                ArmOp::Mov { rd, .. } => *rd,
                other => panic!("shape changed: {other:?}"),
            };
            assert!(
                matches!(home, Reg::R4 | Reg::R5 | Reg::R6 | Reg::R7 | Reg::R8),
                "a value live across a call must stay callee-saved, got {home:?}"
            );
            assert_eq!(out[2].op, body[2].op, "the call was rewritten");
        }
    }

    /// The HIGH-LEVEL call pseudo-ops stay out of scope: they carry a result /
    /// table-index register and are EXPANDED downstream (bounds guard, table
    /// load, result move), so the register footprint this pass would colour is
    /// not the one that ships. Declined, with the reason named.
    #[test]
    fn declines_the_high_level_call_pseudo_ops() {
        for (op, why) in [
            (
                ArmOp::Call {
                    rd: Reg::R0,
                    func_idx: 1,
                },
                "call-pseudo",
            ),
            (
                ArmOp::CallIndirect {
                    rd: Reg::R0,
                    type_idx: 0,
                    table_index_reg: Reg::R1,
                    table_size: 4,
                    table_byte_offset: 0,
                    null_check: false,
                    type_check: None,
                },
                "call-indirect-pseudo",
            ),
        ] {
            let body = vec![ins(op), ins(ArmOp::Bx { rm: Reg::LR })];
            assert_eq!(joins::build_cfg(&body), Err(why));
            assert!(reallocate(&body, &POOL, &enc_est).is_none());
        }
    }
}
