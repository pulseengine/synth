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
//! **Bounded scope (increment 1).** WHOLE straight-line functions only: a
//! function whose entire body is one straight-line segment (no branches, no
//! calls, no i64-pair / FP ops — anything [`crate::liveness::straight_line_value_ranges`]
//! or [`crate::liveness::reg_effect`] declines). Such a function is coloured as a
//! SINGLE whole-function interference graph over the R0-R8 pool, with segment
//! inputs and live-outs pinned to their incoming/outgoing registers and reserved
//! registers (R9-R12) identity-assigned. On ANY control flow, spill, or unmodeled
//! op, it declines to the shipping path.
//!
//! Increment 2 (NAMED, NOT in this spike): whole-function *webs* built from
//! [`crate::liveness::cfg_liveness`] — colouring value ranges ACROSS control-flow
//! joins, where "the allocator and validator share the dataflow" fully lands.
//! That needs SSA-style web construction across joins that does not exist yet;
//! it is honestly beyond a bounded first slice.
//!
//! **The oracle IS the point (red-first).** Every rewrite this module produces is
//! proven semantics-preserving by [`crate::liveness::validate_segment_rewrite`]
//! (the Rideau/Leroy pairwise trace-equality validator — the SAME acceptance gate
//! `reallocate_function` uses); a rewrite the validator rejects is dropped and the
//! function declines. Downstream, the unconditional VCR-RA-003
//! [`crate::liveness::validate_final_allocation`] re-checks the final stream, and
//! the wasmtime execution differential is the runtime backstop.

use crate::instruction_selector::ArmInstruction;
use crate::liveness::{
    apply_range_coloring, color_ranges, is_straight_line, range_interference, reg_effect,
    straight_line_value_ranges, validate_segment_rewrite,
};
use crate::rules::Reg;
use std::collections::{BTreeMap, BTreeSet};

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
pub fn reallocate(instrs: &[ArmInstruction], pool: &[Reg]) -> Option<Vec<ArmInstruction>> {
    // BOUNDED SCOPE: the whole function must be ONE straight-line segment. Any
    // control-flow / call / unmodeled op → decline (shipping path segments such
    // functions; this spike does not, by design — increment 2 is the whole-
    // function webs across joins).
    if instrs.is_empty() {
        return None;
    }
    for ins in instrs {
        if !is_straight_line(&ins.op) || reg_effect(&ins.op).is_none() {
            return None;
        }
    }

    let ranges = straight_line_value_ranges(instrs)?;
    if ranges.is_empty() {
        return None;
    }

    let pool_index: BTreeMap<Reg, usize> = pool.iter().enumerate().map(|(i, r)| (*r, i)).collect();
    let adj = range_interference(&ranges);

    // Pins: segment inputs (def == 0) and each register's LAST-opened range
    // (the whole-function live-out) keep their original register — the function
    // must return its result registers unchanged. Reserved registers (R9-R12,
    // SP, LR, PC) are identity-assigned outside the colouring.
    let mut last_opened: BTreeMap<Reg, usize> = BTreeMap::new();
    for r in &ranges {
        last_opened.insert(r.reg, r.vreg); // ranges are in creation order
    }
    let mut pins: BTreeMap<usize, usize> = BTreeMap::new();
    let mut assignment: BTreeMap<usize, Reg> = BTreeMap::new();
    let mut pool_nodes: BTreeSet<usize> = BTreeSet::new();
    for r in &ranges {
        match pool_index.get(&r.reg) {
            None => {
                // Reserved register: identity, never coloured.
                assignment.insert(r.vreg, r.reg);
            }
            Some(&idx) => {
                pool_nodes.insert(r.vreg);
                let exit_pinned = last_opened.get(&r.reg) == Some(&r.vreg);
                if r.def == 0 || exit_pinned {
                    pins.insert(r.vreg, idx);
                }
            }
        }
    }

    // Colouring input: pool ranges only (reserved registers cannot collide with
    // pool colours, so their edges are irrelevant to the pool colouring).
    let mut pool_adj: BTreeMap<usize, BTreeSet<usize>> = adj
        .iter()
        .filter(|(n, _)| pool_nodes.contains(n))
        .map(|(n, nbrs)| (*n, nbrs.intersection(&pool_nodes).copied().collect()))
        .collect();

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
        pool_adj.insert(blocker, pool_nodes.iter().copied().collect());
    }

    // Spill cost: occurrence count per range (1 per def + 1 per use event),
    // replayed with the same vreg numbering `straight_line_value_ranges` uses.
    let costs = occurrence_costs(instrs)?;

    let (coloring, spilled) = color_ranges(&pool_adj, pool.len(), &pins, &costs);
    if !spilled.is_empty() {
        // Spill code insertion is increment 2+ (reuse the Belady machinery).
        // For now a function that does not fit the pool declines to the shipping
        // path — which HAS spill support.
        return None;
    }
    for (v, c) in &coloring {
        assignment.insert(*v, pool[*c]);
    }

    // Defense-in-depth: independently of the colourer, re-check every
    // interference edge against the final assignment (cf.
    // `liveness::verify_allocation`, but keyed on value ranges).
    for (n, nbrs) in &adj {
        for m in nbrs {
            match (assignment.get(n), assignment.get(m)) {
                (Some(a), Some(b)) if a != b => {}
                _ => return None,
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
    let new = apply_range_coloring(instrs, &assignment)?;
    match validate_segment_rewrite(instrs, &new) {
        Ok(()) => Some(new),
        Err(_) => None,
    }
}

/// Per-range occurrence cost (Chaitin spill metric input): 1 per def + 1 per use,
/// replayed with the SAME vreg numbering as [`straight_line_value_ranges`] so the
/// costs align with the range ids `range_interference` / `color_ranges` use.
/// `None` on an unmodeled op (already excluded by the caller's pre-scan, but kept
/// total).
fn occurrence_costs(instrs: &[ArmInstruction]) -> Option<BTreeMap<usize, usize>> {
    let mut costs: BTreeMap<usize, usize> = BTreeMap::new();
    let mut current: BTreeMap<Reg, usize> = BTreeMap::new();
    let mut next = 0usize;
    for ins in instrs {
        let e = reg_effect(&ins.op)?;
        for u in &e.uses {
            let v = *current.entry(*u).or_insert_with(|| {
                let v = next;
                next += 1;
                v
            });
            *costs.entry(v).or_insert(0) += 1;
        }
        for d in &e.defs {
            current.insert(*d, next);
            *costs.entry(next).or_insert(0) += 1;
            next += 1;
        }
    }
    Some(costs)
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
        ];
        let out = reallocate(&body, &POOL).expect("straight-line function colours");
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
        ];
        // The r1 range opened at instruction 1 is free (def index 1, overwritten
        // at 2). It is dead-on-arrival (defined, immediately overwritten), so it
        // does not interfere with the pinned r0/r1 ranges beyond r0; the colourer
        // simplifies+selects a colour for it. A `Some` result that PASSES the
        // trace-equality validator proves the free-placement path ran soundly.
        let out = reallocate(&body, &small_pool).expect("free interior range colours");
        assert_eq!(out.len(), body.len());
        assert_eq!(
            validate_segment_rewrite(&body, &out),
            Ok(()),
            "the colouring of the free interior range must preserve dataflow"
        );
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
            reallocate(&body, &POOL).is_none(),
            "control flow is outside the bounded whole-straight-line scope"
        );
    }

    #[test]
    fn declines_on_call() {
        let body = vec![ins(ArmOp::Bl {
            label: "func_1".into(),
        })];
        assert!(
            reallocate(&body, &POOL).is_none(),
            "a call is unmodeled — decline to the shipping path"
        );
    }

    #[test]
    fn declines_on_empty() {
        assert!(reallocate(&[], &POOL).is_none());
    }
}
