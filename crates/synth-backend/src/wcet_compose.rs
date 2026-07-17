//! #778 phase 3 — inter-procedural WCET composition over the DIRECT call graph.
//!
//! Phase 1/2 (`crate::wcet`, `crate::wcet_loops`) produce a per-function
//! [`WcetIntermediate`]: either a composition-independent decline, or a
//! `Composable` record carrying the function's own cycle sum (every instruction,
//! including each direct `BL`'s branch overhead, priced at its proven execution
//! count) plus the direct call sites still to resolve.
//!
//! This module is the module-level SECOND pass. It is a PURE function over those
//! intermediates — it never re-touches the instruction streams (which are dropped
//! after per-function compilation) — so it is trivially frozen-safe and directly
//! unit-testable on a synthetic leaf→mid→root graph.
//!
//! ## The composed bound (and why it is a sound upper bound)
//!
//! For an acyclic direct call graph, a function's total worst-case cycles is:
//!
//! ```text
//!   total(f) = own_cycles(f) + Σ_{site in f} multiplier(site) × total(callee(site))
//! ```
//!
//! - `own_cycles(f)` already over-approximates every straight-line path through
//!   `f` (both arms of every `if`, each instruction at its documented worst case)
//!   and prices each `BL` at the branch-with-link overhead (4 cyc, `1 + 3` refill).
//! - `multiplier(site)` is the site's proven worst-case execution count (1 outside
//!   any loop; the enclosing proven-loop trip product otherwise), so a callee
//!   invoked inside a counted loop is summed `trip` times — never once. This is the
//!   #1 composition soundness trap, eliminated by construction.
//! - Composing callee-first over a reverse-topological order means `total(callee)`
//!   is a settled sound bound before it is multiplied in.
//!
//! ## What still DECLINES (the decline-honesty guard — nothing is deleted)
//!
//! - **Recursion**: any cycle in the direct call graph (self- or mutual). An upper
//!   cycle bound cannot be composed from a call graph that may revisit a frame an
//!   unbounded number of times → every function on (or reaching) a cycle declines
//!   [`WcetDecline::Recursion`].
//! - **Propagation**: a `Composable` caller that (transitively) calls a callee
//!   which itself declined is [`WcetDecline::CalleeUnbounded`] — a decline must
//!   travel UP the call graph; a caller cannot be bounded while a callee it invokes
//!   is unbounded.
//! - **Unresolved callee**: a direct `BL func_N` whose target is not a compiled
//!   function in this module (an import/external symbol) → [`WcetDecline::Call`].
//!
//! Indirect calls (`Blx`/`call_indirect`) never reach here as a composable — they
//! are already a per-function [`WcetDecline::IndirectCall`] in phase 3's scan.

use std::collections::HashMap;

use synth_core::wcet::{WcetDecline, WcetFunction, WcetIntermediate};

/// Compose per-function intermediates into final [`WcetFunction`]s over the direct
/// call graph. Input order is preserved in the output (one entry per input, same
/// index), so the caller can zip results back to its function list.
///
/// Callees are resolved by their `BL` label: a `func_<idx>` site resolves to the
/// intermediate whose function name is `func_<idx>` OR whose WASM index is `idx`
/// (an exported callee is keyed by its export name in the report but called by
/// `func_<idx>` in the stream — the `index_by_func_label` map bridges that).
///
/// `index_by_func_label` maps a direct-call label (`func_<idx>`) to the index of
/// the callee intermediate in `intermediates`. Built by the driver from the
/// compiled function list (WASM index → position). A label absent from this map is
/// an external/import callee (declines [`WcetDecline::Call`]).
pub fn compose(
    intermediates: &[WcetIntermediate],
    index_by_func_label: &HashMap<String, usize>,
) -> Vec<WcetFunction> {
    let n = intermediates.len();

    // Per-node resolution state, memoized. `Pending` = not yet resolved; the
    // recursion below fills it. `OnStack` marks nodes in the current DFS path so a
    // back-edge (cycle) is detected.
    #[derive(Clone)]
    enum State {
        Pending,
        OnStack,
        Bounded(u64),
        Declined(WcetDecline),
    }
    let mut state = vec![State::Pending; n];
    // Cache the final WcetFunction only after state settles (built at the end).

    // Resolve node `i` to a settled `State` (Bounded/Declined), memoizing. Uses an
    // explicit stack to avoid Rust recursion-depth limits on deep call chains.
    //
    // Algorithm: iterative DFS with a two-phase visit. On first visit we mark the
    // node OnStack and push all its NOT-yet-settled callee dependencies; on the
    // second visit (dependencies settled) we combine them. A callee found OnStack
    // is a back-edge → the whole current path is on a cycle → Recursion.
    fn resolve(
        start: usize,
        intermediates: &[WcetIntermediate],
        index_by_func_label: &HashMap<String, usize>,
        state: &mut [State],
        recursion_hits: &mut [bool],
    ) {
        // Work items: (node, second_visit?)
        let mut work: Vec<(usize, bool)> = vec![(start, false)];
        while let Some((i, second)) = work.pop() {
            match &state[i] {
                State::Bounded(_) | State::Declined(_) => continue,
                _ => {}
            }
            let inter = &intermediates[i];
            let WcetIntermediate::Composable {
                own_cycles,
                call_sites,
                recursion_cert,
                ..
            } = inter
            else {
                // A per-function decline settles immediately.
                if let WcetIntermediate::Declined { reason, .. } = inter {
                    state[i] = State::Declined(reason.clone());
                }
                continue;
            };

            // #778 phase 4 (#49): a verified self-recursion certificate authorizes
            // the function's OWN self-edge. The self-call site (`func_<idx>` == this
            // node's own label) is DROPPED from the dependency graph — the recursive
            // frames are folded analytically as `(max_depth+1) × frame_cost` — so a
            // back-edge to a certified self is NOT a Recursion decline. Any OTHER
            // cycle (mutual recursion, an uncertified self) still declines.
            let self_label: Option<&str> = recursion_cert.as_ref().map(|c| c.self_label.as_str());
            let is_self_site =
                |site: &synth_core::wcet::WcetCallSite| Some(site.callee_label.as_str()) == self_label;

            if !second {
                // First visit: mark on-stack, schedule the second visit AFTER all
                // dependency resolutions (pushed on top, popped first).
                state[i] = State::OnStack;
                work.push((i, true));
                for site in call_sites {
                    // Skip the certified self-edge — it is not a graph dependency.
                    if is_self_site(site) {
                        continue;
                    }
                    match index_by_func_label.get(&site.callee_label) {
                        None => {} // external — handled in the combine phase
                        Some(&callee) => match &state[callee] {
                            State::OnStack => {
                                // Back-edge: `callee` is an ancestor on the current
                                // DFS path → a cycle. Mark it so the combine phase
                                // declines Recursion; do not schedule it again.
                                recursion_hits[callee] = true;
                            }
                            State::Pending => work.push((callee, false)),
                            State::Bounded(_) | State::Declined(_) => {}
                        },
                    }
                }
                continue;
            }

            // Second visit: every dependency is settled (or was a back-edge).
            // If this node itself was hit as a back-edge target, it is on a cycle.
            // A CERTIFIED self is exempt: the only back-edge to it is its own
            // (dropped) self-edge; a mutual cycle would still mark it via a
            // DIFFERENT caller's non-self edge.
            if recursion_hits[i] && recursion_cert.is_none() {
                state[i] = State::Declined(WcetDecline::Recursion);
                continue;
            }
            // frame_cost = own body + every NON-self callee (counted at its site
            // multiplier). own_cycles already prices the self-BL overhead once.
            let mut frame_cost: u128 = *own_cycles as u128;
            let mut verdict: Option<WcetDecline> = None;
            for site in call_sites {
                if is_self_site(site) {
                    continue; // folded analytically below
                }
                let callee = match index_by_func_label.get(&site.callee_label) {
                    None => {
                        // Direct BL to a symbol with no body in this module.
                        verdict = Some(WcetDecline::Call);
                        break;
                    }
                    Some(&c) => c,
                };
                match &state[callee] {
                    State::Bounded(c) => {
                        frame_cost =
                            frame_cost.saturating_add(site.multiplier.saturating_mul(*c as u128));
                    }
                    State::Declined(WcetDecline::Recursion) => {
                        verdict = Some(WcetDecline::Recursion);
                        break;
                    }
                    State::Declined(_) => {
                        // Callee is unbounded for any other reason → propagate.
                        verdict = Some(WcetDecline::CalleeUnbounded);
                        break;
                    }
                    // A callee still OnStack here (not marked as a back-edge) would
                    // be a resolution-order bug; treat conservatively as recursion.
                    State::OnStack | State::Pending => {
                        verdict = Some(WcetDecline::Recursion);
                        break;
                    }
                }
            }
            // Fold the certified self-recursion: `frame_count = max_depth + 1`
            // frames (the base frame runs own_cycles but no self-call), each
            // costing `frame_cost`. The self-call is a simple chain (single call
            // per frame, multiplier 1, proven at certification), so summing
            // frame_count × frame_cost is a sound upper bound.
            let total: u128 = match (&verdict, recursion_cert.as_ref()) {
                (None, Some(cert)) => {
                    let frames = (cert.max_depth as u128).saturating_add(1);
                    frame_cost.saturating_mul(frames)
                }
                _ => frame_cost,
            };
            state[i] = match verdict {
                Some(reason) => State::Declined(reason),
                None => match u64::try_from(total) {
                    Ok(c) => State::Bounded(c),
                    // Astronomically large composed product: decline rather than
                    // emit a truncated (unsound) number.
                    Err(_) => State::Declined(WcetDecline::Recursion),
                },
            };
        }
    }

    let mut recursion_hits = vec![false; n];
    for i in 0..n {
        if matches!(state[i], State::Pending) {
            resolve(
                i,
                intermediates,
                index_by_func_label,
                &mut state,
                &mut recursion_hits,
            );
        }
    }

    // Build the final report entries in input order.
    intermediates
        .iter()
        .enumerate()
        .map(|(i, inter)| match &state[i] {
            State::Bounded(cycles) => {
                let (name, instr_count, loops, recursion, hint_rejections) = match inter {
                    WcetIntermediate::Composable {
                        name,
                        instr_count,
                        loops,
                        recursion_cert,
                        hint_rejections,
                        ..
                    } => (
                        name.clone(),
                        *instr_count,
                        loops.clone(),
                        // #778 phase 4 (#49): surface the derived depth + frame count
                        // when this bound was composed via a self-recursion cert.
                        recursion_cert.as_ref().map(|c| {
                            synth_core::wcet::WcetRecursionBound {
                                max_depth: c.max_depth,
                                frame_count: c.max_depth.saturating_add(1),
                                hint: c.hint,
                            }
                        }),
                        hint_rejections.clone(),
                    ),
                    // A Bounded state always comes from a Composable node.
                    WcetIntermediate::Declined { name, .. } => {
                        (name.clone(), 0, Vec::new(), None, Vec::new())
                    }
                };
                WcetFunction::Bounded {
                    name,
                    cycles: *cycles,
                    instr_count,
                    loops,
                    recursion,
                    hint_rejections,
                }
            }
            State::Declined(reason) => {
                let hint_rejections = match inter {
                    WcetIntermediate::Composable {
                        hint_rejections, ..
                    }
                    | WcetIntermediate::Declined {
                        hint_rejections, ..
                    } => hint_rejections.clone(),
                };
                WcetFunction::declined_with_rejections(
                    inter.name(),
                    reason.clone(),
                    hint_rejections,
                )
            }
            // Every node is resolved to Bounded/Declined by the loop above.
            State::Pending | State::OnStack => {
                WcetFunction::declined(inter.name(), WcetDecline::Recursion)
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use synth_core::wcet::{WcetCallSite, WcetIntermediate};

    fn composable(name: &str, own: u64, sites: &[(&str, u128)]) -> WcetIntermediate {
        WcetIntermediate::Composable {
            name: name.to_string(),
            own_cycles: own,
            instr_count: 1,
            call_sites: sites
                .iter()
                .map(|(l, m)| WcetCallSite {
                    callee_label: (*l).to_string(),
                    multiplier: *m,
                })
                .collect(),
            loops: Vec::new(),
            recursion_cert: None,
            hint_rejections: Vec::new(),
        }
    }

    /// A composable node with a self-recursion certificate for `self_label` at
    /// `max_depth` (the self-edge is folded `(max_depth+1)×frame_cost`).
    fn recursive(
        name: &str,
        own: u64,
        sites: &[(&str, u128)],
        self_label: &str,
        max_depth: u64,
    ) -> WcetIntermediate {
        let WcetIntermediate::Composable {
            name,
            own_cycles,
            instr_count,
            call_sites,
            loops,
            hint_rejections,
            ..
        } = composable(name, own, sites)
        else {
            unreachable!()
        };
        WcetIntermediate::Composable {
            name,
            own_cycles,
            instr_count,
            call_sites,
            loops,
            recursion_cert: Some(synth_core::wcet::WcetRecursionCert {
                self_label: self_label.to_string(),
                max_depth,
                hint: max_depth,
            }),
            hint_rejections,
        }
    }

    fn declined(name: &str, reason: WcetDecline) -> WcetIntermediate {
        WcetIntermediate::Declined {
            name: name.to_string(),
            reason,
            hint_rejections: Vec::new(),
        }
    }

    fn labels(names: &[&str]) -> HashMap<String, usize> {
        names
            .iter()
            .enumerate()
            .map(|(i, n)| ((*n).to_string(), i))
            .collect()
    }

    fn cycles_of(f: &WcetFunction) -> u64 {
        match f {
            WcetFunction::Bounded { cycles, .. } => *cycles,
            other => panic!("expected bounded, got {other:?}"),
        }
    }

    fn reason_of(f: &WcetFunction) -> &WcetDecline {
        match f {
            WcetFunction::Declined { reason, .. } => reason,
            other => panic!("expected declined, got {other:?}"),
        }
    }

    #[test]
    fn leaf_mid_root_chain_composes_tightly() {
        // func_0 = leaf (own 10, no calls)
        // func_1 = mid  (own 20, calls leaf once)
        // func_2 = root (own 30, calls mid once)
        let inters = vec![
            composable("func_0", 10, &[]),
            composable("func_1", 20, &[("func_0", 1)]),
            composable("func_2", 30, &[("func_1", 1)]),
        ];
        let out = compose(&inters, &labels(&["func_0", "func_1", "func_2"]));
        assert_eq!(cycles_of(&out[0]), 10); // leaf
        assert_eq!(cycles_of(&out[1]), 30); // mid = 20 + 1×10
        assert_eq!(cycles_of(&out[2]), 60); // root = 30 + 1×(20+10)
    }

    #[test]
    fn call_inside_loop_multiplies_callee() {
        // root calls leaf with multiplier 5 (call sits in a proven trip-5 loop).
        let inters = vec![
            composable("func_0", 10, &[]),
            composable("func_1", 7, &[("func_0", 5)]),
        ];
        let out = compose(&inters, &labels(&["func_0", "func_1"]));
        assert_eq!(cycles_of(&out[1]), 7 + 5 * 10); // 57, callee counted 5×
    }

    #[test]
    fn diamond_counts_each_path() {
        // func_3 calls func_1 and func_2; both call func_0. Summing every path is a
        // sound over-approximation (func_0 counted on both edges).
        let inters = vec![
            composable("func_0", 4, &[]),
            composable("func_1", 5, &[("func_0", 1)]),
            composable("func_2", 6, &[("func_0", 1)]),
            composable("func_3", 7, &[("func_1", 1), ("func_2", 1)]),
        ];
        let out = compose(&inters, &labels(&["func_0", "func_1", "func_2", "func_3"]));
        // func_1 = 5+4 = 9; func_2 = 6+4 = 10; func_3 = 7 + 9 + 10 = 26.
        assert_eq!(cycles_of(&out[3]), 26);
    }

    #[test]
    fn self_recursion_declines() {
        let inters = vec![composable("func_0", 10, &[("func_0", 1)])];
        let out = compose(&inters, &labels(&["func_0"]));
        assert_eq!(reason_of(&out[0]), &WcetDecline::Recursion);
    }

    #[test]
    fn certified_self_recursion_folds_depth_frames() {
        // func_0 self-recurses (own 10) with a cert max_depth 3 → 4 frames × 10 = 40.
        let inters = vec![recursive("func_0", 10, &[("func_0", 1)], "func_0", 3)];
        let out = compose(&inters, &labels(&["func_0"]));
        assert_eq!(cycles_of(&out[0]), 4 * 10); // (3+1) frames × own_cycles
    }

    #[test]
    fn certified_self_recursion_folds_nonself_callee_per_frame() {
        // func_1 self-recurses (own 5, cert depth 2 → 3 frames) and each frame also
        // calls the leaf func_0 (own 10) once. Composed: 3 × (5 + 10) = 45.
        let inters = vec![
            composable("func_0", 10, &[]),
            recursive("func_1", 5, &[("func_1", 1), ("func_0", 1)], "func_1", 2),
        ];
        let out = compose(&inters, &labels(&["func_0", "func_1"]));
        assert_eq!(cycles_of(&out[0]), 10);
        assert_eq!(cycles_of(&out[1]), 3 * (5 + 10)); // 45
    }

    #[test]
    fn certified_self_still_declines_a_mutual_cycle() {
        // func_0 has a self-cert BUT also participates in a mutual cycle with func_1
        // (func_0→func_1→func_0). The mutual (non-self) cycle must STILL decline —
        // the cert only exempts the self-edge, not a distinct cycle.
        let inters = vec![
            recursive("func_0", 10, &[("func_0", 1), ("func_1", 1)], "func_0", 3),
            composable("func_1", 10, &[("func_0", 1)]),
        ];
        let out = compose(&inters, &labels(&["func_0", "func_1"]));
        assert_eq!(reason_of(&out[0]), &WcetDecline::Recursion);
        assert_eq!(reason_of(&out[1]), &WcetDecline::Recursion);
    }

    #[test]
    fn mutual_recursion_declines_both() {
        let inters = vec![
            composable("func_0", 10, &[("func_1", 1)]),
            composable("func_1", 10, &[("func_0", 1)]),
        ];
        let out = compose(&inters, &labels(&["func_0", "func_1"]));
        assert_eq!(reason_of(&out[0]), &WcetDecline::Recursion);
        assert_eq!(reason_of(&out[1]), &WcetDecline::Recursion);
    }

    #[test]
    fn declined_callee_propagates_up() {
        // func_1 (a loop decline) is called by func_2 → func_2 declines
        // CalleeUnbounded, NOT its own reason.
        let inters = vec![
            composable("func_0", 10, &[]),
            declined("func_1", WcetDecline::Loop),
            composable("func_2", 5, &[("func_1", 1)]),
        ];
        let out = compose(&inters, &labels(&["func_0", "func_1", "func_2"]));
        assert_eq!(cycles_of(&out[0]), 10);
        assert_eq!(reason_of(&out[1]), &WcetDecline::Loop);
        assert_eq!(reason_of(&out[2]), &WcetDecline::CalleeUnbounded);
    }

    #[test]
    fn external_callee_declines_call() {
        // A direct BL to a label with no intermediate in the module.
        let inters = vec![composable("func_0", 10, &[("func_99", 1)])];
        let out = compose(&inters, &labels(&["func_0"]));
        assert_eq!(reason_of(&out[0]), &WcetDecline::Call);
    }

    #[test]
    fn transitive_recursion_caller_also_declines() {
        // func_2 calls func_1 calls func_1 (self-loop). func_1 recurses; func_2
        // reaches a recursive callee → also unbounded.
        let inters = vec![
            composable("func_1", 10, &[("func_1", 1)]),
            composable("func_2", 5, &[("func_1", 1)]),
        ];
        let out = compose(&inters, &labels(&["func_1", "func_2"]));
        assert_eq!(reason_of(&out[0]), &WcetDecline::Recursion);
        // func_2's callee is recursive → propagate as Recursion.
        assert_eq!(reason_of(&out[1]), &WcetDecline::Recursion);
    }
}
