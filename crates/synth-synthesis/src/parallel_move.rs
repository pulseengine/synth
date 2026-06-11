//! Cycle-safe parallel-move resolver — VCR-RA-004.
//!
//! Spill/reload insertion and the re-allocation pass (VCR-RA-001 step 4) need
//! to realize a *parallel* move set `{ dst_i <- src_i }` at split points: all
//! sources are read in the old state, all destinations written at once. The
//! move graph may contain chains (`a <- b <- c`), cycles (a 2-swap, 3-cycles,
//! …), and self-moves — and sequentializing naively clobbers sources. The
//! literature names this the correctness-critical sub-piece: CompCert proves
//! its parallel-move algorithm separately (Rideau/Serpette/Leroy), and
//! regalloc2's move resolution needs a scratch register, a stackslot-as-scratch
//! fallback, and an emergency spill. Per the verified-codegen roadmap
//! (`artifacts/verified-codegen-roadmap.yaml`, VCR-RA-004) we build the
//! resolver as its own pure, testable component before anything consumes it.
//!
//! **Algorithm.** Destinations must be pairwise distinct (anything else is a
//! caller bug and is rejected); self-moves are dropped. Phase 1 emits chain
//! moves leaf-first with a worklist: a move is *ready* when its destination is
//! not read by any remaining move, and emitting it can unblock the move that
//! feeds it. What remains after saturation is exactly a set of disjoint
//! cycles (every remaining destination is read by exactly one remaining
//! move). Phase 2 breaks each cycle: save one endpoint into a scratch
//! register from `scratch` (filtered against the move set), rotate the rest
//! as a chain, and restore from scratch; if no scratch register survives the
//! filter, one stack-slot scratch pair ([`MoveStep::SpillScratch`] /
//! [`MoveStep::ReloadScratch`]) brackets the cycle instead — the consumer
//! lowers these to `str`/`ldr [sp, #resolver_slot]`.
//!
//! **Progress discipline.** There is no fixpoint-and-hope loop: phase 1
//! removes exactly one pending move per worklist pop, the phase-2 cycle walk
//! removes one pending move per step and is checked against the disjoint-cycle
//! invariant, and the outer phase-2 loop asserts the pending set strictly
//! shrank after every cycle. The emitted sequence is bounded by
//! `moves.len() + 2 * cycle_count` steps, asserted before returning.
//!
//! Nothing here is wired into codegen yet: it is a pure function over
//! [`Reg`], so it cannot change emitted bytes.

use crate::rules::Reg;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// One sequential step realizing part of a parallel move set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MoveStep {
    /// Plain register-to-register move: `dst <- src`.
    Move { dst: Reg, src: Reg },
    /// Store `slot_store` to the (single) resolver stack slot. Always paired
    /// with a later [`MoveStep::ReloadScratch`] in the same cycle; the
    /// consumer lowers it to `str slot_store, [sp, #resolver_slot]`.
    SpillScratch { slot_store: Reg },
    /// Load the resolver stack slot into `slot_load_into`, closing the cycle
    /// opened by the matching [`MoveStep::SpillScratch`].
    ReloadScratch { slot_load_into: Reg },
}

/// Rejected inputs. These are caller bugs, not recoverable conditions: a
/// parallel move set with two writes to the same destination has no defined
/// final state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParallelMoveError {
    /// The same destination register appears in more than one move.
    DuplicateDst(Reg),
}

impl fmt::Display for ParallelMoveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParallelMoveError::DuplicateDst(r) => {
                write!(f, "duplicate destination {r:?} in parallel move set")
            }
        }
    }
}

impl std::error::Error for ParallelMoveError {}

/// Sequentialize the parallel move set `moves` (`(dst, src)` pairs) into
/// steps that, executed in order, give every destination its source's
/// *original* value and leave every register outside `dsts ∪ scratch`
/// unchanged.
///
/// - Destinations must be pairwise distinct ([`ParallelMoveError::DuplicateDst`]
///   otherwise).
/// - Self-moves (`a <- a`) are dropped.
/// - Chains are emitted leaf-first; no source is read after it is clobbered.
/// - Each cycle is broken with the first register in `scratch` that does not
///   appear anywhere in the move set; if none qualifies, with one stack-slot
///   spill/reload pair around the cycle.
/// - The result has at most `moves.len() + 2 * cycle_count` steps.
pub fn sequentialize(
    moves: &[(Reg, Reg)],
    scratch: &[Reg],
) -> Result<Vec<MoveStep>, ParallelMoveError> {
    // Reject duplicate destinations up front — that is a caller bug.
    let mut seen_dsts = BTreeSet::new();
    for &(dst, _) in moves {
        if !seen_dsts.insert(dst) {
            return Err(ParallelMoveError::DuplicateDst(dst));
        }
    }

    // Pending moves keyed by destination (distinct, so this loses nothing),
    // with self-moves dropped: they are already satisfied.
    let mut pending: BTreeMap<Reg, Reg> = moves
        .iter()
        .copied()
        .filter(|(dst, src)| dst != src)
        .collect();

    // How many pending moves still need to *read* each register. A move is
    // safe to emit once nothing pending reads its destination.
    let mut src_reads: BTreeMap<Reg, usize> = BTreeMap::new();
    for &src in pending.values() {
        *src_reads.entry(src).or_insert(0) += 1;
    }

    let mut steps: Vec<MoveStep> = Vec::new();

    // Phase 1 — chains, leaf-first. Worklist of destinations whose pending
    // move is ready (destination read by nothing pending). Each pop removes
    // exactly one pending move; each destination enters the worklist at most
    // once (initially, or on the single transition of its read-count to 0),
    // so this loop runs at most `pending.len()` times by construction.
    let mut ready: Vec<Reg> = pending
        .keys()
        .filter(|dst| src_reads.get(dst).copied().unwrap_or(0) == 0)
        .copied()
        .collect();
    while let Some(dst) = ready.pop() {
        let src = pending
            .remove(&dst)
            .expect("worklist invariant: every ready destination has a pending move");
        steps.push(MoveStep::Move { dst, src });
        let reads = src_reads
            .get_mut(&src)
            .expect("read-count invariant: every pending source is counted");
        *reads -= 1;
        if *reads == 0 && pending.contains_key(&src) {
            // Emitting `dst <- src` freed `src`: the move writing `src` is
            // now safe.
            ready.push(src);
        }
    }

    // Phase 2 — what remains is a disjoint union of cycles: every remaining
    // destination is still read, and (destinations being distinct) by exactly
    // one remaining move. A scratch register must not hold any value the
    // remaining work still needs, so filter against the *entire* move set —
    // conservative, and exactly the "unused by the move set" contract.
    let move_set_regs: BTreeSet<Reg> = moves.iter().flat_map(|&(dst, src)| [dst, src]).collect();
    let scratch_reg: Option<Reg> = scratch.iter().copied().find(|r| !move_set_regs.contains(r));

    let mut cycle_count: usize = 0;
    while let Some((&first_dst, &first_src)) = pending.iter().next() {
        let before = pending.len();

        // Walk the cycle: the move feeding `cur` is the one whose
        // destination is `cur`. Each step removes one pending move, so the
        // walk is bounded; the `expect` fires (rather than looping) if the
        // disjoint-cycle invariant were ever violated.
        let mut cycle: Vec<(Reg, Reg)> = vec![(first_dst, first_src)];
        pending.remove(&first_dst);
        let mut cur = first_src;
        while cur != first_dst {
            let next_src = pending
                .remove(&cur)
                .expect("phase-2 invariant: remaining moves form disjoint cycles");
            cycle.push((cur, next_src));
            cur = next_src;
        }
        assert!(
            cycle.len() >= 2,
            "self-moves were dropped, so every cycle has length >= 2"
        );
        assert!(
            pending.len() < before,
            "progress: extracting a cycle must shrink the pending set"
        );
        cycle_count += 1;

        // The cycle is d1 <- d2 <- ... <- dk <- d1. Save d1 (read only by
        // the last move), rotate d1..d(k-1) as a plain chain, restore dk
        // from the saved value: k + 1 steps for a k-move cycle.
        let last_dst = cycle.last().expect("cycle is non-empty").0;
        match scratch_reg {
            Some(tmp) => {
                steps.push(MoveStep::Move {
                    dst: tmp,
                    src: first_dst,
                });
                for &(dst, src) in &cycle[..cycle.len() - 1] {
                    steps.push(MoveStep::Move { dst, src });
                }
                steps.push(MoveStep::Move {
                    dst: last_dst,
                    src: tmp,
                });
            }
            None => {
                steps.push(MoveStep::SpillScratch {
                    slot_store: first_dst,
                });
                for &(dst, src) in &cycle[..cycle.len() - 1] {
                    steps.push(MoveStep::Move { dst, src });
                }
                steps.push(MoveStep::ReloadScratch {
                    slot_load_into: last_dst,
                });
            }
        }
    }

    assert!(
        steps.len() <= moves.len() + 2 * cycle_count,
        "size bound: {} steps for {} moves and {} cycles",
        steps.len(),
        moves.len(),
        cycle_count
    );
    Ok(steps)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// All registers the simulated register file tracks: the R0..R8 move
    /// universe plus the R9/R10 scratch candidates.
    const ALL_REGS: [Reg; 11] = [
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
    ];

    /// Move universe for the property test: 9 registers, R0..R8.
    const MOVE_REGS: [Reg; 9] = [
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

    /// Deterministic xorshift64 PRNG — no external crates, fixed seed, so the
    /// property test is reproducible bit-for-bit.
    struct XorShift64(u64);

    impl XorShift64 {
        fn next_u64(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        /// Uniform-enough index in `0..n` (n small, modulo bias irrelevant).
        fn below(&mut self, n: usize) -> usize {
            (self.next_u64() % n as u64) as usize
        }
    }

    /// Sequentialize `moves`, run the steps against a simulated register
    /// file (with one memory cell modeling the resolver stack slot), and
    /// assert the parallel semantics: every destination holds its source's
    /// ORIGINAL value; every register outside `dsts ∪ scratch` is unchanged.
    /// Returns the steps for additional shape assertions.
    fn check(moves: &[(Reg, Reg)], scratch: &[Reg]) -> Vec<MoveStep> {
        let steps = sequentialize(moves, scratch).expect("distinct-dst input must sequentialize");

        // Distinct initial values per register.
        let initial: BTreeMap<Reg, u64> = ALL_REGS
            .iter()
            .enumerate()
            .map(|(i, &r)| (r, 0x1000 + i as u64))
            .collect();
        let mut rf = initial.clone();
        let mut slot: Option<u64> = None;

        for step in &steps {
            match *step {
                MoveStep::Move { dst, src } => {
                    let v = rf[&src];
                    rf.insert(dst, v);
                }
                MoveStep::SpillScratch { slot_store } => {
                    slot = Some(rf[&slot_store]);
                }
                MoveStep::ReloadScratch { slot_load_into } => {
                    let v = slot.expect("reload must follow a spill");
                    rf.insert(slot_load_into, v);
                }
            }
        }

        let dsts: BTreeSet<Reg> = moves.iter().map(|&(d, _)| d).collect();
        for &(dst, src) in moves {
            assert_eq!(
                rf[&dst], initial[&src],
                "dst {dst:?} must hold the ORIGINAL value of src {src:?} \
                 (moves: {moves:?}, scratch: {scratch:?}, steps: {steps:?})"
            );
        }
        for r in ALL_REGS {
            if !dsts.contains(&r) && !scratch.contains(&r) {
                assert_eq!(
                    rf[&r], initial[&r],
                    "non-dst, non-scratch reg {r:?} must be unchanged \
                     (moves: {moves:?}, scratch: {scratch:?}, steps: {steps:?})"
                );
            }
        }
        steps
    }

    /// Directed case + its known cycle count, for the size-bound assertion.
    fn check_directed(moves: &[(Reg, Reg)], cycles: usize) {
        for scratch in [&[][..], &[Reg::R9][..], &[Reg::R9, Reg::R10][..]] {
            let steps = check(moves, scratch);
            assert!(
                steps.len() <= moves.len() + 2 * cycles,
                "size bound violated: {} steps for {} moves, {} cycles (scratch: {scratch:?})",
                steps.len(),
                moves.len(),
                cycles
            );
        }
    }

    #[test]
    fn empty_move_set() {
        check_directed(&[], 0);
        assert!(sequentialize(&[], &[]).unwrap().is_empty());
    }

    #[test]
    fn all_self_moves_drop_to_nothing() {
        let moves = [(Reg::R0, Reg::R0), (Reg::R3, Reg::R3), (Reg::R8, Reg::R8)];
        check_directed(&moves, 0);
        assert!(sequentialize(&moves, &[]).unwrap().is_empty());
    }

    #[test]
    fn two_swap() {
        check_directed(&[(Reg::R0, Reg::R1), (Reg::R1, Reg::R0)], 1);
    }

    #[test]
    fn three_cycle() {
        check_directed(
            &[(Reg::R0, Reg::R1), (Reg::R1, Reg::R2), (Reg::R2, Reg::R0)],
            1,
        );
    }

    #[test]
    fn two_disjoint_cycles() {
        check_directed(
            &[
                (Reg::R0, Reg::R1),
                (Reg::R1, Reg::R0),
                (Reg::R2, Reg::R3),
                (Reg::R3, Reg::R4),
                (Reg::R4, Reg::R2),
            ],
            2,
        );
    }

    #[test]
    fn chain_into_cycle() {
        // R5 <- R6 <- R0, hanging off the cycle R0 <-> R1: the chain must be
        // emitted leaf-first (R5 <- R6 before R6 <- R0) and before the cycle
        // clobbers R0.
        check_directed(
            &[
                (Reg::R5, Reg::R6),
                (Reg::R6, Reg::R0),
                (Reg::R0, Reg::R1),
                (Reg::R1, Reg::R0),
            ],
            1,
        );
    }

    #[test]
    fn plain_chain_and_fanout() {
        // a <- b <- c plus fan-out (two readers of R2): no cycles, no scratch
        // needed even with an empty scratch set.
        let moves = [(Reg::R0, Reg::R1), (Reg::R1, Reg::R2), (Reg::R4, Reg::R2)];
        let steps = check(&moves, &[]);
        assert_eq!(steps.len(), moves.len());
        assert!(
            steps.iter().all(|s| matches!(s, MoveStep::Move { .. })),
            "chains must not touch the stack slot"
        );
    }

    #[test]
    fn duplicate_dst_is_an_error() {
        assert_eq!(
            sequentialize(&[(Reg::R0, Reg::R1), (Reg::R0, Reg::R2)], &[Reg::R9]),
            Err(ParallelMoveError::DuplicateDst(Reg::R0))
        );
        // Even duplicate self-moves are a caller bug.
        assert_eq!(
            sequentialize(&[(Reg::R3, Reg::R3), (Reg::R3, Reg::R3)], &[]),
            Err(ParallelMoveError::DuplicateDst(Reg::R3))
        );
    }

    #[test]
    fn cycle_with_scratch_register_avoids_stack() {
        let steps = check(&[(Reg::R0, Reg::R1), (Reg::R1, Reg::R0)], &[Reg::R9]);
        assert!(
            steps.iter().all(|s| matches!(s, MoveStep::Move { .. })),
            "with a usable scratch register no stack slot may be touched"
        );
    }

    #[test]
    fn cycle_without_scratch_uses_one_stack_pair() {
        let steps = check(&[(Reg::R0, Reg::R1), (Reg::R1, Reg::R0)], &[]);
        let spills = steps
            .iter()
            .filter(|s| matches!(s, MoveStep::SpillScratch { .. }))
            .count();
        let reloads = steps
            .iter()
            .filter(|s| matches!(s, MoveStep::ReloadScratch { .. }))
            .count();
        assert_eq!((spills, reloads), (1, 1));
    }

    #[test]
    fn scratch_colliding_with_move_set_is_filtered_out() {
        // R0 is in the move set, so it must NOT be used as scratch; with no
        // other candidate the resolver falls back to the stack pair.
        let steps = check(&[(Reg::R0, Reg::R1), (Reg::R1, Reg::R0)], &[Reg::R0]);
        assert!(
            steps
                .iter()
                .any(|s| matches!(s, MoveStep::SpillScratch { .. })),
            "colliding scratch must be rejected in favor of the stack slot"
        );
    }

    /// The property test from the VCR-RA-004 verification criteria: random
    /// permutations and partial move sets over R0..R8, each checked with 0,
    /// 1, and 2 available scratch registers, against the reference parallel
    /// semantics. 2000 deterministic iterations.
    #[test]
    fn property_random_move_sets_match_parallel_semantics() {
        const ITERATIONS: usize = 2000;
        let mut rng = XorShift64(0x5EED_CA11_F00D_2026);

        for iter in 0..ITERATIONS {
            let moves: Vec<(Reg, Reg)> = if iter % 2 == 0 {
                // Full random permutation: dst_i <- perm(i). Guaranteed
                // cycles + self-moves in the mix.
                let mut perm = MOVE_REGS;
                for i in (1..perm.len()).rev() {
                    perm.swap(i, rng.below(i + 1));
                }
                MOVE_REGS.iter().copied().zip(perm).collect()
            } else {
                // Partial move set: distinct random dsts (shuffle, take a
                // prefix), arbitrary srcs — chains, fan-out, self-moves,
                // cycles all arise.
                let mut dsts = MOVE_REGS;
                for i in (1..dsts.len()).rev() {
                    dsts.swap(i, rng.below(i + 1));
                }
                let count = rng.below(MOVE_REGS.len() + 1);
                dsts[..count]
                    .iter()
                    .map(|&d| (d, MOVE_REGS[rng.below(MOVE_REGS.len())]))
                    .collect()
            };

            for scratch in [&[][..], &[Reg::R9][..], &[Reg::R9, Reg::R10][..]] {
                let steps = check(&moves, scratch);
                // Global size bound: every cycle has length >= 2, so there
                // are at most moves.len() / 2 cycles.
                assert!(
                    steps.len() <= moves.len() + 2 * (moves.len() / 2),
                    "size bound violated at iteration {iter} (moves: {moves:?})"
                );
            }
        }
    }
}
