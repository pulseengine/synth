//! RQ-71-STACKDEPTH (#1341): a SOUND per-export maximum native stack depth for
//! a `--relocatable` object.
//!
//! WHY THIS IS A SIBLING PASS AND NOT A FIELD ON THE WCET INTERMEDIATE. The
//! reporter proposed reusing `--emit-wcet`'s traversal, and the TRAVERSAL is
//! right — a memoized DFS over the direct call graph with honest declines for
//! recursion, cycles, `call_indirect` and external callees. Two things are not:
//!
//! 1. THE ARITHMETIC. [`crate::wcet_compose`] composes
//!    `total = own + Σ_site multiplier × total(callee)`, where `multiplier` is
//!    the site's PROVEN EXECUTION COUNT. A callee invoked 1000 times inside a
//!    proven loop costs 1000× the cycles and **once** the stack: frames are
//!    popped between calls. Stack depth is a MAX over the call tree, never a
//!    trip-weighted sum. Reusing the composer unchanged would over-report by
//!    orders of magnitude, and over-reporting is not the safe direction — an
//!    embedder told to reserve 2 MB for a 2.3 KB requirement stops believing
//!    the number, which is its own failure.
//!
//! 2. THE DECLINE SET. `WcetDecline` includes `Loop`, `LoopedExpansion`,
//!    `UnmodeledOp` and `UnresolvedBranch`. None of those affect stack depth:
//!    a data-dependent loop is WCET-unbounded and perfectly stack-bounded,
//!    because the loop body's frame is the same frame every trip. Riding on the
//!    WCET decline would refuse a bound for most real modules — including the
//!    reporter's, whose control loop is exactly that shape.
//!
//! WHAT A FRAME ACTUALLY COSTS, measured rather than assumed. The prologue
//! moves SP in up to three separate steps:
//!
//! ```text
//!   push.w { r4-r8, lr }      24 B   DIRECT_PROLOGUE_BYTES — ALWAYS present
//!   vpush  { d8-d15 }         64 B   only when the AAPCS VFP half is in play
//!   sub.w  sp, sp, #0x20      32 B   only when frame_size > 0
//! ```
//!
//! Summing only the `sub sp` — the obvious reading, and the one #1341 reports —
//! misses the callee-saved push entirely AND misses every function whose
//! `frame_size` is 0, which emits no `sub sp` at all while still consuming 8 or
//! 24 bytes. On `stack_depth_branch_1341.wat` that method gives 96 B against a
//! true 120 B: a 20 % UNDER-report, in the direction that corrupts memory.
//! (The immediate is also printed in HEX — `#0x20` is 32, and a `#[0-9]+`
//! regex silently reads it as 0.)
//!
//! So this pass walks the EMITTED STREAM — the artifact we ship, not a model of
//! it — and tracks the running SP delta, taking the maximum over every
//! instruction boundary. That covers transient `PUSH`/`POP` inside encoder
//! expansions (`I64Popcnt`, `I64Rotl`, `I64Rotr` really do emit them) without
//! enumerating which ops those are, and it is why the answer is a maximum
//! rather than a prologue reading.
//!
//! ANY SP MOVEMENT THIS WALKER CANNOT PRICE DECLINES. The give-up direction is
//! [`StackDecline::UnknownSpMove`]; a silent lower bound would reproduce the
//! exact defect being reported.

use crate::wcet_loops::may_move_sp;
use std::collections::HashMap;
pub use synth_core::stack_depth::{StackDecline, StackFrame, StackResult};
use synth_synthesis::{ArmInstruction, ArmOp, Operand2, Reg};

/// Bytes `VPUSH {d8-d15}` / `VPOP {d8-d15}` move SP by — 8 doubles × 8 bytes.
/// Named here rather than spelled `64` at the use site so the reason travels
/// with the number.
const VFP_CALLEE_SAVED_BYTES: i64 = 8 * 8;

/// Walk one function's FINAL emitted stream and record its own stack profile.
///
/// The running delta is signed because an epilogue `POP`/`ADD SP` legitimately
/// brings it back up; the reported figure is the maximum depth reached, which
/// is what an embedder must reserve.
pub fn analyze_function(name: &str, instrs: &[ArmInstruction]) -> StackFrame {
    let mut cur: i64 = 0;
    let mut max: i64 = 0;
    let mut calls = Vec::new();
    let mut decline = None;

    for ins in instrs {
        match &ins.op {
            ArmOp::Push { regs } => cur += 4 * regs.len() as i64,
            ArmOp::Pop { regs } => cur -= 4 * regs.len() as i64,
            ArmOp::VPushCalleeSavedVfp => cur += VFP_CALLEE_SAVED_BYTES,
            ArmOp::VPopCalleeSavedVfp => cur -= VFP_CALLEE_SAVED_BYTES,
            ArmOp::Sub {
                rd: Reg::SP,
                rn: Reg::SP,
                op2: Operand2::Imm(n),
            } => cur += i64::from(*n),
            ArmOp::Add {
                rd: Reg::SP,
                rn: Reg::SP,
                op2: Operand2::Imm(n),
            } => cur -= i64::from(*n),
            ArmOp::Bl { label } => calls.push(label.clone()),
            // `call_indirect` reaches the stream as an indirect BRANCH, not as
            // a `CallIndirect` pseudo-op: the direct selector lowers it to
            // `ldr rN,[pc,#..]` + `blx rN` (measured on
            // stack_depth_indirect_1341.wat). Both spellings are named here.
            //
            // Without this arm the catch-all below still DECLINES — `may_move_sp`
            // answers true for an indirect branch — but with the reason
            // `unknown-sp-move`, which is safe and wrong: it tells an embedder
            // the walker got confused rather than that their module has an
            // unresolvable call graph. The oracle demanded the accurate reason,
            // which is how this arm came to exist.
            ArmOp::CallIndirect { .. } | ArmOp::Blx { .. } | ArmOp::Bx { .. } => {
                decline.get_or_insert(StackDecline::IndirectCall);
            }
            other => {
                // The catch-all is SAFE here only because `may_move_sp` is an
                // exhaustive, wildcard-free match over every `ArmOp` variant,
                // pinned by `wcet_sp_no_wildcard_946.rs`. Anything it says can
                // move SP and that the arms above did not price is a DECLINE.
                // A new variant that moves SP therefore lands here as a loud
                // refusal instead of a silent under-count.
                if may_move_sp(other) {
                    decline.get_or_insert(StackDecline::UnknownSpMove);
                }
            }
        }
        if cur > max {
            max = cur;
        }
    }

    StackFrame {
        name: name.to_string(),
        own_bytes: max.max(0) as u64,
        calls,
        decline,
    }
}

/// Compose per-function profiles into a per-function maximum over the call
/// tree: `total(f) = own(f) + MAX over call sites of total(callee)`.
///
/// `index_by_label` maps a direct-call label (`func_<idx>`) to a position in
/// `frames`; a label absent from it is an external callee and declines.
pub fn compose(frames: &[StackFrame], index_by_label: &HashMap<String, usize>) -> Vec<StackResult> {
    #[derive(Clone)]
    enum State {
        Pending,
        OnStack,
        Bounded(u64),
        Declined(StackDecline),
    }
    let mut state = vec![State::Pending; frames.len()];

    fn resolve(
        i: usize,
        frames: &[StackFrame],
        index_by_label: &HashMap<String, usize>,
        state: &mut Vec<State>,
    ) -> State {
        match &state[i] {
            State::Bounded(b) => return State::Bounded(*b),
            State::Declined(d) => return State::Declined(d.clone()),
            // A back-edge: this node is already on the current DFS path, so the
            // call graph has a cycle and no finite depth exists.
            State::OnStack => return State::Declined(StackDecline::Recursion),
            State::Pending => {}
        }
        if let Some(d) = &frames[i].decline {
            let s = State::Declined(d.clone());
            state[i] = s.clone();
            return s;
        }
        state[i] = State::OnStack;
        let mut deepest: u64 = 0;
        for label in &frames[i].calls {
            let Some(&j) = index_by_label.get(label) else {
                let s = State::Declined(StackDecline::ExternalCall);
                state[i] = s.clone();
                return s;
            };
            match resolve(j, frames, index_by_label, state) {
                State::Bounded(b) => deepest = deepest.max(b),
                State::Declined(StackDecline::Recursion) => {
                    // Name the cycle as recursion at every node on it, rather
                    // than reporting the caller as merely "callee-unbounded".
                    let s = State::Declined(StackDecline::Recursion);
                    state[i] = s.clone();
                    return s;
                }
                State::Declined(_) => {
                    let s = State::Declined(StackDecline::CalleeUnbounded);
                    state[i] = s.clone();
                    return s;
                }
                State::Pending | State::OnStack => unreachable!("resolve always settles"),
            }
        }
        let s = State::Bounded(frames[i].own_bytes.saturating_add(deepest));
        state[i] = s.clone();
        s
    }

    (0..frames.len())
        .map(|i| match resolve(i, frames, index_by_label, &mut state) {
            State::Bounded(b) => StackResult::Bounded {
                name: frames[i].name.clone(),
                bytes: b,
            },
            State::Declined(d) => StackResult::Declined {
                name: frames[i].name.clone(),
                reason: d,
            },
            State::Pending | State::OnStack => unreachable!("resolve always settles"),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ins(op: ArmOp) -> ArmInstruction {
        ArmInstruction {
            op,
            source_line: None,
        }
    }
    fn push(n: usize) -> ArmInstruction {
        ins(ArmOp::Push {
            regs: vec![Reg::R4; n],
        })
    }
    fn sub_sp(n: i32) -> ArmInstruction {
        ins(ArmOp::Sub {
            rd: Reg::SP,
            rn: Reg::SP,
            op2: Operand2::Imm(n),
        })
    }

    #[test]
    fn prologue_push_counts_even_with_no_sub_sp() {
        // The `leaf` shape: frame_size 0 emits NO `sub sp`, yet the function
        // still consumes its callee-saved push. Summing `sub sp` alone reports
        // 0 here — the under-count that makes #1341's 1456 B look ample.
        let f = analyze_function(
            "leaf",
            &[
                push(2),
                ins(ArmOp::Pop {
                    regs: vec![Reg::R4; 2],
                }),
            ],
        );
        assert_eq!(f.own_bytes, 8, "2 registers pushed = 8 bytes, not 0");
    }

    #[test]
    fn frame_is_push_plus_sub_sp() {
        let f = analyze_function("mid", &[push(6), sub_sp(32)]);
        assert_eq!(f.own_bytes, 24 + 32);
    }

    #[test]
    fn transient_push_inside_the_body_raises_the_maximum() {
        // An encoder expansion (I64Popcnt/Rotl/Rotr really do this) pushes
        // mid-body. The reported figure is the MAXIMUM depth, not the depth at
        // the end, so a transient that is popped again still counts.
        let f = analyze_function(
            "t",
            &[
                push(6),
                sub_sp(8),
                push(2),
                ins(ArmOp::Pop {
                    regs: vec![Reg::R4; 2],
                }),
            ],
        );
        assert_eq!(f.own_bytes, 24 + 8 + 8);
    }

    #[test]
    fn composition_takes_the_max_over_branches_not_the_sum() {
        // THE load-bearing test. top calls a and b; a and b are never live at
        // the same time. A trip-weighted or summing composer reports 56+56+56;
        // the truth is 56 + max(56, 56) = 112.
        let frames = vec![
            StackFrame {
                name: "top".into(),
                own_bytes: 56,
                calls: vec!["func_1".into(), "func_2".into()],
                decline: None,
            },
            StackFrame {
                name: "a".into(),
                own_bytes: 56,
                calls: vec![],
                decline: None,
            },
            StackFrame {
                name: "b".into(),
                own_bytes: 56,
                calls: vec![],
                decline: None,
            },
        ];
        let idx = HashMap::from([("func_1".to_string(), 1), ("func_2".to_string(), 2)]);
        let out = compose(&frames, &idx);
        match &out[0] {
            StackResult::Bounded { bytes, .. } => assert_eq!(
                *bytes, 112,
                "must be own + MAX(callees) = 112, not the sum 168"
            ),
            other => panic!("expected bounded, got {other:?}"),
        }
    }

    #[test]
    fn a_cycle_declines_recursion_rather_than_looping_forever() {
        let frames = vec![
            StackFrame {
                name: "f".into(),
                own_bytes: 8,
                calls: vec!["func_1".into()],
                decline: None,
            },
            StackFrame {
                name: "g".into(),
                own_bytes: 8,
                calls: vec!["func_0".into()],
                decline: None,
            },
        ];
        let idx = HashMap::from([("func_0".to_string(), 0), ("func_1".to_string(), 1)]);
        for r in compose(&frames, &idx) {
            match r {
                StackResult::Declined { reason, .. } => assert_eq!(reason, StackDecline::Recursion),
                other => panic!("expected a recursion decline, got {other:?}"),
            }
        }
    }

    #[test]
    fn an_unresolved_label_is_an_external_call_decline_not_a_zero() {
        let frames = vec![StackFrame {
            name: "f".into(),
            own_bytes: 24,
            calls: vec!["func_99".into()],
            decline: None,
        }];
        match &compose(&frames, &HashMap::new())[0] {
            StackResult::Declined { reason, .. } => assert_eq!(*reason, StackDecline::ExternalCall),
            other => panic!("an unknown callee must DECLINE, not contribute 0: {other:?}"),
        }
    }

    #[test]
    fn a_decline_propagates_up_as_callee_unbounded() {
        let frames = vec![
            StackFrame {
                name: "top".into(),
                own_bytes: 24,
                calls: vec!["func_1".into()],
                decline: None,
            },
            StackFrame {
                name: "bad".into(),
                own_bytes: 24,
                calls: vec![],
                decline: Some(StackDecline::IndirectCall),
            },
        ];
        let idx = HashMap::from([("func_1".to_string(), 1)]);
        match &compose(&frames, &idx)[0] {
            StackResult::Declined { reason, .. } => {
                assert_eq!(*reason, StackDecline::CalleeUnbounded)
            }
            other => panic!("expected propagation, got {other:?}"),
        }
    }
}
