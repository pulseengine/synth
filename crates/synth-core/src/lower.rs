//! ISA-neutral control-frame bookkeeping, shared by the selectors that lower
//! wasm's structured control flow in ONE pass over the op stream (AArch64 and
//! x86-64; RQ-91-LOWERCORE, plan lane S1 / reuse item R3, #1741).
//!
//! WHAT LIVES HERE is every decision that does not depend on the instruction
//! set, so that it exists once:
//!
//! - the [`Frame`] record of an open `block` / `loop` / `if`, with the
//!   [`Frame::label_arity`] / [`Frame::result_arity`] split;
//! - the LABEL-ARITY RULE ([`label_arities`]): a branch to a `loop` targets
//!   its HEADER and carries the loop's PARAMETERS, a branch to a `block` or
//!   `if` targets its END and carries the frame's RESULTS;
//! - the blocktype ORDINAL ([`Control::block_type`]), which advances on every
//!   `block`/`loop`/`if` in the op stream, dead ones included;
//! - REACHABILITY: code after `br` / `br_table` / `return` / `unreachable` is
//!   dead and is SKIPPED ([`Control::skip_dead`]), never lowered — wasm
//!   validates it against a polymorphic stack, so it may pop values that are
//!   not there, or pop below its frame's entry height (#1740);
//! - the JOIN RULE ([`Control::end`]): the position after a frame's `end` is
//!   reachable only when a LIVE edge enters the join — the fall-through, a
//!   forward branch, or an else-less `if`'s skip.
//!
//! WHAT DOES NOT LIVE HERE: anything that emits. The backend owns its output
//! buffer; this module hands it branch positions (`P`, whatever the backend
//! uses to name an emitted branch or a place in its output) and a per-frame
//! payload (`S`, where a value-carrying frame's result is reconciled).

use crate::WasmOp;

/// What a control frame is, and so where a branch to its label goes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FrameKind<P> {
    /// A plain `block`: branches to it go to its END (forward).
    Block,
    /// A `loop`: branches to it go to `entry` (the loop header, backward).
    Loop { entry: P },
    /// An `if`: like `Block` for a branch (its label is its END), and it
    /// carries the position of the conditional branch that skips the THEN
    /// arm, resolved at `else` (to the else arm) or at `end` (past the then
    /// arm). `None` once an `else` has taken it.
    If { else_fixup: Option<P> },
}

/// One open `block` / `loop` / `if`.
#[derive(Debug, Clone)]
pub struct Frame<P, S> {
    pub kind: FrameKind<P>,
    /// FORWARD branches targeting this frame's END, awaiting resolution when
    /// the frame closes (Block/If only; a Loop's branches are backward and
    /// the backend resolves them as it emits them). Every entry was emitted
    /// in LIVE code, so a non-empty list says the join is reached.
    pub pending: Vec<P>,
    /// #1740 — the branch over the else arm of an `if` whose THEN arm ended
    /// dead. A backend that emits it resolves it like any forward branch, but
    /// it never executes, so it is NOT an edge into the join: kept apart from
    /// `pending`.
    pub dead_skip: Option<P>,
    /// Value-stack height on entry.
    pub stack_entry: usize,
    /// How many values a `br`/`br_if`/`br_table` to THIS frame's LABEL
    /// carries. For a Block/If the label is its END, so this is the frame's
    /// RESULT count; for a Loop the label is its HEADER, so this is the
    /// frame's PARAMETER count. Getting that distinction wrong is a SILENT
    /// MISCOMPILE, not a decline: reconciling on a `loop (result i32)`
    /// back-edge would overwrite the frame's result with a garbage value on
    /// every iteration. Only 0 or 1 (see [`label_arities`]).
    pub label_arity: u8,
    /// How many values the frame's FALL-THROUGH `end` leaves on the stack
    /// (the frame's result count). Only 0 or 1.
    pub result_arity: u8,
    /// The backend's payload: where a value-carrying frame's result is
    /// reconciled.
    pub slot: Option<S>,
}

/// Why a block type is not lowered by the one-result reconciliation model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockTypeDecline {
    /// The block type takes PARAMETERS.
    Params,
    /// The block type has more than one RESULT.
    MultiValue,
}

/// THE LABEL-ARITY RULE. From a block type's `(params, results)` counts,
/// `(label_arity, result_arity)` of its frame.
///
/// SOUNDNESS-CRITICAL: a `br` to a Loop targets its HEADER and carries the
/// loop's PARAMETERS, while a `br` to a Block/If targets its END and carries
/// the frame's RESULTS. A `loop (result i32)` therefore has label arity 0 —
/// its back-edge must reconcile NOTHING.
///
/// A block type with parameters, or with more than one result, is declined:
/// the model reconciles at most ONE value per label.
pub fn label_arities(arity: (u8, u8), is_loop: bool) -> Result<(u8, u8), BlockTypeDecline> {
    let (params, results) = arity;
    if params != 0 {
        return Err(BlockTypeDecline::Params);
    }
    if results > 1 {
        return Err(BlockTypeDecline::MultiValue);
    }
    Ok((if is_loop { params } else { results }, results))
}

/// Why an `else` is malformed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ElseError {
    /// No frame is open.
    NoFrame,
    /// The innermost frame is an `if` that already had its `else`.
    Duplicate,
    /// The innermost frame is not an `if`.
    NotIf,
}

/// A frame at its `end`, as [`Control::end`] hands it to the backend.
#[derive(Debug)]
pub struct Closed<P, S> {
    /// The closed frame. Its `pending` and `dead_skip` have been moved into
    /// [`Closed::fixups`], and an else-less `if`'s `else_fixup` too.
    pub frame: Frame<P, S>,
    /// Whether the frame's body FELL THROUGH to this `end` (the position was
    /// reachable just before it). Only then does the fall-through edge
    /// reconcile a result, and only then does the stack-height rule hold.
    pub fallthrough_live: bool,
    /// Whether any live edge enters the join. The position after the `end`
    /// is reachable exactly when this is true; [`Control::end`] has already
    /// recorded that.
    pub join_live: bool,
    /// Every branch to resolve to the join: the dead else-skip (if any), an
    /// else-less `if`'s skip (if any), then the pending forward branches in
    /// the order they were recorded.
    pub fixups: Vec<P>,
}

/// The open control frames of one function body, the blocktype ordinal and
/// the reachability of the current position.
#[derive(Debug, Clone)]
pub struct Control<P, S> {
    frames: Vec<Frame<P, S>>,
    /// Ordinal over `block`/`loop`/`if` in op order — the key into the
    /// decoder's blocktype-arity side-table.
    ordinal: usize,
    /// Reachability of the current linear position.
    reachable: bool,
    /// Frames opened in DEAD code. Nothing can reach them at runtime: a frame
    /// opened in dead code is entered only by falling into it, and a branch
    /// to such a frame's label sits inside it — so it is dead in its
    /// entirety, and so is the fall-through past its `end`.
    dead_depth: usize,
}

impl<P, S> Default for Control<P, S> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P, S> Control<P, S> {
    pub fn new() -> Self {
        Control {
            frames: Vec::new(),
            ordinal: 0,
            reachable: true,
            dead_depth: 0,
        }
    }

    /// Whether the current position is reachable.
    pub fn reachable(&self) -> bool {
        self.reachable
    }

    /// An UNCONDITIONAL transfer (`br`, `br_table`, `return`, `unreachable`)
    /// was just lowered: the fall-through is dead.
    pub fn transfer(&mut self) {
        self.reachable = false;
    }

    /// THE DEAD-CODE RULE. Call with every op, before lowering it; `true`
    /// means the op is dead and must NOT be lowered.
    ///
    /// In dead code a `block`/`loop`/`if` still advances the blocktype
    /// ordinal (the side-table is keyed by the ordinal of EVERY such op) and
    /// opens a dead frame; the `else`/`end` of a dead frame are dead. The
    /// `else`/`end` that close the LIVE frame the transfer sat in are NOT
    /// skipped: that join is reached by the frame's other edges.
    pub fn skip_dead(&mut self, op: &WasmOp) -> bool {
        if self.reachable {
            return false;
        }
        match op {
            WasmOp::Block | WasmOp::Loop | WasmOp::If => {
                self.ordinal += 1;
                self.dead_depth += 1;
                true
            }
            WasmOp::Else if self.dead_depth > 0 => true,
            WasmOp::End if self.dead_depth > 0 => {
                self.dead_depth -= 1;
                true
            }
            WasmOp::Else | WasmOp::End => false,
            _ => true,
        }
    }

    /// The ordinal and `(params, results)` arity of the `block`/`loop`/`if`
    /// being opened, advancing the ordinal. An op past the end of the table
    /// (hand-built op streams carry none) is a void block.
    pub fn block_type(&mut self, block_arity: &[(u8, u8)]) -> (usize, (u8, u8)) {
        let ord = self.ordinal;
        self.ordinal += 1;
        (ord, block_arity.get(ord).copied().unwrap_or((0, 0)))
    }

    /// How many frames are open.
    pub fn depth(&self) -> usize {
        self.frames.len()
    }

    /// The index of the frame a branch of relative depth `depth` targets
    /// (`0` is the innermost), or `None` when no such frame is open.
    pub fn target(&self, depth: u32) -> Option<usize> {
        self.frames
            .len()
            .checked_sub(1)?
            .checked_sub(depth as usize)
    }

    /// Open a frame.
    pub fn open(&mut self, frame: Frame<P, S>) {
        self.frames.push(frame);
    }

    /// The innermost open frame.
    pub fn innermost_mut(&mut self) -> Option<&mut Frame<P, S>> {
        self.frames.last_mut()
    }

    /// The open frames, outermost first.
    pub fn frames(&self) -> &[Frame<P, S>] {
        &self.frames
    }

    /// The open frames, outermost first, for the backend to record a pending
    /// branch or a reconciliation in.
    pub fn frames_mut(&mut self) -> &mut [Frame<P, S>] {
        &mut self.frames
    }

    /// `else`, first half: the skip branch of the innermost `if`, which the
    /// backend resolves to the else arm's entry. The frame stays open.
    pub fn begin_else(&mut self) -> Result<P, ElseError> {
        let frame = self.frames.last_mut().ok_or(ElseError::NoFrame)?;
        match &mut frame.kind {
            FrameKind::If { else_fixup } => else_fixup.take().ok_or(ElseError::Duplicate),
            _ => Err(ElseError::NotIf),
        }
    }

    /// `else`, second half. `skip` is the branch over the else arm the
    /// backend emitted at the end of the THEN arm (`None` when it emitted
    /// none, which is only sound when the then arm ended dead). A LIVE then
    /// arm makes it an edge into the join; a dead one does not (#1740). The
    /// else arm is the target of the `if`'s skip, so it is always reachable.
    pub fn enter_else(&mut self, skip: Option<P>) {
        let then_live = self.reachable;
        debug_assert!(
            skip.is_some() || !then_live,
            "a live then arm needs its branch over the else arm"
        );
        if let (Some(frame), Some(skip)) = (self.frames.last_mut(), skip) {
            if then_live {
                frame.pending.push(skip);
            } else {
                frame.dead_skip = Some(skip);
            }
        }
        self.reachable = true;
    }

    /// `end`: close the innermost frame. `None` when no frame is open (the
    /// `end` is then the function's own, for a backend that opens no frame
    /// for the function body).
    ///
    /// THE JOIN RULE (#1740): the join is reached iff a LIVE edge enters it —
    /// the fall-through, a forward branch (every branch in `pending` was
    /// lowered while reachable, because dead code is skipped), or an
    /// else-less `if`'s skip. A loop's `end` has only its fall-through (its
    /// branches go to the header). The position after the `end` is reachable
    /// exactly when the join is; this records it.
    pub fn end(&mut self) -> Option<Closed<P, S>> {
        let mut frame = self.frames.pop()?;
        let fallthrough_live = self.reachable;
        let else_less = match &mut frame.kind {
            FrameKind::If { else_fixup } => else_fixup.take(),
            _ => None,
        };
        let join_live = fallthrough_live || !frame.pending.is_empty() || else_less.is_some();
        let mut fixups = Vec::with_capacity(frame.pending.len() + 2);
        fixups.extend(frame.dead_skip.take());
        fixups.extend(else_less);
        fixups.append(&mut frame.pending);
        self.reachable = join_live;
        Some(Closed {
            frame,
            fallthrough_live,
            join_live,
            fixups,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type C = Control<usize, ()>;

    fn frame(kind: FrameKind<usize>, arity: (u8, u8)) -> Frame<usize, ()> {
        let is_loop = matches!(kind, FrameKind::Loop { .. });
        let (label_arity, result_arity) = label_arities(arity, is_loop).unwrap();
        Frame {
            kind,
            pending: Vec::new(),
            dead_skip: None,
            stack_entry: 0,
            label_arity,
            result_arity,
            slot: None,
        }
    }

    #[test]
    fn a_loop_label_carries_params_and_a_block_label_results() {
        assert_eq!(label_arities((0, 0), false), Ok((0, 0)));
        assert_eq!(label_arities((0, 0), true), Ok((0, 0)));
        // The soundness-critical row: `loop (result T)` has label arity 0.
        assert_eq!(label_arities((0, 1), true), Ok((0, 1)));
        assert_eq!(label_arities((0, 1), false), Ok((1, 1)));
    }

    #[test]
    fn params_and_multi_value_are_declined_for_every_kind() {
        for is_loop in [false, true] {
            assert_eq!(
                label_arities((1, 0), is_loop),
                Err(BlockTypeDecline::Params)
            );
            assert_eq!(
                label_arities((1, 1), is_loop),
                Err(BlockTypeDecline::Params)
            );
            assert_eq!(
                label_arities((0, 2), is_loop),
                Err(BlockTypeDecline::MultiValue)
            );
            // An unresolvable type index is recorded as (MAX, MAX).
            assert_eq!(
                label_arities((u8::MAX, u8::MAX), is_loop),
                Err(BlockTypeDecline::Params)
            );
        }
    }

    #[test]
    fn the_ordinal_advances_over_dead_frames() {
        let table = [(0, 0), (0, 1), (0, 0), (0, 1)];
        let mut c = C::new();
        assert_eq!(c.block_type(&table), (0, (0, 0)));
        c.open(frame(FrameKind::Block, (0, 0)));
        c.transfer();
        // Two dead frames: ordinals 1 and 2 are consumed, nothing is lowered.
        assert!(c.skip_dead(&WasmOp::Block));
        assert!(c.skip_dead(&WasmOp::I32Add));
        assert!(c.skip_dead(&WasmOp::If));
        assert!(c.skip_dead(&WasmOp::Else));
        assert!(c.skip_dead(&WasmOp::End));
        assert!(c.skip_dead(&WasmOp::End));
        // The live frame's own `end` is NOT skipped.
        assert!(!c.skip_dead(&WasmOp::End));
        let closed = c.end().unwrap();
        assert!(!closed.fallthrough_live && !closed.join_live);
        assert!(!c.reachable());
        // Still dead after the join no edge enters: the next block is dead
        // too and takes ordinal 3; a table past its end reads as void.
        assert!(c.skip_dead(&WasmOp::Block));
        assert!(c.skip_dead(&WasmOp::End));
        assert_eq!(c.block_type(&table), (4, (0, 0)));
    }

    #[test]
    fn live_code_is_never_skipped() {
        let mut c = C::new();
        for op in [
            WasmOp::Block,
            WasmOp::Else,
            WasmOp::End,
            WasmOp::I32Add,
            WasmOp::Unreachable,
        ] {
            assert!(!c.skip_dead(&op), "{op:?}");
        }
    }

    #[test]
    fn a_branch_depth_names_a_frame_from_the_innermost() {
        let mut c = C::new();
        assert_eq!(c.target(0), None);
        c.open(frame(FrameKind::Block, (0, 0)));
        c.open(frame(FrameKind::Loop { entry: 7 }, (0, 0)));
        assert_eq!(c.target(0), Some(1));
        assert_eq!(c.target(1), Some(0));
        assert_eq!(c.target(2), None);
        assert_eq!(c.target(u32::MAX), None);
    }

    /// Each edge into a join, alone, makes it live; none makes it dead.
    #[test]
    fn the_join_is_live_exactly_when_an_edge_enters_it() {
        // Fall-through only.
        let mut c = C::new();
        c.open(frame(FrameKind::Block, (0, 0)));
        let j = c.end().unwrap();
        assert!(j.fallthrough_live && j.join_live && j.fixups.is_empty());
        assert!(c.reachable());

        // A forward branch only (the body then ends dead).
        let mut c = C::new();
        c.open(frame(FrameKind::Block, (0, 0)));
        c.frames_mut()[0].pending.push(11);
        c.transfer();
        let j = c.end().unwrap();
        assert!(!j.fallthrough_live && j.join_live);
        assert_eq!(j.fixups, vec![11]);
        assert!(c.reachable());

        // An else-less if whose then arm ends dead: the skip is the edge.
        let mut c = C::new();
        c.open(frame(
            FrameKind::If {
                else_fixup: Some(3),
            },
            (0, 0),
        ));
        c.transfer();
        let j = c.end().unwrap();
        assert!(!j.fallthrough_live && j.join_live);
        assert_eq!(j.fixups, vec![3]);
        assert!(c.reachable());

        // No edge: a body ending dead with no branch to the label.
        let mut c = C::new();
        c.open(frame(FrameKind::Block, (0, 1)));
        c.transfer();
        let j = c.end().unwrap();
        assert!(!j.fallthrough_live && !j.join_live && j.fixups.is_empty());
        assert!(!c.reachable());

        // A loop's end has only its fall-through, whatever branched to it.
        let mut c = C::new();
        c.open(frame(FrameKind::Loop { entry: 0 }, (0, 1)));
        c.transfer();
        assert!(!c.end().unwrap().join_live);
    }

    #[test]
    fn else_resolves_the_skip_once_and_the_else_arm_is_live() {
        let mut c = C::new();
        assert_eq!(c.begin_else(), Err(ElseError::NoFrame));
        c.open(frame(FrameKind::Block, (0, 0)));
        assert_eq!(c.begin_else(), Err(ElseError::NotIf));
        c.open(frame(
            FrameKind::If {
                else_fixup: Some(5),
            },
            (0, 0),
        ));
        assert_eq!(c.begin_else(), Ok(5));
        c.enter_else(Some(9));
        assert_eq!(c.begin_else(), Err(ElseError::Duplicate));
        // A LIVE then arm's branch over the else arm is an edge into the join.
        let j = c.end().unwrap();
        assert_eq!(j.fixups, vec![9]);
        assert!(j.join_live);
    }

    /// #1740: a DEAD then arm's skip is resolved but is no edge. With a dead
    /// else arm as well, no edge enters the join.
    #[test]
    fn a_dead_then_arms_skip_is_not_an_edge() {
        let mut c = C::new();
        c.open(frame(
            FrameKind::If {
                else_fixup: Some(5),
            },
            (0, 1),
        ));
        c.transfer();
        assert_eq!(c.begin_else(), Ok(5));
        c.enter_else(Some(9));
        assert!(c.reachable(), "the else arm is reached by the if's skip");
        c.transfer();
        let j = c.end().unwrap();
        assert_eq!(j.fixups, vec![9], "the dead skip is still resolved");
        assert!(!j.join_live);
        assert!(!c.reachable());

        // The same with no branch emitted for the dead then arm.
        let mut c = C::new();
        c.open(frame(
            FrameKind::If {
                else_fixup: Some(5),
            },
            (0, 1),
        ));
        c.transfer();
        c.begin_else().unwrap();
        c.enter_else(None);
        // A live else arm falls through: the join is live, nothing to fix.
        let j = c.end().unwrap();
        assert!(j.fallthrough_live && j.join_live && j.fixups.is_empty());
    }

    #[test]
    fn fixups_come_dead_skip_then_else_less_skip_then_pending() {
        let mut c = C::new();
        c.open(frame(
            FrameKind::If {
                else_fixup: Some(1),
            },
            (0, 0),
        ));
        let f = &mut c.frames_mut()[0];
        f.pending.extend([4, 2]);
        f.dead_skip = Some(8);
        assert_eq!(c.end().unwrap().fixups, vec![8, 1, 4, 2]);
    }

    #[test]
    fn end_with_no_frame_open_is_the_functions_own() {
        let mut c = C::new();
        assert!(c.end().is_none());
        assert!(c.reachable());
    }
}
