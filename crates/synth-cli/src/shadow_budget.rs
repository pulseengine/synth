//! VCR-MEM-001 layer-2: derive the shadow-stack budget `B` from a PROVEN
//! worst-case shadow-stack depth, instead of trusting an integrator-asserted
//! number (layer-1, #383).
//!
//! This module is the **decision logic only** and is deliberately dep-free:
//! it operates over a synth-owned [`StackDepthBound`], never over
//! `scry_analyze_core::StackBound`. The adapter from scry's type lives at the
//! (gated) call site that actually runs `analyze()`; keeping the decision here
//! means the budget logic — and its unit tests — compile and run without scry
//! in the build graph (and, critically, without scry's 28-crate transitive
//! closure entering the Bazel `rust_binary` compile). The mechanism that
//! *consumes* `B` is the proven layer-1 shrink (`--shadow-stack-size`,
//! main.rs:2641): re-base the `__stack_pointer` global `sp_init -> B` and
//! resize the `.bss` reservation. Layer-2 only changes *where B comes from*.
//!
//! ## Soundness scope — "proven stack DEPTH, asserted no-heap"
//!
//! When the bound is [`StackDepthBound::Bytes`], `B` is derived from scry's
//! `stack_usage.max_stack_bytes`, documented (scry-sai-core, FEAT-021 /
//! SCRY-001) as "the deepest weighted path through the call graph, each
//! function weighted by the frame its prologue subtracts from the
//! `__stack_pointer` global … guest shadow-stack only." Because it is a *sound
//! over-approximation*, `B >= real max shadow-stack depth`, so the reservation
//! cannot underflow the live stack. That is the ONLY thing layer-2 proves.
//!
//! What stays **asserted** (the inherited layer-1 contract, NOT proven here):
//! the static tail above `sp_init` and any heap use. scry's bound says nothing
//! about heap allocation or static data — so this remains safe only for the
//! no-grow / no-heap MCU images layer-1 already requires. We must label the
//! footprint as proven-depth + asserted-no-heap and never restate it as a bare
//! "proven footprint" (the #383 overclaim shape).

/// Synth-owned mirror of a worst-case shadow-stack depth result.
///
/// Mirrors `scry_analyze_core::StackBound`'s three-way shape but is dep-free so
/// the decision logic below compiles without scry. Per scry's contract,
/// `Unbounded` and `Unknown` both mean "no finite bound proven" and are NEVER
/// treated as zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StackDepthBound {
    /// A proven finite worst-case shadow-stack depth, in bytes. `u64` to match
    /// scry's `StackBound::Bytes(u64)` without a lossy narrowing at the adapter.
    Bytes(u64),
    /// Recursion / a cycle in the call graph — no finite bound exists.
    Unbounded,
    /// The analyzer could not determine a bound (dynamic `alloca`, an
    /// unresolved `call_indirect` / host edge, or an ambiguous stack-pointer
    /// global).
    Unknown,
}

/// How a chosen budget `B` is justified — drives the user-facing label so a
/// proven budget is never reported with the same words as an asserted one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BudgetSource {
    /// `B` derived from a proven shadow-stack depth (scry FEAT-021 / SCRY-001).
    /// Scope: proven stack DEPTH only; the static tail above `sp_init` and any
    /// heap remain the layer-1 ASSERTED no-heap / no-grow contract.
    ProvenStackDepth,
    /// `B` is the integrator-asserted layer-1 fallback: no finite bound was
    /// proven, but the caller supplied a trusted budget to fall back to.
    AssertedFallback,
}

/// The outcome of the budget derivation: either use a concrete `B` (with its
/// justification) or refuse honestly (the #359/#368 typed-Err lesson — never
/// silently pick a number we cannot defend).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BudgetDecision {
    /// Re-base the shadow stack to `bytes`, justified by `source`.
    Use { bytes: u32, source: BudgetSource },
    /// No defensible budget; the message explains why (surfaced as a typed
    /// `Err` at the call site).
    Refuse(String),
}

/// AAPCS wants 8-byte stack alignment; LLVM typically initialises
/// `__stack_pointer` 16-aligned. We round the re-based top up to 16 so frames
/// stay aligned — rounding *up* preserves `B >= proven depth`, so soundness is
/// not weakened. (All observed fixture `sp_init`s — 4096, 65536, 1048576 — are
/// 16-aligned, so a 16-aligned `B <= sp_init` whenever the depth fits.)
const STACK_ALIGN_BYTES: u64 = 16;

/// Decide the shadow-stack budget `B` from a proven depth `bound`, given the
/// module's original shadow-stack top `sp_init` and an optional
/// integrator-asserted `fallback` (the layer-1 `--shadow-stack-size` value).
///
/// - [`StackDepthBound::Bytes(n)`] → a PROVEN budget: `B = align16(n)`, source
///   [`BudgetSource::ProvenStackDepth`]. Refuses if `n > sp_init` — a proven
///   depth that exceeds the original reservation means the *original image
///   under-provisioned its stack*, a latent bug layer-2 surfaces for free
///   rather than hiding behind a generic refuse.
/// - [`StackDepthBound::Unbounded`] / [`StackDepthBound::Unknown`] → no finite
///   bound proven: fall back to the asserted `fallback` if given
///   ([`BudgetSource::AssertedFallback`]), else refuse honestly.
pub fn budget_from_bound(
    bound: StackDepthBound,
    sp_init: u32,
    fallback: Option<u32>,
) -> BudgetDecision {
    match bound {
        StackDepthBound::Bytes(n) => {
            // A proven depth above the original top is an under-provisioned
            // image, not a shrink opportunity — name it precisely.
            if n > u64::from(sp_init) {
                return BudgetDecision::Refuse(format!(
                    "proven shadow-stack depth {n} B exceeds the original reservation top \
                     sp_init={sp_init} B — the original image UNDER-provisioned its stack \
                     (this is a latent bug in the source, not a shrink target). Refusing. \
                     VCR-MEM-001 layer-2/#383."
                ));
            }
            // Round the re-based top up to 16-byte alignment. Since `n <= sp_init`
            // and `sp_init` is 16-aligned in every observed image, `align16(n) <=
            // sp_init`; `min` is a belt-and-braces guard for a non-aligned top.
            let aligned = n.next_multiple_of(STACK_ALIGN_BYTES);
            let bytes = aligned.min(u64::from(sp_init)) as u32;
            BudgetDecision::Use {
                bytes,
                source: BudgetSource::ProvenStackDepth,
            }
        }
        StackDepthBound::Unbounded | StackDepthBound::Unknown => match fallback {
            Some(b) => BudgetDecision::Use {
                bytes: b,
                source: BudgetSource::AssertedFallback,
            },
            None => BudgetDecision::Refuse(format!(
                "no finite shadow-stack bound was proven ({}) and no asserted \
                 --shadow-stack-size fallback was given; refusing to invent a budget. \
                 VCR-MEM-001 layer-2/#383.",
                match bound {
                    StackDepthBound::Unbounded => "recursion / call-graph cycle ⇒ unbounded",
                    _ =>
                        "analysis incomplete ⇒ unknown (dynamic alloca, \
                          unresolved call_indirect, or ambiguous stack pointer)",
                }
            )),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The #392 spike measured msgq's max_stack_bytes = Bytes(32); a realistic
    // sp_init for that image is the full 1 MiB page top. Proven depth 32 →
    // align16 → 32, justified ProvenStackDepth.
    #[test]
    fn proven_depth_rounds_to_16_and_is_proven() {
        let d = budget_from_bound(StackDepthBound::Bytes(32), 1_048_576, Some(4096));
        assert_eq!(
            d,
            BudgetDecision::Use {
                bytes: 32,
                source: BudgetSource::ProvenStackDepth
            }
        );
    }

    #[test]
    fn proven_depth_unaligned_rounds_up() {
        // 33 → next multiple of 16 = 48.
        let d = budget_from_bound(StackDepthBound::Bytes(33), 65_536, None);
        assert_eq!(
            d,
            BudgetDecision::Use {
                bytes: 48,
                source: BudgetSource::ProvenStackDepth
            }
        );
    }

    #[test]
    fn zero_depth_is_proven_zero() {
        // sp_global present but no frame ever subtracted ⇒ Bytes(0): a proven
        // zero-byte stack. Stays proven; layer-1 will re-base to 0 + static tail.
        let d = budget_from_bound(StackDepthBound::Bytes(0), 4096, None);
        assert_eq!(
            d,
            BudgetDecision::Use {
                bytes: 0,
                source: BudgetSource::ProvenStackDepth
            }
        );
    }

    #[test]
    fn proven_depth_above_sp_init_is_under_provision_refusal() {
        // A proven depth exceeding the original top is the source image's bug,
        // surfaced explicitly — NOT a generic refuse.
        let d = budget_from_bound(StackDepthBound::Bytes(8192), 4096, Some(2048));
        match d {
            BudgetDecision::Refuse(msg) => {
                assert!(msg.contains("UNDER-provisioned"), "got: {msg}");
                assert!(msg.contains("8192"));
            }
            other => panic!("expected under-provision refusal, got {other:?}"),
        }
    }

    #[test]
    fn proven_depth_exactly_at_top_is_accepted() {
        // n == sp_init is not "exceeds"; align16 keeps it at the top (no shrink
        // benefit, still sound and proven).
        let d = budget_from_bound(StackDepthBound::Bytes(4096), 4096, None);
        assert_eq!(
            d,
            BudgetDecision::Use {
                bytes: 4096,
                source: BudgetSource::ProvenStackDepth
            }
        );
    }

    #[test]
    fn unbounded_with_fallback_is_asserted() {
        let d = budget_from_bound(StackDepthBound::Unbounded, 65_536, Some(8192));
        assert_eq!(
            d,
            BudgetDecision::Use {
                bytes: 8192,
                source: BudgetSource::AssertedFallback
            }
        );
    }

    #[test]
    fn unbounded_without_fallback_refuses() {
        let d = budget_from_bound(StackDepthBound::Unbounded, 65_536, None);
        match d {
            BudgetDecision::Refuse(msg) => {
                assert!(msg.contains("unbounded"), "got: {msg}");
                assert!(msg.contains("recursion"));
            }
            other => panic!("expected unbounded refusal, got {other:?}"),
        }
    }

    #[test]
    fn unknown_with_fallback_is_asserted_not_proven() {
        // The critical anti-overclaim case: Unknown must NEVER yield
        // ProvenStackDepth, even with a fallback.
        let d = budget_from_bound(StackDepthBound::Unknown, 65_536, Some(1024));
        assert_eq!(
            d,
            BudgetDecision::Use {
                bytes: 1024,
                source: BudgetSource::AssertedFallback
            }
        );
    }

    #[test]
    fn unknown_without_fallback_refuses_with_cause() {
        let d = budget_from_bound(StackDepthBound::Unknown, 65_536, None);
        match d {
            BudgetDecision::Refuse(msg) => {
                assert!(msg.contains("unknown"), "got: {msg}");
                assert!(msg.contains("call_indirect") || msg.contains("alloca"));
            }
            other => panic!("expected unknown refusal, got {other:?}"),
        }
    }
}
