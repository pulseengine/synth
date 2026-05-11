//! Regression test for the synth analog of CVE-2026-34971 / GHSA-jhxm-h53p-jm7w.
//!
//! Background:
//! In Wasmtime 32.0.0–43.0.0, an aarch64 Cranelift ISLE lowering rule for
//! `load(iadd(base, ishl(index, amt)))` masked the `amt` field incorrectly
//! when matching. The pattern fired on `amt` values for which the
//! `Replacement` was unsound — the actual loaded address diverged from the
//! address the bounds check had already validated. With spectre mitigations
//! off (Wasmtime 44.0.0 default) this gives guests an arbitrary
//! read/write primitive against the host.
//!
//! Synth analog:
//! `RuleDatabase::with_standard_rules()` registers a rule named
//! `"add_with_shift"` (`crates/synth-synthesis/src/rules.rs:1887`) that
//! pattern-matches the WASM sequence `I32Shl` then `I32Add` and proposes to
//! replace it with a single ARM `ADD rd, rn, rm, LSL #amount`. The
//! `amount` field of the replacement is **hard-coded to 2** and a comment
//! says "Would be extracted from pattern". This is structurally the same
//! class of bug as the aarch64 ISLE one: the *condition* (any
//! `I32Shl;I32Add`) is broader than the *replacement* (LSL #2 specifically),
//! so if the rule ever fires for a different shift constant the lowering
//! becomes unsound.
//!
//! Why synth is not exploitable today:
//! `RuleApplicator::apply_rules` at
//! `crates/synth-synthesis/src/pattern_matcher.rs:201-208` matches the
//! pattern but currently copies the *original* WASM ops unchanged rather
//! than emitting the `Replacement`. The unbound `amount=2` therefore never
//! reaches the encoder. The unsoundness is latent.
//!
//! What this test asserts:
//! Disjunction — at least one of the following must hold, else the
//! GHSA-jhxm-h53p-jm7w shape is now live in synth:
//!   (a) the `add_with_shift` standard rule has been removed; OR
//!   (b) the rule no longer hard-codes `amount = 2` (it has been parameterized
//!       — i.e. the constraint and replacement are over the same set); OR
//!   (c) `RuleApplicator::apply_rules` still does not rewrite ops to the
//!       rule's `Replacement` (the rule remains inert).
//!
//! If a future change enables actual rewriting AND keeps the hard-coded
//! amount, this test fails — the developer must either extract the shift
//! constant from the matched `I32Const`, or remove the rule, before the
//! patch can land.
//!
//! See `docs/spectre-policy.md` §3 for the policy decision.

use synth_synthesis::{
    ArmOp, Operand2, Pattern, Replacement, RuleApplicator, RuleDatabase, ShiftType, WasmOp,
};

/// Returns the `add_with_shift` standard rule, if it still exists in the
/// rule database.
fn find_add_with_shift() -> Option<synth_synthesis::SynthesisRule> {
    let db = RuleDatabase::with_standard_rules();
    db.rules()
        .iter()
        .find(|r| r.name == "add_with_shift")
        .cloned()
}

/// Returns `true` if the rule's `Replacement` hard-codes a specific shift
/// `amount` rather than extracting it from the matched pattern.
fn replacement_has_hardcoded_shift_amount(rule: &synth_synthesis::SynthesisRule) -> bool {
    match &rule.replacement {
        Replacement::ArmInstr(ArmOp::Add {
            op2:
                Operand2::RegShift {
                    shift: ShiftType::LSL,
                    amount,
                    ..
                },
            ..
        }) => {
            // Any concrete u32 here is a hard-coded constant — if it had been
            // parameterized, the `Replacement` enum would expose a binding
            // variant (e.g. `ArmInstrWithBindings`) and this match arm would
            // no longer apply.
            // The bug shape is the rule baking in *any* fixed amount while
            // matching *any* I32Shl;I32Add.
            let _ = amount;
            true
        }
        _ => false,
    }
}

/// Returns `true` if `RuleApplicator::apply_rules` actually transforms the
/// input ops when the `add_with_shift` pattern matches.
///
/// The current applicator (`pattern_matcher.rs:201-208`) is documented as
/// "For now, just keep the original operations" — it copies the matched
/// ops verbatim, so the output equals the input for the patterns we test.
/// If a future patch wires the rewrite (so output differs from input on a
/// matching pattern), this helper detects it and the CVE shape may become
/// live.
fn applicator_actually_rewrites() -> bool {
    let db = RuleDatabase::with_standard_rules();
    let app = RuleApplicator::new(db.rules().to_vec());

    // The `add_with_shift` pattern: `[I32Shl, I32Add]`. We surround it with
    // a non-matching prefix and suffix so any rewrite is detectable by
    // comparing the windows.
    let input = vec![
        WasmOp::LocalGet(0), // not part of any standard pattern
        WasmOp::I32Shl,
        WasmOp::I32Add,
        WasmOp::LocalGet(1),
    ];

    let output = app
        .apply_rules(&input)
        .expect("apply_rules should not fail for valid input");

    // If the applicator is now actually emitting the replacement, the
    // output will differ from the input. (We can't observe an ArmOp
    // through this WASM-to-WASM API — but a real rewrite would have to
    // replace the matched WasmOps with *something* else, e.g. a synthetic
    // marker op or a different WasmOp shape.)
    output != input
}

#[test]
fn cve_2026_34971_analog_add_with_shift_rule_is_safe() {
    let rule = match find_add_with_shift() {
        // (a) rule removed entirely — safe by construction.
        None => return,
        Some(r) => r,
    };

    // (b) replacement no longer hard-codes the shift amount — safe.
    if !replacement_has_hardcoded_shift_amount(&rule) {
        return;
    }

    // (c) applicator still does not rewrite — rule is inert.
    if !applicator_actually_rewrites() {
        return;
    }

    // None of the three safety conditions hold. Fail loudly.
    panic!(
        "Synth analog of CVE-2026-34971 / GHSA-jhxm-h53p-jm7w is now LIVE.\n\
         The `add_with_shift` standard rule (rules.rs:1887) hard-codes\n\
         `amount = 2` in its replacement while matching any `I32Shl;I32Add`\n\
         sequence, AND `RuleApplicator::apply_rules` now actually rewrites\n\
         matched ops to the rule's `Replacement`. This is the same\n\
         pattern-condition-vs-replacement mismatch shape as the aarch64\n\
         Cranelift bug.\n\n\
         Fix: either remove the rule, or extend `Replacement` so the\n\
         shift `amount` is bound from the matched `I32Const` immediate.\n\
         See docs/spectre-policy.md §3."
    );
}

/// Companion test: ensure the `add_with_shift` standard rule's matching
/// pattern remains exactly the `[I32Shl, I32Add]` sequence. If anyone
/// generalizes the pattern further (e.g. to `[Any, I32Shl, I32Add]`)
/// without also generalizing the replacement, the safety analysis in
/// `docs/spectre-policy.md` row #8 needs to be redone.
#[test]
fn add_with_shift_pattern_shape_is_stable() {
    let rule = match find_add_with_shift() {
        None => return, // rule removed — nothing to check
        Some(r) => r,
    };

    match &rule.pattern {
        Pattern::Sequence(patterns) => {
            assert_eq!(
                patterns.len(),
                2,
                "add_with_shift pattern should be a 2-instruction sequence; got {} elements. \
                 If you widened the pattern, revisit docs/spectre-policy.md row #8.",
                patterns.len()
            );
            assert!(
                matches!(patterns[0], Pattern::WasmInstr(WasmOp::I32Shl)),
                "add_with_shift pattern element 0 should be I32Shl"
            );
            assert!(
                matches!(patterns[1], Pattern::WasmInstr(WasmOp::I32Add)),
                "add_with_shift pattern element 1 should be I32Add"
            );
        }
        other => panic!(
            "add_with_shift rule's pattern should be a Sequence; got {:?}. \
             Revisit docs/spectre-policy.md row #8.",
            other
        ),
    }
}
