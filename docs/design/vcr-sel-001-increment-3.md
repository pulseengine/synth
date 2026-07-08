# VCR-SEL-001 — Increment 3 scope (the i64 register-pair family)

Status: **implemented, flag-off** (2026-07-08). Extends the increment-1/2 DSL
(`docs/design/vcr-sel-001-first-increment.md`,
`docs/design/vcr-sel-001-increment-2.md`; PRs #623/#639) into the i64
register-pair family. Epic #242.

## Why this family, now

This week's miscompile cluster (#615 A32 NOPs, #632 popcnt clobber, #633
div_s overflow, #643 globals, #599 pair shifts) sits entirely in hand-written
i64 paths — and zero bugs landed in DSL-covered ops. The pair shapes are also
where the rule format's side-condition machinery earns its keep: the #632
lesson is that a rule that cannot state "the result must not be clobbered
before use" is how those bugs happen.

## Op families

- **In:**
  - `i64.add` / `i64.sub` / `i64.and` / `i64.or` / `i64.xor` — the natural
    first pair rules, each a two-instruction pair (ADDS+ADC / SUBS+SBC /
    AND×2 / ORR×2 / EOR×2) over SIX register variables
    (`rd_lo rd_hi rn_lo rn_hi rm_lo rm_hi`);
  - `i64.eqz` — the single-instruction `I64SetCondZ` shape (the "SetCondZ
    shape"; it discharges directly against the `i64_setcondz_bits_spec`
    axiom, no comparison tactic needed).
- **Out (increment-4 territory):** i64 mul/div/rem/shifts/rotates (pseudo-ops
  or multi-instruction sequences with scratch + branches), the full i64
  comparison family (`I64SetCond` — same pseudo-op pattern as eqz, deferred
  to keep this increment bounded), memory, globals.

## Model-extension finding: none needed

The go/no-go question — can the Rocq model express register pairs? — came
back **yes, with zero model extension**. The flat model has carried the pair
convention since v0.8.0 (`ADDS/ADC/SUBS/SBC` with real NZCV carry coupling in
`ArmSemantics.v`; value-pair correspondence via `combine_i32` /
`lo_of_i64` / `hi_of_i64`), and `CorrectnessI64.v` already proves the
fixed-register ancestors T1 at `R0:R1 op= R2:R3`. Increment 3 is exactly the
pilot's move applied to pairs: lift fixed registers to universally-quantified
ones, and turn what was `discriminate` on concrete register pairs into
explicit aliasing hypotheses.

## The aliasing side-condition design (the #632 lesson, made structural)

Every two-instruction pair rule writes `rd_lo` (low half) BEFORE the second
instruction reads `rn_hi`/`rm_hi` and writes `rd_hi`. Three explicit side
conditions per pair rule (`I64_PAIR_SIDE_CONDITIONS` in `sel_dsl/mod.rs`,
hypotheses of the paired theorems, runtime `Err` in the generated lowerings):

1. `rd_hi ≠ rd_lo` — the high write must not destroy the low result word;
2. `rd_lo ≠ rn_hi` — the low write must not clobber operand 1's high half
   before the second instruction reads it;
3. `rd_lo ≠ rm_hi` — same for operand 2.

Deliberately NOT required: `rd_lo = rn_lo` / `rd_hi = rn_hi` in-place reuse
(what `select_default`'s fixed `R0:R1 op= R2:R3` arms emit) and every other
aliasing — the universal quantifier admits them, so one Qed per rule covers
both selectors' assignments. `i64.eqz` carries no side conditions (the
pseudo-op reads both halves before writing `rd`).

## Rocq obligations

27 rules ↔ 27 Qed (7 + 14 + 6), 1:1 naming, coverage gated by
`//coq:vcr_sel_rules_coverage` against `coq/vcr_sel_rules.manifest`. The six
new theorems are **pair-result T1**: both words of the result are proven
(post-conditions on `rd_lo` AND `rd_hi`), value-level against the WASM-spec
functions (`I64.add` etc. on `combine_i32`-combined operands) — the same
honest shape as their `CorrectnessI64.v` ancestors. Discharge:

- add/sub — `synth_i64_carry_pair_proof_poly`, the fixed-register stepped
  proof register-generalized verbatim, fed by the existing
  `i64_add_via_adds_adc` / `i64_sub_via_subs_sbc` carry/borrow lemmas
  (ArmFlagLemmas.v). **No new axiom.**
- and/or/xor — `synth_i64_bitwise_pair_proof_poly`, fed by the
  halves-distribute combine lemmas imported from `CorrectnessI64.v`
  (not duplicated).
- eqz — direct `i64_setcondz_bits_spec` rewrite, like the clz/ctz/popcnt
  ancestors.

**0 holdouts: 6/6 attempted rules discharged.** (The kill-criterion's ≥70%
auto-discharge bar is met at 100% again.)

## Where the delegation lands

All six rules are `Delegation::Both`:

- `select_default`'s fixed-register arms (in-place `R0:R1 op= R2:R3`,
  `I64SetCondZ R0, R0, R1`) — in-place instances of the rules;
- `select_with_stack`'s allocated-pair arms — `alloc_consecutive_pair`
  destinations avoid every operand half (its `extra_avoid` argument), so the
  side conditions hold by construction; a violation would surface as a loud
  `Err`, never a silent misassemble.

## Gates (same two as increments 1–2, in order)

1. **Mirror-pinning per op** — the select_default loop
   (`sel_dsl_mirror_pin_generated_rules_match_handwritten_arms_242`, now 17
   rules) plus the dedicated pair test
   (`sel_dsl_mirror_pin_i64_pair_rules_select_with_stack_242`: i64-typed
   probes, OFF≡ON full-sequence equality, and the RMW-vacuity window check —
   the emission window must equal the rule's output for the selector's own
   six chosen registers).
2. **Frozen fixtures under the flag** — OFF ≡ baseline holds by construction
   (every delegation is flag-gated); the frozen `.text` byte gate
   (`frozen_codegen_bytes.rs`) stays green flag-off.

## What remains before the SYNTH_SEL_DSL default flip

Unchanged from increment 2: nothing byte-visible — the flip changes which
*code* serves the arms, not what they emit. The flip itself is a later PR
with the standard re-freeze ritual, one release, never bundled with a
byte-changing lever.
