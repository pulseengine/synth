# VCR-SEL-001 — Increment 2 scope (comparisons + register shifts)

Status: **implemented, flag-off** (2026-07-08). Extends the increment-1 DSL
(`docs/design/vcr-sel-001-first-increment.md`, PR #623) with the next op
families the pilot showed tractable. Epic #242; long-arc issues #73/#166.

## Op families

- **In:**
  - the ten i32 comparisons (`eq/ne/lt_s/lt_u/gt_s/gt_u/le_s/le_u/ge_s/ge_u`)
    — the CMP+SetCond shape;
  - the i32 register shifts (`shl/shr_s/shr_u`) + `rotr`.
- **Out (unchanged from increment 1):** div/rem (VCR-ISA-001-gated on the flat
  executor's no-op `BCondOffset`), i64 pairs, memory, control flow.

## Measurement results (what generalization actually cost)

- **Shifts + rotr are tier-A**, not scratch-using: each lowers to a single
  `LslReg/AsrReg/LsrReg/RorReg` instruction, so the increment-1 scratch
  non-aliasing machinery is *not needed* — `synth_binop_proof_poly` discharges
  all four unchanged (their fixed-register ancestors in `CorrectnessI32.v`
  already close with `synth_binop_proof`). The side-condition machinery
  remains exercised by `rule_i32_rotl` alone.
- **Comparisons generalize with NO side conditions**: `CMP` latches NZCV into
  the state's flags *before* `rd` is written, so the flags transfer is not
  through a register and the universal quantifier admits every `rd/rn/rm`
  aliasing. Discharge: `synth_cmp_binop_proof_poly` — verbatim
  `synth_cmp_binop_proof` (Tactics.v) modulo the extra register binders and
  the lowering-unfold target, applied with the same per-op flag lemma the
  fixed-register proofs use. Seven of ten close with the tactic; `ne`, `lt_s`
  and `lt_u` use the same manual scripts as their `CorrectnessI32.v`
  ancestors, register-generalized verbatim. **0 holdouts: 14/14 Qed.**
- The Rust `ArmOp::SetCond { rd, cond }` pseudo-op is modeled in
  `VcrSelRules.v` as `MOV rd #0; MOVcc rd #1` — the established
  `Compilation.v` convention for the same Rust shape.

## Where the delegation lands — and the one honest holdout

Increment 1 wired `select_default` only. Increment 2 keeps that pattern for
the shifts, but the comparison family delegates in **`select_with_stack`**:

- `select_default`'s comparison arms are a **blind bare-`Cmp` lowering** —
  the 0/1 result is never materialized into a register. They are
  production-unreachable (`select_with_stack` owns comparisons; the wildcard
  fallthrough never sees them), and a rule byte-matching them would be
  **unprovable as T1 result-correspondence** (there is no result register to
  state the theorem about). Those arms stay hand-written. This is the
  increment's deliberate holdout, and it keeps the eventual default flip
  strictly byte-invisible: delegating the CMP+SetCond rule into
  `select_default` would have *changed* that dead path's shape under the
  flag.
- `select_with_stack`'s reg-reg comparison emission (`Cmp {rn:a, Reg(b)}` +
  `SetCond {dst, cond}`) is exactly the rule's shape — the delegation is
  byte-identical by construction. The #258 imm-fold peephole (`cmp a, #C` /
  `cmn a, #-C`) is outside the reg-reg rule's shape and stays hand-written
  on both flag settings (pinned by
  `sel_dsl_cmp_imm_fold_path_stays_handwritten_and_byte_identical_242`).
- The four shifts delegate in **both** selectors (`Delegation::Both`) — the
  identical single instruction in each.

This is the first (deliberate, byte-identical) step of the DSL into the
load-bearing `select_with_stack` path — motivation (ii) of the artifact
(collapsing the selector accretion), pulled forward because the comparison
shape only exists there.

## Gates (same two as increment 1, in order)

1. **Mirror-pinning per op** —
   `sel_dsl_mirror_pin_generated_rules_match_handwritten_arms_242`
   (select_default OFF/ON, 11 rules: inc-1 seven + four shifts) and
   `sel_dsl_mirror_pin_select_with_stack_rules_byte_identical_242`
   (select_with_stack OFF/ON, 14 rules: ten comparisons + four shifts, with a
   non-vacuity check that the hand-written emission window equals the rule's
   output for the registers the selector actually chose).
2. **Frozen fixtures under the flag** — `SYNTH_SEL_DSL=1` keeps the frozen
   byte-gate green (and OFF ≡ baseline holds by construction).

## Rocq obligations

21 rules ↔ 21 Qed (7 increment-1 + 14 increment-2), 1:1 naming, coverage
gated by `//coq:vcr_sel_rules_coverage` against `coq/vcr_sel_rules.manifest`
(pinned to the Rust `RULES` table by a cargo test). A rule without its Qed
cannot merge.

## What remains before the SYNTH_SEL_DSL default flip

Nothing byte-visible: every delegation is mirror-pinned byte-identical, so
the flip changes which *code* serves the arms, not what they emit. The flip
itself is a later PR with the standard re-freeze ritual (flip default →
full differential → CI-pinned opt-out), one release, never bundled with a
byte-changing lever.
