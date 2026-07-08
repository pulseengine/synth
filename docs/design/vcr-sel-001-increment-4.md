# VCR-SEL-001 — Increment 4 scope (scratch-using / multi-instruction shapes + the I64SetCond family)

Status: **implemented, flag-off** (2026-07-08). Extends the increment-1/2/3
DSL (`docs/design/vcr-sel-001-first-increment.md`,
`docs/design/vcr-sel-001-increment-2.md`,
`docs/design/vcr-sel-001-increment-3.md`; PRs #623/#639/#661) into the tier
the pilot called out and increments 1–3 deferred: scratch-using and
multi-instruction shapes, plus the binary i64 comparison family. Epic #242.

## Op families

- **In:**
  - `i32.clz` — single `CLZ` (tier A, unary; first unary rule in the table);
  - `i32.ctz` — the **two-instruction `RBIT rd, rm; CLZ rd, rd` shape with
    the scratch=dest trick**: instruction 1 writes the bit-reversed value
    into `rd` itself and instruction 2 reads it back, so the shape needs no
    extra scratch register and — unlike `i32.rotl`'s `rs <> rn` — **no
    aliasing side condition** (RBIT reads `rm` before writing `rd`; the
    second instruction only reads `rd`). Stepped proof closing with the
    `I32.clz_rbit` axiom, the register-generalized `i32_ctz_correct`;
  - `i32.popcnt` — included at **pseudo-op tier** (see the honesty note);
  - the **binary `I64SetCond` comparison family** —
    `i64.eq/ne/lt_s/lt_u/gt_s/gt_u/le_s/le_u/ge_s/ge_u`, ten rules over FIVE
    register variables (`rd` + both operand pairs), each mirroring the single
    `ArmOp::I64SetCond` pseudo-op BOTH selectors emit, with the hand-written
    arms' condition mapping (`lt_u → LO/Cond_CC`, `ge_u → HS/Cond_CS`, …).
    No side conditions: the pseudo-op reads all four operand halves before
    writing `rd`, so the universal quantifier admits every aliasing —
    including `select_default`'s in-place `rd = rn_lo = R0`.
- **Already present (checked, not re-added):** the i32 rotr-by-register twin
  landed in increment 2 (`rule_i32_rotr`, tier A single `ROR_reg`).
- **Out (later increments):** i64 mul/div/rem, i64 pair shifts/rotates
  (multi-instruction with branches), i64 clz/ctz/popcnt pseudo-ops, i32.eqz
  (the CMP-imm shape — the reg-reg rule format has no immediate-operand
  CMP template yet), memory, globals, control flow.

## The I64SetCond verdict (the highest-value target, honestly bounded)

This family is the shape #615 re-implemented on A32 and where cond-mapping
bugs live. What increment 4 verifies and what it cannot:

**Verified (pseudo-op tier T1):** both selectors lower a binary i64
comparison to ONE `ArmOp::I64SetCond` pseudo-op. The rules mirror exactly
that — so the mirror-pins are byte-identical at the ArmOp level — and each
theorem discharges against the `i64_setcond_bits_spec` axiom, which pins the
pseudo-op's result to the WASM-spec
`if I64.<cmp> (combine_i32 lo hi) … then 1 else 0` form. This is the
register-generalized form of the fixed-register ancestors in
`CorrectnessI64Comparisons.v` — the **condition-code mapping** (the #615 bug
class at the selector level: which `Condition` goes with which WASM op) is
now covered for every register assignment, in both selectors.

**Not verified — the flat-executor gap, documented exactly:** the encoder
expands the pseudo-op to the dual-precision flags-chain

- ordered: `CMP lo,lo; SBCS rd,hi,hi; MOV+MOVcc` — with the operand-swap
  trick for GT/LE/HI/LS (compare `(rm, rn)` and test the LT/GE/LO/HS
  complement);
- EQ/NE: `CMP lo,lo; CMPEQ hi,hi; MOV+MOVcc` (compare highs only if lows
  equal).

Proving THAT expansion equal to `i64_setcond_bits` needs three things the
flat Rocq executor (`ArmSemantics.v`) lacks today:

1. **`SBCS`** — a flag-*setting* subtract-with-carry. The model's `SBC`
   reads C but writes no flags, so the chain's second link (N/Z/C/V from
   `hi1 - hi2 - borrow`) is inexpressible.
2. **Conditionally-executed flags-writers** — `CMPEQ` (the EQ/NE chain).
   The model's only conditional forms are the register-writing `MOVcc`
   family; there is no conditional CMP.
3. **Three-operand borrow-aware flag helpers** — `compute_c_flag_sub` /
   `compute_v_flag_sub` are two-operand; the SBCS link needs the
   carry-in-aware variants.

This is the same executor gap the VCR-ISA-001 spike hit with `BCondOffset`
(a no-op in the flat executor, which is why the div/rem trap guards are the
remaining T3 admits): control- and flags-chain-shaped expansions are below
the flat model's floor. Pseudo-op-tier proofs are the honest ceiling until
the Sail-generated ISA model (VCR-ISA-001) or a PC-indexed executor lands.
The expansion itself stays covered by the differential oracles (and got its
A32 no-silent-NOP gate in #615's fix).

## The popcnt honesty note

At the ArmOp level `i32.popcnt` is a single `Popcnt` pseudo-op in both
selectors — that is what the rule mirrors (mirror-pinnable byte-identically)
and what `rule_i32_popcnt_correct` proves, against the axiomatized
`I32.popcnt` (exactly like the fixed-register ancestor and like
`i64.eqz`/`I64SetCond`). The encoder's ~15-instruction shift-and-add
expansion below the ArmOp boundary — where the #632 clobber actually lived —
is **not modeled and not provable in the flat executor** (it is also not
expressible as a rule without breaking the "migrate structure, never bytes"
invariant: the selector emits the pseudo-op, not the expansion). Included at
pseudo-op tier rather than held out, because the established DSL boundary is
the selector's ArmOp emission; the expansion is encoder territory
(VCR-ISA-001 / the encoder oracles). Anyone reading "popcnt: DSL-served"
must read it with this asterisk — `coq/STATUS.md`'s coverage table carries
the same footnote.

## Rocq obligations

40 rules ↔ 40 Qed (7 + 14 + 6 + 13), 1:1 naming, coverage gated by
`//coq:vcr_sel_rules_coverage` against `coq/vcr_sel_rules.manifest`.
Discharge for the thirteen new theorems:

- clz / popcnt — `synth_unop_proof_poly` (verbatim `synth_unop_proof`
  modulo binders and unfold target, the same generalization move as
  `synth_binop_proof_poly`);
- ctz — stepped two-instruction proof (`set`/`subst` through both states,
  `get_set_reg_eq` twice, close with `I32.clz_rbit`) — the
  `rule_i32_rotl_correct` structure with no aliasing hypothesis;
- the ten comparisons — `synth_i64_setcond_proof_poly`, the uniform
  CorrectnessI64Comparisons.v script register-generalized (expose the
  pseudo-op step, substitute the four half-reads, reduce
  `i64_setcond_bits_spec` on the concrete condition). **No new axiom.**

**0 holdouts: 13/13 attempted rules discharged** (the deliberate holdouts —
the encoder expansions — are below the rule boundary, not failed rule
attempts; the kill-criterion's ≥70% bar is met at 100% again.)

## Where the delegation lands

All thirteen rules are `Delegation::Both`:

- `select_default`: the `I32Clz`/`I32Ctz`/`I32Popcnt` arms and the (merged)
  binary i64 comparison arm delegate behind `SYNTH_SEL_DSL` (default OFF);
- `select_with_stack`: the i32 unary arms (allocated `dst`/`src`) and the
  `I64SetCond` arm (stack-tracked pairs, `alloc_temp_or_spill` result)
  delegate the emission window, hand-written otherwise.

## Gates (same two as increments 1–3, in order)

1. **Mirror-pinning per op** — the select_default loop now pins 30 rules;
   the select_with_stack loop 17 (with a unary window branch); the i64
   dedicated loop 16 (with an I64SetCond window branch). All include the
   RMW-vacuity window check: the hand-written emission window must equal the
   rule's output for the selector's own chosen registers.
2. **Frozen fixtures** — OFF ≡ baseline by construction (every delegation is
   flag-gated); the `.text` byte gate (`frozen_codegen_bytes.rs`) green
   flag-off AND flag-on (the delegations are byte-identical, so
   `SYNTH_SEL_DSL=1` must not move a fixture byte).

## What remains before the SYNTH_SEL_DSL default flip

Unchanged from increments 2–3: nothing byte-visible — the flip changes which
*code* serves the arms, not what they emit. The flip itself is a later PR
with the standard re-freeze ritual, one release, never bundled with a
byte-changing lever. 40/40 rules (100%) still serve behind the default-OFF
flag.
