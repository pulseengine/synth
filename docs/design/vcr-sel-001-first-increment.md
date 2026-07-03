# VCR-SEL-001 — First increment scope (Rocq-discharged selector DSL)

Status: **design** (no code yet). Scopes the first wired increment of
`VCR-SEL-001` in `artifacts/verified-codegen-roadmap.yaml`, epic #242.
Evidence base: the pilot measurement `coq/Synth/Synth/VcrSelPilot.v`
(2026-06-20, 7 Qed / 0 Admitted, built green via `//coq:vcr_sel_pilot`).

## Where the pilot left us

The go/abandon question — "do the existing tactics still auto-discharge once a
rule is lifted from fixed R0/R1 to universally-quantified registers?" — came
back two-tier:

- **Tier A (no-scratch, single-instruction i32 binops):** Add/Sub/Mul/And/Or/
  Xor — **6/6 auto-discharge unchanged** (`synth_binop_proof_poly` is verbatim
  `synth_binop_proof` modulo the lowering-unfold target). One Qed per op covers
  every register aliasing.
- **Tier B (scratch-using shapes):** `i32.rotl` (RSB scratch + ROR)
  generalizes but needs an explicit `rs <> rn` non-aliasing hypothesis the DSL
  must carry and feed the allocator.
- **Out of reach for now:** trap-guarded div/rem — their fixed-register proofs
  are already Admitted, blocked on the flat executor's no-op `BCondOffset`
  (VCR-ISA-001), not on register generalization.

The pilot generated no Rust and replaced no selector arm. The first increment
is exactly that step: **the smallest wiring in which a hand-written arm is
served from a verified rule**, without moving a byte of frozen output.

## Increment-1 scope

### 1. Op families

- **In:** the tier-A six — `i32.add`, `i32.sub`, `i32.mul`, `i32.and`,
  `i32.or`, `i32.xor` — plus **one** tier-B shape, `i32.rotl`, included
  deliberately so the DSL's rule format carries a scratch non-aliasing side
  condition from day one (a DSL that can only express side-condition-free
  rules would be a dead end).
- **Out:** div/rem (VCR-ISA-001-gated), i64 pairs, comparisons, shifts-by-
  register, memory, control flow, and the optimized path entirely — the DSL
  targets `select_default`'s arms only (`select_with_stack` /
  `optimizer_bridge` are phase-later; collapsing the selector accretion is
  motivation (ii), not increment 1).

### 2. Coexistence with the hand-written selector

- The DSL is a **checked-in rule table**: declarative
  `op → parameterized ARM sequence` (registers as variables, side conditions
  explicit), plus a generator that emits plain Rust lowering functions
  **committed to the tree** — reviewable diffs, no build-time codegen magic.
- `select_default` **keeps dispatch ownership**. A migrated op's match arm
  delegates to the generated rule behind `SYNTH_SEL_DSL` (default **off**);
  unmigrated arms are untouched. `OFF ≡ baseline` byte-identical by
  construction — the same landing pattern as every VCR-RA lever.
- The exhaustive `WasmOp` match (no `_ =>` wildcard) stays: compile-checked
  coverage remains owned by the compiler, per the 2026-06-20 re-scoping.

### 3. The Rocq obligation per rule

One universally-quantified **T1 theorem per rule**, in the `VcrSelPilot.v`
form:

```coq
Theorem rule_i32_add_correct : forall rd rn rm astate,
  exists astate',
    exec_program (rule_lowering I32Add rd rn rm) astate = Some astate' /\
    get_reg astate' rd = I32.add (get_reg astate rn) (get_reg astate rm).
```

(For `rotl`, with the explicit `rs <> rn` hypothesis.) Discharged by
`synth_binop_proof_poly`; **rule ↔ theorem naming is 1:1** and a coverage
check fails the `//coq` build if any rule lacks its Qed — a rule without a
theorem cannot merge. Honest T1 bound carried over from the pilot: the
theorems prove "the ARM sequence computes the named result", not full WASM
refinement (that upgrade is VCR-WASM-001/VCR-ISA-001 territory).

### 4. Frozen anchors gate the migration

Two gates, in order, before any default flip:

1. **Mirror-pinning per op** (the #511/#513 pattern): a test lowers the probe
   set through BOTH the hand-written arm and the generated rule and asserts
   **byte-equality**. The two must-agree implementations are pinned before the
   flag can matter. Increment 1 migrates *structure, never bytes* — the
   generated rules must reproduce the current lowering exactly.
2. **Frozen fixtures under the flag**: `SYNTH_SEL_DSL=1` must keep
   `control_step 0x00210A55`, flat+inlined `flight_algo 0x07FDF307`, and
   `divseam` bit-identical, plus the full differential green. Only then may
   the default flip — one op-class per release, never bundled with a
   byte-changing lever.

## Success criterion for increment 1

The six ALU arms + `rotl` are served from the DSL with their seven Qed
theorems; fixtures bit-identical under the flag; and deleting a hand-written
arm body is a no-op. That is the first *structural* (not additive) step of the
VCR-SEL-001 migration — after it, the per-op-class cadence is mechanical:
rule + theorem + mirror-pin + flip.

## Kill-criterion (unchanged from the artifact)

≥70% auto-discharge per attempted rule over the pilot class, and bit-for-bit
selector match. Increment 1's class is chosen to be at 100%/100% by
measurement — if even this class cannot wire bit-identically, the DSL
collapses into "CompCert with extra syntax" and the direct-proof path
(the existing T1 tactic suite against `exec_indexed`) wins instead.
