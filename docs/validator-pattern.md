# Validator-Pattern Verification Architecture

**Status:** Proposed (prototype landed in `crates/synth-verify/src/validator_pattern.rs`)
**Issues:** [#76](https://github.com/pulseengine/synth/issues/76) (proposal), [#73](https://github.com/pulseengine/synth/issues/73) (the gap this closes)
**Date:** May 2026

## TL;DR

Synth's current verification story is: a Rocq proof suite (233 Qed) that proves
`compile_wasm_to_arm` (a Rocq function in `coq/Synth/Synth/Compilation.v`)
preserves WASM semantics. The trouble is that Rocq function *diverges* from
what the Rust selector actually emits in five documented ways
(see #73). The proofs are internally valid but do not establish correctness of
the **shipped binary**.

This document proposes adopting the **certifying-algorithm** pattern that
CompCert was built on:

1. **Untrusted selector** — the existing Rust selector in
   `synth-synthesis/src/instruction_selector.rs` keeps producing ARM
   instruction sequences. It can be arbitrarily complex, heuristic, and
   register-allocator-driven. It is *not* in the trusted base.
2. **Trusted validator** — a small, formally verified per-op checker confirms
   each concrete selection is semantically equivalent to the WASM operation it
   replaces. Implemented in Rust on top of `synth-verify`'s existing Z3
   infrastructure.
3. **Certified output** — the compiler emits a `CertifiedSelection` per WASM
   op: `(wasm_op, arm_instructions, Z3 witness)`. A binary is "certified" iff
   every selection it contains is accepted by the validator.

The validator is the only piece that needs a Rocq proof. One meta-theorem
("if the validator accepts, then the selection is semantically correct")
replaces ~150 per-op Rocq proofs. This is the pattern CompCert qualified for
DO-178C in March 2026 (ATR 42/72 aircraft).

## Motivation

### The Concrete Gap (Issue #73)

`coq/Synth/Synth/Compilation.v` defines a `compile_wasm_to_arm` function. The
Rocq proofs verify that function. But it disagrees with the Rust compiler in
five places, all documented in #73:

| # | Divergence | Rocq model | Actual Rust selector |
|---|-----------|------------|----------------------|
| 1 | Division trap guard | `SDIV Rd, Rn, Rm` (1 instr) | `CMP Rm,#0; BNE; UDF; SDIV` (4+ instr) |
| 2 | Comparison count | `CMP + MOV #0 + MOVEQ #1` (3 instr) | `CMP` only (1 instr) — flags-based |
| 3 | Register allocation | Hardcoded R0/R1/R2 | Dynamic (round-robin or stack-based) |
| 4 | Constant materialisation | `MOVW Rd, #imm16` | `MOVW`, `MVN`, or `MOVW+MOVT` for 32-bit |
| 5 | i64 operations | Modeled as 32-bit | Register pairs, multi-instruction |

Additionally, `WasmSemantics.v` has a `| _ => Some s` catch-all that makes
every unmodeled WASM instruction a no-op-that-succeeds — so all i64 proofs are
vacuously true.

### Why Closing The Gap By Updating Compilation.v Is Not Viable

Trying to keep `Compilation.v` synchronised with the Rust selector requires:

- Modelling register allocation in Rocq (a non-trivial algorithm proof)
- Modelling trap guards (requires `exec_program` to handle PC-relative
  branching, currently admitted — 7 of the 10 current admits)
- Adding 64-bit register pairs to `ArmSemantics.v`
- Re-proving every theorem after every selector change

Even if we did this work, future improvements to the selector (better register
allocator, peephole optimisations, new ARM patterns) would re-break the
synchronisation. We are committing to an open-ended maintenance burden in
exchange for proofs that say what we already informally know.

This is precisely the trap CompCert avoided. Their NP-hard passes (register
allocation, instruction scheduling) are *not* verified algorithms. Each pass
emits a concrete result + a witness; a verified validator checks the witness.
The validator is much smaller and simpler than the algorithm.

### Evidence From Recent Work

The gale silicon investigation (now-closed work on PRs #93 / #103 / #104)
surfaced exactly this brittleness: every time the selector picks a different
instruction (e.g. `I32WrapI64` epilogue handling in #111), the Rocq side either
admits the case or papers over it. The validator pattern eliminates that
coupling — the selector can change freely; the validator is invariant.

## Architecture

```
                      ┌─────────────────────────────────┐
                      │ Rust selector (untrusted)        │
                      │ instruction_selector.rs          │
                      │ ─ heuristic, dynamic regalloc    │
                      │ ─ trap guards, MOVW+MOVT, i64    │
                      └────────────┬────────────────────┘
                                   │ (wasm_op, [arm_op])
                                   ▼
                      ┌─────────────────────────────────┐
                      │ Validator (trusted)              │
                      │ validator_pattern::Z3ArmValidator│
                      │ ─ encodes WASM semantics in Z3   │
                      │ ─ encodes ARM sequence in Z3     │
                      │ ─ proves ∀state. wasm ≡ arm      │
                      └────────────┬────────────────────┘
                                   │ accept / reject
                                   ▼
                      ┌─────────────────────────────────┐
                      │ CertifiedSelection<W, A>         │
                      │   .wasm:   W                     │
                      │   .arm:    Vec<A>                │
                      │   .witness: Option<Z3Witness>    │
                      └─────────────────────────────────┘
```

### `CertifiedSelection<W, A>`

The core data type is generic in `W` (source op — initially `WasmOp`) and `A`
(target op — initially `ArmOp`, later RISC-V):

```rust
pub struct CertifiedSelection<W, A> {
    pub wasm: W,
    pub arm: Vec<A>,
    pub witness: Option<Witness>,
}
```

The selector creates a `CertifiedSelection` with `witness: None`. A `Validator`
consumes the selection, runs Z3, and either rejects (returns
`ValidationError`) or attaches a witness (returns `Witness`). The witness is a
record of what was proved — for now it's just the form of the equivalence; in
the future it can carry an SMT-LIB script that can be replayed independently.

### Per-Op Validation

Each WASM op has a *precondition* (what state the selector expects) and a
*postcondition* (what the WASM operation produces). The validator's job is:

> For all states `s` satisfying `pre(s)`, the ARM sequence executed on `s`
> produces a state `s'` such that `s'` satisfies `post(wasm, s)`.

In Z3 terms:

```
assert ¬ (wasm_result(inputs) = arm_result(execute_arm(arm_sequence, inputs)))
check-sat
```

If Z3 returns `unsat`, the equivalence holds for all inputs — the selection
is correct. If `sat`, the model is a concrete counterexample (e.g.
"`a = 5, b = 3, wasm says 8, arm says 2`") that disproves the selection.

For `I32Add`, the encoding is direct: WASM's `i32.add` is `bvadd` on
32-bit bitvectors, ARM's `ADD Rd, Rn, op2` is `bvadd` on 32-bit bitvectors,
and Z3 proves equivalence in milliseconds. For richer ops (division, shifts,
i64 pairs) the encoding is more elaborate but mechanically the same.

The full WASM and ARM SMT encoders already exist:
`crates/synth-verify/src/wasm_semantics.rs` and
`crates/synth-verify/src/arm_semantics.rs`. The new `validator_pattern.rs`
module composes them through a uniform `Validator` trait. The pre-existing
`TranslationValidator` validates `SynthesisRule` patterns (templates) — the
new pattern validates concrete `(wasm_op, [arm_op])` selections, which is
what the compiler actually emits.

### Witness Format

For the prototype, the witness is intentionally minimal:

```rust
pub struct Witness {
    pub wasm_op_label: String,
    pub arm_op_count: usize,
    pub solver_result: SolverResult, // Unsat | Sat | Unknown
}
```

A v0.5 expansion will carry the SMT-LIB2 script that Z3 was given. That makes
the witness *independently replayable*: a third party can re-run the Z3 check
without trusting the validator's encoding logic. For certification work this
is the key property — the auditor checks the Z3 script, not Synth's Rust code.

## Rocq Side: The Meta-Theorem

Once the validator is in place, the Rocq suite collapses to one theorem:

```coq
Theorem validator_sound : forall (w : WasmOp) (a : list ArmOp) (witness : Witness),
  validate w a = Some witness ->
  forall (state : State),
    exec_wasm_instr w state ≡ exec_arm_sequence a state.
```

Reading: "if the validator accepts a selection, then the WASM op and ARM
sequence are semantically equivalent on every state." This is one proof, not
one-per-op. The validator's encoding logic becomes part of the trusted base
*via this theorem* — but the trusted base is now finite, fixed, and
proportional to the validator's complexity rather than the selector's.

For the prototype, this theorem is **a stated obligation, not a completed
proof**. The Rocq proof of `validator_sound` is future work — it requires
formalising the Z3 encoding of bitvector semantics in Rocq (CompCert
formalises a similar property for their validators). For now we provide the
Rust validator, the prototype test, and the meta-theorem statement.

## Migration Plan: Retire Divergent Proofs

The 233 Qed / 10 Admitted proofs in `coq/Synth/Synth/` fall into three tiers
(per `coq/STATUS.md`):

| Tier | Description | Count | Plan |
|------|-------------|-------|------|
| T1 | Result-correspondence (i32 arith, cmp, bit-manip, shift) | 35 | Keep — these are valuable independent checks. They can be deprecated *if* the validator proves the same property for the same ops. |
| T2 | Existence-only ("ARM execution succeeds, no result claim") | 142 | Retire as the validator covers each op. T2 proofs do not constrain semantics — the validator strictly subsumes them. |
| T3 | Admitted (trap guards, MOVW+MOVT, etc.) | 10 | Re-examine. Most are admitted because `exec_program` does not handle PC-relative branches. The Z3 validator does not have this limitation: it composes ARM ops in sequence and tracks state symbolically. Several T3s should close immediately under the validator. |

The migration is **strictly additive**: the validator runs alongside the
existing Rocq proofs. No `.v` file is deleted in this PR or the next several.
A T2 op is "retired" by adding a `# Retired by validator` row to
`coq/STATUS.md` and marking the corresponding `.v` theorem with a comment
like `(* Subsumed by validator_pattern::Z3ArmValidator for I32X; kept for
historical reference *)`. The `.v` file still compiles, the proof still
passes; we just no longer claim it carries the trust burden.

### Per-Phase Op Coverage

This PR ships the prototype with `I32Add` only. Subsequent PRs (v0.5
milestone) extend coverage roughly in this order:

1. **i32 arithmetic** (`I32Add`, `I32Sub`, `I32Mul`) — direct bvadd/bvsub/bvmul
2. **i32 bitwise** (`I32And`, `I32Or`, `I32Xor`) — direct bvand/bvor/bvxor
3. **i32 shifts** (`I32Shl`, `I32ShrS`, `I32ShrU`, `I32Rotl`, `I32Rotr`) —
   modulo-32 shift amount per WASM spec
4. **i32 comparisons** (11 ops) — flags-based encoding; validator handles
   the "single CMP" vs "CMP+MOV+MOVEQ" divergence (#73 item 2) directly
5. **i32 division** (`I32DivS`, `I32DivU`, `I32RemS`, `I32RemU`) — must model
   the trap-guard sequence (#73 item 1)
6. **i32 bit-manipulation** (`I32Clz`, `I32Ctz`, `I32Popcnt`) — encoders
   already exist in `wasm_semantics.rs`
7. **i32 constants** (`I32Const`) — must handle `MOVW`/`MVN`/`MOVW+MOVT`
   selection (#73 item 4)
8. **i64 operations** — register-pair encoding (#73 item 5); the validator
   models pairs as two parallel 32-bit BVs concatenated to a 64-bit BV
9. **f32/f64** — requires Z3's floating-point theory, more work

Each phase is one PR landing 10–20 validator entries and the test cases that
exercise them. Per-op work after the prototype is small (~20 LoC of encoding
per op, mostly delegated to the existing `WasmSemantics` and `ArmSemantics`
encoders).

## Trusted Base

What we are trusting after this PR + the migration:

1. **The Z3 solver** — well-studied, used by Microsoft, AWS, etc. for
   safety-critical software (Azure VM scheduler, Firecracker microVM).
2. **The WASM SMT encoder** (`wasm_semantics.rs`) — ~1500 LoC of bitvector
   formulas. Far smaller than the Rocq formalisation it replaces.
3. **The ARM SMT encoder** (`arm_semantics.rs`) — ~1000 LoC. Same.
4. **The validator's Z3 plumbing** (`validator_pattern.rs`) — ~150 LoC.

What we are *no longer* trusting:

- The Rust instruction selector (~5000 LoC of heuristics)
- The register allocator
- The peephole optimizer
- The constant materialisation logic (MOVW vs MOVT vs MVN)
- Any future selector improvement

That is the value proposition: the trusted base shrinks even as the
compiler grows.

## Open Questions

1. **Validator scope per binary**: do we validate every selection on every
   compile, or sample? Z3 is fast for i32 ops (<10ms each), so we can afford
   to validate every selection in `synth compile` debug builds. For
   release builds we keep validation as a `synth verify --strict` mode.

2. **Validation caching**: if the selector emits the same selection for two
   different functions (very common — every `i32.add` is the same selection
   modulo register names), we should cache the Z3 result keyed on the
   selection's shape. Easy follow-up.

3. **Memory operations** (`I32Load`, `I32Store`): require a memory model.
   Z3 supports array theories; the encoders already use them. Validating
   memory ops is roughly twice the encoding work of arithmetic ops.

4. **Control flow** (`Br`, `BrIf`, `Call`): the validator works per-op,
   not per-block. For control flow we either lift to a per-block
   validator or accept that control-flow correctness lives in a separate
   layer (CFG-level proofs). The existing Rocq suite barely touches
   control flow, so this is not a regression.

5. **Cross-architecture (RISC-V)**: the `CertifiedSelection<W, A>`
   generic is designed to support `A = RiscvOp` once we have a RISC-V
   SMT encoder. RV32 work is tracked separately (`crates/synth-backend-riscv`).

## Acceptance Criteria

This PR ships a working prototype: 1 documented architecture, 1 working
`I32Add` validator, 1 test that demonstrates accept-on-correct,
reject-on-wrong. Subsequent PRs extend the op coverage. The Rocq proof
suite is unchanged; the migration story in this document is what guides
its future evolution.

## References

- CompCert: <https://compcert.org/>
- CompCert DO-178C qualification: ATR 42/72 (March 2026)
- "Translation Validation for a Verified OS Kernel", Sewell et al.
- "Mechanized verification of a fine-grained concurrent stack" — relevant
  for the validator-soundness meta-theorem
- Synth issue #73 — the divergence catalogue
- Synth issue #76 — this proposal
- Synth PR #93, #103, #104 — empirical evidence that Compilation.v
  synchronisation is fragile
