# CLAUDE.md — Synth Project Context

## What This Is

Synth is a WebAssembly-to-ARM Cortex-M (Thumb-2), Cortex-R5 (A32), RISC-V (RV32IMAC), and AArch64 (host-native) compiler with mechanized correctness proofs in Rocq (formerly Coq). It produces bare-metal ELF binaries for embedded targets.

Part of [PulseEngine](https://github.com/pulseengine): synth (compiler) + [loom](https://github.com/pulseengine/loom) (WASM optimizer) + [meld](https://github.com/pulseengine/meld) (platform).

## Build Commands

```bash
# Rust — primary build
cargo test --workspace             # full workspace test suite (no C++ toolchain needed since v0.27.0 — ordeal replaced the default Z3 engine)
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --check

# Bazel — full build including Rocq proofs and Renode emulation tests
bazel build //crates:synth         # Rust binary via Bazel
bazel test //coq:verify_proofs     # Compile all Rocq proofs
bazel test //tests/...             # Renode ARM Cortex-M4 emulation tests
```

## Crate Map

| Crate | Purpose |
|-------|---------|
| `synth-cli` | CLI entry point (`synth compile`, `synth verify`, `synth disasm`) |
| `synth-core` | Shared types, error handling, `Backend` trait, WASM decoder |
| `synth-frontend` | WASM Component Model parser and validator |
| `synth-backend` | ARM Thumb-2 (Cortex-M) + A32 (Cortex-R5) encoder, ELF builder, vector table, linker scripts, MPU |
| `synth-backend-riscv` | RISC-V RV32IMAC backend (selector, encoder, relocatable ELF) — qemu_riscv32 / ESP32-C3 |
| `synth-backend-aarch64` | AArch64 (A64) host-native backend — i32/i64 core, complete scalar f32/f64, globals, `call_indirect`, bounds-checked linear memory; `-b aarch64` |
| `synth-backend-awsm` | aWsm backend integration (WASM→native via aWsm) |
| `synth-backend-wasker` | Wasker backend integration (WASM→Rust transpiler) |
| `synth-synthesis` | WASM→ARM instruction selection, peephole optimizer, pattern matcher |
| `synth-cfg` | Control flow graph construction and analysis |
| `synth-opt` | IR-level optimization passes (CSE, constant folding, DCE) |
| `synth-verify` | SMT translation validation — ordeal (pure-Rust QF_BV) default; Z3 = feature-gated differential oracle |
| `synth-analysis` | SSA, control flow analysis, call graph |
| `synth-abi` | WebAssembly Component Model ABI (lift/lower) |
| `synth-memory` | Portable memory abstraction (Zephyr, Linux, bare-metal) |
| `synth-qemu` | QEMU integration for testing |
| `synth-test` | WAST→Robot Framework test generator for Renode |
| `synth-wit` | WIT (WebAssembly Interface Types) parser |

## Rocq Proof Suite

**Directory**: `coq/Synth/` (logical prefix: `Synth`)

### Key Files

- `Common/Base.v` — Foundational definitions, tactics (`get_set_reg_eq`, etc.)
- `Common/Integers.v` — I32/I64 integer modules (CompCert-style `repr`/`unsigned`/`signed`)
- `Synth/Compilation.v` — The `compile_wasm_to_arm` function mapping WASM ops to ARM instruction sequences
- `Synth/Tactics.v` — Automation: `synth_binop_proof`, `synth_comparison_proof`, `synth_unop_proof`
- `Synth/Correctness*.v` — Per-category correctness proofs
- `ARM/ArmSemantics.v` — ARM instruction execution model
- `WASM/WasmSemantics.v` — WebAssembly stack machine model

### Common Proof Pattern

```coq
Theorem i32_add_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 -> get_reg astate R1 = v2 ->
  exec_wasm_instr I32Add wstate = Some (...) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Add) astate = Some astate' /\
    get_reg astate' R0 = I32.add v1 v2.
Proof. intros. synth_binop_proof. Qed.
```

### Rocq 9 Migration Notes

- Use `From Stdlib Require Import ...` (not bare `Require Import ZArith`)
- The stdlib moved to `Stdlib` prefix (e.g., `From Stdlib Require Import Lia`)
- `Require Import` does NOT re-export to dependent files; use `Export` or import directly
- `Z.mod_mod` signature changed — some proofs need reworking

### Building Proofs

```bash
# Via Bazel (hermetic, uses Nix for Rocq toolchain)
bazel test //coq:verify_proofs

# Via Make (requires local Rocq 9 installation)
cd coq && make proofs
```

### Proof Status

See `coq/STATUS.md` for the complete coverage matrix. Current: 623 Qed / 2 Admitted
(+2 `admit.` tactics) across `coq/Synth/`. The 80 selector-DSL rule theorems
(`VcrSelRules.v`) are stated directly about the GENERATED model (VCR-ISA-001
#667: `rule_X := Gen.rule_X`, single source `VcrSelRulesGenerated.v` emitted
from the shipped `sel_dsl::RULES`); the former 40-lemma `VcrSelRulesGenCheck.v`
reflexivity gate was retired as vacuous once the hand-written mirror was gone
(512 → 472). This count is CI-gated: `claims.yaml` +
`scripts/claim_check.py` re-derive it on every commit — when a proof lands, update
the docs AND `claims.yaml` in the same PR. Proofs are tiered:
T1 (result-correspondence), T2 (existence-only), T3 (admitted). Remaining admits:
2 ArmRefinement.v — 0 division admits
(all four i32 div/rem trap guards discharged against `exec_program_br`, #73)
and 0 i64 admits. (#166: the 2 Compilation.v example admits were discharged
via `vm_compute`; the former CorrectnessSimple.v `i32_const_correct` T3 was
closed in #933 by normalizing `I32Const` at the WASM model boundary — the
theorem as previously stated quantified over un-normalized `Z` representatives
and was false; the reconstruction arithmetic (`movw_movt_reconstruct_Z`,
`i32_const_large_reconstruct`) plus boundary normalization now discharge it;
the 2 ArmRefinement.v admits
are opaque-`sail_exec_instr`-axiom placeholders superseded by `SailArmBridge.v`.)
All i32 AND i64 operations have T1 proofs (i64 T1 parity since v0.11.0).

### Claim-verification gate

Load-bearing doc claims (proof counts, "verified" wording, DSL rule coverage,
trusted-base sizes) are pinned in `claims.yaml` and re-derived by
`python3 scripts/claim_check.py claims.yaml` (CI job `claim-check`). Never fix a
red gate by loosening the ledger — when evidence genuinely weakened, change the
public claim; when a proof/rule landed, bump doc + ledger together.

## North Star (roadmap)

**Replace synth's patch-accreting code generator with foundationally-verified,
allocator-robust infrastructure — correctness from construction, not an
ever-growing pile of locally-correct patches.**

> **EXTENSION (v0.60, researched 2026-08-25 — the goal was right and too narrow).**
> Two invariants, both earned rather than asserted:
>
> 1. **Derive what you check against from the artifact you ship.** No
>    hand-written mirror of a shipped thing. This was invented locally three
>    times before anyone named it — the generated Rocq model (#667), real-encoder
>    WCET pricing (#936), the family-aware ratchets (RQ-58-METRIC) — and the
>    external literature says the same failure recurs everywhere it is violated.
>    Crocus (ASPLOS 2024) verified ISLE lowering rules against HAND-WRITTEN
>    instruction specs; Arrival (OOPSLA2 2025) then found an `sdiv`
>    miscompilation Crocus had **erroneously verified**, because the hand spec was
>    wrong — and fixed the class by deriving 93 % of specs from Arm's
>    authoritative machine-readable ISA. synth's own #1021 is the same shape one
>    tier down: `rule_i32_popcnt` was genuinely proved, but `ArmSemantics`
>    executes `POPCNT` atomically (`set_reg s rd (I32.popcnt v)`), so the R11
>    clobber in its ENCODER EXPANSION was unrepresentable in the model. An atomic
>    model of a multi-instruction expansion is not a missing feature; it is a
>    silent claim that the expansion is scratch-free.
>
> 2. **Reach is part of correctness.** A proof about input we refuse is worth
>    nothing. Measured on 805 REAL-WORLD modules (#1017 — toolchain output and
>    wasm.directory components, not spec fixtures): ARM accepts **531/805
>    (66 %)**, RISC-V **113 (14 %)**, AArch64 **13 (1.6 %)**. A verified compiler
>    that accepts 1.6 % of real AArch64 input is verified about almost nothing.
>    The ranked blockers are all WELL-TRODDEN ELSEWHERE and closable WITHOUT
>    spending the trust story: AArch64 import dispatch (~121 modules, and 88 of
>    101 real components) is the Wasker/wasm2c undefined-symbol pattern, which IS
>    synth's own ARM `--relocatable` design ported; multi-memory (124 modules)
>    became a **Wasm 3.0 standard on 2025-09-17**, so declining it is no longer
>    "we only do standardized wasm".
>
> **What the research also says NOT to do**, recorded so it is not re-litigated:
> the search strategy is not where allocator quality lives. LLVM moved to greedy
> in 2011 and WebKit recently replaced Air's IRC graph colouring with a greedy
> allocator at similar quality and much higher speed; both converged on cost
> model, coalescing/hints and splitting as the real levers. synth's own
> RQ-59-MEASURE verdict found the same thing independently — the regression tail
> traced to the **cost metric** (which prices a 2-byte register copy and a 4-byte
> frame reload identically), not to the algorithm. So VCR-DEC-001's remaining
> increments target the cost model and the tied-operand handling, NOT a better
> search. Also ruled out with reasons: porting regalloc2's backtracking engine
> (its wins are pressure-at-scale wins), ILP/SMT in the compile path (trusted-base
> cost), SSA-chordal (optimizes the non-binding constraint; synth is not SSA),
> ML-guided eviction (non-deterministic quality, antithetical to a proof-carrying
> compiler), a full bare-metal WASI (nobody has one; a ~10-function BSP archive is
> the practice), and competing with WAMR on feature breadth. The moat is the two
> artifacts DAL-A certification actually consumes — proven functional correctness
> and sound timing bounds — which no surveyed system produces.
>
> **Strategic note:** no safety-certified wasm runtime exists. synth's structural
> advantage is having NO RUNTIME TO CERTIFY — the CompCert-shaped story that
> DO-333 (the DO-178C formal-methods supplement) already tells authorities how to
> consume.

> **CORRECTION (v0.58, measured — the goal is right, the strategy was not).**
> A rule is NOT done when it is proven. It is done when the hand-written arm it
> replaces is **DELETED**. Measured v0.42.0 → v0.57.0: `instruction_selector.rs`
> grew **24,909 → 29,616** lines (churn **5,515 added / 808 deleted**, 6.8:1)
> while VCR-SEL-001's verified rules went **40 → 50 and then sat flat for twelve
> releases** (RQ-58-METRIC re-derived this: the manifest reached 50 at
> **v0.45.0**, not v0.50 — 40 at v0.42/v0.43, 41 at v0.44, 50 ever since, so the
> stall is nearly twice as long as first reported);
> the workspace grew 130,658 → 174,578 lines. We were building the
> verified path ALONGSIDE the unverified one, and the unverified one was winning
> on volume — because "replace" was never measured, only asserted.
>
> The compounding cost: each release added a proof, a checker for the proof, a
> doc claim about the checker and a ledger pin for the doc — all hand-maintained
> (57 files say "mirror", 11 "hand-maintained", exactly **1** "single source of
> truth"). v0.57 then found **5 of its 10** defects were in checkers, and three
> doc claims had rotted behind a green gate. Verification machinery became its
> own defect surface because nothing was ever retired.
>
> So the metric is now **subtraction**, CI-pinned so it can go the wrong way
> (RQ-58-METRIC): selector line count and wildcard count are CEILINGS that must
> fall; the rule count is a FLOOR that must rise. Adding a hand-written lowering
> without deleting one must turn the gate red.
>
> **The ratchet, and how to move it.** Seven `kind: ratchet` pins in
> `claims.yaml` (engine + escape hatch documented in `scripts/claim_check.py`,
> unit-tested in `scripts/test_claim_check.py`, printed every CI run by
> `claim_check.py claims.yaml --metric`). Each carries a `value:` that must
> EQUAL the live derivation — there is no "current + slack" ceiling to hide in,
> so **every movement of a pinned number is a visible `claims.yaml` diff in the
> PR that caused it**. Beating a baseline fails until `baseline:` is updated
> too, so a win cannot be silently given back. The DIRECTED pins are
> region-scoped (measured before `#[cfg(test)] mod tests`) because a large
> share of the selector file is its own test module (at pin creation, v0.57:
> 43 of its 105 `_ =>` arms and 11,136 of its 29,616 lines; the live figures
> move with the pins in `claims.yaml` — 35 of 90 and 10,608 of 28,599 after
> RQ-58-RETIRE + RQ-58-WILDCARD);
> the whole-file counts are pinned `direction: track` — slack-free, but
> asserting no direction, so adding test coverage costs a number update and not
> a waiver.
>
> This is deliberately **not a code-golf gate** — it counts hand-maintained
> DECISIONS, not characters, and the ceilings are measured over the selector's
> non-test region so adding tests never moves them. When a lane legitimately
> needs to grow the file, the ceiling MOVES: add a `waivers:` entry whose `to:`
> equals the new value with a written `reason:`, in the same PR (the #911 rule
> applied to size). The waiver is bound to that value, so a second regression
> needs a second waiver — permission is per-growth, never standing. Use it;
> a gate people cannot move honestly is a gate they route around.
>
> This is NOT "clean up the codebase" — refactoring 29k lines of selector
> without a per-step execution oracle is how you inject the miscompiles this
> project exists to prevent. Every subtraction is gated on byte-identity or an
> execution differential; a deletion that moves emitted bytes without an oracle
> proving the new bytes correct is REFUSED, not explained. The recurring greedy fixes
(reciprocal-mult cost-gate, register-exhaustion hard-fail, the "selector missed
an op" class #223/#226/#232) are symptoms of two single-pass hand-written
components: the instruction selector and the register allocator. Filed as the
phased, parallelizable **VCR-\*** rivet program (epic #242,
`artifacts/verified-codegen-roadmap.yaml`), built incrementally — behavior
frozen and oracle-gated every step:

- **Track A (core):** `VCR-RA-001` allocator with Belady spilling — **verified,
  default-on since v0.24.0** (`SYNTH_SPILL_REALLOC`; `SYNTH_SPILL_ON_EXHAUST`
  built flag-off, silicon-gated #580). Next: `VCR-SEL-001` Rocq-discharged
  verified selector DSL (increments 1–6 shipped **default-on**, 80 rules / 80 Qed;
  the Rocq-proved rules are the ONLY lowering path for their 60 covered ops —
  RQ-58-RETIRE (v0.58) deleted the superseded hand-written arms byte-identically,
  and with them the `SYNTH_SEL_DSL`/`SYNTH_NO_SEL_DSL` lever and the mirror-pin
  gates, both vacuous once the second implementation was gone) and
  `VCR-PERF-002` proof-carrying specialization (#494,
  0.45× floor; phase 1 facts ingestion landed, PR #624).
- **Track B (semantics):** `VCR-ISA-001` Sail-generated Rocq ISA model —
  approved, Sail/ASL bridge spike landed (92 Qed, `coq/Synth/ARM/SailArmBridge.v`);
  "generate, don't mirror" landed (#667): the shipped `sel_dsl::RULES` table
  EMITS the covered ops' Rocq lowerings
  (`coq/Synth/Synth/VcrSelRulesGenerated.v`, `Module Gen`), and `VcrSelRules.v`
  DEFINES `rule_X := Gen.rule_X` — the generated file is the single model
  source, the 80 correctness Qed are stated directly about it, and a
  selector-table change regenerates `Gen` and breaks the matching proof, so the
  #682 model↔selector drift is unrepresentable at the instruction-sequence level
  for those ops (the interim `VcrSelRulesGenCheck.v` reflexivity gate was
  retired as vacuous/subsumed). `VCR-WASM-001` WasmCert-Coq source semantics —
  phases 1–3 landed: the i32 (19 ops) AND i64 (22 ops) integer fragments
  transcribed from the
  pinned coq9.0-wasm-2.2.0 sources with line-level provenance and proven
  refined by `exec_wasm_instr` (104 Qed, `coq/Synth/WASM/WasmCertBridge.v`;
  all 22 i64 ops carry both op-level and executor-level refinement);
  real external dep nix-feasible, bazel-deferred (roadmap entry).
- **Track C (validation):** the differential oracles are CI-gated jobs
  (cmp-select, RV32 shift-fold/const-addr-fold, callee-saved, spill-frame,
  symtab-based frozen-fixture differentials). `VCR-VER-003` (#777, implemented
  v0.46; phase 2 v0.47) is a per-compilation *static-data addressing* validator
  (`synth_core::static_data_addr`): for every static-data reloc it proves the
  bytes the packed `.data` serves equal the runtime-image bytes (overlapping
  active segments applied later-wins), hard-erroring the compile on the #757
  wrong-segment miscompile. Concrete byte-equality (not SMT), unconditional
  (runs in the default `--features riscv` build), red-first gated (same
  validator Mismatch on `.position()` / Consistent on `.rposition()`).
  Phase 2 (#777 follow-ups): conservative multi-byte SPAN validation against
  the shipped init blob on the mixed split (the staggered-overlap straddle is
  refused with a span diagnostic); the self-contained `--cortex-m` #758 ROM
  image is packed by a shared later-wins packer and validated unconditionally;
  RV32 active data segments SHIP since v0.48 (#798): sparse `.wasm_data`
  records ([off][len][bytes], declaration order) placed in flash by the
  generated linker.ld and byte-copied to `__linear_memory_base + off` by the
  generated startup at reset — the emitted blob is READ BACK and
  validate_served_image hard-errors the compile on any served/runtime
  disagreement (the v0.47 warning is gone; the de-vacuated control_step
  differential + a full-boot unicorn oracle gate it); AArch64 is N/A, but for a
  DIFFERENT reason than when this was written — it HAS bounds-checked
  linear-memory load/store (v0.52 #865), and is N/A because it emits no data
  section at all and REFUSES a module carrying active data segments loudly
  (v0.53), so there is no served-vs-runtime image to compare.
- **Track D (schedulability, #778):** `--emit-wcet` emits a SOUND static
  per-function worst-case cycle bound (`synth-wcet-v1` sidecar) as gale spar's
  T3/T4 `C_i` input — a bound, not a DWT observation. Loop-free functions get an
  EXACT sum of documented Cortex-M3/M4 worst-case per-op cycles (MAX over {M3,M4};
  the sound-critical model constants are `STRAIGHTLINE_CEIL_PER_HALFWORD = 5`,
  `Umull = 5`, `Mls/Mla = 2`, `Sdiv/Udiv = 12`, `BL_BLX_CALL_OVERHEAD_CYCLES = 4`
  (1+P, P≤3, the branch-with-refill class), and the four i64 software
  div/rem = `LoopedExpansion` decline, pinned in `claims.yaml`). Phase 2
  (v0.47): canonical const-bound counted loops (const init/step/bound, head- or
  bottom-test, nested-multiplicative, memory-writing bodies) are PROVEN by a
  conservative symbolic walk over the final stream (`wcet_loops.rs`, real-
  encoder byte layout — NOT the estimator, whose high-reg `SetCond` sizes
  drift) and bounded `trip × per-op worst cases`; `--wcet-hints`
  (`synth-wcet-hints-v1`, UNTRUSTED scry seam) entries are verified against
  synth's own derived trip and REJECTED with machine reasons
  (`hint-below-derived-trip` / `hint-unverifiable-induction`) otherwise —
  equality-exit shapes bound only under a verified hint. Phase 3 (v0.48):
  INTER-PROCEDURAL COMPOSITION over the DIRECT call graph (`wcet_compose.rs`, a
  pure memoized DFS over per-function intermediates) — a caller with a direct
  `BL func_N` to a LOCAL bounded callee is now BOUNDED (`total = own_cycles +
  Σ_site multiplier × callee_total`), the per-site multiplier being the call
  site's proven execution count so a callee invoked inside a proven loop is
  counted `trip×` (never once). Decline-honesty residuals (moved, never deleted):
  recursion / any call-graph cycle → `recursion`, indirect `Blx`/`call_indirect`
  → `indirect-call`, external/import direct call → `call`, a declined callee →
  `callee-unbounded` (a decline propagates UP). Phase 4 (#49): BOUNDED
  SELF-RECURSION via a VERIFIED depth-hint (`wcet_recursion.rs`) — the `recursion`
  decline is CONVERTED for exactly one provably-sound shape: a SINGLE-self-call
  chain (mult 1) whose controlling value is ENTRY-INDEPENDENTLY bounded by a mask
  (`m = param & K ∈ [0,K]`), decreasing by a const step toward a base guard on the
  SAME masked quantity, with the self-call proven control-dependent on that guard.
  synth DERIVES its own max depth (`exit_index` seeded at `init = mask`, wrap/
  divisibility-safe) and the composer folds the self-edge as `(max_depth+1) ×
  frame_cost` (the `+1` base frame is sound-critical, pinned in `claims.yaml`); a
  `--wcet-hints` `recursion_depth` entry only GATES consumption (opt-in, mirroring
  the equality-exit loop gate) — the emitted depth is always synth's DERIVED
  ceiling, never the raw hint. Decline-honesty MOVED not deleted: a too-low hint →
  `hint-below-derived-depth`; a TREE recursion (two self-calls, e.g. fib — `depth ×
  per-frame` would under-count exponentially), an UNCAPPED runtime-param countdown
  (unbounded at one end of i32), mutual / indirect recursion → still LOUD-decline
  `recursion` + `hint-unverifiable-recursion`. Data-dependent loops, non-canonical
  shapes, i64-software-div and non-M3/M4 cores (incl. the ambiguous `-eabihf`
  M4F/M7 triple) still LOUD-DECLINE with a machine reason. Frozen-safe (`.text`
  unchanged, hints/sidecar byte-invisible); gated by `wcet_bound_gate.rs` (bound ≥
  actual + trip-aware floor + red-first hint rejection + decline matrix + composed
  exact-literal chain + recursion/indirect decline honesty + masked-recursion
  accept/reject) and the `wcet_phase4_49_recursion_soundness.py` unicorn cross-
  check (`md(0xFFFFFFFF)` executes 267 insns across all 16 frames ≤ 752 cyc,
  entry-independent). Phase 5 (#778): DATA-DEPENDENT masked-ceiling LOOP
  certificates (`wcet_loops.rs`) — the scry seam extended past const-trip to a
  loop whose exit bound is a MASKED value `i REL (x & K)`. `x & K ∈ [0, K]` for
  ANY runtime `x` (`Sym::Masked`, mask sign-bit clear; base identity irrelevant),
  so synth DERIVES the worst-case trip as the MAX over BOTH endpoints of `[0, K]`
  (`rhs = K` and `rhs = 0`, both required to terminate — a single endpoint would
  undercount a count-DOWN loop, the fatal class; the both-endpoints max is pinned
  in `claims.yaml`). Like the equality-exit and recursion-depth seams it is
  HINT-GATED (unhinted masked loop still declines `loop`) and DERIVE-not-trust
  (emitted trip is synth's derived ceiling, source `mask-ceiling`); a too-low hint
  → `hint-below-derived-trip`; an UNMASKED `i < param` (no entry-independent
  ceiling) still LOUD-DECLINES `loop` + `hint-unverifiable-induction` (the mask is
  the sole discriminator — the decline MOVED onto the masked shape, not widened to
  every runtime bound). Gated by `wcet_bound_gate.rs` (count-up/-down accept +
  unhinted/too-low/unmasked reject) and the `wcet_phase5_778_masked_loop_soundness.py`
  unicorn cross-check (count-down `cd(0)` executes 180 insns ≤ 339 cyc). Richer
  certificates (clamp-bounded controlling values, data-dependent recursion depths,
  scry) are a named follow-up. #936: `I64Const`/`I64Ldr`/`I64Str` are now
  PRICED rather than declined — reachable on the RELOCATABLE/direct selector
  (`select_with_stack`, #197; `coverage()` in `estimator_encoder_agreement.rs`
  hand-asserts they are OffPath for the optimized selector, a claim that file's
  own doc says it cannot prove exhaustively). `I64Const`/`I64Str` are the two
  opcode families gale's whole-object `--emit-wcet` run over a real `gust:os`
  composite found behind all 9 of its `unmodeled-op` declines (and 11
  `callee-unbounded` cascades behind those); `I64Ldr` is a separate finding —
  #921's own `unmodeled-op` reproduction used `i64.load` — priced alongside
  its two siblings because it shares `i64_effective_base`'s address-
  materialization shape. Sized from the REAL Thumb-2 encoder's own byte length
  per instance (`straightline_expansion_real`), not a hand-mirrored predicate:
  an exact hand mirror of `i64_effective_base`'s offset-fold threshold was
  tried first and found UNSOUND at authoring (the address-materialization
  `ADD` can need its own `MOVW` for a large offset, which only the real
  encoder's own output reflects) — the same drift class `op_mnemonic`'s "no
  second source of truth to forget to update" already guards against
  elsewhere in this file. The #936 audit's HONEST RESIDUAL —
  `scan_for_decline` reports only the FIRST decline per function, and
  `I64Sub` (a saturating trunc-sat conversion sequence),
  `I64ExtendI32S`/`I64ExtendI32U`, and `I32WrapI64` were ALSO real
  direct-selector emissions with no price — was closed by RQ-59-WCETI64
  (v0.59): all four are priced by the same real-encoder mechanism (measured
  per op, decline scan re-run after each; nothing new surfaced behind any of
  them), so the narrowing shape (`i64.load` + `i32.wrap_i64`) and the
  widen-store shape (`i64.extend_i32_s` + `i64.store`) now BOUND. `I64Sub`'s
  only real emission (the f64 trunc-sat decompose) cannot even compile on a
  sound core — priced so a future integer-path emission is covered, not
  latent. Still-loud declines, measured: `memory.size`/`memory.grow`
  (`unmodeled-op`), i64 software div/rem (`looped-expansion`, deliberate).
  Gated by `wcet_bound_gate.rs` (leaf + cascade-composition + converted
  narrow shape + still-declines pins) and the
  `wcet_phase6_936_i64_leaf_soundness.py` +
  `wcet_phase7_936_i64_conv_soundness.py` unicorn cross-checks.
- **Gate `VCR-VER-001`:** DEMONSTRATED (implemented, evidence in
  `scripts/repro/vcr_ver_001_gate.md`) — the v0.11.20 reciprocal-mult
  cost-gate was deleted outright (PR #322, differential bit-identical); the
  #496 exhaustion decline is revertable behind `SYNTH_SPILL_ON_EXHAUST`
  (red case green, anchors byte-identical, declines 14→8) with the flip
  held on a measured i32-shape cycle regression (missing capability:
  post-exhaustion code quality on the optimized path).

Shipped default-on levers (v0.13–v0.30, each evidence-gated with a CI-pinned
opt-out): cmp→select fusion (ARM+RV32), i32 local promotion, immediate-shift
folds (ARM+RV32), base-CSE, const-CSE (gale-confirmed gust_mix 90→86 B),
dead-frame-elim, uxth-fold. The gale #209 numbers that motivated Track A
(flat_flight 315 cyc vs 99 native, 61 % redundant consts, 17 spills) are
historical — flat_flight sits at its Belady optimum (frame traffic 0) since
v0.24.0. See the README "Roadmap — North Star" section for the full table.

## Compliance envelope (state this before any performance comparison)

**In its default embedded configuration synth emits no out-of-bounds trap.** An
OOB linear-memory access reads or writes whatever sits at `R11 + addr`.
Spec-conformant OOB trapping requires `--safety-bounds software|mask|mpu` on
ARM/RV32, and is unconditional on AArch64 (v0.52 #865). The default
(`SafetyBounds::None`, `synth-core/src/backend.rs`) is a deliberate bare-metal
choice — "fastest, unsafe", relying on MPU/PMP or a trusted module — not an
oversight. It is pinned by `SYNTH-SAFETY-BOUNDS-DEFAULT-ENVELOPE` in
`claims.yaml` so it cannot change silently.

Why this section exists: the 2026 wasm2c-performance findings (Narayan, UT
Austin) showed several AOT wasm compilers posting numbers flattered by
undisclosed non-compliance — aWsm lowering i32/i64 accesses to typed LLVM
pointers so LLVM assumes no-alias (illegal under wasm's untyped linear memory),
and per that talk WAMR and Wasmer trading away the dead-load trap obligation.
The failure mode is not dishonesty; it is that an unstated envelope turns every
comparison into flattery. So:

- **Never publish a cross-compiler benchmark without a compliance column** —
  bounds-check mode, trap-preservation status, and which spec categories each
  configuration passes. Where a competitor's status is unverified, write
  "unverified" rather than repeating a claim.
- **Publish the acceptance rate as the denominator, and as a feature.** Measured
  on 805 real modules (#1017): ARM 66 %, RV32 14 %, AArch64 1.6 %. Perf numbers
  describe the accepted subset only. Loud-decline-over-silent-miscompile is the
  actual differentiator against systems that accept everything and are quietly
  wrong on some of it — disclosed, selection bias becomes a soundness story;
  undisclosed, it is the same flattery.
- **Report WCET claims separately from throughput.** synth is the only system in
  this comparison space emitting a sound cycle bound; mixing "fast" and
  "bounded" invites exactly the confusion that makes fast/slow-path
  optimizations look like wins (see VCR-VER-002 and the Track D note on
  loop-versioning).

## Trap preservation — the rule, written down while it is free

The WebAssembly spec traps an out-of-bounds load as an effect of EXECUTING the
instruction, not as a property of its result: a load whose value is dead still
traps if its address is out of bounds. wasm2c pays real performance (inline-asm
optimization barriers, forced register materialization, lost load+op fusion) to
stay on the right side of this.

synth is compliant today **by not having the optimizations that would break it**,
which is a fragile reason to be right:

- DCE removes only instructions in UNREACHABLE blocks — never executed, no trap
  lost.
- CSE explicitly refuses `MemLoad`/`MemStore` (`synth-opt/src/lib.rs`: "there is
  no alias analysis for linear memory; any MemStore can invalidate any address").
- The one load elimination that exists — peephole store-to-load forwarding — is
  trap-preserving because the same-address, same-width store executes
  immediately before: if the address were OOB the store faults first.

**THE RULE, for any future alias-aware CSE/LICM in synth-opt or loom:** a
wasm-level linear-memory load may be removed only if (a) it is dominated by a
same-address same-width access, or (b) its address is proven in-bounds by a
certified fact. Anything else drops a trap and is the wasm2c-force-read class.
Widening the peephole (different widths, an intervening instruction, forwarding
across a guard) leaves the legitimate class — flag it in review. This obligation
belongs to `VCR-VER-002`, which is still `proposed`.

Note the distinction that matters: `--proven-safe` / fact-spec elisions remove
the GUARD on an access PROVEN in bounds, fail-closed. That is categorically
different from eliding the trap of a possibly-OOB access, and it is legitimate.

## Conventions

- Rust edition 2024, MSRV 1.88
- Edition 2024 notes: `unsafe fn` bodies require explicit inner `unsafe {}` blocks; `#[no_mangle]` must be `#[unsafe(no_mangle)]`; `static mut` access via `&raw const`/`&raw mut`
- Bazel 8.x with bzlmod (`MODULE.bazel`, not `WORKSPACE`)
- Renode tests use `rules_renode` (PulseEngine fork with macOS support)
- All `.v` files use `-Q Synth Synth` logical mapping (see `coq/_CoqProject`)
