# Mutation survey — v0.65 (RQ-65-MUTANTS, #1189)

**Measured 2026-09-09** on synth at `580d53f9` (RQ-65-PARITY merged), with
`scripts/mutation_survey.py`; every verdict, the exact text diff of every
mutant, the sampling seed, the frame and the suite are in the committed ledger
`docs/status/mutation_survey.json` — the numbers below are derived from it and
pinned in `claims.yaml` (`SYNTH-MUTATION-SURVEY-*`), so they cannot drift from
the ledger without a red gate.

> **THE HEADLINE.** Of the sampled code-generator decisions that change
> emitted bytes when flipped, **4 of 21 byte-changing mutants survived** the
> named suite — **19 % survival**. Of the 17 kills, **2** came from an
> execution differential observing a WRONG VALUE against wasmtime, 8 from
> unit/integration tests, **2 from frozen-byte goldens only** (a change
> detector, not a wrongness detector), 1 from the compiler hanging, and the
> remaining **4 from the compiler REFUSING or a non-vacuity floor firing**
> (`#952` skipped exports, a compiler panic, a census `NEW DECLINE`).
>
> **"81 % caught" means CI GOES RED, not "an oracle noticed wrong code".**
> Those are different claims and the difference is the finding. Restricting to
> the **15** mutants that changed bytes SILENTLY — no decline, no panic, no
> floor — **4 survive, 27 %**, and an execution differential caught only **2**;
> 9 of the 11 silent kills came from `cargo test` and 2 from byte goldens
> alone. The apparatus is better at noticing that the compiler stopped than at
> noticing that it lied. Every survivor is enumerated below with
> its exact diff; that list is what v0.66 is scoped from. The rate is an
> **upper bound** on survival under the full CI board (§ "what it is
> relative to").

## Why this exists

#1189 (v0.64) was a silent miscompile on `main` — the if/else join register
could be a register-homed local's home register — that survived every oracle
because the then-arm was correct **by accident**. It was found by a lane
strengthening an oracle, not by anything going red. That left a question
nobody in this repository had asked: of the emitted-code DECISIONS in the
code generator, what fraction would any oracle notice being wrong?

This survey answers it the only honest way: flip one decision, rebuild, ask
the oracles, count what survives. A surviving mutant is a line of codegen that
could be wrong today with nothing to tell us.

## The number, and exactly what it is relative to

| | count | note |
|---|---|---|
| mutants drawn (seed 1189) | **38** | target 8 compiled per region; the run stopped at draw 38 when that mutant hung the compiler — R2 reached 6 compiled, R4 3 (R4 drew 4 uncompilable sites) |
| uncompilable (excluded, replaced in seed order) | 6 | rustc rejected the edit — stillborn, not in any denominator |
| compiled | 32 | |
| byte-identical on the whole corpus (no oracle run) | 11 | 5 EQUIVALENT · 4 DEAD · 2 UNRESOLVED (declared below) |
| **byte-changing — the denominator** | **21** | |
| KILLED | 17 | execution 6 · structure 8 · **freeze-only 2** · compiler hang 1 |
| **UNTESTED (survived)** | **4** | **4 / 21 = 19.0 %** |

Pinned in `claims.yaml` (`SYNTH-MUTATION-SURVEY-RQ65`): `mutants_untested` is
the eighth `kind: ratchet` — a ceiling of 4 that must fall; the 38 / 21 / 4
figures and the three controls are pinned by exact text against the ledger.

**Survival rate = UNTESTED ÷ byte-changing compilable mutants.** It is relative
to THIS frame, THIS corpus, THIS named suite (below), at `580d53f9`, seed 1189.
Three things it is **not**:

- **Not a property of the whole selector.** 38 mutants were drawn from a
  candidate pool of 1,538 sites (2.5 %), stratified 8 per region and per
  operator; 6 were uncompilable and 32 compiled. A different seed draws a
  different sample and yields a different rate — with 21 in the denominator,
  one survivor is ±5 points. The ledger records the seed so a re-run is a
  comparison, not a new claim.
- **Not against "the oracles".** It is against the five CI jobs named below
  plus the workspace test suite. A broader suite can only move survival
  **down** — an oracle cannot un-kill a mutant — so this rate is an **upper
  bound on survival** under the full CI board, which is the conservative
  direction.
- **Not a code-quality score.** Nothing here says the mutated code was wrong;
  it says whether an oracle would have said so.

## The sampling frame — stated, supplied by RQ-65-PARITY, not invented here

Five regions, ranked by PR #1216 by where the two shipped selectors disagree,
located by **function anchor** (not line number, so the frame survives
unrelated edits; the live spans are printed by `mutation_survey.py sites`):

| region | file(s) | anchor(s) | lines | candidate sites |
|---|---|---|---|---|
| R1 routing | `crates/synth-backend/src/arm_backend.rs` | `has_value_carrying_branch`, `compile_wasm_to_arm` — the optimized-vs-direct gate, its nine predicates, the `select_direct` retry ladder | 1,264 | 65 |
| R2 `ir_to_arm` | `crates/synth-synthesis/src/optimizer_bridge.rs` | `ir_to_arm_impl`, `fold_mem_offset`, `push_software_bounds_guard` | 3,715 | 346 |
| R3 direct selector | `crates/synth-synthesis/src/instruction_selector/select_with_stack.rs` | `select_with_stack` — the hand-written operand plumbing around the Rocq-proved `sel_dsl` rules | 8,227 | 509 |
| R4 shared post-merge tail | `arm_backend.rs` (`finish_allocated_stream`, `classify_arm_branch`, `resolve_label_branches`, `validate_branch_targets`), `crates/synth-synthesis/src/liveness.rs` (non-test region), `crates/synth-backend/src/arm_encoder.rs` (`i64_effective_base`) | 10,262 | 603 |
| R5 startup blob | `crates/synth-cli/src/main.rs` | `generate_minimal_startup` — the R9/R10/R11 register contract | 169 | 15 |

One correction to the frame as briefed, measured rather than assumed: the two
selectors share **no lowering code inside `synth-synthesis`** — `sel_dsl` has
zero call sites in `optimizer_bridge.rs`, and no helper defined in
`instruction_selector.rs` is called from both. What they share is downstream
of the merge point in `arm_backend.rs` (the post-selection passes, branch
resolution/validation, the encoder). R4 is defined as that.

## Operators — mechanical, one site per mutant, the diff recorded

| operator | mutation | reach probe |
|---|---|---|
| REG | `Reg::Rn` → `Reg::R((n+1) mod 13)` | the original token wrapped in `{ eprintln!(MARK); token }` |
| COND | `Condition::X` → its inverse (EQ↔NE, LT↔GE, LE↔GT, LO↔HS, LS↔HI) | same |
| DROPMOV | a `push(… ArmOp::Mov …)` statement deleted | `eprintln!(MARK);` inserted before the statement |
| IMM | `Operand2::Imm(e)` → `Imm((e).wrapping_add(1))`; `MemAddr::imm(b, o)` → `(o).wrapping_add(4)`; `imm16: e` → `+1`; `encode_thumb2_mov{w,t}(n, …)` → register `(n+1) mod 13` | the immediate wrapped |
| GUARD | `if COND {` → `if !(COND) {`; a complete `\|\| term` / `&& term` continuation line → the term negated | the condition wrapped |
| BOUND | ` < `↔` <= `, ` > `↔` >= `; `.len() - 1` → `.len()` | the left operand wrapped |

Sites are enumerated in deterministic order (file, line, column; comment and
string-literal matches excluded) and drawn with a seeded RNG, stratified per
region and per operator, round-robin across regions so any time-boxed prefix
stays balanced. A mutant rustc rejects is **UNCOMPILABLE**: excluded from every
denominator and replaced by the next draw in seed order.

## Triage before the oracles — where the affordability comes from

The corpus is every `scripts/repro/*.wat` and `*.wasm` (200 modules) compiled
in three ARM configurations — `--all-exports --relocatable --target cortex-m4`
(the direct selector, #197), self-contained `--target cortex-m4` (the
optimized path with per-function routing), and self-contained `--no-optimize`
— 600 (module, configuration) pairs, 461 objects and 139 declines on the
unmutated binary. Each object is hashed over `.text`/`.data`/`.rodata` bytes
and the symbol table (name, value, size); each mutant recompiles the corpus
(~10 s) and diffs the hashes. A newly declining or newly accepted module
counts as a change.

- **Identical everywhere** ⇒ no oracle is run. The mutant is EQUIVALENT or
  DEAD, told apart by a **reach probe**: the ORIGINAL token is rebuilt wrapped
  in a marker print and the corpus compiled again. Marker seen ⇒ the decision
  was evaluated and made no difference to any of these 600 compiles ⇒
  **EQUIVALENT** (for this corpus). Marker absent ⇒ **DEAD** (for this corpus —
  a deletion *candidate* for the subtraction ratchet, not a proof of
  unreachability). A probe rustc rejects (pattern position, const context) ⇒
  **UNRESOLVED**.
- **Changed anywhere** ⇒ the suite runs.

## The named suite — what "an oracle" means in this document

Derived from `.github/workflows/ci.yml` by `mutation_survey.py`, not
hand-listed: the selected jobs' own `run:` steps are executed verbatim under
`bash -eo pipefail` with the binary path substituted (install, ledger and
tree-mutating steps skipped). Two layers, fastest-first:

**L1 — execution differentials** (the five jobs below; 12 steps; 23 s green
on the unmutated binary; **0 steps red on baseline**, so nothing had to be
excluded for being already-failing):

| job | what it executes | why chosen |
|---|---|---|
| `wast-conformance-oracle` | 381 `assert_return`/`assert_trap` from `tests/wast/` executed under unicorn against wasmtime (#928) | the broadest executed spec-shaped corpus that runs in seconds |
| `repro-sweep-arm-corpus-oracle` | `arm_corpus_sweep_973.py` — compile census + execution differential over every emulatable `scripts/repro/*.wat`, plus the #973 and #989 differentials | the triage corpus itself, executed |
| `join-alias-1189-oracle` | the #1189 fixture red half + 149 live vectors on four legs | the oracle that closed the miscompile this release is about |
| `cmp-select-oracle` | the cmp→select two-move fusion executed flag-off/flag-on | covers the R4 `liveness.rs` fusion pass |
| `frame-slot-dce-242-oracle` | frame-slot DCE executed flag-on | covers the R4 dead-frame elision |

**L2 — structure** (only when L1 is green): the `test` job's cargo commands —
`cargo test --workspace` (84 test binaries, 1,784 tests) plus its three
follow-on commands; 274 s green on the unmutated tree. A kill here is
attributed to the failing test binaries; a kill by frozen-byte goldens alone
(`frozen_codegen_bytes`, `base_cse_flip_468`, `const_cse_reduction_242`,
`flag_flip_wave_242`, the RV32 flips) is sub-classified **freeze-only** — a
change detector, not a wrongness detector: it goes red on any byte movement
and is routinely re-pinned.

**Deliberately outside the suite, with the measured reason:**

- `selector-parity-oracle` (RQ-65-PARITY, #1216) — the coordinator's first
  suggestion and the obvious strongest kill signal for selector mutations.
  Run the CI way (single-threaded under `oracle_run.py`) it took **>20 min**
  on this machine before it was stopped, against a budget of minutes per
  survivor; CI runs it in 1m22s on a self-hosted runner. A `-j` leg is the
  first thing a v0.66 re-survey should add.
- the other 28 ARM oracle jobs (`trap-semantics-oracle`'s 32 scripts, the
  `repro-sweep-selector`/`-memory` sweeps, the call-indirect and i64 families,
  `proven-safe`, `fact-spec`, …) — affordable individually, not per mutant
  within this lane's budget. They are listed in the ledger's
  `suite.unselected_jobs`.
- the 15 jobs the frame cannot reach or that rebuild the tree: RV32 (8
  jobs) and AArch64/arm64-linux/Mach-O (4) are separate backend crates;
  `instrument-independence-oracle` mutates and rebuilds the tree itself;
  `claim-check` and `rivet` are documentation gates that happen to invoke a
  census script. In the ledger's `suite.excluded_jobs`.

Lints are not oracles: mutants build without `-Dwarnings`.

## Red-first controls — the instrument discriminates

Three mutations known to be caught were run through the same pipeline before
the sample. Every one MUST come back KILLED or the survey publishes no rate
(`mutation_survey.py controls` exits 1).

| control | mutation | corpus objects changed | verdict | killed by |
|---|---|---|---|---|
| `CONTROL/1189-copy-disabled` | `if !live_home {` → `if true {` in `copy_live_home_then_results` — the pre-#1189 behaviour, byte for byte | 7 | **KILLED** | execution: `join-alias-1189-oracle` (18 s) |
| `CONTROL/select-operands-swapped` | `rule_i32_select(dst, cond_reg, val1, val2)` → `(…, val2, val1)` on the direct selector (PR #1216's red-first plant) | 15 | **KILLED** | execution: `cmp-select-oracle` (18 s) |
| `CONTROL/startup-r10-seeded-into-r9` | `encode_thumb2_movw(10, memory_size…)` → register 9 in `generate_minimal_startup` | 325 (every self-contained image) | **KILLED** | structure: `cargo test` only (274 s) |

The third control is itself a finding: **no execution oracle in this suite
boots the shipped `Reset_Handler`** — a startup-contract mutation that
rewrites every self-contained image is caught only by FROZEN-BYTE GOLDENS
(layer `freeze-only`: `base_cse_escape_hatch…_468` and `const_cse_…_242` x2).
**No startup unit test fired, and none exists**: nothing in the named suite
decodes the emitted `MOVW`/`MOVT` for the R10 seed. A golden detects that the
bytes CHANGED; it cannot say the new bytes are wrong. (The parity oracle does
boot the shipped startup; it is the one left out for cost.)

## Per-region results

| region | sampled | uncompilable | identical (equiv/dead/unres.) | changed | killed (exec/struct/freeze-only/timeout) | UNTESTED | survival |
|---|---|---|---|---|---|---|---|
| R1 routing | 8 | 0 | 6 (1/4/1) | 2 | 2 (0/1/1/0) | 0 | 0 % |
| R2 `ir_to_arm` | 8 | 2 | 1 (1/0/0) | 5 | 4 (3/0/1/0) | 1 | 20 % |
| R3 direct selector | 8 | 0 | 2 (2/0/0) | 6 | 5 (3/1/0/1) | 1 | 17 % |
| R4 shared tail | 7 | 4 | 2 (1/0/1) | 1 | 0 (0/0/0/0) | 1 | 100 % |
| R5 startup | 7 | 0 | 0 (0/0/0) | 7 | 6 (0/6/0/0) | 1 | 14 % |

Read the small denominators as they are: R4's "100 %" is one byte-changing
mutant out of one (four of its seven draws were uncompilable — the operators
hit `liveness.rs` type patterns rustc rejects), and R1's routing predicates
mostly produced DEAD or EQUIVALENT mutants because the corpus never exercises
the VFP/exhaustion retry rungs (`vfp.is_ok()`, `grown.is_ok()`, the
"spilling the VFP register file" message match). R5 is the sharpest
per-region signal: every startup mutation changed bytes, six were caught, and
**all six only by the structural layer** — no execution oracle in this suite
boots the shipped `Reset_Handler`.

## The two UNRESOLVED mutants, declared

Both are byte-identical on the whole corpus and therefore already outside the
denominator; neither could be classified EQUIVALENT vs DEAD by the reach probe:

- `R4-shared/REG/liveness.rs:5038:45` — `const CALLEE_SAVED: [Reg; 5] =
  [R4, R5, R6, R7, R8]` → `[R4, R6, R6, R7, R8]`. A `const` has no runtime
  evaluation to probe (the marker print is not `const`). Bytes identical
  means the R5 entry never mattered to any of the 600 compiles — either the
  consumer never ran on this corpus or R5 was never a candidate there; the
  survey cannot say which.
- `R1-routing/BOUND/arm_backend.rs:1329:67` — the `<` inside the multi-line
  format string `"(validated; arbiter: {cand} B < shipping {base} B)"`. This
  is **not a decision site at all**: the enumerator's single-line quote check
  did not see the opening quote on the previous line. A diagnostic-text edit
  cannot change bytes; it is recorded so the sampling defect is visible, not
  hidden.

## Every survivor, classified

**(a) UNTESTED — reachable codegen no oracle in the suite exercises. The finding.**

| id | operator | diff | objects changed | what it is |
|---|---|---|---|---|
| `R2-ir_to_arm/DROPMOV/optimizer_bridge.rs:6705:0` | DROPMOV | `arm_instrs.push(ArmOp::Mov { rd: Reg::R1, … })` deleted | 8 | an `ir_to_arm` result/argument move in the optimized path's epilogue region; eight self-contained objects lose a `mov` and nothing executes them |
| `R3-direct/COND/select_with_stack.rs:6774:37` | COND | `I32Eq => Condition::EQ,` → `Condition::NE` | 2 | the direct selector's hand-written **`cmn` residual** compare table (negative-immediate compares fall out of the Rocq-proved `i32_cmp_rule`); PR #1216 predicted exactly this region as uncovered |
| `R4-shared/REG/liveness.rs:7025:36` | REG | `aapcs_dead_at_return = [R2, R3, R12, LR]` → `[R3, R3, R12, LR]` | 49 | R2 no longer treated as dead at return — a *conservative* change (more saves kept), so it is safe, but 49 objects moved and no oracle or golden noticed |
| `R5-startup/IMM/main.rs:9295:32` | IMM | `encode_thumb2_movw(2, data_copy_bytes …)` → register `3` | 46 | the ROM→RAM data-copy loop's byte-count register in `generate_minimal_startup`; every self-contained image with data segments changes and nothing in this suite boots one (`self_contained_data_758`, outside the subset, would) |

**(b) DEAD — never evaluated during the 600 corpus compiles. Deletion
candidates for the subtraction ratchet, not proofs of unreachability.**

> **v0.66 (RQ-66-DELETE): all four are REACHABLE** under hard-float and
> flag-on configurations the corpus never compiles — none was deleted. See
> § "v0.66 follow-up" below.

| id | diff | why unreached here |
|---|---|---|
| `R1-routing/BOUND/arm_backend.rs:1316:36` | `if literals > 0 {` → `>= 0` | inside the `SYNTH_PATH_DEBUG`-style arbiter reporting after realloc; no corpus function reaches that branch |
| `R1-routing/GUARD/arm_backend.rs:836:24` | `\|\| msg.contains("spilling the VFP register file")` negated | the VFP-spill retry rung; no corpus module exhausts the VFP file |
| `R1-routing/GUARD/arm_backend.rs:862:0` | `if grown.is_ok() {` negated | the frame-growth retry rung; never entered on this corpus |
| `R1-routing/GUARD/arm_backend.rs:808:0` | `if vfp.is_ok() {` negated | the VFP retry rung; never entered on this corpus |

**(c) EQUIVALENT — evaluated, byte-neutral on the whole corpus. Not a gap.**

| id | diff | why byte-neutral |
|---|---|---|
| `R1-routing/BOUND/arm_backend.rs:1565:21` | `if imm12 > 0xFFF {` → `>= 0xFFF` | the boundary value 0xFFF never occurs on the corpus |
| `R2-ir_to_arm/BOUND/optimizer_bridge.rs:6848:40` | `let deallocated = i > 0` → `>= 0` | a bookkeeping flag whose 0 case does not reach emission |
| `R3-direct/BOUND/select_with_stack.rs:1672:39` | `.filter(\|&u\| u >= 3 …)` → `> 3` | the reciprocal-mult candidate filter; `u == 3` never a candidate here |
| `R4-shared/REG/liveness.rs:1242:17` | `if rd != Reg::R12 {` → `!= Reg::R0` | a scratch-register exclusion in a pass whose R0/R12 cases coincide on the corpus |
| `R3-direct/BOUND/select_with_stack.rs:4450:38` | `if target_idx < block_labels.len() {` → `<=` | the guard's failing side never happens on well-formed input |

## Every kill, attributed

| id | operator | diff | objects changed | killed by |
|---|---|---|---|---|
| `R3-direct/GUARD/select_with_stack.rs:884:0` | GUARD | `if aeabi_route && is_aeabi_i64_f32_routed_op(op) {` negated | 425 | execution: `repro-sweep-arm-corpus-oracle` / #989 WAR-aliasing differential |
| `R3-direct/REG/select_with_stack.rs:188:45` | REG | `regs: vec![R4, R5, R6, …]` → `[R4, R5, R7, R7, …]` | 297 | execution: `repro-sweep-arm-corpus-oracle` / #989 |
| `R2-ir_to_arm/GUARD/optimizer_bridge.rs:3658:0` | GUARD | `if (*addr as usize) < num_params && (*addr as usize) < 4 {` negated | 47 | execution: `repro-sweep-arm-corpus-oracle` / #989 |
| `R2-ir_to_arm/GUARD/optimizer_bridge.rs:4108:0` | GUARD | `} else if (*addr as usize) >= num_params {` negated | 15 | execution: `repro-sweep-arm-corpus-oracle` / #989 |
| `R3-direct/GUARD/select_with_stack.rs:5979:0` | GUARD | `if self.native_pointer_abi {` negated | 9 | execution: `repro-sweep-arm-corpus-oracle` / ARM corpus sweep (#973) |
| `R2-ir_to_arm/DROPMOV/optimizer_bridge.rs:5652:0` | DROPMOV | `arm_instrs.push(ArmOp::Mov { … })` deleted | 4 | execution: `repro-sweep-arm-corpus-oracle` / #973 i64-cmp select differential |
| `R1-routing/GUARD/arm_backend.rs:1006:8` | GUARD | `\|\| has_br_table` negated (the routing gate) | 104 | structure: 17 tests across 9 binaries (`synth-backend` unit, `wast_compile`, `wcet_bound_gate`, `cabi_arena_bind_418`, `spill_on_exhaust_242`, `i64_pair_exhaust_587`, `volatile_segment_phase2_543`, the two CSE goldens) |
| `R3-direct/REG/select_with_stack.rs:2601:24` | REG | `Reg::R0` → `Reg::R1` | 53 | structure: `issue_95_const_addr_load::canonical_load_before_vs_after_byte_count` — one test |
| `R5-startup/BOUND/main.rs:9280:58` | BOUND | `if data_copy_bytes > 0 {` → `>= 0` | 279 | structure: `synth-cli` unit (`test_minimal_startup_generation`, `test_startup_code_patching`, `…_687`) + the two CSE goldens |
| `R5-startup/GUARD/main.rs:9359:0` | GUARD | `if !globals_words.is_empty() {` negated | 325 | structure: `synth-cli` unit + `arm_reloc_globalinit_refusal_1052` + the two CSE goldens |
| `R5-startup/GUARD/main.rs:9324:0` | GUARD | `if enable_fpu {` negated | 325 | structure: `synth-cli` unit + the two CSE goldens |
| `R5-startup/IMM/main.rs:9340:28` | IMM | `encode_thumb2_movw(11, linmem_base …)` → register 12 (the R11 seed) | 325 | structure: `synth-cli` unit + `base_cse_flip_468` |
| `R5-startup/IMM/main.rs:9365:32` | IMM | `encode_thumb2_movw(9, base …)` → register 10 (the R9 seed) | 80 | structure: `synth-cli` unit (`test_startup_globals_materializer_649`, `…_687`) |
| `R5-startup/IMM/main.rs:9369:36` | IMM | `encode_thumb2_movw(12, w …)` → register 0 | 80 | structure: `synth-cli` unit (`test_startup_globals_materializer_649`) — one test |
| `R2-ir_to_arm/IMM/optimizer_bridge.rs:6396:46` | IMM | `MemAddr::imm(Reg::R12, mem_off)` → `mem_off + 4` | 10 | **freeze-only**: `base_cse_flip_468` golden — nothing executed the changed objects |
| `R1-routing/REG/arm_backend.rs:1177:12` | REG | `Reg::R4,` → `Reg::R5,` (the realloc pool) | 188 | **freeze-only**: `const_cse_reduction_242` + `frozen_codegen_bytes` goldens |
| `R3-direct/BOUND/select_with_stack.rs:543:46` | BOUND | `if *last > start && *last < end {` → `<= end` | 3 (triage stopped at the first hang) | compiler hang: `synth compile` exceeded 60 s on `aarch64_brtable_blockvals_851.wat` (all three configurations) — every CI job would time out |

Two readings of this table matter more than the count. First, **the
execution kills all came from one job** (`repro-sweep-arm-corpus-oracle`,
mostly its #989 differential) — the corpus-sweep oracle is doing the work,
and `wast-conformance`, `cmp-select`, `frame-slot-dce` and `join-alias`
killed no sampled mutant (they did kill the controls they were chosen for).
Second, **the two freeze-only kills and control 3 are byte goldens doing an
oracle's job**: a change detector that is routinely re-pinned when bytes move
for a good reason. A re-pin of `base_cse_flip_468` without reasoning would
have let `optimizer_bridge.rs:6396` (a memory offset +4) through.

## What v0.66 gets scoped from

1. **The four UNTESTED sites, each with an oracle to add** — the `cmn`
   residual compare on the direct selector needs a negative-immediate
   compare fixture executed against wasmtime (PR #1216 named this gap; this
   survey confirms it with a mutant); the `ir_to_arm` epilogue `Mov` and the
   AAPCS dead-at-return set need the self-contained optimized-path objects
   EXECUTED, not just compiled (the corpus sweep runs `--relocatable` only);
   the startup data-copy register needs a booted self-contained image with
   data segments in the fast layer (`self_contained_data_758` already exists
   in `trap-semantics-oracle`; promote it or its shape).
2. **Boot the shipped `Reset_Handler` in an execution oracle.** All six R5
   kills and control 3 fell only to unit tests and byte goldens. The parity
   oracle boots it; it was excluded here for cost. A cheap "boot every
   self-contained corpus image and check R9/R10/R11 after reset" leg would
   convert the whole region from structure-caught to execution-caught.
3. **Re-survey with the parity oracle in the suite** (a `-j` leg, or a
   sub-corpus), and finish R2/R4 to the stated 8 per region. Expect the rate
   to fall — that is the direction the ratchet allows without a waiver.
4. **Four DEAD sites** are deletion candidates for the subtraction ratchet
   (`RQ-58-METRIC`): the VFP/frame-growth retry rungs in `arm_backend.rs`
   (808, 836, 862) and the literals arbiter branch (1316). DEAD here means
   "unreached on 200 corpus modules", so each needs a reachability argument
   or a fixture before deletion — the survey supplies the list, not the
   proof. **v0.66 supplied the argument and it went the other way: all four
   are reachable (§ "v0.66 follow-up" below).**
5. **Two freeze-only kills** (`optimizer_bridge.rs:6396`, `arm_backend.rs:1177`)
   are protected by goldens alone; the next re-pin of `base_cse_flip_468` or
   `const_cse_reduction_242` should be treated as a review event, not a
   chore.
6. **Harness defects found and fixed while surveying, for the record:** a
   "mentions `scripts/repro/`" job-selection rule admitted `coverage`
   (`cargo llvm-cov` of the whole workspace), `claim-check` and `rivet` —
   replaced by "invokes an oracle"; the corpus-compile timeout was 300 s with
   no short-circuit, so one hanging mutant cost >20 min and crashed the run
   — now 60 s and stop-at-first-hang; a killed run left a mutated file on
   disk — SIGTERM now unwinds the restore; cargo's `Running …/deps/` line
   shape was missed, so structural kills were attributed to `?` until
   re-attributed from the recorded test names.

## v0.66 follow-up — the four DEAD sites are reachable (RQ-66-DELETE, #242, #1238)

v0.66 set out to DELETE the four DEAD sites under the byte-identity gate. It
tried to reach them first, with this survey's own probe (`Edit(site, "probe")`
on the original token, `enumerate_sites()`, the same 203-module corpus, a
rebuilt `synth` per site, tree asserted clean after each), under the three
survey configurations AND five the corpus never compiles.
**Every one of the four DEAD sites is REACHED** — and under the survey's own
three `cortex-m4` configurations every probe stays silent, so the v0.65 verdict
reproduces exactly on its own terms:

| site (`arm_backend.rs`) | survey (`reloc` / `self` / `self-noopt`) | `m7dp-reloc` | `m7dp-self` | `m4f-reloc` | `SYNTH_GRAPH_ALLOC=1` reloc / self |
|---|---|---|---|---|---|
| `:808` `if vfp.is_ok() {` | 0 / 0 / 0 | **2** (`vfp_spill_881.wat`, `vfp_local_pressure_1069.wat`) | **2** (same) | **2** (same) | 0 / 0 |
| `:836` `\|\| msg.contains("spilling the VFP register file")` | 0 / 0 / 0 | **1** (`vfp_local_pressure_1069.wat`) | **1** | **1** | 0 / 0 |
| `:862` `if grown.is_ok() {` | 0 / 0 / 0 | **1** (`vfp_local_pressure_1069.wat`) | **1** | **1** | 0 / 0 |
| `:1316` `if literals > 0 {` | 0 / 0 / 0 | 0 | 0 | 0 | **171** / **108** of 203 |

**How each site is reached — re-runnable without mutating anything.** The
compiler's own stats lines name the rung / the arbiter on the unmutated binary:

```
# :808 (the plain #881 rung) — 7 functions take it on cortex-m7dp
SYNTH_RECOVERY_STATS=1 synth compile scripts/repro/vfp_spill_881.wat \
    --all-exports --relocatable --target cortex-m7dp -o /tmp/a.o
#   -> 1x rung=base result=ok, 7x rung=vfp-spill result=ok
# :836 and :862 (the #1069 frame-homed stage and its grown-pool retry)
SYNTH_RECOVERY_STATS=1 synth compile scripts/repro/vfp_local_pressure_1069.wat \
    --all-exports --relocatable --target cortex-m7dp -o /tmp/b.o
#   -> 1x rung=base result=ok (live13), 4x rung=vfp-frame-locals result=ok
#      (live14, live16, live24 = the grown-pool composition, live8d)
# :1316 (the graph-colouring arbiter's literal-pool sizing)
SYNTH_GRAPH_ALLOC=1 SYNTH_GRAPH_ALLOC_STATS=1 synth compile scripts/repro/const_cse.wat \
    --all-exports --relocatable --target cortex-m4 -o /tmp/e.o
#   -> "[graph-alloc] arbiter ..." lines; with the flag unset: no [graph-alloc] line at all
# the survey's own instrument, per site:
python3 scripts/mutation_survey.py reach --only R1-routing/GUARD/arm_backend.rs:808:0
```

**Why the survey called them DEAD — the mechanism, named.** Not a probe
defect and not circular: `evaluate` does NOT infer reach from byte-identity.
Byte-identity only decides WHETHER the reach probe runs; the probe itself
rebuilds the compiler with `{ eprintln!(MARK); token }` around the original
token and re-compiles the corpus — a real instrument, and the same one that
fired under the wide configurations above. The defect is the CONFIGURATION SET
the probe ran over. `CORPUS_CFGS` is three `--target cortex-m4` runs — no FPU —
and on that target the selector REFUSES every scalar float op BEFORE any
register pressure can arise: the same two fixtures compile to `8 of 8 functions
were skipped … GI-FPU-002: scalar f32 requires a…` and `5 of 5 … skipped`,
`rung=base result=exhausted`, "no functions compiled successfully". The VFP
retry ladder is therefore unreachable BY CONSTRUCTION under the survey, while
the fixtures written to exercise it sit in the corpus and are compiled by their
own CI oracles on `cortex-m7dp`. The fourth site sits behind
`graph_alloc::enabled()` = `SYNTH_GRAPH_ALLOC` set, and no corpus compile sets
any environment, although the `vcr_dec_001_graph_alloc_differential` job runs it
on every PR. The `"spilling the VFP register file"` term is not vestigial
either: `instruction_selector.rs` emits `"#881: spill-slot pool exhausted while
spilling the VFP register file"`, which lacks the `i64 ` prefix of
`SLOT_EXHAUSTION`, so that term is the only thing that catches it. So: "DEAD"
was an honest verdict for the frame this document states — and the frame
excluded exactly the two levers the code is gated on. The report then read
DEAD as a deletion list; that reading was the error.

**Blast radius on v0.65's published claims — stated plainly.** v0.65.0
published "4 DEAD (deletion candidates for the subtraction ratchet)" in three
places: the 0.65.0 CHANGELOG ("the DEAD four are deletion targets and give the
subtraction ratchet its first principled target list"), this document (§ (b)
"Deletion candidates", § "What v0.66 gets scoped from" item 4) and the
RQ-65-MUTANTS artifact ("(b) DEAD — unreachable, which is a DELETION target").
**That statement is false, 4 of 4.** Every one of the four sites is reachable
and none is a deletion candidate. The ledger records carry the correction
beside the original verdict (`reach_wide`, `reach_wide_at`, `reach_note`,
`published_as`); the v0.65 text itself is left as shipped — how the correction
is published is a release decision, recorded in #1238.

**Is DEAD salvageable as a category? Yes — and the rule is now in the
harness.** The probe is real, so DEAD is measurable; what it lacked was a
stated configuration set. From this release `classify_identical` assigns DEAD
only when a byte-identical mutant is unreached under `CORPUS_CFGS` AND under
every `REACH_CFGS` configuration (`evaluate` now always runs the wide probe,
~15 s per byte-identical mutant); reached ONLY under `REACH_CFGS` is
UNRESOLVED with a note — the byte triage was not run under those
configurations, so it is neither DEAD nor EQUIVALENT — and never DEAD. Two
residuals, recorded rather than closed: the byte-triage baseline is still
`CORPUS_CFGS`-only, so folding `REACH_CFGS` into the baseline (a re-survey,
item 3) is what makes a future DEAD a sound candidate; and `REACH_CFGS` is a
hand-listed set — the honest version is DERIVED from the levers the code
generator reads (`std::env::var` gates and the FPU target variants), the same
"derive what you check against" rule the rest of this repository runs on.
Until both land, a DEAD verdict reads "unreached under `CORPUS_CFGS` +
`REACH_CFGS` as listed at that commit" and still needs a reachability argument
before deletion.

**Nothing was deleted, and the ratchet did not move.** `selector_lines_code`
stays at 19,896 with no waiver — and it could not have moved: it counts
`instruction_selector.rs` + `instruction_selector/**`, and all four sites are in
`arm_backend.rs`. Four of this survey's five regions (R1 routing, R2
`optimizer_bridge.rs`, R4 shared tail, R5 startup) lie outside that population;
only R3 (`select_with_stack.rs`) is inside it. A DEAD site from the other four
regions can never move the ratchet even if deleted.

**What now guards this.** `mutation_survey.py reach [--write]` re-probes DEAD
sites under `REACH_CFGS` (`m7dp-reloc`, `m7dp-self`, `graph-alloc-reloc`,
`graph-alloc-self`) and records the reaching modules per configuration on the
ledger record (`reach_wide`, `reach_wide_at`, `reach_note`); `pin-subset` pins the first four
witnesses per configuration as `want_reach_wide`, and `ci` requires every
witness to keep reaching (subset semantics — reach may widen without a ledger
edit; a witness going silent is red, whether the code became unreachable, was
deleted, or the probe went blind). The replay prints `MUTANTS-REACH-WIDE
entries=4 reached=4 unreached=0`, grepped by the `mutation-survey-discrimination`
job. The decision function is pure and unit-tested from both sides
(`scripts/test_mutation_survey.py`, 12 tests). The four records keep
`classification: DEAD` as v0.65 recorded it — the publication decision is the
coordinator's — with the contradicting evidence and `published_as` beside it;
under the new rule the same measurement classifies UNRESOLVED (the `ci` replay
prints `expect DEAD -> UNRESOLVED wide=…` for them, which is the instrument
saying so), and any DEAD verdict from now on reads "unreached under
`CORPUS_CFGS` + `REACH_CFGS`" and still needs a reachability argument before
deletion. `REACH_CFGS` is deliberately NOT folded into `CORPUS_CFGS`: every
baseline hash and `changed` set in the ledger is relative to `CORPUS_CFGS`, and
widening that is a re-survey (item 3 above), not a patch.

## Re-running and the CI pin

- Full survey: `baseline --jobs <named subset>` → `l2` → `controls` → `run
  --seed 1189 --per-region 8` → `report`. The ledger is resumable; each
  mutant restores the tree (asserted with `git diff --quiet` after every
  edit).
- CI (`mutation-survey-discrimination` job): `mutation_survey.py ci` replays
  the ledger's `ci_subset` — the three controls (their recorded killer step
  must go red again) and known SURVIVED / EQUIVALENT / DEAD mutants (their
  recorded byte-triage set and reach verdict must reproduce exactly). It
  fails on any disagreement in either direction and on a subset smaller than
  two per side. It re-runs no survey and declares no new emulation floor.
- `claims.yaml`: the UNTESTED count is a `direction: down` ratchet over the
  ledger (a survivor that becomes caught must be banked as a visible diff);
  the sample and byte-changing denominators are pinned `count-eq` so the rate
  quoted here cannot drift from the ledger.

## Ledger drift after RQ-65-MVPCORE (#1232) and RQ-65-ALIASCLASS (#1227)

Both landed between this survey being measured and this PR merging. Measured on
the merged tree, not assumed:

| | |
|---|---|
| mutation sites enumerated | 1,542 |
| `ci_subset` entries that still resolve | **7 of 7** |
| sites whose line anchor moved | 15 — **all relocated by `reanchor`, 0 not found** |
| baseline corpus entries that drifted | **13 of 609** |

**Anchors: repaired mechanically.** `mutation_survey.py reanchor` re-locates every
recorded site by its stored `before` TEXT rather than its line number, so a
refactor that moves code does not orphan the ledger. It reported 15 moved, 0 not
found. Structural definitions survive refactors that line numbers do not — the
three controls come from `control_sites()` and never moved at all.

**One measurement genuinely changed, and it is recorded rather than papered over.**
`R4-shared/REG/liveness.rs:7025:36` perturbs **53** corpus modules on the merged
tree where it perturbed 49 when surveyed. The site did not move; the BASELINE did
(13 of 609 entries), so the mutation's blast radius moved with it. Re-derived by
byte triage on the merged tree — CI and a local run agree at 53 independently.

**What is NOT re-verified, stated plainly.** That mutant's CLASSIFICATION
(`UNTESTED`) was measured at `meta.commit` and has not been re-established on the
merged tree. The CI replay checks byte triage for `UNTESTED` entries, not the
oracle suite (that needs `--full`), so nothing here asserts it. The published rate
remains relative to the commit this ledger names — a survival rate is a property
of a tree, not of a project.

**A local re-survey was attempted and DISCARDED as invalid.** Two independent
environmental faults made this machine unable to run the oracle suite: 147 of the
196 L1 steps invoke bare `python`, which is absent here (exit 127 in 0.1 s, which
the harness scores as a KILL), and `fact_spec_div_494_differential.py` is red on
the UNMUTATED tree locally while green in CI. The run reported 0 of 29 surviving —
an artifact of dead oracles, not a result. Its own control check caught it:
`1 control(s) not killed — the survey measures nothing; do not publish the rate`.
That refusal is the harness working exactly as intended, and it is the reason a
fabricated 0 % is not in this document.

## v0.66 follow-up — probe before scoring, lock the sampling frame (RQ-66-POTENCY, #1189)

The near-miss above was caught by luck, not judgement — the control check
requires each control to die to its OWN recorded oracle, and one of the three
controls' recorded oracle happened to be among the 49 steps that could still
run, so it alone surfaced `1 control(s) not killed`. Nothing checked that the
other 147 steps ever executed; they simply never killed anything, so nothing
noticed that all 147 had scored every mutant that reached them anyway. This
release makes that non-vacuity a property of the harness rather than a
property of which control's oracle happens to survive.

**`classify_unrunnable(code, out)`** (pure) is the decision that gates every
step before it can be scored: exit 127/126, a `command not found` line, a
`ModuleNotFoundError`, or an `env` shebang failing to find its interpreter
mean the step never EXECUTED — UNRUNNABLE. Everything else (a real assertion
failure, a script's own deliberate `FileNotFoundError` on a missing fixture,
a generic application-level `ImportError`) means the step ran and is a
different thing: real evidence about the tree, not about the environment.
`fact_spec_div_494_differential.py`'s local/CI divergence, named above, is
exactly this second case and must never be classified UNRUNNABLE — doing so
would refuse the survey into never running anywhere the environment differs
even slightly from CI, which is the opposite failure.

**`preflight_suite`** runs every L1 and L2 step once on the unmutated tree
before `run`, `controls`, or `ci` touch a single mutant, and:

- REFUSES (`sys.exit`, no ledger written) when anything is UNRUNNABLE, or
  when any L2 (`cargo test`) command is red for any reason (a broken test
  suite is not survivable by excluding the broken part).
- EXCLUDES (does not score) an L1 step that executes and is merely red on
  this tree — recorded in the ledger as `suite.l1_excluded_at_preflight` —
  the same thing `baseline` has always done, now also applied when a
  possibly stale or foreign `suite` (baselined elsewhere, or a while ago) is
  reused without re-baselining. That reuse path is exactly the shape of the
  incident above: a suite derived once (in CI, where `python` exists) and
  replayed later somewhere it does not.

`cmd_ci` does NOT get the full preflight when replaying without `--full` —
its own module doc is explicit that `ci` is "the harness's DISCRIMINATION,
not a re-run of the survey", so paying a full-suite probe on every CI
invocation would contradict that design. Instead it probes only the L1 steps
the pinned subset's recorded KILLED-type entries actually depend on (a
handful, not 198), and refuses on EITHER unrunnable or red there — a
replayed KILLED verdict is meaningless if the killer step is not green
before the mutation is even applied.

**Second-order: `draw_frame` locks the sampling frame.** `cmd_run` used to
overwrite `ledger["meta"]` unconditionally with its own argparse defaults on
every invocation — the mechanism behind the `per_region: 12`-for-8 drift
recorded in `meta.per_region_note` above. `draw_frame(existing_meta, seed,
per_region, oversample)` (pure) writes the frame once; a later `run` must
reproduce the same three numbers or it refuses, showing both the recorded and
requested values, rather than silently rewriting the record of how the sample
was drawn. `candidate_sites` is deliberately NOT part of the locked
comparison — it is live tree-state context that legitimately drifts as the
codebase changes (see "Ledger drift" above) and is refreshed every run.

**Verified red-first, for real:**

```
$ python3 scripts/mutation_survey.py run --seed 1189 --per-region 12 --oversample 4 \
    --ledger /tmp/ledger-with-per_region-8-already-recorded.json
refusing to run: this ledger's sampling frame is recorded as {'seed': 1189,
'per_region': 8, 'oversample': 4}, but this invocation asked for {'seed': 1189,
'per_region': 12, 'oversample': 4}. Re-running `run` against an existing ledger
must not silently rewrite the frame (#1189 — v0.65 shipped per_region:12 this
way for a sample drawn at 8) — pass the SAME --seed/--per-region/--oversample
as the recorded draw, or use a fresh --ledger for a genuinely different frame.
```

The ledger file's checksum was byte-identical before and after that refusal.
A synthetic suite containing one genuinely-missing binary alongside real
repro scripts (`cmp_select_two_move_differential.py`, run through the
harness's existing bare-`python`→`python3` substitution) REFUSED naming the
missing binary while the real scripts ran and passed in the same probe pass;
a suite with only the real scripts proceeded. `python3
scripts/test_mutation_survey.py`: 30/30, 12 new — `classify_unrunnable` on
both directions (including a live example pulled from that week's own CI: a
`home-alias-audit-oracle` step whose own oracle printed `RESULT: PASS` but
whose step exit was 1 because of a stale `grep -Eq` count assertion further
down the same step — correctly "ran, not unrunnable", the same class as
`fact_spec_div_494_differential.py` from the other direction) and
`draw_frame` on both directions.

