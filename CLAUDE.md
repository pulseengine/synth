# CLAUDE.md — Synth Project Context

## What This Is

Synth is a WebAssembly-to-ARM Cortex-M (Thumb-2), Cortex-R5 (A32), RISC-V (RV32IMAC), and AArch64 (host-native, integer subset) compiler with mechanized correctness proofs in Rocq (formerly Coq). It produces bare-metal ELF binaries for embedded targets.

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
| `synth-backend-aarch64` | AArch64 (A64) host-native backend — integer subset, `-b aarch64` |
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

See `coq/STATUS.md` for the complete coverage matrix. Current: 591 Qed / 3 Admitted
(+2 `admit.` tactics) across `coq/Synth/`. The 50 selector-DSL rule theorems
(`VcrSelRules.v`) are stated directly about the GENERATED model (VCR-ISA-001
#667: `rule_X := Gen.rule_X`, single source `VcrSelRulesGenerated.v` emitted
from the shipped `sel_dsl::RULES`); the former 40-lemma `VcrSelRulesGenCheck.v`
reflexivity gate was retired as vacuous once the hand-written mirror was gone
(512 → 472). This count is CI-gated: `claims.yaml` +
`scripts/claim_check.py` re-derive it on every commit — when a proof lands, update
the docs AND `claims.yaml` in the same PR. Proofs are tiered:
T1 (result-correspondence), T2 (existence-only), T3 (admitted). Remaining admits:
1 CorrectnessSimple.v, 2 ArmRefinement.v — 0 division admits
(all four i32 div/rem trap guards discharged against `exec_program_br`, #73)
and 0 i64 admits. (#166: the 2 Compilation.v example admits were discharged
via `vm_compute`; the CorrectnessSimple.v `i32_const_correct` residual is a
documented T3 — the MOVW+MOVT reconstruction arithmetic is now proven
(`movw_movt_reconstruct_Z`, `i32_const_large_reconstruct`), the residual is the
un-normalized-`Z` WASM-constant representation gap; the 2 ArmRefinement.v admits
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
ever-growing pile of locally-correct patches.** The recurring greedy fixes
(reciprocal-mult cost-gate, register-exhaustion hard-fail, the "selector missed
an op" class #223/#226/#232) are symptoms of two single-pass hand-written
components: the instruction selector and the register allocator. Filed as the
phased, parallelizable **VCR-\*** rivet program (epic #242,
`artifacts/verified-codegen-roadmap.yaml`), built incrementally — behavior
frozen and oracle-gated every step:

- **Track A (core):** `VCR-RA-001` allocator with Belady spilling — **verified,
  default-on since v0.24.0** (`SYNTH_SPILL_REALLOC`; `SYNTH_SPILL_ON_EXHAUST`
  built flag-off, silicon-gated #580). Next: `VCR-SEL-001` Rocq-discharged
  verified selector DSL (increments 1–4 shipped **default-on**, 50 rules / 50 Qed,
  `SYNTH_SEL_DSL`; the Rocq-proved rules are the SHIPPED lowering path for their
  50 covered ops, opt-out `SYNTH_NO_SEL_DSL=1`, byte-invisible flip) and
  `VCR-PERF-002` proof-carrying specialization (#494,
  0.45× floor; phase 1 facts ingestion landed, PR #624).
- **Track B (semantics):** `VCR-ISA-001` Sail-generated Rocq ISA model —
  approved, Sail/ASL bridge spike landed (92 Qed, `coq/Synth/ARM/SailArmBridge.v`);
  "generate, don't mirror" landed (#667): the shipped `sel_dsl::RULES` table
  EMITS the 50 covered ops' Rocq lowerings
  (`coq/Synth/Synth/VcrSelRulesGenerated.v`, `Module Gen`), and `VcrSelRules.v`
  DEFINES `rule_X := Gen.rule_X` — the generated file is the single model
  source, the 50 correctness Qed are stated directly about it, and a
  selector-table change regenerates `Gen` and breaks the matching proof, so the
  #682 model↔selector drift is unrepresentable at the instruction-sequence level
  for those ops (the interim `VcrSelRulesGenCheck.v` reflexivity gate was
  retired as vacuous/subsumed). `VCR-WASM-001` WasmCert-Coq source semantics —
  phases 1+2 landed: the i32 integer fragment (19 ops) transcribed from the
  pinned coq9.0-wasm-2.2.0 sources with line-level provenance and proven
  refined by `exec_wasm_instr` (49 Qed, `coq/Synth/WASM/WasmCertBridge.v`);
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
  differential + a full-boot unicorn oracle gate it); AArch64 is N/A (no
  linear-memory ops in the integer subset).
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
  entry-independent). Richer recursion certificates (clamp-bounded controlling
  values, data-dependent depths, scry) are a named follow-up.
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

## Conventions

- Rust edition 2024, MSRV 1.88
- Edition 2024 notes: `unsafe fn` bodies require explicit inner `unsafe {}` blocks; `#[no_mangle]` must be `#[unsafe(no_mangle)]`; `static mut` access via `&raw const`/`&raw mut`
- Bazel 8.x with bzlmod (`MODULE.bazel`, not `WORKSPACE`)
- Renode tests use `rules_renode` (PulseEngine fork with macOS support)
- All `.v` files use `-Q Synth Synth` logical mapping (see `coq/_CoqProject`)
