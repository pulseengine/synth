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

See `coq/STATUS.md` for the complete coverage matrix. Current: 298 Qed / 9 Admitted
(+2 `admit.` tactics) across `coq/Synth/` — STATUS.md's 291 headline recount predates
the 7 Qed VCR-SEL-001 pilot lemmas in `Synth/VcrSelPilot.v` (#386). Proofs are tiered:
T1 (result-correspondence), T2 (existence-only), T3 (admitted). Remaining admits:
4 i32 division trap guards (exec_program model gap, #73), 2 Compilation.v,
1 CorrectnessSimple.v, 2 ArmRefinement.v — 0 i64 admits.
All i32 AND i64 operations have T1 proofs (i64 T1 parity since v0.11.0).

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
  verified selector DSL (increment 1 in review, PR #623, `SYNTH_SEL_DSL`) and
  `VCR-PERF-002` proof-carrying specialization (#494, 0.45× floor; phase 1 in
  review, PR #624).
- **Track B (semantics):** `VCR-ISA-001` Sail-generated Rocq ISA model;
  `VCR-WASM-001` WasmCert-Coq source semantics — both still proposed.
- **Track C (validation):** the differential oracles are CI-gated jobs
  (cmp-select, RV32 shift-fold/const-addr-fold, callee-saved, spill-frame,
  symtab-based frozen-fixture differentials).
- **Gate `VCR-VER-001`:** a previously load-bearing greedy-fix becomes
  revertable, full differential bit-identical, cycles equal-or-better.

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
