# CLAUDE.md — Synth Project Context

## What This Is

Synth is a WebAssembly-to-ARM Cortex-M compiler with mechanized correctness proofs in Rocq (formerly Coq). It produces bare-metal ELF binaries for embedded targets.

Part of [PulseEngine](https://github.com/pulseengine): synth (compiler) + [loom](https://github.com/pulseengine/loom) (WASM optimizer) + [meld](https://github.com/pulseengine/meld) (platform).

## Build Commands

```bash
# Rust — primary build
cargo test --workspace             # 885+ tests
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
| `synth-backend` | ARM Thumb-2 encoder, ELF builder, vector table, linker scripts, MPU |
| `synth-backend-awsm` | aWsm backend integration (WASM→native via aWsm) |
| `synth-backend-wasker` | Wasker backend integration (WASM→Rust transpiler) |
| `synth-synthesis` | WASM→ARM instruction selection, peephole optimizer, pattern matcher |
| `synth-cfg` | Control flow graph construction and analysis |
| `synth-opt` | IR-level optimization passes (CSE, constant folding, DCE) |
| `synth-verify` | Z3 SMT translation validation |
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

See `coq/STATUS.md` for the complete coverage matrix. Current: 188 Qed / 52 Admitted.
Proofs are tiered: T1 (39 result-correspondence), T2 (95 existence-only), T3 (52 admitted).
All 52 admits require VFP/float semantics (48) or are low-priority infrastructure (4).
All i32 operations (arithmetic, division, comparison, bit-manip, shift/rotate) have T1 proofs.

## Conventions

- Rust edition 2024, MSRV 1.88
- Edition 2024 notes: `unsafe fn` bodies require explicit inner `unsafe {}` blocks; `#[no_mangle]` must be `#[unsafe(no_mangle)]`; `static mut` access via `&raw const`/`&raw mut`
- Bazel 8.x with bzlmod (`MODULE.bazel`, not `WORKSPACE`)
- Renode tests use `rules_renode` (PulseEngine fork with macOS support)
- All `.v` files use `-Q Synth Synth` logical mapping (see `coq/_CoqProject`)
