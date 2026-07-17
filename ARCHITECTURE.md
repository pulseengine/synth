# Synth Architecture

Architectural overview of the Synth WASM-to-native compiler for embedded
systems. Every claim in this document is checked against the tree —
load-bearing statements are pinned in `claims.yaml` (CI job `claim-check`),
and anything numeric lives in the machine-derived
[`artifacts/status.json`](artifacts/status.json), not in prose.

## Table of Contents
1. [Overview](#overview)
2. [System Architecture](#system-architecture)
3. [Compilation Pipeline](#compilation-pipeline)
4. [Core Components](#core-components)
5. [Code Generation](#code-generation)
6. [Optimization](#optimization)
7. [Binary Emission](#binary-emission)
8. [Verification Architecture](#verification-architecture)
9. [Testing](#testing)
10. [Supported Targets](#supported-targets)

## Overview

Synth is an ahead-of-time compiler from WebAssembly to bare-metal native code.
It carries **four backends**:

| Backend | Crate | ISA | Primary targets |
|---------|-------|-----|-----------------|
| ARM Cortex-M (primary) | `synth-backend` | Thumb-2 | cortex-m3/m4/m4f/m7/m7dp (+ m55 experimental MVE) |
| ARM Cortex-R | `synth-backend` | A32 | cortex-r5 |
| RISC-V | `synth-backend-riscv` | RV32IMAC | qemu_riscv32, ESP32-C3 |
| AArch64 (host-native) | `synth-backend-aarch64` | A64 | cortex-a53 (host-linkable ET_REL) |

**Key properties:**

- Direct WASM → native code generation (no C or LLVM intermediary)
- Hardware acceleration where the target has it (SDIV/UDIV, CLZ, RBIT)
- Mechanized Rocq correctness proofs on the integer instruction selection,
  plus per-compilation validators (translation validation, trap preservation,
  static-data addressing) — see [Verification Architecture](#verification-architecture)
- Complete firmware image generation: vector table, reset handler, linker
  scripts, MPU configuration
- Sound static WCET bounds (`--emit-wcet`)
- The honesty rule: a construct without a lowering **declines loudly** with a
  machine reason — never silent wrong code

### Synth and Loom

Synth works alongside [Loom](https://github.com/pulseengine/loom), the
PulseEngine WebAssembly optimizer: Loom transforms WASM → optimized WASM
(Z3-validated); Synth transforms WASM → native ELF (Rocq proofs +
per-compilation validators). Synth can consume Loom-optimized modules and,
with `SYNTH_FACT_SPEC`, use Loom's exported `wsc.facts` invariants as premises
for certificate-checked specializations. See
[SYNTH_LOOM_RELATIONSHIP.md](docs/architecture/SYNTH_LOOM_RELATIONSHIP.md).

## System Architecture

```
                 ┌──────────────────────────────────────────────┐
                 │                synth-cli                      │
                 │  compile · verify · disasm · parse · backends │
                 └──────────────────────┬───────────────────────┘
                                        │
   ┌────────────────────────────────────┼─────────────────────────────┐
   │ synth-core: WasmOp, decoder, Backend trait, target specs,        │
   │             static-data addressing validator (VCR-VER-003)       │
   └────────────────────────────────────┬─────────────────────────────┘
                                        │
        ┌──────────────┬────────────────┼──────────────────┐
        ▼              ▼                ▼                  ▼
 ┌─────────────┐ ┌──────────────┐ ┌───────────────┐ ┌──────────────────┐
 │synth-backend│ │synth-backend-│ │synth-backend- │ │ integration      │
 │ Thumb-2+A32 │ │riscv RV32IMAC│ │aarch64 A64    │ │ backends (aWsm,  │
 │ ELF, vector │ │ relocatable  │ │ host-linkable │ │ wasker) — stubs  │
 │ table, MPU, │ │ ELF          │ │ ET_REL        │ └──────────────────┘
 │ WCET        │ └──────────────┘ └───────────────┘
 └──────┬──────┘
        │ uses
        ▼
 ┌──────────────────────────────────────────────┐
 │ synth-synthesis: instruction selection        │
 │ (verified selector DSL + direct selector),    │
 │ liveness/Belady allocation, peephole          │
 └──────────────────────────────────────────────┘
        │ validated by
        ▼
 ┌──────────────────────────────────────────────┐
 │ synth-verify: ordeal QF_BV translation        │
 │ validation (Z3 = differential oracle),        │
 │ trap-preservation VC, fact-spec certificates  │
 └──────────────────────────────────────────────┘
```

## Compilation Pipeline

### Phase 1: Parsing & Analysis
```
Input: WASM Module (.wasm or .wat)
  │
  ├─▶ Parse via wasmparser/wat
  ├─▶ Decode to WasmOp (synth-core) — undecodable ops mark the function
  │   for a LOUD skip (#369/#554 gate class), never a silent drop
  ├─▶ Extract signatures, locals, memory/table/global sections
  └─▶ Module-level gates (e.g. multi-memory declines with a machine reason)
```

### Phase 2: Instruction Selection

Two selector paths exist in `synth-synthesis` (they have different ABIs —
`--relocatable` forces the full-featured one):

- **`select_with_stack`** — the real compiler: value-stack tracking, control
  flow, locals/globals, calls, memory; used for relocatable output and all
  multi-function/self-contained compilation.
- **`select_default`** — the minimal demo path for trivial single-function
  modules.

Within `select_with_stack`, ops covered by the **verified selector DSL**
(`sel_dsl`, VCR-SEL-001) lower through Rocq-proved rules — the shipped rule
table *generates* the Rocq model (`VcrSelRulesGenerated.v`, #667), so a rule
change breaks its matching proof. Remaining ops use the hand-written arms.

```
WASM Operations
  │
  ├─▶ Verified DSL rules (covered ops) / direct selection (rest)
  │
  ├─▶ Register Allocation
  │   ├─ Allocatable pool: R0–R8
  │   ├─ Reserved: R9 (globals base), R10 (memory size), R11 (memory base,
  │   │  base-CSE), R12 (encoder scratch — never allocated), SP/LR/PC
  │   ├─ Liveness-based Belady spilling (VCR-RA-001, verified, default-on)
  │   └─ i32 local promotion into callee-saved R4–R8 (leaf-aware)
  │
  └─▶ ARM Instruction Stream
```

### Phase 3: Optimization
```
ARM Instructions (unoptimized)
  │
  ├─▶ Peephole + shipped lever ladder (see Optimization below)
  │
  └─▶ ARM Instructions (optimized)
```

### Phase 4: Code Generation
```
Optimized ARM Instructions
  │
  ├─▶ Encoding
  │   ├─ Thumb-2 (Cortex-M, primary) — 16/32-bit mixed; high-register
  │   │  operands force wide forms (encoder is Ok-or-Err, never corrupting)
  │   ├─ A32 (Cortex-R5)
  │   └─ Branch target resolution over real encoded byte layout
  │
  ├─▶ Per-compilation validators (see Verification Architecture)
  │
  ├─▶ Startup Code Generation (self-contained --cortex-m)
  │   ├─ Vector table
  │   ├─ Reset handler (.data copy, .bss zero)
  │   └─ Funcref table in flash for call_indirect (PC-relative dispatch)
  │
  └─▶ Binary Emission
      ├─ ELF32 executable image, or ET_REL relocatable object
      ├─ Section placement + symbol table
      └─ Optional: DWARF line info, WCET sidecar (--emit-wcet)
```

## Core Components

### 1. Synthesis Engine (`synth-synthesis`)

**Modules** (as in the tree):
- `instruction_selector.rs` — WASM → ARM selection, both selector paths
- `sel_dsl/` — the verified selector DSL rule table (emits the Rocq model)
- `rules.rs`, `pattern_matcher.rs` — rule database and pattern matching
- `liveness.rs` — liveness analysis backing Belady spilling
- `peephole.rs` — local optimization passes
- `optimizer_bridge.rs` — wires selection into the pipeline
- `control_flow.rs`, `parallel_move.rs`, `contracts.rs` (Verus specs)

**Example** (real APIs, spot-checked against the tree):
```rust
let db = RuleDatabase::with_standard_rules();
let optimizer = PeepholeOptimizer::new();
let (optimized, stats) = optimizer.optimize_with_stats(&arm_instrs);
let encoder = ArmEncoder::new_arm32();      // A32; Thumb-2 has its own path
let elf = ElfBuilder::new_arm32();
```

### 2. ARM Backend (`synth-backend`)

- `arm_encoder.rs` — A32 + Thumb-2 instruction encoding
- `elf_builder.rs` — ELF generation (executable + relocatable)
- `vector_table.rs`, `reset_handler.rs`, `arm_startup.rs` — Cortex-M startup
- `linker_script.rs` — linker script generation (STM32, nRF52840, generic)
- `memory_layout.rs`, `mpu.rs`, `mpu_allocator.rs` — memory analysis + MPU
- `wcet.rs`, `wcet_loops.rs` — sound worst-case cycle model + proven loop
  bounds (sound-critical constants pinned in `claims.yaml`)

### 3. Other backends

- `synth-backend-riscv` — RV32IMAC selector/encoder/relocatable ELF, PMP
  support, own linker scripts and startup
- `synth-backend-aarch64` — A64 encoder (clang-cross-verified), EM_AARCH64
  ELF64 emitter; straight-line integer + scalar-float subset (see the
  [Feature Matrix](docs/status/FEATURE_MATRIX.md))
- `synth-backend-awsm`, `synth-backend-wasker` — external-toolchain
  integration stubs

### 4. Core (`synth-core`)

Shared types (`WasmOp`), the WASM decoder with the loud-skip contract, the
`Backend` trait + registry, target specs, and the static-data addressing
validator that runs on every compilation.

## Code Generation

### WASM to ARM Mapping (representative)

Per-op worst-case cycle accounting lives in the sound WCET model
(`synth-backend/src/wcet.rs`), not in this table.

| WASM Operation | ARM Instruction | Notes |
|----------------|-----------------|-------|
| `i32.add` | `ADD Rd, Rn, Rm` | |
| `i32.div_s` | `SDIV Rd, Rn, Rm` | preceded by WASM trap guards (div-by-zero, overflow) |
| `i32.shl` | `LSL` | immediate-shift folding when the amount is const |
| `i32.rotl` | `ROR Rd, Rn, #(32-n)` | |
| `i32.ctz` | `RBIT + CLZ` | |
| `i32.load` | `LDR Rd, [Rn, #offset]` | R11-based linear-memory addressing; const addresses fold to `[R11, #imm]` |
| `local.get` | register or `LDR [SP, #offset]` | i32 locals promote to R4–R8 in eligible functions |
| `select` | `CMP` + IT/`CSEL`-style predication | cmp→select fusion default-on |

### Instruction Encoding

Thumb-2 is the primary Cortex-M encoding (16/32-bit mixed); A32 is used for
Cortex-R5. Illustrative A32 data-processing encodings (as in
`arm_encoder.rs`):

```rust
// ADD (A32): 0xE0800000 | (Rn << 16) | (Rd << 12) | Rm
// SDIV (A32): 0xE710F010 | (Rd << 16) | (Rm << 8) | Rn
```

The Thumb-2 encoder refuses (returns `Err`) rather than emit a 16-bit form
with a high register — the #180/#185 corruption class is structurally gated.

## Optimization

### Peephole patterns

1. Redundant-operation elimination (`MOV R0, R0` → removed)
2. NOP removal
3. Instruction fusion (shift-into-operand, `ADD R0, R2, R1, LSL #2`)
4. Constant propagation/folding

### Shipped optimization levers

All default-on, each evidence-gated with a CI-pinned opt-out (see the README
North-Star section for the history):

- Liveness-based Belady spill/realloc (VCR-RA-001, `verified`)
- cmp→select fusion (ARM + RV32)
- i32 local promotion into callee-saved registers
- Immediate-shift folding (ARM + RV32)
- Linear-memory base-CSE into R11 + const-address folding
- Constant-CSE, dead-frame elimination, uxth-fold
- Frame-slot DCE (dead-store elimination + control-flow-transparent reload
  forwarding)

## Binary Emission

### ELF File Structure (self-contained `--cortex-m`)

```
ELF Header (ELF32, little-endian, EM_ARM)
Program Headers
├─ LOAD: .isr_vector + .text (FLASH)
└─ LOAD: .data + .bss (RAM)
Section Headers
├─ .isr_vector — vector table (initial SP, Reset_Handler, exception vectors)
├─ .text — reset handler + compiled functions (+ flash funcref table when
│          the module uses call_indirect)
├─ .rodata / .data / .bss
├─ .symtab / .strtab / .shstrtab (function symbols carry the Thumb bit)
└─ optional .rel.* / .debug_* (relocatable + DWARF paths)
```

`--relocatable` (or any module with imports) emits an ET_REL object with
`R_ARM_THM_CALL` relocations and `func_N` symbols for linking against a
runtime (e.g. Kiln).

### Memory Layout (defaults — configurable via linker scripts)

Flash at `0x08000000` (vector table first, code after), RAM at `0x20000000`
(.data, .bss, heap, stack; initial SP at the RAM top). The concrete values
are produced by `memory_layout.rs` + the generated linker scripts — consult
those, not this document, for exact addresses.

## Verification Architecture

Three layers, complementary by design:

1. **Mechanized proofs (Rocq)** — `coq/Synth/`: per-op correctness theorems
   over the compilation model; the verified selector DSL's rules are proven
   against a model *generated from the shipped rule table*. Counts:
   [`artifacts/status.json`](artifacts/status.json) /
   [coq/STATUS.md](coq/STATUS.md).
2. **Per-compilation validators** — run on every build, not once:
   translation validation (ordeal, pure-Rust QF_BV; Z3 as feature-gated
   differential oracle), trap-preservation VC (dropped-trap classes),
   static-data addressing VC (byte-equality of served vs runtime image),
   and the sound WCET bound with statically-proven loop trips.
3. **Differential oracles (CI)** — frozen-fixture byte differentials
   (symtab-based, host-independent), execution differentials vs wasmtime
   under unicorn/QEMU/Renode, and fixture-scoped silicon gates (gale).

## Testing

- `cargo test --workspace` — unit + integration suites
- `bazel test //coq:verify_proofs` — the full Rocq proof suite (hermetic, Nix)
- `bazel test //tests/...` — Renode ARM Cortex-M4 emulation tests
- `scripts/repro/` — execution/byte differentials, CI-gated
- Silicon: fixture-scoped cycle + correctness gates on NUCLEO-G474RE /
  STM32F100 via the gale loop — there is **no broad board matrix yet**

Test/proof counts are deliberately not written here — they are machine-derived
into [`artifacts/status.json`](artifacts/status.json) and rendered into the
generated [Feature Matrix](docs/status/FEATURE_MATRIX.md).

## Supported Targets

| Family | Profiles | Notes |
|--------|----------|-------|
| ARM Cortex-M (Thumb-2) | `cortex-m3`, `cortex-m4`, `cortex-m4f`, `cortex-m7`, `cortex-m7dp` | f32/f64 VFP requires an FPU profile (`-f`/`dp` suffixes) |
| ARM Cortex-M55 | `cortex-m55` | experimental Helium/MVE encoding — untested on silicon |
| ARM Cortex-R (A32) | `cortex-r5` | integer family |
| RISC-V | `rv32imac`, `rv32imc`, `rv32im`, `rv32i`, `rv32gc`, `esp32c3` | `-b riscv` |
| AArch64 | `cortex-a53` | `-b aarch64`, host-native ET_REL |

Hardware evidence today is emulation (Renode/QEMU/unicorn) plus gale's
fixture-scoped silicon gates; linker scripts exist for STM32-class parts,
nRF52840, and a generic profile.
