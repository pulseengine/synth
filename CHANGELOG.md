# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

#### RISC-V backend (new — Track B in the multi-target plan)
- New `synth-backend-riscv` crate with RV32IMAC encoder, ELF builder
  (EM_RISCV=0xF3), PMP allocator, instruction selector, bare-metal startup
  generator, and linker script generator.
- CLI integration: `--backend riscv`, `--target riscv32imac/rv32imac/rv32i/rv32gc/rv64imac/rv64gc`.
- New `synth riscv-runtime` command emits `startup.c` + `linker.ld` for
  cross-compilation with `riscv64-unknown-elf-gcc`.
- Selector covers the i32 surface (arithmetic, logic, shifts, comparisons,
  division with trap-on-zero), i32.load/store + sub-word load8/16 + store8/16,
  and control flow (block, loop, if/else, br, br_if). Locals for params 0..7.
- ~30 wasm ops; encoder cross-validated against canonical RV32 hex encodings.
  98 RISC-V backend tests passing.
- Renode RV32IMAC platform (`tests/renode/synth_riscv.repl`).
- Offline smoke tests + calculator end-to-end demo.

#### Cortex-M7 hardening
- `HardwareCapabilities::imxrt1062()` — Cortex-M7 single-precision FPU,
  16 MPU regions, 8 MB QSPI flash, 1 MB OCRAM.
- `HardwareCapabilities::stm32h743()` — Cortex-M7 double-precision FPU,
  16 MPU regions, 2 MB Flash, 1 MB RAM.
- CLI `--hardware {imxrt1062,stm32h743}` and target-info wired up.
- Renode `synth_cortex_m7.repl` profile + `cortex_m7_test.robot`.
- MPU allocator tests proving 16-region operation on M7-class parts.

### Fixed

#### AAPCS regalloc bugs (real-hardware-found)
- **Optimized path** — `optimizer_bridge::ir_to_arm` no longer hardcodes
  i64 ops to R0:R1 / R2:R3. New `alloc_i64_pair` picks free callee-saved
  pairs (R4..R11) skipping live param registers. Fixes silent corruption
  of i32 params when an i64 op ran before all params were read.
- **No-optimize path** — `select_with_stack` now allocates a stack frame
  for non-param locals and uses 8-byte STR/LDR for i64 locals so the
  upper half doesn't get dropped. Fixes corruption of the callee-saved
  spill area when a function has any non-param local.

#### CLI
- `--relocatable` flag — forces ET_REL output even when the wasm has no
  imports, for linking into a host build system (e.g. Zephyr).

#### Toolchain hygiene
- 8 clippy errors fixed (Rust 1.95 lint refresh): `unnecessary_sort_by`,
  `collapsible_match`, `collapsible_if`, `manual_checked_division`.

## [0.1.0] - 2026-03-21

### Added

#### Compiler
- WebAssembly-to-ARM Cortex-M AOT compiler
- ~93 WASM opcodes compile to ARM (i32, i64, f32); SIMD/Helium encoding experimental; f64 decoded but not compiled
- Full control flow (block, loop, if/else, br, br_if, br_table, call)
- Sub-word memory operations (load8/16, store8/16)
- memory.size / memory.grow
- Globals, select, i64 register pairs
- ARM Thumb-2 instruction encoding
- VFP/FPU support (f32; f64 not yet supported in instruction selector)
- WASM SIMD to ARM Helium MVE (Cortex-M55) — encoding and instruction selection implemented, unit-tested only

#### Output
- ELF binary output with vector table and startup code
- Linker script generation (STM32, nRF52840, generic)
- MPU region configuration
- `synth compile --link` cross-compilation pipeline via arm-none-eabi-gcc

#### CLI
- `synth compile` -- compile WASM/WAT to ARM ELF
- `synth disasm` -- disassemble ARM ELF binaries
- `synth verify` -- Z3 SMT translation validation
- `synth backends` -- list available compilation backends
- Target profiles: cortex-m3, cortex-m4, cortex-m4f, cortex-m7, cortex-m7dp, cortex-m55

#### Verification
- Rocq mechanized proofs (233 Qed / 10 Admitted)
- All i32 operations (arithmetic, division, comparison, bit-manip, shift/rotate) have T1 result-correspondence proofs
- Z3 SMT translation validation (53 verification tests)
- STPA safety analysis (losses, hazards, UCAs, constraints)
- Rivet SDLC artifact traceability (250+ artifacts)

#### Testing
- 895 tests, all passing
- 227/257 WebAssembly spec test files compile
- Renode ARM Cortex-M4 emulation tests via Bazel

#### Examples & Integrations
- Zephyr RTOS integration examples
- Anti-pinch window controller (automotive safety demo)
- OSxCAR WASM compilation test

---

## Pre-release Development

### 2025-11-21
- Completed Phase 3a: 100% WASM Core 1.0 coverage (151 operations)
- Added Loom ASIL evaluation and integration analysis
- Added Bazel build system infrastructure

### 2025-11-17
- Initial codebase with 14 Rust crates
- Z3 verification framework
- ARM instruction encoding
- ELF generation
