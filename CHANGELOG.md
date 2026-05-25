# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Documentation
- **Architectural finding: ARMv7-M FPv5 has no F64↔I64 VCVT.** The four
  WASM ops `F64ConvertI64S/U` and `I64TruncF64S/U` listed under v0.7.0's
  "Deferred to follow-up" cannot be implemented as single-instruction
  VCVTs on Cortex-M7DP — the 64-bit integer ↔ floating-point VCVT
  encodings are ARMv8-A FEAT_FP only, not present in M-profile FPv5-D16
  (Cortex-M7DP, M33-DP, M55, M85). Closing these properly requires a
  multi-instruction software sequence (or a soft-float helper) plus
  WASM-trap integration for the trunc family, plus matching Rocq
  proofs — out of scope for v0.8.0's i64-T1-promotion theme. Deferred
  to a later floating-point milestone. Full analysis in
  [`docs/analysis/ARMV7M_F64_I64_VCVT_FINDING.md`](docs/analysis/ARMV7M_F64_I64_VCVT_FINDING.md).
  The selector continues to surface a typed `Error::Synthesis` for
  these ops; no behavior change vs. v0.7.0.

## [0.7.0] - 2026-05-25

Floating-point breadth + verifiable signing CI — synth now compiles
WASM modules with double-precision FP on Cortex-M7DP targets (i.MX RT1062
class), and the sigil keyless-signing path is now exercised end-to-end
in CI against a sha256-pinned wsc v0.9.0. PRs #140 (Phase 5 e2e),
#141 (f64 codegen).

**Falsification statement.** v0.7.0 would be wrong if (a) a WASM module
using only the f64 ops listed below produces an ELF that fails to link,
returns a synthesis error on a Cortex-M7DP target, or computes a result
that disagrees with the WASM reference on a covered op; or (b) the new
`signing-e2e.yml` workflow goes red on a clean `v0.7.0` checkout (cases
1 and 2 must remain hard checks; case 3 is xfail against
[sigil#135](https://github.com/pulseengine/sigil/issues/135)).

### Added

#### f64 codegen — ARM VFP-D end-to-end
- **WASM f64 modules now compile on Cortex-M7DP targets**
  (double-precision FPU, `FPUPrecision::Double`). The non-optimized
  selector (`InstructionSelector::select_with_stack`) lowers every
  f64 op for which the backend has a direct VFP-D encoding:
  arithmetic (`F64Add/Sub/Mul/Div`), comparison
  (`F64Eq/Ne/Lt/Le/Gt/Ge`), unary math
  (`F64Abs/Neg/Sqrt/Ceil/Floor/Trunc/Nearest`), binary math
  (`F64Min/Max/Copysign`), constants (`F64Const`), memory
  (`F64Load/Store`), and the i32/f32 conversion / bitcast family
  (`F64ConvertI32S/U`, `F64PromoteF32`, `F64ReinterpretI64`,
  `I64ReinterpretF64`, `I32TruncF64S/U`). Values live in VFP
  D-registers (D0..D15), allocated via a wrap-around counter
  mirroring the f32 S-register allocator.
- **Targets without double-precision FPU fail cleanly.** F64 ops
  on Cortex-M3 (no FPU) or Cortex-M4F (single-precision only) now
  surface a typed `Error::Synthesis` whose message names the
  missing capability ("target {} has no FPU" or "target {} lacks
  double-precision FPU"). Replaces the previous blanket "F64 not
  supported" path, and matches the existing validate_instructions
  feature-gate behavior. Silent miscompilation or panic is
  impossible — every f64 op is matched explicitly.
- **VFP-D encoding test coverage.** 24 new byte-level encoder
  tests cross-checked against the ARMv7-M Architecture Reference
  Manual (Section A7.5) cover VADD/VSUB/VMUL/VDIV.F64,
  VABS/VNEG/VSQRT.F64, VLDR/VSTR.64, VCVT.F64.F32, and
  VMOV core ↔ D-register. The coprocessor-11 (cp11 / 0xB)
  selection bit is verified independently from each arithmetic
  op's bit pattern.
- The optimized path (`optimize_full` in `synth-synthesis`) still
  declines modules containing f64 ops and falls back to the
  non-optimized selector (PR #126 behavior, unchanged); the
  fallback path is what now compiles f64 modules end-to-end.

#### Deferred to follow-up
- f64 ↔ i64 conversions (`F64ConvertI64S/U`, `I64TruncF64S/U`)
  remain unimplemented — they require i64 register-pair handling
  in the VFP-D backend. The selector emits a typed error
  mentioning "i64 register pairs on 32-bit ARM" when these ops
  are encountered, consistent with the existing f32 behavior.
- `F32DemoteF64` (round f64 to f32) is not yet handled — needs a
  `VCVT.F32.F64 Sd, Dm` ArmOp variant in the encoder.
- Extending the optimized IR path (`wasm_to_ir` → `ir_to_arm`) to
  model f64 is a separate, larger feature.

### Internal
- CI: `signing-e2e.yml` workflow added (Phase 5 end-to-end). Runs three
  wsc keyless cases against a sha256-pinned wsc v0.9.0. Case 3
  (tamper-negative) is `xfail` against current wsc — see
  [pulseengine/sigil#135](https://github.com/pulseengine/sigil/issues/135):
  `wsc verify --keyless` accepts WASM modules whose signed payload has
  been byte-modified after signing. Documented in
  `docs/sigil-integration.md`.

## [0.6.0] - 2026-05-24

Supply-chain close-out — synth produces all six evidence layers from
rivet#107's table (SLSA + cosign + SBOM + build-attest + signed-output
+ sbom-record). PRs #135 (Phase 5) and #136 (Phases 4 + 6).

### Added

#### CLI — sign synth's output ELF binaries (release roadmap Phase 5)
- **`synth compile --sign-output`** invokes sigil's
  `wsc sign --keyless --format elf` after writing the ELF, attaching a
  Sigstore keyless signature in place. Off by default — opt in per
  invocation; the unsigned compile path is unchanged for consumers
  without `wsc` installed. Composes with `--all-exports` (one signing
  call covers the multi-function ELF) and with `--sbom` (the SBOM
  records the unsigned synth output; the on-disk ELF after this
  command is the signed version). When `wsc` is missing, synth exits
  non-zero with an actionable error pointing at sigil's install
  instructions. See [`docs/sigil-integration.md`](docs/sigil-integration.md)
  for the trust model, verification command, and the wsc-version
  contract assumption.

#### Release pipeline — Phases 4 + 6
- **Phase 4 — crates.io trusted publishing.** New workflow
  `.github/workflows/publish-to-crates-io.yml` publishes the
  workspace's public crates (`synth-cli`, `synth-core`, `synth-frontend`,
  `synth-synthesis`, `synth-backend`, `synth-backend-{awsm,wasker,riscv}`,
  `synth-cfg`, `synth-opt`, `synth-verify`) on every `v*` tag via
  crates.io OIDC trusted publishing — no stored `CRATES_IO_TOKEN`.
  Internal-only crates (`synth-analysis`, `synth-abi`, `synth-memory`,
  `synth-qemu`, `synth-test`, `synth-wit`) carry `publish = false`.
  Dependency-order walk lives in `scripts/publish.rs` (compiled by
  `rustc` at workflow start). User-side step still required:
  per-crate trusted-publisher registration on crates.io.
- **Phase 6 — toolchain SBOM auto-emit.** `release.yml` now installs
  `cargo-cyclonedx` and writes `synth-v<VERSION>.cdx.json` (CycloneDX
  1.5 JSON) into the release assets before the SHA256SUMS step, so the
  existing cosign signature over `SHA256SUMS.txt` transitively covers
  the SBOM. Complements (does not replace) the per-compilation SBOM
  from `synth compile --sbom`.

### Changed
- Workspace `version` bumped from `0.1.0` to `0.6.0` to support
  crates.io trusted publishing (real semvers required) and to align
  the in-tree version with the next release tag. Going forward the
  workspace version is bumped pre-tag in lockstep with the release
  tag. Every published crate's internal `path` deps now also carry
  an explicit `version = "0.6.0"` so `cargo publish` can resolve
  them on crates.io.

## [0.5.0] - 2026-05-23

Verification & robustness release. Three workstreams: prototype-to-
production validator pattern, panic-free optimized lowering with the
gating fuzz harness restored, and the RV32 i64 integer surface
completed.

### Added

#### Verification — validator pattern reaches production (#76)
- **`Z3ArmValidator` now covers the full i32 + i64 op surface** —
  arithmetic, logic, shifts/rotates, comparisons, unary ops, div/rem
  for i32; the same arithmetic/logic/shift/comparison surface for
  i64, modeled as 64-bit bitvectors and decomposed into the (lo, hi)
  register pair the ARM lowering uses. Per-op Z3 SMT validation
  replaces hand-written Rocq lemmas for the i64 surface (the layer
  where Rocq is most painful). Negative tests confirm the validator
  rejects deliberately wrong lowerings. **133 synth-verify tests.**
  Closes #76 (CompCert-style untrusted-solver + trusted-validator
  strategy); sidesteps #73 (Rocq divergence). (#133)

#### RISC-V — i64 div/rem (Phase 3 completes the i64 integer surface)
- **`I64DivS` / `I64DivU` / `I64RemS` / `I64RemU`** lower to inline
  software long division (one shared 64-iteration restoring-binary-
  division core; signed wrappers compute magnitudes via branchless
  abs and fix the result sign). Wasm trap semantics honored:
  divide-by-zero traps via 64-bit-or-of-halves; `INT64_MIN / -1`
  overflow trap is emitted only for `div_s` — `rem_s` correctly does
  not trap there. **+11 tests, 158 RV32 selector tests.** (#131)

### Fixed

#### Optimized path — panic-free, fuzz re-gated
- **`ir_to_arm` returns `Result` instead of panicking** on an
  unmapped vreg. The `get_arm_reg` defensive panic (PR #101) was the
  last remaining panic site in the optimized lowering pipeline;
  166 call sites threaded through `?`. The backend falls back to
  the direct selector on `Err` (same shape as the issue-#120 float
  fallback). The diagnostic content of the original panic is
  preserved in the `Err` message — the bug-finder role still holds.
- **`pop_i32_unary!` macro converted to `?`** — sibling fix. The
  earlier slot_stack Result conversion missed this macro because
  its `.expect(...)` ended with `,` (macro-arg) not `;`
  (statement); the re-gated fuzz harness caught it on the first
  run.
- **`wasm_ops_lower_or_error` fuzz harness re-promoted to gating**
  (`gating: true`) — closes debt open since v0.3.1 / PR #117. The
  gating harness now serves as a permanent clean-room verifier of
  the panic-free invariant. (#132)

## [0.4.0] - 2026-05-22

### Added

#### RISC-V backend — i64 Phase 2
- **16 new i64 ops** in the RV32IMAC selector, building on the Phase 1
  typed register-pair model (v0.3.1):
  - `I64Mul` — low-64 product via `mul` + `mulhu`.
  - `I64Shl` / `I64ShrS` / `I64ShrU` — runtime-amount shifts with the
    cross-word (`shamt >= 32`) case handled.
  - `I64Rotl` / `I64Rotr` — composed from cross-word shifts.
  - `I64Clz` / `I64Ctz` / `I64Popcnt` — base-ISA software sequences
    (no Zbb dependency).
  - `I64{Lt,Le,Gt,Ge}{S,U}` — the hi-then-lo 64-bit comparison ladder.
  - `I64Extend8S` / `I64Extend16S` / `I64Extend32S`.
- i64 `div`/`rem` remain deferred to Phase 3 (need a `__divdi3`-style
  runtime); they fail loudly with `Unsupported`, not silently. (#128)

#### Supply chain — CycloneDX SBOM
- **`synth compile --sbom`** writes a CycloneDX 1.5 JSON SBOM
  (`<output>.cdx.json`, or an explicit path) documenting the synth
  compiler, the input WASM module (SHA-256 + size), the output ELF
  (SHA-256, size, target triple, backend), and the WASM module's
  imports as a dependency graph. This is the artifact consumed by
  `rivet import --format cyclonedx` for rivet #107's `sbom-record`.
  See `docs/sbom.md`. (#129)

### Changed
- Closed #72 (explicit WASM value-stack tracking): the production
  lowering path (`select_with_stack`) already tracks the value stack
  deterministically, and the `Replacement::Var`/`Inline` silent-`Nop`
  variants now error. The round-robin `select_default` flagged by the
  issue is test-only and never reaches a compiled binary.

## [0.3.1] - 2026-05-21

First release built and published by the automated release pipeline:
cross-platform binaries, SHA256 checksums, SLSA build provenance, and
cosign keyless signatures (see `docs/release-process.md`).

### Added

#### RISC-V backend — toward ARM parity
- **`WasmOp::Call` leaf-call lowering** — arguments marshalled into
  `a0..a7` per the RV psABI, label-based `RiscVOp::Call` resolved by the
  ELF builder. i64 call args and back-to-back calls with surviving
  results are deferred to v0.4 (need function-signature plumbing). (#116)
- **i64 Phase 1** — the selector's value stack is now a typed
  `Vec<VstackVal>` (`I32` / `I64 { lo, hi }`). i64 const, add, sub,
  and/or/xor, eq/ne/eqz, extend_i32_s/u, wrap_i64, and load/store. (#119)

#### Binary safety — Phase 1
- **`--safety-bounds` umbrella flag** (`mpu` / `software` / `mask` /
  `none`) with `--bounds-check` kept as a deprecated alias. RV32
  software bounds checks (`bgeu` + `ebreak` trap block), RV32 signed
  division overflow trap, and `safety-manifest.json` emission. (#115)

#### Verification
- **Validator-pattern prototype** — `CertifiedSelection` + `Validator`
  trait + `Z3ArmValidator` for `I32Add`. First step of the CompCert-
  style certifying-validator strategy toward retiring divergent Rocq
  proofs. (#113, issues #73 / #76)

#### Release engineering
- **Automated release pipeline** (`release.yml`) — tag-triggered
  cross-platform binary matrix, `SHA256SUMS.txt`, SLSA provenance via
  `actions/attest-build-provenance`, cosign keyless signing, GitHub
  release automation. `docs/release-process.md` documents the process
  and a 5-phase rollout plan. (#123)

### Fixed

#### Silicon-blocking codegen
- **`wasm_to_ir` slot-model rewrite** — `inst_id` was overloaded as both
  the unique IR id and the vreg-slot index, so any op that consumed a
  stack slot without producing one (`Drop`, `LocalSet`, stores, …)
  corrupted downstream back-references — a silent miscompilation Gale
  caught on real silicon. Decoupled via an explicit `slot_stack`. (#122,
  issue #121)
- **f32/f64 in the optimized path** — float ops fell through to
  `Opcode::Nop`, leaving downstream consumers with unmapped vregs and
  tripping the defensive panic. `optimize_full` now declines float
  modules with a typed error and the backend falls back to the
  non-optimized selector, which lowers f32 via VFP/FPU. (#126, issue
  #120)

#### Robustness
- **Pre-flight wasm stack-underflow check** (`wasm_stack_check`) — the
  lowering pipeline returns a typed `Err` on malformed input instead of
  panicking. `wasm_to_ir` now returns `Result` and propagates
  slot-stack underflow rather than `.expect()`-panicking. (#117)
- **`synth verify` exits non-zero** when the binary was built without
  `--features verify`, instead of printing a hint and exiting
  success-shaped — a no-op verify step silently passing CI is a
  correctness-of-process bug. (#125, issue #124)

### Changed
- CHANGELOG backfilled with per-version sections for v0.1.1–v0.3.0. (#114)

### Internal
- cargo-fuzz harness `i64_lowering_doesnt_clobber_params` gained a
  carve-out for return-value-placement dead stores. (#118, closes #112)
- `fuzz/seed_corpus/` directory layout for committed regression seeds;
  the fuzz-smoke workflow replays them on every run.

## [0.3.0] - 2026-05-15

### Added

#### Optimizations
- **`(i32.const C)(i32.load offset=O)`** folds to a single 4-byte
  `LDR rd, [base, #(C+O)]` when `C+O ≤ 4095`. Drops from ≥10 bytes
  (MOVW+MOVT+LDR triplet). Applies to load/store + sub-word variants. (#96)
- **u64-packed FFI return extraction**: `(i64.shr_u 32; i32.wrap_i64)`
  and friends lower to a direct hi/lo register rename. **83% size
  reduction** on the canonical pattern (48 bytes → 8 bytes). (#98)

#### Test + verification infrastructure
- 59 new semantic-correctness tests covering every i64 wasm op. Closes
  the gap that allowed #93 to ship. (#99)
- 37 tests of coverage uplift for the v0.1.1 diff. (#92)
- 4 cargo-fuzz harnesses + CI smoke gate (#100):
  - `wasm_ops_lower_or_error` (gating) — arbitrary `Vec<WasmOp>` through
    both lowering paths, asserts no panic / no unencodable instruction
  - `wasm_to_ir_roundtrip_op_coverage` (gating) — value-producing ops
    must emit live IR (catches the #93-class silent-drop bug)
  - `i64_lowering_doesnt_clobber_params` (exploration) — random
    i64/i32-param mixes, asserts AAPCS preservation
  - `encoder_no_panic` (exploration) — random ArmOp values, encoder
    panic-freedom
- Spectre/csdb policy doc + aarch64 CVE audit (CVE-2026-34971 /
  CVE-2026-34944) + arXiv 2604.17391 citation. (#105)
- 842-line binary-safety design covering MPU/PMP/CFI/PAC/BTI/MSPLIM with
  per-target applicability matrix and 5-phase roadmap. (#110)

### Fixed

#### AAPCS bug class — systematic closure
- 24 i64 ops (Eq/Ne/Lt/Le/Gt/Ge × Signed/Unsigned, Mul/Div/Rem,
  Rotl/Rotr, Clz/Ctz/Popcnt, Extend8/16/32 Signed, I32WrapI64)
  re-routed through `alloc_consecutive_pair`. (#106, #103)
- CSE missing arms for `MemLoad`/`MemStore`/`Extend` consumers added —
  fixes silent miscompile when CSE killed a duplicate load. (#107, #104)
- **Systematic audit**: 47 hardcoded R0..R3 sites swept, 6 new `Opcode`
  variants, 27 regression tests. (#108)
- `WasmOp::Call` had no `wasm_to_ir` handler — fell through to `Nop`,
  causing recursive `fib` to silently miscompile. (#109)
- **Defensive panic** on unmapped vreg replaces the silent `R0` fallback.
  Future wasm_to_ir gaps now crash the compiler with a diagnostic instead
  of producing miscompiled firmware. (#101)
- `I32WrapI64` no longer preassigns R0 — defers to function-return
  epilogue. (#111)

### CI / infrastructure
- Test + Clippy moved back to ubuntu-latest (smithy runners couldn't
  hold the z3-sys C++ build's intermediate files). (#102)
- Fuzz workflow split into gating (2 harnesses) + exploration (2 harnesses,
  `continue-on-error: true`). Promotion criterion documented.

## [0.2.1] - 2026-05-10

### Fixed
- **Silicon-blocking memset i64-codegen non-terminating loop** on
  Cortex-M. `optimizer_bridge::wasm_to_ir` had no handler for
  `I64ExtendI32U` / `I64ExtendI32S` / `I32WrapI64` — their result vregs
  were never mapped to ARM registers, and `get_arm_reg`'s silent R0
  fallback caused subsequent i64 shifts to read R0 as `rm_lo`/`rm_hi`,
  destroying memset's destination pointer. Discovered on real
  STM32G474RE silicon at `memset+0x4c` during Zephyr's `z_bss_zero`.
  Synth-emitted memset was 454 bytes vs picolibc's ~80 and looped
  forever. (#93 / #97)

## [0.2.0] - 2026-05-10

### Added — RISC-V RV32IMAC GA

- New `synth-backend-riscv` crate: RV32IMAC encoder, ELF builder
  (EM_RISCV=0xF3), PMP allocator, instruction selector, bare-metal
  startup + linker script generators.
- CLI: `--backend riscv`, `--target riscv32imac/rv32imac/rv32i/rv32gc/rv64imac/rv64gc`.
- New `synth riscv-runtime` command emits `startup.c` + `linker.ld` for
  cross-compilation with `riscv64-unknown-elf-gcc`.
- Selector covers the i32 surface (arithmetic, logic, shifts,
  comparisons, division with trap-on-zero), `i32.load/store` +
  sub-word load8/16 + store8/16, and control flow (block, loop,
  if/else, br, br_if). Locals for params 0..7.
- 98 RISC-V backend tests passing; encoder cross-validated against
  canonical RV32 hex encodings.
- Renode RV32IMAC platform (`tests/renode/synth_riscv.repl`) wired into
  Bazel CI.
- Offline integration smoke + end-to-end calculator demo.

### Known gaps (deferred to v0.3.x)
- i64 lowering for RV32 (register pairs)
- RV32F/D floating point
- br_table jump-table emission
- Cross-function calls + relocations
- RISC-V Rocq proofs

## [0.1.1] - 2026-05-10

### Fixed — AAPCS regalloc bugs (real-hardware-found via gale silicon tests)
- **Optimized path** — `optimizer_bridge::ir_to_arm` no longer hardcodes
  i64 ops to R0:R1 / R2:R3. New `alloc_i64_pair` picks free callee-saved
  pairs (R4..R11) skipping live param registers. Fixes silent corruption
  of i32 params when an i64 op ran before all params were read.
- **No-optimize path** — `select_with_stack` now allocates a stack frame
  for non-param locals and uses 8-byte STR/LDR for i64 locals so the
  upper half doesn't get dropped. Fixes corruption of the callee-saved
  spill area when a function has any non-param local.

### Added
- `HardwareCapabilities::imxrt1062()` — Cortex-M7 single-precision FPU,
  16 MPU regions, 8 MB QSPI flash, 1 MB OCRAM.
- `HardwareCapabilities::stm32h743()` — Cortex-M7 double-precision FPU,
  16 MPU regions, 2 MB Flash, 1 MB RAM.
- CLI `--hardware {imxrt1062,stm32h743}` and target-info wired up.
- Renode `synth_cortex_m7.repl` profile + `cortex_m7_test.robot`.
- MPU allocator tests proving 16-region operation on M7-class parts.
- CLI `--relocatable` flag — forces ET_REL output even when the wasm
  has no imports, for linking into a host build system (e.g. Zephyr).

### Toolchain hygiene
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
