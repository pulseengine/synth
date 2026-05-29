# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.10.0] - 2026-05-29

**Theme: i64 add/sub T1 + Rocq 9 Z.mod_mod wrap closed + bitwise lift infrastructure.**

v0.10.0 closes the two carry/borrow i64 admits and the long-standing
`Z.mod_mod` blocker, and lands the infrastructure for the remaining
bitwise T1 lifts. All proofs verified against the local Nix/Bazel Rocq
toolchain (`bazel build //coq:verify_proofs` green) before each push —
this session established that synth's Rocq proofs can be checked locally,
ending the blind-CI-round-trip pattern.

**Falsification statement.** v0.10.0 is wrong if (a) any newly-Qed lemma
is actually `Admitted`/`Abort` (grep confirms the claimed Qeds compile),
(b) `bazel test //coq:verify_proofs` goes red on a clean v0.10.0 checkout,
(c) a new `Axiom` was introduced (grep confirms zero), or (d) the stated
admit count (12) does not match the tree.

### Added
- **i64 add/sub T1 result-correspondence** (PR #160). `i64_add_correct`
  and `i64_sub_correct` (Admitted in v0.9.0) are now Qed, via new
  ADDS/ADC carry-propagation and SUBS/SBC borrow-propagation lemmas in
  `coq/Synth/ARM/ArmFlagLemmas.v` (`i64_add_via_adds_adc`,
  `i64_sub_via_subs_sbc`, `carry_split_add`, `borrow_split_sub`). The
  discharge steps `exec_program` over the real `[ADDS; ADC]` / `[SUBS; SBC]`
  pairs, reading the C flag set by the low-half instruction. No new axioms.
- **Bitwise halves-distribute infrastructure** (PR #161). Six pure-Z
  distribution lemmas (`{land,lor,lxor}_low32` via `Z.land_ones` + bit
  extensionality; `{land,lor,lxor}_high32` via `Z.shiftr_{land,lor,lxor}`),
  plus `combine_i32_raw`, `mod64_mod32`, `combine_lo32`, `combine_hi32`,
  and `and_lo_combine` — all in `coq/Synth/Synth/CorrectnessI64.v`, all
  Qed, no axioms.

### Fixed
- **`i64_to_i32_to_i64_wrap` closed** (PR #161). The long-standing Rocq 9
  `Z.mod_mod` Admit in `coq/Synth/Common/Integers.v` is now Qed via a
  canonical symbolic-atom modular proof (keeps moduli as atoms so `lia`
  avoids 2^64-scale literal certificates; `rewrite !Z.mod_small` clears the
  double `mod 2^64` introduced by `I64.repr` + `I64.unsigned`).

### Deferred to v0.11.0
- `i64_and_correct` / `i64_or_correct` / `i64_xor_correct` remain Admitted
  (3 of the 12 total admits). The remaining work is the high-half combine
  helper (`(Z.land X Y mod 2^64) / 2^32 mod 2^32`, via `ZDivEucl.mod_mul_r`),
  the or/xor analogues of `and_lo_combine`, and the three theorem
  exec-proofs (template: `i64_add_correct` minus flag handling). The
  infrastructure to close them shipped in this release.

## [0.9.0] - 2026-05-27

**Theme: i64 T1 result-correspondence lifts against the aligned model.**

v0.9.0 picks up what v0.8.0 set up. v0.8.0 (the "honest foundation") aligned
`Compilation.v` with the real Rust codegen and shipped 26 type-only pseudo-op
axioms + tactics + flag-correspondence lemmas. v0.9.0 layers the value-correspondence
on top: 26 new `_spec` axioms equate every i64 pseudo-op's result to the WASM-spec
function, then 30 existence-only (T2) i64 proofs are lifted to result-correspondence
(T1), and the 5 strategically-`Admitted` theorems #150 carried over are discharged.

**Net delta:** previously had 36 i64 theorems Qed at T2 plus 5 admits.
Now has **30 new T1 Qeds + 5 discharged T1 Qeds = 35 i64 T1 Qeds**, with 5 honest
admit carry-overs (Add/Sub/And/Or/Xor) whose proofs depend on missing helper
lemmas (ADDS/ADC carry-propagation; SUBS/SBC borrow-propagation; halves-distribute
over bitwise, blocked by Rocq 9 `Z.mod_mod`).

**Falsification statement.** v0.9.0 is wrong if (a) any of the 35 newly-T1 i64
theorems is shown to disagree with the WASM reference for a value pair the
theorem covers (the `_spec` axioms are inconsistent with `Compilation.v`),
(b) any of the 5 honest-Admitted carry-overs is claimed `Qed.` anywhere in the
release artifacts, (c) `bazel test //coq:verify_proofs` goes red on a clean
v0.9.0 checkout, or (d) any newly-added `_spec` axiom claims a result the Rust
codegen does not actually produce (cross-checked against `docs/analysis/I64_CODEGEN_SURVEY.md`).

### Added

- **i64 pseudo-op result-correspondence axioms (v0.9.0 PR 1 precursor).**
  `coq/Synth/ARM/ArmSemantics.v` gains 26 new `_spec` axioms that pin the
  axiomatic i64 pseudo-op result functions (`i64_const_lo`, `i64_divs_pair`,
  `i64_mul_lo_bits`, etc., introduced as opaque types by v0.8.0 #150) to the
  WASM-spec operation on the combined 64-bit operand pair via the new
  `combine_i32 / lo_of_i64 / hi_of_i64` helpers in `Common/Integers.v`. Each
  axiom is cross-referenced to `docs/analysis/I64_CODEGEN_SURVEY.md` and to
  the `instruction_selector.rs` line numbers that emit the pseudo-op. This
  layer was the missing precursor blocking PRs 2-5 of umbrella #152.
- **5 i64 T1 admit discharges (v0.9.0 PR 1).** `i64_const_correct` in
  `CorrectnessSimple.v` and `i64_{divs,divu,rems,remu}_correct` in
  `CorrectnessI64.v` are now `Qed` via the new spec axioms. Each theorem is
  restated with dual-register hypotheses and dual-register post-conditions
  (R0 = lo_of_i64 result, R1 = hi_of_i64 result), reflecting that an i64
  result spans both halves of the (R0, R1) register pair.
- `I64.rems` and `I64.remu` definitions in `Common/Integers.v` to provide a
  WASM-spec target for the new `i64_rems_pair_spec` / `i64_remu_pair_spec`
  axioms (previously only `I64.divs` and `I64.divu` were defined).

## [0.8.0] - 2026-05-26

**Theme: honest i64 verification foundation.**

v0.8.0 was originally scoped as "i64 T1 result-correspondence parity"
(umbrella issue #147). A clean-room check of the first foundation PR
(#149) surfaced that `coq/Synth/Synth/Compilation.v` modeled i64 ops
as single 32-bit ARM instructions (e.g., `I64Add → [ADD R0 R0 R1]`,
inline comment: *"Simplified: just add low 32 bits"*) while the real
Rust compiler at `crates/synth-synthesis/src/instruction_selector.rs:1450`
emits proper register-pair sequences (`ADDS R0,R0,R2; ADC R1,R1,R3`).
The umbrella's own falsification clause forbade shipping T1 proofs
that "prove a different operation than the compiler emits."

Rather than overclaim or paper over the gap, v0.8.0 ships the
**aligned model + proof tooling** layer, and the actual T2→T1
promotions become v0.9.0's theme. This is a smaller user-visible
delta but a much bigger verification-soundness delta: the existing
i64 proofs now reason about the operation the compiler actually
emits, instead of a degenerate 32-bit slice of it.

**Falsification statement.** v0.8.0 is wrong if (a) the aligned
`Compilation.v` clauses do not match what the Rust compiler emits
(cross-checked against the per-op survey in
[`docs/analysis/I64_CODEGEN_SURVEY.md`](docs/analysis/I64_CODEGEN_SURVEY.md)),
(b) `bazel test //coq:verify_proofs` goes red on a clean v0.8.0
checkout, or (c) any of the 5 strategically-`Admitted` i64 theorems
(4 div/rem + 1 i64_const) are claimed to be Qed anywhere in the
release artifacts.

### Changed
- **`coq/Synth/Synth/Compilation.v` aligned with real Rust i64 codegen** (PR #150).
  28 i64 op clauses updated: I64Add/Sub now emit `ADDS R0,R0,R2; ADC R1,R1,R3`
  (and SUBS/SBC); I64And/Or/Xor emit parallel lo/hi binops; i64 comparison ops
  emit a single `I64SetCond[Z]` pseudo-op; div/rem/mul/shifts/rotates/bit-manip
  emit ArmOp::I64* pseudo-ops mirroring the Rust ArmOp variants. ArmSemantics.v
  gains the real ADDS/ADC/SUBS/SBC instructions plus ~25 axiomatized result
  functions for the pseudo-ops (parallel to how VFP is axiomatized).
  Per-op cross-check against the Rust source is documented in
  [`docs/analysis/I64_CODEGEN_SURVEY.md`](docs/analysis/I64_CODEGEN_SURVEY.md).
- ~36 existence-only (T2) i64 proofs re-proved against the aligned model
  using the existing `solve_single_arm` / `solve_cmp_mov` / `solve_mem_single`
  tactics. **Net: previously had 29 i64 theorems Qed against a model that
  proved the wrong operation; now has 36 i64 theorems Qed against the
  correct model, plus 5 strategically-Admitted theorems pending the
  v0.9.0 lift queue.**

### Added
- **Proof tooling for i64 T1 lifts** (PR #149). Three new tactics in
  `coq/Synth/Synth/Tactics.v`: `synth_binop_proof_i64`,
  `synth_cmp_binop_proof_i64`, and `synth_cmp_unop_proof_i64`. Eleven
  new i64 flag-correspondence lemmas in `coq/Synth/ARM/ArmFlagLemmas.v`
  (`z_flag_sub_eq_i64`, `flags_ne_i64`, `nv_flag_sub_lts_i64`,
  `flags_ltu_i64`, `flags_ges_i64`, `flags_geu_i64`, `flags_gts_i64`,
  `flags_gtu_i64`, `flags_les_i64`, `flags_leu_i64`,
  `z_flag_sub_eqz_i64`), plus 14 supporting boundedness helpers. All
  proofs Qed; 0 Admitted in #149's diff. These are the infrastructure
  the v0.9.0 lift PRs will consume.

### Documentation
- **Architectural finding: ARMv7-M FPv5 has no F64↔I64 VCVT** (PR #148).
  The four WASM ops `F64ConvertI64S/U` and `I64TruncF64S/U` listed under
  v0.7.0's "Deferred to follow-up" cannot be implemented as
  single-instruction VCVTs on Cortex-M7DP — the 64-bit integer ↔
  floating-point VCVT encodings are ARMv8-A FEAT_FP only, not present
  in M-profile FPv5-D16. Closing these requires a multi-instruction
  software sequence plus WASM-trap integration plus matching Rocq
  proofs — deferred to a later floating-point milestone. Full analysis
  in [`docs/analysis/ARMV7M_F64_I64_VCVT_FINDING.md`](docs/analysis/ARMV7M_F64_I64_VCVT_FINDING.md).
  Selector continues to surface a typed `Error::Synthesis`; no
  behavior change vs. v0.7.0.
- **I64 codegen survey** at [`docs/analysis/I64_CODEGEN_SURVEY.md`](docs/analysis/I64_CODEGEN_SURVEY.md):
  per-op extraction of what the Rust compiler emits for every i64 WASM
  op, with line citations into `instruction_selector.rs`. Reviewers
  audit Compilation.v against the Rust source mechanically using this
  file.

### Fixed
- **Bazel rocq_library dep wiring**. `rules_rocq_rust` requires every
  `Require Import Synth.X.Y.` in a `.v` file to be matched by a
  corresponding `:y` target in the library's `deps` list — transitive
  deps through intermediate targets do **not** propagate the `-Q`
  flags to `coqc`. Synth's `:arm_instructions`, `:arm_semantics`,
  `:compilation`, `:tactics`, and `:correctness_*` rocq_libraries were
  relying on transitive resolution that happened to work on main only
  because cached `.vo` files masked the missing flags. PR #150's
  alignment changes broke the happy accident; the deps are now
  explicit (matches the pattern in
  `pulseengine/loom/proofs/BUILD.bazel`).

### Deferred to v0.9.0
- **i64 T1 result-correspondence promotions.** The original umbrella's
  scope: 30 T2 → T1 lifts (arithmetic, bitwise, shifts/rotates,
  comparisons, bit-manip) plus discharging the 5 admits #150 introduced
  (4 div/rem T1 + 1 i64_const T1). These now ride into v0.9.0 as the
  primary theme, against the now-aligned model. Tracked in #147.
- F64↔I64 conversion implementations (see Documentation section).
- F32DemoteF64 (deferred from v0.7.0).

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
