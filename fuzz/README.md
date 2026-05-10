# synth fuzz harnesses

Cargo-fuzz harnesses for synth's WASM → IR → ARM lowering and the
ARM-Thumb-2 encoder. Tracking issue: [#82](https://github.com/pulseengine/synth/issues/82).

The harnesses target the failure surfaces where silent mis-compilations
have actually appeared in synth (#85, #86, #93). Each one corresponds
to one *class* of bug, not a specific instance — when the fuzzer finds
a crash, the failing input goes into the corpus and the fix can write
a minimal regression test from that input.

## Layout

```
fuzz/
├── Cargo.toml                   # Excluded from workspace; depends on libfuzzer-sys.
├── src/
│   ├── lib.rs                   # Re-exports.
│   └── common.rs                # FuzzOp ↔ WasmOp mapping (Arbitrary-derived).
└── fuzz_targets/
    ├── wasm_ops_lower_or_error.rs            # Harness 1
    ├── wasm_to_ir_roundtrip_op_coverage.rs   # Harness 2 (issue #93 class)
    ├── i64_lowering_doesnt_clobber_params.rs # Harness 3 (AAPCS class)
    └── encoder_no_panic.rs                   # Harness 4
```

## Running locally

Cargo-fuzz needs nightly:

```bash
rustup toolchain install nightly
cargo install cargo-fuzz
```

Then, from the repository root:

```bash
# Smoke run — same budget as CI.
cargo +nightly fuzz run wasm_ops_lower_or_error -- -max_total_time=60

# Longer local sweep — useful while developing a fix.
cargo +nightly fuzz run wasm_to_ir_roundtrip_op_coverage -- -max_total_time=300

# All four harnesses in series.
for t in wasm_ops_lower_or_error wasm_to_ir_roundtrip_op_coverage \
         i64_lowering_doesnt_clobber_params encoder_no_panic; do
  cargo +nightly fuzz run "$t" -- -max_total_time=60 || break
done
```

Crashes are written to `fuzz/artifacts/<target>/`. To re-run a saved
crash:

```bash
cargo +nightly fuzz run wasm_ops_lower_or_error fuzz/artifacts/wasm_ops_lower_or_error/crash-XXXX
```

On macOS you may also need `--target $(rustc --print host-tuple)` —
`cargo-fuzz` defaults to the musl target on Linux, which is not what
you want with ASan; on macOS the host triple is correct.

## Harness reference

### `wasm_ops_lower_or_error`

* **Class:** lowering panic / unencodable instruction
* **What it does:** drives an arbitrary `Vec<WasmOp>` through both
  `OptimizerBridge::optimize_full` + `ir_to_arm` (the optimized path)
  and `InstructionSelector::select_with_stack` (the non-optimized path),
  then runs every emitted `ArmOp` through `ArmEncoder::encode`.
* **Pass criterion:** every step returns `Ok(_)` or `Err(_)`. A panic,
  an integer overflow under `arithmetic_overflow=panic`, or any
  unencodable instruction is a crash.
* **Caps:** input is rejected if `wasm_ops.len() > 256` to keep libfuzzer
  cycles focused; this is not a soundness concession, it's a budget.

### `wasm_to_ir_roundtrip_op_coverage`  (issue #93 class)

* **Class:** silent op drop in `wasm_to_ir`
* **What it does:** for each value-producing `FuzzOp`, builds a
  minimal stack-correct preamble, runs `optimize_full` with **all
  optimizations disabled**, and asserts the live IR length is
  ≥ input op count.
* **Pass criterion:** every value-producing wasm op contributes at least
  one IR instruction. The post-filter inside `optimize_full` strips
  `Opcode::Nop`, so an op silently mapped to `Nop` (the #93 fingerprint)
  drops below the floor and the harness panics.
* **Note:** `I64ExtendI32S`, `I64ExtendI32U`, and `I32WrapI64` are
  currently *skipped* until PR #97 lands. The skip block is documented
  inline; remove it after merge.

### `i64_lowering_doesnt_clobber_params`  (AAPCS class)

* **Class:** AAPCS param register clobber
* **What it does:** generates a sequence that mixes i64 ops with
  `LocalGet(p)` reads of i32 params, lowers via
  `select_with_stack`, then walks each emitted ARM instruction and
  asserts no instruction writes to `r{p}` *before* the wasm
  `LocalGet(p)` site.
* **Pass criterion:** for every param `p < num_params`, no ARM
  instruction (excluding the prologue) emitted from a wasm op preceding
  `LocalGet(p)` writes to `r{p}`.
* **Coverage:** the `writes()` helper enumerates every i64-pair op the
  selector currently emits. Conservative — unlisted variants are
  treated as no-write — so false negatives are possible but false
  positives are not.

### `encoder_no_panic`

* **Class:** encoder panic on a syntactically-valid `ArmOp`
* **What it does:** generates randomly-parametrised but well-typed
  `ArmOp` values across the most encoder-rich variants
  (data-processing, load/store, immediate-shift, branch, sign-extend,
  …) and runs each through every encoder mode (ARM32, Thumb-2,
  Thumb-2+VFP single, Thumb-2+VFP double).
* **Pass criterion:** `ArmEncoder::encode` returns `Ok(_)` or `Err(_)`
  on every input — never panics.

## CI integration

`.github/workflows/fuzz-smoke.yml` runs each target for 60 seconds on
every PR. The matrix mirrors the `[[bin]]` list in `fuzz/Cargo.toml`.
Long-budget runs (1 h / target) and corpus persistence are out of
scope for #82 and tracked separately on the issue.

If you add a new harness, update **both**:
1. `fuzz/Cargo.toml` `[[bin]]` block, and
2. `.github/workflows/fuzz-smoke.yml` `matrix.target`.
