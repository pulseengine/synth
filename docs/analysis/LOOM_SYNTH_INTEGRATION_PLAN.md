# Loom ↔ Synth Integration Plan
## Two-Tier Architecture for ASIL D Certification

---

## Architecture Overview

```
┌──────────────────────────────────────────────────────────┐
│ Loom (Open Source - MIT License)                         │
│ https://github.com/pulseengine/loom                      │
├──────────────────────────────────────────────────────────┤
│ ASIL Level: B (maybe C)                                  │
│ Verification: Z3 SMT translation validation              │
│                                                          │
│ ✅ Shared Components (MIT License):                      │
│   ├─ ISLE optimization rules                            │
│   ├─ 12-phase optimization pipeline architecture        │
│   ├─ Cost model definitions                             │
│   ├─ Register allocation heuristics                     │
│   ├─ Instruction selection patterns                     │
│   └─ Test suite (WebAssembly → ARM)                     │
│                                                          │
│ ❌ Loom-Specific (Not Shared):                           │
│   ├─ Z3 SMT verification implementation                 │
│   ├─ Loom CLI and tooling                               │
│   └─ Loom branding/documentation                        │
└──────────────────────────────────────────────────────────┘
                         ↓
                 (dependency: loom-shared crate)
                         ↓
┌──────────────────────────────────────────────────────────┐
│ Synth (Commercial - Proprietary)                         │
│ This repository: pulseengine/Synth (private)             │
├──────────────────────────────────────────────────────────┤
│ ASIL Level: D                                            │
│ Verification: Coq mechanized proofs + Sail ARM semantics │
│                                                          │
│ ✅ Synth-Specific (Proprietary):                         │
│   ├─ Coq formal proofs of compiler correctness          │
│   ├─ Sail ARM v8-M integration                          │
│   ├─ Extracted OCaml verified compiler                  │
│   ├─ ISO 26262 qualification evidence                   │
│   ├─ ASIL D qualification package                       │
│   ├─ Safety manual                                      │
│   └─ Commercial support contracts                       │
│                                                          │
│ ✅ Uses from Loom:                                       │
│   ├─ loom-shared optimization rules                     │
│   ├─ Proven optimization pipeline                       │
│   └─ Battle-tested test suite                           │
└──────────────────────────────────────────────────────────┘
```

---

## Shared Components: loom-shared Crate

### What Goes in loom-shared?

**Rust crate published to crates.io** (MIT license)

```
loom/
├── Cargo.toml                   # Workspace root
├── crates/
│   ├── loom-shared/             # ← NEW: Shared definitions
│   │   ├── Cargo.toml           # MIT license
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── isle/            # ISLE optimization rules
│   │   │   │   ├── mod.rs
│   │   │   │   ├── peephole.isle
│   │   │   │   ├── strength_reduction.isle
│   │   │   │   └── instruction_selection.isle
│   │   │   ├── pipeline/        # Optimization pipeline architecture
│   │   │   │   ├── mod.rs
│   │   │   │   ├── phase_trait.rs
│   │   │   │   └── pipeline_builder.rs
│   │   │   ├── cost_model/      # Cost model definitions
│   │   │   │   ├── mod.rs
│   │   │   │   └── arm_costs.rs
│   │   │   ├── register_allocation/
│   │   │   │   ├── mod.rs
│   │   │   │   └── heuristics.rs
│   │   │   └── test_suite/      # Shared test cases
│   │   │       └── wasm_arm_tests.rs
│   │   └── README.md
│   ├── loom-optimizer/          # Loom-specific implementation
│   │   └── ...uses loom-shared
│   └── loom-verify/             # Z3 SMT verification (Loom only)
│       └── ...
```

### Versioning Strategy

**Semantic versioning with stability guarantees:**

```toml
# loom-shared/Cargo.toml
[package]
name = "loom-shared"
version = "0.3.0"  # Match Loom version
edition = "2021"
license = "MIT"
description = "Shared optimization definitions for WebAssembly → ARM compilers"
repository = "https://github.com/pulseengine/loom"

[dependencies]
# Minimal dependencies for maximum compatibility
cranelift-isle = "0.111"  # ISLE rule engine
wasmparser = "0.121"      # WebAssembly parsing
```

**Stability promise:**
- Patch versions (0.3.x): Bug fixes only, no API changes
- Minor versions (0.x.0): New features, backward compatible
- Major versions (x.0.0): Breaking changes (rare - max once per year)

---

## Integration: Synth Imports Loom

### Synth Cargo.toml

```toml
# Synth/Cargo.toml
[workspace]
members = [
    "crates/synth-core",
    "crates/synth-frontend",
    "crates/synth-backend",
    "crates/synth-verify",    # Coq integration
    "crates/synth-cli",
]

[workspace.dependencies]
# Import Loom shared definitions
loom-shared = { version = "0.3", features = ["arm-cortex-m"] }

# Synth-specific dependencies
coq-extracted = { path = "coq/_build/extracted" }  # From Dune build
```

### Using Loom Definitions in Synth

```rust
// crates/synth-backend/src/optimizer.rs

use loom_shared::pipeline::{OptimizationPipeline, Phase};
use loom_shared::isle::peephole_rules;
use loom_shared::cost_model::ARMCostModel;

pub struct SynthOptimizer {
    // Use Loom's battle-tested pipeline
    pipeline: OptimizationPipeline<ARMCostModel>,

    // Synth-specific: Coq-verified transformations
    verified_compiler: CoqExtractedCompiler,
}

impl SynthOptimizer {
    pub fn new() -> Self {
        // Build optimization pipeline using Loom's architecture
        let pipeline = OptimizationPipeline::builder()
            .add_phase(Phase::Peephole(peephole_rules()))
            .add_phase(Phase::StrengthReduction)
            .add_phase(Phase::DeadCodeElimination)
            .add_phase(Phase::RegisterAllocation)
            .build();

        // Load Coq-verified compiler (Synth-specific)
        let verified_compiler = CoqExtractedCompiler::load();

        Self { pipeline, verified_compiler }
    }

    pub fn compile(&self, wasm: &[u8]) -> Result<Vec<u8>> {
        // Phase 1: Loom optimizations (proven, battle-tested)
        let optimized_ir = self.pipeline.optimize(wasm)?;

        // Phase 2: Coq-verified code generation (ASIL D)
        let arm_binary = self.verified_compiler.generate(optimized_ir)?;

        Ok(arm_binary)
    }
}
```

---

## Separation of Concerns

### What Loom Provides

✅ **Optimization Definitions** (MIT)
- ISLE pattern matching rules
- Cost models for ARM Cortex-M4/M33
- Register allocation heuristics
- Instruction selection patterns
- Pipeline architecture (12 phases)

✅ **Test Suite** (MIT)
- 500+ WebAssembly → ARM test cases
- Edge cases and corner cases
- Performance benchmarks

✅ **Documentation** (MIT)
- Optimization theory (papers, blog posts)
- Architecture diagrams
- Contribution guidelines

### What Synth Adds

✅ **Formal Verification** (Proprietary)
- Coq proofs of compiler correctness
- Sail ARM v8-M formal semantics
- Extracted OCaml verified compiler
- Mechanized theorems (151 WebAssembly instructions)

✅ **ISO 26262 Qualification** (Proprietary)
- Tool Qualification Package (TQP)
- Safety Manual
- Hazard Analysis
- Verification Evidence
- Known Limitations documentation
- Traceability matrices

✅ **Commercial Support** (Proprietary)
- Customer support contracts
- Training materials
- Consulting services
- Custom certification assistance

---

## Workflow: Loom Development → Synth Integration

### Step 1: Loom Development (Open Source)

```bash
cd loom/

# Develop new optimization in Loom
git checkout -b feat/new-peephole-opt
vim crates/loom-shared/src/isle/peephole.isle  # Add new ISLE rule
cargo test --package loom-shared                # Test in isolation
cargo test --package loom-optimizer             # Test in Loom context

# Validate with Z3 SMT
cargo test --package loom-verify

# Open source PR process
git commit -m "feat(shared): Add strength reduction for MUL → SHL"
git push origin feat/new-peephole-opt
# Create PR, community review, merge to main
```

### Step 2: Publish loom-shared to crates.io

```bash
cd loom/crates/loom-shared/

# Bump version (semantic versioning)
vim Cargo.toml  # 0.3.0 → 0.3.1

# Publish to crates.io
cargo publish

# Tag release
git tag loom-shared-v0.3.1
git push --tags
```

### Step 3: Update Synth (Private Repo)

```bash
cd Synth/

# Update loom-shared dependency
vim Cargo.toml
# Change: loom-shared = "0.3.0" → "0.3.1"

# Pull new optimizations
cargo update -p loom-shared

# Test integration
cargo test

# Verify Coq proofs still hold
cd coq/
dune build
dune runtest

# If proofs break, update them
vim coq/theories/Compiler.v  # Extend proofs for new opt
dune build @check

# Integration test with Bazel
bazel build --config=asil_d //crates:synth
bazel test --config=asil_d //...

# Commit to Synth private repo
git commit -m "feat: Integrate loom-shared v0.3.1 with new peephole opt"
git push origin main
```

---

## CI/CD Integration

### Loom CI (GitHub Actions - Public)

```yaml
# loom/.github/workflows/ci.yml
name: Loom CI

on: [push, pull_request]

jobs:
  test-shared:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable

      # Test shared crate in isolation
      - name: Test loom-shared
        run: cargo test --package loom-shared

      # Verify no Loom-specific dependencies leaked
      - name: Check dependencies
        run: |
          cd crates/loom-shared
          cargo tree | grep -v "loom-verify" || exit 1

  verify:
    runs-on: ubuntu-latest
    steps:
      # Z3 SMT verification (Loom-specific, not shared)
      - name: Run Z3 verification
        run: cargo test --package loom-verify

  publish-check:
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    steps:
      - name: Dry-run publish
        run: |
          cd crates/loom-shared
          cargo publish --dry-run
```

### Synth CI (Private CI/CD)

```yaml
# Synth/.github/workflows/ci.yml
name: Synth CI

on: [push]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      # Test Rust code
      - name: Test Rust
        run: cargo test

      # Test Coq proofs
      - name: Install Coq
        run: opam install -y coq dune

      - name: Build Coq proofs
        run: |
          cd coq/
          dune build
          dune runtest

      # Verify ASIL D build
      - name: ASIL D build
        run: bazel build --config=asil_d //crates:synth

  dependency-audit:
    runs-on: ubuntu-latest
    steps:
      # Check loom-shared version
      - name: Audit loom-shared
        run: |
          LOOM_VERSION=$(cargo tree -p loom-shared | head -1 | cut -d' ' -f2)
          echo "Using loom-shared version: $LOOM_VERSION"

          # Ensure we're on a stable release (not -alpha, -beta)
          echo "$LOOM_VERSION" | grep -E '^[0-9]+\.[0-9]+\.[0-9]+$' || exit 1
```

---

## Licensing and Legal

### Loom (MIT License)

```
loom/
├── LICENSE                    # MIT License (entire repo)
├── crates/loom-shared/
│   └── LICENSE                # MIT License (explicit for crates.io)
```

**MIT allows:**
- ✅ Use in proprietary software (Synth)
- ✅ Modification
- ✅ Distribution
- ✅ Commercial use
- ✅ Sublicensing

**MIT requires:**
- ✅ Include LICENSE in Synth distribution
- ✅ Attribute Loom in documentation

### Synth (Proprietary)

```
Synth/
├── LICENSE                    # Proprietary license
├── THIRD_PARTY_LICENSES.md    # Include Loom MIT license
└── docs/
    └── ATTRIBUTION.md         # Credit Loom project
```

**Example attribution:**

```markdown
# THIRD_PARTY_LICENSES.md

## loom-shared

Synth uses optimization definitions from the Loom project:
- Project: https://github.com/pulseengine/loom
- Version: 0.3.1
- License: MIT
- Copyright: 2024 PulseEngine

<full MIT license text>
```

---

## Risk Management

### Risk 1: Loom Breaking Changes

**Mitigation:**
- Pin exact versions in Cargo.toml: `loom-shared = "=0.3.1"`
- Vendor loom-shared for critical releases: `cargo vendor`
- Maintain fork at `pulseengine/loom` (private) if needed
- Automated tests detect API breakage

### Risk 2: Optimization Bugs in Loom

**Mitigation:**
- Coq proofs catch semantic bugs (compile-time)
- Extensive test suite (500+ cases)
- Sail validation catches ARM mismatches
- ASIL D qualification process finds issues

### Risk 3: Dependency Supply Chain Attack

**Mitigation:**
- Checksum verification: `cargo verify-project`
- Audit loom-shared releases: Manual code review
- Reproducible builds: Bazel hermetic builds
- Vendor dependencies for production: `bazel vendor`

### Risk 4: Loom Abandonment

**Mitigation:**
- Fork loom-shared to `synth-optimizations` (private)
- MIT license allows indefinite use
- Minimal dependencies (cranelift-isle, wasmparser)
- Core team maintains expertise

---

## Performance Characteristics

### Development Iteration Speed

| Task | Loom (Open) | Synth (Private) |
|------|-------------|-----------------|
| **Add optimization** | Fast (Rust + Z3) | Slow (extend Coq proofs) |
| **Test optimization** | Instant (cargo test) | Hours (Coq rebuild) |
| **Deploy to users** | Days (crates.io) | Months (ISO 26262 audit) |
| **Iterate on bugs** | Fast (community) | Slow (formal proof fixes) |

**Strategy:** Develop and test in Loom first, then port to Synth with proofs

### Build Times

| Configuration | Time | Cached |
|---------------|------|--------|
| **Loom cargo build** | 2-3 min | 10s |
| **Synth cargo build** | 3-4 min | 15s |
| **Coq proofs dune build** | 15-20 min | 30s |
| **Synth Bazel ASIL D** | 25-30 min | 2 min |

---

## Migration Path

### Phase 1: Current State (Week 0)

```
Loom:
  ✅ All optimizations in loom-optimizer/
  ❌ No loom-shared crate yet

Synth:
  ✅ Bazel infrastructure ready
  ❌ No Loom integration yet
  ❌ No Coq proofs yet
```

### Phase 2: Extract loom-shared (Weeks 1-2)

```bash
cd loom/

# Create loom-shared crate
cargo new --lib crates/loom-shared

# Move shared code
mv crates/loom-optimizer/src/isle/ crates/loom-shared/src/
mv crates/loom-optimizer/src/cost_model/ crates/loom-shared/src/
# ... etc

# Update loom-optimizer to depend on loom-shared
vim crates/loom-optimizer/Cargo.toml
# Add: loom-shared = { path = "../loom-shared" }

# Refactor imports
rg "use crate::isle" -l | xargs sed -i 's/use crate::isle/use loom_shared::isle/g'

# Test
cargo test --all

# Publish initial version
cd crates/loom-shared
cargo publish --version 0.3.0
```

### Phase 3: Synth Integration (Weeks 3-4)

```bash
cd Synth/

# Add loom-shared dependency
vim Cargo.toml
# [workspace.dependencies]
# loom-shared = "0.3"

# Create synth-backend using Loom
vim crates/synth-backend/Cargo.toml
# loom-shared = { workspace = true }

# Implement integration
vim crates/synth-backend/src/optimizer.rs
# (See code example above)

# Test
cargo test
bazel build //crates:synth
```

### Phase 4: Coq Proofs for Loom Opts (Months 2-12)

```bash
cd Synth/coq/

# Extend Coq proofs to cover Loom optimizations
vim theories/Compiler.v
# Add theorems for each ISLE rule

# Extract to OCaml
dune build

# Integrate with Bazel
bazel build --config=asil_d //crates:synth
```

---

## Monitoring and Observability

### Track Loom Version in Synth

```rust
// crates/synth-cli/src/main.rs

fn print_version() {
    println!("Synth v{}", env!("CARGO_PKG_VERSION"));
    println!("Using loom-shared v{}", loom_shared::version());
    println!("Coq proofs: {}", coq_extracted::proof_version());
    println!("ASIL Level: D");
}
```

### Dependency Dashboard

```toml
# Synth/.cargo/audit.toml
[advisories]
ignore = []

[dependencies]
loom-shared = { version = "0.3.1", source = "crates.io" }

[report]
format = "json"
output = "qualification/dependency_audit.json"
```

---

## Success Metrics

### Loom (Open Source)

- ✅ 500+ GitHub stars
- ✅ 10+ external contributors
- ✅ 50+ test cases
- ✅ Published to crates.io
- ✅ Used by 5+ downstream projects

### Synth (Commercial)

- ✅ All Loom optimizations have Coq proofs
- ✅ ISO 26262 ASIL D qualification complete
- ✅ 3+ paying customers
- ✅ <10% performance overhead vs Loom
- ✅ Zero miscompilations in production

---

## Timeline

| Milestone | Duration | Owner | Output |
|-----------|----------|-------|--------|
| **Extract loom-shared** | 2 weeks | Loom team | v0.3.0 on crates.io |
| **Synth integration** | 2 weeks | Synth team | Compiles with Loom opts |
| **First 3 proofs** | 3 months | Synth team | 3 ISLE rules verified |
| **20 instruction subset** | 9 months | Synth team | ASIL C candidate |
| **Full 151 instructions** | 18 months | Synth team | ASIL D ready |
| **ISO 26262 qualification** | 24 months | Synth + auditor | ASIL D certified |

---

## Next Steps (Immediate)

1. ✅ **Create loom-shared crate structure** in Loom repo
2. ✅ **Move ISLE rules** to loom-shared
3. ✅ **Publish loom-shared v0.3.0** to crates.io
4. ✅ **Update Synth Cargo.toml** to import loom-shared
5. ✅ **Create synth-backend** wrapper around Loom + Coq
6. ✅ **Write first Coq proof** for one Loom optimization

---

## Summary

**Loom** = Battle-tested optimizations (open source, community-driven, ASIL B)
**Synth** = Formal verification + ISO 26262 (commercial, proprietary, ASIL D)
**loom-shared** = Bridge between them (MIT licensed, versioned, stable)

This architecture:
- ✅ Maximizes code reuse
- ✅ Minimizes Coq proof burden (only verify, don't reimplement)
- ✅ Allows independent development speeds
- ✅ Follows CompCert/CakeML model
- ✅ Satisfies ISO 26262 requirements
- ✅ Enables commercial + open source collaboration

**Result:** World-class optimizations (Loom) + world-class verification (Synth) = ASIL D at reasonable cost
