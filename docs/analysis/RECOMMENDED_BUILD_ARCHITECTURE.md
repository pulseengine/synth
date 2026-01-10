# Recommended Build Architecture for ASIL D

**Based on research findings and proven approaches (CompCert, CakeML)**

---

## The Multi-Build-System Reality

**No single build system handles everything for ASIL D certified compilers.**

CompCert, CakeML, and all verified compilers use **separate build systems**:

```
┌──────────────────────────────────────────────────┐
│ Coq Proofs (Dune/Make - Separate Build)         │
│ ├─ Formalize WebAssembly semantics              │
│ ├─ Formalize ARM semantics (from Sail)          │
│ ├─ Prove compiler correctness theorems          │
│ └─ Extract to OCaml                             │
└──────────────────────────────────────────────────┘
                    ↓
┌──────────────────────────────────────────────────┐
│ Main Build (Bazel)                               │
│ ├─ Rust frontend (rules_rust)                   │
│ ├─ Extracted OCaml compiler (rules_ocaml)       │
│ ├─ C runtime stubs (rules_cc)                   │
│ └─ Link final binary                            │
└──────────────────────────────────────────────────┘
                    ↓
┌──────────────────────────────────────────────────┐
│ Validation (External Tools)                      │
│ ├─ Sail ARM emulator (opam install sail)        │
│ ├─ QEMU for testing                             │
│ └─ ISO 26262 evidence generation                │
└──────────────────────────────────────────────────┘
```

---

## Phase 1: Fix Bazel Proxy (This Week)

### Option A: Try Vendor Mode First
```bash
cd /home/user/Synth

# Attempt to vendor all dependencies
bazel vendor //... 2>&1 | tee vendor.log

# If successful:
echo "common --vendor_dir=vendor_src" >> .bazelrc.local
git add vendor_src/ .bazelrc.local
git commit -m "Vendor Bazel dependencies"

# Build offline:
bazel build //...
```

### Option B: Manual Download (If Vendor Fails)
```bash
# Use the script I created
./scripts/download_bazel_deps.sh

# Add to .bazelrc.local
echo "build --distdir=$HOME/bazel_distdir" >> .bazelrc.local
echo "fetch --distdir=$HOME/bazel_distdir" >> .bazelrc.local

# Test build
bazel build --distdir=$HOME/bazel_distdir //bazel/platforms:all
```

---

## Phase 2: Coq Proof Infrastructure (Month 1-2)

### Use Dune, Not Bazel

**Create `coq/dune-project`:**
```dune
(lang dune 3.0)
(name synth_verification)
(using coq 0.8)
```

**Create `coq/theories/dune`:**
```dune
(coq.theory
  (name Synth)
  (package synth_verification)
  (theories Stdlib))

; Extract compiler to OCaml
(coq.extraction
  (prelude extraction_prelude.v)
  (extracted_modules WasmSemantics ARMSemantics Compiler))
```

**Build separately from Bazel:**
```bash
# Install Coq and dependencies
opam install coq dune coq-stdlib

# Build Coq proofs
cd coq/
dune build

# Extracted OCaml appears in:
# _build/default/theories/*.ml
```

**Why separate build?**
- ✅ Coq changes infrequently (proofs are stable)
- ✅ Dune is the standard (no wheel reinvention)
- ✅ CompCert and CakeML do the same
- ✅ Simpler than forcing Coq into Bazel

---

## Phase 3: Integrate Extracted OCaml into Bazel (Month 2-3)

### Add OBazl to MODULE.bazel
```python
# MODULE.bazel
bazel_dep(name = "rules_ocaml", version = "3.0.0")
bazel_dep(name = "tools_opam", version = "1.0.0")
```

### Reference Extracted Coq Files
```python
# coq/BUILD.bazel
load("@rules_ocaml//ocaml:rules.bzl", "ocaml_library")

# Import Coq-extracted OCaml
ocaml_library(
    name = "verified_compiler",
    srcs = glob([
        "_build/default/theories/*.ml",
        "_build/default/theories/*.mli",
    ]),
    visibility = ["//visibility:public"],
)
```

### Use in Main Binary
```python
# crates/BUILD.bazel
rust_binary(
    name = "synth",
    srcs = ["synth-cli/src/main.rs"],
    deps = [
        ":synth-frontend",      # Rust parser
        "//coq:verified_compiler",  # Coq-extracted compiler
        # ...
    ],
)
```

---

## Phase 4: Sail as Validation Tool (Month 3-4)

### DON'T Integrate Sail into Build

**Instead, use Sail for validation:**

```bash
# Install Sail separately
opam install sail

# Clone ARM Sail specs
git clone https://github.com/ARM-software/sail-arm.git external/sail-arm
cd external/sail-arm

# Build ARM emulator
make aarch64

# Now you have: sail-aarch64-linux executable
```

### Validation Test Suite
```python
# tests/BUILD.bazel
sh_test(
    name = "validate_against_sail",
    srcs = ["validate_against_sail.sh"],
    data = [
        "//crates:synth",  # Our compiler
        "//external/sail-arm:sail-aarch64-linux",  # Sail emulator
        "//validation:wasm_test_suite",
    ],
)
```

**Validation script:**
```bash
#!/bin/bash
# tests/validate_against_sail.sh

for wasm_test in validation/*.wasm; do
    # Compile with Synth
    ./crates/synth "$wasm_test" -o synth_output.elf

    # Compile with Sail emulator
    ./external/sail-arm/sail-aarch64-linux "$wasm_test" -o sail_output.elf

    # Compare outputs
    diff <(./synth_output.elf) <(./sail_output.elf) || {
        echo "MISMATCH: $wasm_test"
        exit 1
    }
done

echo "✓ All tests match Sail semantics"
```

**Why not integrate Sail into build?**
- 40GB RAM required to build ARM ASL → Sail → Coq
- Pre-generated files are 11.7 MB
- Sail changes infrequently (ARM spec stable)
- Use as validation oracle, not build dependency

---

## Phase 5: ASIL D Qualification Evidence (Month 12-15)

### Proof Artifacts
```
qualification/
├── coq_proofs/
│   ├── compiler_correctness.v
│   ├── proof_certificate.txt
│   └── extraction_log.txt
├── validation/
│   ├── sail_comparison_results.txt
│   ├── test_coverage_report.html
│   └── counterexample_tests/
├── tool_qualification/
│   ├── TQP.md  # Tool Qualification Package
│   ├── TOR.md  # Tool Operational Requirements
│   └── verification_evidence.md
└── iso26262/
    ├── hazard_analysis.md
    ├── safety_manual.md
    └── known_limitations.md
```

---

## Directory Structure (Final)

```
Synth/
├── .bazelrc.local          # Proxy workarounds (distdir or vendor)
├── MODULE.bazel            # Bazel deps (Rust + OCaml)
├── vendor_src/             # Vendored dependencies (if using vendor mode)
│
├── crates/                 # Rust frontend (Bazel build)
│   ├── synth-frontend/     # WASM parsing
│   ├── synth-backend/      # ARM codegen stub
│   └── synth-cli/          # CLI entry point
│
├── coq/                    # Coq proofs (Dune build - SEPARATE)
│   ├── dune-project
│   ├── theories/
│   │   ├── WasmSemantics.v
│   │   ├── ARMSemantics.v  # From Sail
│   │   ├── Compiler.v
│   │   └── Correctness.v
│   ├── _build/default/theories/*.ml  # Extracted OCaml
│   └── BUILD.bazel         # Import extracted .ml into Bazel
│
├── external/               # External validation tools
│   ├── sail-arm/           # Sail ARM emulator (opam + make)
│   └── arm-asl/            # ARM spec (reference only)
│
├── scripts/
│   ├── download_bazel_deps.sh  # Proxy workaround helper
│   └── validate_sail.sh        # Validation against Sail
│
├── qualification/          # ISO 26262 artifacts
│   ├── coq_proofs/
│   ├── validation/
│   └── tool_qualification/
│
└── docs/
    ├── BAZEL_INTEGRATION_RESEARCH.md  # This research
    ├── RECOMMENDED_BUILD_ARCHITECTURE.md  # This document
    └── ASILD_SAIL_MIGRATION_PLAN.md  # Your existing plan
```

---

## Build Commands Summary

### Development (Fast Iteration)
```bash
# Rust frontend changes
cargo build && cargo test

# Coq proof changes
cd coq/
dune build
dune test

# Full integration build
bazel build //crates:synth
```

### Production (ASIL D)
```bash
# 1. Rebuild Coq proofs (if changed)
cd coq/ && dune clean && dune build

# 2. Build with Bazel (includes extracted OCaml)
bazel build --config=asil_d //crates:synth

# 3. Validate against Sail
bazel test //tests:validate_against_sail

# 4. Generate qualification artifacts
bazel build //qualification:all
```

### Cross-Compilation
```bash
# ARM Cortex-M4
bazel build --platforms=//bazel/platforms:cortex_m4 //crates:synth

# With ASIL D verification
bazel build --config=asil_d \
  --platforms=//bazel/platforms:asil_d_cortex_m4 \
  //crates:synth
```

---

## Timeline Estimate

| Phase | Duration | Build System | Key Deliverable |
|-------|----------|--------------|-----------------|
| **1. Fix Proxy** | 1 day | Bazel | Offline builds work |
| **2. Add OBazl** | 1 week | Bazel | OCaml integration ready |
| **3. Coq Infrastructure** | 2-4 weeks | Dune | Proof framework setup |
| **4. First Proofs** | 2-3 months | Dune | 3 operations proven correct |
| **5. Full Verification** | 6-9 months | Dune | All 151 operations proven |
| **6. Sail Validation** | 2-4 weeks | opam/make | Emulator tests passing |
| **7. Integration** | 2-4 weeks | Bazel | Rust + OCaml unified build |
| **8. Qualification** | 3-4 months | Multiple | ISO 26262 package complete |

**Total: 12-18 months to ASIL D certification**

---

## Key Takeaways

1. ✅ **Use Bazel for Rust** - Already configured
2. ✅ **Use OBazl for OCaml** - Integrate extracted Coq
3. ✅ **Use Dune for Coq** - Don't force into Bazel
4. ✅ **Use Sail for validation** - Not build dependency
5. ✅ **Fix proxy NOW** - Vendor mode or distdir
6. ✅ **Follow CompCert/CakeML** - Proven approach

**This is the realistic, proven path to ASIL D.**

No need to invent new Bazel rules for Coq. Use what works.
