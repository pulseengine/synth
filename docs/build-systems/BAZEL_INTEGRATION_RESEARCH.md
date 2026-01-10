# Bazel Integration Research Report
## Coq, OCaml, Sail, and Proxy Workarounds

**Date**: 2025-11-20
**Project**: Synth - WebAssembly Component Synthesizer
**Research Focus**: Bazel integration for formal verification toolchain

---

## Executive Summary

This research investigated Bazel integration options for Coq formal verification, OCaml (Sail) compilation, and proxy authentication workarounds. Key findings:

- ✅ **OCaml + Bazel**: Mature solution exists (OBazl)
- ⚠️ **Coq + Bazel**: Experimental only, no production-ready rules
- ❌ **Sail + Bazel**: No existing integration found
- ✅ **Proxy Workarounds**: Multiple solutions available (distdir, vendor mode)

---

## 1. Bazel Rules for Coq

### Finding: No Production-Ready Solution

**Status**: Experimental efforts exist, but no maintained `rules_coq` package.

### Evidence

1. **Coq Discourse Discussion** (2021)
   - URL: https://coq.discourse.group/t/building-coq-with-bazel-need-help-with-plugins/1257
   - Someone attempted to build Coq itself with Bazel using OBazl (OCaml rules)
   - Issues: "Building OCaml libraries is not easy" and plugin compilation problems
   - Conclusion: Effort was experimental, not completed

2. **Search Results**
   - No `rules_coq` repository found on GitHub
   - No Bazel Central Registry (BCR) entry for Coq
   - coq-community has no official Bazel integration project

### Current Coq Build Ecosystem

**Primary Build Systems**:
- **Dune**: Now the standard for Coq + OCaml projects
- **coq_makefile**: Traditional Coq build tool
- **opam**: Package manager

**Dune Support for Coq** (Mature):
```dune
; Build Coq proofs
(coq.theory
  (name MyTheory)
  (theories Stdlib))

; Extract to OCaml
(coq.extraction
  (prelude extraction_prelude.v)
  (extracted_modules MyProof_ml))
```

### Why No `rules_coq`?

1. **Complex toolchain**: Coq compilation involves OCaml extraction, dependencies on Coq libraries, version-specific plugins
2. **Small market**: Most Coq users are academics using dune/opam
3. **Dune is sufficient**: Dune already provides good Coq support
4. **OBazl complexity**: Even building OCaml with Bazel is "not easy"

### Workaround Options

#### Option 1: Use `rules_foreign_cc` to Wrap Dune
```python
# BUILD.bazel
load("@rules_foreign_cc//foreign_cc:defs.bzl", "make")

make(
    name = "coq_proofs",
    lib_source = "@coq_project//:all",
    out_include_dir = "include",
    targets = ["build"],  # dune build
)
```

Repository: https://github.com/bazelbuild/rules_foreign_cc

#### Option 2: Custom Genrule
```python
genrule(
    name = "compile_coq",
    srcs = glob(["theories/**/*.v"]),
    outs = ["extracted.ml"],
    cmd = """
        cd $$(dirname $(location theories/Main.v))
        coqc -R . MyTheory *.v
        # Extract to OCaml
    """,
)
```

#### Option 3: Separate Coq Build + Import
```bash
# Outside Bazel
cd coq/
dune build
dune install

# In Bazel: use extracted OCaml files
# BUILD.bazel
ocaml_library(
    name = "extracted_proofs",
    srcs = glob(["_build/default/theories/*.ml"]),
)
```

### Recommendation for Synth

**Use Separate Build for Coq, Import Extracted OCaml**:

```bash
# coq/dune-project
(lang dune 3.0)
(name synth_verification)

# coq/theories/dune
(coq.theory
  (name Synth)
  (theories Stdlib))

(coq.extraction
  (prelude extraction.v)
  (extracted_modules Compiler))

# Build separately
cd coq/
dune build

# Copy extracted .ml files to Rust FFI or use with OBazl
```

**Why**: Coq build is infrequent (proof changes), not worth Bazel complexity.

---

## 2. Bazel Rules for OCaml (Sail is OCaml)

### Finding: Mature Solution Exists - OBazl

**Status**: ✅ Production-ready OCaml build rules for Bazel

### OBazl Toolsuite

**Repository**: https://github.com/obazl/rules_ocaml
**Documentation**: https://obazl.github.io/docs_obazl/
**Latest Version**: 3.0.0 (February 2025)
**Maintenance**: Active

**Components**:
1. **rules_ocaml** - Core Bazel ruleset for OCaml
2. **tools_opam** - OPAM package integration

### Usage Example

#### MODULE.bazel
```python
bazel_dep(name = "rules_ocaml", version = "3.0.0")
bazel_dep(name = "tools_opam", version = "1.0.0")
```

#### BUILD.bazel
```python
load("@rules_ocaml//ocaml:rules.bzl", "ocaml_library", "ocaml_binary")

ocaml_library(
    name = "mylib",
    srcs = ["mylib.ml"],
    deps = ["@opam//pkg:lwt"],  # OPAM packages
)

ocaml_binary(
    name = "myapp",
    srcs = ["main.ml"],
    deps = [":mylib"],
)
```

### Demo Repository

**Examples**: https://github.com/obazl/demos_obazl

```bash
# Clone and run demo
git clone https://github.com/obazl/demo_hello.git
cd demo_hello
bazel run bin:greetings
bazel test test
```

### Features

- ✅ OPAM integration
- ✅ PPX preprocessors
- ✅ C stubs
- ✅ Findlib/ocamlfind support
- ✅ Compilation modes (bytecode, native)
- ✅ Module dependencies

### Alternative: jin/rules_ocaml

**Repository**: https://github.com/jin/rules_ocaml
**Status**: "Very experimental"
**Recommendation**: Use OBazl instead

---

## 3. Sail-Specific Bazel Integration

### Finding: No Bazel Integration Exists

**Sail Repository**: https://github.com/rems-project/sail
**Build System**: opam + OCaml standard toolchain
**Installation**: `opam install sail`

### What Sail Provides

Sail is an ISA specification language that generates:
- **C emulators** - Executable processor simulators
- **OCaml emulators** - For integration with OCaml tools
- **Coq definitions** - For theorem proving (see Section 3.1)
- **Isabelle/HOL4** - Other proof assistants

### Sail Workflow (No Bazel)

```bash
# Install Sail
opam install sail

# Generate Coq from ARM specifications
sail -coq arm_spec.sail -o arm_generated.v

# Or generate C emulator
sail -c arm_spec.sail -o arm_emulator.c
```

### ARM ASL → Sail → Coq Toolchain

**Paper**: "ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS" (POPL 2019)
**URL**: https://www.cl.cam.ac.uk/~pes20/sail/sail-popl2019.pdf

**Toolchain**:
1. ARM Architecture Specification Language (ASL) - ARM's internal spec
2. `asl_to_sail` - Translation tool (part of Sail)
3. Sail - ISA specification language
4. Backends: Coq, C, OCaml, Isabelle, HOL4

### ARM Sail Repository

**Official ARM Specs in Sail**:
https://github.com/ARM-software/sail-arm

**Pre-generated Coq Files**:
- Located at: `arm-v8.5-a/snapshots/coq/`
- Files:
  - `aarch64.v` - 11.7 MB (full ARMv8.5-A semantics)
  - `aarch64_types.v` - 2.5 MB
  - Library files for Sail→Coq support

**Build Requirements**:
- 40 GB RAM (!!) - per ARM Sail README
- Coq 8.9.1 (outdated)
- BBV library (not in opam)

### Challenges for Bazel Integration

1. **No Bazel support in Sail project** - Uses opam/dune
2. **Massive generated files** - 11.7 MB Coq files impractical for direct use
3. **Toolchain complexity** - ASL → Sail → Coq pipeline requires Sail compiler
4. **Version constraints** - Old Coq version, unavailable dependencies

### Recommended Approach for Synth

**Per SAIL_FINDINGS_AND_STRATEGY.md** (already in repo):

**Don't integrate Sail Coq directly into Bazel. Instead**:

1. **Use Sail C emulator for validation**:
   ```bash
   cd external/sail-arm
   make aarch64  # Generates C emulator
   # Use for testing, not build integration
   ```

2. **Validate our compiler against Sail emulator**:
   ```bash
   # Extract our Coq compiler to OCaml
   cd coq/
   dune build

   # Run test suite comparing outputs
   ./test_harness \
     --our-compiler extracted/compiler.ml \
     --sail-emulator external/sail-arm/aarch64 \
     --wasm-tests wasm-spec-tests/
   ```

3. **Document semantic correspondence** (not formal proof):
   - Which ARM instructions we use
   - Test coverage against Sail emulator
   - ISO 26262 validation evidence

**Why**: Sail is a validation tool, not a build dependency.

---

## 4. Bazel Proxy Workarounds

### Finding: Multiple Solutions for Authenticated Proxies

Your current issue (from BAZEL_STATUS.md):
```
HTTP_PROXY=http://container_...:jwt_<token>@21.0.0.57:15004
HTTPS_PROXY=http://container_...:jwt_<token>@21.0.0.57:15004

Error: "Unable to tunnel through proxy.
        Proxy returns 'HTTP/1.1 401 Unauthorized'"
```

**Root Cause**: Bazel's Java HTTP client doesn't support JWT tokens in proxy URLs.

### Solution 1: --distdir (Manual Download)

**Most Reliable for Authenticated Proxies**

#### How It Works
Bazel looks in local directories before downloading.

#### Steps

1. **Identify what Bazel needs**:
   ```bash
   # Run build, capture download URLs from error
   bazel build //... 2>&1 | grep "https://"
   ```

2. **Download manually using curl/wget** (which DO work with proxy):
   ```bash
   mkdir -p ~/bazel_distdir

   # Download each dependency manually
   curl https://github.com/bazelbuild/rules_rust/archive/0.54.1.tar.gz \
     -o ~/bazel_distdir/rules_rust-0.54.1.tar.gz

   # Bazel expects filename = URL basename
   ```

3. **Use --distdir flag**:
   ```bash
   bazel build --distdir=$HOME/bazel_distdir //...
   ```

4. **Make permanent in .bazelrc**:
   ```bash
   # .bazelrc.local
   build --distdir=/home/user/bazel_distdir
   fetch --distdir=/home/user/bazel_distdir
   ```

#### Automation Script
```bash
#!/bin/bash
# download_bazel_deps.sh

DISTDIR="$HOME/bazel_distdir"
mkdir -p "$DISTDIR"

# List of known dependencies from MODULE.bazel
DEPS=(
  "https://github.com/bazelbuild/rules_rust/archive/0.54.1.tar.gz"
  "https://github.com/bazelbuild/bazel-skylib/releases/download/1.7.1/bazel-skylib-1.7.1.tar.gz"
  # Add others as needed
)

for url in "${DEPS[@]}"; do
  filename=$(basename "$url")
  echo "Downloading $filename..."
  curl -L "$url" -o "$DISTDIR/$filename"
done

echo "Done! Run: bazel build --distdir=$DISTDIR //..."
```

### Solution 2: Vendor Mode (Bazel 7+)

**Best for Bzlmod + Offline Builds**

#### How It Works
Downloads all dependencies to a local vendor directory.

#### Steps

1. **Configure vendor directory**:
   ```bash
   # .bazelrc.local
   common --vendor_dir=vendor_src
   ```

2. **One-time download** (on network that works, or using Solution 1):
   ```bash
   # Download all dependencies for specific targets
   bazel vendor //...

   # Or vendor specific repos
   bazel vendor --repo=rules_rust //...
   ```

3. **Commit vendor directory** (optional):
   ```bash
   git add vendor_src/
   git commit -m "Vendor Bazel dependencies for offline builds"
   ```

4. **Build offline**:
   ```bash
   bazel build --vendor_dir=vendor_src //...
   # No network access needed!
   ```

#### Vendor Directory Structure
```
vendor_src/
├── _registries/          # BCR registry files
├── rules_rust~0.54.1/    # Vendored repos
├── bazel_skylib~1.7.1/
└── ...
```

**Advantages**:
- ✅ Works with Bzlmod (MODULE.bazel)
- ✅ Version controlled
- ✅ True offline builds
- ✅ No manual URL management

### Solution 3: Repository Cache

**Share downloads across workspaces**

```bash
# .bazelrc.local
build --repository_cache=/home/user/.bazel_repo_cache

# First build downloads to cache
bazel build //...

# Subsequent builds reuse cache (even in other projects)
bazel build //...
```

**Limitations**: Still needs to download once.

### Solution 4: local_repository (Last Resort)

**For dependencies that can't be vendored**

```python
# MODULE.bazel
# Comment out: bazel_dep(name = "rules_rust", version = "0.54.1")

# Create WORKSPACE file (even with Bzlmod)
# WORKSPACE
local_repository(
    name = "rules_rust",
    path = "/home/user/external/rules_rust-0.54.1",
)
```

### Solution 5: WORKSPACE Instead of MODULE.bazel

**Fallback if Bzlmod has proxy issues**

```bash
# Disable Bzlmod
bazel build --noenable_bzlmod //...
```

Create `WORKSPACE`:
```python
# WORKSPACE
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

http_archive(
    name = "rules_rust",
    sha256 = "...",
    urls = ["file:///home/user/bazel_distdir/rules_rust-0.54.1.tar.gz"],
)
```

**Note**: WORKSPACE is deprecated but may handle proxies differently.

### Comparison Matrix

| Solution | Proxy Issues | Offline | Bzlmod | Effort |
|----------|--------------|---------|--------|--------|
| --distdir | ✅ Bypasses | ✅ Yes | ✅ Yes | Medium |
| Vendor mode | ✅ One-time | ✅ Yes | ✅ Yes | Low |
| Repo cache | ⚠️ Helps | ❌ No | ✅ Yes | Low |
| local_repository | ✅ Bypasses | ✅ Yes | ⚠️ Mixed | High |
| WORKSPACE | ⚠️ Maybe | ⚠️ Partial | ❌ No | High |

### Recommended Solution for Synth

**Use Vendor Mode** (cleanest for your use case):

```bash
# One-time setup (on machine with working network OR using curl manually)
mkdir -p vendor_src
bazel vendor //...

# Add to .bazelrc.local
echo "common --vendor_dir=vendor_src" >> .bazelrc.local

# Commit vendored dependencies
git add vendor_src/ .bazelrc.local
git commit -m "Vendor Bazel dependencies for authenticated proxy environment"

# From now on, builds work offline
bazel build //...
```

**Fallback if vendor fails**: Use `--distdir` with manual curl downloads.

---

## 5. CompCert/CakeML Bazel Examples

### Finding: No Bazel Integration Found

### CompCert

**Repository**: https://github.com/AbsInt/CompCert
**Website**: https://compcert.org
**Build System**: configure + Make + Coq

**What it is**:
- Formally verified C compiler (Coq proofs)
- Targets: ARM, PowerPC, RISC-V, x86
- Proof: Compiled code behaves exactly as C semantics prescribe

**Build Process**:
```bash
./configure arm-linux
make
# Re-checks all Coq proofs
# Extracts OCaml from Coq
# Compiles OCaml to ccomp binary
```

**No Bazel Integration Found**:
- Uses traditional autotools + Make
- Coq + OCaml extraction
- Some users report using Meson (not Bazel)

**Reference**: https://cullmann.dev/posts/cmake-meson-compcert/

### CakeML

**Repository**: https://github.com/CakeML/cakeml
**Website**: https://cakeml.org
**Build System**: Holmake (HOL4's build tool)

**What it is**:
- Verified ML compiler and runtime
- Written and verified in HOL4 (not Coq)
- Targets: x86, ARM, RISC-V, etc.

**Build Process**:
```bash
# Requires HOL4 theorem prover
Holmake
# Builds all proofs and extracts code
```

**Coq Integration**:
- CakeML uses HOL4, not Coq
- Issue #579: Request for Coq version exists, not completed
- Some work on Isabelle/HOL → CakeML

**No Bazel Integration Found**:
- Academic project using HOL4 tools
- Not designed for industry build systems

### Why No Bazel Integration?

1. **Academic Tools**: CompCert and CakeML are research projects
2. **Proof Assistant Native**: Coq/HOL4 have their own build tools
3. **Infrequent Builds**: Proofs change rarely, not CI/CD focused
4. **Small User Base**: Verified compiler users are mostly academics

### What We Can Learn

**CompCert Approach**:
```
Coq proofs → Extract to OCaml → Compile OCaml → ccomp binary
```

**CakeML Approach**:
```
HOL4 proofs → Export to SML/OCaml → Compile → Binary
```

**Common Pattern**:
1. Proof assistant (Coq/HOL4) for verification
2. Extraction to functional language (OCaml/SML)
3. Native compiler for extracted code
4. Separate build systems for proofs vs. production

### Recommendation for Synth

**Follow Similar Pattern**:

```
Phase 1: Coq Proofs (separate build)
├── Coq compiler correctness proofs
├── dune build  # Not Bazel
└── Extract to OCaml → compiler.ml

Phase 2: Production Compiler (Bazel)
├── Take extracted OCaml (compiler.ml)
├── Build with Bazel + OBazl
├── Link with Rust frontend (Bazel rules_rust)
└── Ship as binary
```

**Why Separate**:
- Coq proofs: Infrequent changes, complex toolchain
- Production build: Frequent iterations, need fast CI

**Integration Point**: Extracted OCaml files

---

## 6. Concrete Action Plan for Synth

### Phase 1: Fix Proxy Issues (This Week)

#### Option A: Vendor Mode (Recommended)
```bash
# Step 1: Download dependencies using curl (bypasses Bazel proxy issue)
cd /home/user/Synth

# Step 2: Manually download what Bazel needs
mkdir -p /tmp/bazel_manual

# Download rules_rust
curl -L https://github.com/bazelbuild/rules_rust/archive/0.54.1.tar.gz \
  -o /tmp/bazel_manual/0.54.1.tar.gz

# Download bazel_skylib
curl -L https://github.com/bazelbuild/bazel-skylib/releases/download/1.7.1/bazel-skylib-1.7.1.tar.gz \
  -o /tmp/bazel_manual/bazel-skylib-1.7.1.tar.gz

# Step 3: Use distdir temporarily
bazel build --distdir=/tmp/bazel_manual //...

# Step 4: Once working, vendor everything
bazel vendor //...

# Step 5: Enable vendor mode permanently
echo "common --vendor_dir=vendor_src" >> .bazelrc.local

# Step 6: Commit
git add vendor_src/ .bazelrc.local
git commit -m "Vendor Bazel dependencies for offline builds"
```

#### Option B: Pure Distdir
```bash
# Create permanent distdir
mkdir -p ~/bazel_distdir

# Add to .bazelrc.local
echo "build --distdir=$HOME/bazel_distdir" >> .bazelrc.local
echo "fetch --distdir=$HOME/bazel_distdir" >> .bazelrc.local

# Download dependencies as needed when builds fail
# (See download_bazel_deps.sh script above)
```

### Phase 2: OCaml/Sail Integration (Month 1)

#### Add OBazl for OCaml Support
```python
# MODULE.bazel (add these)
bazel_dep(name = "rules_ocaml", version = "3.0.0")
bazel_dep(name = "tools_opam", version = "1.0.0")
```

#### Build Sail Separately
```bash
# Don't integrate Sail into Bazel
# Use as external validation tool

# Install Sail via opam
opam install sail

# Build ARM emulator for validation
cd external/sail-arm
make aarch64

# Use for testing, not as build dependency
```

### Phase 3: Coq Proofs (Separate Build)

#### Use Dune for Coq
```bash
# coq/dune-project
cat > coq/dune-project <<EOF
(lang dune 3.0)
(name synth_verification)
(using coq 0.8)
EOF

# coq/theories/dune
cat > coq/theories/dune <<EOF
(coq.theory
  (name Synth)
  (package synth_verification)
  (theories Stdlib))

(coq.extraction
  (prelude Extraction/CompilerExtract.v)
  (extracted_modules Compiler WasmSemantics ArmSemantics))
EOF

# Build with dune (not Bazel)
cd coq/
dune build
dune install
```

#### Import Extracted OCaml to Bazel
```python
# coq/BUILD.bazel
load("@rules_ocaml//ocaml:rules.bzl", "ocaml_library")

# Manually copy extracted files from dune build
ocaml_library(
    name = "extracted_compiler",
    srcs = glob(["_build/default/theories/extraction/*.ml"]),
    visibility = ["//visibility:public"],
)
```

### Phase 4: Integration (Month 2)

#### Rust + OCaml FFI via Bazel
```python
# crates/BUILD.bazel
rust_library(
    name = "synth-core",
    srcs = glob(["synth-core/src/**/*.rs"]),
    deps = [
        "//coq:extracted_compiler",  # OCaml from Coq
    ],
)
```

Or:

#### Pure Rust Implementation
```rust
// Use Coq proofs as specification
// Implement in Rust for performance
// Validate with property-based tests matching Coq theorems
```

---

## 7. Summary of Findings

### What Exists

| Tool | Bazel Support | Maturity | Repository |
|------|---------------|----------|------------|
| **OCaml** | ✅ Yes (OBazl) | Production | https://github.com/obazl/rules_ocaml |
| **Coq** | ⚠️ Experimental | Proof-of-concept | None official |
| **Sail** | ❌ No | N/A | Use opam |
| **CompCert** | ❌ No | N/A | Use Make |
| **CakeML** | ❌ No | N/A | Use Holmake |

### Proxy Solutions

| Solution | Works with JWT | Offline | Complexity |
|----------|----------------|---------|------------|
| Vendor mode | ✅ Yes (one-time) | ✅ Full | Low |
| --distdir | ✅ Yes (manual curl) | ✅ Full | Medium |
| Repo cache | ⚠️ First build needs network | ❌ No | Low |
| local_repository | ✅ Yes | ✅ Full | High |

### Recommended Architecture

```
┌─────────────────────────────────────────────────────┐
│ Coq Proofs (dune build - separate from Bazel)      │
│ - WasmSemantics.v                                   │
│ - ArmSemantics.v                                    │
│ - Compilation.v                                     │
│ - CorrectnessComplete.v                             │
│ └─→ Extract to OCaml (compiler.ml)                  │
└─────────────────────────────────────────────────────┘
                        ↓
┌─────────────────────────────────────────────────────┐
│ Bazel Build (rules_rust + rules_ocaml)              │
│ - Rust frontend (WASM parsing)                      │
│ - OCaml extracted compiler (from Coq)               │
│ - ARM code generation                               │
│ - Link to final binary                              │
└─────────────────────────────────────────────────────┘
                        ↓
┌─────────────────────────────────────────────────────┐
│ Validation (external tools)                         │
│ - Sail ARM emulator (opam install sail)             │
│ - Test suite comparing outputs                      │
│ - ISO 26262 certification evidence                  │
└─────────────────────────────────────────────────────┘
```

---

## 8. References

### Official Documentation
- **Bazel Vendor Mode**: https://bazel.build/external/vendor
- **Bazel Proxy Config**: https://bazel.build/external/advanced
- **rules_foreign_cc**: https://github.com/bazelbuild/rules_foreign_cc

### OCaml + Bazel
- **OBazl Guide**: https://obazl.github.io/docs_obazl/
- **rules_ocaml**: https://github.com/obazl/rules_ocaml
- **Demo Repository**: https://github.com/obazl/demos_obazl

### Coq Ecosystem
- **Dune Coq Support**: https://dune.readthedocs.io/en/stable/coq.html
- **Coq Extraction**: https://coq.inria.fr/doc/V8.18.0/refman/addendum/extraction.html

### Sail and ARM
- **Sail GitHub**: https://github.com/rems-project/sail
- **ARM Sail Specs**: https://github.com/ARM-software/sail-arm
- **Sail POPL 2019 Paper**: https://www.cl.cam.ac.uk/~pes20/sail/sail-popl2019.pdf

### Verified Compilers
- **CompCert**: https://compcert.org
- **CakeML**: https://cakeml.org
- **CompCert GitHub**: https://github.com/AbsInt/CompCert
- **CakeML GitHub**: https://github.com/CakeML/cakeml

### Bazel Proxy Discussions
- **Issue #14675**: https://github.com/bazelbuild/bazel/issues/14675
- **Issue #6196**: https://github.com/bazelbuild/bazel/issues/6196
- **Vendor Mode Discussion**: https://github.com/bazelbuild/bazel/discussions/19004

---

## 9. Immediate Next Steps

### This Week: Fix Bazel Builds

```bash
# 1. Enable vendor mode
bazel vendor //...
echo "common --vendor_dir=vendor_src" >> .bazelrc.local

# 2. Test build
bazel build //...

# 3. If vendor fails, use distdir:
mkdir -p ~/bazel_distdir
# Download deps manually with curl
bazel build --distdir=~/bazel_distdir //...
```

### Next Week: Add OCaml Support

```python
# MODULE.bazel
bazel_dep(name = "rules_ocaml", version = "3.0.0")
bazel_dep(name = "tools_opam", version = "1.0.0")
```

### Month 1: Coq Extraction Pipeline

```bash
# Setup dune for Coq
cd coq/
cat > dune-project << 'EOF'
(lang dune 3.0)
(name synth_verification)
(using coq 0.8)
EOF

# Build and extract
dune build
dune exec -- coqc -extraction ...
```

### Month 2: Validation Against Sail

```bash
# Install Sail
opam install sail

# Build ARM emulator
cd external/sail-arm
make aarch64

# Create test harness
./validation/test_against_sail.sh
```

---

**End of Research Report**
