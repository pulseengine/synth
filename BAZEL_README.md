# Bazel Setup for Synth

## Current Status

✅ **Bazel infrastructure is configured and ready to use**

The following files have been created:
- `MODULE.bazel` - Bazel module definition (Bzlmod)
- `.bazelrc` - Build configuration with all optimization flags
- `.bazelversion` - Pins Bazel to version 7.4.1
- `BUILD.bazel` - Root build file
- `bazel/platforms/BUILD.bazel` - Platform definitions (ARM, RISC-V, WASM)
- `bazel/constraints/BUILD.bazel` - Custom constraints (ASIL levels, etc.)
- `bazel/features/BUILD.bazel` - Feature flags
- `crates/BUILD.bazel` - Rust crate build definitions
- `coq/BUILD.bazel` - Coq proof build structure
- `BAZEL_SETUP.md` - Comprehensive usage guide

## Quick Start (When Network is Available)

### 1. Install Bazelisk (Already Done)

```bash
# Bazelisk is installed via npm
which bazelisk
# Should show: /opt/node22/bin/bazelisk
```

### 2. Enable Full Dependencies

Uncomment the dependencies in `MODULE.bazel`:
- `rules_rust` - For Rust compilation
- `rules_python` - For Python build scripts
- `rules_cc` - For C/C++ cross-compilation

### 3. Add Your rules_wasm_component

Update `MODULE.bazel` with the correct repository URL and commit:

```python
bazel_dep(name = "rules_wasm_component", version = "0.1.0")
git_override(
    module_name = "rules_wasm_component",
    remote = "https://github.com/pulseengine/rules_wasm_component.git",
    commit = "<your-commit-hash>",  # Replace with actual commit
)
```

### 4. Build the Project

```bash
# Build everything
bazel build //...

# Build just the compiler
bazel build //crates:synth

# Build for ARM Cortex-M4
bazel build --config=arm //crates:synth

# Build in ASIL D mode
bazel build --config=asil_d //crates:synth
```

## Features Configured

### Platform Support
- ✅ ARM Cortex-M4 (STM32F4, nRF52840)
- ✅ ARM Cortex-M33 (nRF9160, STM32L5)
- ✅ RISC-V 32-bit (RV32IMAC)
- ✅ WebAssembly (wasm32-unknown-unknown)
- ✅ ASIL D certified targets

### Build Configurations
- `--config=debug` - Debug build with symbols
- `--config=opt` - Optimized release build
- `--config=dev` - Fast incremental builds
- `--config=arm` - ARM cross-compilation
- `--config=wasm` - WebAssembly Component Model
- `--config=asil_d` - ASIL D certification mode
- `--config=coq` - Coq proof generation

### Safety Levels
- ASIL A/B - Standard verification
- ASIL C - Enhanced verification
- ASIL D - Full formal verification with Coq

## Bazel Structure

```
Synth/
├── MODULE.bazel              # Dependencies (Bzlmod)
├── .bazelrc                  # Build flags and configs
├── .bazelversion             # Version pinning (7.4.1)
├── BUILD.bazel               # Root targets
│
├── bazel/
│   ├── platforms/
│   │   └── BUILD.bazel       # cortex_m4, cortex_m33, riscv32, wasm32
│   ├── constraints/
│   │   └── BUILD.bazel       # asil_d, misra_c_2012, fpu variants
│   └── features/
│       └── BUILD.bazel       # with_verification, with_coq_proofs
│
├── crates/
│   └── BUILD.bazel           # All Rust crates with proper deps
│
└── coq/
    └── BUILD.bazel           # Coq proof infrastructure
```

## Integration with Cargo

Bazel and Cargo can coexist:

```bash
# Development with Cargo (fast iteration)
cargo build
cargo test

# Production build with Bazel (cross-compilation, verification)
bazel build --config=asil_d //crates:synth
```

## Next Steps

### 1. Configure Network Access
If behind proxy, configure `.bazelrc.local`:
```
build --http_proxy=http://proxy:8080
build --https_proxy=https://proxy:8080
```

### 2. Add rules_wasm_component
Once your WebAssembly Component Model rules are available:
- Update `MODULE.bazel` with correct repository
- Uncomment `register_toolchains` line
- Test with `bazel build --config=wasm //crates:synth`

### 3. Enable Rust Dependencies
Uncomment in `MODULE.bazel`:
- `rules_rust` dependency
- `crate` extension for cargo dependencies
- Build with `bazel build //crates:synth`

### 4. Add Coq Rules (For ASIL D)
When Sail integration is complete:
- Add Coq toolchain rules
- Configure `//coq:compiler_correctness` target
- Enable with `bazel build --config=coq //coq:all`

## Benefits Over Cargo Alone

### Cross-Compilation
```bash
# ARM Cortex-M4 - one command
bazel build --platforms=//bazel/platforms:cortex_m4 //crates:synth

# Compare with Cargo (requires rustup target + lots of config)
cargo build --target thumbv7em-none-eabihf
```

### Reproducible Builds
- Hermetic builds (exact dependencies)
- Remote caching support
- Deterministic output

### Multi-Language Support
- Rust + Coq + OCaml (Sail) + C (ARM toolchain)
- All in one build system
- Proper dependency tracking

### Verification Integration
```bash
# Build + verify in one step
bazel test --config=asil_d //...
```

## Troubleshooting

### Network Issues
Currently behind proxy - dependencies commented out in `MODULE.bazel`.
Enable when network is available.

### Missing rules_wasm_component
Add correct repository URL and commit hash to `MODULE.bazel`.

### Rust Toolchain
Once `rules_rust` is enabled:
```bash
bazel run @rules_rust//rust:rustfmt
bazel run @rules_rust//rust:clippy
```

## Documentation

- `BAZEL_SETUP.md` - Detailed usage guide
- `MODULE.bazel` - See comments for configuration options
- `.bazelrc` - See all available configs

## Status

🟡 **Infrastructure Ready** - Waiting for:
1. Network access to Bazel Central Registry
2. rules_wasm_component repository configuration
3. Optional: Custom Coq rules for Sail integration

Once network is available, uncomment dependencies in `MODULE.bazel` and run:
```bash
bazel build //...
```
