# Bazel Build System Setup

This document describes the Bazel build system configuration for Synth.

## Quick Start

### Prerequisites

```bash
# Bazelisk is already installed via npm
# Check version:
bazelisk version
```

### Build the Project

```bash
# Build all targets
bazel build //...

# Build just the compiler
bazel build //crates:synth

# Build with optimizations
bazel build --config=opt //crates:synth

# Build for ARM Cortex-M4
bazel build --config=arm //crates:synth
```

### Run Tests

```bash
# Run all tests
bazel test //...

# Run integration tests
bazel test //crates:integration_tests

# Run with verification enabled
bazel test --define=verification=full //crates/synth-verify:all
```

### Cross-Compilation

```bash
# ARM Cortex-M4 (STM32F4, nRF52840)
bazel build --platforms=//bazel/platforms:cortex_m4 //crates:synth

# ARM Cortex-M33 (nRF9160)
bazel build --platforms=//bazel/platforms:cortex_m33 //crates:synth

# RISC-V 32-bit
bazel build --platforms=//bazel/platforms:riscv32 //crates:synth

# WebAssembly Component Model
bazel build --config=wasm //crates:synth
```

### ASIL D Mode

```bash
# Build with ASIL D strict settings
bazel build --config=asil_d //crates:synth

# This enables:
# - Full Coq proof generation
# - MISRA C compliance checks
# - Strict compiler warnings (-Wall -Werror)
# - Safety analysis
```

## Project Structure

```
Synth/
├── MODULE.bazel              # Bazel module definition (Bzlmod)
├── .bazelrc                  # Build configuration
├── .bazelversion             # Bazel version pinning
├── BUILD.bazel               # Root build file
│
├── bazel/                    # Custom Bazel rules and configs
│   ├── platforms/            # Platform definitions
│   ├── constraints/          # Custom constraints
│   ├── features/             # Feature flags
│   └── toolchains/           # Custom toolchains
│
├── crates/                   # Rust crates
│   ├── BUILD.bazel           # Main crate definitions
│   ├── synth-core/
│   ├── synth-frontend/
│   ├── synth-backend/
│   └── ...
│
└── coq/                      # Coq proofs for ASIL D
    └── BUILD.bazel
```

## Available Configurations

### Build Configurations

- `--config=debug` - Debug build with symbols
- `--config=opt` - Optimized release build
- `--config=dev` - Fast incremental builds
- `--config=asil_d` - ASIL D certification mode

### Platform Configurations

- `--config=arm` - ARM Cortex-M cross-compilation
- `--config=wasm` - WebAssembly Component Model

### Feature Flags

- `--define=verification=full` - Enable Z3 SMT verification
- `--define=with_coq_proofs=true` - Enable Coq proof generation
- `--define=safety_level=asil_d` - ASIL D mode

## Key Bazel Commands

### Building

```bash
# Build everything
bazel build //...

# Build specific target
bazel build //crates:synth

# Build and run
bazel run //crates:synth -- --help

# Clean build
bazel clean
bazel build //...
```

### Testing

```bash
# Run all tests
bazel test //...

# Run specific test
bazel test //crates:integration_tests

# Run with test output
bazel test --test_output=all //...

# Run with coverage
bazel coverage //...
```

### Querying

```bash
# Show all targets
bazel query //...

# Show dependencies
bazel query 'deps(//crates:synth)'

# Show reverse dependencies
bazel query 'rdeps(//..., //crates:synth-core)'
```

## WebAssembly Component Model Integration

Synth uses PulseEngine's `rules_wasm_component` for handling WebAssembly Component Model:

```python
# In MODULE.bazel
bazel_dep(name = "rules_wasm_component", version = "0.1.0")
git_override(
    module_name = "rules_wasm_component",
    remote = "https://github.com/pulseengine/rules_wasm_component.git",
    commit = "main",
)
```

### Using WIT Definitions

```python
# In BUILD.bazel
load("@rules_wasm_component//wasm:defs.bzl", "wasm_component", "wit_bindgen")

wit_bindgen(
    name = "my_interface",
    wit = "interface.wit",
)

wasm_component(
    name = "my_component",
    srcs = [":my_interface"],
    # ...
)
```

## Coq Integration (Future)

When Sail integration is complete, Coq proofs will be built as:

```bash
# Build Coq proofs
bazel build --config=coq //coq:compiler_correctness

# Extract to OCaml
bazel build //coq:extract_proofs

# Verify all proofs
bazel test --config=asil_d //coq:all
```

## Performance Tips

### Remote Caching

Configure remote cache for faster CI builds:

```bash
# In .bazelrc.local (create this file)
build --remote_cache=grpc://your-cache-server:9092
```

### Parallel Builds

```bash
# Use more workers
bazel build --jobs=8 //...

# Limit memory usage
bazel build --local_ram_resources=8192 //...
```

### Incremental Builds

```bash
# Fast incremental for development
bazel build --config=dev //crates:synth

# This uses fastbuild compilation mode
```

## Troubleshooting

### Rust Dependencies Not Found

```bash
# Regenerate Cargo dependencies
bazel run @crates//:crates_vendor

# Or clean and rebuild
bazel clean --expunge
bazel build //...
```

### Platform Issues

```bash
# Check available platforms
bazel query 'kind(platform, //bazel/platforms:all)'

# Verify constraints
bazel query 'kind(constraint_*, //bazel/constraints:all)'
```

### Module Resolution

```bash
# Show module graph
bazel mod graph

# Show specific dependency
bazel mod show_repo rules_rust
```

## Next Steps

1. **Integrate Loom shared library**: Add `loom-shared` as Bazel dependency
2. **Add Sail toolchain**: For ARM ASL → Coq generation
3. **Configure Coq**: Add Coq build rules for proofs
4. **Set up CI**: GitHub Actions with Bazel remote cache

## References

- [Bazel Documentation](https://bazel.build/docs)
- [rules_rust](https://github.com/bazelbuild/rules_rust)
- [rules_wasm_component](https://github.com/pulseengine/rules_wasm_component)
- [Bzlmod User Guide](https://bazel.build/external/module)
