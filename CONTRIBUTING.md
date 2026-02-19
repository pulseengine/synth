# Contributing to Synth

Welcome! We're glad you're interested in contributing to Synth.

## Development Setup

### Prerequisites

- Rust (stable toolchain)
- Cargo
- Git
- [Bazel](https://bazel.build/) (for full build including verification)
- [Nix](https://nixos.org/download/) (optional, for building Rocq proofs via Bazel)

### Getting Started

```bash
# Clone the repository
git clone https://github.com/pulseengine/synth.git
cd synth

# Build with Cargo
cargo build

# Run tests
cargo test --workspace

# Build with Bazel (all crates)
bazel build //crates:synth
```

### Building Rocq Proofs

The formal verification proofs require Rocq 9.0 (or Coq 8.20+):

```bash
# Install Rocq via opam
cd coq
make install-deps

# Build all proofs
make

# Validate (check for Admitted proofs)
make validate
```

## Code Quality

### Formatting and Linting

```bash
# Format all code
cargo fmt

# Check formatting
cargo fmt --all -- --check

# Run clippy
cargo clippy --workspace --all-targets -- -D warnings
```

### Testing

```bash
# Run all tests
cargo test --workspace

# Run Z3 verification tests (requires libz3-dev)
cargo test -p synth-verify --features z3-solver,arm

# Bazel build + test
bazel build //crates:synth //crates:synth-test
```

## Pull Request Process

1. Fork the repository
2. Create a feature branch: `git checkout -b feature/your-feature`
3. Make your changes
4. Ensure `cargo fmt`, `cargo clippy`, and `cargo test` pass
5. Push to your fork and submit a pull request
6. Ensure all CI checks pass

## Code Style

- Follow Rust API guidelines
- Use descriptive variable and function names
- Add documentation comments for public APIs
- Keep functions focused and small
- Write tests for new functionality

## Proof Contributions

If you're contributing to the Rocq proofs:

- Proofs are in `coq/theories/` organized by domain (Common, ARM, WASM, Synth)
- All proofs must use `From Stdlib` imports (Rocq 9 style)
- Prefer `Qed` over `Admitted` — document any remaining admits with a TODO
- Run `make validate` to check for admitted proofs

## License

By contributing to Synth, you agree that your contributions will be licensed under the Apache License 2.0.
