# Synth Examples

This directory contains example WebAssembly modules for testing the Synth synthesizer.

## Examples

### simple_add.wat

A basic WebAssembly module demonstrating:
- Integer addition
- Recursive Fibonacci calculation
- Memory load/store operations
- Linear memory allocation (1 page = 64KB)

### Building Examples

To compile WAT (WebAssembly Text) to WASM (WebAssembly Binary):

```bash
# Install wabt (WebAssembly Binary Toolkit)
# Ubuntu/Debian:
sudo apt install wabt

# macOS:
brew install wabt

# Compile WAT to WASM
wat2wasm examples/wat/simple_add.wat -o examples/wasm/simple_add.wasm
```

### Testing with Synth

```bash
# Parse a WebAssembly module
cargo run --bin synth -- parse examples/wasm/simple_add.wasm

# Parse and output JSON
cargo run --bin synth -- parse examples/wasm/simple_add.wasm -o output.json

# Display target information
cargo run --bin synth -- target-info nrf52840

# Synthesize for Nordic nRF52840 (when implemented)
cargo run --bin synth -- synthesize examples/wasm/simple_add.wasm \
    -o build/simple_add.elf \
    --hardware nrf52840 \
    --xip \
    --verify
```

## Creating New Examples

1. Write WebAssembly text format (.wat) in `examples/wat/`
2. Compile to binary: `wat2wasm input.wat -o output.wasm`
3. Test with Synth: `cargo run --bin synth -- parse output.wasm`
