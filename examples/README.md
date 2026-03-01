# Synth Examples

This directory contains example WebAssembly modules for testing the Synth compiler.

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

### Compiling with Synth

```bash
# Compile a WAT file to an ARM ELF binary
synth compile examples/wat/simple_add.wat -o simple_add.elf

# Compile with Cortex-M vector table and startup code
synth compile examples/wat/simple_add.wat --cortex-m -o firmware.elf

# Compile all exported functions
synth compile examples/wat/simple_add.wat --all-exports -o multi.elf

# Compile and verify the translation via Z3
synth compile examples/wat/simple_add.wat --verify -o verified.elf

# Disassemble the generated ELF
synth disasm simple_add.elf

# Use a built-in demo (no input file needed)
synth compile --demo add -o demo.elf
```

### Running via Cargo (without installing)

```bash
cargo run -p synth-cli -- compile examples/wat/simple_add.wat -o simple_add.elf
cargo run -p synth-cli -- disasm simple_add.elf
```

## Creating New Examples

1. Write WebAssembly text format (.wat) in `examples/wat/`
2. Compile with Synth: `synth compile examples/wat/your_module.wat -o output.elf`
3. Inspect: `synth disasm output.elf`
