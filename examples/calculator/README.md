# Calculator Example

A minimal WebAssembly module that implements five basic integer arithmetic
operations. This is the recommended starting point for getting familiar with
Synth's compilation pipeline.

## What it does

`calculator.wat` exports the following functions, each taking two `i32`
parameters and returning an `i32` result:

| Export       | WASM instruction | Description                  |
|--------------|------------------|------------------------------|
| `add`        | `i32.add`        | Addition (a + b)             |
| `subtract`   | `i32.sub`        | Subtraction (a - b)          |
| `multiply`   | `i32.mul`        | Multiplication (a * b)       |
| `divide`     | `i32.div_s`      | Signed division (a / b)      |
| `modulo`     | `i32.rem_s`      | Signed remainder (a % b)     |

Division and modulo will trap (abort) on division by zero, matching the
WebAssembly specification. Signed division also traps on overflow
(`INT32_MIN / -1`).

## Compiling to an ARM Cortex-M ELF

```bash
synth compile examples/calculator/calculator.wat -o calculator.elf --cortex-m --all-exports
```

`--all-exports` tells Synth to compile every exported function in the module.
The result is a bare-metal ELF binary targeting ARM Cortex-M with a vector
table, ready to flash or run under emulation.

## Verifying the compilation

Synth can invoke Z3 to perform translation validation, checking that the
generated ARM instructions preserve the semantics of the original WASM:

```bash
synth compile examples/calculator/calculator.wat -o calculator.elf --cortex-m --all-exports --verify
```

If verification succeeds the compiler prints a confirmation for each function.
If it fails, no ELF is produced.

## What the generated ELF contains

The output `calculator.elf` is a minimal ARM Cortex-M ELF with:

- A vector table (initial stack pointer and reset handler)
- Native Thumb-2 code for each exported function
- No runtime, no heap, no OS dependencies

You can inspect the binary with standard tools:

```bash
# Disassemble with Synth
synth disasm calculator.elf

# Or with the ARM toolchain
arm-none-eabi-objdump -d calculator.elf
```

## Further reading

- `examples/pid-controller/` — a more advanced example using floating-point PID control
- `tests/wast/` — the full WebAssembly spec-test suite used by Synth's CI
