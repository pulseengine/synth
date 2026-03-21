# Synth WASM Compiler - Zephyr Calculator

Interactive calculator demonstrating 14 WASM functions compiled to native ARM
Thumb-2 assembly and linked into a Zephyr RTOS application.

## What It Demonstrates

| Category | Functions | WASM Features |
|----------|-----------|---------------|
| Arithmetic | `add`, `sub`, `mul`, `div_safe` | i32.add/sub/mul, i32.div_s, if/else (div-by-zero guard) |
| Accumulator | `acc_set`, `acc_get`, `acc_add` | i32.load, i32.store (linear memory) |
| Bitwise | `bit_and`, `bit_or`, `bit_xor`, `bit_not` | i32.and/or/xor |
| Comparison | `max`, `min`, `abs` | i32.gt_s/lt_s, if/else control flow |

Every function is native ARM -- no interpreter, no WASM runtime, zero overhead.

## Project Structure

```
zephyr-calculator/
  calculator.wat         WASM source (14 exported functions)
  CMakeLists.txt         Zephyr build configuration
  prj.conf               Zephyr project settings
  src/
    calculator.s          Synth-compiled ARM Thumb-2 assembly
    main.c                Zephyr application (self-test + demo loop)
  README.md               This file
```

## Building

### Prerequisites

1. Zephyr SDK installed and configured
2. ARM toolchain (`arm-none-eabi-gcc`)
3. `west` build tool

### Build and Run

```bash
cd examples/zephyr-calculator

# QEMU Cortex-M3 (easiest for testing)
west build -b qemu_cortex_m3 .
west build -t run

# STM32F4 Discovery (real hardware)
west build -b stm32f4_disco .
west flash
```

### Expected Output

```
===========================================================
  Synth WASM Compiler - Zephyr Calculator
===========================================================

14 WASM functions compiled to native ARM Thumb-2 assembly.
Source: calculator.wat   Target: Cortex-M

--- Arithmetic ---
  PASS  add(3, 4)                            = 7
  PASS  sub(10, 3)                           = 7
  PASS  mul(6, 7)                            = 42
  PASS  div_safe(20, 4)                      = 5
  PASS  div_safe(1, 0)                       = 0
  ...

--- Accumulator (WASM memory) ---
  PASS  acc_set(100); acc_get()              = 100
  PASS  acc_add(50)                          = 150
  ...

--- Bitwise ---
  PASS  bit_and(0xFF, 0x0F)                  = 15
  ...

--- Comparison ---
  PASS  max(5, 3)                            = 5
  PASS  abs(-42)                             = 42
  ...

===========================================================
  Results: 32 / 32 tests passed
===========================================================

Running continuous accumulator demo...
```

## Regenerating the Assembly

The `src/calculator.s` file can be regenerated from the WASM source:

```bash
# 1. Compile WAT to ELF with Synth
cargo run -p synth-cli -- compile calculator.wat -o /tmp/calc.elf \
    --cortex-m --all-exports

# 2. Disassemble to inspect the generated code
cargo run -p synth-cli -- disasm /tmp/calc.elf

# 3. The current .s file is hand-maintained to match Synth's output
#    while using standard GNU as directives for Zephyr linking.
```

## Compilation Approach

Synth compiles WASM to a standalone Cortex-M ELF with vector table and startup
code. For Zephyr integration, we use the assembly path: the `.s` file contains
just the function bodies with standard AAPCS calling convention, linked directly
into the Zephyr image by CMake.

| WASM instruction | ARM Thumb-2 | Example |
|------------------|-------------|---------|
| `i32.add` | `adds r0, r0, r1` | `add(a, b)` |
| `i32.sub` | `subs r0, r0, r1` | `sub(a, b)` |
| `i32.mul` | `muls r0, r1, r0` | `mul(a, b)` |
| `i32.div_s` | `sdiv r0, r0, r1` | `div_safe(a, b)` |
| `i32.and` | `ands r0, r0, r1` | `bit_and(a, b)` |
| `i32.or` | `orrs r0, r0, r1` | `bit_or(a, b)` |
| `i32.xor` | `eors r0, r0, r1` | `bit_xor(a, b)` |
| `i32.load` | `ldr r0, [r1]` | `acc_get()` |
| `i32.store` | `str r0, [r1]` | `acc_set(v)` |
| `if/else` | `cmp` + `bge/ble/beq` | `max`, `min`, `abs`, `div_safe` |
