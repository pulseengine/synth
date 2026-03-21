# Cross-Compilation Pipeline Design

Issue #27 -- ARM cross-compilation toolchain for producing runnable firmware.

## Status

Draft -- 2026-03-21

## Overview

This document defines the complete cross-compilation pipeline from WASM Component
to runnable firmware on ARM Cortex-M targets. The pipeline spans three phases:
bare-metal (no OS), Zephyr RTOS integration, and real hardware deployment. It
covers the roles of all PulseEngine components (synth, kiln, gale, meld) and the
testing strategy from emulation through hardware.

## Architecture Diagram

```
                          PulseEngine Cross-Compilation Pipeline
                          ==========================================

  +-----------------+       +-----------+       +-----------------+
  | WASM Component  | ----> |   Meld    | ----> | Core WASM (.wasm)|
  | (.wasm + .wit)  |       | (fuser)   |       | (host imports)   |
  +-----------------+       +-----------+       +-----------------+
                                                        |
                                                        v
                                                +-----------------+
                                                |     Synth       |
                                                | (AOT compiler)  |
                                                +-----------------+
                                                        |
                                          +-------------+-------------+
                                          |                           |
                                          v                           v
                                  +---------------+           +---------------+
                                  | module.o      |           | module.s      |
                                  | (relocatable  |           | (assembly,    |
                                  |  ELF, ET_REL) |           |  Zephyr path) |
                                  +---------------+           +---------------+
                                          |                           |
        +-----------------+               |                           |
        | kiln-builtins.a |               |                           |
        | (C ABI bridge,  |               |                           |
        |  no_std, ARM)   |               |                           |
        +-----------------+               |                           |
                |                         |                           |
                +-------+-----------------+                           |
                        |                                             |
                        v                                             v
                +------------------+                    +----------------------------+
                | arm-none-eabi-ld |                    |  Zephyr Build (west build) |
                | + linker script  |                    |  CMakeLists.txt includes   |
                +------------------+                    |  module.s as target_source |
                        |                               +----------------------------+
                        v                                             |
                +------------------+                                  v
                | firmware.elf     |                    +----------------------------+
                | (bare-metal,     |                    | zephyr.elf                 |
                |  standalone)     |                    | (Zephyr firmware with      |
                +------------------+                    |  synth + gale + kiln)      |
                        |                               +----------------------------+
                        |                                             |
          +-------------+-------------+                 +-------------+-------------+
          |             |             |                 |             |             |
          v             v             v                 v             v             v
     +---------+   +---------+   +--------+       +---------+   +---------+   +--------+
     | Renode  |   | QEMU    |   | J-Link |       | Renode  |   | QEMU    |   | J-Link |
     | (CM4)   |   | (CM3)   |   | (HW)   |       | (CM4)   |   | (CM3)   |   | (HW)   |
     +---------+   +---------+   +--------+       +---------+   +---------+   +--------+
```

## Phase 1 -- Bare-Metal (No OS)

### Goal

Produce a standalone firmware.elf from a WASM module that boots and executes on a
Cortex-M4 emulator without any RTOS. This validates the core compilation chain
end-to-end.

### Build Steps

```
# Step 1: Compile WASM to relocatable ELF
synth compile module.wasm --target cortex-m4 -o module.o

# Step 2: Link with kiln-builtins stub and generated linker script
arm-none-eabi-ld -T synth_cortex_m4.ld module.o kiln-builtins.a -o firmware.elf

# Step 3: Execute on Renode emulator
renode --execute "sysbus LoadELF @firmware.elf; start"
```

### module.o Format (Relocatable ELF)

Synth emits a relocatable ELF object (ET_REL) containing:

| Section             | Type        | Placement | Content |
|---------------------|-------------|-----------|---------|
| `.text`             | SHT_PROGBITS | FLASH    | Compiled ARM Thumb-2 code |
| `.meld_import_table`| SHT_PROGBITS | FLASH    | Import descriptor array (KB-005 format) |
| `.meld_import_strings` | SHT_PROGBITS | FLASH | Module/field name strings |
| `.symtab`           | SHT_SYMTAB  | --        | Symbol table (UND for imports, GLOBAL for exports) |
| `.strtab`           | SHT_STRTAB  | --        | String table |
| `.rel.text`         | SHT_REL     | --        | R_ARM_THM_CALL relocations for import BLs |

Undefined symbols emitted by synth:
- `__meld_dispatch_import` -- generic import dispatch (or `__meld_import_N` per-import)
- `__meld_get_memory_base` -- linear memory base address accessor
- `cabi_realloc` -- canonical ABI memory allocator

### kiln-builtins.a (Minimal Stub for Phase 1)

For Phase 1, a minimal stub library provides the three required symbols:

```c
// kiln-builtins-stub.c -- minimal Phase 1 stub
#include <stdint.h>

// Linear memory region (statically allocated in RAM)
static uint8_t __wasm_memory[65536] __attribute__((section(".wasm_linear_memory")));

int32_t __meld_dispatch_import(uint32_t import_index,
                                const void *args,
                                uint32_t args_len,
                                void *ret) {
    // Phase 1: no host functions, return trap
    return -1;
}

uint8_t* __meld_get_memory_base(uint32_t memory_index) {
    return __wasm_memory;
}

uint8_t* cabi_realloc(uint8_t *old_ptr, uint32_t old_size,
                       uint32_t align, uint32_t new_size) {
    // Phase 1: bump allocator within linear memory
    static uint32_t bump_offset = 0;
    uint32_t aligned = (bump_offset + align - 1) & ~(align - 1);
    bump_offset = aligned + new_size;
    return &__wasm_memory[aligned];
}
```

Cross-compile with: `arm-none-eabi-gcc -mcpu=cortex-m4 -mthumb -c -o kiln-builtins.o`

### Linker Script

Generated by `LinkerScriptGenerator::new_stm32().with_meld_integration().with_wasm_memory(65536)`:

```
ENTRY(Reset_Handler)
EXTERN(__meld_dispatch_import)
EXTERN(__meld_get_memory_base)

MEMORY {
  FLASH (rx):  ORIGIN = 0x08000000, LENGTH = 0x80000    /* 512 KB */
  RAM   (rwx): ORIGIN = 0x20000000, LENGTH = 0x20000    /* 128 KB */
}

SECTIONS {
  .isr_vector : { ALIGN(128); KEEP(*(.isr_vector)) } >FLASH
  .text       : { *(.text) *(.text.*) } >FLASH
  .meld_import_table : { KEEP(*(.meld.imports)) } >FLASH
  .rodata     : { *(.rodata) *(.rodata*) } >FLASH
  .data       : { *(.data) } >RAM AT> FLASH
  .bss        : { *(.bss) } >RAM
  .wasm_linear_memory (NOLOAD) : { . = . + 0x10000; } >RAM
  .stack      : { . = . + 0x1000; _estack = .; } >RAM
}
```

### CI Integration via Bazel

```python
# tests/compilation-chain/BUILD.bazel

sh_test(
    name = "bare_metal_e2e",
    srcs = ["bare_metal_e2e_test.sh"],
    data = [
        "//crates:synth",
        "//tests/compilation-chain:test_import.wat",
        "//tests/compilation-chain:kiln-builtins-stub.a",
        "//tests/compilation-chain:synth_cortex_m4.ld",
    ],
    tags = ["integration", "arm"],
    deps = [
        "@bazel_tools//tools/bash/runfiles",
    ],
)

# Renode emulation test (requires rules_renode)
renode_test(
    name = "bare_metal_renode",
    firmware = ":bare_metal_e2e",
    platform = "//tests:synth_cortex_m.repl",
    robot = "bare_metal_test.robot",
    tags = ["renode", "emulation"],
)
```

### Toolchain Detection

Synth detects the ARM cross-linker in priority order:
1. `--linker <path>` CLI flag
2. `SYNTH_LINKER` environment variable
3. PATH search for: `arm-none-eabi-ld`, `arm-zephyr-eabi-ld`, `ld.lld`

---

## Phase 2 -- Zephyr RTOS Integration

### Goal

Integrate synth-compiled WASM modules with Zephyr applications, with gale kernel
primitives available for task isolation and kiln-builtins providing WASI dispatch
through Zephyr APIs.

### Architecture

```
+------------------------------------------------------------------+
|                     Zephyr Application                            |
|                                                                    |
|  +--------------------+  +------------------+  +----------------+ |
|  | main.c             |  | synth module.s   |  | gale (Zephyr   | |
|  | (Zephyr app logic) |  | (WASM->ARM, .s)  |  |  module via    | |
|  |                    |  |                  |  |  libgale_ffi.a) | |
|  | extern int32_t     |  | .global func_0  |  |                | |
|  |   func_0(...);     |  | func_0:         |  | gale_sem_*     | |
|  |                    |  |   push {r4,lr}   |  | gale_mutex_*   | |
|  | result =           |  |   ...ARM code... |  | gale_msgq_*    | |
|  |   func_0(a, b);    |  |   pop {r4,pc}   |  | gale_pipe_*    | |
|  +--------------------+  +------------------+  +----------------+ |
|                                                                    |
|  +--------------------+  +------------------+                     |
|  | kiln-builtins.a    |  | Zephyr kernel    |                     |
|  | (dispatch, memory, |  | (scheduler,      |                     |
|  |  cabi_realloc)     |  |  drivers, HAL)   |                     |
|  +--------------------+  +------------------+                     |
+------------------------------------------------------------------+
|                        Hardware (Cortex-M4)                        |
+------------------------------------------------------------------+
```

### Build Steps (Assembly Path)

This path integrates synth output as assembly into the Zephyr build system,
matching the existing `examples/zephyr-poc/` and `examples/pid-controller/` patterns:

```bash
# Step 1: Compile WASM to ARM assembly
synth compile module.wasm --target cortex-m4 --output-format asm -o module.s

# Step 2: Build with Zephyr (west build system)
cd my-zephyr-app/
west build -b stm32f4_disco
```

CMakeLists.txt:
```cmake
cmake_minimum_required(VERSION 3.20.0)
find_package(Zephyr REQUIRED HINTS $ENV{ZEPHYR_BASE})
project(my_wasm_app)

target_sources(app PRIVATE src/main.c)
target_sources(app PRIVATE src/module.s)       # Synth-compiled WASM

# Optional: gale kernel primitives (if Zephyr module path includes gale)
# set(EXTRA_ZEPHYR_MODULES /path/to/gale ${EXTRA_ZEPHYR_MODULES})
```

prj.conf:
```ini
CONFIG_PRINTK=y
CONFIG_CONSOLE=y
# For gale integration:
# CONFIG_GALE_KERNEL_SEM=y
# CONFIG_GALE_KERNEL_MUTEX=y
# For MPU protection of WASM linear memory:
# CONFIG_ARM_MPU=y
# CONFIG_MPU_ALLOW_FLASH_WRITE=n
```

### Build Steps (Object Path -- Full Pipeline)

For modules with host imports requiring kiln-builtins:

```bash
# Step 1: Compile WASM to relocatable ELF
synth compile module.wasm --target cortex-m4 -o module.o

# Step 2: Build kiln-builtins for ARM
cd ../kiln && cargo build -p kiln-builtins --target thumbv7em-none-eabihf --release

# Step 3: Integrate with Zephyr via external library
# CMakeLists.txt uses target_link_libraries for module.o and kiln-builtins.a
```

### Gale Integration

Gale provides formally verified Zephyr kernel primitives accessible to
synth-compiled WASM modules via the Kiln runtime:

**Path A -- Direct Zephyr Module (Phase 1, current):**
- Gale is a Zephyr module (zephyr/module.yml)
- C shim bridges Zephyr k_sem/k_mutex/etc. API to Rust FFI
- CONFIG_GALE_KERNEL_SEM=y replaces kernel/sem.c count arithmetic
- No direct WASM access -- Zephyr C code calls gale, synth code calls Zephyr

**Path B -- Kiln Host Functions (Phase 2, planned per gale STKH-002):**
- Gale primitives linked directly into Kiln as Rust crate (no C FFI)
- WIT interfaces define kernel object operations
- WASM components import kernel objects via WIT
- Synth compiles imports as BL to kiln dispatch
- Call path: WASM import -> kiln dispatch -> gale Rust method

Gale primitives available:

| Primitive | Zephyr Module | FFI Functions | Verified Properties |
|-----------|---------------|---------------|---------------------|
| Semaphore | CONFIG_GALE_KERNEL_SEM | gale_sem_count_init/give/take | P1-P3, P5-P6, P9 |
| Mutex | CONFIG_GALE_KERNEL_MUTEX | gale_mutex_lock/unlock_validate | M3-M7, M10 |
| Condvar | CONFIG_GALE_KERNEL_CONDVAR | (pure wait queue, no FFI) | C1-C8 |
| Message Queue | CONFIG_GALE_KERNEL_MSGQ | gale_msgq_init/put/get/peek | MQ1-MQ13 |
| Stack (LIFO) | CONFIG_GALE_KERNEL_STACK | gale_stack_init/push/pop_validate | SK1-SK9 |
| Pipe | CONFIG_GALE_KERNEL_PIPE | gale_pipe_write/read_check | PP1-PP10 |
| Timer | (planned) | -- | TM1-TM8 |
| Event | (planned) | -- | EV1-EV8 |
| Mem Slab | (planned) | -- | MS1-MS8 |

### WASM Task Isolation via Gale

For multi-component embedded applications, gale primitives provide the
isolation boundary between WASM modules:

1. Each WASM component runs in its own Zephyr thread
2. Gale semaphores/mutexes coordinate access to shared resources
3. Gale message queues provide inter-component communication
4. MPU regions isolate each component's linear memory
5. kiln-builtins mediates all cross-component calls via Meld dispatch

---

## Phase 3 -- Real Hardware

### Goal

Execute synth-compiled firmware on physical ARM Cortex-M boards, validating the
full pipeline from WASM to silicon.

### Target Boards

| Board | SoC | CPU | Flash | RAM | MPU | FPU | Target Triple |
|-------|-----|-----|-------|-----|-----|-----|---------------|
| STM32F4-Discovery | STM32F407VG | Cortex-M4F | 1 MB @ 0x08000000 | 192 KB @ 0x20000000 | 8 regions | SP VFP | thumbv7em-none-eabihf |
| nRF52840-DK | nRF52840 | Cortex-M4F | 1 MB @ 0x00000000 | 256 KB @ 0x20000000 | 8 regions | SP VFP | thumbv7em-none-eabihf |

### Deployment

```bash
# Via Zephyr west (preferred)
west flash -b stm32f4_disco

# Via OpenOCD (bare-metal)
openocd -f board/stm32f4discovery.cfg \
  -c "program firmware.elf verify reset exit"

# Via J-Link (nRF52840-DK)
JLinkExe -device nRF52840_xxAA -if SWD -speed 4000 \
  -CommanderScript flash.jlink
```

### UART Verification

```bash
# Monitor UART output for test pass/fail
minicom -D /dev/ttyACM0 -b 115200

# Expected output for calculator test:
# synth_add(5, 42) = 47
# synth_multiply(6, 7) = 42
```

---

## Testing Strategy

### Progression: Emulation to Hardware

```
Level 1: Unit Tests (cargo test --workspace)
  - Instruction encoding correctness
  - ELF structure validation (synth_elf_integration_test.sh)
  - Relocation emission (synth_static_link_test.sh)
  - Meld ABI pipeline (meld_abi_test.rs)
  - 526+ tests, no hardware required

Level 2: Renode Emulation (bazel test //tests/...)
  - Full Cortex-M4 emulation with NVIC, SysTick, UART
  - WAST test suite via synth-test -> Robot Framework
  - End-to-end: WASM -> compile -> link -> boot -> execute -> verify output
  - Platform: synth_cortex_m.repl (generic CM4 @ 0x0/0x20000000)

Level 3: Zephyr QEMU (west build -b qemu_cortex_m3)
  - Zephyr scheduler, drivers, printk via QEMU
  - Tests: zephyr-poc, pid-controller, calculator
  - Validates Zephyr CMake integration path

Level 4: Zephyr + Gale (west build with EXTRA_ZEPHYR_MODULES=gale)
  - Gale kernel primitives active (CONFIG_GALE_KERNEL_SEM=y, etc.)
  - Tests: multi-threaded WASM with semaphore coordination
  - Validates gale FFI -> Rust -> ARM -> Zephyr integration

Level 5: Real Hardware (west flash -b nrf52840dk/nrf52840)
  - Physical nRF52840-DK or STM32F4-Discovery
  - UART output verification via serial console
  - Validates: clock configuration, flash XIP, real MPU, real interrupts
```

### CI Pipeline

```
GitHub Actions / Bazel CI:
  - Level 1: Always (cargo test, clippy, fmt)
  - Level 2: Always (Renode via rules_renode, hermetic)
  - Level 3: Gated on Zephyr SDK availability (optional)
  - Level 4: Gated on both Zephyr SDK and gale checkout
  - Level 5: Manual trigger, requires physical hardware runner
```

---

## Cross-Repository Dependencies

```
                      +-----------+
                      |   meld    |
                      | (fuser)  |
                      +-----+-----+
                            |
                            | Core WASM with
                            | canonical ABI wrappers
                            v
    +-----------+     +-----------+     +-----------+
    |   gale    |     |   synth   |     |   kiln    |
    | (kernel   |     | (AOT      |     | (runtime, |
    |  prims)   |     |  compiler)|     |  builtins)|
    +-----------+     +-----------+     +-----------+
         |                  |                  |
         | Zephyr module    | module.o         | kiln-builtins.a
         | (libgale_ffi.a)  | (ET_REL)         | (no_std ARM)
         |                  |                  |
         +--------+---------+--------+---------+
                  |                  |
                  v                  v
           +-----------+     +-----------+
           | Zephyr    |     | arm-none- |
           | (west     |     | eabi-ld   |
           |  build)   |     | (linker)  |
           +-----------+     +-----------+
                  |                  |
                  v                  v
           +-----------+     +-----------+
           | zephyr.elf|     |firmware.elf|
           +-----------+     +-----------+
```

### Dependency Matrix

| Produces | Consumes | Interface | Status |
|----------|----------|-----------|--------|
| meld | synth | Core WASM (.wasm) | Draft (CC-002) |
| synth | arm-none-eabi-ld | module.o (ET_REL) | Implemented (CC-003) |
| synth | Zephyr CMake | module.s (assembly) | Implemented (ZI-001) |
| kiln | arm-none-eabi-ld | kiln-builtins.a | Draft (CC-004) |
| gale | Zephyr CMake | libgale_ffi.a + C shims | Implemented |
| arm-none-eabi-ld | Renode/hardware | firmware.elf (ET_EXEC) | Draft (CC-005) |
| Zephyr (west) | Renode/hardware | zephyr.elf | Implemented (ZI-001) |

### Version Compatibility

All PulseEngine repos target:
- Rust edition 2024, MSRV 1.88
- Bazel 8.x with bzlmod
- ARM target: thumbv7em-none-eabihf (Cortex-M4F with hardware float)
- Gale and synth both use the same Rust target triple detection logic

---

## Implementation Plan

### Phase 1 Milestones (Issue #27)

| # | Task | Artifacts | Estimate |
|---|------|-----------|----------|
| 1 | Create kiln-builtins-stub.a (minimal) | XC-001, XC-002 | 1 day |
| 2 | Add `synth compile --link` CLI flag | SL-TR-002 | 2 days |
| 3 | Linker detection and invocation | SL-001, XC-003 | 1 day |
| 4 | Bare-metal Renode e2e test | E2E-VER-001 | 2 days |
| 5 | Bazel CI integration | E2E-VER-007, XC-006 | 1 day |
| 6 | Startup code: `__meld_get_memory_base` | KB-TR-005 | 1 day |

### Phase 2 Milestones

| # | Task | Artifacts | Estimate |
|---|------|-----------|----------|
| 7 | Zephyr + synth + gale CMake integration | GI-001, GI-002 | 2 days |
| 8 | kiln-builtins with WASI stdout | E2E-VER-003 | 3 days |
| 9 | Multi-component isolation demo | GI-003 | 3 days |
| 10 | Zephyr QEMU CI test | XC-007 | 1 day |

### Phase 3 Milestones

| # | Task | Artifacts | Estimate |
|---|------|-----------|----------|
| 11 | STM32F4-Discovery flash test | XC-008 | 1 day |
| 12 | nRF52840-DK flash test | XC-009 | 1 day |
| 13 | UART output verification | E2E-VER-001 | 1 day |

---

## Artifact Traceability

New artifacts created for this design are tracked in:
- `artifacts/cross-compilation.yaml` -- XC-* (cross-compilation toolchain requirements)
- `artifacts/gale-integration.yaml` -- GI-* (gale integration requirements)

These trace to existing artifacts:
- CC-001..CC-008 (compilation chain)
- SL-001..SL-007 (static linking)
- KB-001..KB-005 (kiln-builtins API)
- ZI-001..ZI-010 (Zephyr integration)
- TP-001..TP-008 (target platforms)
- E2E-VER-001..E2E-VER-010 (end-to-end verification)
