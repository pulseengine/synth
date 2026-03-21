# Meld & Kiln Integration Instructions for Synth Pipeline

## Context

Synth (WASM→ARM Cortex-M AOT compiler) can now compile real-world WASM to ARM ELF binaries. The next step is the full cross-compilation chain:

```
WASM Components → meld fuse → Core WASM → synth compile --link → firmware.elf → Cortex-M
```

We've verified that the **OSxCAR anti-pinch window controller** (3 WASM components from https://osxcar.de/insights/demonstration/) compiles through synth individually. The goal is to fuse them via meld, then compile+link the fused output into a single firmware.elf that runs on Renode.

---

## What Synth Provides Today

- `synth compile <file.wasm> -o output.elf --cortex-m --all-exports` — AOT compiles core WASM to ARM Cortex-M ELF
- `synth compile ... --link --builtins <kiln_builtins.o>` — Compiles AND links into firmware.elf
- Relocatable ELF output with `__meld_dispatch_import` undefined symbol + `.meld_import_table` section
- Linker script generation with Meld integration sections
- 197+ WASM opcodes, 227/257 spec files compile, 851 tests

---

## What Meld Needs To Do

### Step 1: Fuse the OSxCAR Components

The 3 OSxCAR WASM modules are already-lowered core modules (not full P2 components). They were lowered by wit-component before being base64-embedded in JavaScript. Meld should be able to fuse them:

```bash
meld fuse anti_pinch_v2.wasm motor_driver_v2.wasm soft_start_stop.wasm -o fused_antipinch.wasm --memory shared
```

**Key requirement:** The output must be a **single-memory core module** (not multi-memory). Synth targets single-memory ARM Cortex-M. Options:
1. `--memory shared` with `--address-rebase` (preferred if stable)
2. OR synth adds multi-memory support (more work)

### Step 2: Verify the Fused Output

```bash
meld inspect fused_antipinch.wasm --types --interfaces
```

Expected output should show:
- Single core module (not component)
- Merged exports from all 3 components
- Unresolved WASI imports listed as core imports
- Single memory

### Step 3: Import Map (nice-to-have)

Add `--emit-import-map imports.json` flag that produces:

```json
{
  "imports": [
    {"index": 0, "module": "wasi:cli/stderr@0.2.6", "name": "get-stderr"},
    {"index": 1, "module": "wasi:io/streams@0.2.6", "name": "[method]output-stream.blocking-write-and-flush"}
  ]
}
```

This tells synth (and kiln-builtins) exactly which import index maps to which WASI function, enabling the dispatcher to route calls correctly.

### Step 4: Test with Synth

After fusing, synth should be able to compile the output:

```bash
synth compile fused_antipinch.wasm -o antipinch.elf --cortex-m --all-exports
```

If this fails, the error message will tell us what WASM opcodes or features the fused module uses that synth doesn't support yet.

---

## What Kiln Needs To Do

### Step 1: Create `kiln-builtins` Crate

A new `no_std` crate in the kiln workspace. This is the **C ABI bridge** between synth-compiled ARM code and kiln's runtime services.

**Location:** `kiln-builtins/`

**Cargo.toml:**
```toml
[package]
name = "kiln-builtins"
version = "0.1.0"
edition = "2024"

[lib]
crate-type = ["staticlib"]  # Produces libkiln_builtins.a

[dependencies]
kiln-foundation = { path = "../kiln-foundation", default-features = false }

[features]
default = []
std = ["kiln-foundation/std"]
```

**Target:** `thumbv7em-none-eabi` (Cortex-M4F) and `thumbv7em-none-eabihf` (hard-float)

### Step 2: Implement Core Functions

The minimum viable set (3 functions):

```rust
#![no_std]

/// Called by synth-compiled code: MOV R0, #import_index; BL __meld_dispatch_import
/// Routes to the appropriate WASI/host function based on the import index.
#[unsafe(no_mangle)]
pub extern "C" fn __meld_dispatch_import(import_index: u32) -> u32 {
    // Read import table from .meld_import_table section (linker-provided symbols)
    // Match module/name to handler
    // Call handler with args from linear memory
    // Return result
    0 // stub for Phase 1
}

/// Returns the base address of WASM linear memory.
#[unsafe(no_mangle)]
pub extern "C" fn __meld_get_memory_base() -> *mut u8 {
    extern "C" { static __wasm_memory_start: u8; }
    unsafe { &raw const __wasm_memory_start as *mut u8 }
}

/// Canonical ABI allocator for linear memory.
/// Called by adapter code to allocate space for strings, lists, records.
/// For embedded: bump allocator within linear memory bounds.
#[unsafe(no_mangle)]
pub extern "C" fn cabi_realloc(
    old_ptr: u32,
    old_size: u32,
    align: u32,
    new_size: u32,
) -> u32 {
    // Bump allocator: maintain a pointer at a known memory location
    // Allocate new_size bytes at current pointer, advance pointer
    // If old_ptr != 0, this is a realloc (copy old data, return new ptr)
    // Return offset from memory base (not absolute address)
    0 // stub for Phase 1
}
```

### Step 3: WASI Embedded Dispatcher

For the anti-pinch demo, the minimum WASI needed is:
- `wasi:cli/stderr` — error output (can stub to UART/semihosting)
- `wasi:io/streams` — blocking write (route to UART)
- `wasi:clocks/monotonic-clock` — timer (read SysTick)

Source material exists in `kiln-wasi/src/dispatcher.rs` — extract the dispatch logic into no_std-compatible form.

### Step 4: Build for ARM Target

```bash
cargo build --target thumbv7em-none-eabi -p kiln-builtins --release
# Produces: target/thumbv7em-none-eabi/release/libkiln_builtins.a
```

### Step 5: Test with Synth

```bash
# Compile WASM to relocatable object
synth compile fused_antipinch.wasm -o module.o --cortex-m --all-exports

# Link with kiln-builtins
arm-none-eabi-gcc -nostartfiles -nostdlib -mcpu=cortex-m4 -mthumb \
  -T synth_generated.ld module.o libkiln_builtins.a -o firmware.elf

# OR use synth's --link flag:
synth compile fused_antipinch.wasm -o firmware.elf \
  --cortex-m --all-exports --link --builtins libkiln_builtins.a
```

---

## The OSxCAR Test Case

### What We Have

Three WASM modules extracted from https://osxcar.de/insights/demonstration/:

| Component | WASM Size | ARM Code | Functions |
|-----------|-----------|----------|-----------|
| anti_pinch_v2 | 13,294 bytes | 8,392 bytes | initialize, step, terminate |
| motor_driver_v2 | 2,574 bytes | 1,844 bytes | initialize, step, terminate |
| soft_start_stop | 1,785 bytes | 1,728 bytes | step, terminate |

WIT interface: `aptiv:antipinch/anti-pinch-v2@0.1.0`, `aptiv:antipinch/motor-driver-v2@0.1.0`, `aptiv:antipinch/soft-start-stop@0.1.0`

### Test Script

`tests/integration/fetch_osxcar_wasm.sh` fetches these from the website, compiles each individually through synth (all 3 pass).

### End-to-End Goal

```bash
# 1. Fetch WASM components
bash tests/integration/fetch_osxcar_wasm.sh  # → /tmp/osxcar_*.wasm

# 2. Fuse with meld (MELD TODO)
meld fuse /tmp/osxcar_antipinch_0.wasm /tmp/osxcar_motor_driver_0.wasm \
  /tmp/osxcar_soft_start_0.wasm -o /tmp/fused.wasm --memory shared

# 3. Compile + link with synth (SYNTH READY)
synth compile /tmp/fused.wasm -o /tmp/firmware.elf \
  --cortex-m --all-exports --link --builtins libkiln_builtins.a

# 4. Run on Renode (verification)
renode --execute "machine LoadPlatformDescription @synth_cortex_m.repl; \
  sysbus LoadELF @/tmp/firmware.elf; start"
```

---

## Synth's Expectations (Contract)

### From Meld:
1. Output is a **single core WASM module** (not a component, not multi-memory)
2. Unresolved imports have human-readable module/name strings
3. Exports are the merged set of all component exports
4. Memory is single, shared (OR synth needs to add multi-memory — tell us)
5. `cabi_realloc` is either exported by the fused module or provided externally

### From Kiln-builtins:
1. `__meld_dispatch_import(u32) -> u32` — C ABI, AAPCS calling convention
2. `__meld_get_memory_base() -> *mut u8` — returns `__wasm_memory_start` linker symbol
3. `cabi_realloc(u32, u32, u32, u32) -> u32` — bump allocator in linear memory
4. Compiled as `libkiln_builtins.a` for `thumbv7em-none-eabi`
5. All symbols have `#[unsafe(no_mangle)]` / `extern "C"`

### Linker Symbols Synth Provides:
- `__wasm_memory_start` / `__wasm_memory_end` — linear memory bounds
- `__meld_import_table_start` / `__meld_import_table_end` — import metadata
- All exported WASM functions as global symbols (with Thumb bit set)

### Linker Symbols Synth Expects (undefined):
- `__meld_dispatch_import` — provided by kiln-builtins.a
- `__meld_get_memory_base` — provided by kiln-builtins.a

---

## Priority Order

1. **Kiln: Create kiln-builtins stub** (even returning 0 for all imports — enables linking)
2. **Meld: Test fusing OSxCAR components** (verify single-memory output works)
3. **Kiln: Implement cabi_realloc** (bump allocator — enables canonical ABI)
4. **Meld: Add --emit-import-map** (enables intelligent dispatch)
5. **Kiln: WASI embedded dispatcher** (clocks, stdout — enables output verification)
6. **All: End-to-end Renode test** (the goal)

## Rivet Artifacts

All requirements are traced in synth's rivet artifacts:
- `artifacts/kiln-builtins-api.yaml` — KB-001..005 (API requirements)
- `artifacts/compilation-chain.yaml` — CC-001..008 (pipeline stages)
- `artifacts/static-linking.yaml` — SL-001..007 (linker requirements)
- `artifacts/e2e-verification.yaml` — E2E-VER-001..010 (test plan)
- `artifacts/cross-compilation.yaml` — XC-001..009 (toolchain requirements)

Cross-link with `kiln:` and `meld:` prefixes in rivet externals.
