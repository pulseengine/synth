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
- Relocatable ELF output: every wasm function import is an undefined symbol named by its **bare field name**, called directly per AAPCS (`bl <field>`, `R_ARM_THM_CALL`), plus a `.meld_import_table` section. A module that calls a function import is compiled this way with or without `--relocatable` (see [Import call boundary](#import-call-boundary-direct-bl-field-no-dispatcher)). There is no `__meld_dispatch_import`.
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
    {"index": 0, "module": "$root", "name": "[task-return]0", "kind": "p3-builtin"},
    {"index": 1, "module": "$root", "name": "[context-get-0]", "kind": "p3-builtin"},
    {"index": 12, "module": "wasi:cli/stderr@0.2.6", "name": "get-stderr", "kind": "wasi"}
  ]
}
```

This tells kiln-builtins which import is which WASI function or P3 async built-in. Synth does not use it for calls: it never passes an import index, it calls the symbol named by the import's field (see [Import call boundary](#import-call-boundary-direct-bl-field-no-dispatcher)).

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

The minimum viable set: one function **per wasm import**, under the import's
field name, plus the two below.

```rust
#![no_std]

/// One per import. Synth-compiled code calls it directly, per AAPCS: the wasm
/// arguments arrive in R0-R3 (then the stack), the result returns in R0
/// (R0:R1 for an i64). The SYMBOL is the import's bare wasm field name, so a
/// field that is not a Rust identifier needs `export_name`.
#[unsafe(export_name = "get-stderr")]
pub extern "C" fn wasi_cli_get_stderr() -> u32 {
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

## Import call boundary: direct `bl <field>`, no dispatcher

This is the contract synth implements (Refs #1696, #1755, #1699, #1758).
Earlier versions of this document described a dispatcher,
`__meld_dispatch_import(import_index)`. Synth's lowering for it passed the
import index in R0 and **none** of the wasm arguments, so it was removed; no
synth output references that symbol.

- **Symbol.** Each called wasm function import is an undefined symbol whose
  name is the import's **bare field name**, byte for byte (`poll-task`,
  `mpu-write`, `[task-return]0`). The module name is not part of it. Two
  imports that share a field name across modules are refused at compile time,
  as is a field name that collides with a symbol the object defines
  (RQ-91-NAMECOLL, #1698).
- **Call.** A direct AAPCS call: `bl <field>` with an `R_ARM_THM_CALL`
  relocation (`R_ARM_CALL` on A32). Arguments in R0-R3 then the stack, result
  in R0 (R0:R1 for i64). The callee may clobber R0-R3, R12 and the flags, as
  AAPCS allows; synth preserves what it needs across the call.
- **Registers the embedder owns.** R11 = linear-memory base, R10 = its size in
  bytes, R9 = globals-table base. The embedder sets all three before any
  export runs, and every function it provides must preserve them
  (`docs/embedder-abi-relocatable-arm.md`).
- **When.** Whenever a function of the module calls a function import.
  `--relocatable` is not needed to get this object, and `--cortex-m` does not
  produce a self-contained image for such a module: it produces this object
  and says so. An import that is declared but never called changes nothing.
- **kiln-builtins' P3 built-ins.** Functions named `__p3_task_return` and the
  like do not match field names such as `[task-return]0`. A provider needs an
  alias per imported field: `#[unsafe(export_name = "[task-return]0")]` (or a
  linker `--defsym`).

## P3 Async Built-in Imports

Meld-fused P3 async components produce core module imports for the Component
Model async built-ins. Kiln must recognize and dispatch these imports when
executing fused P3 modules (interpreter or AOT-compiled via synth).

### Import Names from `$root` Namespace

| Import name | Signature | Description |
|---|---|---|
| `[task-return]N` | varies per export N | Task return for export N. Multiple variants with different signatures. |
| `[context-get-0]` | `() -> i32` | Get task-local context slot 0. |
| `[context-set-0]` | `(i32) -> ()` | Set task-local context slot 0. |
| `[waitable-set-new]` | `() -> i32` | Create a new waitable set. |
| `[waitable-set-poll]` | `(i32, i32) -> i32` | Poll a waitable set. First arg = set handle, second = memory ptr for result. |
| `[waitable-set-drop]` | `(i32) -> ()` | Destroy a waitable set. |
| `[waitable-join]` | `(i32, i32) -> ()` | Join a waitable to a set. First arg = waitable handle, second = set handle. |

### Import Names from `[export]$root` Namespace

| Import name | Signature | Description |
|---|---|---|
| `[task-cancel]` | `(i32) -> i32` | Cancel a running task. Returns cancellation status. |

### Multi-Instance Suffix Convention

Meld suffixes import names with `$N` for multi-instance components:
- `[context-get-0]$2` — context get for component 2
- `[waitable-set-new]$5` — waitable-set-new for component 5

Each suffixed name is its **own link symbol** (`[context-get-0]$2` and
`[context-get-0]$5` are two undefined symbols in the object), because synth
calls an import by its bare field name. Kiln provides one exported function
per suffixed field; each strips the `$N` suffix to determine the built-in
operation and uses the suffix value to select the correct component's memory
and context state.

### Naming Convention Note

These names follow the component model internal naming convention. RFC 46
proposes standardized names (e.g., `env::[context[0].get]`). For now, kiln
handles meld's naming as documented. Future RFC 46 alignment is tracked.

## Multi-Memory Handling for P3 Fused Modules

Meld's fused P3 modules use multi-memory (one linear memory per original
component). The fused module exports all memories:

| Export name | Memory index | Component |
|---|---|---|
| `memory` | 0 | First component |
| `memory$0` | 1 | Component 0 |
| `memory$5` | 2 | Component 5 (CLI runner) |

Each WASI import and P3 built-in is associated with a specific component's
memory. The import suffix (`$2`, `$5`) indicates which component originated
the import, and therefore which memory to use for pointer arguments and
canonical ABI operations.

For single-memory targets (`--memory shared`), all components share one memory.
Multi-memory support is required for P3 async fused modules.

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
1. One `extern "C"` function per wasm import, exported under the import's bare field name, AAPCS calling convention (see [Import call boundary](#import-call-boundary-direct-bl-field-no-dispatcher))
2. `__meld_get_memory_base() -> *mut u8` — returns `__wasm_memory_start` linker symbol
3. `cabi_realloc(u32, u32, u32, u32) -> u32` — bump allocator in linear memory
4. Compiled as `libkiln_builtins.a` for `thumbv7em-none-eabi`
5. All symbols have `#[unsafe(no_mangle)]` / `extern "C"`

### Linker Symbols Synth Provides:
- `__wasm_memory_start` / `__wasm_memory_end` — linear memory bounds
- `__meld_import_table_start` / `__meld_import_table_end` — import metadata
- All exported WASM functions as global symbols (with Thumb bit set)

### Linker Symbols Synth Expects (undefined):
- one per called wasm import, named by its bare field name — provided by the embedder / kiln-builtins.a
- `__meld_get_memory_base` — provided by kiln-builtins.a (referenced by the `--link` linker script, not by compiled code)

---

## Priority Order

1. **Kiln: Create kiln-builtins stub** (even returning 0 for all imports — enables linking)
2. **Meld: Test fusing OSxCAR components** (verify single-memory output works)
3. **Kiln: Implement cabi_realloc** (bump allocator — enables canonical ABI)
4. **Meld: Add --emit-import-map** (tells the provider which import is which)
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
