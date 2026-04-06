# P3 Async Codegen: Reentrancy Guard and Built-in Import Dispatch

## Status

Phase 4 design -- not yet implemented. This document describes the ARM codegen
changes needed for Component Model entry/exit sequences and the
`recursive_reentrance` flag.

## Background

The Component Model spec (Concurrency.md) requires a **reentrancy guard** at
the entry point of each canonical ABI lifted function. Before a component
instance can be entered, the runtime checks a `may_enter` flag. If the flag is
`false` (the instance is already on the call stack), the call **traps**.

After meld fusion, multiple original component instances collapse into a single
instance. Cross-component calls that were previously inter-instance now become
intra-instance -- and the reentrancy guard incorrectly traps them.

The `recursive_reentrance` flag (already present on `ComponentInstance` in
synth-core and `AbiOptions` in synth-abi) tells the AOT compiler to **skip**
the guard for a given instance. This is an opt-in extension ahead of the spec's
planned `recursive` effect on function types.

## Current Codegen Architecture

```
WASM ops
  -> InstructionSelector::select_with_stack()   [synth-synthesis]
     -> function prologue (PUSH {R4-R8, LR})
     -> body (WASM op -> ARM instruction sequences)
        -> Call(idx < num_imports) -> MOV R0, #idx; BL __meld_dispatch_import
        -> Call(idx >= num_imports) -> BL func_N
     -> function epilogue (POP {R4-R8, PC})
  -> validate_instructions()                    [ISA feature gate]
  -> ArmEncoder::encode()                       [synth-backend]
  -> ELF emission with relocations              [synth-backend]
```

The pipeline currently has **no** canonical ABI entry/exit sequence. Functions
get a standard AAPCS prologue/epilogue, and import calls dispatch through the
Kiln bridge via `__meld_dispatch_import`. There is no `may_enter` check.

## Design: Canonical ABI Entry Sequence

### Where It Goes

The reentrancy guard is inserted **after** the function prologue in
`InstructionSelector::select_with_stack()` (in
`crates/synth-synthesis/src/instruction_selector.rs`), and the exit sequence
(clearing the guard) is inserted **before** the function epilogue.

This applies to **exported** functions only -- functions that represent
canon-lifted entry points. Internal (non-exported) functions do not need
the guard. The `CompileConfig` struct (in `crates/synth-core/src/backend.rs`)
must be extended to carry the `recursive_reentrance` flag.

### ARM Instruction Sequence

#### With reentrancy guard (default, `recursive_reentrance = false`)

```
; --- Function prologue ---
    PUSH  {R4-R8, LR}

; --- Reentrancy guard (canon entry) ---
    LDR   R4, =__may_enter_instance_N     ; address of the may_enter flag
    LDRB  R5, [R4, #0]                    ; load current flag value
    CMP   R5, #0                          ; is instance already active?
    BEQ   .trap_reentrant                 ; trap if may_enter == 0
    MOV   R5, #0
    STRB  R5, [R4, #0]                    ; set may_enter = 0 (now active)

; --- Function body ---
    ...

; --- Reentrancy guard exit (canon exit) ---
    MOV   R5, #1
    STRB  R5, [R4, #0]                    ; restore may_enter = 1

; --- Function epilogue ---
    POP   {R4-R8, PC}

; --- Trap handler ---
.trap_reentrant:
    UDF   #0                              ; generate trap (HardFault)
```

The `__may_enter_instance_N` symbol is a linker-provided address in BSS,
one byte per component instance. Initialized to 1 (may enter) at startup.
For single-instance fused components, `N = 0`.

#### Without reentrancy guard (`recursive_reentrance = true`)

```
; --- Function prologue ---
    PUSH  {R4-R8, LR}

; --- No reentrancy guard ---

; --- Function body ---
    ...

; --- No reentrancy exit ---

; --- Function epilogue ---
    POP   {R4-R8, PC}
```

This is the current behavior -- no change needed when the flag is true.

### Register Usage

The guard uses R4 and R5 (callee-saved, already pushed in prologue):
- R4 holds the address of the `may_enter` flag for the duration of the function
  (available for the exit sequence without reloading).
- R5 is a scratch register for load/compare/store.

This does not conflict with the existing prologue which already pushes R4-R8.

### Data Section Requirements

Each component instance needs a 1-byte `may_enter` flag in BSS:

```
.section .bss.meld_reentrance_flags, "aw", %nobits
    .global __may_enter_instance_0
    .align 2
__may_enter_instance_0:
    .byte 0    ; initialized to 1 by startup code (Reset_Handler)
```

The startup code (`reset_handler.rs` / `arm_startup.rs`) must initialize these
to 1 before calling any exported WASM functions.

## P3 Async Built-in Import Dispatch

Meld-fused P3 async components produce core module imports from the `$root`
namespace for Component Model async built-ins. These are dispatched through
`__meld_dispatch_import` the same way as WASI imports -- the import index in
R0 tells the Kiln bridge which built-in to invoke.

### Import Name to Dispatch Index Mapping

The mapping is established by meld's `--emit-import-map` output:

| Import Index | Name | Handler |
|---|---|---|
| 0 | `[task-return]0` | Kiln: complete current task with result |
| 1 | `[context-get-0]` | Kiln: read task-local context slot |
| 2 | `[context-set-0]` | Kiln: write task-local context slot |
| 3 | `[waitable-set-new]` | Kiln: create waitable set |
| 4 | `[waitable-set-poll]` | Kiln: poll waitable set |
| ... | ... | ... |

### ARM Call Sequence (unchanged)

P3 async built-in calls use the same dispatch mechanism as all other imports:

```
    MOV   R0, #import_index
    BL    __meld_dispatch_import
    ; result in R0
```

No special ARM codegen is needed for P3 built-ins. The Kiln bridge
(`kiln-builtins`) handles the routing based on the import table metadata.

## Implementation Plan

### Step 1: Extend `CompileConfig`

Add `recursive_reentrance: bool` to `CompileConfig` in
`crates/synth-core/src/backend.rs`. Wire it from CLI flags and component
metadata.

### Step 2: Generate Guard in Instruction Selector

In `InstructionSelector::select_with_stack()`, after the prologue PUSH:
- If `recursive_reentrance == false`, emit the LDR/LDRB/CMP/BEQ/STRB
  guard sequence.
- If `recursive_reentrance == true`, emit nothing (current behavior).

Before each epilogue POP (both normal end and early Return):
- If `recursive_reentrance == false`, emit the STRB to restore
  `may_enter = 1`.

### Step 3: Add ArmOp Variants (if needed)

The guard sequence uses only existing ARM ops (LDR, LDRB, CMP, BEQ, MOV,
STRB, UDF). No new `ArmOp` variants are required, though a pseudo-op
like `ArmOp::ReentrancyGuardEntry` / `ArmOp::ReentrancyGuardExit` could
be added for clarity in the IR before encoding.

### Step 4: Linker Script and Startup

Update `LinkerScriptGenerator` to emit the `.bss.meld_reentrance_flags`
section. Update `ResetHandlerGenerator` to initialize flags to 1.

### Step 5: Testing

- Unit test: instruction selector emits guard when `recursive_reentrance = false`
- Unit test: instruction selector skips guard when `recursive_reentrance = true`
- Integration test: ELF contains `__may_enter_instance_0` symbol
- Renode test: fused component with `recursive_reentrance = true` does not trap
  on cross-component calls

## References

- Component Model Concurrency.md -- `call_might_be_recursive` check
- `crates/synth-core/src/component.rs` -- `ComponentInstance::recursive_reentrance`
- `crates/synth-abi/src/options.rs` -- `AbiOptions::recursive_reentrance`
- `artifacts/component-model.yaml` -- CM-006 requirement
- `docs/design/meld-kiln-integration-instructions.md` -- dispatch ABI contract
