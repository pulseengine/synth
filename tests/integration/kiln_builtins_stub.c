/*
 * Minimal kiln-builtins stub for bare-metal testing.
 *
 * Provides the two external symbols that synth-compiled code expects:
 *   - __meld_dispatch_import: routes WASM imports to host handlers
 *   - __meld_get_memory_base: returns WASM linear memory base address
 *
 * This is a test stub — the real implementation lives in kiln-builtins.
 * For Phase 1 bare-metal testing, all imports return 0.
 */

#include <stdint.h>

/* Linker-provided symbols for WASM linear memory region */
extern uint8_t __wasm_memory_start;
extern uint8_t __wasm_memory_end;

/*
 * Generic import dispatcher.
 *
 * Called by synth-compiled code via: MOV R0, #import_index; BL __meld_dispatch_import
 * The import index corresponds to entries in the .meld_import_table section.
 *
 * Stub: returns 0 for all imports.
 */
uint32_t __attribute__((used)) __meld_dispatch_import(uint32_t import_index)
{
    (void)import_index;
    return 0;
}

/*
 * Returns the base address of the WASM linear memory.
 *
 * The linker script places .wasm_linear_memory in RAM with
 * __wasm_memory_start and __wasm_memory_end bounding symbols.
 */
uint8_t * __attribute__((used)) __meld_get_memory_base(void)
{
    return &__wasm_memory_start;
}
