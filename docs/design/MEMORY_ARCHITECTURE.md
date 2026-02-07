# Memory Architecture for Synth

This document outlines memory handling strategies for the Synth WASM-to-ARM compiler, based on research into efficient bounds checking, MPU utilization, and multi-memory support.

## Current Implementation

### What's Implemented

| Feature | Status | Location |
|---------|--------|----------|
| Load/Store (i32) | ✅ Working | `instruction_selector.rs` → LDR/STR |
| Linear memory base | Hardcoded | `0x20000000` (RAM base) |
| Software bounds checking | ✅ ABI layer only | `synth-abi/src/memory.rs` |
| MPU region allocation | ✅ Implemented | `mpu_allocator.rs` |
| Multi-memory API | Placeholder | `AbiOptions.memory_index` |

### Memory Layout

```
0x00000000 ┌──────────────────┐
           │   Flash (Code)   │  Vector table, startup, functions
           │                  │
0x20000000 ├──────────────────┤
           │   RAM (Data)     │  Linear memory, stack, heap
           │                  │
0x20010000 └──────────────────┘  (64KB RAM end, stack top)
```

## Bounds Checking Strategies

### 1. Software Bounds Checking (Current)

**Implementation:** Check address bounds before every load/store.

```rust
// Current implementation in synth-abi/src/memory.rs
if end > self.data.len() {
    return Err(AbiError::Trap("Memory access out of bounds"));
}
```

**Overhead:**
- **Cortex-M4:** ~25% slowdown ([aWsm benchmarks](https://github.com/gwsystems/aWsm))
- **Cortex-M7:** ~40% slowdown

**Pros:** Simple, portable, no hardware requirements
**Cons:** High overhead on in-order cores

### 2. MPU-Based Protection (Recommended for Cortex-M)

**Concept:** Configure MPU regions to create guard pages; illegal access triggers HardFault.

**Implementation approach:**
```
┌─────────────────────────────────────┐
│          Guard Region (No Access)   │  ← Triggers HardFault
├─────────────────────────────────────┤
│          Linear Memory (RW)         │  ← Valid WASM memory
│          (power-of-2 size)          │
├─────────────────────────────────────┤
│          Guard Region (No Access)   │  ← Triggers HardFault
└─────────────────────────────────────┘
```

**Key constraints (ARMv7-M):**
- Region size must be power of 2 (min 32 bytes)
- Base address must be aligned to region size
- Maximum 8 regions on Cortex-M3/M4, 16 on Cortex-M7

**Overhead:** Near-zero for valid accesses (hardware check)

**References:**
- [OmniWasm (IEEE RTAS 2024)](http://www.runyupan.com/wp-content/uploads/2024/08/7-pan24owasm.pdf)
- [ARM MPU Documentation](https://medium.com/@wadixtech/cortex-m3-mpu-91d8aa9c08e7)

### 3. Address Masking (Power-of-2 Memory)

**Concept:** If memory size is power of 2, mask addresses instead of bounds checking.

```rust
// For 64KB memory (0x10000 bytes)
let masked_addr = addr & 0xFFFF;  // Always in bounds
```

**Overhead:** Single AND instruction per access (~5% overhead)

**Limitation:** Wastes memory if actual needs are not power-of-2

### 4. Memory Tagging (Cortex-A only)

[Cage (arXiv 2024)](https://arxiv.org/html/2408.11456v1) uses ARM MTE for hardware-accelerated bounds checking. **Not available on Cortex-M.**

## Recommended Strategy for Synth

### Phase 1: MPU Guard Regions

1. Allocate linear memory with guard regions:
   ```
   size_with_guards = round_up_power2(wasm_memory_size + 2 * guard_size)
   ```

2. Configure MPU:
   - Region 0: Lower guard (No Access)
   - Region 1: Linear memory (RW, Privileged + Unprivileged)
   - Region 2: Upper guard (No Access)

3. Generate unprivileged load/store:
   ```arm
   LDRT Rd, [Rn, #offset]   ; Unprivileged load (respects MPU)
   STRT Rd, [Rn, #offset]   ; Unprivileged store
   ```

### Phase 2: Hybrid Approach

For non-power-of-2 memory or when MPU regions are exhausted:

```rust
if memory_size.is_power_of_two() && mpu_regions_available() {
    use_mpu_protection()
} else {
    use_software_masking()  // addr & (size - 1) for power-of-2
                            // or full bounds check
}
```

## Multi-Memory Implementation

### WebAssembly Multi-Memory Proposal

The [multi-memory proposal](https://github.com/WebAssembly/multi-memory) allows multiple linear memories per module:

```wat
(memory $mem0 1)
(memory $mem1 1)
(i32.load $mem1 (i32.const 0))  ; Load from memory 1
```

### Implementation Strategy

#### Option A: Multiple Base Registers (Fast Path)

Reserve registers for frequently-used memories:
- R11: Memory 0 base (most common)
- R10: Memory 1 base (if needed)

```arm
; Load from memory 0 (fast path)
LDR Rd, [R11, Rn]

; Load from memory 1
LDR Rd, [R10, Rn]
```

**Trade-off:** Uses scarce registers but avoids indirection.

#### Option B: Memory Descriptor Table

Store memory bases in a table, load on demand:

```rust
struct MemoryDescriptor {
    base: u32,
    size: u32,
    mpu_region: u8,
}

// At runtime
static MEMORY_TABLE: [MemoryDescriptor; MAX_MEMORIES] = ...;
```

```arm
; Load memory base for index in R0
LDR R12, =MEMORY_TABLE
LDR R12, [R12, R0, LSL #3]  ; Load base address
LDR Rd, [R12, Rn]            ; Actual memory access
```

**Trade-off:** Extra indirection but flexible.

#### Recommended: Hybrid

- **Memory 0:** Dedicated register (R11) for zero-overhead access
- **Memory 1+:** Table lookup when accessed

### Bounds Checking for Multi-Memory

Each memory needs its own bounds:

```arm
; Check bounds for memory N
LDR R12, =MEMORY_TABLE
ADD R12, R12, R_memidx, LSL #3
LDR R_base, [R12, #0]    ; Load base
LDR R_size, [R12, #4]    ; Load size
CMP Rn, R_size           ; Compare address with size
BHS trap_handler         ; Branch if out of bounds
LDR Rd, [R_base, Rn]     ; Safe to load
```

Or with MPU: configure separate regions per memory.

## Performance Summary

| Strategy | Overhead | Hardware Required | Notes |
|----------|----------|-------------------|-------|
| Software bounds check | 25-40% | None | Portable, simple |
| Address masking | ~5% | None | Power-of-2 memory only |
| MPU guard regions | ~0% | Cortex-M3+ MPU | Recommended for safety-critical |
| MTE (Cage) | ~0% | Cortex-A MTE | Not available on Cortex-M |

## Implementation Roadmap

1. **Short-term:** Keep software bounds checking in ABI layer
2. **Medium-term:** Add MPU configuration for Cortex-M targets
3. **Long-term:** Implement multi-memory with hybrid base register/table approach

## References

- [aWsm Runtime](https://github.com/gwsystems/aWsm) - Multiple bounds checking strategies
- [OmniWasm](http://www.runyupan.com/wp-content/uploads/2024/08/7-pan24owasm.pdf) - MPU-based sandboxing
- [Cage](https://arxiv.org/html/2408.11456v1) - Hardware-accelerated WebAssembly
- [WebAssembly Multi-Memory](https://github.com/WebAssembly/multi-memory) - Official proposal
- [ARM Cortex-M MPU](https://medium.com/@wadixtech/cortex-m3-mpu-91d8aa9c08e7) - MPU programming guide
