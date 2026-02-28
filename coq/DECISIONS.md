# Synth Proof Suite -- Specification Baselines and Modeling Decisions

## Specification Baselines

| Domain | Specification | Version |
|--------|--------------|---------|
| WebAssembly | [WebAssembly Core Specification](https://www.w3.org/TR/wasm-core-1/) | 1.0 |
| ARM Target | ARM Architecture Reference Manual (Cortex-M profile) | ARMv7-M |
| Proof Assistant | [Rocq](https://rocq-prover.org/) (formerly Coq) | 9.0 |
| Standard Library | Rocq Stdlib (`ZArith`, `Ring`) | ships with Rocq 9.0 |

## Key Modeling Decisions

### 1. Integer Representation

Integers (`I32`, `I64`) are modeled as Coq `Z` values with modular arithmetic wrappers. Operations like `add`, `sub`, `mul` apply `Z.modulo` to keep values within 32- or 64-bit range. This matches the WebAssembly spec's wrapping semantics.

Axioms are used for `clz`, `ctz`, `popcnt` (bit manipulation functions that are well-understood but tedious to formalize in `Z`). These are low-risk axioms that could be replaced with `Zdigits`-based proofs.

### 2. ARM State Model

The ARM state is modeled as a record with:
- 16 general-purpose registers (`R0`-`R15`)
- Condition flags (N, Z, C, V)
- VFP registers (for floating-point, currently stubs)
- Memory (modeled as `Z -> I32.int`)

This captures the Cortex-M4 programmer's model. APSR/CPSR details beyond NZCV are abstracted away.

### 3. WASM State Model

The WASM state is a stack machine with:
- Operand stack (list of `wasm_value`)
- Local variables (list of `wasm_value`)
- Global variables (list of `wasm_value`)
- Linear memory (modeled as `Z -> I32.int`)

This models the WebAssembly 1.0 execution semantics faithfully.

### 4. Compilation Function

`compile_wasm_to_arm` maps a single WASM instruction to a list of ARM instructions. The correctness theorem pattern is:

> Given matching preconditions (WASM operands on stack, ARM operands in registers),
> executing the compiled ARM code produces a result register value equal to the
> WASM instruction's semantics.

This is a *per-instruction* correctness statement, not end-to-end. Composing these into a full-program theorem is future work.

### 5. Register Convention

- `R0`: first operand / result
- `R1`: second operand
- `R2`-`R3`: temporaries (used for remainder, multi-step sequences)
- `R12`: scratch register for extended sequences

For i64 operations (future): `R0:R1` = first operand pair, `R2:R3` = second.

### 6. Floating-Point

Floating-point operations are defined but semantics are stubs (`Some s` -- identity). Full IEEE 754 formalization requires the Flocq library, which is not yet integrated. All f32/f64 correctness theorems are `Admitted`.

### 7. Memory Operations

Memory is modeled as a total function `Z -> I32.int` with explicit load/store operations. Two properties are proven:
- `load_store_mem_eq`: loading from a just-stored address returns the stored value
- `load_store_mem_neq`: loading from a different address is unaffected by a store

Connecting these to the ARM LDR/STR instruction semantics is in progress.
