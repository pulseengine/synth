# Synth Rocq Verification

This directory contains the Rocq (formerly Coq) formalization and correctness proofs for the Synth WebAssembly-to-ARM compiler.

## Overview

Synth compiles WebAssembly to ARM assembly. This Rocq development proves that the compilation preserves semantics — i.e., that compiled ARM code behaves identically to the original WebAssembly code.

## Structure

```
Synth/
├── Common/
│   ├── Base.v            - Basic utilities, tactics, and notations
│   ├── Integers.v        - 32-bit and 64-bit integer formalization
│   └── StateMonad.v      - State monad for processor state transformations
│
├── ARM/
│   ├── ArmState.v        - ARM processor state (registers, flags, memory)
│   ├── ArmInstructions.v - ARM instruction set definition
│   └── ArmSemantics.v    - Operational semantics of ARM instructions
│
├── WASM/
│   ├── WasmValues.v      - WebAssembly value types and stack
│   ├── WasmInstructions.v- WebAssembly instruction set
│   └── WasmSemantics.v   - Operational semantics of WASM (stack machine)
│
└── Synth/
    ├── Compilation.v     - WASM→ARM compilation function
    └── Correctness.v     - Correctness theorems proving compilation is sound
```

## Building

### Prerequisites

```bash
# Install OPAM (OCaml package manager)
sudo apt-get install opam

# Initialize OPAM
opam init

# Install Rocq 9.0 (formerly Coq)
opam install rocq-prover.9.0.0

# Install useful libraries
opam install coq-mathcomp-ssreflect coq-ext-lib coq-stdpp
```

### Build Instructions

```bash
# Via Bazel (hermetic — uses Nix for Rocq toolchain):
bazel test //coq:verify_proofs

# Via Make (requires local Rocq 9 installation):
cd coq && make proofs

# To clean build artifacts:
cd coq && make clean
```

## Current Status

See [STATUS.md](STATUS.md) for the detailed per-file coverage matrix.

| Metric | Value |
|--------|-------|
| `.v` files | 23 |
| `Qed.` (closed proofs) | 106 |
| `Admitted.` (open) | 122 |
| Axioms (modeling) | 10 |

### Completed

- Integer representations (I32, I64) with modular arithmetic
- ARM processor state model (16 registers + flags + VFP + memory)
- WASM stack machine model (stack + locals + globals + memory)
- 60+ ARM instructions, 150+ WASM instructions formalized
- Compilation function (`compile_wasm_to_arm`)
- Custom tactics library (`synth_binop_proof`, `synth_comparison_proof`, `synth_unop_proof`)
- i32 arithmetic/bitwise proofs (add, sub, mul, div, and, or, xor)

### Open Work

- Most comparison/shift/bit-manipulation proofs need register correspondence lemmas
- i64 proofs need 64-bit register handling
- f32/f64 proofs need Flocq library integration
- Memory model, control flow proofs
- Sail ARM integration (replace hand-written semantics)

## Example Proofs

### I32.Add Correctness

```coq
Theorem compile_i32_add_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32Add wstate =
    Some (mkWasmState
            (VI32 (I32.add v1 v2) :: stack')
            wstate.(locals)
            wstate.(globals)
            wstate.(memory)) ->
  exists astate',
    exec_program (compile_wasm_to_arm I32Add) astate = Some astate' /\
    get_reg astate' R0 = I32.add v1 v2.
Proof.
  (* Proof omitted - see Synth/Correctness.v *)
Qed.
```

This theorem states:
- **Given**: WASM stack with v1 and v2, ARM state with R0=v1 and R1=v2
- **When**: We execute WASM I32.Add and compiled ARM code
- **Then**: Both produce the same result: v1 + v2

## Certification

This Rocq development supports ISO 26262 ASIL D qualification:

- `Synth/**/*.v`: Formal specifications and proofs
- Proof certificates (`.vo` files)
- OCaml extraction (`Extraction/CompilerExtract.v`)
- Traceability: WASM operation → ARM code → Rocq proof

## Integration with Synth

### Correspondence to Rust Code

This Rocq development mirrors the Rust implementation:

| Rocq File | Rust File |
|----------|-----------|
| `ARM/ArmState.v` | `crates/synth-verify/src/arm_semantics.rs::ArmState` |
| `ARM/ArmInstructions.v` | `crates/synth-synthesis/src/rules.rs::ArmOp` |
| `WASM/WasmInstructions.v` | `crates/synth-synthesis/src/lib.rs::WasmOp` |
| `Synth/Compilation.v` | `crates/synth-synthesis/src/rules.rs::SynthesisRule` |

### Testing Strategy

1. **Property-based testing** (Rust + proptest): Random testing
2. **SMT verification** (Rust + Z3): Bounded verification
3. **Rocq proofs**: Unbounded mathematical proof

All three approaches complement each other:
- Proptest finds bugs quickly
- Z3 verifies within bounds (e.g., 32-bit integers)
- Rocq proves for all possible inputs

## Contributing

See [PROOF_GUIDE.md](PROOF_GUIDE.md) for the contributor guide, and [DECISIONS.md](DECISIONS.md) for spec baselines.

## References

- [Software Foundations](https://softwarefoundations.cis.upenn.edu/) — Intro to Rocq
- [CompCert](https://github.com/AbsInt/CompCert) — Verified C compiler
- [CakeML](https://github.com/CakeML/cakeml) — Verified ML compiler with ARM backend
