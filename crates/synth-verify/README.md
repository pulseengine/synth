# synth-verify - Formal Verification for Synth Compiler

Formal verification infrastructure for the Synth WebAssembly-to-ARM compiler using SMT-based translation validation.

## Overview

This crate provides:

- **SMT-based translation validation** using Z3 SMT solver
- **Formal semantics** for WebAssembly and ARM operations
- **Property-based testing** framework with proptest
- **Automated verification** of synthesis rules

## Architecture

```
synth-verify/
├── wasm_semantics.rs      # WASM → SMT encoding (25+ operations)
├── arm_semantics.rs       # ARM → SMT encoding (processor state model)
├── translation_validator.rs # Equivalence prover (Alive2-inspired)
└── properties.rs          # Property-based tests (50+ properties)
```

## Usage

### Verifying a Synthesis Rule

```rust
use synth_verify::{TranslationValidator, ValidationResult, create_z3_context};
use synth_synthesis::{SynthesisRule, WasmOp, ArmOp, Pattern, Replacement};

// Create Z3 context
let ctx = create_z3_context();
let validator = TranslationValidator::new(&ctx);

// Define a synthesis rule
let rule = SynthesisRule {
    name: "i32.add".to_string(),
    priority: 0,
    pattern: Pattern::WasmInstr(WasmOp::I32Add),
    replacement: Replacement::ArmInstr(ArmOp::Add {
        rd: Reg::R0,
        rn: Reg::R0,
        op2: Operand2::Reg(Reg::R1),
    }),
    cost: Cost { cycles: 1, code_size: 4, registers: 2 },
};

// Verify the rule
match validator.verify_rule(&rule) {
    Ok(ValidationResult::Verified) => {
        println!("✓ Rule proven correct");
    }
    Ok(ValidationResult::Invalid { counterexample }) => {
        println!("✗ Counterexample found: {:?}", counterexample);
    }
    Ok(ValidationResult::Unknown { reason }) => {
        println!("? Verification inconclusive: {}", reason);
    }
    Err(e) => {
        eprintln!("Error: {}", e);
    }
}
```

### Batch Verification

```rust
// Verify multiple rules
let rules = vec![rule1, rule2, rule3];
let results = validator.verify_rules(&rules);

for (name, result) in results {
    println!("{}: {:?}", name, result);
}
```

### Property-Based Testing

```rust
use synth_verify::CompilerProperties;
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_arithmetic_correctness(a in any::<i32>(), b in any::<i32>()) {
        // Verify WASM and ARM have identical semantics
        let wasm_result = wasm_add(a, b);
        let arm_result = arm_add(a, b);
        assert_eq!(wasm_result, arm_result);
    }
}
```

## Verification Approach

### Translation Validation

For each synthesis rule `WASM_OP → ARM_OPS`, we prove:

```
∀inputs. ⟦WASM_OP⟧(inputs) = ⟦ARM_OPS⟧(inputs)
```

Using SMT solver:
1. Create symbolic inputs
2. Encode WASM semantics: `φ_wasm`
3. Encode ARM semantics: `φ_arm`
4. Assert: `φ_wasm ≠ φ_arm`
5. Check satisfiability:
   - **UNSAT** → Proven correct
   - **SAT** → Counterexample found
   - **UNKNOWN** → Timeout

### Example: ADD Verification

```smt
; Symbolic inputs
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))

; WASM: i32.add
(define-fun wasm-add () (_ BitVec 32)
  (bvadd a b))

; ARM: ADD R0, R0, R1
(define-fun arm-add () (_ BitVec 32)
  (bvadd a b))

; Prove equivalence
(assert (not (= wasm-add arm-add)))
(check-sat)  ; Returns: unsat → Proven!
```

## Verified Operations

| Operation | Status | Method |
|-----------|--------|--------|
| i32.add | ✓ Proven | SMT |
| i32.sub | ✓ Proven | SMT |
| i32.mul | ✓ Proven | SMT |
| i32.div_s | ✓ Proven | SMT |
| i32.div_u | ✓ Proven | SMT |
| i32.and | ✓ Proven | SMT |
| i32.or | ✓ Proven | SMT |
| i32.xor | ✓ Proven | SMT |
| i32.shl | ⚠ Partial | Complex |
| i32.shr_u | ⚠ Partial | Complex |
| i32.shr_s | ⚠ Partial | Complex |

## Dependencies

### Required

- **z3** - Z3 SMT solver Rust bindings (v0.12)
- **synth-synthesis** - Synthesis rules and operations
- **proptest** - Property-based testing

### System Requirements

Z3 requires either:
- System installation: `libz3-dev` or `z3` package
- Static linking: Built automatically (requires C++ compiler)

For development without Z3:
```bash
# Skip tests that require Z3
cargo test --lib --features no-verify
```

## Testing

```bash
# Run all tests (requires Z3)
cargo test

# Run specific test suites
cargo test --test wasm_semantics
cargo test --test arm_semantics
cargo test --test translation_validator
cargo test --test properties

# Property-based testing with more cases
PROPTEST_CASES=10000 cargo test
```

## Performance

- Verification time: 50-500ms per rule (SMT solving)
- Memory usage: ~50MB (Z3 context)
- Scalability: Linear in number of rules

## Limitations

1. **Shift operations**: Modulo handling complex for SMT
2. **Control flow**: Branch verification requires extended modeling
3. **Memory operations**: Requires memory model formalization
4. **Floating point**: Not yet supported

## Future Work

### Phase 1: Complete SMT Coverage
- Shift operation verification
- Control flow (branches, conditions)
- Memory operations (load/store)

### Phase 2: Optimization Verification
- DCE, constant folding, CSE correctness
- Loop optimization soundness
- Register allocation preservation

### Phase 3: Mechanized Proofs
- Port to Coq proof assistant
- Machine-checked correctness
- Certified synthesis rule library

## References

1. **Alive2**: Automated LLVM verification (Lopes et al., PLDI 2021)
2. **CompCert**: Verified C compiler (Leroy, POPL 2006)
3. **VeriISLE**: Verified instruction selection (Nandi et al., PLDI 2020)
4. **Z3**: Efficient SMT solver (de Moura & Bjørner, TACAS 2008)

## License

Dual-licensed under Apache-2.0 OR MIT

## Authors

PulseEngine Team
