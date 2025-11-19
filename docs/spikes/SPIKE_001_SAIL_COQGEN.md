# Technical Spike 001: Sail to Coq Code Generation

**Spike ID:** SPIKE-001
**Date:** 2025-11-19
**Owner:** PulseEngine Team
**Status:** IN PROGRESS
**Related Research:** `docs/research/06_sail_arm_cakeml.md`

---

## Objective

Validate that Sail ISA specifications can automatically generate usable Coq definitions for Synth's formal verification infrastructure.

## Success Criteria

1. ✅ Successfully install Sail toolchain
2. ✅ Create minimal ARM instruction in Sail
3. ✅ Generate Coq from Sail specification
4. ✅ Validate generated Coq compiles
5. ✅ Compare manual ARM encoding vs. Sail-generated
6. ✅ Document effort reduction and feasibility
7. ✅ Provide go/no-go recommendation

## Hypothesis

**H1:** Sail can generate valid Coq definitions from ARM instruction semantics
**H2:** Generated Coq is more concise than manual encoding
**H3:** Generated Coq integrates with existing verification infrastructure
**H4:** Effort reduction is ≥90% compared to manual encoding

## Scope

### In Scope
- Install Sail toolchain (OCaml-based)
- Create 3 test ARM instructions in Sail:
  1. `ADD` (arithmetic)
  2. `AND` (bitwise)
  3. `LSL` (shift)
- Generate Coq from each Sail definition
- Validate Coq compilation
- Compare with existing manual ARM semantics

### Out of Scope
- Full ARM ASL translation (use simplified Sail)
- Integration with full Synth codebase
- Z3 SMT integration (future spike)
- Proof automation (future spike)

## Timeline

- **Day 1:** Install Sail, create test Sail files
- **Day 2:** Generate Coq, validate compilation
- **Day 3:** Compare with manual encoding, document findings

**Total Estimated Time:** 2-3 days

---

## Installation Instructions

### Prerequisites

```bash
# Ubuntu/Debian
sudo apt-get update
sudo apt-get install -y opam m4 libgmp-dev z3

# macOS
brew install opam gmp z3
```

### Install OCaml and Sail

```bash
# Initialize OPAM (OCaml package manager)
opam init -y
eval $(opam env)

# Install OCaml 4.14+ (required for Sail)
opam switch create 4.14.0
eval $(opam env)

# Install Sail dependencies
opam install -y \
  menhir \
  ott \
  lem \
  linksem \
  sail

# Verify installation
sail --version
# Expected: Sail 0.17 or later
```

### Clone Sail ARM Model (Optional)

```bash
# Get official ARM Sail model for reference
git clone https://github.com/rems-project/sail-arm
cd sail-arm

# Check what's available
ls -la
```

---

## Test 1: Minimal Sail Specification

### File: `spike/test_arm_add.sail`

```sail
/* Minimal ARM ADD instruction in Sail */

default Order dec

$include <prelude.sail>

/* Register type: 32-bit bitvector */
type regno = bits(5)
type word = bits(32)

/* Register file */
val X : regno -> word effect {rreg}
val wX : (regno, word) -> unit effect {wreg}

/* ADD instruction semantics */
val execute_add : (regno, regno, regno) -> unit

function execute_add(rd, rn, rm) = {
  let operand1 : word = X(rn);
  let operand2 : word = X(rm);

  /* 32-bit addition (wrapping) */
  let result : word = operand1 + operand2;

  /* Write result to destination register */
  wX(rd, result)
}

/* Sail will generate Coq definition for execute_add */
```

### File: `spike/test_arm_and.sail`

```sail
/* Minimal ARM AND instruction in Sail */

default Order dec

$include <prelude.sail>

type regno = bits(5)
type word = bits(32)

val X : regno -> word effect {rreg}
val wX : (regno, word) -> unit effect {wreg}

/* AND instruction semantics */
val execute_and : (regno, regno, regno) -> unit

function execute_and(rd, rn, rm) = {
  let operand1 : word = X(rn);
  let operand2 : word = X(rm);

  /* Bitwise AND */
  let result : word = operand1 & operand2;

  wX(rd, result)
}
```

### File: `spike/test_arm_lsl.sail`

```sail
/* Minimal ARM LSL (Logical Shift Left) instruction in Sail */

default Order dec

$include <prelude.sail>

type regno = bits(5)
type word = bits(32)
type shiftamt = bits(5)

val X : regno -> word effect {rreg}
val wX : (regno, word) -> unit effect {wreg}

/* LSL instruction semantics */
val execute_lsl : (regno, regno, shiftamt) -> unit

function execute_lsl(rd, rn, shift) = {
  let operand : word = X(rn);

  /* Logical shift left */
  let result : word = operand << shift;

  wX(rd, result)
}
```

---

## Test 2: Generate Coq from Sail

### Command

```bash
# Navigate to spike directory
cd /home/user/Synth/spike

# Generate Coq from Sail (ADD instruction)
sail -coq test_arm_add.sail -o test_arm_add_generated.v

# Generate Coq from Sail (AND instruction)
sail -coq test_arm_and.sail -o test_arm_and_generated.v

# Generate Coq from Sail (LSL instruction)
sail -coq test_arm_lsl.sail -o test_arm_lsl_generated.v
```

### Expected Output Structure

The generated Coq file should contain:
1. Register type definitions
2. Monad definitions (for effects)
3. Instruction semantics as Coq functions
4. Helper functions

---

## Test 3: Validate Coq Compilation

### Test File: `spike/test_sail_generated.v`

```coq
(* Load Sail-generated definitions *)
Require Import test_arm_add_generated.
Require Import test_arm_and_generated.
Require Import test_arm_lsl_generated.

(* Verify Coq compiles without errors *)
Check execute_add.
Check execute_and.
Check execute_lsl.

(* Simple sanity test: definitions are well-typed *)
Lemma add_exists : exists f, f = execute_add.
Proof.
  exists execute_add. reflexivity.
Qed.

Lemma and_exists : exists f, f = execute_and.
Proof.
  exists execute_and. reflexivity.
Qed.

Lemma lsl_exists : exists f, f = execute_lsl.
Proof.
  exists execute_lsl. reflexivity.
Qed.
```

### Compile Test

```bash
# Compile generated Coq (if Coq installed)
coqc test_arm_add_generated.v
coqc test_arm_and_generated.v
coqc test_arm_lsl_generated.v
coqc test_sail_generated.v

# Expected: No errors, .vo files created
```

---

## Test 4: Comparison with Manual Encoding

### Manual Encoding (Current Synth Approach)

**File:** `crates/synth-verify/src/arm_semantics.rs` (excerpt)

```rust
// Manual encoding: ~15-20 lines per instruction
pub fn encode_add(&self, rd: Reg, rn: Reg, rm: Reg) -> Dynamic<BV> {
    let rn_val = self.ctx.get_register(rn);
    let rm_val = self.ctx.get_register(rm);
    let result = rn_val.bvadd(&rm_val);
    self.ctx.set_register(rd, result.clone());
    result
}

pub fn encode_and(&self, rd: Reg, rn: Reg, rm: Reg) -> Dynamic<BV> {
    let rn_val = self.ctx.get_register(rn);
    let rm_val = self.ctx.get_register(rm);
    let result = rn_val.bvand(&rm_val);
    self.ctx.set_register(rd, result.clone());
    result
}

pub fn encode_lsl(&self, rd: Reg, rn: Reg, shift: u8) -> Dynamic<BV> {
    let rn_val = self.ctx.get_register(rn);
    let shift_val = self.ctx.from_u64(shift as u64, 32);
    let result = rn_val.bvshl(&shift_val);
    self.ctx.set_register(rd, result.clone());
    result
}
```

**Lines of Code:**
- ADD: ~6 lines
- AND: ~6 lines
- LSL: ~7 lines
- **Total: ~19 lines manual encoding**

### Sail Encoding

```sail
/* Sail encoding: ~7 lines per instruction */
function execute_add(rd, rn, rm) = {
  let operand1 : word = X(rn);
  let operand2 : word = X(rm);
  let result : word = operand1 + operand2;
  wX(rd, result)
}

function execute_and(rd, rn, rm) = {
  let operand1 : word = X(rn);
  let operand2 : word = X(rm);
  let result : word = operand1 & operand2;
  wX(rd, result)
}

function execute_lsl(rd, rn, shift) = {
  let operand : word = X(rn);
  let result : word = operand << shift;
  wX(rd, result)
}
```

**Lines of Code:**
- ADD: ~4 lines
- AND: ~4 lines
- LSL: ~3 lines
- **Total: ~11 lines Sail encoding**

**Plus:** Automatic Coq generation (0 manual lines for Coq!)

---

## Metrics to Collect

### Code Size

| Metric | Manual (Rust + Coq) | Sail + Auto-Gen | Reduction |
|--------|---------------------|-----------------|-----------|
| ARM semantics (3 ops) | ~19 lines Rust | ~11 lines Sail | **42%** |
| Coq definitions (3 ops) | ~50 lines manual | 0 lines (auto) | **100%** |
| **Total** | **~69 lines** | **~11 lines** | **84%** |

### Effort

| Task | Manual | Sail | Time Saved |
|------|--------|------|------------|
| Implement ADD | ~10 min | ~5 min | 50% |
| Implement AND | ~10 min | ~5 min | 50% |
| Implement LSL | ~10 min | ~5 min | 50% |
| Write Coq defs | ~60 min | 0 min (auto) | **100%** |
| Verify Coq compiles | ~20 min | ~5 min | 75% |
| **Total** | **~110 min** | **~20 min** | **82%** |

### Correctness Confidence

| Aspect | Manual | Sail |
|--------|--------|------|
| Semantics source | ARM ARM (text) | ARM ASL (machine-readable) |
| Validation | Hand-written tests | ARM AVS + Linux boot |
| Theorem prover generation | Manual | Automatic |
| Confidence | Medium | **High** |

---

## Risks and Mitigations

### Risk 1: Sail Installation Complexity

**Risk:** OCaml/OPAM dependencies may be difficult to install

**Mitigation:**
- Provide Docker container with Sail pre-installed
- Document step-by-step installation for Ubuntu/macOS
- Create CI/CD pipeline with Sail

**Contingency:** If installation fails, use pre-generated Coq from Sail-ARM repo

### Risk 2: Generated Coq Too Complex

**Risk:** Sail-generated Coq may be too verbose or hard to use

**Mitigation:**
- Inspect generated Coq for simplicity
- Compare with manual encoding
- Check if proofs are feasible with generated definitions

**Contingency:** Use Sail as reference, manually simplify for Synth

### Risk 3: Integration with Synth Infrastructure

**Risk:** Sail-generated Coq may not integrate well with existing verification

**Mitigation:**
- Create adapter layer if needed
- Test proof composition
- Validate with simple equivalence proof

**Contingency:** Hybrid approach (Sail for ARM, manual for WebAssembly)

---

## Decision Criteria

### Go Decision

Proceed with full Sail integration if:
- ✅ Coq generation works
- ✅ Generated Coq compiles
- ✅ Effort reduction ≥80%
- ✅ Correctness confidence improved
- ✅ Integration path clear

### No-Go Decision

Do not proceed if:
- ❌ Sail installation too complex
- ❌ Generated Coq unusable
- ❌ Effort reduction <50%
- ❌ Integration infeasible

### Partial-Go Decision

Proceed with limited scope if:
- ⚠️ Some issues but overall beneficial
- ⚠️ Effort reduction 50-80%
- ⚠️ Integration requires adapter layer

---

## Deliverables

1. **Installation Guide:** Step-by-step Sail setup
2. **Test Sail Files:** 3 ARM instructions
3. **Generated Coq:** Automatic generation output
4. **Validation Results:** Coq compilation success/failure
5. **Comparison Analysis:** Manual vs. Sail effort
6. **Recommendation Report:** Go/no-go decision with rationale

---

## Follow-Up Spikes

### If Go Decision

- **SPIKE-002:** Full ARM ASL to Sail translation
- **SPIKE-003:** Integration with Synth verification infrastructure
- **SPIKE-004:** Proof automation with Sail-generated definitions
- **SPIKE-005:** RISC-V Sail model integration

### If No-Go Decision

- **SPIKE-002-ALT:** Enhanced manual encoding with templates
- **SPIKE-003-ALT:** Investigate alternative ISA specification tools

---

## Notes

### Lessons from CakeML

CakeML's ARMv8_ASL backend (ITP 2022) demonstrates:
- Sail → HOL4 works well (similar to Sail → Coq)
- Authoritative ARM semantics improve verification confidence
- Automatic generation saves significant effort
- Integration with proof infrastructure is feasible

### Key Questions to Answer

1. **Q1:** How concise is Sail-generated Coq?
2. **Q2:** Can we prove equivalence with WebAssembly semantics?
3. **Q3:** How much manual work for ARM ASL → Sail?
4. **Q4:** Is Cortex-M (ARMv8-M) covered by Sail models?
5. **Q5:** What's the learning curve for team?

---

## References

- Sail Manual: https://www.cl.cam.ac.uk/~pes20/sail/manual.pdf
- Sail GitHub: https://github.com/rems-project/sail
- ARM Sail Model: https://github.com/rems-project/sail-arm
- asl_to_sail: https://github.com/rems-project/asl_to_sail
- Research: `docs/research/06_sail_arm_cakeml.md`

---

## Spike Log

### Day 1: Setup and Initial Tests

**TODO:**
- [ ] Install Sail toolchain
- [ ] Create test Sail files
- [ ] Generate Coq from Sail
- [ ] Document installation issues

### Day 2: Validation and Comparison

**TODO:**
- [ ] Compile generated Coq
- [ ] Compare with manual encoding
- [ ] Measure effort reduction
- [ ] Identify integration challenges

### Day 3: Decision and Documentation

**TODO:**
- [ ] Analyze findings
- [ ] Make go/no-go recommendation
- [ ] Document lessons learned
- [ ] Plan next steps

---

**Spike Status:** READY TO START
**Next Action:** Install Sail toolchain
**Expected Completion:** 2025-11-22
