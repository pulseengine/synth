# Machine-Readable ARM Specification Integration Strategy

**Status:** Planning Phase
**Target:** Replace hand-written ARM semantics with officially-specified machine-readable semantics
**Priority:** High (for certification credibility)
**Timeline:** After reaching 50-75 operations proven

---

## Executive Summary

Currently, we use **hand-written ARM semantics** in `coq/theories/ARM/ArmSemantics.v` based on our understanding of ARM instructions. For ASIL D certification, we need **machine-readable, officially-specified ARM semantics** to maximize trustworthiness and reduce human error.

**Solution:** Integrate **Sail-generated ARM semantics** from ARM's official Architecture Specification Language (ASL).

---

## Current State (Hand-Written Semantics)

### What We Have Now

**File:** `coq/theories/ARM/ArmSemantics.v` (394 lines)

```coq
Definition exec_instr (i : arm_instr) (s : arm_state) : option arm_state :=
  match i with
  | ADD rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.add v1 v2 in
      Some (set_reg s rd result)
  (* ... manually defined for 60+ instructions *)
  end.
```

### Problems with Hand-Written Semantics

1. **Trust Issue:** "Did we implement ADD correctly?"
   - No official reference backing our implementation
   - Certification auditors will question every instruction

2. **Completeness Issue:** ARM has hundreds of instructions
   - We manually encode only the subset we need
   - Easy to miss edge cases (condition codes, flag updates, etc.)

3. **Maintenance Burden:**
   - ARM specifications evolve
   - Manual updates required for each change

4. **Verification Gap:**
   - Our proofs verify WASM→ARM compilation
   - But who verifies our ARM semantics?
   - **Missing link in the trust chain!**

---

## Target State (Machine-Readable ARM Semantics)

### What We Want

**Source:** ARM Architecture Specification Language (ASL)
- Official ARM specification
- Machine-readable format
- Covers ALL ARM instructions
- Maintained by ARM Limited

**Pipeline:** ARM ASL → Sail → Coq

```
ARM ASL Specification
    ↓ (asl_to_sail tool)
Sail Specification
    ↓ (Sail Coq backend)
Coq ARM Semantics
    ↓ (our proofs)
WASM→ARM Correctness
```

### Benefits

1. **Official Specification:**
   - ARM ASL is the ground truth
   - Used by ARM internally for CPU design
   - Same specification used by ARM engineers

2. **Auto-Generated Coq:**
   - Sail can generate Coq definitions
   - Eliminates human encoding errors
   - ~95% effort reduction

3. **Certification Credibility:**
   - "We use ARM's official specification"
   - Auditors can verify against ARM documentation
   - Stronger trust argument

4. **Completeness:**
   - Get all instruction variants
   - Proper handling of condition codes
   - Status flag updates
   - Edge cases covered

---

## Technical Architecture

### Component 1: ARM ASL

**What:** ARM Architecture Specification Language

**Source:** ARM releases ASL specifications for their processors
- Available from ARM developer website
- Covers ARMv7, ARMv8, etc.
- Each instruction has formal ASL definition

**Example ASL (simplified):**
```asl
// ADD instruction definition
AddWithCarry(x, y, carry_in)
{
    unsigned_sum = UInt(x) + UInt(y) + UInt(carry_in);
    signed_sum = SInt(x) + SInt(y) + UInt(carry_in);
    result = unsigned_sum<N-1:0>;
    carry_out = UInt(result) != unsigned_sum;
    overflow = SInt(result) != signed_sum;
    return (result, carry_out, overflow);
}
```

### Component 2: Sail

**What:** ISA Specification Language from Cambridge REMS project

**Repository:** https://github.com/rems-project/sail

**Capabilities:**
- Intermediate representation for ISA specifications
- Multiple backends: Coq, Isabelle/HOL, OCaml, C
- Used by RISC-V, ARM, CHERI, x86

**ARM Support:**
- `asl_to_sail` tool converts ARM ASL → Sail
- ARM Sail models available in Sail repository
- Actively maintained

**Coq Backend:**
- Generates Coq definitions from Sail specifications
- Produces executable semantics
- Generates monad-based state transformers

### Component 3: Generated Coq Semantics

**Output:** Coq definitions of ARM instructions

**Example (what Sail would generate):**
```coq
Definition execute_ADD (rd : regnum) (rn : regnum) (op2 : operand2)
  : M (armstate) unit :=
  v1 <- read_reg rn;
  v2 <- eval_operand2 op2;
  let (result, carry, overflow) := AddWithCarry v1 v2 0 in
  write_reg rd result;
  (* Update flags if needed *)
  ret tt.
```

---

## Integration Plan

### Phase 1: Research & Preparation (Week 1-2)

**Goals:**
- Obtain ARM ASL specifications for ARMv7
- Set up Sail toolchain
- Generate initial Coq output

**Tasks:**
1. Download ARM ASL:
   - Visit ARM developer site
   - Obtain ARMv7-A/R ASL files
   - Identify needed instructions (ADD, SUB, MUL, etc.)

2. Install Sail:
   ```bash
   git clone https://github.com/rems-project/sail.git
   cd sail
   opam install sail
   ```

3. Test `asl_to_sail`:
   ```bash
   asl_to_sail arm_asl/*.asl -o arm.sail
   ```

4. Test Sail→Coq generation:
   ```bash
   sail -coq arm.sail -o coq/theories/ARM/Generated/
   ```

5. Review generated Coq:
   - Understand the monad structure
   - Identify state representation
   - Map to our `arm_state` type

### Phase 2: Parallel Development (Week 3-4)

**Strategy:** Keep both implementations running in parallel

**File Structure:**
```
coq/theories/ARM/
├── ArmState.v              # Our state (keep)
├── ArmInstructions.v       # Our instructions (keep)
├── ArmSemantics.v          # Our semantics (keep for now)
├── Generated/
│   ├── ArmSailState.v      # Sail-generated state
│   ├── ArmSailSemantics.v  # Sail-generated semantics
│   └── ArmSailMonad.v      # Sail's monadic structure
└── Bridge/
    └── SailBridge.v        # Translation between our types and Sail's
```

**Tasks:**
1. Create bridge layer:
   - Convert our `arm_state` ↔ Sail's state
   - Adapt Sail's monad to our option-based semantics
   - Prove equivalence lemmas

2. Prove consistency:
   ```coq
   Theorem our_semantics_matches_sail : forall instr state,
     exec_instr instr state =
     sail_to_our (sail_exec_instr (our_to_sail state) instr).
   ```

3. Gradually migrate:
   - Start with simple instructions (ADD, SUB)
   - Verify existing proofs still work
   - Expand to all instructions

### Phase 3: Full Migration (Week 5-6)

**Goal:** Replace hand-written semantics with Sail semantics

**Tasks:**
1. Update all proofs to use Sail semantics
2. Remove hand-written `ArmSemantics.v`
3. Update `Compilation.v` to target Sail instructions
4. Regenerate all correctness proofs

**Risk Mitigation:**
- Keep git branches for rollback
- Test thoroughly at each step
- Maintain both versions until confident

### Phase 4: Validation & Documentation (Week 7-8)

**Tasks:**
1. Comprehensive testing:
   - Run all 46+ proven operations
   - Verify all proofs still pass
   - Check edge cases

2. Documentation:
   - Document Sail integration in README
   - Explain provenance chain
   - Update certification materials

3. Create reproducibility guide:
   - Instructions for regenerating Coq from ASL
   - Version pinning (ARM ASL version, Sail version)
   - Build scripts

---

## Benefits Analysis

### Quantitative Benefits

| Aspect | Hand-Written | Sail-Generated | Improvement |
|--------|-------------|----------------|-------------|
| Lines of code | ~400 | ~2000 (but auto) | -75% manual effort |
| Instructions covered | ~60 | ~500+ | 8x coverage |
| Update time | Hours-days | Minutes | ~95% faster |
| Error rate | Unknown | Near-zero | Massive |
| Trust level | Low | Very High | Critical for ASIL D |

### Qualitative Benefits

1. **Certification Argument:**
   - "Our ARM semantics are derived directly from ARM's official ASL specification"
   - Much stronger than "We wrote ARM semantics based on documentation"

2. **Auditor Confidence:**
   - Auditors can verify provenance
   - Reproducible from ARM sources
   - No human encoding errors

3. **Completeness:**
   - All instruction variants covered
   - Proper condition code handling
   - Status flags correctly updated

4. **Maintainability:**
   - ARM updates ASL → we regenerate
   - No manual maintenance burden
   - Always up-to-date

---

## Risks & Mitigation

### Risk 1: Sail Integration Complexity

**Risk:** Sail-generated Coq may be incompatible with our proof structure

**Likelihood:** Medium
**Impact:** High

**Mitigation:**
- Start early with small examples
- Create robust bridge layer
- Keep hand-written version as backup
- Gradual migration, not big-bang

### Risk 2: Performance

**Risk:** Sail-generated semantics may be slow for proof checking

**Likelihood:** Low
**Impact:** Medium

**Mitigation:**
- Sail Coq output is designed to be efficient
- Can add computational optimizations
- Extraction to OCaml possible for testing

### Risk 3: Specification Gaps

**Risk:** ARM ASL may not cover all instructions we need

**Likelihood:** Low
**Impact:** Medium

**Mitigation:**
- Preliminary research shows good coverage
- Can fall back to hand-written for edge cases
- Hybrid approach possible

### Risk 4: Learning Curve

**Risk:** Team needs to learn Sail and ASL

**Likelihood:** High
**Impact:** Low

**Mitigation:**
- Excellent documentation available
- Cambridge REMS team support
- Growing community
- Phased approach allows learning

---

## Alternative Approaches Considered

### Alternative 1: Continue Hand-Written

**Pros:**
- No integration work
- We control everything
- Simpler initially

**Cons:**
- Weak certification argument
- High maintenance
- Limited coverage
- Trust gap

**Verdict:** ❌ Not recommended for ASIL D

### Alternative 2: Use CakeML ARM Model

**Pros:**
- CakeML has verified ARM semantics
- Already in HOL4, could port to Coq

**Cons:**
- Porting HOL4 → Coq is major work
- CakeML ARM model is partial
- Not official ARM spec

**Verdict:** ⚠️ Possible but inferior to Sail

### Alternative 3: Directly Use ARM ASL

**Pros:**
- Most direct
- Official specification

**Cons:**
- ASL tools limited
- No Coq backend
- Would need to build infrastructure

**Verdict:** ❌ Too much tooling work

### Alternative 4: Sail Integration (Recommended)

**Pros:**
- Official ARM specification via ASL
- Proven Coq backend
- Active maintenance
- Used by other projects (RISC-V verification)

**Cons:**
- Integration effort
- Some learning curve

**Verdict:** ✅ **Recommended approach**

---

## Timeline & Milestones

### Immediate (Current Session)

- ✅ Reach 46/151 operations with hand-written semantics
- ✅ Complete 5 operation categories
- ⏳ Continue to 50-75 operations (establish proof patterns)

### Short Term (Next 1-2 weeks)

- 📋 Download ARM ASL specifications
- 📋 Set up Sail toolchain
- 📋 Generate initial Coq output
- 📋 Create proof-of-concept bridge

### Medium Term (3-8 weeks)

- 📋 Phase 1: Research & Preparation (Week 1-2)
- 📋 Phase 2: Parallel Development (Week 3-4)
- 📋 Phase 3: Full Migration (Week 5-6)
- 📋 Phase 4: Validation & Documentation (Week 7-8)

### Long Term (After Sail Integration)

- 📋 Prove remaining operations with Sail semantics
- 📋 Reach 151/151 complete
- 📋 Prepare certification package
- 📋 Submit for ASIL D review

---

## Current Status & Next Steps

### Current State (Session Progress)

- **46/151 operations proven (30%)**
- 5 complete categories (i32 comparison, i64 comparison, i32 shift/rotate, simple/control, automation)
- Hand-written ARM semantics working well
- Simplified compilation strategy validated

### Decision Point

**When to integrate Sail?**

**Recommendation:** After reaching **50-75 operations** (35-50% complete)

**Rationale:**
1. Establish clear proof patterns first
2. Understand what we need from ARM semantics
3. Have substantial test suite for validation
4. Avoid disrupting current momentum

**Next Actions:**
1. ✅ Continue proving operations (current momentum is excellent!)
2. ✅ Reach 50 operations milestone
3. 📋 Begin Sail research in parallel
4. 📋 Create proof-of-concept integration
5. 📋 Make go/no-go decision based on PoC

---

## Conclusion

**Machine-readable ARM specification integration via Sail is essential for ASIL D certification.**

The integration provides:
- ✅ Official ARM specification provenance
- ✅ Near-zero encoding errors
- ✅ Comprehensive instruction coverage
- ✅ Strong certification argument
- ✅ Long-term maintainability

**Recommended Timeline:**
- **Now - 50 ops:** Continue with hand-written semantics (build proof patterns)
- **50-75 ops:** Begin Sail integration research & PoC
- **75+ ops:** Full migration to Sail-generated semantics
- **100-151 ops:** Complete all proofs with official ARM semantics

This approach balances immediate progress with long-term quality and certification needs.

---

**Document Version:** 1.0
**Last Updated:** Session 2025-11-19
**Next Review:** After reaching 50 operations
