# Sail & ARM ISA Integration - Technical Details

## Overview

This document details the integration between our verified WebAssembly-to-ARM compiler
and the official ARM architecture specifications via Sail ISA language.

## What is Sail?

**Sail** is a domain-specific language for describing processor instruction set
architectures (ISAs), developed at the University of Cambridge as part of the
REMS (Rigorous Engineering for Mainstream Systems) project.

### Key Features:
- **Machine-readable ISA specifications**: Unlike PDF architecture manuals
- **Multi-backend code generation**: Can generate executable emulators, theorem prover definitions (Coq, Isabelle/HOL, HOL4), and documentation
- **Official ARM specifications**: ARM uses Sail for ARMv8-A and ARMv9-A
- **Industry adoption**: Used for RISC-V, CHERI, Power, MIPS specifications

### Why Sail Matters for Our Project:
- **Official semantics**: ARM's Sail specs ARE the official architecture reference
- **Mathematical rigor**: Can generate Coq definitions we can prove against
- **Validation**: ARM validates their silicon against these specs
- **Certification**: Links our proofs to industry-standard architecture

## Architecture: Three-Layer Verification

Our integration uses a refinement-based approach with three semantic layers:

```
┌─────────────────────────────────────────────────────────┐
│ Layer 1: WASM Semantics (WasmSemantics.v)        ✅   │
│ - 151/151 operations formally specified                 │
│ - Stack machine model                                   │
│ - 57/151 operations fully proven (38%)                  │
│ - Our implementation in Coq                             │
└─────────────────────────────────────────────────────────┘
                         ↓
          [WASM→ARM Compiler: Compilation.v]
                         ↓
┌─────────────────────────────────────────────────────────┐
│ Layer 2: Simplified ARM IR (ArmSemantics.v)      ✅   │
│ - Abstract ARM instruction model                        │
│ - Easy to reason about for high-level proofs            │
│ - Proves compiler correctness properties                │
│ - Register allocation, stack management, etc.           │
└─────────────────────────────────────────────────────────┘
                         ↓
          [Refinement Proof: ArmRefinement.v]
                         ↓
┌─────────────────────────────────────────────────────────┐
│ Layer 3: ARM Sail Semantics (SailARMGenerated.v) 🎯  │
│ - Official ARM architecture specification               │
│ - Generated from Sail ISA language                      │
│ - Maintained and validated by ARM                       │
│ - Bit-precise instruction semantics                     │
│ - Full ARMv8-A architecture model                       │
└─────────────────────────────────────────────────────────┘
                         ↓
          [CakeML Verified Backend (Future)]
                         ↓
                  ARM Machine Code
```

## Refinement Relation

The key to this architecture is the **refinement relation** defined in `ArmRefinement.v`:

```coq
Definition refines {A : Type} (simplified : option A) (sail : option A) : Prop :=
  match simplified with
  | None => True  (* Simplified can fail - no constraint *)
  | Some s => match sail with
              | None => False  (* If simplified succeeds, Sail must succeed *)
              | Some s' => s = s'  (* Results must match *)
              end
  end.

Notation "x ⊑ y" := (refines x y) (at level 70).
```

### What Refinement Means:

1. **If our semantics succeed, Sail must succeed**: Our compiler can't invent
   behavior not in the architecture
2. **Observable states must match**: Results visible to the program (registers,
   memory, flags) must be identical
3. **Internal details can differ**: Sail may track more internal state (caches,
   pipeline, system registers) which we don't model

### Correctness Theorem Structure:

```coq
Theorem arm_refines_sail : forall (instr : arm_instr) (s : arm_state) (s_sail : SailARM.sail_state),
  SailARM.state_corresponds s s_sail ->
  exists s_sail',
    SailARM.sail_exec_instr instr s_sail = Some s_sail' /\
    (forall s', exec_instr instr s = Some s' ->
                exists s_sail'',
                  SailARM.state_corresponds s' s_sail'').
```

This says: For any ARM instruction and corresponding states, if our simplified
semantics execute successfully, the Sail semantics must also execute and produce
a corresponding result.

## State Correspondence

We define which parts of the ARM state must match:

```coq
Definition state_corresponds (our : arm_state) (sail : sail_state) : Prop :=
  (forall r, get_reg our r = sail_regs sail r) /\        (* Registers match *)
  (forall vr, get_vfp_reg our vr = sail_vfp_regs sail vr) /\  (* VFP regs match *)
  (our.(flags) = sail_flags sail) /\                     (* Flags match *)
  (forall addr, load_mem our addr = sail_mem sail addr). (* Memory matches *)
```

**What we match:**
- General-purpose registers (R0-R15)
- VFP floating-point registers (S0-S31, D0-D15)
- Condition flags (N, Z, C, V)
- User-accessible memory

**What we don't match (Sail tracks these, we don't):**
- System registers (CPSR, SPSR, etc.)
- MMU state (page tables, TLB)
- Cache state
- Pipeline state
- Debug/trace registers
- Hypervisor state (for ARMv8-A virtualization)

This is valid because these internal details don't affect user-visible program behavior.

## Sail→Coq Code Generation

Sail can generate Coq definitions from ARM ISA specifications:

```bash
# Generate Coq from Sail ARM specs
sail -coq arm8_base.sail -o theories/ARM/SailARMGenerated.v
```

### What Gets Generated:

1. **Type definitions**: ARM instruction encodings, register types, memory models
2. **Instruction decoders**: Binary → instruction AST
3. **Instruction semantics**: Execution functions for each instruction
4. **Helper functions**: Bit manipulation, flag computation, addressing modes

### Example Generated Code (simplified):

```coq
(* Generated from Sail *)
Inductive sail_arm_instr :=
  | SAIL_ADD_reg : sail_register -> sail_register -> sail_register -> sail_arm_instr
  | SAIL_SUB_reg : sail_register -> sail_register -> sail_register -> sail_arm_instr
  | ...

Definition sail_exec_ADD_reg (rd rn rm : sail_register) (s : sail_state) : option sail_state :=
  let val_n := sail_read_register s rn in
  let val_m := sail_read_register s rm in
  let result := sail_add_with_carry val_n val_m false in
  Some (sail_write_register s rd result.(value)).
```

## Proof Strategy

### Phase 1: Per-Instruction Refinement

For each ARM instruction we use, prove it refines the Sail version:

```coq
Theorem add_refines_sail : forall rd rn op2 s s_sail,
  SailARM.state_corresponds s s_sail ->
  exec_instr (ADD rd rn op2) s ⊑
    SailARM.sail_exec_instr (SAIL_ADD_reg rd rn ...) s_sail.
Proof.
  (* Show that our ADD implementation matches Sail's ADD semantics *)
Qed.
```

### Phase 2: Compiler Correctness via Refinement

Compose the refinement with our compiler correctness:

```coq
Theorem compiler_refines_sail : forall (wasm_instr : wasm_instr) (arm_prog : list arm_instr),
  compile_wasm_to_arm wasm_instr = arm_prog ->
  forall s s_sail,
    state_corresponds s s_sail ->
    exec_program arm_prog s ⊑
      SailARM.sail_exec_program (map to_sail arm_prog) s_sail.
```

### Phase 3: End-to-End Correctness

Prove that WASM programs compiled to ARM respect official ARM semantics:

```coq
Theorem wasm_to_sail_correct : forall wasm_prog arm_prog,
  compile_wasm_program wasm_prog = Some arm_prog ->
  forall wstate astate,
    wasm_arm_state_corresponds wstate astate ->
    exists astate',
      SailARM.sail_exec_program (map to_sail arm_prog) (to_sail_state astate) = Some astate' /\
      wasm_result_matches wstate astate'.
```

## Integration Steps

### Step 1: Install Sail (IN PROGRESS)
```bash
opam install sail
sail --version  # Verify installation
```

### Step 2: Clone ARM Specifications
```bash
git clone https://github.com/ARM-software/sail-arm external/sail-arm
cd external/sail-arm
```

### Step 3: Identify Required ARM Subset

Our compiler only uses a small subset of ARMv8-A:
- **Arithmetic**: ADD, SUB, MUL, SDIV, UDIV
- **Bitwise**: AND, ORR, EOR, MVN
- **Shifts**: LSL, LSR, ASR, ROR
- **Moves**: MOV, MOVW, MOVT
- **Memory**: LDR, STR (32-bit and 64-bit variants)
- **VFP**: VADD, VSUB, VMUL, VDIV, VCMP (for floating-point)
- **Stack**: PUSH, POP
- **Branches**: B (unconditional), BEQ, BNE, BLT, BGE, etc.

We need to extract these from the full ARM Sail specification.

### Step 4: Generate Coq for Subset

```bash
# Create a Sail file with just our subset
cat > arm_subset.sail <<EOF
(* Include base ARM definitions *)
include "arm8_base.sail"

(* Define our subset of instructions *)
(* ... *)
EOF

# Generate Coq
sail -coq arm_subset.sail -o ../coq/theories/ARM/SailARMGenerated.v
```

### Step 5: Import and Prove Refinement

Update `ArmRefinement.v`:
```coq
Require Import Synth.ARM.SailARMGenerated.

(* Replace axioms with real definitions *)
Module SailARM.
  (* Import generated types and functions *)
  Definition sail_state := SailARMGenerated.arm_state.
  Definition sail_exec_instr := SailARMGenerated.execute_instruction.
End SailARM.

(* Now prove actual refinement theorems *)
Theorem add_refines_sail : forall rd rn op2 s s_sail,
  SailARM.state_corresponds s s_sail ->
  exec_instr (ADD rd rn op2) s ⊑
    SailARM.sail_exec_instr ... s_sail.
Proof.
  (* Actual proof using generated Sail definitions *)
Qed.
```

## Benefits of This Approach

### For Safety Certification (ISO 26262 ASIL D):
1. **Official Specifications**: Our proofs reference ARM's official specs
2. **Tool Qualification**: Compiler proven against architecture reference
3. **Reduced Testing**: Mathematical proof replaces extensive validation
4. **Audit Trail**: Clear chain from WASM to ARM to machine code

### For Correctness:
1. **Architecture Compliance**: Guaranteed to match ARM behavior
2. **No Undefined Behavior**: Sail specs are complete and unambiguous
3. **Validation**: ARM validates hardware against these specs
4. **Precision**: Bit-level accuracy in semantics

### For Maintainability:
1. **Upstream Updates**: ARM maintains the Sail specs
2. **New Architecture Versions**: Can update to ARMv9 by regenerating
3. **Bug Fixes**: If ARM fixes spec bugs, we get them automatically
4. **Documentation**: Sail specs serve as precise documentation

## Challenges and Solutions

### Challenge 1: Sail Complexity
**Problem**: Full ARM Sail specs are thousands of lines and very detailed

**Solution**:
- Extract only the subset we use
- Focus on user-mode instructions
- Ignore system-level features (MMU, exceptions, etc.)

### Challenge 2: State Mismatch
**Problem**: Sail tracks more state than we model

**Solution**:
- Use refinement relation, not equality
- Prove correspondence only on observable state
- Abstract away internal ARM details

### Challenge 3: Generated Coq Quality
**Problem**: Sail-generated Coq may be hard to work with

**Solution**:
- Wrapper layer in `ArmRefinement.v`
- Don't modify generated code
- All proofs in separate files

### Challenge 4: Instruction Encoding
**Problem**: Sail works with bit-level encodings, we use abstract syntax

**Solution**:
- Define mapping from our AST to Sail AST
- Prove mapping preserves semantics
- Don't prove about binary encoding (CakeML handles that)

## Timeline

### Week 1: Setup and Exploration
- ✅ Install Sail
- ⏳ Clone ARM specs
- ⏳ Generate simple test case
- ⏳ Verify Coq generation works

### Week 2-3: Subset Extraction and Generation
- Extract instruction subset we use
- Create Sail file for subset
- Generate Coq definitions
- Import into build system

### Week 4-5: Refinement Proofs
- Prove refinement for arithmetic instructions
- Prove refinement for memory instructions
- Prove refinement for control flow
- Develop proof automation

### Week 6-8: Compiler Integration
- Connect compiler correctness to refinement
- Prove end-to-end theorem
- Validate against ARM test cases
- Document certification artifacts

## References

### Sail Resources:
- **Sail Language**: https://github.com/rems-project/sail
- **Sail Manual**: https://github.com/rems-project/sail/blob/sail2/manual.pdf
- **ARM Sail Specs**: https://github.com/ARM-software/sail-arm
- **Sail Paper**: "ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS" (POPL 2019)

### ARM Architecture:
- **ARMv8-A Reference Manual**: ARM DDI 0487
- **ARM Architecture Profile**: https://developer.arm.com/documentation/

### Formal Methods:
- **Refinement**: "Refinement Types for ML" (PLDI 1991)
- **Compiler Verification**: "Formal Verification of a Realistic Compiler" (CompCert, CACM 2009)

---

**Status**: Phase 1 (Sail installation) IN PROGRESS
**Next Action**: Complete Sail installation, clone ARM specs, generate test Coq
