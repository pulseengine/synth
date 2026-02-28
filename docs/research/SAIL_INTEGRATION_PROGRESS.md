# Sail & ARM Integration - Session Progress

## Session Goal
Integrate official ARM Sail specifications into our verified WebAssembly-to-ARM compiler to achieve end-to-end formal verification against the official ARM architecture.

## Progress Overview

### ✅ Phase 1: Setup Complete

#### 1. Fixed ArmRefinement.v Compilation ✅
- **Issue**: Missing `get_flags` function reference
- **Fix**: Changed `get_flags our` to `our.(flags)` (direct field access)
- **Result**: File now compiles successfully with Coq 9.1.0
- **Location**: `/home/user/Synth/coq/Synth/ARM/ArmRefinement.v`

#### 2. Installed Sail Toolchain ✅
- **Version**: Sail 0.20.0
- **Method**: `opam install sail -y`
- **Backends Installed**:
  - `sail_coq_backend` - **Critical for our project**
  - `sail_c_backend` - For executable emulators
  - `sail_lem_backend` - For Lem theorem prover
  - `sail_lean_backend` - For Lean prover
  - `sail_smt_backend` - For SMT-based verification
  - Additional backends for OCaml, SystemVerilog, LaTeX, documentation
- **Verification**: `sail --version` confirms Sail 0.20.0

#### 3. Cloned ARM Sail Specifications ✅
- **Repository**: `https://github.com/rems-project/sail-arm`
- **Location**: `/home/user/Synth/external/sail-arm/`
- **Architecture Versions Available**:
  - **ARMv8.5-A** - 457 files, 5.5MB of Sail specs
    - `aarch64.sail` - 1.7MB (main 64-bit instruction set)
    - `aarch32.sail` - 2.1MB (32-bit instruction set)
    - `aarch64_float.sail` - 82KB (floating-point ops)
    - `aarch64_vector.sail` - 383KB (SIMD/NEON)
    - `aarch_types.sail` - Type definitions
    - `aarch_mem.sail` - Memory model
    - `prelude.sail` - Basic definitions
  - ARMv9.3-A - Newer architecture
  - ARMv9.4-A - Latest architecture

- **Coverage**: All 32-bit and 64-bit instructions for ARMv8.5-A
- **Source**: Official ARM specifications (converted from ARM ASL reference)
- **License**: BSD 3-Clause Clear

#### 4. Created Documentation ✅
- **SAIL_INTEGRATION.md** - Comprehensive integration roadmap
- **docs/SAIL_ARM_INTEGRATION.md** - Technical details of integration
- **This file** - Session progress tracking

### 🔄 Phase 2: In Progress

#### 5. Installing Z3 SMT Solver 🔄
- **Status**: Installation in progress (background task)
- **Why Needed**: Sail→Coq generation uses Z3 for constraint solving
- **Command**: `opam install z3 -y`
- **Next**: Test Sail→Coq generation after installation completes

### ⏳ Phase 3: Planned

#### 6. Generate Test Coq from Sail ⏳
**Plan**:
1. Generate Coq from `prelude.sail` (464 lines)
2. Generate Coq from `aarch_types.sail` (683 lines)
3. Verify generated Coq compiles
4. Extract subset of instructions we use

**Command Template**:
```bash
opam exec -- sail -coq model/prelude.sail -o coq/Synth/ARM/SailARMPrelude.v
```

#### 7. Extract ARM Instruction Subset ⏳
We only use a small subset of ARM instructions:

**Arithmetic**: ADD, SUB, MUL, SDIV, UDIV
**Bitwise**: AND, ORR, EOR, MVN, BIC
**Shifts**: LSL, LSR, ASR, ROR
**Moves**: MOV, MOVW, MOVT
**Memory**: LDR, STR (32/64-bit)
**Floating-Point**: VADD, VSUB, VMUL, VDIV, VCMP
**Stack**: PUSH, POP
**Branches**: B, BEQ, BNE, BLT, BGE, BGT, BLE

**Plan**:
- Create `arm_synth_subset.sail` with only these instructions
- Generate focused Coq output
- Reduce proof burden significantly

#### 8. Prove Refinement Theorems ⏳
For each instruction category:
- Arithmetic: `add_refines_sail`, `sub_refines_sail`, etc.
- Memory: `ldr_refines_sail`, `str_refines_sail`
- Control: `branch_refines_sail`

**Template**:
```coq
Theorem add_refines_sail : forall rd rn rm s s_sail,
  SailARM.state_corresponds s s_sail ->
  exec_instr (ADD rd rn (Reg rm)) s ⊑
    SailARM.sail_exec_instr (SAIL_ADD_reg rd rn rm) s_sail.
```

#### 9. Compose with Compiler Correctness ⏳
Connect refinement to existing compiler correctness proofs:

```coq
Theorem wasm_to_sail_correct : forall wasm_instr arm_code,
  compile_wasm_to_arm wasm_instr = arm_code ->
  forall wstate astate s_sail,
    wasm_arm_corresponds wstate astate ->
    state_corresponds astate s_sail ->
    exec_program arm_code astate ⊑
      SailARM.sail_exec_program (map to_sail arm_code) s_sail.
```

## Architecture Layers

Our verification now spans four semantic layers:

```
┌─────────────────────────────────────┐
│ Layer 1: WASM Semantics       ✅   │  151/151 ops, 57 proven
└─────────────────────────────────────┘
                ↓
    [WASM→ARM Compiler: Compilation.v]
                ↓
┌─────────────────────────────────────┐
│ Layer 2: Simplified ARM IR     ✅   │  Abstract model
└─────────────────────────────────────┘
                ↓
    [Refinement: ArmRefinement.v ✅]
                ↓
┌─────────────────────────────────────┐
│ Layer 3: ARM Sail Semantics   🔄   │  Official ARM specs
└─────────────────────────────────────┘
                ↓
    [CakeML Backend (Future) ⏳]
                ↓
         ARM Machine Code
```

## Key Technical Insights

### 1. Refinement vs. Equality
We use **refinement** rather than **equality** because:
- Sail tracks internal ARM state (system registers, MMU, caches)
- Our model only tracks user-visible state (registers, flags, memory)
- Refinement allows abstraction: our semantics ⊑ Sail semantics
- Valid because internal details don't affect program behavior

### 2. State Correspondence
```coq
Definition state_corresponds (our : arm_state) (sail : sail_state) : Prop :=
  (forall r, get_reg our r = sail_regs sail r) /\        (* GP registers *)
  (forall vr, get_vfp_reg our vr = sail_vfp_regs sail vr) /\  (* VFP regs *)
  (our.(flags) = sail_flags sail) /\                     (* NZCV flags *)
  (forall addr, load_mem our addr = sail_mem sail addr). (* Memory *)
```

**We match**: R0-R15, S0-S31, D0-D15, NZCV flags, user memory
**We don't match**: CPSR, SPSR, system registers, MMU state, caches

### 3. Subset Extraction Strategy
Rather than generate Coq for all 50,000+ lines of Sail specs:
1. Identify which instructions our compiler uses (~30 core instructions)
2. Create minimal Sail file with only those definitions
3. Generate focused Coq output (manageable size)
4. Prove refinement only for instructions we use
5. Much smaller proof burden, same correctness guarantee

## Files Modified/Created

### Coq Files:
- ✅ `coq/Synth/ARM/ArmRefinement.v` - Fixed and compiling
- 🔄 `coq/Synth/ARM/SailARMPrelude.v` - To be generated
- ⏳ `coq/Synth/ARM/SailARMTypes.v` - To be generated
- ⏳ `coq/Synth/ARM/SailARMInstructions.v` - To be generated
- ⏳ `coq/Synth/ARM/ArmSubset.v` - Prove subset validity

### Documentation:
- ✅ `SAIL_INTEGRATION.md` - Integration roadmap
- ✅ `docs/SAIL_ARM_INTEGRATION.md` - Technical details
- ✅ `SAIL_INTEGRATION_PROGRESS.md` - This file

### External Resources:
- ✅ `external/sail-arm/` - ARM Sail specifications repository

## Metrics

### Coverage:
- **WASM Operations**: 151/151 (100%)
- **Proven Operations**: 57/151 (38%)
- **ARM Instructions Used**: ~30 core instructions
- **ARM Sail Specs**: 5.5MB (ARMv8.5-A)

### Build Status:
- ✅ All Coq 9.1.0 files compile
- ✅ Sail 0.20.0 installed
- 🔄 Z3 SMT solver installing
- ⏳ Sail→Coq generation pending

## Next Immediate Actions

1. **Wait for Z3 installation** - Currently in progress
2. **Test Sail→Coq generation** - Generate prelude.sail → .v file
3. **Verify generated Coq compiles** - Use Coq 9.1.0 to check
4. **Create instruction subset** - Extract only instructions we use
5. **Generate full subset Coq** - For all needed instructions
6. **Prove first refinement** - Pick simplest instruction (MOV)
7. **Scale up proofs** - Extend to all used instructions
8. **Compose correctness** - Connect to existing WASM→ARM proofs

## Timeline Estimate

- **Week 1** (Current): ✅ Setup, Sail installation, repository cloning
- **Week 2**: 🔄 Coq generation, subset extraction, first refinement proof
- **Week 3-4**: ⏳ Refinement proofs for all instructions, automation
- **Week 5-6**: ⏳ Composition with compiler correctness, end-to-end theorem
- **Week 7-8**: ⏳ CakeML integration exploration (Phase 2 of roadmap)

## Success Criteria

### Short-term (This Week):
- [x] Sail installed and working
- [x] ARM Sail specs cloned
- [ ] Z3 installed
- [ ] Successfully generate Coq from Sail
- [ ] Generated Coq compiles

### Medium-term (2-4 Weeks):
- [ ] Subset of ARM instructions extracted
- [ ] Refinement proof for at least one instruction (MOV)
- [ ] Automation tactics for refinement proofs
- [ ] Refinement proven for arithmetic instructions

### Long-term (2-3 Months):
- [ ] All used instructions proven to refine Sail
- [ ] Compiler correctness composed with refinement
- [ ] End-to-end WASM→Sail correctness theorem
- [ ] Integration with CakeML backend begun

## Challenges Encountered

1. **Git Authentication** ❌→✅
   - Initial attempt to clone from `ARM-software/sail-arm` failed
   - **Solution**: Correct repository is `rems-project/sail-arm`

2. **Missing Z3** ❌→🔄
   - Sail→Coq generation requires Z3 SMT solver
   - **Solution**: Installing via `opam install z3` (in progress)

3. **ArmRefinement.v Compilation** ❌→✅
   - Used non-existent `get_flags` function
   - **Solution**: Use direct field access `our.(flags)`

## Resources Used

### Primary Sources:
- Sail Language: https://github.com/rems-project/sail
- ARM Sail Specs: https://github.com/rems-project/sail-arm
- Sail Manual: https://github.com/rems-project/sail/blob/sail2/manual.pdf

### Papers Referenced:
- "ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS" (POPL 2019)
- "Verified Compilation of CakeML to Multiple Machine-Code Targets" (CPP 2017)

### Tools:
- Sail 0.20.0
- Coq 9.1.0
- Z3 SMT solver (installing)
- Git, opam

---

**Current Status**: Phase 1 Complete ✅, Phase 2 In Progress 🔄
**Blocked On**: Z3 installation completion
**Next Action**: Test Sail→Coq generation with prelude.sail
**Estimated Time to Next Milestone**: 15-30 minutes (Z3 install + test generation)
