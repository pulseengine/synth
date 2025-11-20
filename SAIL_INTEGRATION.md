# Sail & CakeML Integration Roadmap

## Overview

Now that we have **151/151 WebAssembly operations** formally specified in Coq,
the next phase is connecting to **official ARM specifications** via Sail and
**verified machine code generation** via CakeML.

## Current Achievement ✅

- **100% WASM Coverage**: All 151 operations have formal Coq theorems
- **38% Fully Proven**: 57 operations with complete mathematical proofs
- **Simplified ARM Semantics**: Clean abstraction for high-level correctness
- **WASM→ARM Compiler**: Compilation.v implements translation

## The Gap 🔍

Our current ARM semantics in `ArmSemantics.v` are **simplified placeholders**:
- Most operations compile to `[]` (empty ARM program)
- This is fine for proving high-level properties (stack management, etc.)
- But we need **real ARM instructions** for an executable compiler

## Solution: Three-Layer Architecture 🏗️

```
┌─────────────────────────────────────────────────────────┐
│ Layer 1: WASM Semantics (Coq)                     ✅   │
│ - 151 operations fully specified                        │
│ - Stack machine semantics                               │
│ - Our verified implementation                           │
└─────────────────────────────────────────────────────────┘
                         ↓
          [Our WASM→ARM Compiler - Compilation.v]
                         ↓
┌─────────────────────────────────────────────────────────┐
│ Layer 2: Simplified ARM IR (Coq)                  ✅   │
│ - Clean abstraction (ArmSemantics.v)                    │
│ - Easy to reason about                                  │
│ - Proves high-level correctness properties              │
└─────────────────────────────────────────────────────────┘
                         ↓
          [Refinement Proof - ArmRefinement.v]
                         ↓
┌─────────────────────────────────────────────────────────┐
│ Layer 3: Official ARM Sail Specs (Generated Coq) 🎯    │
│ - Official ARM architecture semantics                   │
│ - Generated from Sail ISA specifications                │
│ - Maintained by ARM                                     │
│ - Proves we target real ARM correctly                   │
└─────────────────────────────────────────────────────────┘
                         ↓
          [CakeML Integration]
                         ↓
┌─────────────────────────────────────────────────────────┐
│ Layer 4: CakeML Verified Backend               🎯      │
│ - Verified ARM instruction selection                    │
│ - Verified register allocation                          │
│ - Verified machine code generation                      │
│ - Generates actual executable binaries                  │
└─────────────────────────────────────────────────────────┘
                         ↓
                  ARM Machine Code
```

## Implementation Phases

### Phase 1: Sail Integration (Weeks 1-3)

**Goal**: Import official ARM Sail specifications into Coq

**Tasks**:
1. ✅ Create `ArmRefinement.v` with refinement framework (DONE!)
2. Install Sail compiler: `opam install sail`
3. Clone ARM Sail specs: `git clone https://github.com/ARM-software/sail-arm`
4. Generate Coq from Sail for ARMv8-A subset:
   ```bash
   sail -coq arm8_base.sail -o theories/ARM/SailARMGenerated.v
   ```
5. Import generated definitions into `ArmRefinement.v`
6. Prove refinement for core instructions (ADD, SUB, MUL, etc.)

**Deliverables**:
- `theories/ARM/SailARMGenerated.v` - Generated from Sail
- `theories/ARM/ArmRefinement.v` - Refinement proofs (updated)
- `theories/ARM/ArmSubset.v` - Prove we use a valid ARM subset

**Success Criteria**:
- Can prove: `Theorem add_refines_sail : our_ADD ⊑ sail_ADD`
- Validated against official ARM semantics

### Phase 2: CakeML Integration (Weeks 4-6)

**Goal**: Connect to CakeML's verified ARM backend

**Tasks**:
1. Study CakeML ARM backend structure
2. Import CakeML ARMv8 theories into Coq
3. Define translation: Our ARM IR → CakeML's ARM representation
4. Prove translation preserves semantics
5. Connect to CakeML's verified assembler

**Deliverables**:
- `theories/CakeML/CakeMLImport.v` - Import CakeML backend
- `theories/CakeML/ArmToCakeML.v` - Translation layer
- `theories/CakeML/TranslationCorrect.v` - Correctness proofs

**Success Criteria**:
- Can invoke CakeML's verified codegen from our compiler
- Preserves our WASM semantics through to machine code

### Phase 3: End-to-End Verification (Weeks 7-9)

**Goal**: Prove full WASM→ARM→Binary correctness

**Tasks**:
1. Compose all correctness theorems:
   ```coq
   Theorem wasm_to_machine_correct :
     forall wasm_prog machine_code,
       compile_to_machine wasm_prog = Some machine_code ->
       machine_semantics machine_code ≡ wasm_semantics wasm_prog.
   ```
2. Extract executable compiler to OCaml
3. Build command-line tool: `synth compile input.wasm -o output.elf`
4. Test on WASM conformance suite

**Deliverables**:
- `theories/EndToEnd/EndToEndCorrectness.v` - Full correctness theorem
- `extraction/CompilerExtract.v` - Extraction to OCaml
- `bin/synth` - Executable verified compiler
- Test results on WASM conformance suite

**Success Criteria**:
- End-to-end correctness theorem proven
- Executable compiler passes WASM tests
- Can generate ARM binaries from WASM

### Phase 4: Production Deployment (Weeks 10-12)

**Goal**: Package for industrial use (ASIL D certification)

**Tasks**:
1. Performance optimization (while preserving verification)
2. Documentation for safety certification
3. Tool qualification per ISO 26262
4. Integration with automotive toolchains
5. Example: Verified WASM runtime for embedded systems

**Deliverables**:
- Industrial-grade compiler with safety certification artifacts
- Integration guides for automotive OEMs
- Benchmark results vs. non-verified compilers
- Safety manual for ASIL D qualification

## Quick Start: Installing Sail

```bash
# Install Sail via opam
opam install sail

# Verify installation
sail --version

# Clone ARM Sail specifications
cd /tmp
git clone https://github.com/ARM-software/sail-arm
cd sail-arm

# Generate Coq from a simple subset (just to test)
sail -coq sail-arm/arm-v8_5.sail -o test_arm.v

# Check generated Coq compiles
coqc test_arm.v
```

## Resources

### Sail Documentation
- **Sail GitHub**: https://github.com/rems-project/sail
- **Sail Manual**: https://github.com/rems-project/sail/blob/sail2/manual.pdf
- **ARM Sail Specs**: https://github.com/ARM-software/sail-arm

### CakeML Resources
- **CakeML Website**: https://cakeml.org
- **CakeML GitHub**: https://github.com/CakeML/cakeml
- **ARM8 Backend**: https://github.com/CakeML/cakeml/tree/master/compiler/backend/arm8
- **Paper**: "Verified Compilation of CakeML to Multiple Machine-Code Targets" (CPP 2017)

### Key Papers
1. **"ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS"** (POPL 2019)
   - Describes Sail and ARM formal specifications

2. **"Verified Compilation of CakeML"** (CPP 2017)
   - CakeML's approach to verified backend compilation

3. **"Rigorous Engineering for Hardware Security"** (S&P 2021)
   - Using Sail for security-critical processor verification

## Why This Matters

### For Safety-Critical Systems (ASIL D)
- **Official ARM Semantics**: Sail specs are maintained by ARM
- **End-to-End Verification**: From WASM to machine code
- **Tool Qualification**: Verified compiler qualifies as TD2/TD3 tool
- **Reduced Testing**: Mathematical proof replaces extensive testing

### For Research
- **Novel Architecture**: First verified WASM→ARM compiler
- **Modular Verification**: Clean separation of concerns
- **Reusable Framework**: Can adapt to other targets (RISC-V, x86)

### For Industry
- **Trustworthy Embedded Systems**: Run WASM safely on ARM MCUs
- **Automotive**: Verified software for autonomous vehicles
- **Aerospace**: Critical control systems
- **Medical Devices**: Life-critical embedded software

## Current Status

```
✅ Phase 0: WASM Formal Specification (COMPLETE)
   - 151/151 operations specified
   - 57/151 fully proven (38%)
   - All files compile

🎯 Phase 1: Sail Integration (STARTING)
   - ArmRefinement.v created
   - Framework in place
   - Ready for Sail specs import

⏳ Phase 2: CakeML Integration (PLANNED)
⏳ Phase 3: End-to-End (PLANNED)
⏳ Phase 4: Production (PLANNED)
```

## Next Immediate Actions

1. **Install Sail** (5 minutes)
   ```bash
   opam install sail
   ```

2. **Download ARM Specs** (10 minutes)
   ```bash
   git clone https://github.com/ARM-software/sail-arm external/sail-arm
   ```

3. **Generate Test Coq** (15 minutes)
   ```bash
   cd external/sail-arm
   sail -coq <some-subset>.sail -o ../../coq/theories/ARM/SailTest.v
   ```

4. **Prove First Refinement** (1-2 days)
   - Pick simplest instruction (e.g., MOV)
   - Prove our MOV refines Sail MOV
   - Validate approach

5. **Scale Up** (Weeks)
   - Add more instructions
   - Automate proof patterns
   - Complete refinement layer

---

**Let's make this the world's first fully verified WASM→ARM compiler! 🚀**
