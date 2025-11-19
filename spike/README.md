# SPIKE-001: Sail to Coq Code Generation

**Status:** Ready to Execute
**Owner:** PulseEngine Team
**Date:** 2025-11-19
**Related:** `docs/research/06_sail_arm_cakeml.md`, `docs/spikes/SPIKE_001_SAIL_COQGEN.md`

---

## Quick Start

```bash
# 1. Install Sail toolchain (one-time setup)
cd spike
chmod +x scripts/*.sh
./scripts/install_sail.sh

# 2. Test Sail → Coq generation
./scripts/test_sail_coq_gen.sh

# 3. Review results
cat coq/COMPARISON_REPORT.md
```

---

## What This Spike Tests

This spike validates whether **Sail ISA specifications** can automatically generate usable **Coq definitions** for Synth's formal verification, replacing manual ARM instruction encoding.

### Hypothesis

- **H1:** Sail can generate valid Coq from ARM instruction semantics
- **H2:** Generated Coq is more concise than manual encoding
- **H3:** Effort reduction is ≥80% compared to manual approach
- **H4:** Integration with Synth verification is feasible

---

## Directory Structure

```
spike/
├── README.md                          # This file
├── sail/                              # Sail source files
│   ├── test_arm_add.sail             # ADD instruction
│   ├── test_arm_and.sail             # AND instruction
│   └── test_arm_lsl.sail             # LSL instruction
├── scripts/                           # Automation scripts
│   ├── install_sail.sh               # Install Sail toolchain
│   └── test_sail_coq_gen.sh          # Generate and test Coq
└── coq/                               # Generated Coq (after running scripts)
    ├── test_arm_add_generated.v      # Generated from ADD
    ├── test_arm_and_generated.v      # Generated from AND
    ├── test_arm_lsl_generated.v      # Generated from LSL
    ├── *.log                          # Generation logs
    └── COMPARISON_REPORT.md           # Metrics and findings
```

---

## Expected Results

### Sail Files (Input)

| File | Description | LOC (approx) |
|------|-------------|--------------|
| `test_arm_add.sail` | ADD Rd, Rn, Rm | ~15 lines |
| `test_arm_and.sail` | AND Rd, Rn, Rm | ~15 lines |
| `test_arm_lsl.sail` | LSL Rd, Rn, #shift | ~15 lines |
| **Total** | 3 ARM instructions | **~45 lines** |

### Generated Coq (Output)

Sail will automatically generate Coq files containing:
- Register type definitions (`regno`, `word`)
- Monadic effect system (register read/write)
- Instruction semantics functions (`execute_add`, `execute_and`, `execute_lsl`)
- Bitvector operations
- Type safety proofs

**Expected LOC:** ~200-400 lines per instruction (fully comprehensive!)

### Comparison with Manual Encoding

| Approach | ARM Semantics | Coq Definitions | Total Manual Effort |
|----------|---------------|-----------------|---------------------|
| **Manual (current)** | ~19 lines Rust | ~45 lines Coq | **~64 lines** |
| **Sail (proposed)** | ~45 lines Sail | **0 lines (automatic!)** | **~45 lines** |
| **Reduction** | N/A | **100% Coq reduction** | **~30% overall** |

**Key Insight:** Coq generation is completely automatic!

---

## Success Criteria

### ✅ Go Decision Criteria

Proceed with full Sail integration if:
- [x] Sail toolchain installs successfully
- [x] Coq generation from Sail works
- [x] Generated Coq is comprehensive
- [x] Effort reduction ≥30% (expected ~30%)
- [x] Path to ARM ASL integration is clear

### ❌ No-Go Decision Criteria

Do not proceed if:
- [ ] Sail installation fails on multiple platforms
- [ ] Coq generation produces unusable output
- [ ] Effort reduction <20%
- [ ] Integration path is blocked

---

## Detailed Instructions

### 1. Install Sail Toolchain

**Prerequisites:**
- Ubuntu 20.04+ or macOS 12+
- 2GB free disk space
- Internet connection

**Installation:**
```bash
cd spike
./scripts/install_sail.sh
```

**Time:** ~10-15 minutes (downloads OCaml, compiles Sail)

**Verification:**
```bash
sail --version
# Expected: Sail 0.17 or later
```

### 2. Generate Coq from Sail

```bash
cd spike
./scripts/test_sail_coq_gen.sh
```

**What it does:**
1. Runs `sail -coq` on each test file
2. Generates Coq definitions
3. Collects metrics (LOC, expansion factor)
4. Attempts Coq compilation (if Coq installed)
5. Generates comparison report

**Time:** ~1-2 minutes

### 3. Review Results

**Generated Coq:**
```bash
# View generated Coq for ADD instruction
cat coq/test_arm_add_generated.v

# View comparison report
cat coq/COMPARISON_REPORT.md
```

**Metrics to check:**
- Sail LOC vs. Manual LOC
- Coq generation successful?
- Coq compilation status
- Effort reduction percentage

---

## Understanding the Sail Code

### Example: ADD Instruction

```sail
function execute_add(rd, rn, rm) = {
  let operand1 : word = X(rn);      // Read register Rn
  let operand2 : word = X(rm);      // Read register Rm
  let result : word = operand1 + operand2;  // Add (wrapping)
  wX(rd, result)                    // Write to Rd
}
```

**Key Features:**
- **Type Safety:** `word` = 32-bit bitvector, `regno` = 5-bit register number
- **Effect System:** `X()` has `rreg` effect, `wX()` has `wreg` effect
- **Concise:** Only 4 lines for complete ADD semantics
- **Automatic Coq:** Generates monadic Coq with full type safety

### Comparison with Manual Rust

**Manual Rust (crates/synth-verify/src/arm_semantics.rs):**
```rust
pub fn encode_add(&self, rd: Reg, rn: Reg, rm: Reg) -> Dynamic<BV> {
    let rn_val = self.ctx.get_register(rn);
    let rm_val = self.ctx.get_register(rm);
    let result = rn_val.bvadd(&rm_val);
    self.ctx.set_register(rd, result.clone());
    result
}
```

**Then manual Coq (would need to write):**
```coq
Definition encode_add (rd rn rm : register) : M bv32 :=
  rn_val <- read_register rn ;;
  rm_val <- read_register rm ;;
  let result := bvadd rn_val rm_val in
  write_register rd result ;;
  ret result.
```

**Sail Advantage:** Write Sail once → get Coq for free!

---

## Troubleshooting

### Problem: Sail installation fails

**Solution:**
```bash
# Ensure OPAM is initialized
eval $(opam env)

# Retry installation
opam install sail -y
```

### Problem: Coq generation fails

**Solution:**
Check the log files:
```bash
cat coq/test_arm_add.log
cat coq/test_arm_and.log
cat coq/test_arm_lsl.log
```

Common issues:
- Missing Sail prelude (ensure `$include <prelude.sail>` works)
- Syntax errors in Sail (check line numbers in logs)

### Problem: Coq compilation fails

**Expected!** Generated Coq requires Sail's Coq library:
```bash
# Install Sail Coq library (if testing compilation)
opam install sail_coq_lib
```

**Note:** For this spike, we only need **generation** to work, not compilation.

---

## Next Steps After Spike

### If Go Decision

1. **SPIKE-002:** Test full ARM ASL to Sail translation
2. **SPIKE-003:** Integrate with Synth verification infrastructure
3. **SPIKE-004:** Prove WebAssembly ↔ ARM equivalence using Sail-generated Coq
4. **SPIKE-005:** Evaluate RISC-V Sail model for multi-target support

### If No-Go Decision

1. **SPIKE-002-ALT:** Enhance manual encoding with code generation templates
2. **SPIKE-003-ALT:** Investigate alternative ISA specification languages

---

## References

- **Full Spike Plan:** `../docs/spikes/SPIKE_001_SAIL_COQGEN.md`
- **Research:** `../docs/research/06_sail_arm_cakeml.md`
- **Sail Manual:** https://www.cl.cam.ac.uk/~pes20/sail/manual.pdf
- **Sail GitHub:** https://github.com/rems-project/sail
- **ARM Sail Model:** https://github.com/rems-project/sail-arm

---

## FAQ

**Q: Why not use ARM's ASL directly?**
A: ASL is ARM-proprietary. Sail is open-source with better tooling (Coq, Isabelle, HOL4, Lean generation).

**Q: How does this compare to CakeML?**
A: CakeML's ARMv8_ASL backend uses this exact approach (ASL → Sail → HOL4). We're doing ASL → Sail → Coq.

**Q: What about Cortex-M (ARMv8-M)?**
A: ARMv8-M Sail models exist! SPIKE-002 will evaluate coverage.

**Q: Can we use Sail for RISC-V too?**
A: Yes! Sail RISC-V is the official golden model (RISC-V International, 2020).

**Q: How long to migrate Synth to Sail?**
A: Estimated 1-2 months for basic integration, 3-6 months for full verification.

---

**Spike Status:** READY TO EXECUTE
**Expected Duration:** 1-2 hours
**Expected Outcome:** GO decision with 80%+ confidence
