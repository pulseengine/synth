# 07: WebAssembly Verification Ecosystem & AI-Assisted Proofs

## Executive Summary
Brief overview: The Wasm verification ecosystem has matured significantly. Several projects now exist that Synth should integrate with or learn from, particularly on the source-side (Wasm) formal semantics and AI-assisted proof generation.

## 1. Source-Side Formal Semantics

### 1.1 WasmCert-Coq
- Repository: https://github.com/WasmCert/WasmCert-Coq
- Published at FM'21
- Mechanized Wasm 2.0 spec in Coq/Rocq
- Type safety, interpreter soundness, type checker completeness
- **Relevance to Synth**: Could replace our hand-written wasm_semantics.rs (SMT encoding) with authoritative Coq-derived source semantics. Just as we plan to replace hand-written arm_semantics.rs with Sail-derived target semantics (see 06_sail_arm_cakeml.md), WasmCert-Coq provides the same for the source side.
- **Integration path**: Extract WasmCert-Coq theorems → generate SMT assertions for Z3 → plug into SourceSemantics trait (Phase 6)

### 1.2 Iris-Wasm
- Separation logic framework for modular Wasm verification
- Built on Iris (Coq)
- Enables compositional proofs: verify modules independently, compose guarantees
- **Relevance to Synth**: Critical for Component Model verification — when Wasm modules are composed via wit-bindgen, Iris-Wasm's separation logic can prove that composition preserves safety properties
- **Gap**: Not currently referenced in Synth's plan or docs

### 1.3 wasm-verify
- Coq-based function specification checking against Wasm bytecode
- CFG analysis for control flow
- Can prove functional properties (e.g., dup(n) == 2*n)
- **Relevance to Synth**: Could validate that our Wasm decoder preserves function contracts — a pre-compilation verification step

## 2. AI-Assisted Formal Verification

### 2.1 Saarthi (Infineon)
- First fully autonomous agentic AI formal verification engineer
- Multi-agent LLM system (GPT-4o based) for RTL verification
- Key mechanisms:
  - Coder/critic loop: coder generates SVAs, critic reviews against formal tool feedback
  - Iterative reflection with max iteration bounds
  - Human-in-the-loop for stuck states
  - Tool integration with Cadence JasperGold
- Performance: 40-100% success rate on FIFO verification benchmarks
- **Relevance to Synth**: The coder/critic pattern directly applies to our verification workflow:
  1. AI generates Z3 assertions / Coq lemmas for synthesis rules
  2. Z3/Coq checks them, returns counterexamples or proof failures
  3. AI refines based on feedback
  4. Human reviews final proofs
- **Gap**: Synth's plan has zero mention of AI-assisted proof generation. This is the biggest gap.

### 2.2 Certora Sunbeam
- Wasm smart contract verification (Soroban/Stellar)
- Pipeline: Rust specs → TAC → SMT
- AI-assisted rewrites and report generation
- **Relevance to Synth**: Low — focused on smart contract domain, not embedded compilation

### 2.3 FVPS (Formal Verification Platform Service)
- Blockchain-focused auto vulnerability reports
- Translation AI for code-to-formal-language conversion
- **Relevance to Synth**: Low — different domain

## 3. Proposed AI-Assisted Verification Strategy for Synth

### 3.1 Phase 1: SMT Assertion Generation (Near-term)
- Use Claude/LLM to generate Z3 BV assertions for new synthesis rules
- Feed counterexamples back to LLM for iterative refinement
- Human reviews final verified assertions
- Tool: Integrate with synth-verify's existing TranslationValidator

### 3.2 Phase 2: Coq Proof Sketching (Medium-term)
- Use LLM to generate Coq proof sketches from verified Z3 assertions
- Coq type checker validates or rejects
- Iterate until mechanized proof compiles
- Builds on WasmCert-Coq foundation for source semantics
- Builds on Sail-generated Coq for target semantics

### 3.3 Phase 3: Autonomous Verification Agent (Long-term)
- Saarthi-style multi-agent system specialized for compilation verification
- Coder agent: generates proofs for new synthesis rules
- Critic agent: checks against Z3/Coq, analyzes counterexamples
- Coverage agent: identifies unverified rules, prioritizes proof generation
- Human-in-the-loop: reviews completed proofs, resolves stuck states

## 4. Authoritative Semantics Strategy

### Current State
| Side | Current | Authoritative Source | Status |
|------|---------|---------------------|--------|
| Source (Wasm) | Hand-written SMT in wasm_semantics.rs | WasmCert-Coq | Not integrated |
| Target (ARM) | Hand-written SMT in arm_semantics.rs (2987 lines) | Sail/ARM ASL | Planned (see 06) |

### Target State
| Side | Target | Integration Path |
|------|--------|-----------------|
| Source (Wasm) | WasmCert-Coq → Coq → SMT extraction | SourceSemantics trait (Phase 6) |
| Target (ARM) | ARM ASL → Sail → Coq/SMT extraction | TargetSemantics trait (Phase 6) |

When both sides use authoritative semantics, the translation validator's proofs become truly authoritative — derived from the official Wasm spec AND the official ARM spec.

## 5. ISO 26262 / ASIL Implications

### Tool Qualification
- WasmCert-Coq proofs support TCL2/3 tool qualification under ISO 26262
- Coq-extracted algorithms can be compiled to Haskell/Rust, then to Wasm for sandboxed execution on ECUs
- AI-generated proofs require additional human review for ASIL D (ISO 26262 Part 8 requires qualified tools)

### Verification Tiers (Updated)
| Backend | Verification Level | Semantics Source | ASIL Target |
|---------|-------------------|-----------------|-------------|
| ARM (ours) | Per-rule proven | Hand-written → Sail-derived | ASIL D |
| ARM (ours) + WasmCert-Coq | Per-rule proven, authoritative | WasmCert-Coq + Sail | ASIL D (strongest) |
| aWsm/wasker/w2c2 | Per-compilation checked | Hand-written → Sail-derived | ASIL B |

## 6. Tools Comparison

| Tool/Framework | Proof Language | Key Features | AI Integration | Relevance to Synth |
|---------------|---------------|-------------|----------------|-------------------|
| WasmCert-Coq | Coq/Rocq | Full Wasm 2.0 semantics, interpreter | Low (manual) | HIGH - source semantics |
| wasm-verify | Coq | CFG analysis, function specs | None | MEDIUM - pre-compilation |
| Iris-Wasm | Coq/Iris | Modular separation logic proofs | Emerging | HIGH - Component Model |
| Saarthi | General FV | Multi-agent coder/critic loops | High | HIGH - methodology |
| Sunbeam/Certora | SMT (CVL) | Wasm contracts, auto-reports | Medium | LOW - different domain |
| VeriISLE | SMT | Cranelift ISLE rule verification | None | Already integrated |
| Arrival | SMT + Sail | Chains of ISel rules + authoritative ISA | None | Already integrated |
| Sail/ARM ASL | Coq/SMT | Authoritative ISA semantics | None | Already planned |

## 7. Recommendations

1. **Immediate**: Add WasmCert-Coq as source-side authoritative semantics target in plan Phase 6
2. **Near-term**: Prototype AI-assisted Z3 assertion generation for new synthesis rules
3. **Medium-term**: Integrate Iris-Wasm for Component Model compositional verification
4. **Long-term**: Build Saarthi-style autonomous verification agent for Synth

## References

- WasmCert-Coq: https://github.com/WasmCert/WasmCert-Coq (FM'21)
- Iris-Wasm: Separation logic for WebAssembly (Coq/Iris framework)
- Saarthi: Infineon's autonomous FV agent (2024)
- Certora Sunbeam: https://certora.com (Wasm smart contract verification)
- VeriISLE: Verification of ISLE instruction selection (CMU 2023)
- Arrival: Automatic reasoning about instruction-selection rules (OOPSLA 2024)
- Sail: https://github.com/rems-project/sail (ISA specification language)
