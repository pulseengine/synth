# Phase 2c: f64 Implementation Plan

**Target**: Complete all 30 f64 (64-bit floating-point) operations
**Timeline**: 8-12 hours (3 sessions)
**Status**: Ready to Begin

---

## Overview

Phase 2c completes the WebAssembly Core 1.0 specification by implementing all f64 operations. This follows the same pattern as f32 (Phase 2b) but uses double-precision VFP registers.

### Operations Breakdown: 30 Total

| Category | Operations | Count |
|----------|-----------|-------|
| Arithmetic | add, sub, mul, div | 4 |
| Comparisons | eq, ne, lt, le, gt, ge | 6 |
| Math Functions | abs, neg, ceil, floor, trunc, nearest, sqrt, min, max, copysign | 10 |
| Memory | const, load, store | 3 |
| Conversions | convert_i32_s/u, convert_i64_s/u, promote_f32, demote_f64, reinterpret_i64, i64_reinterpret_f64 | 7 |

---

## Implementation Strategy

### Template: Reuse f32 Implementation

**Approach**: f64 operations are nearly identical to f32, just using:
- Double-precision VFP registers (D0-D15 instead of S0-S31)
- 64-bit representation instead of 32-bit
- Same IEEE 754 semantics

**Changes Required**:
1. Add f64 variants to WasmOp enum
2. Add f64 ARM operations to ArmOp enum
3. Implement semantics (copy from f32, adjust register types)
4. Update encoder (NOP placeholders or real ARM instructions)
5. Add verification tests

---

## Session 1: Arithmetic & Comparisons (4 hours)

**Target**: 10/30 operations (33%)

### Tasks

#### 1. Infrastructure (30 min)
- [ ] Add f64 operations to WasmOp enum (10 ops)
- [ ] Add F64 variants to ArmOp enum (10 ops)
- [ ] Update VfpReg to support double-precision

#### 2. Arithmetic Operations (1 hour)
- [ ] F64Add { dd, dn, dm }
- [ ] F64Sub { dd, dn, dm }
- [ ] F64Mul { dd, dn, dm }
- [ ] F64Div { dd, dn, dm }

**WASM Semantics**: Use Z3 FloatingPoint operations
**ARM Semantics**: VADD.F64, VSUB.F64, VMUL.F64, VDIV.F64

#### 3. Comparison Operations (1.5 hours)
- [ ] F64Eq { rd, dn, dm }
- [ ] F64Ne { rd, dn, dm }
- [ ] F64Lt { rd, dn, dm }
- [ ] F64Le { rd, dn, dm }
- [ ] F64Gt { rd, dn, dm }
- [ ] F64Ge { rd, dn, dm }

**WASM Semantics**: IEEE 754 comparison with NaN handling
**ARM Semantics**: VCMP.F64 + VMRS + conditional set

#### 4. Testing (1 hour)
- [ ] Add arithmetic tests
- [ ] Add comparison tests
- [ ] Test NaN handling
- [ ] Test infinity handling

**Commit**: "feat(phase2): Implement f64 arithmetic and comparisons (10/30 ops)"

---

## Session 2: Math Functions & Memory (4 hours)

**Target**: 23/30 operations (77%)

### Tasks

#### 1. Simple Math Functions (1 hour)
- [ ] F64Abs { dd, dm }
- [ ] F64Neg { dd, dm }
- [ ] F64Sqrt { dd, dm }

**ARM Semantics**: VABS.F64, VNEG.F64, VSQRT.F64

#### 2. Rounding Functions (1.5 hours)
- [ ] F64Ceil { dd, dm }
- [ ] F64Floor { dd, dm }
- [ ] F64Trunc { dd, dm }
- [ ] F64Nearest { dd, dm }

**ARM Semantics**: Complex (requires rounding mode manipulation)

#### 3. Min/Max/Copysign (1 hour)
- [ ] F64Min { dd, dn, dm }
- [ ] F64Max { dd, dn, dm }
- [ ] F64Copysign { dd, dn, dm }

**ARM Semantics**: Sequence of VCMP + conditional moves

#### 4. Memory Operations (30 min)
- [ ] F64Const { dd, value }
- [ ] F64Load { dd, addr }
- [ ] F64Store { dd, addr }

**ARM Semantics**: VLDR.64, VSTR.64, immediate load

**Commit**: "feat(phase2): Implement f64 math functions and memory (23/30 ops)"

---

## Session 3: Conversions & Testing (4 hours)

**Target**: 30/30 operations (100%)

### Tasks

#### 1. Integer Conversions (1.5 hours)
- [ ] F64ConvertI32S { dd, rm }
- [ ] F64ConvertI32U { dd, rm }
- [ ] F64ConvertI64S { dd, rmlo, rmhi }
- [ ] F64ConvertI64U { dd, rmlo, rmhi }

**ARM Semantics**: VCVT.F64.S32, VCVT.F64.U32, complex for i64

#### 2. Float Conversions (1 hour)
- [ ] F64PromoteF32 { dd, sm }
- [ ] F32DemoteF64 { sd, dm }

**ARM Semantics**: VCVT.F64.F32, VCVT.F32.F64

#### 3. Reinterpret Operations (30 min)
- [ ] F64ReinterpretI64 { dd, rmlo, rmhi }
- [ ] I64ReinterpretF64 { rdlo, rdhi, dm }

**ARM Semantics**: VMOV register transfers

#### 4. Comprehensive Testing (1 hour)
- [ ] Test all conversions
- [ ] Test edge cases (NaN, infinity, ±0)
- [ ] Test rounding modes
- [ ] Integration tests

**Commit**: "feat(phase2): Complete f64 conversions - Phase 2c DONE (30/30 ops)"

---

## ARM VFP Double-Precision Instructions

### Arithmetic
```
VADD.F64 Dd, Dn, Dm    # Double add
VSUB.F64 Dd, Dn, Dm    # Double sub
VMUL.F64 Dd, Dn, Dm    # Double mul
VDIV.F64 Dd, Dn, Dm    # Double div
```

### Math Functions
```
VABS.F64 Dd, Dm        # Absolute value
VNEG.F64 Dd, Dm        # Negation
VSQRT.F64 Dd, Dm       # Square root
```

### Comparisons
```
VCMP.F64 Dd, Dm        # Compare (sets FPSCR)
VMRS APSR_nzcv, FPSCR  # Transfer flags to APSR
MOVcc Rd, #1/#0        # Conditional result
```

### Memory
```
VLDR.64 Dd, [Rn, #off] # Load double
VSTR.64 Dd, [Rn, #off] # Store double
```

### Conversions
```
VCVT.F64.S32 Dd, Sm    # Signed i32 → f64
VCVT.F64.U32 Dd, Sm    # Unsigned i32 → f64
VCVT.S32.F64 Sd, Dm    # f64 → signed i32
VCVT.U32.F64 Sd, Dm    # f64 → unsigned i32
VCVT.F64.F32 Dd, Sm    # f32 → f64 (promote)
VCVT.F32.F64 Sd, Dm    # f64 → f32 (demote)
```

### Register Transfers
```
VMOV Dd, Rm, Rn        # Two ARM regs → double
VMOV Rm, Rn, Dd        # Double → two ARM regs
```

---

## Code Structure

### WasmOp Additions (rules.rs)
```rust
// f64 Arithmetic
F64Add,
F64Sub,
F64Mul,
F64Div,

// f64 Comparisons
F64Eq,
F64Ne,
F64Lt,
F64Le,
F64Gt,
F64Ge,

// f64 Math
F64Abs,
F64Neg,
F64Sqrt,
F64Ceil,
F64Floor,
F64Trunc,
F64Nearest,
F64Min,
F64Max,
F64Copysign,

// f64 Memory
F64Const(f64),
F64Load { offset: u32, align: u32 },
F64Store { offset: u32, align: u32 },

// f64 Conversions
F64ConvertI32S,
F64ConvertI32U,
F64ConvertI64S,
F64ConvertI64U,
F64PromoteF32,
F64ReinterpretI64,
I64ReinterpretF64,
I64TruncF64S,
I64TruncF64U,
I32TruncF64S,
I32TruncF64U,
```

### ArmOp Additions (rules.rs)
```rust
// f64 operations use Dd (double-precision) instead of Sd (single)
F64Add { dd: VfpReg, dn: VfpReg, dm: VfpReg },
F64Sub { dd: VfpReg, dn: VfpReg, dm: VfpReg },
// ... etc (mirror f32 structure)
```

---

## Testing Strategy

### Unit Tests
- Arithmetic operations with normal values
- Comparisons with NaN, infinity, ±0
- Math functions edge cases
- Conversions round-trip
- Memory alignment

### Integration Tests
- Complex expressions
- Mixed f32/f64 operations
- Float-integer interactions
- IEEE 754 compliance

### Edge Cases
- NaN propagation
- Infinity arithmetic
- Signed zero handling
- Rounding mode effects
- Denormalized numbers

---

## Success Criteria

- ✅ All 30 f64 operations implemented
- ✅ All operations compile without errors
- ✅ All verification tests pass
- ✅ IEEE 754 semantics correct
- ✅ Documentation complete
- ✅ Commit messages detailed

---

## Estimated Timeline

| Session | Duration | Operations | Cumulative |
|---------|----------|-----------|------------|
| Session 1 | 4 hours | 10 ops | 33% |
| Session 2 | 4 hours | 13 ops | 77% |
| Session 3 | 4 hours | 7 ops | 100% |
| **Total** | **12 hours** | **30 ops** | **100%** |

**Buffer**: +2 hours for debugging and polish

---

## Post-Completion

After f64 completion:
1. **Update PHASE2_KICKOFF.md**: Mark Phase 2 100% complete
2. **Create session summary**: Document the f64 implementation
3. **Update ANALYSIS_AND_PLAN.md**: Mark Phase 2c complete
4. **Run full test suite**: Ensure everything passes
5. **Performance baseline**: Benchmark f64 operations
6. **Begin Phase 3**: Start SIMD planning

---

## Notes

- f64 implementation should be straightforward by replicating f32
- Main difference is register type (Dd vs Sd) and data size
- IEEE 754 semantics are identical
- Focus on correctness; optimization comes later
- Document any ARM-specific quirks

---

**Ready to Execute**: Yes
**Dependencies**: None (f32 complete)
**Risk Level**: Low (well-understood pattern)
**Priority**: High (completes WebAssembly Core 1.0)
