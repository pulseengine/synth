# Phase 2: Floating-Point Operations (f32/f64)

**Date**: November 17, 2025
**Status**: 📋 **Planning**
**Branch**: `claude/analyze-and-plan-01C71LBryojcFNnSmLuCy3o1`

---

## Executive Summary

With i64 operations complete (100% coverage), Phase 2 continues with floating-point operations. WebAssembly supports both 32-bit (f32) and 64-bit (f64) IEEE 754 floating-point operations, totaling approximately 60 operations.

### Floating-Point Operation Count
- **f32 Operations**: ~30 operations
- **f64 Operations**: ~30 operations
- **Total FP Operations**: ~60 operations

---

## f32 Operations (32-bit Float)

### Arithmetic (4)
- f32.add
- f32.sub
- f32.mul
- f32.div

### Comparisons (6)
- f32.eq
- f32.ne
- f32.lt
- f32.le
- f32.gt
- f32.ge

### Math Functions (10)
- f32.abs - Absolute value
- f32.neg - Negation
- f32.ceil - Ceiling
- f32.floor - Floor
- f32.trunc - Truncate toward zero
- f32.nearest - Round to nearest even
- f32.sqrt - Square root
- f32.min - Minimum
- f32.max - Maximum
- f32.copysign - Copy sign bit

### Constants & Memory (3)
- f32.const
- f32.load
- f32.store

### Conversions (7)
- f32.convert_i32_s - Convert signed i32 to f32
- f32.convert_i32_u - Convert unsigned i32 to f32
- f32.convert_i64_s - Convert signed i64 to f32
- f32.convert_i64_u - Convert unsigned i64 to f32
- f32.demote_f64 - Convert f64 to f32 (demote)
- f32.reinterpret_i32 - Reinterpret i32 bits as f32
- i32.reinterpret_f32 - Reinterpret f32 bits as i32

**Total f32 Operations**: 30

---

## f64 Operations (64-bit Float)

### Arithmetic (4)
- f64.add
- f64.sub
- f64.mul
- f64.div

### Comparisons (6)
- f64.eq
- f64.ne
- f64.lt
- f64.le
- f64.gt
- f64.ge

### Math Functions (10)
- f64.abs - Absolute value
- f64.neg - Negation
- f64.ceil - Ceiling
- f64.floor - Floor
- f64.trunc - Truncate toward zero
- f64.nearest - Round to nearest even
- f64.sqrt - Square root
- f64.min - Minimum
- f64.max - Maximum
- f64.copysign - Copy sign bit

### Constants & Memory (3)
- f64.const
- f64.load
- f64.store

### Conversions (7)
- f64.convert_i32_s - Convert signed i32 to f64
- f64.convert_i32_u - Convert unsigned i32 to f64
- f64.convert_i64_s - Convert signed i64 to f64
- f64.convert_i64_u - Convert unsigned i64 to f64
- f64.promote_f32 - Convert f32 to f64 (promote)
- f64.reinterpret_i64 - Reinterpret i64 bits as f64
- i64.reinterpret_f64 - Reinterpret f64 bits as i64

**Total f64 Operations**: 30

---

## ARM VFP (Vector Floating Point) Support

### ARM VFP Registers
- **Single-precision**: S0-S31 (32 registers)
- **Double-precision**: D0-D15 (16 registers, D0=S0:S1, D1=S2:S3, etc.)

### ARM VFP Instructions

**Arithmetic**:
- `VADD.F32 Sd, Sn, Sm` - Single-precision add
- `VADD.F64 Dd, Dn, Dm` - Double-precision add
- `VSUB.F32 Sd, Sn, Sm` - Single-precision sub
- `VSUB.F64 Dd, Dn, Dm` - Double-precision sub
- `VMUL.F32 Sd, Sn, Sm` - Single-precision mul
- `VMUL.F64 Dd, Dn, Dm` - Double-precision mul
- `VDIV.F32 Sd, Sn, Sm` - Single-precision div
- `VDIV.F64 Dd, Dn, Dm` - Double-precision div

**Math Functions**:
- `VABS.F32 Sd, Sm` - Absolute value
- `VABS.F64 Dd, Dm` - Double absolute
- `VNEG.F32 Sd, Sm` - Negation
- `VNEG.F64 Dd, Dm` - Double negation
- `VSQRT.F32 Sd, Sm` - Square root
- `VSQRT.F64 Dd, Dm` - Double square root

**Comparisons**:
- `VCMP.F32 Sd, Sm` - Compare and set FPSCR
- `VCMP.F64 Dd, Dm` - Double compare
- `VMRS APSR_nzcv, FPSCR` - Transfer FPSCR flags to APSR

**Conversions**:
- `VCVT.F32.S32 Sd, Sm` - Convert signed int to float
- `VCVT.F32.U32 Sd, Sm` - Convert unsigned int to float
- `VCVT.S32.F32 Sd, Sm` - Convert float to signed int
- `VCVT.U32.F32 Sd, Sm` - Convert float to unsigned int
- `VCVT.F64.F32 Dd, Sm` - Convert f32 to f64 (promote)
- `VCVT.F32.F64 Sd, Dm` - Convert f64 to f32 (demote)

**Memory**:
- `VLDR.32 Sd, [Rn, #offset]` - Load single
- `VLDR.64 Dd, [Rn, #offset]` - Load double
- `VSTR.32 Sd, [Rn, #offset]` - Store single
- `VSTR.64 Dd, [Rn, #offset]` - Store double

**Data Transfer**:
- `VMOV Sd, Rn` - Move ARM register to VFP
- `VMOV Rn, Sd` - Move VFP to ARM register
- `VMOV.F32 Sd, #imm` - Load immediate

---

## IEEE 754 Semantics

### Special Values
- **+0.0 and -0.0**: Signed zeros
- **+Infinity and -Infinity**: Overflow results
- **NaN (Not a Number)**: Invalid operation results
  - Quiet NaN (qNaN): Propagates through calculations
  - Signaling NaN (sNaN): Raises exceptions

### Rounding Modes
- Round to nearest, ties to even (default)
- Round toward zero (truncate)
- Round toward +infinity (ceiling)
- Round toward -infinity (floor)

### Comparison Semantics
- NaN != NaN (NaN is not equal to itself)
- -0.0 == +0.0 (signed zeros compare equal)
- Comparisons with NaN always return false (except ne)

### Math Operations
- `min(x, NaN) = NaN`, `min(NaN, x) = NaN`
- `max(x, NaN) = NaN`, `max(NaN, x) = NaN`
- `min(-0.0, +0.0) = -0.0`, `max(-0.0, +0.0) = +0.0`
- `sqrt(-x) = NaN` for x > 0
- `div(x, 0.0) = ±Infinity` or NaN

---

## Implementation Strategy

### Phase 2a: f32 Operations (Priority 1)
1. **Basic Arithmetic** (4 ops): add, sub, mul, div
2. **Simple Math** (3 ops): abs, neg, sqrt
3. **Comparisons** (6 ops): eq, ne, lt, le, gt, ge
4. **Constants & Memory** (3 ops): const, load, store
5. **Advanced Math** (7 ops): ceil, floor, trunc, nearest, min, max, copysign
6. **Conversions** (7 ops): convert_i32/i64, demote_f64, reinterpret

**f32 Total**: 30 operations

### Phase 2b: f64 Operations (Priority 2)
1. **Basic Arithmetic** (4 ops): add, sub, mul, div
2. **Simple Math** (3 ops): abs, neg, sqrt
3. **Comparisons** (6 ops): eq, ne, lt, le, gt, ge
4. **Constants & Memory** (3 ops): const, load, store
5. **Advanced Math** (7 ops): ceil, floor, trunc, nearest, min, max, copysign
6. **Conversions** (7 ops): convert_i32/i64, promote_f32, reinterpret

**f64 Total**: 30 operations

---

## Verification Challenges

### Challenge 1: IEEE 754 Compliance
**Problem**: Floating-point has complex semantics (NaN, infinity, signed zero)

**Solution**:
- Use Z3 FloatingPoint theory (FP sort)
- Model IEEE 754 special values explicitly
- Verify rounding modes and exception behavior

### Challenge 2: VFP Register Allocation
**Problem**: ARM has separate FP register file

**Solution**:
- Extend verification state with VFP registers
- Model S0-S31 for f32, D0-D15 for f64
- Track register usage separately from integer registers

### Challenge 3: Math Functions
**Problem**: Operations like ceil, floor, sqrt have no direct SMT equivalents

**Solution**:
- Use Z3's FloatingPoint theory functions where available
- Model complex operations symbolically
- Focus on semantic correctness over bit-exact verification

### Challenge 4: Conversions
**Problem**: int↔float conversions have rounding and overflow behavior

**Solution**:
- Use Z3's fp.to_sbv and fp.to_ubv for float→int
- Use to_fp for int→float conversions
- Model rounding modes explicitly

---

## Pseudo-Instruction Design

### f32 Pseudo-Instructions
```rust
// Arithmetic
F32Add { sd: VfpReg, sn: VfpReg, sm: VfpReg },
F32Sub { sd: VfpReg, sn: VfpReg, sm: VfpReg },
F32Mul { sd: VfpReg, sn: VfpReg, sm: VfpReg },
F32Div { sd: VfpReg, sn: VfpReg, sm: VfpReg },

// Math
F32Abs { sd: VfpReg, sm: VfpReg },
F32Neg { sd: VfpReg, sm: VfpReg },
F32Sqrt { sd: VfpReg, sm: VfpReg },
F32Ceil { sd: VfpReg, sm: VfpReg },  // Pseudo
F32Floor { sd: VfpReg, sm: VfpReg }, // Pseudo
F32Trunc { sd: VfpReg, sm: VfpReg }, // Pseudo
F32Nearest { sd: VfpReg, sm: VfpReg }, // Pseudo
F32Min { sd: VfpReg, sn: VfpReg, sm: VfpReg }, // Pseudo
F32Max { sd: VfpReg, sn: VfpReg, sm: VfpReg }, // Pseudo
F32Copysign { sd: VfpReg, sn: VfpReg, sm: VfpReg }, // Pseudo

// Comparisons
F32Eq { rd: Reg, sn: VfpReg, sm: VfpReg },
F32Ne { rd: Reg, sn: VfpReg, sm: VfpReg },
F32Lt { rd: Reg, sn: VfpReg, sm: VfpReg },
F32Le { rd: Reg, sn: VfpReg, sm: VfpReg },
F32Gt { rd: Reg, sn: VfpReg, sm: VfpReg },
F32Ge { rd: Reg, sn: VfpReg, sm: VfpReg },

// Memory
F32Load { sd: VfpReg, addr: MemAddr },
F32Store { sd: VfpReg, addr: MemAddr },
F32Const { sd: VfpReg, value: f32 },

// Conversions
F32ConvertI32S { sd: VfpReg, rm: Reg },
F32ConvertI32U { sd: VfpReg, rm: Reg },
F32ConvertI64S { sd: VfpReg, rmlo: Reg, rmhi: Reg },
F32ConvertI64U { sd: VfpReg, rmlo: Reg, rmhi: Reg },
F32DemoteF64 { sd: VfpReg, dm: VfpReg },
F32ReinterpretI32 { sd: VfpReg, rm: Reg },
I32ReinterpretF32 { rd: Reg, sm: VfpReg },
```

### f64 Pseudo-Instructions
Similar structure but using double-precision registers (Dd) and f64 values.

---

## Implementation Plan

### Session 1: f32 Basic Operations (10-12 ops)
- Add f32 operations to WasmOp enum
- Create VFP register type
- Implement basic arithmetic (add, sub, mul, div)
- Implement simple math (abs, neg, sqrt)
- Implement constants (const)
- Add VFP state to verification framework

**Target**: 12/30 f32 operations (40%)

### Session 2: f32 Comparisons & Memory (9 ops)
- Implement all 6 comparison operations
- Implement memory operations (load, store)
- Handle IEEE 754 special cases (NaN, infinity)

**Target**: 21/30 f32 operations (70%)

### Session 3: f32 Advanced Math & Conversions (9 ops)
- Implement advanced math (ceil, floor, trunc, nearest, min, max, copysign)
- Implement basic conversions (convert_i32_s/u)

**Target**: 30/30 f32 operations (100%)

### Session 4: f64 Operations (30 ops)
- Replicate f32 implementations for f64
- Implement f32↔f64 conversions (promote/demote)
- Implement i64 conversions

**Target**: 60/60 FP operations (100%)

---

## Success Criteria

### Correctness
- ✅ All operations compile without errors
- ✅ IEEE 754 special values handled correctly
- ✅ Rounding modes modeled appropriately
- ✅ NaN propagation semantics correct

### Coverage
- ✅ 100% f32 operation coverage (30/30)
- ✅ 100% f64 operation coverage (30/30)
- ✅ All conversions implemented

### Quality
- ✅ Clean git history with detailed commits
- ✅ Comprehensive inline documentation
- ✅ Session summaries with metrics

---

## Next Steps

1. **Immediate**: Add f32 operations to WasmOp enum
2. **Immediate**: Create VfpReg type and VFP pseudo-instructions
3. **Short-term**: Implement f32 arithmetic and simple math
4. **Medium-term**: Complete all f32 operations
5. **Long-term**: Implement all f64 operations

---

*Document Version: 1.0*
*Date: November 17, 2025*
*Status: Planning Phase*
*Target: 60 floating-point operations*
