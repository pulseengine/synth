//! Synthesis Rules for WebAssembly→ARM Optimization
//!
//! ISLE-inspired declarative transformation rules

use serde::{Deserialize, Serialize};
pub use synth_core::WasmOp;

/// Synthesis rule for pattern-based transformations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SynthesisRule {
    /// Rule name/identifier
    pub name: String,

    /// Priority (higher = applied first)
    pub priority: i32,

    /// Pattern to match
    pub pattern: Pattern,

    /// Replacement/transformation
    pub replacement: Replacement,

    /// Cost model (lower is better)
    pub cost: Cost,
}

/// Pattern to match in IR
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Pattern {
    /// Match a WebAssembly instruction
    WasmInstr(WasmOp),

    /// Match a sequence of instructions
    Sequence(Vec<Pattern>),

    /// Match with variable binding
    Var(String, Box<Pattern>),

    /// Match any instruction (wildcard)
    Any,
}

/// Replacement/transformation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Replacement {
    /// Generate ARM instruction
    ArmInstr(ArmOp),

    /// Sequence of ARM instructions
    ArmSequence(Vec<ArmOp>),

    /// Use a variable from pattern
    Var(String),

    /// Inline function call
    Inline,

    /// No transformation (identity)
    Identity,
}

/// ARM instruction operations
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ArmOp {
    // Data processing
    Add {
        rd: Reg,
        rn: Reg,
        op2: Operand2,
    },
    Sub {
        rd: Reg,
        rn: Reg,
        op2: Operand2,
    },
    // i64 support: Add/Sub with carry/borrow for register pairs
    Adds {
        // Add and set flags (for carry)
        rd: Reg,
        rn: Reg,
        op2: Operand2,
    },
    Adc {
        // Add with carry (uses C flag)
        rd: Reg,
        rn: Reg,
        op2: Operand2,
    },
    Subs {
        // Subtract and set flags (for borrow)
        rd: Reg,
        rn: Reg,
        op2: Operand2,
    },
    Sbc {
        // Subtract with carry (borrow)
        rd: Reg,
        rn: Reg,
        op2: Operand2,
    },
    Mul {
        rd: Reg,
        rn: Reg,
        rm: Reg,
    },
    Sdiv {
        rd: Reg,
        rn: Reg,
        rm: Reg,
    }, // Signed division (ARMv7-M+)
    Udiv {
        rd: Reg,
        rn: Reg,
        rm: Reg,
    }, // Unsigned division (ARMv7-M+)
    Mls {
        rd: Reg,
        rn: Reg,
        rm: Reg,
        ra: Reg,
    }, // Multiply and subtract (for modulo)
    And {
        rd: Reg,
        rn: Reg,
        op2: Operand2,
    },
    Orr {
        rd: Reg,
        rn: Reg,
        op2: Operand2,
    },
    Eor {
        rd: Reg,
        rn: Reg,
        op2: Operand2,
    },
    Lsl {
        rd: Reg,
        rn: Reg,
        shift: u32,
    },
    Lsr {
        rd: Reg,
        rn: Reg,
        shift: u32,
    },
    Asr {
        rd: Reg,
        rn: Reg,
        shift: u32,
    },
    Ror {
        rd: Reg,
        rn: Reg,
        shift: u32,
    }, // Rotate right (immediate)
    // Register-based shifts (shift amount in register)
    LslReg {
        rd: Reg,
        rn: Reg,
        rm: Reg,
    },
    LsrReg {
        rd: Reg,
        rn: Reg,
        rm: Reg,
    },
    AsrReg {
        rd: Reg,
        rn: Reg,
        rm: Reg,
    },
    RorReg {
        rd: Reg,
        rn: Reg,
        rm: Reg,
    },

    // Reverse subtract: Rd = imm - Rn (used for ROTL: 32 - shift_amount)
    Rsb {
        rd: Reg,
        rn: Reg,
        imm: u32,
    },

    // Bit manipulation (ARMv6T2+)
    Clz {
        rd: Reg,
        rm: Reg,
    }, // Count leading zeros
    Rbit {
        rd: Reg,
        rm: Reg,
    }, // Reverse bits (for CTZ)
    Popcnt {
        rd: Reg,
        rm: Reg,
    }, // Population count (pseudo-instruction for verification)
    Sxtb {
        rd: Reg,
        rm: Reg,
    }, // Sign-extend byte (8-bit to 32-bit)
    Sxth {
        rd: Reg,
        rm: Reg,
    }, // Sign-extend halfword (16-bit to 32-bit)

    // Move
    Mov {
        rd: Reg,
        op2: Operand2,
    },
    Mvn {
        rd: Reg,
        op2: Operand2,
    },
    // Move Wide (load 16-bit immediate into low half, zero upper)
    Movw {
        rd: Reg,
        imm16: u16,
    },
    // Move Top (load 16-bit immediate into high half, preserve low)
    Movt {
        rd: Reg,
        imm16: u16,
    },

    // Compare
    Cmp {
        rn: Reg,
        op2: Operand2,
    },

    /// Compare Negative (CMN) - computes Rn + op2 and sets flags
    /// CMN Rn, #1 sets Z flag if Rn == -1 (since -1 + 1 = 0)
    Cmn {
        rn: Reg,
        op2: Operand2,
    },

    // Load/Store
    Ldr {
        rd: Reg,
        addr: MemAddr,
    },
    Str {
        rd: Reg,
        addr: MemAddr,
    },

    // Branch
    B {
        label: String,
    },
    /// Branch with numeric offset (in instructions, not bytes)
    /// offset is signed: negative = backward, positive = forward
    BOffset {
        offset: i32,
    },
    /// Conditional branch with numeric offset
    /// Branch if condition is met (after CMP instruction)
    BCondOffset {
        cond: Condition,
        offset: i32,
    },
    /// Branch if Higher or Same (unsigned >=) - used for bounds checking
    /// Branches to label if C flag is set (after CMP, addr >= limit)
    Bhs {
        label: String,
    },
    /// Branch if Lower (unsigned <) - complementary to BHS
    Blo {
        label: String,
    },
    Bl {
        label: String,
    },
    Bx {
        rm: Reg,
    },
    // Branch with Link and Exchange (indirect call)
    Blx {
        rm: Reg,
    },

    // No operation
    Nop,

    /// Undefined instruction - triggers UsageFault (used for WASM traps)
    /// imm8 can encode trap reason (0 = div by zero, 1 = integer overflow)
    Udf {
        imm: u8,
    },

    // Conditional execution (for verification)
    // SetCond evaluates a condition based on NZCV flags and sets register to 0 or 1
    SetCond {
        rd: Reg,
        cond: Condition,
    },

    // i64 comparison: compare two register pairs, result 0/1 in rd
    // Emits multi-instruction sequence (CMP chain or SBCS approach)
    I64SetCond {
        rd: Reg,
        rn_lo: Reg,
        rn_hi: Reg,
        rm_lo: Reg,
        rm_hi: Reg,
        cond: Condition,
    },

    // i64 equal-to-zero: test if register pair is zero, result 0/1 in rd
    I64SetCondZ {
        rd: Reg,
        rn_lo: Reg,
        rn_hi: Reg,
    },

    /// i64 multiply: UMULL + MLA cross products, result in rd_lo:rd_hi
    I64Mul {
        rd_lo: Reg,
        rd_hi: Reg,
        rn_lo: Reg,
        rn_hi: Reg,
        rm_lo: Reg,
        rm_hi: Reg,
    },

    /// i64 shift left: multi-instruction with branch for n<32 vs n>=32
    I64Shl {
        rd_lo: Reg,
        rd_hi: Reg,
        rn_lo: Reg,
        rn_hi: Reg,
        rm_lo: Reg,
        rm_hi: Reg, // used as temp
    },

    /// i64 arithmetic shift right: sign-extending shift
    I64ShrS {
        rd_lo: Reg,
        rd_hi: Reg,
        rn_lo: Reg,
        rn_hi: Reg,
        rm_lo: Reg,
        rm_hi: Reg, // used as temp
    },

    /// i64 logical shift right: zero-extending shift
    I64ShrU {
        rd_lo: Reg,
        rd_hi: Reg,
        rn_lo: Reg,
        rn_hi: Reg,
        rm_lo: Reg,
        rm_hi: Reg, // used as temp
    },

    // Conditional move: MOV{cond} rd, rm - only executes if condition is true
    // Used in IT blocks for Thumb-2: IT <cond>; MOV rd, rm
    SelectMove {
        rd: Reg,
        rm: Reg,
        cond: Condition,
    },

    // Select operation (for verification)
    // Selects between two values based on condition
    // If rcond != 0, select rval1, else select rval2
    Select {
        rd: Reg,
        rval1: Reg,
        rval2: Reg,
        rcond: Reg,
    },

    // Local/Global variable access (pseudo-instructions for verification)
    LocalGet {
        rd: Reg,
        index: u32,
    },
    LocalSet {
        rs: Reg,
        index: u32,
    },
    LocalTee {
        rd: Reg,
        rs: Reg,
        index: u32,
    },
    GlobalGet {
        rd: Reg,
        index: u32,
    },
    GlobalSet {
        rs: Reg,
        index: u32,
    },

    // Control flow operations (pseudo-instructions for verification)
    // These model WASM control flow semantics for verification purposes
    BrTable {
        rd: Reg,
        index_reg: Reg,
        targets: Vec<u32>,
        default: u32,
    },
    Call {
        rd: Reg,
        func_idx: u32,
    },
    CallIndirect {
        rd: Reg,
        type_idx: u32,
        table_index_reg: Reg,
    },

    // ========================================================================
    // i64 Operations (Phase 2) - Pseudo-instructions for verification
    // ========================================================================
    // 64-bit operations on ARM32 use register pairs (low:high)
    // These pseudo-instructions abstract multi-register operations
    // Actual compiler would expand these to instruction sequences

    // i64 Arithmetic (register pairs)
    I64Add {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64Sub {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64DivS {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64DivU {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64RemS {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64RemU {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },

    // i64 Bitwise (register pairs)
    I64And {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64Or {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64Xor {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },

    // i64 Rotation operations (register pairs, shift amount in single register)
    I64Rotl {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
        rnhi: Reg,
        shift: Reg,
    },
    I64Rotr {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
        rnhi: Reg,
        shift: Reg,
    },

    // i64 Bit manipulation (register pairs)
    I64Clz {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
    }, // Count leading zeros (result is 32-bit)
    I64Ctz {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
    }, // Count trailing zeros
    I64Popcnt {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
    }, // Population count

    // i64 Comparison (register pairs, result in single register)
    I64Eqz {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
    },
    I64Eq {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64Ne {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64LtS {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64LtU {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64LeS {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64LeU {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64GtS {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64GtU {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64GeS {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },
    I64GeU {
        rd: Reg,
        rnlo: Reg,
        rnhi: Reg,
        rmlo: Reg,
        rmhi: Reg,
    },

    // i64 Constants (load 64-bit immediate into register pair)
    I64Const {
        rdlo: Reg,
        rdhi: Reg,
        value: i64,
    },

    // i64 Memory operations (load/store with register pairs)
    I64Ldr {
        rdlo: Reg,
        rdhi: Reg,
        addr: MemAddr,
    },
    I64Str {
        rdlo: Reg,
        rdhi: Reg,
        addr: MemAddr,
    },

    // i64 Conversion operations
    I64ExtendI32S {
        rdlo: Reg,
        rdhi: Reg,
        rn: Reg,
    }, // Sign-extend i32 to i64
    I64ExtendI32U {
        rdlo: Reg,
        rdhi: Reg,
        rn: Reg,
    }, // Zero-extend i32 to i64

    // i64 in-place sign extension (operate on register pair)
    I64Extend8S {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
    }, // Sign-extend low 8 bits to 64 bits
    I64Extend16S {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
    }, // Sign-extend low 16 bits to 64 bits
    I64Extend32S {
        rdlo: Reg,
        rdhi: Reg,
        rnlo: Reg,
    }, // Sign-extend low 32 bits to 64 bits

    I32WrapI64 {
        rd: Reg,
        rnlo: Reg,
    }, // Wrap i64 to i32 (take low 32 bits)

    // ========================================================================
    // f32 Operations (Phase 2 - Floating Point)
    // ========================================================================
    // VFP (Vector Floating Point) instructions for 32-bit float operations
    // ARM uses separate floating-point register file (S0-S31 for single precision)

    // f32 Arithmetic
    F32Add {
        sd: VfpReg,
        sn: VfpReg,
        sm: VfpReg,
    }, // VADD.F32 Sd, Sn, Sm
    F32Sub {
        sd: VfpReg,
        sn: VfpReg,
        sm: VfpReg,
    }, // VSUB.F32 Sd, Sn, Sm
    F32Mul {
        sd: VfpReg,
        sn: VfpReg,
        sm: VfpReg,
    }, // VMUL.F32 Sd, Sn, Sm
    F32Div {
        sd: VfpReg,
        sn: VfpReg,
        sm: VfpReg,
    }, // VDIV.F32 Sd, Sn, Sm

    // f32 Math Functions
    F32Abs {
        sd: VfpReg,
        sm: VfpReg,
    }, // VABS.F32 Sd, Sm
    F32Neg {
        sd: VfpReg,
        sm: VfpReg,
    }, // VNEG.F32 Sd, Sm
    F32Sqrt {
        sd: VfpReg,
        sm: VfpReg,
    }, // VSQRT.F32 Sd, Sm
    F32Ceil {
        sd: VfpReg,
        sm: VfpReg,
    }, // Pseudo (rounding mode change + VRINTP)
    F32Floor {
        sd: VfpReg,
        sm: VfpReg,
    }, // Pseudo (rounding mode change + VRINTM)
    F32Trunc {
        sd: VfpReg,
        sm: VfpReg,
    }, // Pseudo (rounding mode change + VRINTZ)
    F32Nearest {
        sd: VfpReg,
        sm: VfpReg,
    }, // Pseudo (rounding mode change + VRINTN)
    F32Min {
        sd: VfpReg,
        sn: VfpReg,
        sm: VfpReg,
    }, // Pseudo (compare + select)
    F32Max {
        sd: VfpReg,
        sn: VfpReg,
        sm: VfpReg,
    }, // Pseudo (compare + select)
    F32Copysign {
        sd: VfpReg,
        sn: VfpReg,
        sm: VfpReg,
    }, // Pseudo (bitwise operations)

    // f32 Comparisons (result in integer register)
    F32Eq {
        rd: Reg,
        sn: VfpReg,
        sm: VfpReg,
    }, // VCMP.F32 + VMRS + condition check
    F32Ne {
        rd: Reg,
        sn: VfpReg,
        sm: VfpReg,
    },
    F32Lt {
        rd: Reg,
        sn: VfpReg,
        sm: VfpReg,
    },
    F32Le {
        rd: Reg,
        sn: VfpReg,
        sm: VfpReg,
    },
    F32Gt {
        rd: Reg,
        sn: VfpReg,
        sm: VfpReg,
    },
    F32Ge {
        rd: Reg,
        sn: VfpReg,
        sm: VfpReg,
    },

    // f32 Constants and Memory
    F32Const {
        sd: VfpReg,
        value: f32,
    }, // VMOV.F32 Sd, #imm (or literal pool)
    F32Load {
        sd: VfpReg,
        addr: MemAddr,
    }, // VLDR.32 Sd, [Rn, #offset]
    F32Store {
        sd: VfpReg,
        addr: MemAddr,
    }, // VSTR.32 Sd, [Rn, #offset]

    // f32 Conversions
    F32ConvertI32S {
        sd: VfpReg,
        rm: Reg,
    }, // VMOV Sd, Rm + VCVT.F32.S32 Sd, Sd
    F32ConvertI32U {
        sd: VfpReg,
        rm: Reg,
    }, // VMOV Sd, Rm + VCVT.F32.U32 Sd, Sd
    F32ConvertI64S {
        sd: VfpReg,
        rmlo: Reg,
        rmhi: Reg,
    }, // Complex (requires library or multi-step)
    F32ConvertI64U {
        sd: VfpReg,
        rmlo: Reg,
        rmhi: Reg,
    }, // Complex (requires library or multi-step)
    F32ReinterpretI32 {
        sd: VfpReg,
        rm: Reg,
    }, // VMOV Sd, Rm (bitcast)
    I32ReinterpretF32 {
        rd: Reg,
        sm: VfpReg,
    }, // VMOV Rd, Sm (bitcast)
    I32TruncF32S {
        rd: Reg,
        sm: VfpReg,
    }, // VCVT.S32.F32 Sd, Sm + VMOV Rd, Sd
    I32TruncF32U {
        rd: Reg,
        sm: VfpReg,
    }, // VCVT.U32.F32 Sd, Sm + VMOV Rd, Sd

    // ========================================================================
    // f64 Operations (Phase 2c - Double-Precision Floating Point)
    // ========================================================================

    // f64 Arithmetic
    F64Add {
        dd: VfpReg,
        dn: VfpReg,
        dm: VfpReg,
    }, // VADD.F64 Dd, Dn, Dm
    F64Sub {
        dd: VfpReg,
        dn: VfpReg,
        dm: VfpReg,
    }, // VSUB.F64 Dd, Dn, Dm
    F64Mul {
        dd: VfpReg,
        dn: VfpReg,
        dm: VfpReg,
    }, // VMUL.F64 Dd, Dn, Dm
    F64Div {
        dd: VfpReg,
        dn: VfpReg,
        dm: VfpReg,
    }, // VDIV.F64 Dd, Dn, Dm

    // f64 Math Functions
    F64Abs {
        dd: VfpReg,
        dm: VfpReg,
    }, // VABS.F64 Dd, Dm
    F64Neg {
        dd: VfpReg,
        dm: VfpReg,
    }, // VNEG.F64 Dd, Dm
    F64Sqrt {
        dd: VfpReg,
        dm: VfpReg,
    }, // VSQRT.F64 Dd, Dm
    F64Ceil {
        dd: VfpReg,
        dm: VfpReg,
    }, // Pseudo (rounding mode change + VRINTP)
    F64Floor {
        dd: VfpReg,
        dm: VfpReg,
    }, // Pseudo (rounding mode change + VRINTM)
    F64Trunc {
        dd: VfpReg,
        dm: VfpReg,
    }, // Pseudo (rounding mode change + VRINTZ)
    F64Nearest {
        dd: VfpReg,
        dm: VfpReg,
    }, // Pseudo (rounding mode change + VRINTN)
    F64Min {
        dd: VfpReg,
        dn: VfpReg,
        dm: VfpReg,
    }, // Pseudo (compare + select)
    F64Max {
        dd: VfpReg,
        dn: VfpReg,
        dm: VfpReg,
    }, // Pseudo (compare + select)
    F64Copysign {
        dd: VfpReg,
        dn: VfpReg,
        dm: VfpReg,
    }, // Pseudo (bitwise operations)

    // f64 Comparisons (result in integer register)
    F64Eq {
        rd: Reg,
        dn: VfpReg,
        dm: VfpReg,
    }, // VCMP.F64 + VMRS + condition check
    F64Ne {
        rd: Reg,
        dn: VfpReg,
        dm: VfpReg,
    },
    F64Lt {
        rd: Reg,
        dn: VfpReg,
        dm: VfpReg,
    },
    F64Le {
        rd: Reg,
        dn: VfpReg,
        dm: VfpReg,
    },
    F64Gt {
        rd: Reg,
        dn: VfpReg,
        dm: VfpReg,
    },
    F64Ge {
        rd: Reg,
        dn: VfpReg,
        dm: VfpReg,
    },

    // f64 Constants and Memory
    F64Const {
        dd: VfpReg,
        value: f64,
    }, // VMOV.F64 Dd, #imm (or literal pool)
    F64Load {
        dd: VfpReg,
        addr: MemAddr,
    }, // VLDR.64 Dd, [Rn, #offset]
    F64Store {
        dd: VfpReg,
        addr: MemAddr,
    }, // VSTR.64 Dd, [Rn, #offset]

    // f64 Conversions
    F64ConvertI32S {
        dd: VfpReg,
        rm: Reg,
    }, // VMOV Sd, Rm + VCVT.F64.S32 Dd, Sd
    F64ConvertI32U {
        dd: VfpReg,
        rm: Reg,
    }, // VMOV Sd, Rm + VCVT.F64.U32 Dd, Sd
    F64ConvertI64S {
        dd: VfpReg,
        rmlo: Reg,
        rmhi: Reg,
    }, // Complex (requires library or multi-step)
    F64ConvertI64U {
        dd: VfpReg,
        rmlo: Reg,
        rmhi: Reg,
    }, // Complex (requires library or multi-step)
    F64PromoteF32 {
        dd: VfpReg,
        sm: VfpReg,
    }, // VCVT.F64.F32 Dd, Sm
    F64ReinterpretI64 {
        dd: VfpReg,
        rmlo: Reg,
        rmhi: Reg,
    }, // VMOV Dd, Rmlo, Rmhi (bitcast)
    I64ReinterpretF64 {
        rdlo: Reg,
        rdhi: Reg,
        dm: VfpReg,
    }, // VMOV Rdlo, Rdhi, Dm (bitcast)
    I64TruncF64S {
        rdlo: Reg,
        rdhi: Reg,
        dm: VfpReg,
    }, // Complex (requires library or multi-step)
    I64TruncF64U {
        rdlo: Reg,
        rdhi: Reg,
        dm: VfpReg,
    }, // Complex (requires library or multi-step)
    I32TruncF64S {
        rd: Reg,
        dm: VfpReg,
    }, // VCVT.S32.F64 Sd, Dm + VMOV Rd, Sd
    I32TruncF64U {
        rd: Reg,
        dm: VfpReg,
    }, // VCVT.U32.F64 Sd, Dm + VMOV Rd, Sd
}

/// ARM condition codes (based on NZCV flags)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Condition {
    EQ, // Equal (Z == 1)
    NE, // Not equal (Z == 0)
    LT, // Less than signed (N != V)
    LE, // Less than or equal signed (Z == 1 || N != V)
    GT, // Greater than signed (Z == 0 && N == V)
    GE, // Greater than or equal signed (N == V)
    LO, // Less than unsigned (C == 0)
    LS, // Less than or equal unsigned (C == 0 || Z == 1)
    HI, // Greater than unsigned (C == 1 && Z == 0)
    HS, // Greater than or equal unsigned (C == 1)
}

/// ARM register
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Reg {
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
    R11,
    R12,
    SP, // Stack pointer (R13)
    LR, // Link register (R14)
    PC, // Program counter (R15)
}

/// ARM VFP (Vector Floating Point) register
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum VfpReg {
    // Single-precision registers (32-bit)
    S0,
    S1,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    S12,
    S13,
    S14,
    S15,
    S16,
    S17,
    S18,
    S19,
    S20,
    S21,
    S22,
    S23,
    S24,
    S25,
    S26,
    S27,
    S28,
    S29,
    S30,
    S31,

    // Double-precision registers (64-bit)
    // Note: D0 = S0:S1, D1 = S2:S3, etc.
    D0,
    D1,
    D2,
    D3,
    D4,
    D5,
    D6,
    D7,
    D8,
    D9,
    D10,
    D11,
    D12,
    D13,
    D14,
    D15,
}

/// ARM operand 2 (flexible second operand)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Operand2 {
    /// Immediate value
    Imm(i32),

    /// Register
    Reg(Reg),

    /// Register with shift
    RegShift {
        rm: Reg,
        shift: ShiftType,
        amount: u32,
    },
}

/// ARM shift types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ShiftType {
    LSL, // Logical shift left
    LSR, // Logical shift right
    ASR, // Arithmetic shift right
    ROR, // Rotate right
}

/// Memory address
///
/// Supports three addressing modes:
/// 1. [base, #imm] - base register + immediate offset
/// 2. [base, Roff] - base register + register offset
/// 3. [base, Roff, #imm] - base register + register offset + immediate
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MemAddr {
    /// Base register
    pub base: Reg,

    /// Immediate offset (can be combined with offset_reg)
    pub offset: i32,

    /// Optional register offset for [base, Roff] addressing
    /// Used for WASM memory access where base=R11 (memory base) and offset_reg=address from stack
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub offset_reg: Option<Reg>,
}

impl MemAddr {
    /// Create a new memory address with immediate offset only
    pub fn imm(base: Reg, offset: i32) -> Self {
        Self {
            base,
            offset,
            offset_reg: None,
        }
    }

    /// Create a new memory address with register offset
    pub fn reg(base: Reg, offset_reg: Reg) -> Self {
        Self {
            base,
            offset: 0,
            offset_reg: Some(offset_reg),
        }
    }

    /// Create a new memory address with both register and immediate offset
    pub fn reg_imm(base: Reg, offset_reg: Reg, offset: i32) -> Self {
        Self {
            base,
            offset,
            offset_reg: Some(offset_reg),
        }
    }
}

/// Cost model for transformations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Cost {
    /// Cycles (estimated)
    pub cycles: u32,

    /// Code size in bytes
    pub code_size: u32,

    /// Register pressure
    pub registers: u32,
}

impl Cost {
    /// Calculate total cost with weights
    pub fn total(&self) -> u32 {
        // Weight: 1 cycle = 10, 1 byte = 1, 1 register = 5
        self.cycles * 10 + self.code_size + self.registers * 5
    }
}

/// Rule database
pub struct RuleDatabase {
    rules: Vec<SynthesisRule>,
}

impl RuleDatabase {
    /// Create a new empty rule database
    pub fn new() -> Self {
        Self { rules: Vec::new() }
    }

    /// Add a rule
    pub fn add_rule(&mut self, rule: SynthesisRule) {
        self.rules.push(rule);
        // Sort by priority (highest first)
        self.rules.sort_by(|a, b| b.priority.cmp(&a.priority));
    }

    /// Get all rules
    pub fn rules(&self) -> &[SynthesisRule] {
        &self.rules
    }

    /// Create a database with standard optimizations
    pub fn with_standard_rules() -> Self {
        let mut db = Self::new();

        // Rule 1: Strength reduction (mul by power of 2 → shift)
        db.add_rule(SynthesisRule {
            name: "mul_pow2_to_shift".to_string(),
            priority: 100,
            pattern: Pattern::WasmInstr(WasmOp::I32Mul),
            replacement: Replacement::ArmInstr(ArmOp::Lsl {
                rd: Reg::R0,
                rn: Reg::R0,
                shift: 0, // Would be computed from constant
            }),
            cost: Cost {
                cycles: 1,
                code_size: 2,
                registers: 1,
            },
        });

        // Rule 2: Constant folding
        db.add_rule(SynthesisRule {
            name: "const_add_fold".to_string(),
            priority: 90,
            pattern: Pattern::Sequence(vec![
                Pattern::WasmInstr(WasmOp::I32Const(0)),
                Pattern::WasmInstr(WasmOp::I32Const(0)),
                Pattern::WasmInstr(WasmOp::I32Add),
            ]),
            replacement: Replacement::ArmInstr(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(0), // Would be sum of constants
            }),
            cost: Cost {
                cycles: 1,
                code_size: 2,
                registers: 1,
            },
        });

        // Rule 3: ARM instruction fusion (add with shift)
        db.add_rule(SynthesisRule {
            name: "add_with_shift".to_string(),
            priority: 80,
            pattern: Pattern::Sequence(vec![
                Pattern::WasmInstr(WasmOp::I32Shl),
                Pattern::WasmInstr(WasmOp::I32Add),
            ]),
            replacement: Replacement::ArmInstr(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::RegShift {
                    rm: Reg::R2,
                    shift: ShiftType::LSL,
                    amount: 2, // Would be extracted from pattern
                },
            }),
            cost: Cost {
                cycles: 1,
                code_size: 2,
                registers: 3,
            },
        });

        db
    }
}

impl Default for RuleDatabase {
    fn default() -> Self {
        Self::with_standard_rules()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rule_database_creation() {
        let db = RuleDatabase::new();
        assert_eq!(db.rules().len(), 0);
    }

    #[test]
    fn test_standard_rules() {
        let db = RuleDatabase::with_standard_rules();
        assert!(db.rules().len() > 0);

        // Rules should be sorted by priority
        for i in 1..db.rules().len() {
            assert!(db.rules()[i - 1].priority >= db.rules()[i].priority);
        }
    }

    #[test]
    fn test_cost_calculation() {
        let cost = Cost {
            cycles: 2,
            code_size: 4,
            registers: 1,
        };

        // 2*10 + 4 + 1*5 = 29
        assert_eq!(cost.total(), 29);
    }

    #[test]
    fn test_rule_priority_sorting() {
        let mut db = RuleDatabase::new();

        db.add_rule(SynthesisRule {
            name: "low".to_string(),
            priority: 10,
            pattern: Pattern::Any,
            replacement: Replacement::Identity,
            cost: Cost {
                cycles: 1,
                code_size: 1,
                registers: 1,
            },
        });

        db.add_rule(SynthesisRule {
            name: "high".to_string(),
            priority: 100,
            pattern: Pattern::Any,
            replacement: Replacement::Identity,
            cost: Cost {
                cycles: 1,
                code_size: 1,
                registers: 1,
            },
        });

        // High priority rule should come first
        assert_eq!(db.rules()[0].name, "high");
        assert_eq!(db.rules()[1].name, "low");
    }
}
