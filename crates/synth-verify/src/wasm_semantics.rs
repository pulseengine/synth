//! WASM Semantics Encoding to SMT
//!
//! Encodes WebAssembly operation semantics as SMT bitvector formulas.
//! Each WASM operation is translated to a mathematical formula that precisely
//! captures its behavior.

use synth_synthesis::WasmOp;
use z3::ast::{Ast, Bool, BV};
use z3::Context;

/// WASM semantics encoder
pub struct WasmSemantics<'ctx> {
    ctx: &'ctx Context,
    /// Memory model: maps addresses to 32-bit values
    /// For bounded verification, we use a limited memory space
    memory: Vec<BV<'ctx>>,
}

impl<'ctx> WasmSemantics<'ctx> {
    /// Create a new WASM semantics encoder
    pub fn new(ctx: &'ctx Context) -> Self {
        // Initialize bounded memory (256 32-bit words)
        let memory = (0..256)
            .map(|i| BV::new_const(ctx, format!("mem_{}", i), 32))
            .collect();

        Self { ctx, memory }
    }

    /// Create encoder with mutable memory for load/store operations
    pub fn new_with_memory(ctx: &'ctx Context, memory: Vec<BV<'ctx>>) -> Self {
        Self { ctx, memory }
    }

    /// Encode a WASM operation as an SMT formula
    ///
    /// Returns a bitvector representing the result of the operation.
    /// For operations with multiple operands, inputs are provided as a slice.
    pub fn encode_op(&self, op: &WasmOp, inputs: &[BV<'ctx>]) -> BV<'ctx> {
        match op {
            // Arithmetic operations
            WasmOp::I32Add => {
                assert_eq!(inputs.len(), 2, "I32Add requires 2 inputs");
                inputs[0].bvadd(&inputs[1])
            }

            WasmOp::I32Sub => {
                assert_eq!(inputs.len(), 2, "I32Sub requires 2 inputs");
                inputs[0].bvsub(&inputs[1])
            }

            WasmOp::I32Mul => {
                assert_eq!(inputs.len(), 2, "I32Mul requires 2 inputs");
                inputs[0].bvmul(&inputs[1])
            }

            WasmOp::I32DivS => {
                assert_eq!(inputs.len(), 2, "I32DivS requires 2 inputs");
                inputs[0].bvsdiv(&inputs[1])
            }

            WasmOp::I32DivU => {
                assert_eq!(inputs.len(), 2, "I32DivU requires 2 inputs");
                inputs[0].bvudiv(&inputs[1])
            }

            WasmOp::I32RemS => {
                assert_eq!(inputs.len(), 2, "I32RemS requires 2 inputs");
                inputs[0].bvsrem(&inputs[1])
            }

            WasmOp::I32RemU => {
                assert_eq!(inputs.len(), 2, "I32RemU requires 2 inputs");
                inputs[0].bvurem(&inputs[1])
            }

            // Bitwise operations
            WasmOp::I32And => {
                assert_eq!(inputs.len(), 2, "I32And requires 2 inputs");
                inputs[0].bvand(&inputs[1])
            }

            WasmOp::I32Or => {
                assert_eq!(inputs.len(), 2, "I32Or requires 2 inputs");
                inputs[0].bvor(&inputs[1])
            }

            WasmOp::I32Xor => {
                assert_eq!(inputs.len(), 2, "I32Xor requires 2 inputs");
                inputs[0].bvxor(&inputs[1])
            }

            WasmOp::I32Shl => {
                assert_eq!(inputs.len(), 2, "I32Shl requires 2 inputs");
                // WASM spec: shift amount is modulo 32
                let shift_mod = inputs[1].bvurem(&BV::from_i64(self.ctx, 32, 32));
                inputs[0].bvshl(&shift_mod)
            }

            WasmOp::I32ShrS => {
                assert_eq!(inputs.len(), 2, "I32ShrS requires 2 inputs");
                // WASM spec: shift amount is modulo 32
                let shift_mod = inputs[1].bvurem(&BV::from_i64(self.ctx, 32, 32));
                inputs[0].bvashr(&shift_mod)
            }

            WasmOp::I32ShrU => {
                assert_eq!(inputs.len(), 2, "I32ShrU requires 2 inputs");
                // WASM spec: shift amount is modulo 32
                let shift_mod = inputs[1].bvurem(&BV::from_i64(self.ctx, 32, 32));
                inputs[0].bvlshr(&shift_mod)
            }

            WasmOp::I32Rotl => {
                assert_eq!(inputs.len(), 2, "I32Rotl requires 2 inputs");
                // WASM spec: rotation amount is modulo 32
                let shift_mod = inputs[1].bvurem(&BV::from_i64(self.ctx, 32, 32));
                inputs[0].bvrotl(&shift_mod)
            }

            WasmOp::I32Rotr => {
                assert_eq!(inputs.len(), 2, "I32Rotr requires 2 inputs");
                // WASM spec: rotation amount is modulo 32
                let shift_mod = inputs[1].bvurem(&BV::from_i64(self.ctx, 32, 32));
                inputs[0].bvrotr(&shift_mod)
            }

            WasmOp::I32Clz => {
                assert_eq!(inputs.len(), 1, "I32Clz requires 1 input");
                // Count leading zeros - use bit tricks
                self.encode_clz(&inputs[0])
            }

            WasmOp::I32Ctz => {
                assert_eq!(inputs.len(), 1, "I32Ctz requires 1 input");
                // Count trailing zeros - use bit tricks
                self.encode_ctz(&inputs[0])
            }

            WasmOp::I32Popcnt => {
                assert_eq!(inputs.len(), 1, "I32Popcnt requires 1 input");
                // Population count - count 1 bits
                self.encode_popcnt(&inputs[0])
            }

            // Constants
            WasmOp::I32Const(value) => {
                assert_eq!(inputs.len(), 0, "I32Const requires 0 inputs");
                BV::from_i64(self.ctx, *value as i64, 32)
            }

            // Comparison operations (return i32: 0 or 1)
            WasmOp::I32Eqz => {
                assert_eq!(inputs.len(), 1, "I32Eqz requires 1 input");
                let zero = BV::from_i64(self.ctx, 0, 32);
                let cond = inputs[0]._eq(&zero);
                self.bool_to_bv32(&cond)
            }

            WasmOp::I32Eq => {
                assert_eq!(inputs.len(), 2, "I32Eq requires 2 inputs");
                let cond = inputs[0]._eq(&inputs[1]);
                self.bool_to_bv32(&cond)
            }

            WasmOp::I32Ne => {
                assert_eq!(inputs.len(), 2, "I32Ne requires 2 inputs");
                let cond = inputs[0]._eq(&inputs[1]).not();
                self.bool_to_bv32(&cond)
            }

            WasmOp::I32LtS => {
                assert_eq!(inputs.len(), 2, "I32LtS requires 2 inputs");
                let cond = inputs[0].bvslt(&inputs[1]);
                self.bool_to_bv32(&cond)
            }

            WasmOp::I32LtU => {
                assert_eq!(inputs.len(), 2, "I32LtU requires 2 inputs");
                let cond = inputs[0].bvult(&inputs[1]);
                self.bool_to_bv32(&cond)
            }

            WasmOp::I32LeS => {
                assert_eq!(inputs.len(), 2, "I32LeS requires 2 inputs");
                let cond = inputs[0].bvsle(&inputs[1]);
                self.bool_to_bv32(&cond)
            }

            WasmOp::I32LeU => {
                assert_eq!(inputs.len(), 2, "I32LeU requires 2 inputs");
                let cond = inputs[0].bvule(&inputs[1]);
                self.bool_to_bv32(&cond)
            }

            WasmOp::I32GtS => {
                assert_eq!(inputs.len(), 2, "I32GtS requires 2 inputs");
                let cond = inputs[0].bvsgt(&inputs[1]);
                self.bool_to_bv32(&cond)
            }

            WasmOp::I32GtU => {
                assert_eq!(inputs.len(), 2, "I32GtU requires 2 inputs");
                let cond = inputs[0].bvugt(&inputs[1]);
                self.bool_to_bv32(&cond)
            }

            WasmOp::I32GeS => {
                assert_eq!(inputs.len(), 2, "I32GeS requires 2 inputs");
                let cond = inputs[0].bvsge(&inputs[1]);
                self.bool_to_bv32(&cond)
            }

            WasmOp::I32GeU => {
                assert_eq!(inputs.len(), 2, "I32GeU requires 2 inputs");
                let cond = inputs[0].bvuge(&inputs[1]);
                self.bool_to_bv32(&cond)
            }

            // Control flow operations
            WasmOp::Select => {
                assert_eq!(inputs.len(), 3, "Select requires 3 inputs");
                // Select returns inputs[0] if inputs[2] != 0, else inputs[1]
                // WASM spec: select(val1, val2, cond) = cond ? val1 : val2
                let zero = BV::from_i64(self.ctx, 0, 32);
                let cond = inputs[2]._eq(&zero).not(); // cond != 0
                cond.ite(&inputs[0], &inputs[1])
            }

            WasmOp::Drop => {
                assert_eq!(inputs.len(), 1, "Drop requires 1 input");
                // Drop discards the value - for verification, we return a dummy value
                // In actual compilation, this operation doesn't produce a value
                BV::from_i64(self.ctx, 0, 32)
            }

            // Memory operations
            WasmOp::I32Load { offset, .. } => {
                assert_eq!(inputs.len(), 1, "I32Load requires 1 input (address)");
                // Load from memory: mem[address + offset]
                // For bounded verification, we model memory as array of symbolic values
                let address = inputs[0].clone();
                let offset_bv = BV::from_u64(self.ctx, *offset as u64, 32);
                let effective_addr = address.bvadd(&offset_bv);

                // For simplicity, return symbolic value based on address
                // A complete model would index into memory array
                BV::new_const(self.ctx, format!("load_{}_{}", offset, address), 32)
            }

            WasmOp::I32Store { offset, .. } => {
                assert_eq!(inputs.len(), 2, "I32Store requires 2 inputs (address, value)");
                // Store to memory: mem[address + offset] = value
                // For verification, we model the effect without mutating state
                let _address = inputs[0].clone();
                let value = inputs[1].clone();
                let _offset_bv = BV::from_u64(self.ctx, *offset as u64, 32);

                // Store returns no value in WASM, but we return the stored value for verification
                value
            }

            // Local/Global variable operations
            WasmOp::LocalGet(index) => {
                assert_eq!(inputs.len(), 0, "LocalGet requires 0 inputs");
                // Return symbolic value representing local variable
                BV::new_const(self.ctx, format!("local_{}", index), 32)
            }

            WasmOp::LocalSet(index) => {
                assert_eq!(inputs.len(), 1, "LocalSet requires 1 input");
                // Set local variable (modeled as assignment)
                // Return the value for verification purposes
                inputs[0].clone()
            }

            WasmOp::LocalTee(index) => {
                assert_eq!(inputs.len(), 1, "LocalTee requires 1 input");
                // Tee sets local and returns the value
                inputs[0].clone()
            }

            WasmOp::GlobalGet(index) => {
                assert_eq!(inputs.len(), 0, "GlobalGet requires 0 inputs");
                // Return symbolic value representing global variable
                BV::new_const(self.ctx, format!("global_{}", index), 32)
            }

            WasmOp::GlobalSet(index) => {
                assert_eq!(inputs.len(), 1, "GlobalSet requires 1 input");
                // Set global variable (modeled as assignment)
                // Return the value for verification purposes
                inputs[0].clone()
            }

            // No-op operations
            WasmOp::Nop => {
                assert_eq!(inputs.len(), 0, "Nop requires 0 inputs");
                // No operation - return zero
                BV::from_i64(self.ctx, 0, 32)
            }

            WasmOp::Unreachable => {
                assert_eq!(inputs.len(), 0, "Unreachable requires 0 inputs");
                // Unreachable - return symbolic value representing trap
                BV::new_const(self.ctx, "unreachable_trap", 32)
            }

            // Control flow operations
            WasmOp::Block => {
                assert_eq!(inputs.len(), 0, "Block requires 0 inputs");
                // Block is a structure marker - return zero
                BV::from_i64(self.ctx, 0, 32)
            }

            WasmOp::Loop => {
                assert_eq!(inputs.len(), 0, "Loop requires 0 inputs");
                // Loop is a structure marker - return zero
                BV::from_i64(self.ctx, 0, 32)
            }

            WasmOp::End => {
                assert_eq!(inputs.len(), 0, "End requires 0 inputs");
                // End is a structure marker - return zero
                BV::from_i64(self.ctx, 0, 32)
            }

            WasmOp::Br(label) => {
                assert_eq!(inputs.len(), 0, "Br requires 0 inputs");
                // Branch to label - return symbolic control flow value
                BV::new_const(self.ctx, format!("br_{}", label), 32)
            }

            WasmOp::BrIf(label) => {
                assert_eq!(inputs.len(), 1, "BrIf requires 1 input (condition)");
                // Conditional branch - return symbolic control flow value
                // The condition determines whether branch is taken
                let _cond = inputs[0].clone();
                BV::new_const(self.ctx, format!("br_if_{}", label), 32)
            }

            WasmOp::Return => {
                assert_eq!(inputs.len(), 0, "Return requires 0 inputs");
                // Return from function - return symbolic control flow value
                BV::new_const(self.ctx, "return", 32)
            }

            WasmOp::If => {
                assert_eq!(inputs.len(), 1, "If requires 1 input (condition)");
                // If is a structure marker with condition check
                let _cond = inputs[0].clone();
                BV::from_i64(self.ctx, 0, 32)
            }

            WasmOp::Else => {
                assert_eq!(inputs.len(), 0, "Else requires 0 inputs");
                // Else is a structure marker
                BV::from_i64(self.ctx, 0, 32)
            }

            WasmOp::BrTable { targets, default } => {
                assert_eq!(inputs.len(), 1, "BrTable requires 1 input (index)");
                // Multi-way branch based on index
                // If index < len(targets), branch to targets[index]
                // Otherwise, branch to default
                let index = inputs[0].clone();

                // For verification, we model this as symbolic control flow
                // A complete model would use nested ITEs to select the target
                BV::new_const(
                    self.ctx,
                    format!("br_table_{}_{}", targets.len(), default),
                    32
                )
            }

            WasmOp::Call(func_idx) => {
                // Function call - for verification, we model the call result symbolically
                // A complete model would require analyzing the called function
                // For now, we represent the result as a symbolic value
                BV::new_const(self.ctx, format!("call_{}", func_idx), 32)
            }

            WasmOp::CallIndirect(type_idx) => {
                assert_eq!(inputs.len(), 1, "CallIndirect requires 1 input (table index)");
                // Indirect function call through table
                // For verification, we model the call result symbolically
                let _table_index = inputs[0].clone();
                BV::new_const(self.ctx, format!("call_indirect_{}", type_idx), 32)
            }

            // ================================================================
            // i64 Operations (Phase 2) - Basic implementation
            // ================================================================
            // Note: These return 64-bit bitvectors, but current architecture
            // expects 32-bit. For now, we truncate to 32-bit for compatibility.
            // Full 64-bit support requires architectural changes.

            WasmOp::I64Const(value) => {
                assert_eq!(inputs.len(), 0, "I64Const requires 0 inputs");
                // For now, truncate to 32-bit (low part)
                // TODO: Full 64-bit support with register pairs
                let low32 = (*value as i32) as i64;
                BV::from_i64(self.ctx, low32, 32)
            }

            WasmOp::I64Add => {
                assert_eq!(inputs.len(), 2, "I64Add requires 2 inputs");
                // Simplified: treat as 32-bit for now
                // TODO: Implement full 64-bit addition with carry
                inputs[0].bvadd(&inputs[1])
            }

            WasmOp::I64Eqz => {
                assert_eq!(inputs.len(), 1, "I64Eqz requires 1 input");
                // Check if value is zero
                // Simplified: 32-bit check for now
                let zero = BV::from_i64(self.ctx, 0, 32);
                let cond = inputs[0]._eq(&zero);
                self.bool_to_bv32(&cond)
            }

            WasmOp::I32WrapI64 => {
                assert_eq!(inputs.len(), 1, "I32WrapI64 requires 1 input");
                // Wrap 64-bit to 32-bit (truncate)
                // Already 32-bit in our simplified model
                inputs[0].clone()
            }

            WasmOp::I64ExtendI32S => {
                assert_eq!(inputs.len(), 1, "I64ExtendI32S requires 1 input");
                // Sign-extend 32-bit to 64-bit
                // In our simplified model, already 32-bit
                // Full implementation would sign-extend to 64-bit
                inputs[0].clone()
            }

            WasmOp::I64ExtendI32U => {
                assert_eq!(inputs.len(), 1, "I64ExtendI32U requires 1 input");
                // Zero-extend 32-bit to 64-bit
                // In our simplified model, already 32-bit
                inputs[0].clone()
            }

            // i64 Memory operations
            WasmOp::I64Load { offset, .. } => {
                assert_eq!(inputs.len(), 1, "I64Load requires 1 input (address)");
                // Load 64-bit value from memory: mem[address + offset]
                // In our simplified 32-bit model, return symbolic 32-bit value (low part)
                // Full implementation would return 64-bit value
                let address = inputs[0].clone();
                let offset_bv = BV::from_u64(self.ctx, *offset as u64, 32);
                let effective_addr = address.bvadd(&offset_bv);

                // Return symbolic value representing the low 32 bits of the loaded i64
                BV::new_const(self.ctx, format!("i64load_{}_{}", offset, address), 32)
            }

            WasmOp::I64Store { offset, .. } => {
                assert_eq!(inputs.len(), 2, "I64Store requires 2 inputs (address, value)");
                // Store 64-bit value to memory: mem[address + offset] = value
                // In our simplified 32-bit model, store the 32-bit value
                let _address = inputs[0].clone();
                let value = inputs[1].clone();
                let _offset_bv = BV::from_u64(self.ctx, *offset as u64, 32);

                // Store returns no value in WASM, but we return the stored value for verification
                value
            }

            // ========================================================================
            // f32 Operations (Phase 2 - Floating Point)
            // ========================================================================
            // Note: f32 values represented as 32-bit bitvectors (IEEE 754 format)

            WasmOp::F32Const(value) => {
                // f32 constant value
                // Convert f32 to IEEE 754 bit representation
                let bits = value.to_bits() as i64;
                BV::from_i64(self.ctx, bits, 32)
            }

            WasmOp::F32Add => {
                assert_eq!(inputs.len(), 2, "F32Add requires 2 inputs");
                // f32 addition (symbolic for verification)
                BV::new_const(self.ctx, "f32_add_result", 32)
            }

            WasmOp::F32Sub => {
                assert_eq!(inputs.len(), 2, "F32Sub requires 2 inputs");
                // f32 subtraction (symbolic for verification)
                BV::new_const(self.ctx, "f32_sub_result", 32)
            }

            WasmOp::F32Mul => {
                assert_eq!(inputs.len(), 2, "F32Mul requires 2 inputs");
                // f32 multiplication (symbolic for verification)
                BV::new_const(self.ctx, "f32_mul_result", 32)
            }

            WasmOp::F32Div => {
                assert_eq!(inputs.len(), 2, "F32Div requires 2 inputs");
                // f32 division (symbolic for verification)
                BV::new_const(self.ctx, "f32_div_result", 32)
            }

            WasmOp::F32Abs => {
                assert_eq!(inputs.len(), 1, "F32Abs requires 1 input");
                // f32 absolute value: clear sign bit
                let val = inputs[0].clone();
                let mask = BV::from_u64(self.ctx, 0x7FFFFFFF, 32);
                val.bvand(&mask)
            }

            WasmOp::F32Neg => {
                assert_eq!(inputs.len(), 1, "F32Neg requires 1 input");
                // f32 negation: flip sign bit
                let val = inputs[0].clone();
                let mask = BV::from_u64(self.ctx, 0x80000000, 32);
                val.bvxor(&mask)
            }

            WasmOp::F32Sqrt => {
                assert_eq!(inputs.len(), 1, "F32Sqrt requires 1 input");
                // f32 square root (symbolic for verification)
                BV::new_const(self.ctx, "f32_sqrt_result", 32)
            }

            WasmOp::F32Min => {
                assert_eq!(inputs.len(), 2, "F32Min requires 2 inputs");
                // f32 minimum with IEEE 754 semantics
                BV::new_const(self.ctx, "f32_min_result", 32)
            }

            WasmOp::F32Max => {
                assert_eq!(inputs.len(), 2, "F32Max requires 2 inputs");
                // f32 maximum with IEEE 754 semantics
                BV::new_const(self.ctx, "f32_max_result", 32)
            }

            WasmOp::F32Copysign => {
                assert_eq!(inputs.len(), 2, "F32Copysign requires 2 inputs");
                // f32 copysign: |input[0]| with sign of input[1]
                let val_n = inputs[0].clone();
                let val_m = inputs[1].clone();

                // Extract magnitude from first input
                let mag_mask = BV::from_u64(self.ctx, 0x7FFFFFFF, 32);
                let magnitude = val_n.bvand(&mag_mask);

                // Extract sign from second input
                let sign_mask = BV::from_u64(self.ctx, 0x80000000, 32);
                let sign = val_m.bvand(&sign_mask);

                // Combine magnitude and sign
                magnitude.bvor(&sign)
            }

            WasmOp::F32Load { offset: _, align: _ } => {
                assert_eq!(inputs.len(), 1, "F32Load requires 1 input (address)");
                // f32 load from memory (symbolic)
                BV::new_const(self.ctx, "f32_load_result", 32)
            }

            // Not yet supported operations
            _ => {
                // For unsupported operations, return a symbolic constant
                // This allows partial verification of supported operations
                BV::new_const(self.ctx, format!("unsupported_{:?}", op), 32)
            }
        }
    }

    /// Convert boolean to 32-bit bitvector (0 or 1)
    fn bool_to_bv32(&self, b: &Bool<'ctx>) -> BV<'ctx> {
        let zero = BV::from_i64(self.ctx, 0, 32);
        let one = BV::from_i64(self.ctx, 1, 32);
        b.ite(&one, &zero)
    }

    /// Encode count leading zeros (CLZ)
    ///
    /// Implements full binary search algorithm for counting leading zeros.
    /// This provides precise semantics that can be verified against ARM's CLZ instruction.
    ///
    /// Algorithm: Binary search through bit positions
    /// - Check top 16 bits, then 8, 4, 2, 1
    /// - O(log n) complexity for n-bit integers
    fn encode_clz(&self, input: &BV<'ctx>) -> BV<'ctx> {
        let zero = BV::from_i64(self.ctx, 0, 32);

        // Special case: if input is 0, return 32
        let all_zero = input._eq(&zero);
        let result_if_zero = BV::from_i64(self.ctx, 32, 32);

        // Binary search approach
        let mut count = BV::from_i64(self.ctx, 0, 32);
        let mut remaining = input.clone();

        // Check top 16 bits
        let mask_16 = BV::from_u64(self.ctx, 0xFFFF0000, 32);
        let top_16 = remaining.bvand(&mask_16);
        let top_16_zero = top_16._eq(&zero);

        // If top 16 are zero, add 16 to count and shift focus to bottom 16
        count = top_16_zero.ite(
            &count.bvadd(&BV::from_i64(self.ctx, 16, 32)),
            &count
        );
        remaining = top_16_zero.ite(
            &remaining.bvshl(&BV::from_i64(self.ctx, 16, 32)),
            &remaining
        );

        // Check top 8 bits (of the 16 we're examining)
        let mask_8 = BV::from_u64(self.ctx, 0xFF000000, 32);
        let top_8 = remaining.bvand(&mask_8);
        let top_8_zero = top_8._eq(&zero);

        count = top_8_zero.ite(
            &count.bvadd(&BV::from_i64(self.ctx, 8, 32)),
            &count
        );
        remaining = top_8_zero.ite(
            &remaining.bvshl(&BV::from_i64(self.ctx, 8, 32)),
            &remaining
        );

        // Check top 4 bits
        let mask_4 = BV::from_u64(self.ctx, 0xF0000000, 32);
        let top_4 = remaining.bvand(&mask_4);
        let top_4_zero = top_4._eq(&zero);

        count = top_4_zero.ite(
            &count.bvadd(&BV::from_i64(self.ctx, 4, 32)),
            &count
        );
        remaining = top_4_zero.ite(
            &remaining.bvshl(&BV::from_i64(self.ctx, 4, 32)),
            &remaining
        );

        // Check top 2 bits
        let mask_2 = BV::from_u64(self.ctx, 0xC0000000, 32);
        let top_2 = remaining.bvand(&mask_2);
        let top_2_zero = top_2._eq(&zero);

        count = top_2_zero.ite(
            &count.bvadd(&BV::from_i64(self.ctx, 2, 32)),
            &count
        );
        remaining = top_2_zero.ite(
            &remaining.bvshl(&BV::from_i64(self.ctx, 2, 32)),
            &remaining
        );

        // Check top bit
        let mask_1 = BV::from_u64(self.ctx, 0x80000000, 32);
        let top_1 = remaining.bvand(&mask_1);
        let top_1_zero = top_1._eq(&zero);

        count = top_1_zero.ite(
            &count.bvadd(&BV::from_i64(self.ctx, 1, 32)),
            &count
        );

        // Return 32 if all zeros, otherwise return count
        all_zero.ite(&result_if_zero, &count)
    }

    /// Encode count trailing zeros (CTZ)
    ///
    /// Implements binary search from the low end.
    /// CTZ counts zeros from the least significant bit up.
    fn encode_ctz(&self, input: &BV<'ctx>) -> BV<'ctx> {
        let zero = BV::from_i64(self.ctx, 0, 32);

        // Special case: if input is 0, return 32
        let all_zero = input._eq(&zero);
        let result_if_zero = BV::from_i64(self.ctx, 32, 32);

        // Binary search approach from low end
        let mut count = BV::from_i64(self.ctx, 0, 32);
        let mut remaining = input.clone();

        // Check bottom 16 bits
        let mask_16 = BV::from_u64(self.ctx, 0x0000FFFF, 32);
        let bottom_16 = remaining.bvand(&mask_16);
        let bottom_16_zero = bottom_16._eq(&zero);

        count = bottom_16_zero.ite(
            &count.bvadd(&BV::from_i64(self.ctx, 16, 32)),
            &count
        );
        remaining = bottom_16_zero.ite(
            &remaining.bvlshr(&BV::from_i64(self.ctx, 16, 32)),
            &remaining
        );

        // Check bottom 8 bits
        let mask_8 = BV::from_u64(self.ctx, 0x000000FF, 32);
        let bottom_8 = remaining.bvand(&mask_8);
        let bottom_8_zero = bottom_8._eq(&zero);

        count = bottom_8_zero.ite(
            &count.bvadd(&BV::from_i64(self.ctx, 8, 32)),
            &count
        );
        remaining = bottom_8_zero.ite(
            &remaining.bvlshr(&BV::from_i64(self.ctx, 8, 32)),
            &remaining
        );

        // Check bottom 4 bits
        let mask_4 = BV::from_u64(self.ctx, 0x0000000F, 32);
        let bottom_4 = remaining.bvand(&mask_4);
        let bottom_4_zero = bottom_4._eq(&zero);

        count = bottom_4_zero.ite(
            &count.bvadd(&BV::from_i64(self.ctx, 4, 32)),
            &count
        );
        remaining = bottom_4_zero.ite(
            &remaining.bvlshr(&BV::from_i64(self.ctx, 4, 32)),
            &remaining
        );

        // Check bottom 2 bits
        let mask_2 = BV::from_u64(self.ctx, 0x00000003, 32);
        let bottom_2 = remaining.bvand(&mask_2);
        let bottom_2_zero = bottom_2._eq(&zero);

        count = bottom_2_zero.ite(
            &count.bvadd(&BV::from_i64(self.ctx, 2, 32)),
            &count
        );
        remaining = bottom_2_zero.ite(
            &remaining.bvlshr(&BV::from_i64(self.ctx, 2, 32)),
            &remaining
        );

        // Check bottom bit
        let mask_1 = BV::from_u64(self.ctx, 0x00000001, 32);
        let bottom_1 = remaining.bvand(&mask_1);
        let bottom_1_zero = bottom_1._eq(&zero);

        count = bottom_1_zero.ite(
            &count.bvadd(&BV::from_i64(self.ctx, 1, 32)),
            &count
        );

        // Return 32 if all zeros, otherwise return count
        all_zero.ite(&result_if_zero, &count)
    }

    /// Encode population count (count number of 1 bits)
    ///
    /// Uses the Hamming weight algorithm (parallel bit counting).
    /// This is efficient for SMT solving compared to bit-by-bit iteration.
    ///
    /// Algorithm:
    /// 1. Count bits in pairs: each 2-bit group contains count of its 1 bits
    /// 2. Count pairs in nibbles: each 4-bit group contains count
    /// 3. Count nibbles in bytes: each 8-bit group contains count
    /// 4. Sum all bytes to get final count
    fn encode_popcnt(&self, input: &BV<'ctx>) -> BV<'ctx> {
        let mut x = input.clone();

        // Step 1: Count bits in pairs
        // x = (x & 0x55555555) + ((x >> 1) & 0x55555555)
        // Pattern: 01010101... (alternating bits)
        let mask1 = BV::from_u64(self.ctx, 0x55555555, 32);
        let masked = x.bvand(&mask1);
        let shifted = x.bvlshr(&BV::from_i64(self.ctx, 1, 32));
        let shifted_masked = shifted.bvand(&mask1);
        x = masked.bvadd(&shifted_masked);

        // Step 2: Count pairs in nibbles
        // x = (x & 0x33333333) + ((x >> 2) & 0x33333333)
        // Pattern: 00110011... (pairs of bits)
        let mask2 = BV::from_u64(self.ctx, 0x33333333, 32);
        let masked = x.bvand(&mask2);
        let shifted = x.bvlshr(&BV::from_i64(self.ctx, 2, 32));
        let shifted_masked = shifted.bvand(&mask2);
        x = masked.bvadd(&shifted_masked);

        // Step 3: Count nibbles in bytes
        // x = (x & 0x0F0F0F0F) + ((x >> 4) & 0x0F0F0F0F)
        // Pattern: 00001111... (nibbles)
        let mask3 = BV::from_u64(self.ctx, 0x0F0F0F0F, 32);
        let masked = x.bvand(&mask3);
        let shifted = x.bvlshr(&BV::from_i64(self.ctx, 4, 32));
        let shifted_masked = shifted.bvand(&mask3);
        x = masked.bvadd(&shifted_masked);

        // Step 4: Sum all bytes
        // x = (x * 0x01010101) >> 24
        // Multiply effectively sums all bytes, then we extract top byte
        let multiplier = BV::from_u64(self.ctx, 0x01010101, 32);
        x = x.bvmul(&multiplier);
        x = x.bvlshr(&BV::from_i64(self.ctx, 24, 32));

        x
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::create_z3_context;

    #[test]
    fn test_wasm_add_encoding() {
        let ctx = create_z3_context();
        let encoder = WasmSemantics::new(&ctx);

        let a = BV::new_const(&ctx, "a", 32);
        let b = BV::new_const(&ctx, "b", 32);
        let result = encoder.encode_op(&WasmOp::I32Add, &[a, b]);

        // Result should be a + b
        assert!(result.to_string().contains("bvadd"));
    }

    #[test]
    fn test_wasm_sub_encoding() {
        let ctx = create_z3_context();
        let encoder = WasmSemantics::new(&ctx);

        let a = BV::new_const(&ctx, "a", 32);
        let b = BV::new_const(&ctx, "b", 32);
        let result = encoder.encode_op(&WasmOp::I32Sub, &[a, b]);

        assert!(result.to_string().contains("bvsub"));
    }

    #[test]
    fn test_wasm_const_encoding() {
        let ctx = create_z3_context();
        let encoder = WasmSemantics::new(&ctx);

        let result = encoder.encode_op(&WasmOp::I32Const(42), &[]);

        // Should be the constant 42
        assert_eq!(result.as_i64(), Some(42));
    }

    #[test]
    fn test_wasm_comparison() {
        let ctx = create_z3_context();
        let encoder = WasmSemantics::new(&ctx);

        let a = BV::from_i64(&ctx, 5, 32);
        let b = BV::from_i64(&ctx, 10, 32);

        let result = encoder.encode_op(&WasmOp::I32LtS, &[a, b]);

        // 5 < 10 should be true (1)
        assert_eq!(result.as_i64(), Some(1));
    }

    #[test]
    fn test_wasm_bitwise_ops() {
        let ctx = create_z3_context();
        let encoder = WasmSemantics::new(&ctx);

        let a = BV::from_i64(&ctx, 0b1010, 32);
        let b = BV::from_i64(&ctx, 0b1100, 32);

        // Test AND
        let and_result = encoder.encode_op(&WasmOp::I32And, &[a.clone(), b.clone()]);
        assert_eq!(and_result.as_i64(), Some(0b1000));

        // Test OR
        let or_result = encoder.encode_op(&WasmOp::I32Or, &[a.clone(), b.clone()]);
        assert_eq!(or_result.as_i64(), Some(0b1110));

        // Test XOR
        let xor_result = encoder.encode_op(&WasmOp::I32Xor, &[a, b]);
        assert_eq!(xor_result.as_i64(), Some(0b0110));
    }

    #[test]
    fn test_wasm_shift_ops() {
        let ctx = create_z3_context();
        let encoder = WasmSemantics::new(&ctx);

        let value = BV::from_i64(&ctx, 8, 32);
        let shift = BV::from_i64(&ctx, 2, 32);

        // Test left shift: 8 << 2 = 32
        let shl_result = encoder.encode_op(&WasmOp::I32Shl, &[value.clone(), shift.clone()]);
        assert_eq!(shl_result.as_i64(), Some(32));

        // Test logical right shift: 8 >> 2 = 2
        let shr_result = encoder.encode_op(&WasmOp::I32ShrU, &[value, shift]);
        assert_eq!(shr_result.as_i64(), Some(2));
    }

    #[test]
    fn test_wasm_shift_modulo() {
        let ctx = create_z3_context();
        let encoder = WasmSemantics::new(&ctx);

        let value = BV::from_i64(&ctx, 0xFF, 32);
        // Shift by 33 should be same as shift by 1 (modulo 32)
        let shift = BV::from_i64(&ctx, 33, 32);

        let shl_result = encoder.encode_op(&WasmOp::I32Shl, &[value.clone(), shift.clone()]);
        // 0xFF << 33 = 0xFF << 1 = 0x1FE
        assert_eq!(shl_result.as_i64(), Some(0x1FE));
    }

    #[test]
    fn test_wasm_rem_ops() {
        let ctx = create_z3_context();
        let encoder = WasmSemantics::new(&ctx);

        let a = BV::from_i64(&ctx, 17, 32);
        let b = BV::from_i64(&ctx, 5, 32);

        // Test signed remainder: 17 % 5 = 2
        let rem_s = encoder.encode_op(&WasmOp::I32RemS, &[a.clone(), b.clone()]);
        assert_eq!(rem_s.as_i64(), Some(2));

        // Test unsigned remainder
        let rem_u = encoder.encode_op(&WasmOp::I32RemU, &[a, b]);
        assert_eq!(rem_u.as_i64(), Some(2));
    }

    #[test]
    fn test_wasm_rotation_ops() {
        let ctx = create_z3_context();
        let encoder = WasmSemantics::new(&ctx);

        let value = BV::from_i64(&ctx, 0x12345678, 32);
        let rotate = BV::from_i64(&ctx, 8, 32);

        // Test rotate right
        let rotr_result = encoder.encode_op(&WasmOp::I32Rotr, &[value.clone(), rotate.clone()]);
        assert_eq!(rotr_result.as_i64(), Some(0x78123456));

        // Test rotate left
        let rotl_result = encoder.encode_op(&WasmOp::I32Rotl, &[value, rotate]);
        assert_eq!(rotl_result.as_i64(), Some(0x34567812));
    }

    #[test]
    fn test_wasm_clz_comprehensive() {
        let ctx = create_z3_context();
        let encoder = WasmSemantics::new(&ctx);

        // Test CLZ(0) = 32
        let zero = BV::from_i64(&ctx, 0, 32);
        let clz_zero = encoder.encode_op(&WasmOp::I32Clz, &[zero]);
        assert_eq!(clz_zero.as_i64(), Some(32), "CLZ(0) should be 32");

        // Test CLZ(1) = 31 (binary: 0000...0001)
        let one = BV::from_i64(&ctx, 1, 32);
        let clz_one = encoder.encode_op(&WasmOp::I32Clz, &[one]);
        assert_eq!(clz_one.as_i64(), Some(31), "CLZ(1) should be 31");

        // Test CLZ(0x80000000) = 0 (binary: 1000...0000)
        let msb_set = BV::from_u64(&ctx, 0x80000000, 32);
        let clz_msb = encoder.encode_op(&WasmOp::I32Clz, &[msb_set]);
        assert_eq!(clz_msb.as_i64(), Some(0), "CLZ(0x80000000) should be 0");

        // Test CLZ(0x00FF0000) = 8
        let val1 = BV::from_u64(&ctx, 0x00FF0000, 32);
        let clz1 = encoder.encode_op(&WasmOp::I32Clz, &[val1]);
        assert_eq!(clz1.as_i64(), Some(8), "CLZ(0x00FF0000) should be 8");

        // Test CLZ(0x00001000) = 19
        let val2 = BV::from_u64(&ctx, 0x00001000, 32);
        let clz2 = encoder.encode_op(&WasmOp::I32Clz, &[val2]);
        assert_eq!(clz2.as_i64(), Some(19), "CLZ(0x00001000) should be 19");

        // Test CLZ(0xFFFFFFFF) = 0 (all bits set)
        let all_ones = BV::from_u64(&ctx, 0xFFFFFFFF, 32);
        let clz_all = encoder.encode_op(&WasmOp::I32Clz, &[all_ones]);
        assert_eq!(clz_all.as_i64(), Some(0), "CLZ(0xFFFFFFFF) should be 0");

        // Test CLZ(0x00000100) = 23
        let val3 = BV::from_u64(&ctx, 0x00000100, 32);
        let clz3 = encoder.encode_op(&WasmOp::I32Clz, &[val3]);
        assert_eq!(clz3.as_i64(), Some(23), "CLZ(0x00000100) should be 23");
    }

    #[test]
    fn test_wasm_ctz_comprehensive() {
        let ctx = create_z3_context();
        let encoder = WasmSemantics::new(&ctx);

        // Test CTZ(0) = 32
        let zero = BV::from_i64(&ctx, 0, 32);
        let ctz_zero = encoder.encode_op(&WasmOp::I32Ctz, &[zero]);
        assert_eq!(ctz_zero.as_i64(), Some(32), "CTZ(0) should be 32");

        // Test CTZ(1) = 0 (binary: ...0001)
        let one = BV::from_i64(&ctx, 1, 32);
        let ctz_one = encoder.encode_op(&WasmOp::I32Ctz, &[one]);
        assert_eq!(ctz_one.as_i64(), Some(0), "CTZ(1) should be 0");

        // Test CTZ(2) = 1 (binary: ...0010)
        let two = BV::from_i64(&ctx, 2, 32);
        let ctz_two = encoder.encode_op(&WasmOp::I32Ctz, &[two]);
        assert_eq!(ctz_two.as_i64(), Some(1), "CTZ(2) should be 1");

        // Test CTZ(0x80000000) = 31 (binary: 1000...0000)
        let msb_set = BV::from_u64(&ctx, 0x80000000, 32);
        let ctz_msb = encoder.encode_op(&WasmOp::I32Ctz, &[msb_set]);
        assert_eq!(ctz_msb.as_i64(), Some(31), "CTZ(0x80000000) should be 31");

        // Test CTZ(0x00FF0000) = 16
        let val1 = BV::from_u64(&ctx, 0x00FF0000, 32);
        let ctz1 = encoder.encode_op(&WasmOp::I32Ctz, &[val1]);
        assert_eq!(ctz1.as_i64(), Some(16), "CTZ(0x00FF0000) should be 16");

        // Test CTZ(0x00001000) = 12
        let val2 = BV::from_u64(&ctx, 0x00001000, 32);
        let ctz2 = encoder.encode_op(&WasmOp::I32Ctz, &[val2]);
        assert_eq!(ctz2.as_i64(), Some(12), "CTZ(0x00001000) should be 12");

        // Test CTZ(0xFFFFFFFF) = 0 (all bits set, lowest is bit 0)
        let all_ones = BV::from_u64(&ctx, 0xFFFFFFFF, 32);
        let ctz_all = encoder.encode_op(&WasmOp::I32Ctz, &[all_ones]);
        assert_eq!(ctz_all.as_i64(), Some(0), "CTZ(0xFFFFFFFF) should be 0");

        // Test CTZ(0x00000100) = 8
        let val3 = BV::from_u64(&ctx, 0x00000100, 32);
        let ctz3 = encoder.encode_op(&WasmOp::I32Ctz, &[val3]);
        assert_eq!(ctz3.as_i64(), Some(8), "CTZ(0x00000100) should be 8");

        // Test CTZ(12) = 2 (binary: ...1100, lowest 1 is at bit 2)
        let twelve = BV::from_i64(&ctx, 12, 32);
        let ctz_twelve = encoder.encode_op(&WasmOp::I32Ctz, &[twelve]);
        assert_eq!(ctz_twelve.as_i64(), Some(2), "CTZ(12) should be 2");
    }

    #[test]
    fn test_wasm_popcnt() {
        let ctx = create_z3_context();
        let encoder = WasmSemantics::new(&ctx);

        // Test POPCNT(0) = 0
        let zero = BV::from_i64(&ctx, 0, 32);
        let popcnt_zero = encoder.encode_op(&WasmOp::I32Popcnt, &[zero]);
        assert_eq!(popcnt_zero.as_i64(), Some(0), "POPCNT(0) should be 0");

        // Test POPCNT(1) = 1
        let one = BV::from_i64(&ctx, 1, 32);
        let popcnt_one = encoder.encode_op(&WasmOp::I32Popcnt, &[one]);
        assert_eq!(popcnt_one.as_i64(), Some(1), "POPCNT(1) should be 1");

        // Test POPCNT(0xFFFFFFFF) = 32
        let all_ones = BV::from_u64(&ctx, 0xFFFFFFFF, 32);
        let popcnt_all = encoder.encode_op(&WasmOp::I32Popcnt, &[all_ones]);
        assert_eq!(popcnt_all.as_i64(), Some(32), "POPCNT(0xFFFFFFFF) should be 32");

        // Test POPCNT(0x0F0F0F0F) = 16 (half the bits set)
        let half = BV::from_u64(&ctx, 0x0F0F0F0F, 32);
        let popcnt_half = encoder.encode_op(&WasmOp::I32Popcnt, &[half]);
        assert_eq!(popcnt_half.as_i64(), Some(16), "POPCNT(0x0F0F0F0F) should be 16");

        // Test POPCNT(7) = 3 (binary: 0111)
        let seven = BV::from_i64(&ctx, 7, 32);
        let popcnt_seven = encoder.encode_op(&WasmOp::I32Popcnt, &[seven]);
        assert_eq!(popcnt_seven.as_i64(), Some(3), "POPCNT(7) should be 3");

        // Test POPCNT(0xAAAAAAAA) = 16 (alternating bits)
        let alternating = BV::from_u64(&ctx, 0xAAAAAAAA, 32);
        let popcnt_alt = encoder.encode_op(&WasmOp::I32Popcnt, &[alternating]);
        assert_eq!(popcnt_alt.as_i64(), Some(16), "POPCNT(0xAAAAAAAA) should be 16");
    }

    #[test]
    fn test_wasm_select() {
        let ctx = create_z3_context();
        let encoder = WasmSemantics::new(&ctx);

        // Test select(10, 20, 1) = 10 (cond != 0, so select first value)
        let val1 = BV::from_i64(&ctx, 10, 32);
        let val2 = BV::from_i64(&ctx, 20, 32);
        let cond_true = BV::from_i64(&ctx, 1, 32);
        let result = encoder.encode_op(&WasmOp::Select, &[val1.clone(), val2.clone(), cond_true]);
        assert_eq!(result.as_i64(), Some(10), "select(10, 20, 1) should return 10");

        // Test select(10, 20, 0) = 20 (cond == 0, so select second value)
        let cond_false = BV::from_i64(&ctx, 0, 32);
        let result = encoder.encode_op(&WasmOp::Select, &[val1.clone(), val2.clone(), cond_false]);
        assert_eq!(result.as_i64(), Some(20), "select(10, 20, 0) should return 20");

        // Test select(42, 99, -1) = 42 (negative != 0, so select first value)
        let val3 = BV::from_i64(&ctx, 42, 32);
        let val4 = BV::from_i64(&ctx, 99, 32);
        let cond_neg = BV::from_i64(&ctx, -1, 32);
        let result = encoder.encode_op(&WasmOp::Select, &[val3, val4, cond_neg]);
        assert_eq!(result.as_i64(), Some(42), "select(42, 99, -1) should return 42");
    }
}
