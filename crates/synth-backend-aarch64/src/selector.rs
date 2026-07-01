//! Minimal AArch64 instruction selector — milestone-1 integer subset (#538).
//!
//! A straight-line stack-machine lowering for the leaf integer core: parameters
//! arrive in `w0..w7` (AAPCS64), values live in a small register value-stack, and
//! the function result is moved to `w0` before `ret`. Anything outside the subset
//! returns `Unsupported` — an honest loud-skip (the RISC-V-skeleton contract),
//! never silent wrong code. Spilling, i64, floats, calls, memory and control flow
//! are later milestones.

use crate::encoder as enc;
use crate::encoder::Reg;
use synth_core::WasmOp;

/// The value-stack temp registers: caller-saved `w9..w15` (8 slots). `w0..w7`
/// hold incoming params; results funnel back through `w0`.
const TEMPS: [Reg; 7] = [9, 10, 11, 12, 13, 14, 15];

#[derive(Debug)]
pub struct SelectError(pub String);

impl std::fmt::Display for SelectError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "aarch64 selector: {}", self.0)
    }
}

/// Lower a single function body (its wasm op stream + declared param count) to a
/// vector of A64 instruction words. `num_params` params are assumed resident in
/// `w0..w{num_params-1}` on entry (milestone-1 supports up to 8 i32 params).
pub fn select(ops: &[WasmOp], num_params: u32) -> Result<Vec<u32>, SelectError> {
    if num_params > 8 {
        return Err(SelectError(format!(
            "{num_params} params — milestone-1 supports at most 8 register params"
        )));
    }
    let mut words: Vec<u32> = Vec::new();
    let mut stack: Vec<Reg> = Vec::new();

    // Pick a temp register not currently holding a live value-stack entry.
    let alloc_temp = |stack: &[Reg]| -> Result<Reg, SelectError> {
        TEMPS
            .iter()
            .copied()
            .find(|t| !stack.contains(t))
            .ok_or_else(|| SelectError("value-stack too deep (temp regs exhausted)".into()))
    };

    let binop = |words: &mut Vec<u32>,
                 stack: &mut Vec<Reg>,
                 f: fn(Reg, Reg, Reg) -> u32|
     -> Result<(), SelectError> {
        let b = stack
            .pop()
            .ok_or_else(|| SelectError("binop underflow".into()))?;
        let a = stack
            .pop()
            .ok_or_else(|| SelectError("binop underflow".into()))?;
        let dst = alloc_temp(stack)?;
        words.push(f(dst, a, b));
        stack.push(dst);
        Ok(())
    };

    for op in ops {
        match op {
            WasmOp::LocalGet(i) => {
                if *i >= num_params {
                    return Err(SelectError(format!(
                        "local.get {i}: non-param locals not yet supported (milestone-1)"
                    )));
                }
                // params are in w0..w7
                stack.push(*i as Reg);
            }
            WasmOp::I32Const(c) => {
                let dst = alloc_temp(&stack)?;
                for w in enc::mov_imm32(dst, *c as u32) {
                    words.push(w);
                }
                stack.push(dst);
            }
            WasmOp::I32Add => binop(&mut words, &mut stack, enc::add)?,
            WasmOp::I32Sub => binop(&mut words, &mut stack, enc::sub)?,
            WasmOp::I32Mul => binop(&mut words, &mut stack, enc::mul)?,
            WasmOp::I32And => binop(&mut words, &mut stack, enc::and)?,
            WasmOp::I32Or => binop(&mut words, &mut stack, enc::orr)?,
            WasmOp::I32Xor => binop(&mut words, &mut stack, enc::eor)?,
            // End of the function body: move the result to w0 and return.
            WasmOp::End => {
                if let Some(top) = stack.last().copied()
                    && top != 0
                {
                    words.push(enc::mov_reg(0, top));
                }
                words.push(enc::ret());
            }
            other => {
                return Err(SelectError(format!(
                    "unsupported wasm op for aarch64 milestone-1: {other:?}"
                )));
            }
        }
    }

    // A body without a trailing `End` still needs an epilogue.
    if !matches!(ops.last(), Some(WasmOp::End)) {
        if let Some(top) = stack.last().copied()
            && top != 0
        {
            words.push(enc::mov_reg(0, top));
        }
        words.push(enc::ret());
    }
    Ok(words)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bytes(words: &[u32]) -> Vec<u8> {
        words.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    #[test]
    fn add_two_params() {
        // (param i32 i32) (result i32) local.get 0; local.get 1; i32.add
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let w = select(&ops, 2).unwrap();
        // add w9,w0,w1 ; mov w0,w9 ; ret
        assert_eq!(w, vec![enc::add(9, 0, 1), enc::mov_reg(0, 9), enc::ret()]);
        // sanity: three 32-bit instructions
        assert_eq!(bytes(&w).len(), 12);
    }

    #[test]
    fn const_add_uses_movz() {
        // (param i32)(result i32) local.get 0; i32.const 5; i32.add
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Const(5),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let w = select(&ops, 1).unwrap();
        // movz w9,#5 ; add w9,w0,w9 ; mov w0,w9 ; ret — the temp w9 is freed by
        // the pops before the result is allocated, so the selector reuses it
        // (clang-verified: 0x528000A9, 0x0B090009, 0x2A0903E0, 0xD65F03C0).
        assert_eq!(
            w,
            vec![
                enc::movz(9, 5),
                enc::add(9, 0, 9),
                enc::mov_reg(0, 9),
                enc::ret()
            ]
        );
    }

    #[test]
    fn result_already_in_w0_skips_mov() {
        // a single param returned directly: local.get 0
        let ops = vec![WasmOp::LocalGet(0), WasmOp::End];
        let w = select(&ops, 1).unwrap();
        assert_eq!(w, vec![enc::ret()]); // top is w0 already, no mov
    }

    #[test]
    fn unsupported_op_is_loud() {
        let ops = vec![WasmOp::LocalGet(0), WasmOp::I32DivU, WasmOp::End];
        assert!(select(&ops, 2).is_err());
    }
}
