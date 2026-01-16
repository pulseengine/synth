//! WASM Binary Decoder - Converts wasmparser operators to WasmOp sequences
//!
//! This module bridges the gap between parsed WASM binaries and the synthesis pipeline.
//! It extracts function bodies and converts wasmparser operators to our internal WasmOp format.

use crate::rules::WasmOp;
use anyhow::{Context, Result};
use wasmparser::{Parser, Payload};

/// Decode a WASM binary and extract all function bodies as WasmOp sequences
pub fn decode_wasm_functions(wasm_bytes: &[u8]) -> Result<Vec<FunctionOps>> {
    let mut functions = Vec::new();
    let mut func_index = 0u32;

    for payload in Parser::new(0).parse_all(wasm_bytes) {
        let payload = payload.context("Failed to parse WASM payload")?;

        if let Payload::CodeSectionEntry(body) = payload {
            let ops = decode_function_body(&body)?;
            functions.push(FunctionOps {
                index: func_index,
                ops,
            });
            func_index += 1;
        }
    }

    Ok(functions)
}

/// Decoded function with its WasmOp sequence
#[derive(Debug, Clone)]
pub struct FunctionOps {
    pub index: u32,
    pub ops: Vec<WasmOp>,
}

/// Decode a single function body to WasmOp sequence
fn decode_function_body(body: &wasmparser::FunctionBody) -> Result<Vec<WasmOp>> {
    let mut ops = Vec::new();

    // Parse operators from the function body
    let ops_reader = body.get_operators_reader()?;
    for op_result in ops_reader {
        let op = op_result.context("Failed to read operator")?;

        if let Some(wasm_op) = convert_operator(&op) {
            ops.push(wasm_op);
        }
    }

    Ok(ops)
}

/// Convert a wasmparser Operator to our WasmOp enum
fn convert_operator(op: &wasmparser::Operator) -> Option<WasmOp> {
    use wasmparser::Operator::*;

    match op {
        // Constants
        I32Const { value } => Some(WasmOp::I32Const(*value)),

        // Arithmetic
        I32Add => Some(WasmOp::I32Add),
        I32Sub => Some(WasmOp::I32Sub),
        I32Mul => Some(WasmOp::I32Mul),
        I32DivS => Some(WasmOp::I32DivS),
        I32DivU => Some(WasmOp::I32DivU),
        I32RemS => Some(WasmOp::I32RemS),
        I32RemU => Some(WasmOp::I32RemU),

        // Bitwise
        I32And => Some(WasmOp::I32And),
        I32Or => Some(WasmOp::I32Or),
        I32Xor => Some(WasmOp::I32Xor),
        I32Shl => Some(WasmOp::I32Shl),
        I32ShrS => Some(WasmOp::I32ShrS),
        I32ShrU => Some(WasmOp::I32ShrU),
        I32Rotl => Some(WasmOp::I32Rotl),
        I32Rotr => Some(WasmOp::I32Rotr),
        I32Clz => Some(WasmOp::I32Clz),
        I32Ctz => Some(WasmOp::I32Ctz),
        I32Popcnt => Some(WasmOp::I32Popcnt),

        // Comparison
        I32Eqz => Some(WasmOp::I32Eqz),
        I32Eq => Some(WasmOp::I32Eq),
        I32Ne => Some(WasmOp::I32Ne),
        I32LtS => Some(WasmOp::I32LtS),
        I32LtU => Some(WasmOp::I32LtU),
        I32LeS => Some(WasmOp::I32LeS),
        I32LeU => Some(WasmOp::I32LeU),
        I32GtS => Some(WasmOp::I32GtS),
        I32GtU => Some(WasmOp::I32GtU),
        I32GeS => Some(WasmOp::I32GeS),
        I32GeU => Some(WasmOp::I32GeU),

        // Memory
        I32Load { memarg } => Some(WasmOp::I32Load {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I32Store { memarg } => Some(WasmOp::I32Store {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),

        // Local/Global
        LocalGet { local_index } => Some(WasmOp::LocalGet(*local_index)),
        LocalSet { local_index } => Some(WasmOp::LocalSet(*local_index)),
        LocalTee { local_index } => Some(WasmOp::LocalTee(*local_index)),
        GlobalGet { global_index } => Some(WasmOp::GlobalGet(*global_index)),
        GlobalSet { global_index } => Some(WasmOp::GlobalSet(*global_index)),

        // Control flow
        Block { .. } => Some(WasmOp::Block),
        Loop { .. } => Some(WasmOp::Loop),
        Br { relative_depth } => Some(WasmOp::Br(*relative_depth)),
        BrIf { relative_depth } => Some(WasmOp::BrIf(*relative_depth)),
        Return => Some(WasmOp::Return),
        Call { function_index } => Some(WasmOp::Call(*function_index)),

        // End/Nop/Drop/etc - skip for now
        End | Nop | Drop | Unreachable => None,

        // Select
        Select => Some(WasmOp::Select),

        // If/Else - simplified handling
        If { .. } => Some(WasmOp::If),
        Else => Some(WasmOp::Else),

        // Other operators not yet supported
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decode_simple_add() {
        // Simple add function: (func (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
        let wat = r#"
            (module
                (func (export "add") (param i32 i32) (result i32)
                    local.get 0
                    local.get 1
                    i32.add
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert_eq!(functions[0].index, 0);
        assert_eq!(
            functions[0].ops,
            vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::I32Add]
        );
    }

    #[test]
    fn test_decode_arithmetic() {
        let wat = r#"
            (module
                (func (export "calc") (result i32)
                    i32.const 5
                    i32.const 3
                    i32.mul
                    i32.const 2
                    i32.add
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert_eq!(
            functions[0].ops,
            vec![
                WasmOp::I32Const(5),
                WasmOp::I32Const(3),
                WasmOp::I32Mul,
                WasmOp::I32Const(2),
                WasmOp::I32Add,
            ]
        );
    }
}
