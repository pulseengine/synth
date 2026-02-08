//! WASM Binary Decoder - Converts wasmparser operators to WasmOp sequences
//!
//! This module bridges the gap between parsed WASM binaries and any backend.
//! It extracts function bodies and converts wasmparser operators to our internal WasmOp format.

use crate::wasm_op::WasmOp;
use anyhow::{Context, Result};
use std::collections::HashMap;
use wasmparser::{ExternalKind, Parser, Payload};

/// WASM linear memory specification
#[derive(Debug, Clone)]
pub struct WasmMemory {
    /// Memory index
    pub index: u32,
    /// Initial size in pages (64KB each)
    pub initial_pages: u32,
    /// Maximum size in pages (if specified)
    pub max_pages: Option<u32>,
    /// Whether memory is shared (requires threads proposal)
    pub shared: bool,
}

impl WasmMemory {
    /// Get initial size in bytes
    pub fn initial_bytes(&self) -> u32 {
        self.initial_pages * 65536
    }

    /// Get maximum size in bytes (or initial if not specified)
    pub fn max_bytes(&self) -> u32 {
        self.max_pages.unwrap_or(self.initial_pages) * 65536
    }
}

/// Decoded WASM module with functions and memory
#[derive(Debug, Clone)]
pub struct DecodedModule {
    /// Decoded functions
    pub functions: Vec<FunctionOps>,
    /// Linear memories
    pub memories: Vec<WasmMemory>,
    /// Data segments (offset, data) for memory initialization
    pub data_segments: Vec<(u32, Vec<u8>)>,
}

/// Decode a WASM binary and extract functions, memory, and data segments
pub fn decode_wasm_module(wasm_bytes: &[u8]) -> Result<DecodedModule> {
    let mut functions = Vec::new();
    let mut memories = Vec::new();
    let mut data_segments = Vec::new();
    let mut func_index = 0u32;
    let mut num_imported_funcs = 0u32;
    let mut export_names: HashMap<u32, String> = HashMap::new();

    for payload in Parser::new(0).parse_all(wasm_bytes) {
        let payload = payload.context("Failed to parse WASM payload")?;

        match payload {
            Payload::ImportSection(imports) => {
                for import in imports {
                    let import = import.context("Failed to parse import")?;
                    if matches!(import.ty, wasmparser::TypeRef::Func(_)) {
                        num_imported_funcs += 1;
                    }
                }
            }
            Payload::MemorySection(reader) => {
                for (idx, memory) in reader.into_iter().enumerate() {
                    let mem = memory.context("Failed to parse memory")?;
                    memories.push(WasmMemory {
                        index: idx as u32,
                        initial_pages: mem.initial as u32,
                        max_pages: mem.maximum.map(|m| m as u32),
                        shared: mem.shared,
                    });
                }
            }
            Payload::DataSection(reader) => {
                for data in reader {
                    let data = data.context("Failed to parse data segment")?;
                    if let wasmparser::DataKind::Active {
                        memory_index: 0,
                        offset_expr,
                    } = data.kind
                    {
                        let mut ops = offset_expr.get_operators_reader();
                        if let Ok(wasmparser::Operator::I32Const { value }) = ops.read() {
                            data_segments.push((value as u32, data.data.to_vec()));
                        }
                    }
                }
            }
            Payload::ExportSection(exports) => {
                for export in exports {
                    let export = export.context("Failed to parse export")?;
                    if export.kind == ExternalKind::Func {
                        export_names.insert(export.index, export.name.to_string());
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                let ops = decode_function_body(&body)?;
                let actual_index = num_imported_funcs + func_index;
                let export_name = export_names.get(&actual_index).cloned();

                functions.push(FunctionOps {
                    index: actual_index,
                    export_name,
                    ops,
                });
                func_index += 1;
            }
            _ => {}
        }
    }

    Ok(DecodedModule {
        functions,
        memories,
        data_segments,
    })
}

/// Decode a WASM binary and extract all function bodies as WasmOp sequences
pub fn decode_wasm_functions(wasm_bytes: &[u8]) -> Result<Vec<FunctionOps>> {
    let mut functions = Vec::new();
    let mut func_index = 0u32;
    let mut num_imported_funcs = 0u32;
    let mut export_names: HashMap<u32, String> = HashMap::new();

    for payload in Parser::new(0).parse_all(wasm_bytes) {
        let payload = payload.context("Failed to parse WASM payload")?;

        match payload {
            Payload::ImportSection(imports) => {
                for import in imports {
                    let import = import.context("Failed to parse import")?;
                    if matches!(import.ty, wasmparser::TypeRef::Func(_)) {
                        num_imported_funcs += 1;
                    }
                }
            }
            Payload::ExportSection(exports) => {
                for export in exports {
                    let export = export.context("Failed to parse export")?;
                    if export.kind == ExternalKind::Func {
                        export_names.insert(export.index, export.name.to_string());
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                let ops = decode_function_body(&body)?;
                let actual_index = num_imported_funcs + func_index;
                let export_name = export_names.get(&actual_index).cloned();

                functions.push(FunctionOps {
                    index: actual_index,
                    export_name,
                    ops,
                });
                func_index += 1;
            }
            _ => {}
        }
    }

    Ok(functions)
}

/// Decoded function with its WasmOp sequence
#[derive(Debug, Clone)]
pub struct FunctionOps {
    /// Function index in the module (includes imported functions)
    pub index: u32,
    /// Export name if this function is exported
    pub export_name: Option<String>,
    /// The WASM operations in this function body
    pub ops: Vec<WasmOp>,
}

/// Decode a single function body to WasmOp sequence
fn decode_function_body(body: &wasmparser::FunctionBody) -> Result<Vec<WasmOp>> {
    let mut ops = Vec::new();

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

        // i32 Arithmetic
        I32Add => Some(WasmOp::I32Add),
        I32Sub => Some(WasmOp::I32Sub),
        I32Mul => Some(WasmOp::I32Mul),
        I32DivS => Some(WasmOp::I32DivS),
        I32DivU => Some(WasmOp::I32DivU),
        I32RemS => Some(WasmOp::I32RemS),
        I32RemU => Some(WasmOp::I32RemU),

        // i64 Constants
        I64Const { value } => Some(WasmOp::I64Const(*value)),

        // i64 Arithmetic
        I64Add => Some(WasmOp::I64Add),
        I64Sub => Some(WasmOp::I64Sub),
        I64Mul => Some(WasmOp::I64Mul),
        I64DivS => Some(WasmOp::I64DivS),
        I64DivU => Some(WasmOp::I64DivU),
        I64RemS => Some(WasmOp::I64RemS),
        I64RemU => Some(WasmOp::I64RemU),

        // i64 Bitwise
        I64And => Some(WasmOp::I64And),
        I64Or => Some(WasmOp::I64Or),
        I64Xor => Some(WasmOp::I64Xor),
        I64Shl => Some(WasmOp::I64Shl),
        I64ShrS => Some(WasmOp::I64ShrS),
        I64ShrU => Some(WasmOp::I64ShrU),
        I64Rotl => Some(WasmOp::I64Rotl),
        I64Rotr => Some(WasmOp::I64Rotr),
        I64Clz => Some(WasmOp::I64Clz),
        I64Ctz => Some(WasmOp::I64Ctz),
        I64Popcnt => Some(WasmOp::I64Popcnt),
        I64Extend8S => Some(WasmOp::I64Extend8S),
        I64Extend16S => Some(WasmOp::I64Extend16S),
        I64Extend32S => Some(WasmOp::I64Extend32S),

        // i64 Comparison
        I64Eqz => Some(WasmOp::I64Eqz),
        I64Eq => Some(WasmOp::I64Eq),
        I64Ne => Some(WasmOp::I64Ne),
        I64LtS => Some(WasmOp::I64LtS),
        I64LtU => Some(WasmOp::I64LtU),
        I64LeS => Some(WasmOp::I64LeS),
        I64LeU => Some(WasmOp::I64LeU),
        I64GtS => Some(WasmOp::I64GtS),
        I64GtU => Some(WasmOp::I64GtU),
        I64GeS => Some(WasmOp::I64GeS),
        I64GeU => Some(WasmOp::I64GeU),

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
        I32Extend8S => Some(WasmOp::I32Extend8S),
        I32Extend16S => Some(WasmOp::I32Extend16S),

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
        CallIndirect {
            type_index,
            table_index,
            ..
        } => Some(WasmOp::CallIndirect {
            type_index: *type_index,
            table_index: *table_index,
        }),

        // End is needed for control flow pattern matching
        End => Some(WasmOp::End),

        // Nop/Unreachable - skip these
        Nop | Unreachable => None,

        // Drop is needed for br_if pattern matching
        Drop => Some(WasmOp::Drop),

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
        assert_eq!(functions[0].export_name, Some("add".to_string()));
        assert_eq!(
            functions[0].ops,
            vec![
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32Add,
                WasmOp::End
            ]
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
        assert_eq!(functions[0].export_name, Some("calc".to_string()));
        assert_eq!(
            functions[0].ops,
            vec![
                WasmOp::I32Const(5),
                WasmOp::I32Const(3),
                WasmOp::I32Mul,
                WasmOp::I32Const(2),
                WasmOp::I32Add,
                WasmOp::End,
            ]
        );
    }

    #[test]
    fn test_decode_multi_function_module() {
        let wat = r#"
            (module
                (func $helper)
                (func (export "add") (param i32 i32) (result i32)
                    local.get 0
                    local.get 1
                    i32.add
                )
                (func (export "sub") (param i32 i32) (result i32)
                    local.get 0
                    local.get 1
                    i32.sub
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 3);
        assert_eq!(functions[0].index, 0);
        assert_eq!(functions[0].export_name, None);
        assert_eq!(functions[1].index, 1);
        assert_eq!(functions[1].export_name, Some("add".to_string()));
        assert_eq!(functions[2].index, 2);
        assert_eq!(functions[2].export_name, Some("sub".to_string()));
    }

    #[test]
    fn test_find_function_by_export_name() {
        let wat = r#"
            (module
                (func $helper)
                (func (export "add") (param i32 i32) (result i32)
                    local.get 0
                    local.get 1
                    i32.add
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        let add_func = functions
            .iter()
            .find(|f| f.export_name.as_deref() == Some("add"))
            .expect("Should find 'add' function");

        assert_eq!(add_func.index, 1);
        assert!(add_func.ops.contains(&WasmOp::I32Add));
    }
}
