//! WASM Binary Decoder - Converts wasmparser operators to WasmOp sequences
//!
//! This module bridges the gap between parsed WASM binaries and any backend.
//! It extracts function bodies and converts wasmparser operators to our internal WasmOp format.

use crate::wasm_op::WasmOp;
use anyhow::{Context, Result};
use std::collections::HashMap;
use wasmparser::{ExternalKind, Parser, Payload};

/// Kind of a WASM import
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportKind {
    /// Imported function with type index
    Function(u32),
    /// Imported memory
    Memory,
    /// Imported table
    Table,
    /// Imported global
    Global,
}

/// A WASM import entry with full metadata
#[derive(Debug, Clone)]
pub struct ImportEntry {
    /// Module name (e.g., "wasi:cli/stdout" or "env")
    pub module: String,
    /// Field name (e.g., "write" or "memory")
    pub name: String,
    /// Import kind and associated data
    pub kind: ImportKind,
    /// Index of this import within its kind (e.g., function import index)
    pub index: u32,
}

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

/// A WASM global's declaration — its initial value and mutability (#237).
/// Needed so the native-pointer ABI can recognize a global whose initializer is
/// a linear-memory address (e.g. `$__stack_pointer = 65536`) and make it
/// `__synth_wasm_data`-relative, rather than reading it from an R9 globals table
/// the self-contained drop-in object can't rely on.
#[derive(Debug, Clone)]
pub struct WasmGlobal {
    /// Global index (defined globals; imported globals are not counted here).
    pub index: u32,
    /// The `i32.const` initializer value (other init exprs decode to `None`).
    pub init_i32: Option<i32>,
    /// Whether the global is mutable.
    pub mutable: bool,
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
    /// Import entries (module name, field name, kind)
    pub imports: Vec<ImportEntry>,
    /// Number of imported functions (for distinguishing import calls from local calls)
    pub num_imported_funcs: u32,
    /// AAPCS integer-argument count per function, indexed by the *full* WASM
    /// function index (imported functions first, then locally-defined ones).
    /// Used by the backend to marshal call arguments into R0–R3 (issue #195).
    /// Counts every parameter as one slot (i64/f64 over-counted — see the
    /// backend's `set_func_arg_counts` scope note).
    pub func_arg_counts: Vec<u32>,
    /// AAPCS integer-argument count per *function type*, indexed by type index.
    /// Used by `call_indirect`, whose callee arg count comes from the static
    /// type index (issue #195).
    pub type_arg_counts: Vec<u32>,
    /// #311: whether each *function* (full index, imports first) returns i64 —
    /// the call lowering must tag the result as a register PAIR (r0:r1) or the
    /// hi half is invisible to liveness and the next constant clobbers it.
    pub func_ret_i64: Vec<bool>,
    /// #311: whether each *function type* returns i64 (for `call_indirect`).
    pub type_ret_i64: Vec<bool>,
    /// #359: declared parameter widths per *function* (full index, imports
    /// first): `func_params_i64[f][k]` is true when param `k` is i64/f64. The
    /// AAPCS stack-argument path needs the declared widths — op-stream inference
    /// can't see an unused i64 param that still shifts the incoming-stack layout.
    pub func_params_i64: Vec<Vec<bool>>,
    /// Defined globals with their initializers (#237). Empty if the module has
    /// no global section. Used by the native-pointer ABI to make a global whose
    /// initializer is a linear-memory address (e.g. `$__stack_pointer`)
    /// self-contained rather than table-relative.
    pub globals: Vec<WasmGlobal>,
    /// Function indices that populate any table via an element segment (#275).
    /// These are the possible `call_indirect` targets — a function reached only
    /// through the table is invisible to direct-`call` reachability, so the
    /// whole-graph closure must treat every table entry as reachable once any
    /// reachable function performs a `call_indirect`. Empty for modules with no
    /// element section (every leaf/direct-call module), keeping output identical.
    pub elem_func_indices: Vec<u32>,
}

/// Decode a WASM binary and extract functions, memory, and data segments
pub fn decode_wasm_module(wasm_bytes: &[u8]) -> Result<DecodedModule> {
    let mut functions = Vec::new();
    let mut memories = Vec::new();
    let mut data_segments = Vec::new();
    let mut globals: Vec<WasmGlobal> = Vec::new();
    let mut imports = Vec::new();
    let mut func_index = 0u32;
    let mut num_imported_funcs = 0u32;
    let mut export_names: HashMap<u32, String> = HashMap::new();
    // #195: per-type AAPCS arg count (indexed by type index) and per-function
    // arg count (indexed by full function index: imports first, then locals).
    let mut type_arg_counts: Vec<u32> = Vec::new();
    let mut func_arg_counts: Vec<u32> = Vec::new();
    let mut type_ret_i64: Vec<bool> = Vec::new();
    let mut func_ret_i64: Vec<bool> = Vec::new();
    // #359: declared param widths per type / per function (full index).
    let mut type_params_i64: Vec<Vec<bool>> = Vec::new();
    let mut func_params_i64: Vec<Vec<bool>> = Vec::new();
    let mut elem_func_indices: Vec<u32> = Vec::new();

    for payload in Parser::new(0).parse_all(wasm_bytes) {
        let payload = payload.context("Failed to parse WASM payload")?;

        match payload {
            Payload::TypeSection(reader) => {
                // Record the parameter count of each function type so calls can
                // marshal the right number of arguments (issue #195).
                for rec_group in reader {
                    let rec_group = rec_group.context("Failed to parse type")?;
                    for sub_ty in rec_group.types() {
                        let (count, ret_i64, params_i64) = match &sub_ty.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(func_ty) => (
                                func_ty.params().len() as u32,
                                func_ty
                                    .results()
                                    .first()
                                    .is_some_and(|t| *t == wasmparser::ValType::I64),
                                // #359: i64/f64 params occupy 8 bytes / a register
                                // pair under AAPCS. f32/f64 are not in scope for the
                                // stack-arg path (refused), but mark both 64-bit
                                // float and i64 so the guard catches them.
                                func_ty
                                    .params()
                                    .iter()
                                    .map(|t| {
                                        matches!(
                                            t,
                                            wasmparser::ValType::I64 | wasmparser::ValType::F64
                                        )
                                    })
                                    .collect::<Vec<bool>>(),
                            ),
                            _ => (0, false, Vec::new()),
                        };
                        type_arg_counts.push(count);
                        type_ret_i64.push(ret_i64);
                        type_params_i64.push(params_i64);
                    }
                }
            }
            Payload::ImportSection(reader) => {
                // wasmparser 0.221+ groups imports (the "compact imports"
                // proposal): the section reader yields `Imports` groups, each of
                // which may expand to several `Import`s. `into_imports()`
                // flattens groups back to individual `Import`s (preserving the
                // module/name/ty fields), keeping the per-import loop intact.
                for import in reader.into_imports() {
                    let import = import.context("Failed to parse import")?;
                    let (kind, idx) = match import.ty {
                        wasmparser::TypeRef::Func(type_idx) => {
                            let idx = num_imported_funcs;
                            num_imported_funcs += 1;
                            // Record the imported function's arg count at its
                            // full function index (imports come first).
                            func_arg_counts
                                .push(type_arg_counts.get(type_idx as usize).copied().unwrap_or(0));
                            func_ret_i64.push(
                                type_ret_i64
                                    .get(type_idx as usize)
                                    .copied()
                                    .unwrap_or(false),
                            );
                            func_params_i64.push(
                                type_params_i64
                                    .get(type_idx as usize)
                                    .cloned()
                                    .unwrap_or_default(),
                            );
                            (ImportKind::Function(type_idx), idx)
                        }
                        wasmparser::TypeRef::Memory(_) => (ImportKind::Memory, 0),
                        wasmparser::TypeRef::Table(_) => (ImportKind::Table, 0),
                        wasmparser::TypeRef::Global(_) => (ImportKind::Global, 0),
                        _ => continue,
                    };
                    imports.push(ImportEntry {
                        module: import.module.to_string(),
                        name: import.name.to_string(),
                        kind,
                        index: idx,
                    });
                }
            }
            Payload::FunctionSection(reader) => {
                // Each entry gives the type index of a locally-defined function,
                // in order. Their full function indices follow the imports, so
                // appending to `func_arg_counts` keeps it indexed by full index
                // (issue #195).
                for ty in reader {
                    let type_idx = ty.context("Failed to parse function type index")?;
                    func_arg_counts
                        .push(type_arg_counts.get(type_idx as usize).copied().unwrap_or(0));
                    func_ret_i64.push(
                        type_ret_i64
                            .get(type_idx as usize)
                            .copied()
                            .unwrap_or(false),
                    );
                    func_params_i64.push(
                        type_params_i64
                            .get(type_idx as usize)
                            .cloned()
                            .unwrap_or_default(),
                    );
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
            Payload::GlobalSection(reader) => {
                // #237: capture each defined global's i32 initializer + mutability.
                // The init is a const expr; we only decode a leading `i32.const`
                // (the shape `$__stack_pointer`/data-layout globals use). Anything
                // else (global.get, f32/f64, etc.) records `init_i32: None` and is
                // left to the table-relative path.
                for (idx, global) in reader.into_iter().enumerate() {
                    let global = global.context("Failed to parse global")?;
                    let mut init_i32 = None;
                    let mut ops = global.init_expr.get_operators_reader();
                    if let Ok(wasmparser::Operator::I32Const { value }) = ops.read() {
                        init_i32 = Some(value);
                    }
                    globals.push(WasmGlobal {
                        index: idx as u32,
                        init_i32,
                        mutable: global.ty.mutable,
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
            Payload::ElementSection(reader) => {
                // #275: collect every function index that initializes a table.
                // These are the `call_indirect` targets the direct-call closure
                // cannot see; `reachable_from_exports` unions them in when a
                // reachable function does a `call_indirect`. Both element forms
                // are handled: a flat function-index list, and the const-expr
                // form whose `ref.func` entries name the functions.
                for elem in reader {
                    let elem = elem.context("Failed to parse element segment")?;
                    match elem.items {
                        wasmparser::ElementItems::Functions(funcs) => {
                            for f in funcs {
                                elem_func_indices
                                    .push(f.context("Failed to parse element func index")?);
                            }
                        }
                        wasmparser::ElementItems::Expressions(_, exprs) => {
                            for expr in exprs {
                                let expr = expr.context("Failed to parse element expr")?;
                                for op in expr.get_operators_reader() {
                                    if let wasmparser::Operator::RefFunc { function_index } =
                                        op.context("Failed to parse element op")?
                                    {
                                        elem_func_indices.push(function_index);
                                    }
                                }
                            }
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
                let (ops, unsupported) = decode_function_body(&body)?;
                let actual_index = num_imported_funcs + func_index;
                let export_name = export_names.get(&actual_index).cloned();

                functions.push(FunctionOps {
                    index: actual_index,
                    export_name,
                    ops,
                    unsupported,
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
        imports,
        num_imported_funcs,
        func_arg_counts,
        type_arg_counts,
        func_ret_i64,
        type_ret_i64,
        func_params_i64,
        globals,
        elem_func_indices,
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
                // wasmparser 0.221+ compact-imports grouping — flatten groups
                // to individual imports (see the ImportSection handler above).
                for import in imports.into_imports() {
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
                let (ops, unsupported) = decode_function_body(&body)?;
                let actual_index = num_imported_funcs + func_index;
                let export_name = export_names.get(&actual_index).cloned();

                functions.push(FunctionOps {
                    index: actual_index,
                    export_name,
                    ops,
                    unsupported,
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
    /// `Some(reason)` when the body contained a value-affecting operator the
    /// decoder cannot lower (e.g. scalar f32/f64 — #369, bulk-memory
    /// memory.copy/fill). Such an op would otherwise be silently *dropped*
    /// (`convert_operator` → `None`), leaving the operand stack wrong and the
    /// function a silent miscompile. The compile path LOUD-SKIPS a flagged
    /// function (diagnostic + symbol absent → link error names it) instead —
    /// the #180/#185 "unsupported op must Err, never silently continue"
    /// contract. `None` once every op decoded or was intentionally ignorable
    /// (Nop/Unreachable).
    pub unsupported: Option<String>,
}

/// Decode a single function body to WasmOp sequence.
///
/// Returns the ops plus `Some(reason)` if any operator was a value-affecting
/// op the decoder cannot lower (so the function must be loud-skipped, #369 —
/// not silently miscompiled by dropping the op).
fn decode_function_body(body: &wasmparser::FunctionBody) -> Result<(Vec<WasmOp>, Option<String>)> {
    let mut ops = Vec::new();
    let mut unsupported: Option<String> = None;

    let ops_reader = body.get_operators_reader()?;
    for op_result in ops_reader {
        let op = op_result.context("Failed to read operator")?;

        if let Some(wasm_op) = convert_operator(&op) {
            ops.push(wasm_op);
        } else if unsupported.is_none() && !is_intentionally_ignored(&op) {
            // The op was DROPPED by `convert_operator` (`_ => None`) and is not
            // an intentional no-op (Nop/Unreachable) — record it so the
            // function is loud-skipped rather than silently miscompiled (#369).
            unsupported = Some(format!("{op:?}"));
        }
    }

    Ok((ops, unsupported))
}

/// Operators that `convert_operator` returns `None` for *on purpose* — they
/// carry no value-affecting semantics for our backend, so dropping them is
/// correct (NOT a silent miscompile). Everything else that decodes to `None`
/// is an unsupported op that must loud-skip its function (#369).
fn is_intentionally_ignored(op: &wasmparser::Operator) -> bool {
    use wasmparser::Operator::*;
    matches!(op, Nop | Unreachable)
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
        // i32<->i64 width conversions. Previously UNMAPPED → silently dropped,
        // which left an i32 value as a 64-bit operand with a garbage high half
        // (harmless when a following `i64.shl 32` discards it, but a latent
        // miscompile for extend-then-arithmetic, and it breaks width-correct
        // register allocation). (#204)
        I64ExtendI32U => Some(WasmOp::I64ExtendI32U),
        I64ExtendI32S => Some(WasmOp::I64ExtendI32S),
        I32WrapI64 => Some(WasmOp::I32WrapI64),

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
        // #372: full-width i64 load/store. The selector already lowers these to
        // a lo/hi i32 register-pair access (`generate_i64_load/store_with_bounds_check`,
        // reusing the #171 pair regalloc) — only the decoder arm was missing, so
        // `i64.load`/`i64.store` fell through `_ => None` and (since v0.11.46)
        // loud-skipped their function. The narrow forms (I64Load8.. / I64Store32)
        // were already decoded below.
        I64Load { memarg } => Some(WasmOp::I64Load {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Store { memarg } => Some(WasmOp::I64Store {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),

        // Sub-word loads (i32)
        I32Load8S { memarg } => Some(WasmOp::I32Load8S {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I32Load8U { memarg } => Some(WasmOp::I32Load8U {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I32Load16S { memarg } => Some(WasmOp::I32Load16S {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I32Load16U { memarg } => Some(WasmOp::I32Load16U {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),

        // Sub-word stores (i32)
        I32Store8 { memarg } => Some(WasmOp::I32Store8 {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I32Store16 { memarg } => Some(WasmOp::I32Store16 {
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
        // br_table: indexed multi-way branch. Previously UNMAPPED → silently
        // dropped, so the selector never emitted the index dispatch and control
        // fell straight into the first table arm — every br_table behaved as if
        // it always took target 0 (gale's binary-sem WAKE path never fired). The
        // jump-table relative depths + default depth are preserved in order.
        BrTable { targets } => {
            let default = targets.default();
            let tgts: Vec<u32> = targets.targets().filter_map(Result::ok).collect();
            Some(WasmOp::BrTable {
                targets: tgts,
                default,
            })
        }
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

        // i64 sub-word loads
        I64Load8S { memarg } => Some(WasmOp::I64Load8S {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Load8U { memarg } => Some(WasmOp::I64Load8U {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Load16S { memarg } => Some(WasmOp::I64Load16S {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Load16U { memarg } => Some(WasmOp::I64Load16U {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Load32S { memarg } => Some(WasmOp::I64Load32S {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Load32U { memarg } => Some(WasmOp::I64Load32U {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),

        // i64 sub-word stores
        I64Store8 { memarg } => Some(WasmOp::I64Store8 {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Store16 { memarg } => Some(WasmOp::I64Store16 {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Store32 { memarg } => Some(WasmOp::I64Store32 {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),

        // Memory management
        MemorySize { mem, .. } => Some(WasmOp::MemorySize(*mem)),
        MemoryGrow { mem, .. } => Some(WasmOp::MemoryGrow(*mem)),

        // Bulk memory (#374). The backend supports a single linear memory
        // (memory 0); any non-zero memory index falls through to `_ => None` and
        // loud-skips the function (GI-FPU-001 honesty contract) rather than
        // miscompiling a multi-memory copy. memory.copy reads dst/src memories;
        // memory.fill one. The selector lowers these to a bounds-checked byte
        // loop (see select_with_stack).
        MemoryCopy {
            dst_mem: 0,
            src_mem: 0,
        } => Some(WasmOp::MemoryCopy),
        MemoryFill { mem: 0 } => Some(WasmOp::MemoryFill),

        // ========================================================================
        // v128 SIMD operations (WASM SIMD proposal, 0xFD prefix)
        // ========================================================================
        V128Const { value } => {
            let mut bytes = [0u8; 16];
            bytes.copy_from_slice(value.bytes());
            Some(WasmOp::V128Const(bytes))
        }
        V128Load { memarg } => Some(WasmOp::V128Load {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        V128Store { memarg } => Some(WasmOp::V128Store {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),

        // v128 bitwise
        V128And => Some(WasmOp::V128And),
        V128Or => Some(WasmOp::V128Or),
        V128Xor => Some(WasmOp::V128Xor),
        V128Not => Some(WasmOp::V128Not),
        V128AndNot => Some(WasmOp::V128AndNot),

        // i8x16
        I8x16Add => Some(WasmOp::I8x16Add),
        I8x16Sub => Some(WasmOp::I8x16Sub),
        I8x16Neg => Some(WasmOp::I8x16Neg),
        I8x16Eq => Some(WasmOp::I8x16Eq),
        I8x16Ne => Some(WasmOp::I8x16Ne),
        I8x16LtS => Some(WasmOp::I8x16LtS),
        I8x16LtU => Some(WasmOp::I8x16LtU),
        I8x16GtS => Some(WasmOp::I8x16GtS),
        I8x16GtU => Some(WasmOp::I8x16GtU),
        I8x16LeS => Some(WasmOp::I8x16LeS),
        I8x16LeU => Some(WasmOp::I8x16LeU),
        I8x16GeS => Some(WasmOp::I8x16GeS),
        I8x16GeU => Some(WasmOp::I8x16GeU),
        I8x16Splat => Some(WasmOp::I8x16Splat),
        I8x16ExtractLaneS { lane } => Some(WasmOp::I8x16ExtractLaneS(*lane)),
        I8x16ExtractLaneU { lane } => Some(WasmOp::I8x16ExtractLaneU(*lane)),
        I8x16ReplaceLane { lane } => Some(WasmOp::I8x16ReplaceLane(*lane)),
        I8x16Shuffle { lanes } => Some(WasmOp::I8x16Shuffle(*lanes)),
        I8x16Swizzle => Some(WasmOp::I8x16Swizzle),

        // i16x8
        I16x8Add => Some(WasmOp::I16x8Add),
        I16x8Sub => Some(WasmOp::I16x8Sub),
        I16x8Mul => Some(WasmOp::I16x8Mul),
        I16x8Neg => Some(WasmOp::I16x8Neg),
        I16x8Eq => Some(WasmOp::I16x8Eq),
        I16x8Ne => Some(WasmOp::I16x8Ne),
        I16x8LtS => Some(WasmOp::I16x8LtS),
        I16x8LtU => Some(WasmOp::I16x8LtU),
        I16x8GtS => Some(WasmOp::I16x8GtS),
        I16x8GtU => Some(WasmOp::I16x8GtU),
        I16x8LeS => Some(WasmOp::I16x8LeS),
        I16x8LeU => Some(WasmOp::I16x8LeU),
        I16x8GeS => Some(WasmOp::I16x8GeS),
        I16x8GeU => Some(WasmOp::I16x8GeU),
        I16x8Splat => Some(WasmOp::I16x8Splat),
        I16x8ExtractLaneS { lane } => Some(WasmOp::I16x8ExtractLaneS(*lane)),
        I16x8ExtractLaneU { lane } => Some(WasmOp::I16x8ExtractLaneU(*lane)),
        I16x8ReplaceLane { lane } => Some(WasmOp::I16x8ReplaceLane(*lane)),

        // i32x4
        I32x4Add => Some(WasmOp::I32x4Add),
        I32x4Sub => Some(WasmOp::I32x4Sub),
        I32x4Mul => Some(WasmOp::I32x4Mul),
        I32x4Neg => Some(WasmOp::I32x4Neg),
        I32x4Eq => Some(WasmOp::I32x4Eq),
        I32x4Ne => Some(WasmOp::I32x4Ne),
        I32x4LtS => Some(WasmOp::I32x4LtS),
        I32x4LtU => Some(WasmOp::I32x4LtU),
        I32x4GtS => Some(WasmOp::I32x4GtS),
        I32x4GtU => Some(WasmOp::I32x4GtU),
        I32x4LeS => Some(WasmOp::I32x4LeS),
        I32x4LeU => Some(WasmOp::I32x4LeU),
        I32x4GeS => Some(WasmOp::I32x4GeS),
        I32x4GeU => Some(WasmOp::I32x4GeU),
        I32x4Splat => Some(WasmOp::I32x4Splat),
        I32x4ExtractLane { lane } => Some(WasmOp::I32x4ExtractLane(*lane)),
        I32x4ReplaceLane { lane } => Some(WasmOp::I32x4ReplaceLane(*lane)),

        // i64x2
        I64x2Add => Some(WasmOp::I64x2Add),
        I64x2Sub => Some(WasmOp::I64x2Sub),
        I64x2Mul => Some(WasmOp::I64x2Mul),
        I64x2Neg => Some(WasmOp::I64x2Neg),
        I64x2Eq => Some(WasmOp::I64x2Eq),
        I64x2Ne => Some(WasmOp::I64x2Ne),
        I64x2LtS => Some(WasmOp::I64x2LtS),
        I64x2GtS => Some(WasmOp::I64x2GtS),
        I64x2LeS => Some(WasmOp::I64x2LeS),
        I64x2GeS => Some(WasmOp::I64x2GeS),
        I64x2Splat => Some(WasmOp::I64x2Splat),
        I64x2ExtractLane { lane } => Some(WasmOp::I64x2ExtractLane(*lane)),
        I64x2ReplaceLane { lane } => Some(WasmOp::I64x2ReplaceLane(*lane)),

        // f32x4
        F32x4Add => Some(WasmOp::F32x4Add),
        F32x4Sub => Some(WasmOp::F32x4Sub),
        F32x4Mul => Some(WasmOp::F32x4Mul),
        F32x4Div => Some(WasmOp::F32x4Div),
        F32x4Abs => Some(WasmOp::F32x4Abs),
        F32x4Neg => Some(WasmOp::F32x4Neg),
        F32x4Sqrt => Some(WasmOp::F32x4Sqrt),
        F32x4Eq => Some(WasmOp::F32x4Eq),
        F32x4Ne => Some(WasmOp::F32x4Ne),
        F32x4Lt => Some(WasmOp::F32x4Lt),
        F32x4Le => Some(WasmOp::F32x4Le),
        F32x4Gt => Some(WasmOp::F32x4Gt),
        F32x4Ge => Some(WasmOp::F32x4Ge),
        F32x4Splat => Some(WasmOp::F32x4Splat),
        F32x4ExtractLane { lane } => Some(WasmOp::F32x4ExtractLane(*lane)),
        F32x4ReplaceLane { lane } => Some(WasmOp::F32x4ReplaceLane(*lane)),

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

    /// #204 regression: `i64.extend_i32_u`, `i64.extend_i32_s` and
    /// `i32.wrap_i64` must DECODE (they were previously unmapped → silently
    /// dropped by `convert_operator`, leaving an i32 value as a 64-bit operand
    /// with a garbage high half — the root cause of gale's miscompiled
    /// `(new_count << 32)` pack). The decoder must surface all three.
    #[test]
    fn test_decode_i64_i32_width_conversions() {
        let wat = r#"
            (module
                (func (export "conv") (param i32 i64) (result i32)
                    local.get 0
                    i64.extend_i32_u
                    local.get 0
                    i64.extend_i32_s
                    i64.add
                    local.get 1
                    i64.add
                    i32.wrap_i64
                )
            )
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let functions = decode_wasm_functions(&wasm).expect("decode");
        let ops = &functions[0].ops;
        assert!(
            ops.contains(&WasmOp::I64ExtendI32U),
            "i64.extend_i32_u must decode (not be dropped): {ops:?}"
        );
        assert!(
            ops.contains(&WasmOp::I64ExtendI32S),
            "i64.extend_i32_s must decode (not be dropped): {ops:?}"
        );
        assert!(
            ops.contains(&WasmOp::I32WrapI64),
            "i32.wrap_i64 must decode (not be dropped): {ops:?}"
        );
    }

    /// #204 WAKE-path regression: `br_table` must DECODE (it was unmapped in
    /// `convert_operator` → silently dropped, so the selector emitted no index
    /// dispatch and every `br_table` fell through to target 0 — gale's binary
    /// semaphore never took its WAKE branch). Targets + default are preserved.
    #[test]
    fn test_decode_br_table() {
        let wat = r#"
            (module
                (func (export "bt") (param i32) (result i32)
                    (block (block (block
                        local.get 0
                        br_table 2 0 1 2)
                      i32.const 30 return)
                      i32.const 20 return)
                    i32.const 10))
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let functions = decode_wasm_functions(&wasm).expect("decode");
        let bt = functions[0]
            .ops
            .iter()
            .find_map(|o| match o {
                WasmOp::BrTable { targets, default } => Some((targets.clone(), *default)),
                _ => None,
            })
            .expect("br_table must decode (not be dropped)");
        assert_eq!(bt.0, vec![2, 0, 1], "br_table targets preserved in order");
        assert_eq!(bt.1, 2, "br_table default preserved");
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
    fn test_decode_module_with_imports() {
        let wat = r#"
            (module
                (import "env" "log" (func $log (param i32)))
                (import "env" "memory" (memory 1))
                (func (export "run") (param i32)
                    local.get 0
                    call 0
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let module = decode_wasm_module(&wasm).expect("Failed to decode");

        // Should have 2 imports (1 func, 1 memory)
        assert_eq!(module.imports.len(), 2);
        assert_eq!(module.num_imported_funcs, 1);

        // First import is the function
        assert_eq!(module.imports[0].module, "env");
        assert_eq!(module.imports[0].name, "log");
        assert!(matches!(module.imports[0].kind, ImportKind::Function(_)));

        // Second import is memory
        assert_eq!(module.imports[1].module, "env");
        assert_eq!(module.imports[1].name, "memory");
        assert_eq!(module.imports[1].kind, ImportKind::Memory);

        // Should have 1 local function (index 1, because import is index 0)
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].index, 1);
        assert_eq!(module.functions[0].export_name, Some("run".to_string()));
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

    #[test]
    fn test_decode_subword_loads() {
        let wat = r#"
            (module
                (memory 1)
                (func (export "test") (param i32) (result i32)
                    local.get 0
                    i32.load8_u
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::I32Load8U {
            offset: 0,
            align: 0,
        }));
    }

    #[test]
    fn test_decode_subword_stores() {
        let wat = r#"
            (module
                (memory 1)
                (func (export "test") (param i32 i32)
                    local.get 0
                    local.get 1
                    i32.store8
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::I32Store8 {
            offset: 0,
            align: 0,
        }));
    }

    #[test]
    fn test_decode_memory_size_grow() {
        let wat = r#"
            (module
                (memory 1)
                (func (export "test") (result i32)
                    memory.size
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::MemorySize(0)));
    }

    #[test]
    fn test_decode_memory_grow() {
        let wat = r#"
            (module
                (memory 1)
                (func (export "test") (param i32) (result i32)
                    local.get 0
                    memory.grow
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::MemoryGrow(0)));
    }

    #[test]
    fn test_decode_bulk_memory_374() {
        // #374: memory.copy / memory.fill on the single linear memory decode to
        // the new WasmOp variants (was `_ => None` -> loud-skip).
        let wat = r#"
            (module
                (memory 1)
                (func (export "cpy") (param i32 i32 i32)
                    local.get 0 local.get 1 local.get 2 memory.copy)
                (func (export "fil") (param i32 i32 i32)
                    local.get 0 local.get 1 local.get 2 memory.fill)
            )
        "#;
        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");
        assert_eq!(functions.len(), 2);
        assert!(functions[0].ops.contains(&WasmOp::MemoryCopy));
        assert!(functions[1].ops.contains(&WasmOp::MemoryFill));
        // Neither function is flagged unsupported (they now lower).
        assert!(functions[0].unsupported.is_none());
        assert!(functions[1].unsupported.is_none());
    }

    #[test]
    fn test_decode_i64_subword_loads() {
        let wat = r#"
            (module
                (memory 1)
                (func (export "test") (param i32) (result i64)
                    local.get 0
                    i64.load8_s
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::I64Load8S {
            offset: 0,
            align: 0,
        }));
    }

    #[test]
    fn test_decode_all_subword_memory_ops() {
        // Test that all sub-word operations are decoded from WAT
        let wat = r#"
            (module
                (memory 1)
                (func (export "test") (param i32)
                    ;; i32 sub-word loads
                    local.get 0
                    i32.load8_s
                    drop
                    local.get 0
                    i32.load8_u
                    drop
                    local.get 0
                    i32.load16_s
                    drop
                    local.get 0
                    i32.load16_u
                    drop

                    ;; i32 sub-word stores
                    local.get 0
                    i32.const 42
                    i32.store8
                    local.get 0
                    i32.const 42
                    i32.store16

                    ;; i64 sub-word loads
                    local.get 0
                    i64.load8_s
                    drop
                    local.get 0
                    i64.load8_u
                    drop
                    local.get 0
                    i64.load16_s
                    drop
                    local.get 0
                    i64.load16_u
                    drop
                    local.get 0
                    i64.load32_s
                    drop
                    local.get 0
                    i64.load32_u
                    drop

                    ;; i64 sub-word stores
                    local.get 0
                    i64.const 42
                    i64.store8
                    local.get 0
                    i64.const 42
                    i64.store16
                    local.get 0
                    i64.const 42
                    i64.store32
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        let ops = &functions[0].ops;

        // Verify i32 sub-word ops are present
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I32Load8S { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I32Load8U { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I32Load16S { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I32Load16U { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I32Store8 { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I32Store16 { .. })));

        // Verify i64 sub-word ops are present
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Load8S { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Load8U { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Load16S { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Load16U { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Load32S { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Load32U { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Store8 { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Store16 { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Store32 { .. })));
    }

    #[test]
    fn test_decode_simd_i32x4_add() {
        let wat = r#"
            (module
                (func (export "add_v128") (param v128 v128) (result v128)
                    local.get 0
                    local.get 1
                    i32x4.add
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(
            functions[0].ops.contains(&WasmOp::I32x4Add),
            "Should decode i32x4.add: {:?}",
            functions[0].ops
        );
    }

    #[test]
    fn test_decode_simd_v128_const() {
        let wat = r#"
            (module
                (func (export "const_v128") (result v128)
                    v128.const i32x4 1 2 3 4
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(
            functions[0]
                .ops
                .iter()
                .any(|o| matches!(o, WasmOp::V128Const(_))),
            "Should decode v128.const: {:?}",
            functions[0].ops
        );
    }

    #[test]
    fn test_decode_simd_v128_load_store() {
        let wat = r#"
            (module
                (memory 1)
                (func (export "load_store") (param i32)
                    local.get 0
                    v128.load
                    local.get 0
                    v128.store
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        let ops = &functions[0].ops;
        assert!(
            ops.iter().any(|o| matches!(o, WasmOp::V128Load { .. })),
            "Should decode v128.load"
        );
        assert!(
            ops.iter().any(|o| matches!(o, WasmOp::V128Store { .. })),
            "Should decode v128.store"
        );
    }

    #[test]
    fn test_decode_simd_bitwise_ops() {
        let wat = r#"
            (module
                (func (export "bitwise") (param v128 v128) (result v128)
                    local.get 0
                    local.get 1
                    v128.and
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::V128And));
    }

    #[test]
    fn test_decode_simd_splat() {
        let wat = r#"
            (module
                (func (export "splat") (param i32) (result v128)
                    local.get 0
                    i32x4.splat
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::I32x4Splat));
    }

    #[test]
    fn test_decode_simd_extract_lane() {
        let wat = r#"
            (module
                (func (export "extract") (param v128) (result i32)
                    local.get 0
                    i32x4.extract_lane 2
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(
            functions[0].ops.contains(&WasmOp::I32x4ExtractLane(2)),
            "Should decode i32x4.extract_lane 2"
        );
    }

    #[test]
    fn test_decode_simd_f32x4_arithmetic() {
        let wat = r#"
            (module
                (func (export "f32x4_add") (param v128 v128) (result v128)
                    local.get 0
                    local.get 1
                    f32x4.add
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::F32x4Add));
    }

    #[test]
    fn test_369_scalar_float_op_flags_function_unsupported_not_dropped() {
        // #369: a scalar f32/f64 op the decoder can't lower must FLAG the
        // function (-> loud skip), never be silently dropped (which left a
        // `mov r0,r1` wrong-value stub). A pure-integer function stays clean.
        let wat = r#"
            (module
                (func (export "fadd") (param f32 f32) (result f32)
                    local.get 0 local.get 1 f32.add)
                (func (export "iadd") (param i32 i32) (result i32)
                    local.get 0 local.get 1 i32.add))
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let functions = decode_wasm_functions(&wasm).expect("decode");
        let fadd = functions
            .iter()
            .find(|f| f.export_name.as_deref() == Some("fadd"))
            .unwrap();
        let iadd = functions
            .iter()
            .find(|f| f.export_name.as_deref() == Some("iadd"))
            .unwrap();
        assert!(
            fadd.unsupported.is_some(),
            "f32.add must flag the function unsupported (loud-skip), got {:?}",
            fadd.unsupported
        );
        assert!(
            fadd.unsupported.as_deref().unwrap().contains("F32Add"),
            "diagnostic should name the op: {:?}",
            fadd.unsupported
        );
        assert!(
            iadd.unsupported.is_none(),
            "a pure-integer function must NOT be flagged: {:?}",
            iadd.unsupported
        );
    }

    #[test]
    fn test_decode_simd_multiple_ops() {
        let wat = r#"
            (module
                (func (export "simd_ops") (param v128 v128 v128) (result v128)
                    ;; (a + b) * c
                    local.get 0
                    local.get 1
                    i32x4.add
                    local.get 2
                    i32x4.mul
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        let ops = &functions[0].ops;
        assert!(ops.contains(&WasmOp::I32x4Add));
        assert!(ops.contains(&WasmOp::I32x4Mul));
    }

    /// #237: the decoder captures a global's `i32.const` initializer + mutability,
    /// so the native-pointer ABI can recognize the stack-pointer global.
    #[test]
    fn test_decode_captures_global_initializer() {
        let wat = r#"
            (module
                (memory 2)
                (global $__stack_pointer (mut i32) (i32.const 65536))
                (global $immutable_const i32 (i32.const 7))
                (func (export "f") (result i32) global.get 0)
            )
        "#;
        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let module = decode_wasm_module(&wasm).expect("Failed to decode");

        assert_eq!(module.globals.len(), 2, "both globals captured");
        let sp = &module.globals[0];
        assert_eq!(sp.index, 0);
        assert_eq!(sp.init_i32, Some(65536), "stack-pointer init captured");
        assert!(sp.mutable, "stack pointer is mutable");
        let c = &module.globals[1];
        assert_eq!(c.init_i32, Some(7));
        assert!(!c.mutable, "second global is immutable");
    }
}
