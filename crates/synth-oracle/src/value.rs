//! The value model both engines are translated into, and the signature of a
//! wasm export read from the module itself.

use std::fmt;

/// A wasm scalar type the harness can carry across both engines.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ValType {
    I32,
    I64,
    F32,
    F64,
}

impl ValType {
    /// Number of 32-bit machine words the value occupies under a soft-float
    /// 32-bit calling convention (AAPCS base variant, RV32 ILP32).
    pub fn words(self) -> usize {
        match self {
            ValType::I32 | ValType::F32 => 1,
            ValType::I64 | ValType::F64 => 2,
        }
    }
}

/// A wasm scalar value, stored as raw bits so floats keep their payload.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum WasmValue {
    I32(u32),
    I64(u64),
    /// f32 bit pattern.
    F32(u32),
    /// f64 bit pattern.
    F64(u64),
}

impl WasmValue {
    pub fn ty(self) -> ValType {
        match self {
            WasmValue::I32(_) => ValType::I32,
            WasmValue::I64(_) => ValType::I64,
            WasmValue::F32(_) => ValType::F32,
            WasmValue::F64(_) => ValType::F64,
        }
    }

    /// The value as little-endian 32-bit words, low word first.
    pub fn to_words(self) -> Vec<u32> {
        match self {
            WasmValue::I32(v) | WasmValue::F32(v) => vec![v],
            WasmValue::I64(v) | WasmValue::F64(v) => vec![v as u32, (v >> 32) as u32],
        }
    }

    /// Rebuild a value of type `ty` from its words, low word first.
    ///
    /// # Panics
    /// If `words` holds fewer words than `ty` needs.
    pub fn from_words(ty: ValType, words: &[u32]) -> Self {
        match ty {
            ValType::I32 => WasmValue::I32(words[0]),
            ValType::F32 => WasmValue::F32(words[0]),
            ValType::I64 => WasmValue::I64(u64::from(words[0]) | (u64::from(words[1]) << 32)),
            ValType::F64 => WasmValue::F64(u64::from(words[0]) | (u64::from(words[1]) << 32)),
        }
    }

    pub fn is_nan(self) -> bool {
        match self {
            WasmValue::F32(b) => f32::from_bits(b).is_nan(),
            WasmValue::F64(b) => f64::from_bits(b).is_nan(),
            _ => false,
        }
    }
}

impl fmt::Debug for WasmValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WasmValue::I32(v) => write!(f, "i32:0x{v:08x}"),
            WasmValue::I64(v) => write!(f, "i64:0x{v:016x}"),
            WasmValue::F32(v) => write!(f, "f32:0x{v:08x}({})", f32::from_bits(*v)),
            WasmValue::F64(v) => write!(f, "f64:0x{v:016x}({})", f64::from_bits(*v)),
        }
    }
}

/// Parameter and result types of a function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub params: Vec<ValType>,
    pub results: Vec<ValType>,
}

/// Read the signature of the exported function `export` from `wasm`.
///
/// Returns `Err` when the module does not parse, the export is missing or is
/// not a function, or the signature uses a type this harness does not carry
/// (v128, references).
pub fn export_signature(wasm: &[u8], export: &str) -> Result<Signature, String> {
    use wasmparser::{CompositeInnerType, ExternalKind, Parser, Payload, TypeRef, ValType as WVal};

    let conv = |v: &WVal| -> Result<ValType, String> {
        match v {
            WVal::I32 => Ok(ValType::I32),
            WVal::I64 => Ok(ValType::I64),
            WVal::F32 => Ok(ValType::F32),
            WVal::F64 => Ok(ValType::F64),
            other => Err(format!("unsupported value type {other:?}")),
        }
    };
    let mut types: Vec<Option<Signature>> = Vec::new();
    let mut func_types: Vec<u32> = Vec::new();
    let mut export_idx = None;
    for payload in Parser::new(0).parse_all(wasm) {
        match payload.map_err(|e| e.to_string())? {
            Payload::TypeSection(r) => {
                for rec in r {
                    for sub in rec.map_err(|e| e.to_string())?.into_types() {
                        types.push(match &sub.composite_type.inner {
                            CompositeInnerType::Func(ft) => Some(Signature {
                                params: ft.params().iter().map(conv).collect::<Result<_, _>>()?,
                                results: ft.results().iter().map(conv).collect::<Result<_, _>>()?,
                            }),
                            _ => None,
                        });
                    }
                }
            }
            Payload::ImportSection(r) => {
                for imp in r.into_imports() {
                    if let TypeRef::Func(t) = imp.map_err(|e| e.to_string())?.ty {
                        func_types.push(t);
                    }
                }
            }
            Payload::FunctionSection(r) => {
                for t in r {
                    func_types.push(t.map_err(|e| e.to_string())?);
                }
            }
            Payload::ExportSection(r) => {
                for e in r {
                    let e = e.map_err(|e| e.to_string())?;
                    if e.name == export {
                        if e.kind != ExternalKind::Func {
                            return Err(format!("export `{export}` is not a function"));
                        }
                        export_idx = Some(e.index);
                    }
                }
            }
            _ => {}
        }
    }
    let idx = export_idx.ok_or_else(|| format!("no export `{export}`"))?;
    let ty = *func_types
        .get(idx as usize)
        .ok_or_else(|| format!("export `{export}` names function {idx}, which does not exist"))?;
    types
        .get(ty as usize)
        .cloned()
        .flatten()
        .ok_or_else(|| format!("export `{export}` has type {ty}, which is not a function type"))
}

/// Whether the module has a linear memory at all: a memory section, a memory
/// import, or a data section.
///
/// The harness maps no linear memory and compares no memory effects, so a
/// module with one is refused by `run_case` rather than run and
/// judged on return values alone (REVIEW_11 F3). `run_case` exists only
/// with the `exec` feature.
pub fn has_linear_memory(wasm: &[u8]) -> Result<bool, String> {
    use wasmparser::{Parser, Payload, TypeRef};
    for payload in Parser::new(0).parse_all(wasm) {
        match payload.map_err(|e| e.to_string())? {
            Payload::MemorySection(r) if r.count() > 0 => return Ok(true),
            Payload::DataSection(r) if r.count() > 0 => return Ok(true),
            Payload::ImportSection(r) => {
                for imp in r.into_imports() {
                    if let TypeRef::Memory(_) = imp.map_err(|e| e.to_string())?.ty {
                        return Ok(true);
                    }
                }
            }
            _ => {}
        }
    }
    Ok(false)
}

/// One function import, in import order (which is function-index order).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuncImport {
    pub module: String,
    pub field: String,
    pub sig: Signature,
}

/// Every FUNCTION import of the module, with its signature.
pub fn function_imports(wasm: &[u8]) -> Result<Vec<FuncImport>, String> {
    use wasmparser::{CompositeInnerType, Parser, Payload, TypeRef, ValType as WVal};
    let conv = |v: &WVal| -> Result<ValType, String> {
        match v {
            WVal::I32 => Ok(ValType::I32),
            WVal::I64 => Ok(ValType::I64),
            WVal::F32 => Ok(ValType::F32),
            WVal::F64 => Ok(ValType::F64),
            other => Err(format!("unsupported value type {other:?}")),
        }
    };
    let mut types: Vec<Option<Result<Signature, String>>> = Vec::new();
    let mut out = Vec::new();
    for payload in Parser::new(0).parse_all(wasm) {
        match payload.map_err(|e| e.to_string())? {
            Payload::TypeSection(r) => {
                for rec in r {
                    for sub in rec.map_err(|e| e.to_string())?.into_types() {
                        types.push(match &sub.composite_type.inner {
                            CompositeInnerType::Func(ft) => Some((|| {
                                Ok(Signature {
                                    params: ft
                                        .params()
                                        .iter()
                                        .map(conv)
                                        .collect::<Result<_, String>>()?,
                                    results: ft
                                        .results()
                                        .iter()
                                        .map(conv)
                                        .collect::<Result<_, String>>()?,
                                })
                            })()),
                            _ => None,
                        });
                    }
                }
            }
            Payload::ImportSection(r) => {
                for imp in r.into_imports() {
                    let imp = imp.map_err(|e| e.to_string())?;
                    if let TypeRef::Func(t) = imp.ty {
                        let sig =
                            types.get(t as usize).cloned().flatten().ok_or_else(|| {
                                format!("import type {t} is not a function type")
                            })??;
                        out.push(FuncImport {
                            module: imp.module.to_string(),
                            field: imp.name.to_string(),
                            sig,
                        });
                    }
                }
            }
            _ => {}
        }
    }
    Ok(out)
}

/// The instantiation state a module needs that the HOSTED harness does not
/// materialize, if any: the reason, for a refusal.
///
/// The hosted emulator maps memory 0 zero-filled and sets R11/R10; it writes
/// no data segment, seeds no globals table (R9) and builds no funcref table.
/// A module that needs one of those would be judged on state the embedder
/// never set up, so it is refused instead.
pub fn uninstantiated_state(wasm: &[u8]) -> Result<Option<&'static str>, String> {
    use wasmparser::{Parser, Payload, TypeRef};
    let mut memories = 0u32;
    for payload in Parser::new(0).parse_all(wasm) {
        match payload.map_err(|e| e.to_string())? {
            Payload::DataSection(r) if r.count() > 0 => return Ok(Some("a data segment")),
            Payload::GlobalSection(r) if r.count() > 0 => return Ok(Some("a global")),
            Payload::TableSection(r) if r.count() > 0 => return Ok(Some("a table")),
            Payload::ElementSection(r) if r.count() > 0 => {
                return Ok(Some("an element segment"));
            }
            Payload::StartSection { .. } => return Ok(Some("a start function")),
            Payload::MemorySection(r) => {
                memories += r.count();
            }
            Payload::ImportSection(r) => {
                for imp in r.into_imports() {
                    match imp.map_err(|e| e.to_string())?.ty {
                        TypeRef::Func(_) => {}
                        _ => return Ok(Some("a non-function import")),
                    }
                }
            }
            _ => {}
        }
    }
    if memories > 1 {
        return Ok(Some("more than one memory"));
    }
    Ok(None)
}

/// Memory 0's declared initial size in bytes (default 64 KiB pages), or
/// `None` when the module defines no memory.
pub fn memory0_initial_bytes(wasm: &[u8]) -> Result<Option<u64>, String> {
    use wasmparser::{Parser, Payload};
    for payload in Parser::new(0).parse_all(wasm) {
        if let Payload::MemorySection(r) = payload.map_err(|e| e.to_string())?
            && let Some(m) = r.into_iter().next()
        {
            let m = m.map_err(|e| e.to_string())?;
            if m.memory64 || m.page_size_log2.is_some() {
                return Err("memory64 / custom page size is not carried".into());
            }
            return Ok(Some(m.initial * 65536));
        }
    }
    Ok(None)
}

/// The initial image of the module's linear memory: `initial` pages of
/// zeros with every active data segment applied in declaration order (a
/// later segment wins an overlap, as instantiation does). `None` for a
/// module without a memory.
///
/// Refused, because the emulator's mapping would not be the reference's:
/// an imported memory, more than one memory, a memory64 or custom-page-size
/// memory, a passive segment, and a segment whose offset is not a plain
/// `i32.const` or that does not fit the memory (instantiation would trap).
pub fn memory_image(wasm: &[u8]) -> Result<Option<Vec<u8>>, String> {
    use wasmparser::{DataKind, Operator, Parser, Payload, TypeRef};
    let mut image: Option<Vec<u8>> = None;
    for payload in Parser::new(0).parse_all(wasm) {
        match payload.map_err(|e| e.to_string())? {
            Payload::ImportSection(r) => {
                for imp in r.into_imports() {
                    if let TypeRef::Memory(_) = imp.map_err(|e| e.to_string())?.ty {
                        return Err("an imported memory is not mapped".into());
                    }
                }
            }
            Payload::MemorySection(r) => {
                for m in r {
                    let m = m.map_err(|e| e.to_string())?;
                    if image.is_some() {
                        return Err("more than one memory".into());
                    }
                    if m.memory64 || m.page_size_log2.is_some() {
                        return Err("memory64 / custom page size is not mapped".into());
                    }
                    let bytes = m
                        .initial
                        .checked_mul(65536)
                        .filter(|b| *b <= 1 << 28)
                        .ok_or("memory too large to map")?;
                    image = Some(vec![0u8; bytes as usize]);
                }
            }
            Payload::DataSection(r) => {
                for d in r {
                    let d = d.map_err(|e| e.to_string())?;
                    let DataKind::Active {
                        memory_index: 0,
                        offset_expr,
                    } = d.kind
                    else {
                        return Err("a passive or memory-k data segment".into());
                    };
                    let mut ops = offset_expr.get_operators_reader();
                    let off = match (ops.read(), ops.read()) {
                        (Ok(Operator::I32Const { value }), Ok(Operator::End)) => value as u32,
                        _ => return Err("a data offset that is not `i32.const`".into()),
                    };
                    let img = image.as_mut().ok_or("a data segment without a memory")?;
                    let end = off as usize + d.data.len();
                    if end > img.len() {
                        return Err(format!(
                            "data segment [{off:#x}, {end:#x}) leaves the memory"
                        ));
                    }
                    img[off as usize..end].copy_from_slice(d.data);
                }
            }
            _ => {}
        }
    }
    Ok(image)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linear_memory_is_detected() {
        let with = wat::parse_str("(module (memory 1) (func (export \"f\")))").unwrap();
        let imported =
            wat::parse_str("(module (import \"env\" \"m\" (memory 1)) (func (export \"f\")))")
                .unwrap();
        let without = wat::parse_str("(module (func (export \"f\")))").unwrap();
        assert_eq!(has_linear_memory(&with), Ok(true));
        assert_eq!(has_linear_memory(&imported), Ok(true));
        assert_eq!(has_linear_memory(&without), Ok(false));
    }

    #[test]
    fn function_imports_carry_module_field_and_signature() {
        let w = wat::parse_str(
            r#"(module
                 (import "env" "log" (func (param i32)))
                 (import "env" "m" (memory 1))
                 (import "host" "add2" (func (param i32 i64) (result i32))))"#,
        )
        .unwrap();
        let imps = function_imports(&w).unwrap();
        assert_eq!(imps.len(), 2);
        assert_eq!(
            (imps[0].module.as_str(), imps[0].field.as_str()),
            ("env", "log")
        );
        assert_eq!(imps[0].sig.results, vec![]);
        assert_eq!(imps[1].field, "add2");
        assert_eq!(imps[1].sig.params, vec![ValType::I32, ValType::I64]);
        assert_eq!(imps[1].sig.results, vec![ValType::I32]);
    }

    #[test]
    fn uninstantiated_state_names_what_the_hosted_harness_leaves_out() {
        let reason = |w: &str| uninstantiated_state(&wat::parse_str(w).unwrap()).unwrap();
        assert_eq!(reason("(module (memory 1) (func (export \"f\")))"), None);
        assert_eq!(
            reason("(module (import \"e\" \"f\" (func)) (func (export \"g\")))"),
            None
        );
        assert_eq!(
            reason("(module (memory 1) (data (i32.const 0) \"x\"))"),
            Some("a data segment")
        );
        assert_eq!(
            reason("(module (global (mut i32) (i32.const 1)))"),
            Some("a global")
        );
        assert_eq!(reason("(module (table 1 funcref))"), Some("a table"));
        assert_eq!(
            reason("(module (func $s) (start $s))"),
            Some("a start function")
        );
        assert_eq!(
            reason("(module (import \"e\" \"g\" (global i32)))"),
            Some("a non-function import")
        );
        assert_eq!(
            reason("(module (memory 1) (memory 1))"),
            Some("more than one memory")
        );
        let w = wat::parse_str("(module (memory 3))").unwrap();
        assert_eq!(memory0_initial_bytes(&w), Ok(Some(3 * 65536)));
        let w = wat::parse_str("(module)").unwrap();
        assert_eq!(memory0_initial_bytes(&w), Ok(None));
    }

    #[test]
    fn memory_image_applies_segments_in_order_and_refuses_what_it_cannot_map() {
        let m = wat::parse_str(
            "(module (memory 1) (data (i32.const 4) \"\\01\\02\\03\") (data (i32.const 5) \"\\ff\"))",
        )
        .unwrap();
        let img = memory_image(&m).unwrap().unwrap();
        assert_eq!(img.len(), 65536);
        assert_eq!(&img[3..8], &[0, 1, 0xff, 3, 0]);
        let none = wat::parse_str("(module (func))").unwrap();
        assert_eq!(memory_image(&none), Ok(None));
        for bad in [
            "(module (import \"e\" \"m\" (memory 1)))",
            "(module (memory 1) (data \"x\"))",
            "(module (memory 1) (data (i32.const 65535) \"xy\"))",
        ] {
            assert!(
                memory_image(&wat::parse_str(bad).unwrap()).is_err(),
                "{bad}"
            );
        }
    }
}
