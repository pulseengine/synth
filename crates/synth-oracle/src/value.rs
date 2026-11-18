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
}
