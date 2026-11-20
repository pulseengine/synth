//! Module-level compile for x86-64: refuse what this lane cannot lower, by
//! name; lower every locally-defined function; lay a SysV ELF64 `ET_REL`
//! around the result with the SHARED object plan (`synth_core::object_plan`).
//!
//! WHY THIS TAKES THE MODULE BYTES. The decoded module synth-core produces
//! records i64/f32/f64 parameters as masks and treats every other type as an
//! i32 word. A `(param externref) (result externref)` identity function would
//! therefore look like an i32 identity and be lowered to a 32-bit move of a
//! 64-bit host reference — a truncation, the silent-miscompile class. So this
//! backend reads the EXACT signature of every function from the module itself
//! (wasmparser) and lowers a function only when every parameter and result is
//! `i32` or `i64`. The [`Backend`] trait's `compile_module`/`compile_function` take no
//! bytes, so they refuse and say why; the CLI calls [`compile_wasm`].
//!
//! MEMORY BASE — THE HOOK, NOT YET USED (maintainer decision, 2026-11-18).
//! This lane lowers no memory access and REFUSES every module that declares or
//! imports a memory. When linear memory lands (lane X8), the base is a
//! LINKER-PLACED memory symbol, one instance per object, addressed
//! RIP-relative (`lea reg, [rip + sym]`, an `R_X86_64_PC32` with the addend
//! the instruction site states). There is no ambient base register on x86-64:
//! a C embedder cannot reserve one (`-ffixed-r15` is refused by clang). Two
//! things the shared object plan does not carry yet, and X8 must add: a
//! `STV_HIDDEN` visibility for that symbol (a default-visibility PC32
//! reference does not link into a shared library — REVIEW_2 X1) and a
//! `.bss`-style section the object itself defines (REVIEW_6 F4).

use std::collections::BTreeMap;

use synth_core::backend::{
    Backend, BackendCapabilities, BackendError, CompilationResult, CompileConfig, CompiledFunction,
    RelocKind,
};
use synth_core::object_plan::{DataBlob, ElfMachine, ObjectFunction, plan_object, write_elf64_rel};
use synth_core::wasm_decoder::{DecodedModule, decode_wasm_module};
use synth_core::{TargetSpec, WasmOp};
use wasmparser::{Encoding, ExternalKind, Parser, Payload, ValType};

use crate::encoder;
use crate::inst::Inst;
use crate::selector::{self, Ty};

/// `EM_X86_64`.
pub const EM_X86_64: u16 = 62;

/// NO wildcard that returns a type: the backend emits no relocation yet, so
/// every kind panics here rather than ship an unrelocated placeholder. Lane X6 adds
/// `R_X86_64_PLT32`/`PC32` as explicit arms.
fn x86_64_reloc_type(kind: RelocKind) -> u32 {
    panic!(
        "x86_64 ELF builder cannot emit relocation kind {kind:?}: the \
         x86_64 backend emits no relocations yet (#1741)"
    )
}

/// The x86-64 machine for the shared ELF64 writer: `EM_X86_64`, `.text`
/// aligned to 16 (the ABI's function alignment), and `.note.GNU-stack` so a
/// GNU ld link does not mark the stack executable (REVIEW_2 X6).
pub const X86_64: ElfMachine = ElfMachine {
    e_machine: EM_X86_64,
    text_align: 16,
    reloc_type: x86_64_reloc_type,
    gnu_stack_note: true,
};

/// One lowered function, as shipped.
#[derive(Debug, Clone)]
pub struct X86Function {
    /// Full wasm function index.
    pub index: u32,
    /// `func_N` first, then any export names.
    pub symbols: Vec<String>,
    /// What the selector asked for.
    pub insts: Vec<Inst>,
    /// The encoding of [`Self::insts`].
    pub code: Vec<u8>,
    /// Each instruction's encoded length, in order.
    pub lens: Vec<usize>,
}

/// A compiled module: the object bytes and what went into them.
#[derive(Debug, Clone)]
pub struct X86Object {
    pub elf: Vec<u8>,
    pub functions: Vec<X86Function>,
}

fn fail(msg: impl Into<String>) -> BackendError {
    BackendError::CompilationFailed(msg.into())
}

/// The exact signature of each locally-defined function, its export names,
/// and every section this lane refuses.
struct ModuleShape {
    /// `(params, results)` per type index; `None` for a non-function type.
    types: Vec<Option<(Vec<ValType>, Vec<ValType>)>>,
    /// Type index per locally-defined function.
    func_types: Vec<u32>,
    /// Export names per full function index.
    exports: BTreeMap<u32, Vec<String>>,
    /// The declared (non-parameter) locals of each locally-defined function,
    /// in index order, with their EXACT types.
    locals: Vec<Vec<ValType>>,
}

fn read_shape(wasm: &[u8]) -> Result<ModuleShape, BackendError> {
    let mut shape = ModuleShape {
        types: Vec::new(),
        func_types: Vec::new(),
        exports: BTreeMap::new(),
        locals: Vec::new(),
    };
    let refuse = |what: &str| {
        Err(fail(format!(
            "x86_64: the module has {what}, which the x86_64 backend does not \
             lower yet (#1741: straight-line i32/i64 leaf functions only) — refusing"
        )))
    };
    for payload in Parser::new(0).parse_all(wasm) {
        let payload = payload.map_err(|e| fail(format!("x86_64: {e}")))?;
        match payload {
            Payload::Version { encoding, .. } => {
                if encoding != Encoding::Module {
                    return refuse("a component, not a core module");
                }
            }
            Payload::TypeSection(r) => {
                for rec in r {
                    let rec = rec.map_err(|e| fail(format!("x86_64: {e}")))?;
                    for sub in rec.into_types() {
                        shape.types.push(match &sub.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(f) => {
                                Some((f.params().to_vec(), f.results().to_vec()))
                            }
                            _ => None,
                        });
                    }
                }
            }
            Payload::FunctionSection(r) => {
                for t in r {
                    shape
                        .func_types
                        .push(t.map_err(|e| fail(format!("x86_64: {e}")))?);
                }
            }
            Payload::ExportSection(r) => {
                for e in r {
                    let e = e.map_err(|e| fail(format!("x86_64: {e}")))?;
                    if e.kind == ExternalKind::Func {
                        shape
                            .exports
                            .entry(e.index)
                            .or_default()
                            .push(e.name.to_string());
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                let mut locals = Vec::new();
                let reader = body
                    .get_locals_reader()
                    .map_err(|e| fail(format!("x86_64: {e}")))?;
                for group in reader {
                    let (count, ty) = group.map_err(|e| fail(format!("x86_64: {e}")))?;
                    // Validation caps a function's locals (50,000), so this
                    // cannot be made to allocate without bound.
                    locals.extend(std::iter::repeat_n(ty, count as usize));
                }
                shape.locals.push(locals);
            }
            Payload::CodeSectionStart { .. } | Payload::CustomSection(_) | Payload::End(_) => {}
            Payload::ImportSection(_) => {
                return refuse("an import section (calls and imports are lane X6)");
            }
            Payload::TableSection(_) => return refuse("a table (call_indirect is lane X9)"),
            Payload::MemorySection(_) => return refuse("a linear memory (memory is lane X8)"),
            Payload::GlobalSection(_) => return refuse("globals (globals are lane X7)"),
            Payload::StartSection { .. } => return refuse("a start function"),
            Payload::ElementSection(_) => return refuse("an element section"),
            Payload::DataCountSection { .. } | Payload::DataSection(_) => {
                return refuse("a data section");
            }
            Payload::TagSection(_) => return refuse("a tag section (exceptions)"),
            other => return refuse(&format!("an unexpected section ({other:?})")),
        }
    }
    Ok(shape)
}

/// Compile a core wasm module to an x86-64 SysV ELF64 `ET_REL`.
///
/// Every locally-defined function is lowered (exported or not), so a helper
/// with an unsupported op fails the compile — the loud-skip contract applied to
/// the whole module. The object has one `.text`; each function carries a LOCAL
/// `func_N` label and its GLOBAL export names (the shared plan's binding rule).
pub fn compile_wasm(wasm: &[u8]) -> Result<X86Object, BackendError> {
    wasmparser::validate(wasm).map_err(|e| fail(format!("x86_64: invalid wasm: {e}")))?;
    let shape = read_shape(wasm)?;
    let module: DecodedModule =
        decode_wasm_module(wasm).map_err(|e| fail(format!("x86_64: decode: {e}")))?;
    if module.num_imported_funcs != 0 {
        return Err(fail("x86_64: imported functions are not lowered (lane X6)"));
    }
    if shape.exports.is_empty() {
        return Err(fail("x86_64: no exported functions found"));
    }
    let mut functions = Vec::new();
    for func in &module.functions {
        let local = func.index as usize;
        let sym = format!("func_{}", func.index);
        let name = func.export_name.clone().unwrap_or_else(|| sym.clone());
        if let Some(reason) = &func.unsupported {
            return Err(fail(format!(
                "x86_64: function '{name}' contains an operator dropped at decode \
                 ({reason}) — refusing"
            )));
        }
        let ty = *shape
            .func_types
            .get(local)
            .ok_or_else(|| fail(format!("x86_64: function {} has no type", func.index)))?;
        let Some(Some((params, results))) = shape.types.get(ty as usize) else {
            return Err(fail(format!(
                "x86_64: function '{name}' has a non-function type"
            )));
        };
        let int = |t: &ValType| match t {
            ValType::I32 => Ok(Ty::I32),
            ValType::I64 => Ok(Ty::I64),
            other => Err(fail(format!(
                "x86_64: function '{name}' has a {other} parameter, result or \
                 local; the x86_64 backend lowers i32 and i64 values only \
                 (floats and references are later lanes) — refusing"
            ))),
        };
        let params: Vec<Ty> = params.iter().map(int).collect::<Result<_, _>>()?;
        let results: Vec<Ty> = results.iter().map(int).collect::<Result<_, _>>()?;
        let locals: Vec<Ty> = shape
            .locals
            .get(local)
            .ok_or_else(|| fail(format!("x86_64: function {} has no body", func.index)))?
            .iter()
            .map(int)
            .collect::<Result<_, _>>()?;
        let insts = selector::select(&func.ops, &params, &locals, &results)
            .map_err(|e| fail(format!("function '{name}': {e}")))?;
        let (code, lens) = encoder::encode_all(&insts);
        let mut symbols = vec![sym.clone()];
        for e in shape.exports.get(&func.index).into_iter().flatten() {
            // REVIEW_13 F3: an export named exactly like this function's own
            // `func_N` label used to be deduplicated against it, and the label
            // is LOCAL — so the export vanished from the object with exit 0
            // and the embedder's link failed later on an undefined symbol.
            // Refused by name instead. (AArch64 has the same dedup today.)
            if *e == sym {
                return Err(fail(format!(
                    "x86_64: function {} is exported as '{e}', the same name as its own object-local label `{sym}`; the label is LOCAL, so the export would be silently missing from the object — refusing (rename the export)",
                    func.index
                )));
            }
            symbols.push(e.clone());
        }
        functions.push(X86Function {
            index: func.index,
            symbols,
            insts,
            code,
            lens,
        });
    }
    let objs: Vec<ObjectFunction> = functions
        .iter()
        .map(|f| ObjectFunction::code(f.symbols.clone(), f.code.clone(), Vec::new()))
        .collect();
    let plan = plan_object("x86_64 ELF builder", &objs, &DataBlob::default(), &[])?;
    Ok(X86Object {
        elf: write_elf64_rel(&plan, &X86_64),
        functions,
    })
}

/// The x86-64 backend. Registered so `synth backends` lists it and `-b x86_64`
/// resolves; the CLI compiles through [`compile_wasm`].
#[derive(Debug, Default)]
pub struct X86_64Backend;

impl X86_64Backend {
    pub fn new() -> Self {
        Self
    }
}

const NEEDS_BYTES: &str = "the x86_64 backend compiles from the module bytes \
     (synth_backend_x86_64::compile_wasm), because the decoded module does not \
     carry exact value types and a reference-typed signature would be lowered as \
     i32 — refusing rather than guessing";

impl Backend for X86_64Backend {
    fn name(&self) -> &str {
        "x86_64"
    }

    fn capabilities(&self) -> BackendCapabilities {
        BackendCapabilities {
            produces_elf: true,
            supports_rule_verification: false,
            supports_binary_verification: false,
            is_external: false,
        }
    }

    fn supported_targets(&self) -> Vec<TargetSpec> {
        vec![TargetSpec::x86_64_sysv()]
    }

    fn compile_module(
        &self,
        _module: &DecodedModule,
        _config: &CompileConfig,
    ) -> Result<CompilationResult, BackendError> {
        Err(BackendError::UnsupportedConfig(NEEDS_BYTES.into()))
    }

    fn compile_function(
        &self,
        _name: &str,
        _ops: &[WasmOp],
        _config: &CompileConfig,
    ) -> Result<CompiledFunction, BackendError> {
        Err(BackendError::UnsupportedConfig(NEEDS_BYTES.into()))
    }

    fn is_available(&self) -> bool {
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_object_is_an_x86_64_et_rel_with_the_stack_note() {
        let wasm = wat::parse_str(
            r#"(module (func (export "add") (param i32 i32) (result i32)
                 local.get 0 local.get 1 i32.add))"#,
        )
        .unwrap();
        let obj = compile_wasm(&wasm).unwrap();
        let e = &obj.elf;
        assert_eq!(&e[..4], b"\x7fELF");
        assert_eq!(e[4], 2, "ELFCLASS64");
        assert_eq!(u16::from_le_bytes([e[16], e[17]]), 1, "ET_REL");
        assert_eq!(u16::from_le_bytes([e[18], e[19]]), EM_X86_64);
        assert!(
            e.windows(16).any(|w| w == b".note.GNU-stack\0"),
            "no .note.GNU-stack name in the object"
        );
        assert_eq!(obj.functions.len(), 1);
        assert_eq!(obj.functions[0].symbols, vec!["func_0", "add"]);
    }

    #[test]
    fn the_trait_entry_points_refuse_and_say_why() {
        let b = X86_64Backend::new();
        let e = b
            .compile_function("f", &[WasmOp::End], &CompileConfig::default())
            .unwrap_err();
        assert!(e.to_string().contains("compile_wasm"), "{e}");
    }
}
