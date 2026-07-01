//! `Backend` trait implementation for the AArch64 host-native backend (#538).
//!
//! Milestone-1b: wires the milestone-1a encoder/selector into synth's `Backend`
//! interface — `compile_function` lowers a leaf integer function to A64 machine
//! code, and `compile_module` concatenates the exported functions into an
//! `EM_AARCH64` relocatable ELF object (via [`crate::elf`]). Functions outside
//! the integer subset are loud-skipped by the caller's compile loop (the selector
//! returns an error), never miscompiled.

use synth_core::backend::{
    Backend, BackendCapabilities, BackendError, CompilationResult, CompileConfig, CompiledFunction,
};
use synth_core::wasm_decoder::DecodedModule;
use synth_core::{TargetSpec, WasmOp};

use crate::elf::{self, ElfFunction};
use crate::selector;

/// The AArch64 (A64) backend. Milestone-1b: leaf integer subset, ELF output.
#[derive(Debug, Default)]
pub struct AArch64Backend;

impl AArch64Backend {
    pub fn new() -> Self {
        Self
    }
}

/// Count register parameters from the op stream (a local index read before it is
/// written is a parameter). Mirrors the ARM/RISC-V backends' heuristic.
fn count_params(ops: &[WasmOp]) -> u32 {
    use std::collections::HashMap;
    let mut first_access: HashMap<u32, bool> = HashMap::new();
    for op in ops {
        match op {
            WasmOp::LocalGet(i) => {
                first_access.entry(*i).or_insert(true);
            }
            WasmOp::LocalSet(i) | WasmOp::LocalTee(i) => {
                first_access.entry(*i).or_insert(false);
            }
            _ => {}
        }
    }
    first_access
        .iter()
        .filter_map(|(&i, &read_first)| if read_first { Some(i + 1) } else { None })
        .max()
        .unwrap_or(0)
}

impl Backend for AArch64Backend {
    fn name(&self) -> &str {
        "aarch64"
    }

    fn capabilities(&self) -> BackendCapabilities {
        BackendCapabilities {
            produces_elf: true,
            supports_rule_verification: false,
            supports_binary_verification: true,
            is_external: false,
        }
    }

    fn supported_targets(&self) -> Vec<TargetSpec> {
        vec![TargetSpec::cortex_a53()]
    }

    fn compile_function(
        &self,
        name: &str,
        ops: &[WasmOp],
        _config: &CompileConfig,
    ) -> Result<CompiledFunction, BackendError> {
        let num_params = count_params(ops);
        let words = selector::select(ops, num_params)
            .map_err(|e| BackendError::CompilationFailed(e.to_string()))?;
        let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        Ok(CompiledFunction {
            name: name.to_string(),
            code,
            wasm_ops: ops.to_vec(),
            relocations: Vec::new(),
            // AArch64 DWARF `.debug_line` is a later milestone (pairs with #394).
            line_map: Vec::new(),
        })
    }

    fn compile_module(
        &self,
        module: &DecodedModule,
        config: &CompileConfig,
    ) -> Result<CompilationResult, BackendError> {
        let exports: Vec<&_> = module
            .functions
            .iter()
            .filter(|f| f.export_name.is_some())
            .collect();
        if exports.is_empty() {
            return Err(BackendError::CompilationFailed(
                "no exported functions found".into(),
            ));
        }

        let mut functions = Vec::new();
        let mut elf_funcs = Vec::new();
        for func in &exports {
            let name = func.export_name.clone().unwrap();
            // #554: honor the decoder's loud-skip marker. An op dropped at decode
            // (`_ => None`, e.g. scalar `f32.*`) is absent from `func.ops`, so it
            // never reaches the selector's unsupported-op guard — lowering the
            // remaining stream would be a silent miscompile. Reject honestly,
            // matching the milestone-1 "unsupported wasm op" contract.
            if let Some(reason) = &func.unsupported {
                return Err(BackendError::CompilationFailed(format!(
                    "function '{name}' contains an unsupported operator ({reason}) \
                     dropped at decode — refusing to emit a silent miscompile \
                     (#369, #554)"
                )));
            }
            let compiled = self.compile_function(&name, &func.ops, config)?;
            elf_funcs.push(ElfFunction {
                name: compiled.name.clone(),
                code: compiled.code.clone(),
            });
            functions.push(compiled);
        }

        let elf = elf::build_relocatable_object(&elf_funcs);
        Ok(CompilationResult {
            functions,
            elf: Some(elf),
            backend_name: self.name().to_string(),
        })
    }

    fn is_available(&self) -> bool {
        true
    }
}
