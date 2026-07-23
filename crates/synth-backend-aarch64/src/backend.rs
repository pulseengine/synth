//! `Backend` trait implementation for the AArch64 host-native backend (#538).
//!
//! Milestone-1b: wires the milestone-1a encoder/selector into synth's `Backend`
//! interface — `compile_function` lowers a leaf integer function to A64 machine
//! code, and `compile_module` concatenates the exported functions into an
//! `EM_AARCH64` relocatable ELF object (via [`crate::elf`]). Functions outside
//! the integer subset are loud-skipped by the caller's compile loop (the selector
//! returns an error), never miscompiled.

use synth_core::backend::{
    Backend, BackendCapabilities, BackendError, CodeRelocation, CompilationResult, CompileConfig,
    CompiledFunction, RelocKind,
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

    /// Lower one function body, threading the module-wide call metadata needed to
    /// lower direct `call` (#851): `num_imports`, `func_arg_counts`, and
    /// `func_result_counts` come from the decoded module (all indexed by full
    /// function index). Each lowered `bl` becomes an `R_AARCH64_CALL26`
    /// relocation against the callee's `func_N` symbol, which
    /// [`Self::compile_module`] emits for every local function. Call-free
    /// functions produce byte-identical code and no relocations.
    fn compile_function_with_results(
        &self,
        name: &str,
        ops: &[WasmOp],
        config: &CompileConfig,
        func_result_counts: &[u32],
        func_ret_float: &[bool],
    ) -> Result<CompiledFunction, BackendError> {
        // #457: cap the access-pattern inference with the declared count when
        // the driver supplied one — a read-before-write non-param local (wasm
        // zero-init) is otherwise indistinguishable from a param and would be
        // read from an argument register (caller garbage). The reclassified
        // local then hits the selector's "non-param locals not yet supported"
        // guard: a LOUD skip instead of a silent miscompile (milestone-1
        // contract; frame-slot zero-init lands with non-param local support).
        let inferred = count_params(ops);
        let num_params = match config.current_func_param_count {
            Some(declared) => inferred.min(declared),
            None => inferred,
        };
        // m3: thread the per-param float masks so float params resolve to their
        // AAPCS64 V registers (an independent counter from the GP arg registers).
        // #538 cf: also thread the decoder's blocktype-arity side-table so the
        // void-block control-flow lowering can gate on `(0,0)` and loud-decline
        // value-carrying (typed) blocks.
        // #851: thread the call metadata so direct `call` lowers to `bl func_N`
        // + an R_AARCH64_CALL26 relocation (call-free bodies are unaffected).
        let (words, call_sites) = selector::select_typed_cf_calls(
            ops,
            num_params,
            &config.current_func_params_f32,
            &config.current_func_params_f64,
            &config.current_func_block_arity,
            config.num_imports,
            &config.func_arg_counts,
            func_result_counts,
            func_ret_float,
        )
        .map_err(|e| BackendError::CompilationFailed(e.to_string()))?;
        let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        // Each direct call site → an R_AARCH64_CALL26 against the callee's
        // `func_N` symbol (emitted for every local function by compile_module).
        let relocations: Vec<CodeRelocation> = call_sites
            .iter()
            .map(|cs| CodeRelocation {
                offset: cs.offset,
                symbol: format!("func_{}", cs.callee),
                kind: RelocKind::AArch64Call26,
            })
            .collect();
        Ok(CompiledFunction {
            name: name.to_string(),
            code,
            wasm_ops: ops.to_vec(),
            relocations,
            // AArch64 DWARF `.debug_line` is a later milestone (pairs with #394).
            line_map: Vec::new(),
            // VCR-DEC-003 (#396): provenance is ARM(Thumb)-only in v1.
            branch_map: Vec::new(),
            // #778: WCET cycle model is ARM(Thumb-2)-only in v1.
            wcet: None,
            wcet_intermediate: None,
        })
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
        config: &CompileConfig,
    ) -> Result<CompiledFunction, BackendError> {
        // #851: the CLI's per-function compile path threads the module-wide
        // result-count + float-return tables via the config so direct `call`
        // lowers here too (a float-returning callee is loud-declined — v0/d0).
        let result_counts = config.func_result_counts.clone();
        let n = config.func_ret_f32.len().max(config.func_ret_f64.len());
        let ret_float: Vec<bool> = (0..n)
            .map(|i| {
                config.func_ret_f32.get(i).copied().unwrap_or(false)
                    || config.func_ret_f64.get(i).copied().unwrap_or(false)
            })
            .collect();
        self.compile_function_with_results(name, ops, config, &result_counts, &ret_float)
    }

    fn compile_module(
        &self,
        module: &DecodedModule,
        config: &CompileConfig,
    ) -> Result<CompilationResult, BackendError> {
        // #851: to lower direct `call`, EVERY locally-defined function must be
        // placed in `.text` with a `func_N` symbol — a callee is often a
        // non-exported helper, and an R_AARCH64_CALL26 needs a symbol to resolve
        // against. (Pre-#851 only exported functions were emitted; a module with
        // no local functions still errors.) Side effect, noted honestly: a
        // non-exported helper containing an unsupported op now FAILS the compile
        // instead of being silently ignored — the loud-skip contract, applied to
        // the whole reachable local set.
        let locals: Vec<&_> = module
            .functions
            .iter()
            .filter(|f| f.index >= module.num_imported_funcs)
            .collect();
        if locals.is_empty() {
            return Err(BackendError::CompilationFailed(
                "no locally-defined functions found".into(),
            ));
        }
        if !module.functions.iter().any(|f| f.export_name.is_some()) {
            return Err(BackendError::CompilationFailed(
                "no exported functions found".into(),
            ));
        }

        // #851: per-function "returns a float" mask (v0/d0 result) — a
        // float-returning callee is loud-declined by the call lowering.
        let nrf = module.func_ret_f32.len().max(module.func_ret_f64.len());
        let func_ret_float: Vec<bool> = (0..nrf)
            .map(|i| {
                module.func_ret_f32.get(i).copied().unwrap_or(false)
                    || module.func_ret_f64.get(i).copied().unwrap_or(false)
            })
            .collect();

        let mut functions = Vec::new();
        let mut elf_funcs = Vec::new();
        for func in &locals {
            // The `.text` symbol is the export name when exported, else `func_N`
            // (the full function index). The relocation-target symbol is ALWAYS
            // `func_N` (added as an alias below) so a call by index resolves
            // regardless of export status.
            let func_sym = format!("func_{}", func.index);
            let name = func.export_name.clone().unwrap_or_else(|| func_sym.clone());
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
            // #457: THIS function's declared param count (imports-first full
            // index) caps the param-count inference in `compile_function`.
            let declared_params = config.func_arg_counts.get(func.index as usize).copied();
            // #851: thread num_imports + func_arg_counts (call metadata) so the
            // call lowering can classify import vs local and marshal args.
            let func_config = CompileConfig {
                current_func_param_count: declared_params.or(config.current_func_param_count),
                num_imports: module.num_imported_funcs,
                func_arg_counts: module.func_arg_counts.clone(),
                ..config.clone()
            };
            let compiled = self.compile_function_with_results(
                &name,
                &func.ops,
                &func_config,
                &module.func_result_counts,
                &func_ret_float,
            )?;
            // Symbol aliases at this function's `.text` offset: always `func_N`;
            // plus the export name when it differs (so both `run` and `func_1`
            // resolve to the same body).
            let mut aliases = vec![func_sym.clone()];
            if let Some(exp) = &func.export_name
                && *exp != func_sym
            {
                aliases.push(exp.clone());
            }
            elf_funcs.push(ElfFunction {
                symbols: aliases,
                code: compiled.code.clone(),
                relocations: compiled.relocations.clone(),
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
