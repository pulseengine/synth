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
        // #865: resolve `--safety-bounds` into the selector's explicit
        // `MemBounds` — `software` emits per-access OOB-trap checks against the
        // module's declared memory limit, `none` is the explicit unchecked
        // opt-out, and anything else (mask/mpu) HARD-ERRORS here too (defense
        // in depth behind the CLI's early rejection): accepting a mode and
        // emitting unchecked accesses is the #865 silent-no-op miscompile.
        let bounds = match config.effective_safety_bounds() {
            synth_core::backend::SafetyBounds::Software => selector::MemBounds::Software {
                limit_bytes: config.linear_memory_bytes as u64,
            },
            synth_core::backend::SafetyBounds::None => selector::MemBounds::Unchecked,
            other => {
                return Err(BackendError::CompilationFailed(format!(
                    "--safety-bounds {} is not implemented on the aarch64 backend — \
                     refusing to silently emit UNCHECKED memory accesses (#865). \
                     Use --safety-bounds software (the default: per-access bounds \
                     checks that trap out-of-bounds) or --safety-bounds none \
                     (explicit unchecked opt-out).",
                    other.as_str()
                )));
            }
        };
        // #851 lane L3: the module-level context for globals + call_indirect.
        // Its `substrate_emitted` flag is FAIL-SAFE — false unless the driver
        // has actually placed `__synth_globals` / `__synth_func_table`.
        let ctx = module_ctx(config);
        let (words, call_sites, sym_relocs) = selector::select_typed_cf_calls(
            ops,
            num_params,
            &config.current_func_params_f32,
            &config.current_func_params_f64,
            &config.current_func_block_arity,
            config.num_imports,
            &config.func_arg_counts,
            func_result_counts,
            func_ret_float,
            bounds,
            &ctx,
        )
        .map_err(|e| BackendError::CompilationFailed(e.to_string()))?;
        let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        // Each direct call site → an R_AARCH64_CALL26 against the callee's
        // `func_N` symbol (emitted for every local function by compile_module);
        // #851 lane L3 adds the `adrp`+`add :lo12:` pairs that reach the
        // emitted globals region / funcref table.
        let relocations: Vec<CodeRelocation> = call_sites
            .iter()
            .map(|cs| CodeRelocation {
                offset: cs.offset,
                symbol: format!("func_{}", cs.callee),
                kind: RelocKind::AArch64Call26,
            })
            .chain(sym_relocs)
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

/// #851 lane L3 — build the selector's module context from the driver-supplied
/// [`CompileConfig`]. `substrate_emitted` is threaded verbatim: it is `false`
/// unless the driver ran [`crate::substrate::plan`] AND placed its output, so a
/// context built here can never authorize code that addresses a region the
/// object lacks.
fn module_ctx(config: &CompileConfig) -> selector::ModuleCtx {
    let guards = &config.call_indirect_guards;
    // Per table: (slot count, base SLOT index). `base_byte_offset` counts the
    // 4-byte pointer slots of the ARM region contract, so /4 recovers the slot
    // index — the aarch64 table uses the same SLOT ORDER with 8-byte records.
    // Stop at the first table without a compile-time size/base: every later
    // table's base is then not a constant, and an index past the end
    // LOUD-DECLINES at the lowering (matching `funcref_region_slots`).
    let mut tables: Vec<(u32, u32)> = Vec::new();
    for t in &guards.tables {
        match (t.table_size, t.base_byte_offset) {
            (Some(size), Some(base_bytes)) => tables.push((size, base_bytes / 4)),
            _ => break,
        }
    }
    let n_types = config
        .type_arg_counts
        .len()
        .max(config.type_class_ids.len())
        .max(config.type_result_counts.len());
    selector::ModuleCtx {
        substrate_emitted: config.a64_substrate_emitted,
        // #643 slot widths: 8 ⇒ an i64/f64 global (the `x` view).
        global_is64: config.global_widths.iter().map(|w| *w == 8).collect(),
        tables,
        type_class_ids: config.type_class_ids.clone(),
        type_arg_counts: config.type_arg_counts.clone(),
        type_result_counts: config.type_result_counts.clone(),
        type_ret_float: (0..n_types)
            .map(|i| {
                config.type_ret_f32.get(i).copied().unwrap_or(false)
                    || config.type_ret_f64.get(i).copied().unwrap_or(false)
            })
            .collect(),
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
        // #851: active data segments are NOT materialized by this backend —
        // there is no data section, no startup, and no x28-establishing code
        // (the base is an embedder precondition). Compiling a data-carrying
        // module would ship its initialized region reading ZEROS where WASM
        // guarantees segment bytes: the silent-miscompile class (#757/#758/
        // #798 on the other backends). Decline loudly; data-segment init is a
        // documented follow-on.
        if !module.data_segments.is_empty() {
            return Err(BackendError::CompilationFailed(format!(
                "module carries {} active data segment(s), but the aarch64 \
                 backend does not materialize data segments — a load from the \
                 initialized region would silently read zeros; refusing \
                 (#851). Data-segment init is a documented follow-on.",
                module.data_segments.len()
            )));
        }
        // A memory-0 segment with a NON-CONST offset is legacy-dropped at
        // decode (absent from data_segments) — the recorded reason is the only
        // trace. Same silent-miscompile class; same loud refusal.
        if let Some(reason) = &module.default_memory_nonconst_data {
            return Err(BackendError::CompilationFailed(format!(
                "aarch64: {reason} — refusing to ship the region uninitialized \
                 (#851)"
            )));
        }
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

        // #851 lane L3 — plan the MODULE-LEVEL substrate (globals `.data` image
        // + `.text` funcref table) BEFORE compiling any body, so an
        // unrepresentable shape declines the whole compile rather than being
        // discovered after code that addresses it was emitted. `plan` is the
        // single producer of both regions, so what the code addresses and what
        // the object ships cannot disagree.
        let uses_globals = locals.iter().any(|f| {
            f.ops
                .iter()
                .any(|op| matches!(op, WasmOp::GlobalGet(_) | WasmOp::GlobalSet(_)))
        });
        let uses_call_indirect = locals.iter().any(|f| {
            f.ops
                .iter()
                .any(|op| matches!(op, WasmOp::CallIndirect { .. }))
        });
        let substrate = crate::substrate::plan(
            &crate::substrate::PlanInputs::from_module(module)
                .with_usage(uses_globals, uses_call_indirect),
        )
        .map_err(|e| BackendError::CompilationFailed(format!("aarch64: {e}")))?;

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
                // #851 lane L3: the substrate metadata + the fail-safe gate.
                // `emitted` is true only when `plan` produced a region that the
                // ELF build below actually places.
                a64_substrate_emitted: substrate.emitted,
                call_indirect_guards: module.call_indirect_guards(),
                type_class_ids: module.structural_type_class_ids(),
                type_arg_counts: module.type_arg_counts.clone(),
                type_result_counts: module.type_result_counts.clone(),
                type_ret_f32: module.type_ret_f32.clone(),
                type_ret_f64: module.type_ret_f64.clone(),
                global_widths: module.globals.iter().map(|g| g.slot_bytes).collect(),
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
            elf_funcs.push(ElfFunction::code(
                aliases,
                compiled.code.clone(),
                compiled.relocations.clone(),
            ));
            functions.push(compiled);
        }

        // #851 lane L3: the funcref table goes LAST in `.text`, so every real
        // function keeps the offset it had before the table existed.
        if let Some(table) = substrate.table {
            elf_funcs.push(table);
        }
        let elf = elf::build_relocatable_object_with_data(&elf_funcs, &substrate.globals);
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
