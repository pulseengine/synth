//! ARM Backend — wraps the instruction selector + optimizer + encoder as a Backend
//!
//! This is Synth's custom ARM compiler targeting Cortex-M (Thumb-2).
//! It's the only backend that supports per-rule formal verification (ASIL D path).

use crate::ArmEncoder;
use synth_core::backend::{
    Backend, BackendCapabilities, BackendError, CodeRelocation, CompilationResult, CompileConfig,
    CompiledFunction, LineMap, SafetyBounds,
};
use synth_core::target::{IsaVariant, TargetSpec};
use synth_core::wasm_decoder::DecodedModule;
use synth_core::wasm_op::WasmOp;
use synth_synthesis::{
    ArmInstruction, ArmOp, BoundsCheckConfig, InstructionSelector, OptimizationConfig,
    OptimizerBridge, RuleDatabase, validate_instructions,
};

/// ARM Cortex-M backend using Synth's custom compiler pipeline
pub struct ArmBackend;

impl ArmBackend {
    pub fn new() -> Self {
        Self
    }
}

impl Default for ArmBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for ArmBackend {
    fn name(&self) -> &str {
        "arm"
    }

    fn capabilities(&self) -> BackendCapabilities {
        BackendCapabilities {
            produces_elf: false,
            supports_rule_verification: true,
            supports_binary_verification: true,
            is_external: false,
        }
    }

    fn supported_targets(&self) -> Vec<TargetSpec> {
        vec![
            TargetSpec::cortex_m3(),
            TargetSpec::cortex_m4(),
            TargetSpec::cortex_m4f(),
            TargetSpec::cortex_m7(),
            TargetSpec::cortex_m7dp(),
        ]
    }

    fn compile_module(
        &self,
        module: &DecodedModule,
        config: &CompileConfig,
    ) -> Result<CompilationResult, BackendError> {
        let exports: Vec<_> = module
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
        for func in &exports {
            let name = func.export_name.clone().unwrap();
            // #359: copy THIS function's declared param widths into the config so
            // `compile_function` (which carries no function index) can refuse a
            // 64-bit param on the AAPCS stack-argument path. Cheap clone only when
            // a signature table is present and this function has a width entry —
            // otherwise reuse the shared config (every existing module unchanged).
            // #509: same per-function pattern for the blocktype-arity side-table
            // (value-carrying-branch lowering).
            let params = config
                .func_params_i64
                .get(func.index as usize)
                .filter(|p| !p.is_empty());
            // #457: THIS function's DECLARED param count (imports-first full
            // index), so the backend can cap the access-pattern inference that
            // mistook a read-before-write local for a param. `None` when the
            // driver supplied no arg-count table (hand-built modules).
            let declared_params = config.func_arg_counts.get(func.index as usize).copied();
            // GI-FPU-002 (#619/#369): THIS function's declared f32-param mask.
            let params_f32 = config
                .func_params_f32
                .get(func.index as usize)
                .filter(|p| !p.is_empty());
            // GI-FPU-002 phase 2 (#369): THIS function's declared f64-param
            // mask (hard-float targets decline f64 params loudly).
            let params_f64 = config
                .func_params_f64
                .get(func.index as usize)
                .filter(|p| !p.is_empty());
            // GI-FPU-002 phase 2 (#719/#369): THIS function's declared f32/f64
            // return flag, so the epilogue soundness guard fires on every driver
            // path (not only the CLI loops).
            let ret_f32 = config
                .func_ret_f32
                .get(func.index as usize)
                .copied()
                .unwrap_or(false);
            let ret_f64 = config
                .func_ret_f64
                .get(func.index as usize)
                .copied()
                .unwrap_or(false);
            let func_config = if params.is_some()
                || params_f32.is_some()
                || params_f64.is_some()
                || !func.block_arity.is_empty()
                || declared_params.is_some()
                || ret_f32
                || ret_f64
            {
                Some(CompileConfig {
                    current_func_params_i64: params.cloned().unwrap_or_default(),
                    current_func_params_f32: params_f32.cloned().unwrap_or_default(),
                    current_func_params_f64: params_f64.cloned().unwrap_or_default(),
                    current_func_ret_f32: ret_f32,
                    current_func_ret_f64: ret_f64,
                    current_func_block_arity: func.block_arity.clone(),
                    current_func_param_count: declared_params,
                    ..config.clone()
                })
            } else {
                None
            };
            let cfg = func_config.as_ref().unwrap_or(config);
            let compiled = self.compile_function(&name, &func.ops, cfg)?;
            functions.push(compiled);
        }

        Ok(CompilationResult {
            functions,
            elf: None,
            backend_name: self.name().to_string(),
        })
    }

    fn compile_function(
        &self,
        name: &str,
        ops: &[WasmOp],
        config: &CompileConfig,
    ) -> Result<CompiledFunction, BackendError> {
        let (code, relocations, line_map, branch_map, final_instrs) =
            compile_wasm_to_arm(ops, config).map_err(BackendError::CompilationFailed)?;

        // #778: derive the SOUND static WCET bound from the final Thumb-2 stream.
        // Only present for the Thumb-2 path; the core class (from the triple)
        // decides whether the bound is sound (M3/M4) or declined (M7). Phase 2:
        // any --wcet-hints entry for THIS function is verified (never trusted)
        // by the loop analyzer.
        let wcet = final_instrs.map(|instrs| {
            let hints = config
                .wcet_hints
                .as_ref()
                .and_then(|h| h.functions.get(name));
            crate::wcet::function_wcet_with_hints(name, &instrs, &config.target.triple, hints)
        });

        Ok(CompiledFunction {
            name: name.to_string(),
            code,
            wasm_ops: ops.to_vec(),
            relocations,
            line_map,
            branch_map,
            wcet,
        })
    }

    fn is_available(&self) -> bool {
        true // Always available — it's a library backend
    }
}

/// Count the number of function parameters by analyzing LocalGet patterns
fn count_params(wasm_ops: &[WasmOp]) -> u32 {
    let mut first_access: std::collections::HashMap<u32, bool> = std::collections::HashMap::new();
    for op in wasm_ops {
        match op {
            WasmOp::LocalGet(idx) => {
                first_access.entry(*idx).or_insert(true);
            }
            WasmOp::LocalSet(idx) | WasmOp::LocalTee(idx) => {
                first_access.entry(*idx).or_insert(false);
            }
            _ => {}
        }
    }

    first_access
        .iter()
        .filter_map(
            |(&idx, &is_read_first)| {
                if is_read_first { Some(idx + 1) } else { None }
            },
        )
        .max()
        .unwrap_or(0)
}

/// #539: fold the `i32.const 0; memory.grow m` idiom to `memory.size m`.
/// `memory.grow(0)` always succeeds and returns the current page count (WASM
/// Core §4.4.7), which is exactly `memory.size`; the fixed-memory backend
/// otherwise emits a constant `-1` for every `memory.grow`, so the legal
/// `memory.grow(0)` "read/validate current size" idiom wrongly reported failure.
/// Only the ADJACENT const-0 delta is folded (a non-zero delta keeps the sound
/// `-1` — fixed memory genuinely cannot grow; a runtime-computed 0 is a
/// documented follow-up). Backend- and path-agnostic: `memory.size` reads the
/// runtime memory-size register on every selector, so this fixes the optimized
/// and direct paths at once.
fn rewrite_memory_grow_zero(wasm_ops: &[WasmOp]) -> Vec<WasmOp> {
    let mut out = Vec::with_capacity(wasm_ops.len());
    let mut i = 0;
    while i < wasm_ops.len() {
        if matches!(wasm_ops[i], WasmOp::I32Const(0))
            && let Some(WasmOp::MemoryGrow(m)) = wasm_ops.get(i + 1)
        {
            out.push(WasmOp::MemorySize(*m));
            i += 2;
        } else {
            out.push(wasm_ops[i].clone());
            i += 1;
        }
    }
    out
}

/// #509: does the op stream contain a `br`/`br_if`/`br_table` that CARRIES a
/// value — i.e. one targeting a result-typed block/if (forward edge with
/// results > 0) or a parameterized loop header (backward edge with loop
/// params > 0)?
///
/// The optimized path's wasm→IR lowering drops the carried value on such
/// edges (the taken arm returns the fall-through result — same class as the
/// #507 `br_table` drop, observed on `pick_br`/`pick_br_fall`), so — like
/// #507 — the shape is detected on the raw op stream and routed to the direct
/// selector, whose #509 designated-result-register lowering lands the value
/// correctly. `block_arity` is the decoder's ordinal blocktype-arity
/// side-table; when it is empty (hand-built op streams) every block reads as
/// void and this never fires, keeping the optimized path byte-identical for
/// every existing caller. Frozen-safe for the same reason as #507: the frozen
/// fixtures compile `--relocatable` (already direct), and no optimized-path
/// fixture branches to a result-typed block.
fn has_value_carrying_branch(wasm_ops: &[WasmOp], block_arity: &[(u8, u8)]) -> bool {
    // Open control constructs: (is_loop, params, results), innermost last.
    let mut open: Vec<(bool, u8, u8)> = Vec::new();
    let mut ctrl_ord = 0usize;
    // A branch edge carries a value when its target is a result-typed forward
    // join (block/if) or a parameterized loop header.
    let carries = |open: &[(bool, u8, u8)], depth: u32| -> bool {
        let Some(&(is_loop, params, results)) = open
            .len()
            .checked_sub(1 + depth as usize)
            .and_then(|i| open.get(i))
        else {
            return false; // function-level target — handled by Return lowering
        };
        if is_loop { params > 0 } else { results > 0 }
    };
    for op in wasm_ops {
        match op {
            WasmOp::Block | WasmOp::If => {
                let (p, r) = block_arity.get(ctrl_ord).copied().unwrap_or((0, 0));
                ctrl_ord += 1;
                open.push((false, p, r));
            }
            WasmOp::Loop => {
                let (p, r) = block_arity.get(ctrl_ord).copied().unwrap_or((0, 0));
                ctrl_ord += 1;
                open.push((true, p, r));
            }
            WasmOp::End => {
                open.pop(); // None only at the function-level end — harmless
            }
            WasmOp::Br(d) | WasmOp::BrIf(d) if carries(&open, *d) => return true,
            WasmOp::BrTable { targets, default }
                if targets
                    .iter()
                    .chain(std::iter::once(default))
                    .any(|d| carries(&open, *d)) =>
            {
                return true;
            }
            _ => {}
        }
    }
    false
}

/// Core compilation: WASM ops → ARM machine code bytes + relocations
///
/// Returns (code_bytes, relocations) where relocations record BL instructions
/// that target external symbols (e.g., `__meld_dispatch_import` for import calls).
type CompileArmOutput = (
    Vec<u8>,
    Vec<CodeRelocation>,
    LineMap,
    synth_core::backend::BranchMap,
    // #778: the SOUND static WCET result over the final Thumb-2 stream, computed
    // by `compile_function` (which knows the function name); `None` for the A32
    // path. Purely additive metadata — does not touch `code`.
    Option<Vec<synth_synthesis::ArmInstruction>>,
);

fn compile_wasm_to_arm(
    wasm_ops: &[WasmOp],
    config: &CompileConfig,
) -> Result<CompileArmOutput, String> {
    // #539: `memory.grow(0)` must return the CURRENT page count, not the
    // fixed-memory `-1` sentinel — growing by zero pages can never fail (WASM
    // Core §4.4.7), so a guest doing `if (memory.grow(0) < 0) trap;` wrongly
    // faulted. Every lowering path emitted a delta-agnostic `-1`. `memory.grow(0)`
    // is semantically identical to `memory.size`, which the backend already
    // computes from the runtime memory-size register (R10 >> 16 = pages), so fold
    // the `i32.const 0; memory.grow` idiom to `memory.size` up front — backend-
    // and path-agnostic. A non-zero delta keeps `-1` (fixed memory genuinely
    // cannot grow); a runtime delta that happens to be 0 is the documented
    // follow-up.
    let rewritten = rewrite_memory_grow_zero(wasm_ops);
    // #494 phase 2b: the fact-spec guard-elision marks are keyed by op index
    // into the stream the DRIVER handed us. The memory.grow(0) fold above can
    // only shift indices AT OR AFTER a `memory.grow` — an op the fact-spec
    // walk never crosses (it stops at the first untracked op, so no mark can
    // follow one). Defense in depth: if the fold fired at all, drop the marks
    // loudly rather than risk keying a guard elision to the wrong op.
    let (fact_div_zero_elide, fact_div_ovf_elide, fact_mem_bounds_elide): (
        &[usize],
        &[usize],
        &[usize],
    ) = if rewritten.len() == wasm_ops.len() {
        (
            &config.fact_div_zero_elide,
            &config.fact_div_ovf_elide,
            &config.fact_mem_bounds_elide,
        )
    } else {
        if !config.fact_div_zero_elide.is_empty()
            || !config.fact_div_ovf_elide.is_empty()
            || !config.fact_mem_bounds_elide.is_empty()
        {
            eprintln!(
                "fact-spec: DECLINE guard elision marks dropped — the                      memory.grow(0) fold shifted op indices (#494 defensive gate);                      general lowering emitted"
            );
        }
        (&[], &[], &[])
    };
    let wasm_ops: &[WasmOp] = &rewritten;

    // #457: `count_params` INFERS the param count from access patterns (a local
    // whose first access is a read is assumed to be a param), so a
    // read-before-write NON-PARAM local — which WASM zero-initializes — was
    // indistinguishable from a param: it got homed in a parameter register and
    // read caller garbage instead of 0. When the driver supplied the DECLARED
    // count (`current_func_param_count`, from the module's type section), cap
    // the inference with it. `min` (not a plain override) keeps every function
    // whose inference is <= declared byte-identical: the inferred count can only
    // EXCEED the declared one via a read-first local index >= the declared count
    // — i.e. exactly the read-before-write locals this issue is about.
    let inferred_params = count_params(wasm_ops);
    let num_params = match config.current_func_param_count {
        Some(declared) => inferred_params.min(declared),
        None => inferred_params,
    };
    // A read-before-write non-param local exists iff the capped count dropped.
    // Such locals need the wasm-mandated zero-init, which only the direct
    // selector emits — the optimized path's `ir_to_arm` maps a non-param
    // local's vreg onto an r4+ temp with no initialization (caller garbage).
    let has_rbw_local = num_params < inferred_params;

    let bounds_config = match config.effective_safety_bounds() {
        SafetyBounds::None => BoundsCheckConfig::None,
        SafetyBounds::Mpu => BoundsCheckConfig::Mpu,
        SafetyBounds::Software => BoundsCheckConfig::Software,
        SafetyBounds::Mask => {
            // #651 (mirroring the RISC-V backend's compile-time decline):
            // index masking wraps `ea & (size-1)` — a modulo only when the
            // linear-memory size is a power of two. With a non-power-of-two
            // size the AND would silently REMAP in-bounds addresses (e.g.
            // 0x18000 & 0x2FFFF = 0x8000 for a 192 KiB memory). Decline
            // loudly rather than miscompile. `linear_memory_bytes == 0`
            // means "unknown" (plain per-function path, no module context)
            // — the startup default of one 64 KiB page is a power of two.
            let bytes = config.linear_memory_bytes;
            if bytes != 0 && !bytes.is_power_of_two() {
                return Err(format!(
                    "--safety-bounds mask requires a power-of-two linear-memory \
                     size, got {bytes} bytes — switch to --safety-bounds software \
                     for the deterministic check (#651)"
                ));
            }
            BoundsCheckConfig::Masking
        }
    };

    // The non-optimized (direct) instruction-selection path. Handles f32 via
    // VFP/FPU. Used directly when `--no-optimize` is set, and as the fallback
    // when the optimized path declines a module (see issue #120 below).
    //
    // VCR-RA-001 step 3b-lite (#242): a FRESH selector per attempt, with
    // `spill_on_exhaustion` set only on the retry — the first pass is the
    // unmodified default, so every function that compiles today is selected by
    // exactly the code that compiled it yesterday (bit-identity is structural,
    // not behavioural).
    let select_direct_attempt = |spill_on_exhaustion: bool,
                                 param_backing_on_exhaustion: bool,
                                 local_promote: bool,
                                 i64_spill_slots: Option<usize>|
     -> Result<Vec<ArmInstruction>, synth_core::Error> {
        let db = RuleDatabase::with_standard_rules();
        let mut selector =
            InstructionSelector::with_bounds_check(db.rules().to_vec(), bounds_config);
        selector.set_target(config.target.fpu, &config.target.triple);
        if config.num_imports > 0 {
            selector.set_num_imports(config.num_imports);
        }
        // #195: plumb the callee argument-count tables so the direct selector can
        // marshal call arguments into R0–R3 per AAPCS.
        selector.set_func_arg_counts(
            config.func_arg_counts.clone(),
            config.type_arg_counts.clone(),
        );
        // #197: in relocatable host-link mode, emit direct `func_N` BLs for
        // imports (rewritten to the wasm field name by build_relocatable_elf)
        // instead of `__meld_dispatch_import`.
        selector.set_relocatable(config.relocatable);
        // #642: call_indirect guard inputs (compile-time table size for the
        // bounds guard + closed-world type verdicts). Without them, every
        // call_indirect lowering declines loudly.
        selector.set_call_indirect_guards(config.call_indirect_guards.clone());
        // #275: on the self-contained image path (NOT --relocatable) the R11
        // funcref-table dispatch is a silent miscompile — the region is only
        // populated by an external runtime, which a self-contained ELF does
        // not have, so the dispatch would read function pointers from
        // linear-memory data. Two outcomes:
        //  - the Thumb-2 `--cortex-m` image path (CLI-flagged: the builder
        //    that emits and patches the flash-resident funcref table will
        //    run) lowers call_indirect through that table, PC-relative,
        //    never via R11;
        //  - every OTHER self-contained configuration (A32/Cortex-R5, the
        //    simple-ELF builder, imports present) keeps the loud decline.
        // The host-linked (--relocatable) path keeps the guarded R11
        // dispatch: there a runtime places the table region at R11.
        let self_contained_table = config.self_contained_funcref_table
            && matches!(config.target.isa, IsaVariant::Thumb2 | IsaVariant::Thumb);
        selector
            .set_reject_self_contained_call_indirect(!config.relocatable && !self_contained_table);
        selector.set_self_contained_funcref_table(self_contained_table);
        // #237: native-pointer ABI — wasm statics become __synth_wasm_data-relative.
        selector.set_native_pointer_abi(config.native_pointer_abi, config.linear_memory_bytes);
        // VCR-MEM-002 phase 1 (#406): per-memory initial page counts — enables
        // the multi-memory arms (memory-0 lowering never reads it; empty ⇒
        // every multi-memory op declines loudly).
        selector.set_memory_pages(config.memory_pages.clone());
        // #311: i64 call results are register PAIRS — tag them.
        selector.set_result_types(config.func_ret_i64.clone(), config.type_ret_i64.clone());
        // #359: declared param widths of THIS function, so the AAPCS stack-arg
        // path can refuse 64-bit params (Ok-or-Err). Empty ⇒ assume i32.
        selector.set_params_i64(config.current_func_params_i64.clone());
        // GI-FPU-002 (#619/#369): declared f32-param mask — home hard-float f32
        // args in S0..S15 (AAPCS-VFP) instead of the R0..R3 integer path.
        selector.set_params_f32(config.current_func_params_f32.clone());
        // GI-FPU-002 phase 2 (#369): declared f64-param mask — hard-float
        // targets decline f64-param functions loudly (no D-register homing yet).
        selector.set_params_f64(config.current_func_params_f64.clone());
        // GI-FPU-002 phase 2 (#719/#369): THIS function's f32/f64 return flag, so
        // the epilogue loudly declines a float result reaching it in a core
        // register (never a silent integer R0 return where a caller reads S0/D0).
        selector.set_ret_float(config.current_func_ret_f32, config.current_func_ret_f64);
        // GI-FPU-002 phase 3 (#369): per-callee float-signature tables. `Call`
        // marshals the AAPCS-VFP boundary from these (float args into S0../D0..,
        // float results out of S0/D0); `CallIndirect` still declines a
        // float-returning static type loudly.
        selector.set_float_call_signatures(
            config.func_ret_f32.clone(),
            config.func_ret_f64.clone(),
            config.type_ret_f32.clone(),
            config.type_ret_f64.clone(),
            config.func_params_f32.clone(),
            config.func_params_f64.clone(),
        );
        // #509: blocktype-arity side-table of THIS function, so value-carrying
        // br/br_if/br_table land the carried value in the target block's
        // designated result register instead of dropping it. Empty ⇒ legacy
        // void-block lowering.
        selector.set_block_arity(config.current_func_block_arity.clone());
        // Stack-pointer promotion is meaningful only under the native-pointer ABI;
        // gating here keeps every non-native compile (all frozen fixtures) on the
        // legacy R9 globals-table path, bit-identical.
        if config.native_pointer_abi
            && let Some((sp_idx, sp_init)) = config.stack_pointer_global
        {
            selector.set_native_pointer_stack(sp_idx, sp_init);
        }
        // #643: per-global slot widths — i64/f64 globals occupy 8-byte slots
        // (register-pair store/load) and shift every later global's offset.
        // Empty for i32-only modules ⇒ the legacy `idx * 4` layout, unchanged.
        selector.set_global_widths(config.global_widths.clone());
        selector.set_spill_on_exhaustion(spill_on_exhaustion);
        selector.set_param_backing_on_exhaustion(param_backing_on_exhaustion);
        // #587 pool-grow rung: a larger i64 spill-slot pool, set ONLY on the
        // retry after an attempt failed with the slot-pool-exhausted Err —
        // functions that compile with the default pool keep their frame
        // byte-identical by construction.
        if let Some(slots) = i64_spill_slots {
            selector.set_i64_spill_slots(slots);
        }
        // VCR-RA local promotion (#390, #242): keep eligible non-param i32 locals
        // in callee-saved registers instead of frame slots — the structural lever
        // toward native parity. DEFAULT-ON as of v0.14.0: gale's G474RE DWT gate
        // cleared it as a net win (gust_mix dissolved 58→50 cyc/call −14%, all 5
        // stack spill/reloads eliminated, correctness bit-identical over [0,2047],
        // 2.00×→1.72× vs LLVM). Escape hatch: `SYNTH_NO_LOCAL_PROMOTE=1` restores
        // the frame-slot path. Leaf-only / i32-only / ARM-only (see
        // compute_local_promotion); the leaf-only lift + i64 locals are follow-ons.
        // #474: `local_promote` is now a per-attempt parameter so the retry ladder
        // can drop promotion as an exhaustion-recovery rung (promotion pins r4-r8,
        // which on a dense function leaves the spill allocator with nothing to
        // free → the frame-slot path is the escape that restores compilability).
        selector.set_local_promote(local_promote);
        // #494 phase 2b: certificate-discharged div/rem trap-guard elision
        // marks (empty in every compile without SYNTH_FACT_SPEC + facts).
        selector
            .set_fact_div_guard_elisions(fact_div_zero_elide.to_vec(), fact_div_ovf_elide.to_vec());
        // #494 bounds-elision: certificate-discharged memory bounds-guard
        // marks (empty in every compile without SYNTH_FACT_SPEC + facts).
        selector.set_fact_mem_bounds_elisions(fact_mem_bounds_elide.to_vec());
        selector.select_with_stack(wasm_ops, num_params)
    };
    let select_direct = || -> Result<Vec<ArmInstruction>, String> {
        const SINGLE_EXHAUSTION: &str = "all allocatable registers are live on the stack";
        const PAIR_EXHAUSTION: &str = "no consecutive pair of free registers for i64";
        const SLOT_EXHAUSTION: &str = "i64 spill-slot pool exhausted";
        // The full exhaustion-recovery ladder, parameterized on whether local
        // promotion is enabled. Each rung is reached only when the previous one
        // returned a recoverable register-exhaustion Err, so a function that
        // compiles on the first attempt is untouched by the later rungs. Returns
        // the result AND which rung produced it (for the #242 measurement below).
        let recovery_ladder =
            |promote: bool,
             i64_spill_slots: Option<usize>|
             -> (Result<Vec<ArmInstruction>, synth_core::Error>, &'static str) {
                let mut attempt = select_direct_attempt(false, false, promote, i64_spill_slots);
                let mut rung = "base";
                // VCR-RA-001 step 3b-lite (#242): the i32 register-exhaustion
                // hard-fail is recoverable — retry with spill-on-exhaustion, which
                // reserves the spill area and spills the deepest stack value when
                // the pool is full.
                if let Err(e) = &attempt
                    && e.to_string().contains(SINGLE_EXHAUSTION)
                {
                    attempt = select_direct_attempt(true, false, promote, i64_spill_slots);
                    rung = "spill";
                }
                // VCR-RA-001 acceptance increment (#242): the i64 consecutive-PAIR
                // exhaustion is recoverable too — not by stack spilling (the pair
                // allocator already spills stack values, #171) but by frame-backing
                // the params (#204) so they stop pinning R0-R3, with spill kept on.
                if let Err(e) = &attempt
                    && e.to_string().contains(PAIR_EXHAUSTION)
                {
                    attempt = select_direct_attempt(true, true, promote, i64_spill_slots);
                    rung = "param-backing";
                }
                (attempt, rung)
            };
        // #474: local promotion (default-on since v0.14.0) is an OPTIMIZATION — it
        // must never be the reason a function fails to compile. Run the full ladder
        // with promotion first (so every function that compiles today is
        // bit-identical), and if it still ends in register exhaustion, fall back to
        // the promotion-off ladder (the v0.12.0 frame-slot lowering — exactly what
        // the `SYNTH_NO_LOCAL_PROMOTE=1` workaround does, now automatic). Promotion
        // pins r4-r8 for the locals; on a dense function that leaves the allocator
        // with nothing to free, so dropping it restores compilability. The fallback
        // is reached ONLY by functions that exhaust WITH promotion, so promotion-on
        // output is untouched by construction (frozen byte gate stays green).
        let promote = std::env::var("SYNTH_NO_LOCAL_PROMOTE").is_err();
        // The full pre-#587 recovery sequence (promotion-on ladder, then the
        // #474 promotion-off fallback), parameterized on the pool size so the
        // pool-grow retry below reruns it verbatim.
        let full_sequence = |slots: Option<usize>| -> (
            Result<Vec<ArmInstruction>, synth_core::Error>,
            &'static str,
            bool,
        ) {
            let (mut attempt, mut rung) = recovery_ladder(promote, slots);
            let mut promotion_dropped = false;
            if promote
                && attempt
                    .as_ref()
                    .err()
                    .is_some_and(|e| e.to_string().contains("register exhaustion"))
            {
                let (rescued, off_rung) = recovery_ladder(false, slots);
                if rescued.is_ok() {
                    attempt = rescued;
                    rung = off_rung;
                    promotion_dropped = true;
                }
            }
            (attempt, rung, promotion_dropped)
        };
        let (mut attempt, mut rung, mut promotion_dropped) = full_sequence(None);
        // #587 pool-grow retry (the falcon func_60/func_73 remainder): the fixed
        // 8-slot i64 spill pool can exhaust while spilling is otherwise working —
        // an i64-dense function simply has more values simultaneously live than
        // the pool holds. Rerun the ENTIRE sequence (every rung, both promotion
        // modes) with the pool sized from a conservative operand-stack-depth
        // bound: the number of simultaneously spilled values can never exceed
        // the operand-stack depth, plus a few transient slots (the arg-move
        // cycle resolver and call-result parking each borrow one). The selector
        // clamps the request to its 12-bit-friendly cap; a function that still
        // exhausts stays an honest loud skip. Deliberately LAST — after the #474
        // promotion-off fallback — so any function that compiled yesterday
        // (through any rung or fallback) is produced by exactly yesterday's
        // path, byte-identical; the grown pool only ever fires for functions
        // whose every existing escape ended in the slot-pool Err.
        if attempt
            .as_ref()
            .err()
            .is_some_and(|e| e.to_string().contains(SLOT_EXHAUSTION))
        {
            let depth = synth_core::wasm_stack_check::max_depth_bound(wasm_ops) as usize;
            let (grown, _, grown_dropped) = full_sequence(Some(depth.saturating_add(4)));
            if grown.is_ok() {
                attempt = grown;
                rung = "pool-grow";
                promotion_dropped = grown_dropped;
            }
        }
        // VCR-RA measurement (#242): log which recovery rung produced the result,
        // so the per-rung distribution across a corpus can be measured — the size
        // of the failure surface a verified allocator must subsume (see
        // scripts/repro/register_exhaustion_recovery_ladder.md). Logging only:
        // emitted bytes are unchanged, so the frozen byte gate is unaffected.
        if std::env::var("SYNTH_RECOVERY_STATS").is_ok() {
            eprintln!(
                "[recovery-stats] rung={rung}{} result={}",
                if promotion_dropped {
                    " promotion-off"
                } else {
                    ""
                },
                if attempt.is_ok() { "ok" } else { "exhausted" },
            );
        }
        attempt.map_err(|e| format!("instruction selection failed: {}", e))
    };

    // Instruction selection: optimized or direct.
    //
    // #197: `--relocatable` (host-link ET_REL) forces the direct selector. The
    // optimized path materializes an absolute linmem base (0x20000100) and does
    // not preserve caller-saved registers across calls — both wrong for a
    // host-linked object, where the linmem base arrives via `fp` at runtime and
    // callees follow AAPCS. `select_with_stack` (now i64-spill capable after
    // #171) handles fp-relative memory + caller-saved preservation correctly.
    //
    // #507: `br_table` is DROPPED during the optimized path's wasm→IR lowering
    // (`optimize_full`), so `ir_to_arm` never sees the dispatch — it emits the
    // arm bodies in fall-through sequence with no `cmp`/branch on the selector, a
    // SILENT miscompile (every input hits the last arm). The selector value isn't
    // even loaded. Because the drop happens before `ir_to_arm`, there's no `Err`
    // to fall back on; detect it on the raw wasm op stream here and force the
    // direct selector (`select_with_stack` lowers `br_table` correctly as a
    // cmp-chain — confirmed on the `--relocatable` path). Same honest-degradation
    // contract as the issue-#120 f32 decline: the function still compiles
    // correctly, just without IR-level optimization. Frozen-safe: the frozen
    // fixtures compile `--relocatable` (already direct), and no optimized-path
    // fixture (control_step, flight_algo) contains `br_table`.
    let has_br_table = wasm_ops
        .iter()
        .any(|op| matches!(op, WasmOp::BrTable { .. }));
    // #509: the optimized path also drops the value carried by a `br`/`br_if`
    // to a result-typed block (the taken edge returns the wrong arm's value —
    // same silent-miscompile class as the #507 br_table drop). Route the shape
    // to the direct selector, whose designated-result-register lowering (#509)
    // lands the carried value at the join. Never fires for void-block control
    // flow (all frozen/optimized fixtures), so those stay byte-identical.
    let has_value_carry = has_value_carrying_branch(wasm_ops, &config.current_func_block_arity);
    // #503-i64/#518: route any signature with a 64-bit (i64/f64) param to the
    // direct selector. The optimized path's param homing is width-naive — its
    // #518 decline covers only functions that READ an i64 param (an `I64Load`
    // from a param index), so a function that reads an i32 param whose AAPCS
    // home a preceding wide param SHIFTED (e.g. p1 of `(i64 i32)` lives in R2,
    // not R1; p3 of `(i64 i32 i32 i32)` lives on the stack, not in R3) was
    // silently miscompiled rather than falling back. The direct selector's
    // `aapcs_param_layout` homing handles every such shape (i64-param READS
    // already fell back to it via the ir_to_arm Err, so those functions emit
    // the same bytes as before). `num_params` counts read-first locals, so a
    // function that never touches any param keeps the optimized path.
    let has_wide_param = config
        .current_func_params_i64
        .iter()
        .take(num_params as usize)
        .any(|&w| w);
    // #782(b): a HARD-float (FPU) target passes f32 args in VFP S-registers
    // and returns floats in S0/D0 (AAPCS-VFP) — but the optimized path's
    // param/return homing is float-naive (integer R0..R3 args, R0 return). A
    // function whose ops ALL lower on the optimized path but whose SIGNATURE
    // carries a float — e.g. the pure value-pick
    // `(param f32 f32 i32) (result f32) select`, no float OP to trip the
    // issue-#120 ir_to_arm fallback — was silently compiled with the integer
    // ABI: callers marshal S0/S1, the body reads R0/R1. Route every
    // float-signature function to the direct selector (AAPCS-VFP homing, or
    // an honest decline). Soft-float targets (no FPU) keep the optimized
    // path: the integer treatment IS the ABI there — byte-identical. (f64
    // params already route direct via `has_wide_param`; this adds f32 params
    // and f32/f64 returns.)
    let has_float_sig = config.target.fpu.is_some()
        && (config.current_func_ret_f32
            || config.current_func_ret_f64
            || config
                .current_func_params_f32
                .iter()
                .take(num_params as usize)
                .any(|&f| f)
            || config
                .current_func_params_f64
                .iter()
                .take(num_params as usize)
                .any(|&f| f));
    // #494 phase 2b: div/rem guard-elision marks are consumed by the DIRECT
    // selector only — the optimized path's IR passes (const-fold/CSE/DCE)
    // renumber instructions, so an op-index-keyed mark cannot soundly survive
    // them. Route marked functions direct (the #507/#509 honest-degradation
    // pattern). Never fires without SYNTH_FACT_SPEC + facts + a discharged
    // obligation, so every existing compile keeps its path byte-identical.
    let has_fact_div_elide = !fact_div_zero_elide.is_empty()
        || !fact_div_ovf_elide.is_empty()
        // #494 bounds-elision: memory bounds-guard marks are direct-selector
        // keyed for the same reason (IR passes renumber instructions).
        || !fact_mem_bounds_elide.is_empty();
    // #643: the optimized path's global lowering is width-naive — `GlobalGet`/
    // `GlobalSet` are single-word `[R9, idx*4]` accesses, which (a) silently
    // dropped the high word of every i64 global and (b) mis-address every
    // global whose offset an earlier wide (i64/f64) slot shifted. When the
    // module has any wide global, route every global-touching function to the
    // direct selector, whose type-aware summed layout pairs the access (or
    // declines loudly). Modules with only 4-byte globals — every existing
    // fixture — keep the optimized path byte-identical.
    let has_wide_global_module = config.global_widths.iter().any(|&w| w > 4);
    let has_global_access = has_wide_global_module
        && wasm_ops
            .iter()
            .any(|op| matches!(op, WasmOp::GlobalGet(_) | WasmOp::GlobalSet(_)));
    // VCR-VER-001 (#242): `post_exhaust` scopes the post-exhaustion cleanup
    // extensions to functions whose bytes the #580 spill-on-exhaustion
    // machinery actually shaped (bridge-reported). Everything else — the
    // direct path, non-exhausted optimized functions — stays byte-identical
    // flag-on (the `vcr_ver_001_gate_242` lock's contract).
    let (arm_instrs, post_exhaust) = if config.no_optimize
        || config.relocatable
        || has_br_table
        || has_value_carry
        || has_wide_param
        || has_float_sig
        || has_global_access
        || has_fact_div_elide
        // #457: route read-before-write non-param locals to the direct
        // selector, whose prologue zero-init lands the wasm-mandated 0.
        || has_rbw_local
    {
        if std::env::var("SYNTH_PATH_DEBUG").is_ok() {
            eprintln!("[path-debug] direct (pre-gate)");
        }
        (select_direct()?, false)
    } else {
        let opt_config = if config.loom_compat {
            OptimizationConfig::loom_compat()
        } else {
            OptimizationConfig::all()
        };

        let mut bridge = OptimizerBridge::with_config(opt_config);
        // #188: tell the bridge how many imports there are so it declines only
        // LOCAL calls (and leaves import calls on the optimized path, keeping
        // the #173 field-name relocation rewrite intact).
        bridge.set_num_imports(config.num_imports);
        // #543 Phase 2: thread the integrator-marked volatile DMA-window ranges
        // (`--volatile-segment <base>:<len>`) to the bridge's address-caching
        // levers — base-CSE (#468) excludes any access inside a marked range
        // from its fold set, and the bridge-level const-CSE declines wholesale
        // while any range is marked. Empty (the default) ⇒ byte-identical.
        bridge.set_volatile_segments(config.volatile_segments.clone());
        // #377: thread `--safety-bounds` to the bridge. Pre-fix the optimized
        // path ignored it — `software`/`mask` were SILENT NO-OPS on the path
        // that lowers the bulk of a flight loop's i32 loads/stores (byte-
        // identical to `none`, while the safety manifest claimed otherwise).
        // `Software` now emits the inline guard per access; `Masking` declines
        // memory-accessing functions to the direct selector; `None`/`Mpu` are
        // byte-identical to before.
        bridge.set_bounds_check(bounds_config);
        // #687: thread the absolute linear-memory base the optimized path
        // materializes. Defaults to 0x2000_0100 (byte-identical);
        // `--stack-layout=low` shifts it up by the reserved stack size so
        // const-address accesses follow the moved linear memory.
        bridge.set_linmem_base(config.linmem_base);
        // `ir_to_arm` now returns `Result` — an `Err` means the optimized path
        // hit an unmapped vreg (issue-#93-class). Treat it identically to an
        // `optimize_full` failure: fall back to the direct selector rather
        // than propagating, so the function still compiles correctly.
        match bridge
            .optimize_full(wasm_ops)
            .and_then(|(opt_ir, _cfg, _stats)| bridge.ir_to_arm(&opt_ir, num_params as usize))
        {
            Ok(arm_ops) => {
                if std::env::var("SYNTH_PATH_DEBUG").is_ok() {
                    eprintln!("[path-debug] optimized (ir_to_arm ok)");
                }
                (
                    arm_ops
                        .into_iter()
                        .map(|op| ArmInstruction {
                            op,
                            source_line: None,
                        })
                        .collect(),
                    bridge.spill_on_exhaust_fired(),
                )
            }
            // Issue #120: the optimized path declines modules it cannot lower
            // (notably scalar f32/f64 ops — the IR has no float opcodes). Fall
            // back to the direct instruction selector, which handles f32 via
            // VFP/FPU. This is honest degradation: the function still compiles
            // correctly, just without IR-level optimization.
            Err(e) => {
                if std::env::var("SYNTH_PATH_DEBUG").is_ok() {
                    eprintln!("[path-debug] direct (fallback: {e})");
                }
                (select_direct()?, false)
            }
        }
    };

    // #257/#277: `mul`+`add`→`mla` fusion is intentionally NOT wired here.
    // The transform is correct and ready (`synth_synthesis::liveness::fuse_mul_add`,
    // fully tested), but it is **register-allocation-coupled**: over the current
    // greedy single-pass selector, folding `mul rM,..; add rD,rM,rX` → `mla`
    // extends the live ranges of the mul inputs to the mla point, and the added
    // pressure (extra moves/spills) costs more than the single-cycle MLA saves —
    // gale measured a +2 cyc on-target REGRESSION (flat_flight 255→257, G474RE)
    // even though it removes 2 instructions and the seam stays 0x07FDF307. So the
    // fusion stays unwired until the spill-aware allocator (VCR-RA-001) chooses
    // registers, at which point it becomes net-positive (per #272's plan and the
    // wiring design note). Lesson (#277): a register-pressure-affecting transform
    // needs an on-target/allocator-aware gate, not a byte-count gate, before it
    // can default on.

    // VCR-RA-001 const-CSE / rematerialization-avoidance (#209): moved to run
    // LAST, after the immediate-folds — see the apply_const_cse call below
    // (#242). Earlier it ran here (before range-realloc and the folds), which is
    // what let it grow gale's --relocatable `gust_mix` 90→92 B (#242 burndown,
    // 2026-06-26): retargeting a read defeated a *downstream* immediate-fold that
    // would otherwise have absorbed the constant. Running CSE-last makes those
    // foldable consts already-folded-and-gone, so CSE only ever touches genuinely
    // redundant materializations.

    // VCR-RA-001 RANGE RE-ALLOCATION (#209/#242, wiring step 3a) — the first
    // CONSEQUENTIAL allocator pass: re-colour each maximal straight-line
    // segment over the R0-R8 pool with value ranges as the allocation unit
    // (segment inputs + per-register live-outs pinned to their original
    // registers, reserved R9-R12/SP identity-assigned — each segment is
    // independently sound, no cross-segment liveness assumed). Renames
    // registers only: never adds, removes, or reorders instructions, so
    // labels/branch offsets are unaffected.
    //
    // DEFAULT-ON since v0.11.36: gale cleared the gate on-target (G474RE,
    // #209 2026-06-10) — flag-on output byte-identical to flag-off on
    // flat_flight/controller/control_step, fires on the filter family with
    // zero cycle delta and a small size win, all selfchecks green on silicon.
    // Opt out with `SYNTH_RANGE_REALLOC=0`; per-function stats with
    // `SYNTH_REALLOC_STATS=1`.
    //
    // The companion dead callee-saved-save elimination (gale's "next
    // consequential lever", same issue comment) then shrinks the prologue
    // `push {r4-r8,lr}` / epilogue `pop {r4-r8,pc}` to the callee-saved
    // registers the re-allocated body still touches (leaf-only,
    // SP-untouched, even-count-padded — see shrink_callee_saved_saves):
    // ~12 cycles of pure save/restore overhead removed on small leaves.
    let realloc_on = std::env::var("SYNTH_RANGE_REALLOC").map_or(true, |v| v != "0");
    let arm_instrs = if realloc_on {
        use synth_synthesis::rules::Reg;
        const POOL: [Reg; 9] = [
            Reg::R0,
            Reg::R1,
            Reg::R2,
            Reg::R3,
            Reg::R4,
            Reg::R5,
            Reg::R6,
            Reg::R7,
            Reg::R8,
        ];
        // VCR-VER-001 (#242): on a function the spill-on-exhaustion machinery
        // shaped, the terminal segment gets relaxed live-out pinning (only
        // R0/R1 are observable past `bx lr` at this pre-prologue position) so
        // the colourer can lower R4-R8-homed tails into caller-saved R0-R3 —
        // shrinking the `push {r4-r8,lr}` the #580 exhaustion shapes pay for.
        // `post_exhaust == false` selects the shipping pass bit for bit.
        let (out, stats) = synth_synthesis::liveness::reallocate_function_post_exhaust(
            &arm_instrs,
            &POOL,
            post_exhaust,
        );
        if std::env::var("SYNTH_REALLOC_STATS").is_ok() {
            eprintln!(
                "[range-realloc] {} segments: {} reallocated, {} declined ({} validator-rejected), {} need spill (step 4)",
                stats.segments,
                stats.reallocated,
                stats.declined,
                stats.validator_rejects,
                stats.needs_spill
            );
        }
        // VCR-RA-002 (#390, epic #242): eliminate a provably-dead stack frame
        // (`sub sp,#N`/`add sp,#N` reserved by `compute_local_layout` for locals
        // that promotion homed in registers, never accessed). Removing it saves
        // the two instructions AND restores the SP-untouched precondition that
        // `shrink_callee_saved_saves` requires — so it must run FIRST.
        // DEFAULT-ON (#242 flag audit flip-wave, #592 audit item): evidence
        // basis was the 2-path × repro-corpus sweep — 0 functions grow, 58
        // shrink (flight_seam controller_step 250→242 −8 / filter_step 180→168
        // −12, native_pointer frame_roundtrip 46→34 −12), locked by the
        // `dead_frame_elim_no_grow_corpus_242` cargo gate; execution
        // differentials re-run green on the new default bytes BEFORE the
        // frozen ARM anchors were re-pinned (leaf_dead_frame, flight_seam,
        // frame_slot_dce — see the flip PR). Escape hatch:
        // `SYNTH_DEAD_FRAME_ELIM=0` opts out and restores the pre-flip bytes
        // (CI-gated in `frozen_codegen_bytes.rs`).
        let out = if !std::env::var("SYNTH_DEAD_FRAME_ELIM").is_ok_and(|v| v == "0") {
            synth_synthesis::liveness::elide_dead_frame(&out).unwrap_or(out)
        } else {
            out
        };
        // #490 (epic #242): the optimized selector uses r4-r8 as scratch /
        // promoted locals but emits no prologue, silently clobbering a caller's
        // callee-saved registers. Add the missing `push {r4-r8,lr}` /
        // `pop {r4-r8,pc}` HERE — on the post-realloc body, where realloc has
        // lowered low-pressure r4-r8 scratch back to r0-r3, so a save is added
        // only for registers genuinely clobbered. `shrink_callee_saved_saves`
        // (next) then trims it to the used set. No-op on the direct path (it
        // already has its own prologue) and on callee-saved-free leaves.
        let out = synth_synthesis::liveness::ensure_callee_saved_prologue(&out);
        synth_synthesis::liveness::shrink_callee_saved_saves(&out).unwrap_or(out)
    } else {
        // Range-realloc off (`SYNTH_RANGE_REALLOC=0`): the optimized path still
        // must preserve the callee-saved registers it clobbers (#490). No shrink
        // (it is coupled to the realloc lever), so the conservative full save
        // stays — correct, just not minimised in this debug configuration.
        synth_synthesis::liveness::ensure_callee_saved_prologue(&arm_instrs)
    };

    // VCR-RA-001 SHADOW ALLOCATION (#209/#242): run the register allocator on
    // the selected stream and LOG what it finds — without changing a single
    // emitted byte. This is the measure-only bridge between the built analysis
    // layer and the eventual virtual-register wiring: it shows, per real
    // function, whether the allocator can colour it within the R0–R8 pool and
    // how much const-CSE / rematerialization headroom exists (#209). Enable with
    // `SYNTH_SHADOW_ALLOC=1`; off by default and side-effect-free either way.
    if std::env::var("SYNTH_SHADOW_ALLOC").is_ok() {
        use synth_synthesis::liveness::{
            AllocationOutcome, allocate_function, function_peak_pressure,
        };
        // R9 globals / R10 mem-size / R11 mem-base / R12 IP-scratch are reserved;
        // pin them above the 0..9 allocatable pool so the colourer keeps R0–R8.
        let precolored = std::collections::BTreeMap::from([
            (synth_synthesis::rules::Reg::R9, 9usize),
            (synth_synthesis::rules::Reg::R10, 10),
            (synth_synthesis::rules::Reg::R11, 11),
            (synth_synthesis::rules::Reg::R12, 12),
        ]);
        // True VALUE pressure (one node per value, not per reused physical reg):
        // a NeedsSpill with peak ≤ 9 is a SPURIOUS physical-register spill — the
        // function fits once virtually allocated.
        let peak = function_peak_pressure(&arm_instrs);
        match allocate_function(&arm_instrs, 9, &precolored) {
            AllocationOutcome::Allocated {
                remat_opportunities,
                coloring,
            } => eprintln!(
                "[shadow-alloc] OK: {} pregs coloured within R0-R8 pool, peak value-pressure {}, {} const-CSE/remat opportunities",
                coloring.len(),
                peak,
                remat_opportunities
            ),
            AllocationOutcome::NeedsSpill(s) => eprintln!(
                "[shadow-alloc] physical-graph would spill {:?}, but peak value-pressure is {} (≤9 ⇒ spurious; fits once virtually allocated)",
                s, peak
            ),
            AllocationOutcome::Declined => {
                eprintln!(
                    "[shadow-alloc] declined (unmodeled construct — calls/i64/fp/offset-branch)"
                )
            }
        }
    }

    // VCR-SEL-004 cmp→select → IT-block predication fusion (#242). The selector
    // lowers a `select` whose condition is a comparison to a *materialize then
    // re-test* sequence (`cmp a,b; SetCond D,c; cmp D,#0; movne dst,v1; moveq
    // dst,v2`); this collapses it onto the comparison's own flags — deleting the
    // `SetCond` and the `cmp D,#0` and retargeting the predicated moves to `c` /
    // `invert(c)` — yielding the textbook predicated clamp (`cmp a,b; movc dst,v1;
    // mov{!c} dst,v2`). −2 instructions per fused select. gale #428 measured this
    // as the #1 hot-path size/cycle lever on the gust_mix clamp chain.
    //
    // Run LATE: after range re-allocation (so the dead-D proof sees final register
    // identities) and before encode. Removal-only + rename-only ⇒ no spill
    // regression and labels/branch offsets are unaffected. Each fusion is proven
    // sound (flags reused only when nothing clobbers them in the window; the
    // boolean deleted only when provably dead) — see `fuse_cmp_select`.
    //
    // DEFAULT-ON as of v0.13.0 (#428): cmp→select fusion ships by default. The
    // byte-changing flip is validated by (a) the unicorn execution oracle that runs
    // the two-move `mov{invert(c)}` arm (cmp_select_two_move_differential.py), (b)
    // gale's gale_decider_diff 10,596-case sweep across all 8 verified primitives
    // (native ≡ flag-off ≡ flag-on = 0x88e73178d232bcf5), and (c) the named-anchor
    // differentials re-run with fusion ON — control_step still 0x00210A55, flat+
    // inlined flight_algo still 0x07FDF307 (results preserved; bytes deliberately
    // changed, re-frozen on this commit). Escape hatch: `SYNTH_NO_CMP_SELECT_FUSE=1`
    // reverts to the pre-fusion lowering. The on-silicon G474RE DWT no-regression
    // check is a tracked post-ship follow-up (gale owns it).
    let arm_instrs = if std::env::var("SYNTH_NO_CMP_SELECT_FUSE").is_err() {
        // The rewritten stream is identical to `fuse_cmp_select`'s 2-tuple form;
        // the extra `two_move` count is diagnostic only (the fusion census /
        // blast-radius datum — #7 made that arm reachable).
        let (out, fused, two_move) =
            synth_synthesis::liveness::fuse_cmp_select_with_stats(&arm_instrs);
        if std::env::var("SYNTH_FUSE_STATS").is_ok() {
            let in_place = fused - two_move;
            eprintln!(
                "[cmp-select-fuse] {fused} select(s) fused to predicated moves \
                 ({two_move} two-move, {in_place} in-place)"
            );
        }
        out
    } else {
        arm_instrs
    };

    // Perf lever 1 toward native parity (#390): redundant stack-reload elimination.
    // synth lowers every wasm local to a frame slot, so `local.set; local.get` emits
    // `str rX,[sp,#N]; … ; ldr rY,[sp,#N]`; when rX still holds the value the reload
    // (a ~2-cycle M4 load) becomes `mov rY,rX`. Removal-of-a-load + rename only ⇒ no
    // new instruction form and no label/offset change. DEFAULT-ON (#242 feature
    // loop): validated bit-identical RESULTS on every frozen anchor (control_step
    // 0x00210A55 13/13, flat+inlined flight_algo 0x07FDF307) with .text reduced on
    // the shipped --relocatable path, plus 8 unit tests + the frame_slot_dce
    // execution differential — the same gated path cmp→select took to default-on in
    // v0.13.0 (G474RE silicon confirms perf post-ship). Escape hatch:
    // `SYNTH_NO_STACK_FWD=1` restores the frame-resident bytes (frozen-old goldens).
    let stack_fwd = std::env::var("SYNTH_NO_STACK_FWD").is_err();
    let arm_instrs = if stack_fwd {
        let (out, fwd) = synth_synthesis::liveness::forward_stack_reloads(&arm_instrs);
        if std::env::var("SYNTH_FUSE_STATS").is_ok() {
            eprintln!("[stack-fwd] {fwd} stack reload(s) forwarded to register moves");
        }
        out
    } else {
        arm_instrs
    };

    // VCR-RA frame-slot DCE (#242): once `forward_stack_reloads` has turned the
    // reloads of a spill slot into register moves, the `str rX,[sp,#N]` that fed
    // them is a dead store — its slot is never loaded again. Remove it. Pairs
    // with (and only pays after) stack-reload forwarding, so it shares the flag.
    let arm_instrs = if stack_fwd {
        let (out, n) = synth_synthesis::liveness::eliminate_dead_frame_stores(&arm_instrs);
        if std::env::var("SYNTH_FUSE_STATS").is_ok() {
            eprintln!("[frame-slot-dce] {n} dead frame store(s) removed");
        }
        out
    } else {
        arm_instrs
    };

    // VCR-RA-001 spill re-choice (#242), two stages behind one flag.
    // Stage 1 (the #569 spike): slot-value forwarding BETWEEN reloads.
    // `forward_stack_reloads` (above) forwards only from a spill store's
    // SOURCE register, so when register pressure clobbers that source its
    // reloads survive; this stage tracks which registers provably still hold
    // a frame slot's value (through earlier reloads and reg-reg moves) and
    // turns reload #2..#n into a 1-cycle `mov` (or deletes it when the target
    // already holds the value). Stage 2 (the Belady re-choice): where NO
    // register still holds the value — the genuine-spill case, flat_flight's
    // peak-11 hot segment — the value was usually evicted while a dead
    // register existed; the clobbering def(s) are renamed onto a provably-dead
    // register (`spill_rechoice_segment`) so the value stays resident and the
    // reload dissolves outright. A dissolved reload can leave the feeding
    // store dead, so the frame-slot DCE sweep runs once more behind the same
    // flag. Per-segment commit gates: executable same-value-flow trace
    // equality, strict shrink, pool-pressure fit, sub-word/unknown-slot
    // conservatism (see `apply_spill_realloc` / `spill_rechoice_segment`).
    // Stage 3 (whole-function slot liveness): the segment-local DCE keeps a
    // store whose slot reaches function end ("reach-end ≠ dead" — it cannot
    // see other segments); `eliminate_unread_frame_stores` walks the whole
    // function (labels/branches/loops, SP-displacement tracked) and drops a
    // store whose slot NO reachable instruction can read — flat_flight's two
    // surviving stores (#576), completing Belady's 0-load side with a 0-store
    // side. Same flag: the three stages are one lever, flipped together.
    // DEFAULT-ON (#242 feature loop, the v0.14.0 local-promotion pattern):
    // Belady spilling ships by default. Evidence basis for the flip: three
    // landed flag-off increments (#569 forwarding, #576 Belady re-choice,
    // #579 whole-fn slot liveness), 40+ functions shrink / 0 grow across the
    // 68-fixture × 2-path sweep, per-segment executable value-trace equality
    // guards, and the unicorn-vs-wasmtime execution differentials re-run
    // green on the new default bytes (flat+inlined flight_algo 0x07FDF307,
    // const_cse, frame_slot_dce, spill_rung_581, r12_spill_496 — which covers
    // control_step_decide vs wasmtime; control_step's .text is byte-identical
    // under the flip) BEFORE the frozen goldens were re-pinned. Escape hatch:
    // `SYNTH_SPILL_REALLOC=0` is the OPT-OUT — it disables all three stages
    // and restores the pre-flip bytes (CI-gated by
    // `frozen_fixtures_spill_realloc_escape_hatch_restores_old_bytes`). Any
    // other value (or unset) runs the pass.
    // VCR-VER-001 post-exhaustion extensions (#242, the PR #659 verdict): with
    // `SYNTH_SPILL_ON_EXHAUST` active the #580 allocation-time Belady spill
    // keeps exhausted functions on the optimized path, and its slots present
    // shapes the shipping pass structurally cannot fire on (fresh-monotonic
    // slots defeat the overwrite-only DCE; the eviction store's source is
    // redefined immediately, defeating store→reload forwarding; R2/R3 are
    // never touched again, so the rename-target deadness proof declines them).
    // `post_exhaust` (bridge-scoped, see above) enables const
    // rematerialization of spilled constants, R2/R3 exit-dead rename targets,
    // and per-pair pressure commit — see `apply_spill_realloc_post_exhaust`.
    // Flag off (the default): `false` selects the shipping behavior bit for
    // bit.
    let arm_instrs = if !std::env::var("SYNTH_SPILL_REALLOC").is_ok_and(|v| v == "0") {
        let (out, n) =
            synth_synthesis::liveness::apply_spill_realloc_post_exhaust(&arm_instrs, post_exhaust);
        let (out, d) = synth_synthesis::liveness::eliminate_dead_frame_stores(&out);
        let (mut out, u) = synth_synthesis::liveness::eliminate_unread_frame_stores(&out);
        let (mut tn, mut td, mut tu) = (n, d, u);
        // Post-exhaustion only: iterate the triple to a bounded fixpoint. Each
        // dissolved spill pair frees registers and removes stores, exposing
        // rename windows and holder chains the previous iteration could not
        // prove — the allocation-time Belady slots (#580) routinely need two
        // or three rounds where the shipping single round suffices for the
        // default path's slots. Every iteration is individually gate-proven
        // (value-trace equality, pool pressure, strict shrink), so iterating
        // composes soundly; the bound keeps compile time deterministic.
        if post_exhaust {
            let mut progress = n + d + u > 0;
            for _ in 0..3 {
                if !progress {
                    break;
                }
                let (o, n) =
                    synth_synthesis::liveness::apply_spill_realloc_post_exhaust(&out, true);
                let (o, d) = synth_synthesis::liveness::eliminate_dead_frame_stores(&o);
                let (o, u) = synth_synthesis::liveness::eliminate_unread_frame_stores(&o);
                progress = n + d + u > 0;
                (tn, td, tu) = (tn + n, td + d, tu + u);
                out = o;
            }
            // The cleanup can leave the spill frame with zero surviving
            // accesses (every reload rematerialized/dissolved, every store
            // swept) — the balanced `sub sp,#K`/`add sp,#K` is then pure
            // overhead. `elide_dead_frame` proves that and removes the pair;
            // its early run (post-realloc) could not, because the spill
            // traffic was still in the stream at that point.
            out = synth_synthesis::liveness::elide_dead_frame(&out).unwrap_or(out);
        }
        if std::env::var("SYNTH_FUSE_STATS").is_ok() {
            eprintln!(
                "[spill-realloc] {tn} reload(s) forwarded/eliminated, {td} newly-dead frame store(s) removed, {tu} unread-slot store(s) removed"
            );
        }
        out
    } else {
        arm_instrs
    };

    // VCR-RA immediate-shift folding (#390, #242): a constant shift amount the
    // stack selector materialized into a scratch register (`movw rM,#C; lsl rD,rN,rM`)
    // folds to the immediate form (`lsl rD,rN,#C`), removing the dead `movw` — −1
    // instruction, −1 live register. Removal-only (offset-neutral before branch
    // resolution, like the dead-store pass). DEFAULT-ON as of v0.15.0: validated
    // bit-identical results + a net cycle win on the dissolved hot path (−2
    // cyc/call, .text 100→90 B on gust_mix). Escape hatch: `SYNTH_NO_IMM_SHIFT_FOLD=1`.
    let arm_instrs = if std::env::var("SYNTH_NO_IMM_SHIFT_FOLD").is_err() {
        let (out, folds) = synth_synthesis::liveness::fold_immediate_shifts(&arm_instrs);
        if std::env::var("SYNTH_FUSE_STATS").is_ok() {
            eprintln!(
                "[imm-shift-fold] {folds} register shift(s) folded to immediate, movw dropped"
            );
        }
        out
    } else {
        arm_instrs
    };

    // #686: elide the #682 mod-32 shift-amount mask (`and r12,rK,#31` before
    // every register-controlled i32 shl/shr) when the amount is STATICALLY
    // provable < 32 — a const amount folds to the immediate-shift form
    // (reduced mod 32, so >= 32 shrinks too), and an already-masked amount
    // (`rK = rX & c`, c < 32) drops the redundant re-mask. gale measured the
    // unconditional mask at ~12% cyc/call (+14 B) on gust_mix, whose Q8
    // fixed-point shifts are all constants (#686). The mask stays wherever
    // the bound is unproven — elision is an optimization, the mask is the
    // sound default (`liveness::elide_shift_masks` has the proof
    // obligations). Runs after `fold_immediate_shifts` (whose movw→shift
    // window the #682 mask intercepts, so it declines every masked const
    // shift) and before branch resolution (removal/rewrite-only ⇒
    // offset-neutral).
    //
    // FLAG-OFF (opt-in via `SYNTH_SHIFT_MASK_ELIDE=1`) because the elision
    // moves the frozen anchors: const-amount shifts in control_step (−20 B),
    // flight_seam (−164 B) and flight_seam_flat (−168 B) fold back to the
    // immediate form — byte-shapes the corpus had BEFORE the #682 mask, now
    // with the mask soundly kept for every unproven amount. Flipping
    // default-on is a deliberate byte-changing refreeze (all differentials
    // re-run on the new bytes, goldens re-pinned) owned by the maintainer.
    let arm_instrs = if std::env::var("SYNTH_SHIFT_MASK_ELIDE").is_ok_and(|v| v != "0") {
        let (out, elisions) = synth_synthesis::liveness::elide_shift_masks(&arm_instrs);
        if std::env::var("SYNTH_FUSE_STATS").is_ok() {
            eprintln!(
                "[shift-mask-elide] {elisions} provably-<32 shift-amount mask(s) elided (#686)"
            );
        }
        out
    } else {
        arm_instrs
    };

    // VCR-RA uxth/uxtb fold (#428, #242): `movw rM,#0xffff; and rD,rN,rM` →
    // `uxth rD,rN` (and the 0xff/uxtb form), removing the dead `movw` — −1
    // instruction, −1 live register per 16/8-bit mask. 0xffff/0xff are not Thumb-2
    // modified immediates so the selector materializes them into a register; the
    // dedicated zero-extend expresses the same masking inline. Removal-only +
    // rewrite-in-place (offset-neutral). DEFAULT-ON (#242 flag audit flip-wave,
    // #592 audit item): evidence basis was the 2-path × repro-corpus sweep —
    // 0 functions grow, 13 shrink (control_step 300→294 −6, gust_mix 38→32 −6,
    // uxth_fold pack 36→24 −12), locked by the `uxth_fold_no_grow_corpus_242`
    // cargo gate; execution differentials re-run green on the new default
    // bytes BEFORE the frozen ARM anchors were re-pinned (uxth_fold,
    // control_step — see the flip PR). Escape hatch: `SYNTH_UXTH_FOLD=0` opts
    // out and restores the pre-flip bytes (CI-gated in
    // `frozen_codegen_bytes.rs`).
    let arm_instrs = if !std::env::var("SYNTH_UXTH_FOLD").is_ok_and(|v| v == "0") {
        let (out, folds) = synth_synthesis::liveness::fold_uxth(&arm_instrs);
        if std::env::var("SYNTH_FUSE_STATS").is_ok() {
            eprintln!("[uxth-fold] {folds} mask-and folded to uxth/uxtb, movw dropped");
        }
        out
    } else {
        arm_instrs
    };

    // VCR-RA-001 const-CSE / rematerialization-avoidance (#209, #242). Drops a
    // `movw`/`mov #imm` that re-materializes a constant already resident in
    // another register and retargets the reads — every rewrite proven by the
    // liveness analysis. Runs LAST, after every immediate-fold (shift, uxth) and
    // range-realloc, but BEFORE branch resolution/encoding (it removes
    // instructions, shifting byte offsets). CSE-last is the #242 no-regression
    // fix: the folds have already absorbed every foldable constant, so CSE can no
    // longer defeat one (the gust_mix 90→92 mechanism). The pass additionally
    // size-guards each segment via the byte-estimator — it commits a segment's
    // rewrites only if they do not grow its estimated size — so a retarget that
    // would flip a 16-bit encoding to 32-bit (higher base register) is declined.
    // DEFAULT-ON (#242 flip-wave, the SYNTH_SPILL_REALLOC/SYNTH_BASE_CSE
    // template): const-CSE ships by default. The flip prerequisites recorded in
    // `const_cse_reduction_242.rs` were retired first — the bridge-level INLINE
    // aliasing (the alias-eviction spill-bijection hazard) was DELETED from
    // `optimizer_bridge::ir_to_arm`, so this post-hoc, liveness-proven pass is
    // the flag's ONLY effect. Evidence basis: 152 fixture×path corpus sweep — 0
    // functions grow (size-guarded per segment), 40 shrink (const_cse::spill12
    // 236→148 B), total −536 B — and the execution differentials re-run green
    // on the new default bytes BEFORE the frozen goldens were re-pinned
    // (const_cse, frame_slot_dce, flight_seam 0x07FDF307, spill_rung_581,
    // volatile_segment_543, control_step 0x00210A55). Escape hatch:
    // `SYNTH_CONST_CSE=0` is the OPT-OUT — it restores the pre-flip bytes
    // (CI-gated by `const_cse_escape_hatch_restores_old_bytes_242` and the
    // frozen-anchor escape-hatch gate). Any other value (or unset) runs the pass.
    //
    // #543 Phase 2: const-CSE declines WHOLESALE while any volatile DMA range
    // (`--volatile-segment`) is marked. At the ArmOp level a cached constant
    // cannot be classified as address-vs-data (a retargeted read may be a
    // memory-access base carrying a per-use immediate offset), so the
    // conservative stance for statically-unknown addressing is to decline every
    // aliasing rewrite — each constant is re-materialized at each occurrence,
    // the documented volatile contract (`CompileConfig::volatile_segments`).
    let arm_instrs = if !std::env::var("SYNTH_CONST_CSE").is_ok_and(|v| v == "0")
        && config.volatile_segments.is_empty()
    {
        let (out, removed) = synth_synthesis::liveness::apply_const_cse(&arm_instrs);
        if std::env::var("SYNTH_FUSE_STATS").is_ok() {
            eprintln!("[const-cse] {removed} redundant constant materialization(s) removed");
        }
        out
    } else {
        arm_instrs
    };

    // VCR-RA-001 spill-choice REPORT (#242): measure-only, like SYNTH_SHADOW_ALLOC.
    // Per straight-line segment, the frame-slot traffic actually emitted vs the
    // reload/store count a farthest-next-use (Belady) allocation over the R0-R8
    // pool would need — the measured headroom for the full spill-choice rewrite.
    // Printed on the FINAL stream (post all rewrite passes), so a flag-off run
    // reports the greedy baseline and a flag-on run reports what remains.
    if std::env::var("SYNTH_SPILL_REPORT").is_ok() {
        for seg in synth_synthesis::liveness::spill_choice_report(&arm_instrs, 9) {
            if seg.actual_reloads + seg.actual_spill_stores > 0 || seg.peak_pressure > 9 {
                eprintln!(
                    "[spill-report] seg@{} len={} peak={} actual={}ld+{}st belady(k=9)={}ld+{}st",
                    seg.start,
                    seg.len,
                    seg.peak_pressure,
                    seg.actual_reloads,
                    seg.actual_spill_stores,
                    seg.belady_reloads,
                    seg.belady_spill_stores
                );
            }
        }
    }

    // ISA feature gate: validate that all generated instructions are supported
    // by the target. This catches FPU instructions on no-FPU targets, double-precision
    // instructions on single-precision targets, etc.
    validate_instructions(&arm_instrs, config.target.fpu, &config.target.triple)
        .map_err(|e| format!("ISA validation failed: {}", e))?;

    // Encode to binary — use Thumb-2 for Cortex-M targets
    let use_thumb2 = matches!(config.target.isa, IsaVariant::Thumb2 | IsaVariant::Thumb);

    let encoder = if use_thumb2 {
        ArmEncoder::new_thumb2_with_fpu(config.target.fpu)
    } else {
        ArmEncoder::new_arm32()
    };

    // #202: resolve local label branches (Bcc/B/Bhs/Blo) to byte-accurate
    // offsets before encoding. `select_with_stack` emits them as label
    // placeholders and never resolves them — without this they encode as
    // `bne.n #0` and land mid-instruction whenever a 32-bit Thumb-2 instruction
    // sits between the branch and its target (UsageFault on real hardware).
    // Only meaningful for Thumb-2 (the offset units are halfword/PC+4).
    let arm_instrs = if use_thumb2 {
        resolve_label_branches(arm_instrs, &encoder)?
    } else {
        arm_instrs
    };

    // #778: capture the FINAL Thumb-2 instruction stream (post label-resolution,
    // the exact list the encode loop below consumes) so `compile_function` can
    // derive the sound WCET bound. Cheap clone; frozen-safe (the WCET walk is a
    // pure observation and never touches `code`). Only the Thumb-2 path — the A32
    // (Cortex-R5) cycle model is a follow-up.
    let final_instrs_for_wcet: Option<Vec<synth_synthesis::ArmInstruction>> = if use_thumb2 {
        Some(arm_instrs.clone())
    } else {
        None
    };

    let mut code = Vec::new();
    let mut relocations = Vec::new();

    // #345: literal-pool address loads. Each `LdrSym` was encoded as a placeholder
    // `LDR.W rd,[pc,#0]`; record where its instruction sits and what it loads so
    // we can append a pooled word (carrying the symbol address via R_ARM_ABS32)
    // and patch the PC-relative offset once the pool position is known.
    struct PendingLiteral {
        ldr_offset: u32,
        symbol: String,
        addend: i32,
    }
    let mut pending_literals: Vec<PendingLiteral> = Vec::new();

    // VCR-DBG-001: per-instruction source map for DWARF `.debug_line`. Captured
    // here because `code.len()` immediately before `encode()` is the final
    // machine offset of the instruction within this function's `.text` — nothing
    // after the loop shifts earlier instructions (the literal pool is appended at
    // the end; the LDR patch below is in-place/length-preserving). Purely
    // additive: it does not touch `code`, so `.text` is byte-identical.
    let mut line_map: LineMap = Vec::new();
    // VCR-DEC-003 (#396): object-branch class per emitted instruction, parallel
    // to `line_map`. Cheap, additive, does not touch `code`.
    let mut branch_map: synth_core::backend::BranchMap = Vec::new();

    for instr in &arm_instrs {
        // Record a relocation for every BL: the encoder emits `bl #0` and
        // relies on a relocation to patch the target. This covers BOTH import
        // dispatch stubs (`__meld_*`, undefined externals) AND internal calls
        // (`func_N`, defined in this object). Previously only `__meld_*` was
        // recorded, so internal `BL func_N` calls were left as unpatched
        // `bl #0` placeholders branching to a garbage address (#167).
        if let ArmOp::Bl { label } = &instr.op {
            relocations.push(CodeRelocation {
                offset: code.len() as u32,
                symbol: label.clone(),
                kind: synth_core::backend::RelocKind::ThmCall,
            });
        }
        // #237: symbol-relative MOVW/MOVT (the `--native-pointer-abi` static-data
        // addressing). The encoder writes the addend in place; record the matching
        // R_ARM_MOVW_ABS_NC / R_ARM_MOVT_ABS so the linker adds the symbol address.
        if let ArmOp::MovwSym { symbol, .. } = &instr.op {
            relocations.push(CodeRelocation {
                offset: code.len() as u32,
                symbol: symbol.clone(),
                kind: synth_core::backend::RelocKind::MovwAbs,
            });
        }
        if let ArmOp::MovtSym { symbol, .. } = &instr.op {
            relocations.push(CodeRelocation {
                offset: code.len() as u32,
                symbol: symbol.clone(),
                kind: synth_core::backend::RelocKind::MovtAbs,
            });
        }
        // #345: defer the literal-pool word + reloc + offset patch to the
        // post-loop pass (the pool address is not yet known).
        if let ArmOp::LdrSym { symbol, addend, .. } = &instr.op {
            pending_literals.push(PendingLiteral {
                ldr_offset: code.len() as u32,
                symbol: symbol.clone(),
                addend: *addend,
            });
        }

        // The machine offset of this instruction is the current code length,
        // captured before the bytes are appended.
        line_map.push((code.len() as u32, instr.source_line));
        branch_map.push((code.len() as u32, classify_arm_branch(&instr.op)));

        let encoded = encoder
            .encode(&instr.op)
            .map_err(|e| format!("ARM encoding failed: {}", e))?;
        code.extend_from_slice(&encoded);
    }

    // #345: place the literal pool at the end of this function's `.text`. Gated on
    // there being at least one `LdrSym` — functions without one are byte-identical
    // to before (no trailing padding, so downstream `func_offsets` are unchanged
    // and the frozen differential fixtures stay bit-for-bit equal).
    if !pending_literals.is_empty() {
        if !use_thumb2 {
            return Err("LdrSym literal-pool addressing requires Thumb-2".to_string());
        }
        // 4-byte align the pool start (Thumb-2 word loads require it, and
        // `Align(PC,4)` in the LDR-literal semantics assumes a word-aligned pool).
        while code.len() % 4 != 0 {
            code.push(0x00);
        }
        // One distinct pooled word per LdrSym (no dedup: different sites carry
        // different addends, and the REL addend lives in the word).
        for lit in &pending_literals {
            let word_offset = code.len() as u32;

            // REL semantics: the linker computes `S + A`, where A is the in-place
            // value of the relocated word. Initialize the word to the addend so
            // the final loaded address is `symbol + addend`.
            code.extend_from_slice(&(lit.addend as u32).to_le_bytes());
            relocations.push(CodeRelocation {
                offset: word_offset,
                symbol: lit.symbol.clone(),
                kind: synth_core::backend::RelocKind::Abs32,
            });

            // Patch the placeholder `LDR.W rd,[pc,#imm12]`. Thumb-2 LDR (literal):
            // address = Align(PC,4) + imm12, with PC = ldr_offset + 4. The pool is
            // always after the LDR, so U=1 (already set in hw1 = 0xF8DF).
            let pc = lit.ldr_offset + 4;
            let aligned_pc = pc & !3u32;
            let imm12 = word_offset - aligned_pc;
            if imm12 > 0xFFF {
                // Wide LDR-literal range is ±4 KB; these function bodies are far
                // smaller, but fail cleanly rather than miscompile if exceeded.
                return Err(format!(
                    "LdrSym literal pool out of range (#345): imm12={} > 4095 \
                     for symbol {}",
                    imm12, lit.symbol
                ));
            }
            let hw2_off = (lit.ldr_offset + 2) as usize;
            let mut hw2 = u16::from_le_bytes([code[hw2_off], code[hw2_off + 1]]);
            hw2 = (hw2 & 0xF000) | (imm12 as u16); // keep Rt, set imm12
            let hw2_bytes = hw2.to_le_bytes();
            code[hw2_off] = hw2_bytes[0];
            code[hw2_off + 1] = hw2_bytes[1];
        }
    }

    Ok((
        code,
        relocations,
        line_map,
        branch_map,
        final_instrs_for_wcet,
    ))
}

/// VCR-DEC-003 (#396): classify one emitted `ArmOp` into its object-level
/// control-flow role for the `synth-provenance-v1` map. Conditional branches are
/// the object decision points MC/DC must reconcile; `SelectMove` is the folded
/// (IT-block) predicated form the cmp→select fuse produces — a decision with no
/// branch.
fn classify_arm_branch(op: &ArmOp) -> synth_core::backend::BranchClass {
    use synth_core::backend::BranchClass;
    match op {
        ArmOp::Bcc { .. } | ArmOp::Bhs { .. } | ArmOp::Blo { .. } | ArmOp::BCondOffset { .. } => {
            BranchClass::CondBranch
        }
        ArmOp::B { .. } | ArmOp::BOffset { .. } => BranchClass::UncondBranch,
        ArmOp::SelectMove { .. } => BranchClass::Predicated,
        _ => BranchClass::Other,
    }
}

/// Resolve local label branches to byte-accurate offsets (#202).
///
/// `select_with_stack` emits conditional/unconditional branches as label
/// placeholders (`Bcc`/`B`/`Bhs`/`Blo` + `Label`) and never resolves them; the
/// encoder then emits a `0xD000`/`0xE000` placeholder with offset 0. Before #197
/// this path only ran for `--no-optimize`/declined functions, so the latent bug
/// stayed hidden — routing relocatable code through it surfaced branches that
/// land mid-instruction (a Cortex-M UsageFault) whenever a 32-bit Thumb-2
/// instruction sits between the branch and its target.
///
/// This pass encodes each instruction to learn its real byte length (so 16- vs
/// 32-bit forms and multi-instruction expansions are exact), maps each `Label`
/// to its byte position, and rewrites every label branch to the displacement
/// the encoder consumes: `(target - branch - 4) / 2` halfwords. A bounded
/// fixed-point handles an offset growing a branch from 16- to 32-bit (which
/// shifts later positions). `BCondOffset`/`BOffset` already produced inline by
/// the optimized path carry no label and are left untouched.
fn resolve_label_branches(
    arm_instrs: Vec<ArmInstruction>,
    encoder: &ArmEncoder,
) -> Result<Vec<ArmInstruction>, String> {
    use std::collections::HashMap;
    use synth_synthesis::Condition;

    enum BKind {
        Cond(Condition),
        Uncond,
    }
    // Record each label branch ONCE — indices are stable across iterations.
    let mut branches: Vec<(usize, BKind, String)> = Vec::new();
    for (i, instr) in arm_instrs.iter().enumerate() {
        match &instr.op {
            ArmOp::Bcc { cond, label } => branches.push((i, BKind::Cond(*cond), label.clone())),
            ArmOp::Bhs { label } => branches.push((i, BKind::Cond(Condition::HS), label.clone())),
            ArmOp::Blo { label } => branches.push((i, BKind::Cond(Condition::LO), label.clone())),
            ArmOp::B { label } => branches.push((i, BKind::Uncond, label.clone())),
            _ => {}
        }
    }
    if branches.is_empty() {
        return Ok(arm_instrs);
    }

    let mut resolved = arm_instrs;
    // Sizes only grow (16→32-bit), so this converges quickly; cap for safety.
    for _ in 0..16 {
        // 1. Byte position of each instruction (Label encodes to 0 bytes).
        let mut positions = Vec::with_capacity(resolved.len());
        let mut pos: i64 = 0;
        for instr in &resolved {
            positions.push(pos);
            pos += encoder
                .encode(&instr.op)
                .map_err(|e| format!("branch-resolve size probe failed: {}", e))?
                .len() as i64;
        }
        // 2. Label name -> byte position (owned keys so the borrow ends here).
        let mut labels: HashMap<String, i64> = HashMap::new();
        for (i, instr) in resolved.iter().enumerate() {
            if let ArmOp::Label { name } = &instr.op {
                labels.insert(name.clone(), positions[i]);
            }
        }
        // 3. Rewrite each branch to its byte-accurate offset.
        let mut changed = false;
        for (idx, kind, label) in &branches {
            // A label not defined locally is an EXTERNAL target (e.g.
            // `Trap_Handler` resolved by a relocation / the vector table). Leave
            // such branches as their placeholder for the existing relocation
            // path — only local control-flow labels are byte-resolved here.
            let Some(&target) = labels.get(label) else {
                continue;
            };
            // Encoder consumes the field as (target - branch - 4) / 2 halfwords.
            // Positions are always even, so this division is exact.
            let halfword_offset = ((target - positions[*idx] - 4) / 2) as i32;
            let new_op = match kind {
                BKind::Cond(c) => ArmOp::BCondOffset {
                    cond: *c,
                    offset: halfword_offset,
                },
                BKind::Uncond => ArmOp::BOffset {
                    offset: halfword_offset,
                },
            };
            if resolved[*idx].op != new_op {
                resolved[*idx].op = new_op;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    Ok(resolved)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// #539: `i32.const 0; memory.grow m` folds to `memory.size m`; other deltas
    /// (const non-zero, runtime) are left as `memory.grow` (→ the sound fixed-
    /// memory -1). Non-grow ops are untouched, so functions without the idiom are
    /// byte-identical.
    #[test]
    fn test_rewrite_memory_grow_zero_539() {
        // the idiom -> memory.size
        assert_eq!(
            rewrite_memory_grow_zero(&[WasmOp::I32Const(0), WasmOp::MemoryGrow(0)]),
            vec![WasmOp::MemorySize(0)]
        );
        // const non-zero delta: NOT folded
        assert_eq!(
            rewrite_memory_grow_zero(&[WasmOp::I32Const(2), WasmOp::MemoryGrow(0)]),
            vec![WasmOp::I32Const(2), WasmOp::MemoryGrow(0)]
        );
        // runtime delta (no preceding const): NOT folded
        assert_eq!(
            rewrite_memory_grow_zero(&[WasmOp::LocalGet(0), WasmOp::MemoryGrow(0)]),
            vec![WasmOp::LocalGet(0), WasmOp::MemoryGrow(0)]
        );
        // a bare const-0 not feeding a grow is untouched
        assert_eq!(
            rewrite_memory_grow_zero(&[WasmOp::I32Const(0), WasmOp::I32Add]),
            vec![WasmOp::I32Const(0), WasmOp::I32Add]
        );
        // fold is local: surrounding ops preserved, indices past the fold intact
        assert_eq!(
            rewrite_memory_grow_zero(&[
                WasmOp::LocalGet(0),
                WasmOp::I32Const(0),
                WasmOp::MemoryGrow(0),
                WasmOp::I32Add,
            ]),
            vec![WasmOp::LocalGet(0), WasmOp::MemorySize(0), WasmOp::I32Add]
        );
    }

    #[test]
    fn test_arm_backend_name() {
        let backend = ArmBackend::new();
        assert_eq!(backend.name(), "arm");
        assert!(backend.is_available());
    }

    #[test]
    fn test_arm_backend_capabilities() {
        let backend = ArmBackend::new();
        let caps = backend.capabilities();
        assert!(!caps.produces_elf);
        assert!(caps.supports_rule_verification);
        assert!(!caps.is_external);
    }

    #[test]
    fn test_compile_add_function() {
        let backend = ArmBackend::new();
        let ops = vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::I32Add];
        let config = CompileConfig::default();

        let result = backend.compile_function("add", &ops, &config);
        assert!(result.is_ok());

        let func = result.unwrap();
        assert_eq!(func.name, "add");
        assert!(!func.code.is_empty());
        assert_eq!(func.wasm_ops, ops);
    }

    /// VCR-DBG-001: the per-instruction source map must cover the function with
    /// monotonic, in-bounds machine offsets, and must not perturb the emitted
    /// code (it is captured at encode time, never serialized here).
    #[test]
    fn test_line_map_is_wellformed_dbg001() {
        let backend = ArmBackend::new();
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let config = CompileConfig::default();
        let func = backend.compile_function("add", &ops, &config).unwrap();

        // Non-empty, and the first instruction starts at machine offset 0.
        assert!(
            !func.line_map.is_empty(),
            "a non-trivial function captures a source map"
        );
        assert_eq!(func.line_map[0].0, 0, "first instruction at offset 0");

        // Offsets strictly increase by at least one ARM/Thumb instruction (>= 2
        // bytes) and every mapped offset lies inside the emitted `.text`.
        for w in func.line_map.windows(2) {
            assert!(w[1].0 > w[0].0, "instruction offsets strictly increase");
            assert!(
                w[1].0 - w[0].0 >= 2,
                "each ARM/Thumb instruction is >= 2 bytes"
            );
        }
        let last = func.line_map.last().unwrap().0 as usize;
        assert!(
            last < func.code.len(),
            "every mapped offset lies inside .text"
        );

        // The side-table is additive: recompiling is deterministic and the map is
        // consistent with that exact code (capturing it does not alter output).
        let again = backend.compile_function("add", &ops, &config).unwrap();
        assert_eq!(
            again.code, func.code,
            "compilation deterministic; map is additive"
        );
        assert_eq!(again.line_map, func.line_map);
    }

    #[test]
    fn test_count_params() {
        let ops = vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::I32Add];
        assert_eq!(count_params(&ops), 2);

        let no_params = vec![WasmOp::I32Const(5), WasmOp::I32Const(3), WasmOp::I32Add];
        assert_eq!(count_params(&no_params), 0);
    }

    /// #457: the declared param count caps the access-pattern inference. The
    /// repro shape `(param i32)(local i32) → p0 + local1` reads local 1 before
    /// any write, so `count_params` infers 2 — with the declared count (1) the
    /// local is reclassified onto the zero-inited frame path instead of being
    /// read from R1 (caller garbage).
    #[test]
    fn declared_param_count_caps_inference_457() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        // The inference alone still says 2 (the misclassification this caps).
        assert_eq!(count_params(&ops), 2);

        let backend = ArmBackend::new();
        let inferred = backend
            .compile_function("rbw", &ops, &CompileConfig::default())
            .unwrap();
        let declared = backend
            .compile_function(
                "rbw",
                &ops,
                &CompileConfig {
                    current_func_param_count: Some(1),
                    ..CompileConfig::default()
                },
            )
            .unwrap();
        // The cap is consumed: the declared-count compile reclassifies local 1
        // and must emit different code than the param-misclassified one.
        assert_ne!(
            inferred.code, declared.code,
            "declared param count must reach the selector"
        );
        // The zero-init is present: a 16-bit Thumb `movs rN, #0`
        // (0x2000 | rd<<8 → LE bytes [0x00, 0x20+rd]) somewhere in the body.
        let has_movs_zero = declared
            .code
            .chunks_exact(2)
            .any(|h| h[0] == 0x00 && (0x20..=0x27).contains(&h[1]));
        assert!(
            has_movs_zero,
            "declared-count compile must zero-init the read-before-write local; code: {:02x?}",
            declared.code
        );
        // A declared count that matches (or exceeds) the inference changes
        // nothing — byte-identity for every function without rbw locals.
        let matching = backend
            .compile_function(
                "rbw",
                &ops,
                &CompileConfig {
                    current_func_param_count: Some(2),
                    ..CompileConfig::default()
                },
            )
            .unwrap();
        assert_eq!(
            matching.code, inferred.code,
            "declared >= inferred must stay byte-identical"
        );
    }

    #[test]
    fn test_arm_backend_register() {
        let mut registry = synth_core::BackendRegistry::new();
        registry.register(Box::new(ArmBackend::new()));
        assert!(registry.get("arm").is_some());
        assert_eq!(registry.available().len(), 1);
    }

    #[test]
    fn test_compile_import_call_produces_relocations() {
        let backend = ArmBackend::new();
        // Simulate a WASM module where func index 0 is an import.
        // Call(0) should generate MOV R0, #0; BL __meld_dispatch_import
        let ops = vec![WasmOp::Call(0)];
        let config = CompileConfig {
            num_imports: 1,
            no_optimize: true, // Direct instruction selection to preserve Call semantics
            ..CompileConfig::default()
        };

        let result = backend.compile_function("caller", &ops, &config);
        assert!(result.is_ok());

        let func = result.unwrap();
        assert!(!func.code.is_empty());
        assert_eq!(func.relocations.len(), 1);
        assert_eq!(func.relocations[0].symbol, "__meld_dispatch_import");
        // The BL is the second instruction (after MOV R0, #0), so offset should be > 0
        assert!(func.relocations[0].offset > 0);
    }

    /// Regression test for #197: in `relocatable` mode, an import call must
    /// relocate against the direct `func_N` symbol (rewritten to the wasm field
    /// name by `build_relocatable_elf`), NOT `__meld_dispatch_import`. This is
    /// the ABI half of the #197 fix — without it, a host linker cannot resolve
    /// the call to the real kernel symbol (e.g. `k_spin_lock`).
    #[test]
    fn test_compile_relocatable_import_uses_direct_func_symbol_197() {
        let backend = ArmBackend::new();
        let ops = vec![WasmOp::Call(0)]; // func 0 is an import
        let config = CompileConfig {
            num_imports: 1,
            relocatable: true,
            ..CompileConfig::default()
        };

        let func = backend
            .compile_function("caller", &ops, &config)
            .expect("relocatable import call compiles");

        assert_eq!(func.relocations.len(), 1);
        assert_eq!(
            func.relocations[0].symbol, "func_0",
            "#197: relocatable import must relocate against func_0 (→ field name), not Meld dispatch"
        );
    }

    #[test]
    fn test_compile_no_imports_no_relocations() {
        let backend = ArmBackend::new();
        let ops = vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::I32Add];
        let config = CompileConfig::default();

        let func = backend.compile_function("add", &ops, &config).unwrap();
        assert!(func.relocations.is_empty());
    }

    /// Regression test for #167: a call to an INTERNAL function
    /// (index `>= num_imports`) must record a relocation against `func_{index}`.
    /// Before the fix, only `__meld_*` (import) BLs were relocated, so
    /// internal `BL func_N` was emitted as an unpatched `bl #0` branching
    /// to a garbage address — making the object non-linkable. This test
    /// would have caught that regression.
    #[test]
    fn test_compile_internal_call_produces_relocation_167() {
        let backend = ArmBackend::new();
        // num_imports = 1, so Call(2) is an INTERNAL call → `BL func_2`.
        let ops = vec![WasmOp::Call(2)];
        let config = CompileConfig {
            num_imports: 1,
            no_optimize: true,
            ..CompileConfig::default()
        };

        let func = backend
            .compile_function("caller", &ops, &config)
            .expect("internal call compiles");

        assert_eq!(
            func.relocations.len(),
            1,
            "an internal call must emit exactly one relocation (#167)"
        );
        assert_eq!(
            func.relocations[0].symbol, "func_2",
            "internal call must relocate against the callee's func_{{index}} symbol (#167)"
        );
    }

    // ─── Phase 1 safety-bounds plumbing for ARM ──────────────────────────

    #[test]
    fn arm_safety_bounds_mpu_emits_same_code_as_none() {
        // Mpu mode must not introduce any inline check on ARM — the MPU
        // handles faults via hardware. The encoded bytes for an i32.load
        // should be identical between None and Mpu.
        let backend = ArmBackend::new();
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Load {
                offset: 0,
                align: 2,
            },
        ];
        let cfg_none = CompileConfig {
            no_optimize: true,
            ..Default::default()
        };
        let cfg_mpu = CompileConfig {
            no_optimize: true,
            safety_bounds: SafetyBounds::Mpu,
            ..Default::default()
        };
        let n = backend.compile_function("ld", &ops, &cfg_none).unwrap();
        let m = backend.compile_function("ld", &ops, &cfg_mpu).unwrap();
        assert_eq!(
            n.code, m.code,
            "Mpu and None should produce identical ARM bytes (Mpu relies on hardware)"
        );
    }

    #[test]
    fn arm_legacy_bounds_check_still_emits_software_check() {
        // Legacy CLI users with `--bounds-check` should keep getting the
        // software path even though the new SafetyBounds field defaults to None.
        let backend = ArmBackend::new();
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Load {
                offset: 0,
                align: 2,
            },
        ];
        let cfg_legacy = CompileConfig {
            no_optimize: true,
            bounds_check: true,
            ..Default::default()
        };
        let cfg_software = CompileConfig {
            no_optimize: true,
            safety_bounds: SafetyBounds::Software,
            ..Default::default()
        };
        let l = backend.compile_function("ld", &ops, &cfg_legacy).unwrap();
        let s = backend.compile_function("ld", &ops, &cfg_software).unwrap();
        assert_eq!(
            l.code, s.code,
            "--bounds-check should produce the same bytes as --safety-bounds=software"
        );
    }

    /// #377: `--safety-bounds software` must be enforced on the OPTIMIZED path
    /// too. Pre-fix, `software` was byte-identical to `none` there (a silent
    /// no-op while the safety manifest claimed enforcement). The compiled
    /// bytes must now (a) differ from `none` and (b) contain the inline
    /// `CMP ip, sl` + `UDF` guard.
    #[test]
    fn arm_safety_bounds_software_enforced_on_optimized_path_377() {
        let backend = ArmBackend::new();
        // Dynamic-address store+load: the optimized path accepts this shape
        // (no calls, no i64 params, ≤4 params).
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Store {
                offset: 4,
                align: 2,
            },
            WasmOp::LocalGet(0),
            WasmOp::I32Load {
                offset: 0,
                align: 2,
            },
        ];
        // no_optimize NOT set — this exercises the optimized path.
        let cfg_none = CompileConfig::default();
        let cfg_sw = CompileConfig {
            safety_bounds: SafetyBounds::Software,
            ..Default::default()
        };
        let n = backend.compile_function("st", &ops, &cfg_none).unwrap();
        let s = backend.compile_function("st", &ops, &cfg_sw).unwrap();
        assert_ne!(
            n.code, s.code,
            "#377: software bounds must CHANGE optimized-path codegen (was a silent no-op)"
        );
        // Thumb-2 `UDF #0` is 0xDE00 (LE bytes: 00 DE); the #752
        // wraparound-safe guard's borrow check `CMP sl, ip` (16-bit
        // high-reg form) is 0x45E2 (LE: E2 45). Both must appear — one
        // guard per access, traps inline.
        let has_udf = s.code.windows(2).any(|w| w == [0x00, 0xDE]);
        let has_cmp_sl_ip = s.code.windows(2).any(|w| w == [0xE2, 0x45]);
        assert!(has_udf, "#377: inline UDF trap missing from optimized path");
        assert!(
            has_cmp_sl_ip,
            "#377/#752: CMP sl, ip bounds borrow-check missing from optimized path"
        );
        // And `none` must contain NO UDF (the function has no other trap).
        assert!(
            !n.code.windows(2).any(|w| w == [0x00, 0xDE]),
            "none must not contain a UDF for this function"
        );
    }

    /// #377: `mpu` on the optimized path is codegen-passthrough — identical
    /// bytes to `none` on BOTH paths (hardware enforcement is target-level;
    /// synth does not emit MPU region programming — tracked separately in
    /// #377's fix-direction discussion). This pins path-parity for `mpu`.
    #[test]
    fn arm_safety_bounds_mpu_optimized_path_parity_377() {
        let backend = ArmBackend::new();
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Load {
                offset: 0,
                align: 2,
            },
        ];
        let cfg_none = CompileConfig::default();
        let cfg_mpu = CompileConfig {
            safety_bounds: SafetyBounds::Mpu,
            ..Default::default()
        };
        let n = backend.compile_function("ld", &ops, &cfg_none).unwrap();
        let m = backend.compile_function("ld", &ops, &cfg_mpu).unwrap();
        assert_eq!(
            n.code, m.code,
            "Mpu and None must produce identical bytes on the optimized path too"
        );
    }

    /// #377: `mask` on the optimized path declines to the direct selector
    /// (honest degradation) — the compiled function must equal the
    /// `--no-optimize` masking bytes, i.e. the flag is honored, never dropped.
    #[test]
    fn arm_safety_bounds_mask_optimized_path_declines_to_direct_377() {
        let backend = ArmBackend::new();
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Store {
                offset: 0,
                align: 2,
            },
        ];
        let cfg_mask_opt = CompileConfig {
            safety_bounds: SafetyBounds::Mask,
            ..Default::default()
        };
        let cfg_mask_direct = CompileConfig {
            no_optimize: true,
            safety_bounds: SafetyBounds::Mask,
            ..Default::default()
        };
        let o = backend.compile_function("st", &ops, &cfg_mask_opt).unwrap();
        let d = backend
            .compile_function("st", &ops, &cfg_mask_direct)
            .unwrap();
        assert_eq!(
            o.code, d.code,
            "#377: mask on the optimized path must fall back to the direct selector's masking"
        );
    }

    // ========================================================================
    // ISA feature gate tests — ensure the compiler never emits unsupported
    // instructions for a given target
    // ========================================================================

    #[test]
    fn test_f32_rejected_on_cortex_m3_no_fpu() {
        let backend = ArmBackend::new();
        let ops = vec![WasmOp::F32Const(1.0), WasmOp::F32Const(2.0), WasmOp::F32Add];
        let config = CompileConfig {
            target: TargetSpec::cortex_m3(),
            no_optimize: true,
            ..CompileConfig::default()
        };

        let result = backend.compile_function("fadd", &ops, &config);
        assert!(
            result.is_err(),
            "f32 operations should fail on Cortex-M3 (no FPU)"
        );
    }

    #[test]
    fn test_f32_accepted_on_cortex_m4f() {
        let backend = ArmBackend::new();
        let ops = vec![WasmOp::F32Const(1.0), WasmOp::F32Const(2.0), WasmOp::F32Add];
        let config = CompileConfig {
            target: TargetSpec::cortex_m4f(),
            no_optimize: true,
            ..CompileConfig::default()
        };

        let result = backend.compile_function("fadd", &ops, &config);
        assert!(
            result.is_ok(),
            "f32 operations should succeed on Cortex-M4F, got: {:?}",
            result.unwrap_err()
        );
    }

    #[test]
    fn test_i32_works_on_all_targets() {
        let backend = ArmBackend::new();
        let ops = vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::I32Add];

        // Cortex-M3 (no FPU)
        let config_m3 = CompileConfig {
            target: TargetSpec::cortex_m3(),
            no_optimize: true,
            ..CompileConfig::default()
        };
        assert!(
            backend.compile_function("add", &ops, &config_m3).is_ok(),
            "i32 ops should work on Cortex-M3"
        );

        // Cortex-M4F (single FPU)
        let config_m4f = CompileConfig {
            target: TargetSpec::cortex_m4f(),
            no_optimize: true,
            ..CompileConfig::default()
        };
        assert!(
            backend.compile_function("add", &ops, &config_m4f).is_ok(),
            "i32 ops should work on Cortex-M4F"
        );

        // Cortex-M7DP (double FPU)
        let config_m7dp = CompileConfig {
            target: TargetSpec::cortex_m7dp(),
            no_optimize: true,
            ..CompileConfig::default()
        };
        assert!(
            backend.compile_function("add", &ops, &config_m7dp).is_ok(),
            "i32 ops should work on Cortex-M7DP"
        );
    }

    #[test]
    fn test_f32_rejected_on_cortex_m4_no_fpu() {
        // Cortex-M4 (without F suffix) has no FPU
        let backend = ArmBackend::new();
        let ops = vec![WasmOp::F32Const(1.5), WasmOp::F32Const(2.5), WasmOp::F32Mul];
        let config = CompileConfig {
            target: TargetSpec::cortex_m4(),
            no_optimize: true,
            ..CompileConfig::default()
        };

        let result = backend.compile_function("fmul", &ops, &config);
        assert!(
            result.is_err(),
            "f32 operations should fail on Cortex-M4 (no FPU)"
        );
    }

    // ========================================================================
    // Issue #120 — f32 ops in the optimized lowering path
    //
    // `OptimizerBridge::wasm_to_ir` has no handlers for f32/f64 ops, so a
    // value-producing float op fell through to `Opcode::Nop`, leaving a
    // downstream consumer with an unmapped vreg and tripping the PR #101
    // defensive panic in `ir_to_arm`. Customer reproducer: `compiler_builtins
    // float::div` and `gale_compute_ipi_mask` in the `falcon-rate-component`
    // module.
    //
    // Fix: `optimize_full` declines float modules with a typed `Err`;
    // `compile_wasm_to_arm` falls back to the non-optimized `select_with_stack`
    // path, which handles f32 via VFP/FPU. These tests use the *default*
    // (optimized) config — `no_optimize` is NOT set — which is the exact
    // configuration that panicked pre-fix.
    // ========================================================================

    /// Pre-fix: this panicked with "vreg vN has no assigned ARM register and
    /// no spill slot" inside `ir_to_arm`. Post-fix: the optimized path declines
    /// the module and the backend falls back to direct selection, producing a
    /// non-empty f32.div lowering on a Cortex-M4F.
    #[test]
    fn test_issue120_f32_div_compiles_via_optimized_default() {
        let backend = ArmBackend::new();
        let ops = vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::F32Div];
        let config = CompileConfig {
            target: TargetSpec::cortex_m4f(),
            // no_optimize NOT set — this exercises the optimized path that
            // panicked in issue #120, then the fallback to direct selection.
            // GI-FPU-002: the f32 params must be declared so the direct
            // selector homes them in S0/S1 (AAPCS-VFP) rather than declining.
            current_func_params_f32: vec![true, true],
            ..CompileConfig::default()
        };

        let result = backend.compile_function("fdiv", &ops, &config);
        assert!(
            result.is_ok(),
            "f32.div must compile on Cortex-M4F via the optimized->direct \
             fallback (issue #120), got: {:?}",
            result.as_ref().err()
        );
        assert!(
            !result.unwrap().code.is_empty(),
            "f32.div must produce non-empty machine code"
        );
    }

    /// A spread of f32 ops, all through the optimized (default) config, must
    /// compile via the fallback on an FPU target without panicking.
    #[test]
    fn test_issue120_assorted_f32_ops_compile_via_optimized_default() {
        let backend = ArmBackend::new();
        let config = CompileConfig {
            target: TargetSpec::cortex_m4f(),
            // GI-FPU-002: declare the two f32 params for AAPCS-VFP homing.
            current_func_params_f32: vec![true, true],
            ..CompileConfig::default()
        };

        let cases: Vec<(&str, Vec<WasmOp>)> = vec![
            (
                "fadd",
                vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::F32Add],
            ),
            (
                "fmul",
                vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::F32Mul],
            ),
            (
                "fsub",
                vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::F32Sub],
            ),
        ];

        for (name, ops) in cases {
            let result = backend.compile_function(name, &ops, &config);
            assert!(
                result.is_ok(),
                "{name} must compile via the optimized->direct fallback \
                 (issue #120), got: {:?}",
                result.as_ref().err()
            );
            assert!(
                !result.unwrap().code.is_empty(),
                "{name} must produce non-empty machine code"
            );
        }
    }

    /// The fallback must still honor the ISA feature gate: f32 on a no-FPU
    /// target must fail cleanly (not panic) even on the optimized path.
    #[test]
    fn test_issue120_f32_div_rejected_on_no_fpu_via_optimized() {
        let backend = ArmBackend::new();
        let ops = vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::F32Div];
        let config = CompileConfig {
            target: TargetSpec::cortex_m3(),
            ..CompileConfig::default()
        };

        let result = backend.compile_function("fdiv", &ops, &config);
        assert!(
            result.is_err(),
            "f32.div must be rejected on Cortex-M3 (no FPU), not panic"
        );
    }

    /// #507: a `br_table` function compiled via the DEFAULT (optimized) config
    /// must produce the SAME bytes as the direct (`no_optimize`) selector —
    /// i.e. the optimized path declined it to direct, lowering the dispatch as a
    /// real cmp-chain instead of silently dropping it (which left all arms in
    /// fall-through). Pre-fix the two outputs differed (the optimized one had no
    /// selector compare). Execution correctness is gated by
    /// `scripts/repro/br_table_507_differential.py`.
    #[test]
    fn test_507_br_table_declines_to_direct() {
        let backend = ArmBackend::new();
        // dispatch(sel): br_table over 3 blocks, each storing a marker to mem[0].
        let ops = vec![
            WasmOp::Block,
            WasmOp::Block,
            WasmOp::Block,
            WasmOp::LocalGet(0),
            WasmOp::BrTable {
                targets: vec![0, 1, 2],
                default: 2,
            },
            WasmOp::End,
            WasmOp::I32Const(0),
            WasmOp::I32Const(10),
            WasmOp::I32Store {
                offset: 0,
                align: 2,
            },
            WasmOp::Return,
            WasmOp::End,
            WasmOp::I32Const(0),
            WasmOp::I32Const(20),
            WasmOp::I32Store {
                offset: 0,
                align: 2,
            },
            WasmOp::Return,
            WasmOp::End,
            WasmOp::I32Const(0),
            WasmOp::I32Const(30),
            WasmOp::I32Store {
                offset: 0,
                align: 2,
            },
        ];
        let opt = CompileConfig {
            target: TargetSpec::cortex_m4(),
            ..CompileConfig::default()
        };
        let direct = CompileConfig {
            target: TargetSpec::cortex_m4(),
            no_optimize: true,
            ..CompileConfig::default()
        };
        let a = backend
            .compile_function("dispatch", &ops, &opt)
            .expect("optimized-default must compile br_table (via decline)");
        let b = backend
            .compile_function("dispatch", &ops, &direct)
            .expect("direct must compile br_table");
        assert_eq!(
            a.code, b.code,
            "#507: optimized-default br_table output must be byte-identical to the \
             direct selector (i.e. declined to direct), not a dropped dispatch"
        );
    }

    /// Issue #94: end-to-end byte-size check for the canonical u64-packed
    /// FFI-return hi32 extract pattern. Compiles two near-identical
    /// functions — one with the optimized shift-by-32, one with a generic
    /// shift-by-7 — and asserts the optimized form is meaningfully smaller.
    #[test]
    fn test_issue94_hi32_extract_is_smaller_than_generic_shift() {
        let backend = ArmBackend::new();
        let config = CompileConfig {
            target: TargetSpec::cortex_m4f(),
            ..CompileConfig::default()
        };

        // #518: the i64 value must NOT come from an i64 PARAM — the optimized
        // path now declines i64-param functions to the direct selector (it homed
        // an i64 param in R4:R5 instead of R0:R1, a silent miscompile this test's
        // byte-size-only assertion masked). The canonical #94 case is a u64 from
        // an FFI return, not a param, anyway. Source the i64 from a sign-extended
        // i32 param (`extend_i32_s`): a runtime, non-constant-foldable i64 that
        // stays on the optimized path, so the shift-by-32 hi-extract peephole is
        // still exercised on CORRECT code.
        // Optimized path: `(i64.extend_i32_s (local.get 0)) >>> 32; wrap_i64`
        let ops_hi32 = vec![
            WasmOp::LocalGet(0), // i32 param in R0
            WasmOp::I64ExtendI32S,
            WasmOp::I64Const(32),
            WasmOp::I64ShrU,
            WasmOp::I32WrapI64,
        ];
        let func_hi32 = backend
            .compile_function("hi32_extract", &ops_hi32, &config)
            .unwrap();

        // Generic path: `... >>> 7; wrap_i64` — same shape, but the shift amount
        // is not a multiple of 32, so it falls through to the runtime shift.
        let ops_generic = vec![
            WasmOp::LocalGet(0),
            WasmOp::I64ExtendI32S,
            WasmOp::I64Const(7),
            WasmOp::I64ShrU,
            WasmOp::I32WrapI64,
        ];
        let func_generic = backend
            .compile_function("generic_shr", &ops_generic, &config)
            .unwrap();

        let bytes_hi32 = func_hi32.code.len();
        let bytes_generic = func_generic.code.len();
        println!(
            "\n[issue #94] hi32 extract: {} bytes (vs generic shift: {} bytes; saved {})",
            bytes_hi32,
            bytes_generic,
            bytes_generic.saturating_sub(bytes_hi32)
        );
        let hex: String = func_hi32
            .code
            .iter()
            .map(|b| format!("{:02x}", b))
            .collect::<Vec<_>>()
            .join(" ");
        println!("[issue #94] hi32 bytes: {}", hex);
        // We expect the optimized form to be at least 30 bytes smaller than
        // the generic 64-bit shift sequence. (Empirically: 14 vs 50 bytes.)
        assert!(
            bytes_hi32 + 30 <= bytes_generic,
            "issue #94: hi32 extract = {} bytes, generic shift = {} bytes; \
             expected optimized form to be at least 30 bytes smaller",
            bytes_hi32,
            bytes_generic,
        );
    }
}
