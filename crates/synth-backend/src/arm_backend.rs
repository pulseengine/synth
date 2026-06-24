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
            let func_config = match config.func_params_i64.get(func.index as usize) {
                Some(p) if !p.is_empty() => Some(CompileConfig {
                    current_func_params_i64: p.clone(),
                    ..config.clone()
                }),
                _ => None,
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
        let (code, relocations, line_map) =
            compile_wasm_to_arm(ops, config).map_err(BackendError::CompilationFailed)?;

        Ok(CompiledFunction {
            name: name.to_string(),
            code,
            wasm_ops: ops.to_vec(),
            relocations,
            line_map,
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

/// Core compilation: WASM ops → ARM machine code bytes + relocations
///
/// Returns (code_bytes, relocations) where relocations record BL instructions
/// that target external symbols (e.g., `__meld_dispatch_import` for import calls).
fn compile_wasm_to_arm(
    wasm_ops: &[WasmOp],
    config: &CompileConfig,
) -> Result<(Vec<u8>, Vec<CodeRelocation>, LineMap), String> {
    let num_params = count_params(wasm_ops);

    let bounds_config = match config.effective_safety_bounds() {
        SafetyBounds::None => BoundsCheckConfig::None,
        SafetyBounds::Mpu => BoundsCheckConfig::Mpu,
        SafetyBounds::Software => BoundsCheckConfig::Software,
        SafetyBounds::Mask => BoundsCheckConfig::Masking,
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
                                 param_backing_on_exhaustion: bool|
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
        // #237: native-pointer ABI — wasm statics become __synth_wasm_data-relative.
        selector.set_native_pointer_abi(config.native_pointer_abi, config.linear_memory_bytes);
        // #311: i64 call results are register PAIRS — tag them.
        selector.set_result_types(config.func_ret_i64.clone(), config.type_ret_i64.clone());
        // #359: declared param widths of THIS function, so the AAPCS stack-arg
        // path can refuse 64-bit params (Ok-or-Err). Empty ⇒ assume i32.
        selector.set_params_i64(config.current_func_params_i64.clone());
        // Stack-pointer promotion is meaningful only under the native-pointer ABI;
        // gating here keeps every non-native compile (all frozen fixtures) on the
        // legacy R9 globals-table path, bit-identical.
        if config.native_pointer_abi
            && let Some((sp_idx, sp_init)) = config.stack_pointer_global
        {
            selector.set_native_pointer_stack(sp_idx, sp_init);
        }
        selector.set_spill_on_exhaustion(spill_on_exhaustion);
        selector.set_param_backing_on_exhaustion(param_backing_on_exhaustion);
        // VCR-RA local promotion (#390, #242): keep eligible non-param i32 locals
        // in callee-saved registers instead of frame slots — the structural lever
        // toward native parity. DEFAULT-ON as of v0.14.0: gale's G474RE DWT gate
        // cleared it as a net win (gust_mix dissolved 58→50 cyc/call −14%, all 5
        // stack spill/reloads eliminated, correctness bit-identical over [0,2047],
        // 2.00×→1.72× vs LLVM). Escape hatch: `SYNTH_NO_LOCAL_PROMOTE=1` restores
        // the frame-slot path. Leaf-only / i32-only / ARM-only (see
        // compute_local_promotion); the leaf-only lift + i64 locals are follow-ons.
        selector.set_local_promote(std::env::var("SYNTH_NO_LOCAL_PROMOTE").is_err());
        selector.select_with_stack(wasm_ops, num_params)
    };
    let select_direct = || -> Result<Vec<ArmInstruction>, String> {
        // The two recoverable exhaustion classes. NOT retried: the i64
        // spill-slot-pool Err ("spill-slot pool exhausted") — the honest
        // remaining bound of the 3b-lite allocator.
        const SINGLE_EXHAUSTION: &str = "all allocatable registers are live on the stack";
        const PAIR_EXHAUSTION: &str = "no consecutive pair of free registers for i64";
        let mut attempt = select_direct_attempt(false, false);
        // VCR-RA-001 step 3b-lite (#242): the i32 register-exhaustion
        // hard-fail is recoverable — retry with spill-on-exhaustion, which
        // reserves the spill area and spills the deepest stack value when the
        // pool is full. Only functions that FAILED the first pass ever reach
        // this, so existing output is untouched by construction.
        if let Err(e) = &attempt
            && e.to_string().contains(SINGLE_EXHAUSTION)
        {
            attempt = select_direct_attempt(true, false);
        }
        // VCR-RA-001 acceptance increment (#242): the i64 consecutive-PAIR
        // exhaustion is recoverable too — but not by stack spilling (the pair
        // allocator already spills stack values, #171): the blockers are the
        // pinned param home registers. The final retry frame-backs the params
        // (#204 machinery) so they stop pinning R0-R3, with spill-on-exhaustion
        // kept on for the single-register pressure the reloads add. Reached
        // only by functions that failed every earlier pass.
        if let Err(e) = &attempt
            && e.to_string().contains(PAIR_EXHAUSTION)
        {
            attempt = select_direct_attempt(true, true);
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
    let arm_instrs = if config.no_optimize || config.relocatable {
        select_direct()?
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
        // `ir_to_arm` now returns `Result` — an `Err` means the optimized path
        // hit an unmapped vreg (issue-#93-class). Treat it identically to an
        // `optimize_full` failure: fall back to the direct selector rather
        // than propagating, so the function still compiles correctly.
        match bridge
            .optimize_full(wasm_ops)
            .and_then(|(opt_ir, _cfg, _stats)| bridge.ir_to_arm(&opt_ir, num_params as usize))
        {
            Ok(arm_ops) => arm_ops
                .into_iter()
                .map(|op| ArmInstruction {
                    op,
                    source_line: None,
                })
                .collect(),
            // Issue #120: the optimized path declines modules it cannot lower
            // (notably scalar f32/f64 ops — the IR has no float opcodes). Fall
            // back to the direct instruction selector, which handles f32 via
            // VFP/FPU. This is honest degradation: the function still compiles
            // correctly, just without IR-level optimization.
            Err(_) => select_direct()?,
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

    // VCR-RA-001 const-CSE / rematerialization-avoidance (#209), the first
    // allocator-analysis-driven CODEGEN change. Drops `movw` re-materializations
    // of a constant already resident in another register and retargets the reads
    // — every rewrite proven by the liveness analysis, and it ONLY removes
    // materializations (pressure never rises), so unlike the mla fusion (#277) it
    // cannot regress on-target. Runs on the selected stream before branch
    // resolution (it removes instructions, shifting byte offsets). Behind
    // `SYNTH_CONST_CSE=1` while it is validated against the differential oracle +
    // gale's five on-target baselines; off by default keeps every fixture
    // bit-identical.
    let arm_instrs = if std::env::var("SYNTH_CONST_CSE").is_ok() {
        synth_synthesis::liveness::apply_const_cse(&arm_instrs).0
    } else {
        arm_instrs
    };

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
        let (out, stats) = synth_synthesis::liveness::reallocate_function(&arm_instrs, &POOL);
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
        synth_synthesis::liveness::shrink_callee_saved_saves(&out).unwrap_or(out)
    } else {
        arm_instrs
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
    // new instruction form and no label/offset change. BEHIND `SYNTH_STACK_FWD=1`
    // (opt-in, off by default ⇒ bit-identical) while it is validated against the
    // execution differential + gale's G474RE bench — the same gated path the
    // cmp→select flip took before shipping default-on in v0.13.0.
    let arm_instrs = if std::env::var("SYNTH_STACK_FWD").is_ok() {
        let (out, fwd) = synth_synthesis::liveness::forward_stack_reloads(&arm_instrs);
        if std::env::var("SYNTH_FUSE_STATS").is_ok() {
            eprintln!("[stack-fwd] {fwd} stack reload(s) forwarded to register moves");
        }
        out
    } else {
        arm_instrs
    };

    // VCR-RA immediate-shift folding (#390, #242): a constant shift amount the
    // stack selector materialized into a scratch register (`movw rM,#C; lsl rD,rN,rM`)
    // folds to the immediate form (`lsl rD,rN,#C`), removing the dead `movw` — −1
    // instruction, −1 live register. Removal-only (offset-neutral before branch
    // resolution, like the dead-store pass). BEHIND `SYNTH_IMM_SHIFT_FOLD=1`
    // (opt-in, off by default ⇒ bit-identical) while it earns the execution
    // differential + gale's G474RE DWT gate — the same gated path local promotion
    // and cmp→select took before shipping default-on. gale-named lever toward ≤1.3×.
    let arm_instrs = if std::env::var("SYNTH_IMM_SHIFT_FOLD").is_ok() {
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

    Ok((code, relocations, line_map))
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

        // Optimized path: `(local.get 0) >>> 32; wrap_i64`
        let ops_hi32 = vec![
            WasmOp::LocalGet(0), // i64 param in R0:R1
            WasmOp::I64Const(32),
            WasmOp::I64ShrU,
            WasmOp::I32WrapI64,
        ];
        let func_hi32 = backend
            .compile_function("hi32_extract", &ops_hi32, &config)
            .unwrap();

        // Generic path: `(local.get 0) >>> 7; wrap_i64` — same shape, but the
        // shift amount is not a multiple of 32, so it falls through to the
        // 38-byte runtime shift.
        let ops_generic = vec![
            WasmOp::LocalGet(0),
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
