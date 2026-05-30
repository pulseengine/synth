//! ARM Backend — wraps the instruction selector + optimizer + encoder as a Backend
//!
//! This is Synth's custom ARM compiler targeting Cortex-M (Thumb-2).
//! It's the only backend that supports per-rule formal verification (ASIL D path).

use crate::ArmEncoder;
use synth_core::backend::{
    Backend, BackendCapabilities, BackendError, CodeRelocation, CompilationResult, CompileConfig,
    CompiledFunction, SafetyBounds,
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
            let compiled = self.compile_function(&name, &func.ops, config)?;
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
        let (code, relocations) =
            compile_wasm_to_arm(ops, config).map_err(BackendError::CompilationFailed)?;

        Ok(CompiledFunction {
            name: name.to_string(),
            code,
            wasm_ops: ops.to_vec(),
            relocations,
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
) -> Result<(Vec<u8>, Vec<CodeRelocation>), String> {
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
    let select_direct = || -> Result<Vec<ArmInstruction>, String> {
        let db = RuleDatabase::with_standard_rules();
        let mut selector =
            InstructionSelector::with_bounds_check(db.rules().to_vec(), bounds_config);
        selector.set_target(config.target.fpu, &config.target.triple);
        if config.num_imports > 0 {
            selector.set_num_imports(config.num_imports);
        }
        selector
            .select_with_stack(wasm_ops, num_params)
            .map_err(|e| format!("instruction selection failed: {}", e))
    };

    // Instruction selection: optimized or direct
    let arm_instrs = if config.no_optimize {
        select_direct()?
    } else {
        let opt_config = if config.loom_compat {
            OptimizationConfig::loom_compat()
        } else {
            OptimizationConfig::all()
        };

        let bridge = OptimizerBridge::with_config(opt_config);
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

    let mut code = Vec::new();
    let mut relocations = Vec::new();

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
            });
        }

        let encoded = encoder
            .encode(&instr.op)
            .map_err(|e| format!("ARM encoding failed: {}", e))?;
        code.extend_from_slice(&encoded);
    }

    Ok((code, relocations))
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

    #[test]
    fn test_compile_no_imports_no_relocations() {
        let backend = ArmBackend::new();
        let ops = vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::I32Add];
        let config = CompileConfig::default();

        let func = backend.compile_function("add", &ops, &config).unwrap();
        assert!(func.relocations.is_empty());
    }

    /// Regression test for #167: a call to an INTERNAL function (index
    /// >= num_imports) must record a relocation against `func_{index}`.
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
