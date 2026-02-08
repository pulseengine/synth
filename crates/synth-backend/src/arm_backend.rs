//! ARM Backend — wraps the instruction selector + optimizer + encoder as a Backend
//!
//! This is Synth's custom ARM compiler targeting Cortex-M (Thumb-2).
//! It's the only backend that supports per-rule formal verification (ASIL D path).

use crate::ArmEncoder;
use synth_core::backend::{
    Backend, BackendCapabilities, BackendError, CompilationResult, CompileConfig, CompiledFunction,
};
use synth_core::target::{IsaVariant, TargetSpec};
use synth_core::wasm_decoder::DecodedModule;
use synth_core::wasm_op::WasmOp;
use synth_synthesis::{
    ArmInstruction, BoundsCheckConfig, InstructionSelector, OptimizationConfig, OptimizerBridge,
    RuleDatabase,
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
        vec![TargetSpec::cortex_m4(), TargetSpec::cortex_m7()]
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
        let code =
            compile_wasm_to_arm(ops, config).map_err(|e| BackendError::CompilationFailed(e))?;

        Ok(CompiledFunction {
            name: name.to_string(),
            code,
            wasm_ops: ops.to_vec(),
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
                if is_read_first {
                    Some(idx + 1)
                } else {
                    None
                }
            },
        )
        .max()
        .unwrap_or(0)
}

/// Core compilation: WASM ops → ARM machine code bytes
fn compile_wasm_to_arm(wasm_ops: &[WasmOp], config: &CompileConfig) -> Result<Vec<u8>, String> {
    let num_params = count_params(wasm_ops);

    let bounds_config = if config.bounds_check {
        BoundsCheckConfig::Software
    } else {
        BoundsCheckConfig::None
    };

    // Instruction selection: optimized or direct
    let arm_instrs = if config.no_optimize {
        let db = RuleDatabase::with_standard_rules();
        let mut selector =
            InstructionSelector::with_bounds_check(db.rules().to_vec(), bounds_config);
        selector
            .select_with_stack(wasm_ops, num_params)
            .map_err(|e| format!("instruction selection failed: {}", e))?
    } else {
        let opt_config = if config.loom_compat {
            OptimizationConfig::loom_compat()
        } else {
            OptimizationConfig::all()
        };

        let bridge = OptimizerBridge::with_config(opt_config);
        let (opt_ir, _cfg, _stats) = bridge
            .optimize_full(wasm_ops)
            .map_err(|e| format!("optimization failed: {}", e))?;

        let arm_ops = bridge.ir_to_arm(&opt_ir, num_params as usize);
        arm_ops
            .into_iter()
            .map(|op| ArmInstruction {
                op,
                source_line: None,
            })
            .collect()
    };

    // Encode to binary — use Thumb-2 for Cortex-M targets
    let use_thumb2 = matches!(config.target.isa, IsaVariant::Thumb2 | IsaVariant::Thumb);

    let encoder = if use_thumb2 {
        ArmEncoder::new_thumb2()
    } else {
        ArmEncoder::new_arm32()
    };

    let mut code = Vec::new();
    for instr in &arm_instrs {
        let encoded = encoder
            .encode(&instr.op)
            .map_err(|e| format!("ARM encoding failed: {}", e))?;
        code.extend_from_slice(&encoded);
    }

    Ok(code)
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
}
