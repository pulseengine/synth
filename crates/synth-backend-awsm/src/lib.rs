//! aWsm Backend — external AOT WebAssembly compiler
//!
//! Wraps the aWsm compiler (ahead-of-time WASM→native via LLVM).
//! Verification tier: binary-level translation validation (ASIL B).

use std::path::Path;
use std::process::Command;
use synth_core::backend::{
    Backend, BackendCapabilities, BackendError, CompilationResult, CompileConfig, CompiledFunction,
};
use synth_core::target::TargetSpec;
use synth_core::wasm_decoder::DecodedModule;
use synth_core::wasm_op::WasmOp;

/// aWsm backend — invokes the external `awsm` compiler
pub struct AwsmBackend {
    /// Path to the awsm executable (None = search PATH)
    awsm_path: Option<String>,
}

impl AwsmBackend {
    pub fn new() -> Self {
        Self { awsm_path: None }
    }

    pub fn with_path(path: impl Into<String>) -> Self {
        Self {
            awsm_path: Some(path.into()),
        }
    }

    fn find_executable(&self) -> Option<String> {
        if let Some(ref path) = self.awsm_path {
            if Path::new(path).exists() {
                return Some(path.clone());
            }
        }
        // Search PATH
        Command::new("which")
            .arg("awsm")
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
    }
}

impl Default for AwsmBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for AwsmBackend {
    fn name(&self) -> &str {
        "awsm"
    }

    fn capabilities(&self) -> BackendCapabilities {
        BackendCapabilities {
            produces_elf: true,
            supports_rule_verification: false,
            supports_binary_verification: true,
            is_external: true,
        }
    }

    fn supported_targets(&self) -> Vec<TargetSpec> {
        // aWsm supports whatever LLVM supports — Cortex-M, RISC-V, etc.
        vec![TargetSpec::cortex_m4(), TargetSpec::cortex_m7()]
    }

    fn compile_module(
        &self,
        _module: &DecodedModule,
        _config: &CompileConfig,
    ) -> Result<CompilationResult, BackendError> {
        let _exe = self.find_executable().ok_or_else(|| {
            BackendError::NotAvailable(
                "awsm not found. Install from https://github.com/aspect-build/aspect-workflows"
                    .to_string(),
            )
        })?;

        // TODO: Write WASM to temp file, invoke awsm, read output ELF
        Err(BackendError::CompilationFailed(
            "aWsm module compilation not yet implemented".to_string(),
        ))
    }

    fn compile_function(
        &self,
        _name: &str,
        _ops: &[WasmOp],
        _config: &CompileConfig,
    ) -> Result<CompiledFunction, BackendError> {
        // aWsm compiles whole modules, not individual functions
        Err(BackendError::UnsupportedConfig(
            "aWsm only supports whole-module compilation (use compile_module)".to_string(),
        ))
    }

    fn is_available(&self) -> bool {
        self.find_executable().is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_awsm_backend_properties() {
        let backend = AwsmBackend::new();
        assert_eq!(backend.name(), "awsm");
        assert!(backend.capabilities().produces_elf);
        assert!(backend.capabilities().is_external);
        assert!(!backend.capabilities().supports_rule_verification);
        assert!(backend.capabilities().supports_binary_verification);
    }

    #[test]
    fn test_awsm_function_compilation_unsupported() {
        let backend = AwsmBackend::new();
        let config = CompileConfig::default();
        let result = backend.compile_function("test", &[WasmOp::I32Add], &config);
        assert!(result.is_err());
    }
}
