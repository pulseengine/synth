//! Wasker Backend — external WASM-to-ELF compiler
//!
//! Wraps the wasker compiler (WASM→ELF relocatable object via LLVM).
//! Verification tier: binary-level translation validation (ASIL B).

use std::path::Path;
use std::process::Command;
use synth_core::backend::{
    Backend, BackendCapabilities, BackendError, CompilationResult, CompileConfig, CompiledFunction,
};
use synth_core::target::TargetSpec;
use synth_core::wasm_decoder::DecodedModule;
use synth_core::wasm_op::WasmOp;

/// Wasker backend — invokes the external `wasker` compiler
pub struct WaskerBackend {
    /// Path to the wasker executable (None = search PATH)
    wasker_path: Option<String>,
}

impl WaskerBackend {
    pub fn new() -> Self {
        Self { wasker_path: None }
    }

    pub fn with_path(path: impl Into<String>) -> Self {
        Self {
            wasker_path: Some(path.into()),
        }
    }

    fn find_executable(&self) -> Option<String> {
        if let Some(ref path) = self.wasker_path {
            if Path::new(path).exists() {
                return Some(path.clone());
            }
        }
        Command::new("which")
            .arg("wasker")
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
    }
}

impl Default for WaskerBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for WaskerBackend {
    fn name(&self) -> &str {
        "wasker"
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
        // Wasker targets are determined by LLVM backend
        vec![TargetSpec::cortex_m4(), TargetSpec::cortex_m7()]
    }

    fn compile_module(
        &self,
        _module: &DecodedModule,
        _config: &CompileConfig,
    ) -> Result<CompilationResult, BackendError> {
        let _exe = self.find_executable().ok_or_else(|| {
            BackendError::NotAvailable(
                "wasker not found. Install from https://github.com/aspect-build/wasker".to_string(),
            )
        })?;

        // TODO: Write WASM to temp file, invoke wasker, read output ELF
        Err(BackendError::CompilationFailed(
            "wasker module compilation not yet implemented".to_string(),
        ))
    }

    fn compile_function(
        &self,
        _name: &str,
        _ops: &[WasmOp],
        _config: &CompileConfig,
    ) -> Result<CompiledFunction, BackendError> {
        // Wasker compiles whole modules, not individual functions
        Err(BackendError::UnsupportedConfig(
            "wasker only supports whole-module compilation (use compile_module)".to_string(),
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
    fn test_wasker_backend_properties() {
        let backend = WaskerBackend::new();
        assert_eq!(backend.name(), "wasker");
        assert!(backend.capabilities().produces_elf);
        assert!(backend.capabilities().is_external);
        assert!(!backend.capabilities().supports_rule_verification);
        assert!(backend.capabilities().supports_binary_verification);
    }

    #[test]
    fn test_wasker_function_compilation_unsupported() {
        let backend = WaskerBackend::new();
        let config = CompileConfig::default();
        let result = backend.compile_function("test", &[WasmOp::I32Add], &config);
        assert!(result.is_err());
    }
}
