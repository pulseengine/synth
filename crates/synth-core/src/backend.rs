//! Backend trait and registry for multi-backend compilation
//!
//! Every compiler backend (ARM, aWsm, wasker, w2c2) implements the `Backend`
//! trait, allowing the CLI and verification framework to treat them uniformly.

use crate::target::TargetSpec;
use crate::wasm_decoder::DecodedModule;
use crate::wasm_op::WasmOp;
use std::collections::HashMap;
use thiserror::Error;

/// Errors from backend compilation
#[derive(Debug, Error)]
pub enum BackendError {
    #[error("compilation failed: {0}")]
    CompilationFailed(String),

    #[error("backend not available: {0}")]
    NotAvailable(String),

    #[error("unsupported configuration: {0}")]
    UnsupportedConfig(String),

    #[error("external tool error: {0}")]
    ExternalToolError(String),
}

/// Configuration for a compilation run
#[derive(Debug, Clone)]
pub struct CompileConfig {
    /// Optimization level (0 = none, 1 = fast, 2 = default, 3 = aggressive)
    pub opt_level: u8,
    /// Target specification
    pub target: TargetSpec,
    /// Enable software bounds checking for memory operations
    pub bounds_check: bool,
    /// Hardware profile name (e.g. "nrf52840", "stm32f407")
    pub hardware: String,
    /// Skip optimization passes (direct instruction selection)
    pub no_optimize: bool,
    /// Use Loom-compatible optimization preset
    pub loom_compat: bool,
}

impl Default for CompileConfig {
    fn default() -> Self {
        Self {
            opt_level: 2,
            target: TargetSpec::cortex_m4(),
            bounds_check: false,
            hardware: String::new(),
            no_optimize: false,
            loom_compat: false,
        }
    }
}

/// A single compiled function
#[derive(Debug, Clone)]
pub struct CompiledFunction {
    /// Function name (from WASM export or generated)
    pub name: String,
    /// Raw machine code bytes
    pub code: Vec<u8>,
    /// Original WASM ops (retained for verification)
    pub wasm_ops: Vec<WasmOp>,
}

/// Result of compiling a full module
#[derive(Debug)]
pub struct CompilationResult {
    /// Compiled functions
    pub functions: Vec<CompiledFunction>,
    /// Complete ELF binary (if backend produces one directly)
    pub elf: Option<Vec<u8>>,
    /// Name of the backend that produced this result
    pub backend_name: String,
}

/// What a backend can and cannot do
#[derive(Debug, Clone)]
pub struct BackendCapabilities {
    /// Backend produces complete ELF files (external backends like aWsm)
    pub produces_elf: bool,
    /// Backend supports per-rule verification (only our custom ARM backend)
    pub supports_rule_verification: bool,
    /// Backend supports binary-level verification (all backends via disassembly)
    pub supports_binary_verification: bool,
    /// Backend is an external tool (not a library)
    pub is_external: bool,
}

/// Trait that every compilation backend implements
pub trait Backend: Send + Sync {
    /// Human-readable backend name
    fn name(&self) -> &str;

    /// What this backend can do
    fn capabilities(&self) -> BackendCapabilities;

    /// Which targets this backend supports
    fn supported_targets(&self) -> Vec<TargetSpec>;

    /// Compile an entire decoded WASM module
    fn compile_module(
        &self,
        module: &DecodedModule,
        config: &CompileConfig,
    ) -> std::result::Result<CompilationResult, BackendError>;

    /// Compile a single function from WASM ops to machine code
    fn compile_function(
        &self,
        name: &str,
        ops: &[WasmOp],
        config: &CompileConfig,
    ) -> std::result::Result<CompiledFunction, BackendError>;

    /// Check if this backend is available (external tools installed, etc.)
    fn is_available(&self) -> bool;
}

/// Registry of available backends
pub struct BackendRegistry {
    backends: HashMap<String, Box<dyn Backend>>,
}

impl BackendRegistry {
    pub fn new() -> Self {
        Self {
            backends: HashMap::new(),
        }
    }

    /// Register a backend under its name
    pub fn register(&mut self, backend: Box<dyn Backend>) {
        let name = backend.name().to_string();
        self.backends.insert(name, backend);
    }

    /// Get a backend by name
    pub fn get(&self, name: &str) -> Option<&dyn Backend> {
        self.backends.get(name).map(|b| b.as_ref())
    }

    /// List all registered backends
    pub fn list(&self) -> Vec<&dyn Backend> {
        self.backends.values().map(|b| b.as_ref()).collect()
    }

    /// List backends that are actually available (installed and working)
    pub fn available(&self) -> Vec<&dyn Backend> {
        self.backends
            .values()
            .filter(|b| b.is_available())
            .map(|b| b.as_ref())
            .collect()
    }
}

impl Default for BackendRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_registry_empty() {
        let reg = BackendRegistry::new();
        assert!(reg.list().is_empty());
        assert!(reg.available().is_empty());
        assert!(reg.get("arm").is_none());
    }

    #[test]
    fn test_compile_config_default() {
        let config = CompileConfig::default();
        assert_eq!(config.opt_level, 2);
        assert!(!config.bounds_check);
        assert!(!config.no_optimize);
    }
}
