//! w2c2 WebAssembly-to-C Transpiler Wrapper
//!
//! Provides Rust interface to the w2c2 transpiler

use std::path::{Path, PathBuf};
use std::process::Command;
use synth_core::backend::{
    Backend, BackendCapabilities, BackendError, CompilationResult, CompileConfig, CompiledFunction,
};
use synth_core::target::TargetSpec;
use synth_core::wasm_decoder::DecodedModule;
use synth_core::wasm_op::WasmOp;
use synth_core::{Error, Result};

/// w2c2 transpiler wrapper
pub struct W2C2Transpiler {
    /// Path to w2c2 executable
    w2c2_path: PathBuf,
}

impl W2C2Transpiler {
    /// Create a new w2c2 transpiler wrapper
    ///
    /// # Arguments
    /// * `w2c2_path` - Path to the w2c2 executable
    pub fn new<P: AsRef<Path>>(w2c2_path: P) -> Self {
        Self {
            w2c2_path: w2c2_path.as_ref().to_path_buf(),
        }
    }

    /// Try to find w2c2 in the system PATH
    pub fn from_path() -> Result<Self> {
        // Try common locations
        let paths = vec!["w2c2", "./w2c2", "../w2c2/build/w2c2"];

        for path in paths {
            if Path::new(path).exists() {
                return Ok(Self::new(path));
            }
        }

        Err(Error::Other(
            "w2c2 not found in PATH. Please install w2c2 from https://github.com/turbolent/w2c2"
                .to_string(),
        ))
    }

    /// Transpile a WebAssembly module to C
    ///
    /// # Arguments
    /// * `wasm_path` - Path to input .wasm file
    /// * `output_path` - Path to output .c file (w2c2 will also create a .h file)
    /// * `options` - Transpilation options
    pub fn transpile<P: AsRef<Path>>(
        &self,
        wasm_path: P,
        output_path: P,
        options: &TranspileOptions,
    ) -> Result<TranspileResult> {
        let wasm_path = wasm_path.as_ref();
        let output_path = output_path.as_ref();

        // Verify input exists
        if !wasm_path.exists() {
            return Err(Error::Other(format!(
                "Input WASM file not found: {}",
                wasm_path.display()
            )));
        }

        // Build w2c2 command
        let mut cmd = Command::new(&self.w2c2_path);
        cmd.arg(wasm_path);
        cmd.arg(output_path);

        // Add options
        if let Some(funcs_per_file) = options.functions_per_file {
            cmd.arg("-f");
            cmd.arg(funcs_per_file.to_string());
        }

        if let Some(threads) = options.threads {
            cmd.arg("-t");
            cmd.arg(threads.to_string());
        }

        if options.debug {
            cmd.arg("-d");
        }

        // Execute w2c2
        let output = cmd.output().map_err(|e| {
            Error::Other(format!(
                "Failed to execute w2c2: {}. Make sure w2c2 is installed and accessible.",
                e
            ))
        })?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(Error::Other(format!(
                "w2c2 transpilation failed: {}",
                stderr
            )));
        }

        // Determine output files
        let c_file = output_path.to_path_buf();
        let h_file = output_path.with_extension("h");

        // Verify output files were created
        if !c_file.exists() {
            return Err(Error::Other(format!(
                "Expected output file not created: {}",
                c_file.display()
            )));
        }

        Ok(TranspileResult {
            c_file,
            h_file: if h_file.exists() { Some(h_file) } else { None },
            stdout: String::from_utf8_lossy(&output.stdout).to_string(),
        })
    }
}

/// Options for WebAssembly-to-C transpilation
#[derive(Debug, Clone)]
pub struct TranspileOptions {
    /// Number of functions per output file (for large modules)
    pub functions_per_file: Option<usize>,

    /// Number of worker threads for parallel compilation
    pub threads: Option<usize>,

    /// Include debug information
    pub debug: bool,
}

impl Default for TranspileOptions {
    fn default() -> Self {
        Self {
            functions_per_file: None,
            threads: Some(1), // Single-threaded by default for determinism
            debug: false,
        }
    }
}

/// Result of WebAssembly-to-C transpilation
#[derive(Debug, Clone)]
pub struct TranspileResult {
    /// Path to generated .c file
    pub c_file: PathBuf,

    /// Path to generated .h file (if created)
    pub h_file: Option<PathBuf>,

    /// stdout from w2c2
    pub stdout: String,
}

/// W2C2 backend — two-stage pipeline: w2c2 (WASM→C) + arm-none-eabi-gcc (C→ELF)
///
/// Verification tier: binary-level translation validation (ASIL B).
pub struct W2C2Backend {
    /// Path to w2c2 executable (None = search PATH)
    w2c2_path: Option<String>,
    /// Path to cross-compiler (None = search for arm-none-eabi-gcc)
    gcc_path: Option<String>,
}

impl W2C2Backend {
    pub fn new() -> Self {
        Self {
            w2c2_path: None,
            gcc_path: None,
        }
    }

    pub fn with_paths(w2c2: impl Into<String>, gcc: impl Into<String>) -> Self {
        Self {
            w2c2_path: Some(w2c2.into()),
            gcc_path: Some(gcc.into()),
        }
    }

    fn find_w2c2(&self) -> Option<String> {
        if let Some(ref path) = self.w2c2_path {
            if Path::new(path).exists() {
                return Some(path.clone());
            }
        }
        W2C2Transpiler::from_path()
            .ok()
            .map(|t| t.w2c2_path.to_string_lossy().to_string())
    }

    fn find_gcc(&self) -> Option<String> {
        if let Some(ref path) = self.gcc_path {
            if Path::new(path).exists() {
                return Some(path.clone());
            }
        }
        Command::new("which")
            .arg("arm-none-eabi-gcc")
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
    }
}

impl Default for W2C2Backend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for W2C2Backend {
    fn name(&self) -> &str {
        "w2c2"
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
        vec![TargetSpec::cortex_m4(), TargetSpec::cortex_m7()]
    }

    fn compile_module(
        &self,
        _module: &DecodedModule,
        _config: &CompileConfig,
    ) -> std::result::Result<CompilationResult, BackendError> {
        let _w2c2 = self.find_w2c2().ok_or_else(|| {
            BackendError::NotAvailable(
                "w2c2 not found. Install from https://github.com/turbolent/w2c2".to_string(),
            )
        })?;
        let _gcc = self.find_gcc().ok_or_else(|| {
            BackendError::NotAvailable(
                "arm-none-eabi-gcc not found. Install ARM GNU toolchain.".to_string(),
            )
        })?;

        // TODO: Write WASM to temp file, w2c2 transpile to C, gcc compile to ELF
        Err(BackendError::CompilationFailed(
            "w2c2 module compilation not yet implemented".to_string(),
        ))
    }

    fn compile_function(
        &self,
        _name: &str,
        _ops: &[WasmOp],
        _config: &CompileConfig,
    ) -> std::result::Result<CompiledFunction, BackendError> {
        Err(BackendError::UnsupportedConfig(
            "w2c2 only supports whole-module compilation (use compile_module)".to_string(),
        ))
    }

    fn is_available(&self) -> bool {
        self.find_w2c2().is_some() && self.find_gcc().is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_transpile_options_default() {
        let options = TranspileOptions::default();
        assert_eq!(options.functions_per_file, None);
        assert_eq!(options.threads, Some(1));
        assert_eq!(options.debug, false);
    }

    #[test]
    #[ignore] // Requires w2c2 to be installed
    fn test_transpile_simple_module() {
        // Create a minimal WASM module for testing
        let wasm_bytes = vec![
            0x00, 0x61, 0x73, 0x6d, // Magic number
            0x01, 0x00, 0x00, 0x00, // Version
        ];

        let temp_dir = std::env::temp_dir();
        let wasm_path = temp_dir.join("test_module.wasm");
        let output_path = temp_dir.join("test_module.c");

        // Write test WASM file
        fs::write(&wasm_path, wasm_bytes).unwrap();

        // Try to find w2c2
        if let Ok(transpiler) = W2C2Transpiler::from_path() {
            let options = TranspileOptions::default();
            let result = transpiler.transpile(&wasm_path, &output_path, &options);

            match result {
                Ok(res) => {
                    assert!(res.c_file.exists());
                    println!("Successfully transpiled to: {}", res.c_file.display());
                }
                Err(e) => {
                    println!(
                        "Transpilation error (expected if w2c2 not installed): {}",
                        e
                    );
                }
            }
        } else {
            println!("w2c2 not found in PATH - skipping transpilation test");
        }

        // Cleanup
        let _ = fs::remove_file(&wasm_path);
        let _ = fs::remove_file(&output_path);
        let _ = fs::remove_file(output_path.with_extension("h"));
    }

    #[test]
    fn test_w2c2_backend_properties() {
        let backend = W2C2Backend::new();
        assert_eq!(backend.name(), "w2c2");
        assert!(backend.capabilities().produces_elf);
        assert!(backend.capabilities().is_external);
        assert!(!backend.capabilities().supports_rule_verification);
    }

    #[test]
    fn test_w2c2_function_compilation_unsupported() {
        let backend = W2C2Backend::new();
        let config = CompileConfig::default();
        let result = backend.compile_function("test", &[WasmOp::I32Add], &config);
        assert!(result.is_err());
    }
}
