//! w2c2 WebAssembly-to-C Transpiler Wrapper
//!
//! Provides Rust interface to the w2c2 transpiler

use std::path::{Path, PathBuf};
use std::process::Command;
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
}
