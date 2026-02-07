//! Native test runner using direct Renode control
//!
//! This module provides a test runner that executes WAST tests directly
//! via the Renode telnet interface, without Robot Framework overhead.

use crate::renode::{to_signed, ExecutionResult, RenodeConfig, RenodeController, TrapReason};
use crate::renode::telnet::TelnetController;
use crate::{ParsedWast, Value, WastTestCase, WastTestType};
use anyhow::{Context, Result};
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// Test result for a single test case
#[derive(Debug, Clone)]
pub struct TestResult {
    pub name: String,
    pub passed: bool,
    pub expected: Option<Value>,
    pub actual: Option<Value>,
    pub error: Option<String>,
    pub duration_ms: u64,
}

/// Summary of test execution
#[derive(Debug, Clone, Default)]
pub struct TestSummary {
    pub total: usize,
    pub passed: usize,
    pub failed: usize,
    pub skipped: usize,
    pub duration_ms: u64,
}

/// Configuration for the native test runner
#[derive(Debug, Clone)]
pub struct RunnerConfig {
    /// Path to synth CLI binary
    pub synth_cli: String,
    /// Path to Renode binary
    pub renode_bin: String,
    /// Renode platform file
    pub platform_file: String,
    /// Renode connection config
    pub renode: RenodeConfig,
    /// Function address (with Thumb bit)
    pub func_addr: u32,
    /// Max steps per function execution
    pub max_steps: u32,
    /// Output directory for compiled ELFs
    pub output_dir: String,
    /// Keep Renode running between tests
    pub persistent_renode: bool,
}

impl Default for RunnerConfig {
    fn default() -> Self {
        Self {
            synth_cli: "synth".to_string(),
            renode_bin: "renode".to_string(),
            platform_file: "synth_cortex_m.repl".to_string(),
            renode: RenodeConfig::default(),
            func_addr: 0x91,
            max_steps: 50,
            output_dir: "/tmp/synth-test".to_string(),
            persistent_renode: true,
        }
    }
}

/// Native test runner for WAST tests
pub struct NativeRunner {
    /// Runner configuration
    pub config: RunnerConfig,
    /// Renode telnet controller
    pub controller: Option<TelnetController>,
    /// Renode process handle (if we started it)
    renode_process: Option<std::process::Child>,
}

impl NativeRunner {
    /// Create a new native test runner
    pub fn new(config: RunnerConfig) -> Self {
        Self {
            config,
            controller: None,
            renode_process: None,
        }
    }

    /// Start Renode process
    pub fn start_renode(&mut self) -> Result<()> {
        // Start Renode with telnet interface enabled
        let child = Command::new(&self.config.renode_bin)
            .args([
                "--disable-xwt",
                "--port", &self.config.renode.monitor_port.to_string(),
            ])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .context("Failed to start Renode")?;

        self.renode_process = Some(child);

        // Wait for Renode to start
        std::thread::sleep(Duration::from_millis(2000));

        // Connect telnet controller
        let mut controller = TelnetController::new(self.config.renode.clone());
        controller.connect().context("Failed to connect to Renode")?;
        self.controller = Some(controller);

        Ok(())
    }

    /// Stop Renode process
    pub fn stop_renode(&mut self) -> Result<()> {
        self.controller = None;
        if let Some(mut child) = self.renode_process.take() {
            let _ = child.kill();
            let _ = child.wait();
        }
        Ok(())
    }

    /// Compile a WAT module to ELF using Synth
    pub fn compile_module(&self, wat_path: &Path, elf_path: &Path) -> Result<()> {
        let output = Command::new(&self.config.synth_cli)
            .args([
                "compile",
                wat_path.to_str().unwrap(),
                "-o",
                elf_path.to_str().unwrap(),
                "--cortex-m",
            ])
            .output()
            .context("Failed to run synth compile")?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            anyhow::bail!("Synth compilation failed: {}", stderr);
        }

        Ok(())
    }

    /// Run a single test case
    pub fn run_test(&mut self, test: &WastTestCase, elf_path: &Path) -> Result<TestResult> {
        let start = Instant::now();

        let controller = self
            .controller
            .as_mut()
            .context("Renode not connected")?;

        // Set up machine if needed
        controller.create_machine("synth-test")?;
        controller.load_platform(&self.config.platform_file)?;
        controller.load_elf(elf_path.to_str().unwrap())?;

        // Convert arguments to unsigned
        let args: Vec<u32> = test.args.iter().map(|v| v.as_u32()).collect();

        // Execute function
        let result = controller.execute_function(
            self.config.func_addr,
            &args,
            self.config.max_steps,
        )?;

        let duration_ms = start.elapsed().as_millis() as u64;

        // Check result based on test type
        match (result, &test.test_type) {
            // assert_return: expect a value
            (ExecutionResult::Return(actual), WastTestType::AssertReturn) => {
                let actual_signed = to_signed(actual);
                let actual_value = Value::I32(actual_signed);

                let passed = match &test.expected {
                    Some(expected) => *expected == actual_value,
                    None => true, // No expected value = just check it doesn't crash
                };

                let error_msg = if passed {
                    None
                } else {
                    Some(format!("Expected {:?}, got {:?}", test.expected, actual_value))
                };

                Ok(TestResult {
                    name: test.name.clone(),
                    passed,
                    expected: test.expected.clone(),
                    actual: Some(actual_value),
                    error: error_msg,
                    duration_ms,
                })
            }

            // assert_trap: expect a trap that matches the expected message
            (ExecutionResult::Trap(reason), WastTestType::AssertTrap) => {
                let passed = test.expected_trap.as_ref().map_or(true, |msg| {
                    reason.matches_wast_message(msg)
                });

                let error_msg = if passed {
                    None
                } else {
                    Some(format!(
                        "Expected trap '{}', got {:?}",
                        test.expected_trap.as_deref().unwrap_or("any"),
                        reason
                    ))
                };

                Ok(TestResult {
                    name: test.name.clone(),
                    passed,
                    expected: test.expected.clone(),
                    actual: None,
                    error: error_msg,
                    duration_ms,
                })
            }

            // assert_trap but got a return: failure
            (ExecutionResult::Return(actual), WastTestType::AssertTrap) => {
                Ok(TestResult {
                    name: test.name.clone(),
                    passed: false,
                    expected: test.expected.clone(),
                    actual: Some(Value::I32(to_signed(actual))),
                    error: Some(format!(
                        "Expected trap '{}', but function returned {}",
                        test.expected_trap.as_deref().unwrap_or("trap"),
                        to_signed(actual)
                    )),
                    duration_ms,
                })
            }

            // assert_return but got a trap: failure
            (ExecutionResult::Trap(reason), WastTestType::AssertReturn) => {
                Ok(TestResult {
                    name: test.name.clone(),
                    passed: false,
                    expected: test.expected.clone(),
                    actual: None,
                    error: Some(format!("Unexpected trap: {:?}", reason)),
                    duration_ms,
                })
            }

            // Timeout is always a failure
            (ExecutionResult::Timeout, _) => {
                Ok(TestResult {
                    name: test.name.clone(),
                    passed: false,
                    expected: test.expected.clone(),
                    actual: None,
                    error: Some("Execution timed out".to_string()),
                    duration_ms,
                })
            }

            // Other test types
            (result, _) => {
                Ok(TestResult {
                    name: test.name.clone(),
                    passed: matches!(result, ExecutionResult::Return(_)),
                    expected: test.expected.clone(),
                    actual: None,
                    error: None,
                    duration_ms,
                })
            }
        }
    }

    /// Run all tests from a parsed WAST file
    pub fn run_all(&mut self, parsed: &ParsedWast, elf_path: &Path) -> Result<(Vec<TestResult>, TestSummary)> {
        let start = Instant::now();
        let mut results = Vec::new();
        let mut summary = TestSummary::default();

        for test in &parsed.test_cases {
            // Run assert_return and assert_trap tests
            if test.test_type != WastTestType::AssertReturn && test.test_type != WastTestType::AssertTrap {
                summary.skipped += 1;
                continue;
            }

            summary.total += 1;

            match self.run_test(test, elf_path) {
                Ok(result) => {
                    if result.passed {
                        summary.passed += 1;
                    } else {
                        summary.failed += 1;
                    }
                    results.push(result);
                }
                Err(e) => {
                    summary.failed += 1;
                    results.push(TestResult {
                        name: test.name.clone(),
                        passed: false,
                        expected: test.expected.clone(),
                        actual: None,
                        error: Some(format!("Test error: {}", e)),
                        duration_ms: 0,
                    });
                }
            }

            // Reset machine for next test
            if let Some(controller) = &mut self.controller {
                let _ = controller.reset();
            }
        }

        summary.duration_ms = start.elapsed().as_millis() as u64;

        Ok((results, summary))
    }
}

impl Drop for NativeRunner {
    fn drop(&mut self) {
        let _ = self.stop_renode();
    }
}

/// Print test results in a human-readable format
pub fn print_results(results: &[TestResult], summary: &TestSummary) {
    println!("\n=== Test Results ===\n");

    for result in results {
        let status = if result.passed { "PASS" } else { "FAIL" };
        print!("[{}] {} ", status, result.name);

        if result.passed {
            println!("({}ms)", result.duration_ms);
        } else {
            println!();
            if let Some(err) = &result.error {
                println!("      Error: {}", err);
            }
        }
    }

    println!("\n=== Summary ===");
    println!("Total:   {}", summary.total);
    println!("Passed:  {} ({:.1}%)", summary.passed,
             100.0 * summary.passed as f64 / summary.total.max(1) as f64);
    println!("Failed:  {}", summary.failed);
    println!("Skipped: {}", summary.skipped);
    println!("Time:    {}ms", summary.duration_ms);
}
