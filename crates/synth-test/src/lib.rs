//! WAST-driven test runner for Synth
//!
//! This crate provides a test runner that parses WebAssembly spec test (WAST) files
//! and executes them on Renode via Synth-compiled ARM binaries.
//!
//! # Architecture
//!
//! ```text
//! .wast file → WastParser → TestCases → Synth CLI → ELF → Renode → Results
//! ```
//!
//! # Backends
//!
//! - **Robot Framework** - Simple, works with rules_renode (current)
//! - **Telnet** - Direct Renode control, lower overhead (recommended)
//! - **GDB** - Trap detection, debugging (future)
//!
//! Key differences from wrt2:
//! - wrt2 executes WASM directly in its runtime
//! - Synth compiles WASM to ARM ELF and executes on Renode emulator

pub mod renode;
pub mod runner;

use anyhow::{Context, Result};
use object::{Object, ObjectSymbol};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use wast::core::{WastArgCore, WastRetCore};
use wast::parser::{self, ParseBuffer};
use wast::{Wast, WastArg, WastDirective, WastExecute, WastInvoke, WastRet};

/// Read function symbols from an ELF file
/// Returns a map of function name -> address (with Thumb bit for Cortex-M)
pub fn read_elf_symbols(elf_path: &Path) -> Result<HashMap<String, u32>> {
    let data = std::fs::read(elf_path)
        .with_context(|| format!("Failed to read ELF file: {}", elf_path.display()))?;

    let file = object::File::parse(&*data)
        .with_context(|| format!("Failed to parse ELF file: {}", elf_path.display()))?;

    let mut symbols = HashMap::new();

    for symbol in file.symbols() {
        // Only include function symbols
        if symbol.kind() == object::SymbolKind::Text {
            if let Ok(name) = symbol.name() {
                // Skip internal symbols (starting with $ or .)
                if !name.starts_with('$') && !name.starts_with('.') && !name.is_empty() {
                    let addr = symbol.address() as u32;
                    symbols.insert(name.to_string(), addr);
                }
            }
        }
    }

    Ok(symbols)
}

/// Value types supported for function arguments and returns
/// Simplified from wrt2's full Value enum - we only support i32 for now
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Value {
    I32(i32),
    I64(i64),
    // Future: F32, F64
}

impl Value {
    /// Convert to u32 for register storage (sign-preserving)
    pub fn as_u32(&self) -> u32 {
        match self {
            Value::I32(v) => *v as u32,
            Value::I64(v) => *v as u32, // Low 32 bits only
        }
    }

    /// Convert to u64 for 64-bit values
    pub fn as_u64(&self) -> u64 {
        match self {
            Value::I32(v) => *v as u32 as u64, // Zero-extend
            Value::I64(v) => *v as u64,
        }
    }

    /// Check if this is a 64-bit value
    pub fn is_64bit(&self) -> bool {
        matches!(self, Value::I64(_))
    }
}

/// Convert WAST arguments to our Value type
/// Modeled after wrt2/wrt-build-core/src/wast_values.rs
pub fn convert_wast_arg_to_value(arg: &WastArg) -> Result<Value> {
    match arg {
        WastArg::Core(core_arg) => convert_wast_arg_core_to_value(core_arg),
        #[allow(unreachable_patterns)]
        _ => Err(anyhow::anyhow!("Unsupported WAST argument type")),
    }
}

fn convert_wast_arg_core_to_value(arg: &WastArgCore) -> Result<Value> {
    match arg {
        WastArgCore::I32(x) => Ok(Value::I32(*x)),
        WastArgCore::I64(x) => Ok(Value::I64(*x)),
        _ => Err(anyhow::anyhow!(
            "Unsupported WAST arg type (only i32/i64 supported for now)"
        )),
    }
}

/// Convert WAST expected results to our Value type
pub fn convert_wast_ret_to_value(ret: &WastRet) -> Result<Value> {
    match ret {
        WastRet::Core(core_ret) => convert_wast_ret_core_to_value(core_ret),
        #[allow(unreachable_patterns)]
        _ => Err(anyhow::anyhow!("Unsupported WAST return type")),
    }
}

fn convert_wast_ret_core_to_value(ret: &WastRetCore) -> Result<Value> {
    match ret {
        WastRetCore::I32(x) => Ok(Value::I32(*x)),
        WastRetCore::I64(x) => Ok(Value::I64(*x)),
        _ => Err(anyhow::anyhow!(
            "Unsupported WAST return type (only i32/i64 supported for now)"
        )),
    }
}

/// A single test case extracted from a WAST file
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WastTestCase {
    /// Unique name for this test case
    pub name: String,
    /// Function to invoke
    pub function: String,
    /// Arguments to pass
    pub args: Vec<Value>,
    /// Expected return value (for assert_return)
    pub expected: Option<Value>,
    /// Expected trap message (for assert_trap)
    pub expected_trap: Option<String>,
    /// Source line/offset for error reporting
    pub source_offset: usize,
    /// Test type classification
    pub test_type: WastTestType,
}

/// Classification of WAST test types (from wrt2)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum WastTestType {
    /// Correctness tests (assert_return)
    AssertReturn,
    /// Trap tests (assert_trap) - not yet supported
    AssertTrap,
    /// Invoke without assertion
    Invoke,
    /// Module definition
    Module,
    /// Skipped (unsupported directive)
    Skipped,
}

/// Statistics for test execution (from wrt2 pattern)
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct WastTestStats {
    pub modules_loaded: usize,
    pub assert_return_count: usize,
    pub assert_trap_count: usize,
    pub invoke_count: usize,
    pub passed: usize,
    pub failed: usize,
    pub skipped: usize,
}

/// Parsed WAST file ready for test generation
#[derive(Debug)]
pub struct ParsedWast {
    /// Test cases extracted from directives
    pub test_cases: Vec<WastTestCase>,
    /// Current module WAT source (binary)
    pub current_module_binary: Option<Vec<u8>>,
    /// Module name to binary mapping
    pub modules: HashMap<String, Vec<u8>>,
    /// Statistics
    pub stats: WastTestStats,
}

/// WAST parser that extracts test cases
/// Modeled after wrt2/wrt-build-core/src/wast.rs WastTestRunner
pub struct WastParser;

impl WastParser {
    /// Parse a WAST file from path
    pub fn parse_file(path: &Path) -> Result<ParsedWast> {
        let contents = std::fs::read_to_string(path)
            .with_context(|| format!("Failed to read WAST file: {}", path.display()))?;
        Self::parse_str(&contents)
    }

    /// Parse WAST content from string
    pub fn parse_str(contents: &str) -> Result<ParsedWast> {
        let buf = ParseBuffer::new(contents)
            .map_err(|e| anyhow::anyhow!("Failed to create parse buffer: {}", e))?;

        let wast = parser::parse::<Wast>(&buf)
            .map_err(|e| anyhow::anyhow!("Failed to parse WAST: {}", e))?;

        let mut result = ParsedWast {
            test_cases: Vec::new(),
            current_module_binary: None,
            modules: HashMap::new(),
            stats: WastTestStats::default(),
        };

        let mut test_counter = 0;

        for directive in wast.directives {
            Self::process_directive(directive, &mut result, &mut test_counter)?;
        }

        Ok(result)
    }

    fn process_directive(
        directive: WastDirective,
        result: &mut ParsedWast,
        test_counter: &mut usize,
    ) -> Result<()> {
        match directive {
            WastDirective::Module(mut quote_wat) => {
                // Encode module to binary
                let binary = quote_wat
                    .encode()
                    .map_err(|e| anyhow::anyhow!("Failed to encode module: {}", e))?;

                // Store as current module
                result.current_module_binary = Some(binary.clone());

                // Also store by name if named
                let name = quote_wat.name().map(|id| id.name().to_string());
                if let Some(n) = name {
                    result.modules.insert(n, binary);
                } else {
                    result.modules.insert("$current".to_string(), binary);
                }

                result.stats.modules_loaded += 1;
            }

            WastDirective::AssertReturn { exec, results, .. } => {
                if let Some(test_case) = Self::process_assert_return(&exec, &results, test_counter)?
                {
                    result.test_cases.push(test_case);
                    result.stats.assert_return_count += 1;
                }
            }

            WastDirective::AssertTrap { exec, message, .. } => {
                if let Some(test_case) = Self::process_assert_trap(&exec, message, test_counter)? {
                    result.test_cases.push(test_case);
                    result.stats.assert_trap_count += 1;
                } else {
                    result.stats.skipped += 1;
                }
            }

            WastDirective::Invoke(invoke) => {
                if let Some(test_case) = Self::process_invoke(&invoke, test_counter)? {
                    result.test_cases.push(test_case);
                    result.stats.invoke_count += 1;
                }
            }

            // Skip unsupported directives
            _ => {
                result.stats.skipped += 1;
            }
        }

        Ok(())
    }

    fn process_assert_return(
        exec: &WastExecute,
        results: &[WastRet],
        test_counter: &mut usize,
    ) -> Result<Option<WastTestCase>> {
        let invoke = match exec {
            WastExecute::Invoke(inv) => inv,
            _ => return Ok(None), // Skip non-invoke assertions
        };

        // Convert arguments
        let args: Result<Vec<Value>> = invoke.args.iter().map(convert_wast_arg_to_value).collect();
        let args = match args {
            Ok(a) => a,
            Err(e) => {
                tracing::debug!("Skipping test with unsupported arg type: {}", e);
                return Ok(None);
            }
        };

        // Convert expected results
        let expected: Result<Vec<Value>> = results.iter().map(convert_wast_ret_to_value).collect();
        let expected = match expected {
            Ok(e) => e.into_iter().next(), // Only single return for now
            Err(e) => {
                tracing::debug!("Skipping test with unsupported return type: {}", e);
                return Ok(None);
            }
        };

        *test_counter += 1;

        Ok(Some(WastTestCase {
            name: format!("{}_{}", invoke.name, test_counter),
            function: invoke.name.to_string(),
            args,
            expected,
            expected_trap: None,
            source_offset: invoke.span.offset(),
            test_type: WastTestType::AssertReturn,
        }))
    }

    fn process_assert_trap(
        exec: &WastExecute,
        message: &str,
        test_counter: &mut usize,
    ) -> Result<Option<WastTestCase>> {
        let invoke = match exec {
            WastExecute::Invoke(inv) => inv,
            _ => return Ok(None), // Skip non-invoke assertions
        };

        // Convert arguments
        let args: Result<Vec<Value>> = invoke.args.iter().map(convert_wast_arg_to_value).collect();
        let args = match args {
            Ok(a) => a,
            Err(e) => {
                tracing::debug!("Skipping assert_trap with unsupported arg type: {}", e);
                return Ok(None);
            }
        };

        *test_counter += 1;

        Ok(Some(WastTestCase {
            name: format!("trap_{}_{}", invoke.name, test_counter),
            function: invoke.name.to_string(),
            args,
            expected: None,
            expected_trap: Some(message.to_string()),
            source_offset: invoke.span.offset(),
            test_type: WastTestType::AssertTrap,
        }))
    }

    fn process_invoke(
        invoke: &WastInvoke,
        test_counter: &mut usize,
    ) -> Result<Option<WastTestCase>> {
        let args: Result<Vec<Value>> = invoke.args.iter().map(convert_wast_arg_to_value).collect();
        let args = match args {
            Ok(a) => a,
            Err(_) => return Ok(None),
        };

        *test_counter += 1;

        Ok(Some(WastTestCase {
            name: format!("invoke_{}_{}", invoke.name, test_counter),
            function: invoke.name.to_string(),
            args,
            expected: None,
            expected_trap: None,
            source_offset: invoke.span.offset(),
            test_type: WastTestType::Invoke,
        }))
    }
}

/// Configuration for the Synth+Renode test execution
#[derive(Debug, Clone)]
pub struct SynthTestConfig {
    /// Path to synth CLI binary
    pub synth_cli: PathBuf,
    /// Path to Renode platform file
    pub platform_file: PathBuf,
    /// Output directory for generated artifacts
    pub output_dir: PathBuf,
    /// Function address in the generated ELF (default: 0x90 with Thumb bit)
    /// Used as fallback when function_addresses is empty
    pub function_address: u32,
    /// Per-function addresses from ELF symbol table (function name -> address)
    pub function_addresses: HashMap<String, u32>,
    /// Default_Handler address (infinite loop trap for return detection)
    pub default_handler_address: u32,
    /// Trap_Handler address (for WASM trap detection: div by zero, overflow)
    pub trap_handler_address: u32,
}

impl Default for SynthTestConfig {
    fn default() -> Self {
        Self {
            synth_cli: PathBuf::from("synth"),
            platform_file: PathBuf::from("synth_cortex_m.repl"),
            output_dir: PathBuf::from("/tmp/synth-tests"),
            function_address: 0x91, // 0x90 with Thumb bit set
            function_addresses: HashMap::new(),
            default_handler_address: 0x8C, // Default_Handler: infinite loop (b .)
            trap_handler_address: 0x8E,    // Trap_Handler: infinite loop for WASM traps
        }
    }
}

impl SynthTestConfig {
    /// Get address for a specific function, falling back to default
    pub fn get_function_address(&self, func_name: &str) -> u32 {
        self.function_addresses
            .get(func_name)
            .copied()
            .unwrap_or(self.function_address)
    }

    /// Load function addresses from an ELF file
    pub fn with_elf_symbols(mut self, elf_path: &Path) -> Result<Self> {
        self.function_addresses = read_elf_symbols(elf_path)?;

        // Also read handler addresses from symbols
        // Strip the Thumb bit (bit 0) since PC values don't include it
        if let Some(addr) = self.function_addresses.get("Default_Handler") {
            self.default_handler_address = *addr & !1; // Strip Thumb bit
        }
        if let Some(addr) = self.function_addresses.get("Trap_Handler") {
            self.trap_handler_address = *addr & !1; // Strip Thumb bit
        }

        Ok(self)
    }
}

/// Options for test generation
#[derive(Debug, Default, Clone)]
pub struct GenerateOptions {
    /// Only generate tests for these functions (if empty, all functions)
    pub filter_funcs: Vec<String>,
}

impl GenerateOptions {
    /// Create options with function filter
    pub fn with_filter(funcs: Vec<String>) -> Self {
        Self {
            filter_funcs: funcs,
        }
    }

    /// Check if a function should be included
    pub fn should_include(&self, func_name: &str) -> bool {
        self.filter_funcs.is_empty() || self.filter_funcs.iter().any(|f| f == func_name)
    }
}

/// Robot Framework test generator for Renode
pub struct RobotGenerator;

impl RobotGenerator {
    /// Generate a Robot Framework test file from parsed WAST
    pub fn generate(
        parsed: &ParsedWast,
        config: &SynthTestConfig,
        output_path: &Path,
    ) -> Result<String> {
        Self::generate_with_options(parsed, config, output_path, &GenerateOptions::default())
    }

    /// Generate Robot test file with filtering options
    pub fn generate_with_options(
        parsed: &ParsedWast,
        config: &SynthTestConfig,
        output_path: &Path,
        options: &GenerateOptions,
    ) -> Result<String> {
        let mut robot = String::new();

        // Settings
        robot.push_str("*** Settings ***\n");
        robot.push_str(
            "Documentation     WAST-driven tests for Synth (auto-generated from .wast file)\n\n",
        );

        // Variables
        robot.push_str("*** Variables ***\n");
        robot.push_str(&format!(
            "${{PLATFORM}}    {}\n",
            config.platform_file.display()
        ));

        // Collect unique functions to generate per-function address variables
        let mut unique_funcs: std::collections::HashSet<&str> = std::collections::HashSet::new();
        for test_case in &parsed.test_cases {
            // Collect function addresses for both AssertReturn and AssertTrap tests
            if (test_case.test_type == WastTestType::AssertReturn
                || test_case.test_type == WastTestType::AssertTrap)
                && options.should_include(&test_case.function)
            {
                unique_funcs.insert(&test_case.function);
            }
        }

        // Generate per-function address variables if we have ELF symbols
        if !config.function_addresses.is_empty() {
            for func_name in &unique_funcs {
                let addr = config.get_function_address(func_name);
                // Create Robot-safe variable name (replace special chars)
                let var_name = func_name.replace('-', "_").replace('.', "_").to_uppercase();
                robot.push_str(&format!("${{FUNC_{}_ADDR}}    0x{:X}\n", var_name, addr));
            }
        } else {
            // Fall back to single address for all functions
            robot.push_str(&format!(
                "${{FUNC_ADDR}}    0x{:X}\n",
                config.function_address
            ));
        }

        robot.push_str(&format!(
            "${{RETURN_TRAP}}    0x{:X}\n",
            config.default_handler_address
        ));
        robot.push_str(&format!(
            "${{TRAP_HANDLER}}    0x{:X}\n\n",
            config.trap_handler_address
        ));

        // Keywords
        robot.push_str("*** Keywords ***\n");
        robot.push_str(Self::generate_keywords());
        robot.push_str("\n");

        // Test Cases
        robot.push_str("*** Test Cases ***\n");
        let mut included = 0;
        let mut skipped = 0;
        for test_case in &parsed.test_cases {
            if options.should_include(&test_case.function) {
                match test_case.test_type {
                    WastTestType::AssertReturn => {
                        robot.push_str(&Self::generate_test_case_with_config(test_case, config));
                        robot.push_str("\n");
                        included += 1;
                    }
                    WastTestType::AssertTrap => {
                        robot.push_str(&Self::generate_trap_test_case(test_case, config));
                        robot.push_str("\n");
                        included += 1;
                    }
                    _ => {
                        skipped += 1;
                    }
                }
            } else {
                skipped += 1;
            }
        }

        if !options.filter_funcs.is_empty() {
            eprintln!(
                "Filtered tests: {} included, {} skipped (filter: {:?})",
                included, skipped, options.filter_funcs
            );
        }

        // Write to file
        std::fs::create_dir_all(output_path.parent().unwrap_or(Path::new(".")))?;
        std::fs::write(output_path, &robot)?;

        Ok(robot)
    }

    fn generate_keywords() -> &'static str {
        r#"Create Cortex-M Machine
    Execute Command    mach create "synth-wast-test"
    Execute Command    machine LoadPlatformDescription @${PLATFORM}

To Unsigned
    [Documentation]    Convert signed i32 to unsigned u32 for register storage
    [Arguments]    ${value}
    ${unsigned}=    Evaluate    int(${value}) & 0xFFFFFFFF
    [Return]    ${unsigned}

To Signed
    [Documentation]    Convert unsigned u32 back to signed i32 for comparison
    [Arguments]    ${value}
    ${clean}=    Evaluate    int(str(${value}).strip())
    ${signed}=    Evaluate    ${clean} if ${clean} < 0x80000000 else ${clean} - 0x100000000
    [Return]    ${signed}

Execute Function
    [Arguments]    ${elf}    ${func_addr}    @{args}
    Create Cortex-M Machine
    Execute Command    sysbus LoadELF "${elf}"
    Execute Command    cpu PC ${func_addr}
    # Set SP (R13) to top of RAM (bypassing vector table reset)
    Execute Command    cpu SetRegisterUnsafe 13 0x20010000
    # Set LR (R14) to Default_Handler | 1 (Thumb) so BX LR traps in infinite loop
    ${lr}=    Evaluate    ${RETURN_TRAP} | 1
    Execute Command    cpu SetRegisterUnsafe 14 ${lr}
    # Set arguments in r0-r3 per AAPCS (convert to unsigned for Renode)
    ${reg}=    Set Variable    0
    FOR    ${arg}    IN    @{args}
        ${arg_unsigned}=    To Unsigned    ${arg}
        Execute Command    cpu SetRegisterUnsafe ${reg} ${arg_unsigned}
        ${reg}=    Evaluate    ${reg} + 1
    END
    # Step generous maximum; function returns into Default_Handler trap well before this
    Execute Command    cpu Step 5000
    # Verify function returned: PC should be at Default_Handler (infinite loop)
    ${pc_raw}=    Execute Command    cpu GetRegisterUnsafe 15
    ${pc}=    Evaluate    int(str(${pc_raw}).strip())
    Should Be Equal As Integers    ${pc}    ${RETURN_TRAP}    msg=Function did not return within 5000 steps (PC=0x${pc.__format__('X')})
    ${result}=    Execute Command    cpu GetRegisterUnsafe 0
    # Convert result back to signed for comparison
    ${result_signed}=    To Signed    ${result}
    [Return]    ${result_signed}

Execute Function I64
    [Documentation]    Execute function with i64 parameters and return (uses register pairs)
    [Arguments]    ${elf}    ${func_addr}    ${arg1_lo}    ${arg1_hi}    ${arg2_lo}    ${arg2_hi}
    Create Cortex-M Machine
    Execute Command    sysbus LoadELF "${elf}"
    Execute Command    cpu PC ${func_addr}
    # Set SP (R13) to top of RAM (bypassing vector table reset)
    Execute Command    cpu SetRegisterUnsafe 13 0x20010000
    # Set LR (R14) to Default_Handler | 1 (Thumb) so BX LR traps in infinite loop
    ${lr}=    Evaluate    ${RETURN_TRAP} | 1
    Execute Command    cpu SetRegisterUnsafe 14 ${lr}
    # i64 arg1: R0=low, R1=high; i64 arg2: R2=low, R3=high (per AAPCS for 64-bit)
    ${arg1_lo_u}=    To Unsigned    ${arg1_lo}
    ${arg1_hi_u}=    To Unsigned    ${arg1_hi}
    ${arg2_lo_u}=    To Unsigned    ${arg2_lo}
    ${arg2_hi_u}=    To Unsigned    ${arg2_hi}
    Execute Command    cpu SetRegisterUnsafe 0 ${arg1_lo_u}
    Execute Command    cpu SetRegisterUnsafe 1 ${arg1_hi_u}
    Execute Command    cpu SetRegisterUnsafe 2 ${arg2_lo_u}
    Execute Command    cpu SetRegisterUnsafe 3 ${arg2_hi_u}
    # Step generous maximum; function returns into Default_Handler trap well before this
    Execute Command    cpu Step 5000
    # Verify function returned: PC should be at Default_Handler (infinite loop)
    ${pc_raw}=    Execute Command    cpu GetRegisterUnsafe 15
    ${pc}=    Evaluate    int(str(${pc_raw}).strip())
    Should Be Equal As Integers    ${pc}    ${RETURN_TRAP}    msg=Function did not return within 5000 steps (PC=0x${pc.__format__('X')})
    # i64 result in R0 (low) + R1 (high)
    ${result_lo}=    Execute Command    cpu GetRegisterUnsafe 0
    ${result_hi}=    Execute Command    cpu GetRegisterUnsafe 1
    # Combine into 64-bit value
    ${lo_clean}=    Evaluate    int(str(${result_lo}).strip()) & 0xFFFFFFFF
    ${hi_clean}=    Evaluate    int(str(${result_hi}).strip()) & 0xFFFFFFFF
    ${result64}=    Evaluate    ${lo_clean} + (${hi_clean} << 32)
    [Return]    ${result64}

Execute Function I64 To I32
    [Documentation]    Execute function with i64 parameters but i32 return (comparisons)
    [Arguments]    ${elf}    ${func_addr}    ${arg1_lo}    ${arg1_hi}    ${arg2_lo}    ${arg2_hi}
    Create Cortex-M Machine
    Execute Command    sysbus LoadELF "${elf}"
    Execute Command    cpu PC ${func_addr}
    # Set SP (R13) to top of RAM (bypassing vector table reset)
    Execute Command    cpu SetRegisterUnsafe 13 0x20010000
    # Set LR (R14) to Default_Handler | 1 (Thumb) so BX LR traps in infinite loop
    ${lr}=    Evaluate    ${RETURN_TRAP} | 1
    Execute Command    cpu SetRegisterUnsafe 14 ${lr}
    # i64 arg1: R0=low, R1=high; i64 arg2: R2=low, R3=high (per AAPCS for 64-bit)
    ${arg1_lo_u}=    To Unsigned    ${arg1_lo}
    ${arg1_hi_u}=    To Unsigned    ${arg1_hi}
    ${arg2_lo_u}=    To Unsigned    ${arg2_lo}
    ${arg2_hi_u}=    To Unsigned    ${arg2_hi}
    Execute Command    cpu SetRegisterUnsafe 0 ${arg1_lo_u}
    Execute Command    cpu SetRegisterUnsafe 1 ${arg1_hi_u}
    Execute Command    cpu SetRegisterUnsafe 2 ${arg2_lo_u}
    Execute Command    cpu SetRegisterUnsafe 3 ${arg2_hi_u}
    # Step generous maximum; function returns into Default_Handler trap well before this
    Execute Command    cpu Step 5000
    # Verify function returned: PC should be at Default_Handler (infinite loop)
    ${pc_raw}=    Execute Command    cpu GetRegisterUnsafe 15
    ${pc}=    Evaluate    int(str(${pc_raw}).strip())
    Should Be Equal As Integers    ${pc}    ${RETURN_TRAP}    msg=Function did not return within 5000 steps (PC=0x${pc.__format__('X')})
    # i32 result in R0 only (comparisons return 0 or 1)
    ${result}=    Execute Command    cpu GetRegisterUnsafe 0
    ${result_signed}=    To Signed    ${result}
    [Return]    ${result_signed}

Execute Function I64 Unary To I32
    [Documentation]    Execute function with single i64 parameter and i32 return (eqz)
    [Arguments]    ${elf}    ${func_addr}    ${arg_lo}    ${arg_hi}
    Create Cortex-M Machine
    Execute Command    sysbus LoadELF "${elf}"
    Execute Command    cpu PC ${func_addr}
    # Set SP (R13) to top of RAM (bypassing vector table reset)
    Execute Command    cpu SetRegisterUnsafe 13 0x20010000
    # Set LR (R14) to Default_Handler | 1 (Thumb) so BX LR traps in infinite loop
    ${lr}=    Evaluate    ${RETURN_TRAP} | 1
    Execute Command    cpu SetRegisterUnsafe 14 ${lr}
    # i64 arg: R0=low, R1=high (per AAPCS for 64-bit)
    ${arg_lo_u}=    To Unsigned    ${arg_lo}
    ${arg_hi_u}=    To Unsigned    ${arg_hi}
    Execute Command    cpu SetRegisterUnsafe 0 ${arg_lo_u}
    Execute Command    cpu SetRegisterUnsafe 1 ${arg_hi_u}
    # Step generous maximum; function returns into Default_Handler trap well before this
    Execute Command    cpu Step 5000
    # Verify function returned: PC should be at Default_Handler (infinite loop)
    ${pc_raw}=    Execute Command    cpu GetRegisterUnsafe 15
    ${pc}=    Evaluate    int(str(${pc_raw}).strip())
    Should Be Equal As Integers    ${pc}    ${RETURN_TRAP}    msg=Function did not return within 5000 steps (PC=0x${pc.__format__('X')})
    # i32 result in R0 only
    ${result}=    Execute Command    cpu GetRegisterUnsafe 0
    ${result_signed}=    To Signed    ${result}
    [Return]    ${result_signed}

Execute Function Expect Trap
    [Documentation]    Execute function expecting a trap (div by zero, overflow). Returns final PC.
    [Arguments]    ${elf}    ${func_addr}    @{args}
    Create Cortex-M Machine
    Execute Command    sysbus LoadELF "${elf}"
    Execute Command    cpu PC ${func_addr}
    # Set SP (R13) to top of RAM (bypassing vector table reset)
    Execute Command    cpu SetRegisterUnsafe 13 0x20010000
    # Set LR (R14) to Default_Handler | 1 (Thumb) so BX LR traps in infinite loop
    ${lr}=    Evaluate    ${RETURN_TRAP} | 1
    Execute Command    cpu SetRegisterUnsafe 14 ${lr}
    # Set arguments in r0-r3 per AAPCS (convert to unsigned for Renode)
    ${reg}=    Set Variable    0
    FOR    ${arg}    IN    @{args}
        ${arg_unsigned}=    To Unsigned    ${arg}
        Execute Command    cpu SetRegisterUnsafe ${reg} ${arg_unsigned}
        ${reg}=    Evaluate    ${reg} + 1
    END
    # Step generous maximum; trap/return happens well before this
    Execute Command    cpu Step 5000
    # Return PC - test will check if it's at TRAP_HANDLER (trap) or RETURN_TRAP (no trap)
    ${pc_raw}=    Execute Command    cpu GetRegisterUnsafe 15
    ${pc}=    Evaluate    int(str(${pc_raw}).strip())
    [Return]    ${pc}

"#
    }

    #[allow(dead_code)]
    fn generate_test_case(test_case: &WastTestCase) -> String {
        let mut tc = String::new();

        // Test case header
        tc.push_str(&format!(
            "WAST {} (offset {})\n",
            test_case.name, test_case.source_offset
        ));
        tc.push_str(&format!(
            "    [Documentation]    {}({:?}) == {:?}\n",
            test_case.function, test_case.args, test_case.expected
        ));

        // Separate arg types from result type for i64 operations
        let args_are_i64 = test_case.args.iter().any(|a| a.is_64bit());
        let result_is_i64 = test_case.expected.as_ref().map_or(false, |e| e.is_64bit());

        if args_are_i64 && test_case.args.len() == 2 {
            // Two i64 arguments: split into register pairs
            let arg1 = test_case.args[0].as_u64();
            let arg2 = test_case.args[1].as_u64();
            let arg1_lo = (arg1 & 0xFFFFFFFF) as u32;
            let arg1_hi = ((arg1 >> 32) & 0xFFFFFFFF) as u32;
            let arg2_lo = (arg2 & 0xFFFFFFFF) as u32;
            let arg2_hi = ((arg2 >> 32) & 0xFFFFFFFF) as u32;

            if result_is_i64 {
                // i64 args → i64 result (arithmetic, shifts)
                tc.push_str(&format!(
                    "    ${{result}}=    Execute Function I64    ${{ELF}}    ${{FUNC_ADDR}}    {}    {}    {}    {}\n",
                    arg1_lo, arg1_hi, arg2_lo, arg2_hi
                ));
                if let Some(expected) = &test_case.expected {
                    let expected64 = expected.as_u64();
                    tc.push_str(&format!(
                        "    Should Be Equal As Integers    ${{result}}    {}    \
                         msg={} should return {} but got ${{result}}\n",
                        expected64, test_case.function, expected64
                    ));
                }
            } else {
                // i64 args → i32 result (comparisons: eq, ne, lt_s, gt_s)
                tc.push_str(&format!(
                    "    ${{result}}=    Execute Function I64 To I32    ${{ELF}}    ${{FUNC_ADDR}}    {}    {}    {}    {}\n",
                    arg1_lo, arg1_hi, arg2_lo, arg2_hi
                ));
                if let Some(expected) = &test_case.expected {
                    tc.push_str(&format!(
                        "    Should Be Equal As Integers    ${{result}}    {}    \
                         msg={} should return {} but got ${{result}}\n",
                        expected.as_u32() as i32,
                        test_case.function,
                        expected.as_u32() as i32
                    ));
                }
            }
        } else if args_are_i64 && test_case.args.len() == 1 {
            // Single i64 argument (eqz, clz, ctz, etc.)
            let arg = test_case.args[0].as_u64();
            let arg_lo = (arg & 0xFFFFFFFF) as u32;
            let arg_hi = ((arg >> 32) & 0xFFFFFFFF) as u32;

            if result_is_i64 {
                // i64 arg → i64 result (clz, ctz, popcnt - future)
                // For now, reuse I64 keyword with second arg as zeros
                tc.push_str(&format!(
                    "    ${{result}}=    Execute Function I64    ${{ELF}}    ${{FUNC_ADDR}}    {}    {}    0    0\n",
                    arg_lo, arg_hi
                ));
                if let Some(expected) = &test_case.expected {
                    let expected64 = expected.as_u64();
                    tc.push_str(&format!(
                        "    Should Be Equal As Integers    ${{result}}    {}    \
                         msg={} should return {} but got ${{result}}\n",
                        expected64, test_case.function, expected64
                    ));
                }
            } else {
                // i64 arg → i32 result (eqz)
                tc.push_str(&format!(
                    "    ${{result}}=    Execute Function I64 Unary To I32    ${{ELF}}    ${{FUNC_ADDR}}    {}    {}\n",
                    arg_lo, arg_hi
                ));
                if let Some(expected) = &test_case.expected {
                    tc.push_str(&format!(
                        "    Should Be Equal As Integers    ${{result}}    {}    \
                         msg={} should return {} but got ${{result}}\n",
                        expected.as_u32() as i32,
                        test_case.function,
                        expected.as_u32() as i32
                    ));
                }
            }
        } else {
            // Standard i32 function
            tc.push_str(&format!(
                "    ${{result}}=    Execute Function    ${{ELF}}    ${{FUNC_ADDR}}"
            ));
            for arg in &test_case.args {
                tc.push_str(&format!("    {}", arg.as_u32() as i32));
            }
            tc.push_str("\n");

            // Assert result
            if let Some(expected) = &test_case.expected {
                tc.push_str(&format!(
                    "    Should Be Equal As Integers    ${{result}}    {}    \
                     msg={} should return {} but got ${{result}}\n",
                    expected.as_u32() as i32,
                    test_case.function,
                    expected.as_u32() as i32
                ));
            }
        }

        tc
    }

    /// Helper to get the Robot variable name for a function's address
    fn get_func_addr_var(func_name: &str, config: &SynthTestConfig) -> String {
        if config.function_addresses.is_empty() {
            "${FUNC_ADDR}".to_string()
        } else {
            let var_name = func_name.replace('-', "_").replace('.', "_").to_uppercase();
            format!("${{FUNC_{}_ADDR}}", var_name)
        }
    }

    /// Generate trap test case (assert_trap) - verifies function traps
    fn generate_trap_test_case(test_case: &WastTestCase, config: &SynthTestConfig) -> String {
        let mut tc = String::new();
        let func_addr_var = Self::get_func_addr_var(&test_case.function, config);

        // Test case header
        tc.push_str(&format!(
            "WAST {} (offset {})\n",
            test_case.name, test_case.source_offset
        ));
        let trap_msg = test_case.expected_trap.as_deref().unwrap_or("trap");
        tc.push_str(&format!(
            "    [Documentation]    {}({:?}) should trap: {}\n",
            test_case.function, test_case.args, trap_msg
        ));

        // Execute function and check for trap (PC at Trap_Handler)
        tc.push_str(&format!(
            "    ${{pc}}=    Execute Function Expect Trap    ${{ELF}}    {}",
            func_addr_var
        ));
        for arg in &test_case.args {
            tc.push_str(&format!("    {}", arg.as_u32() as i32));
        }
        tc.push_str("\n");

        // Verify trap occurred (PC should be at Trap_Handler)
        tc.push_str(&format!(
            "    Should Be Equal As Integers    ${{pc}}    ${{TRAP_HANDLER}}    \
             msg=Expected trap ({}) but function returned normally (PC=${{pc}})\n",
            trap_msg
        ));

        tc
    }

    /// Generate test case with per-function address support
    fn generate_test_case_with_config(
        test_case: &WastTestCase,
        config: &SynthTestConfig,
    ) -> String {
        let mut tc = String::new();
        let func_addr_var = Self::get_func_addr_var(&test_case.function, config);

        // Test case header
        tc.push_str(&format!(
            "WAST {} (offset {})\n",
            test_case.name, test_case.source_offset
        ));
        tc.push_str(&format!(
            "    [Documentation]    {}({:?}) == {:?}\n",
            test_case.function, test_case.args, test_case.expected
        ));

        // Separate arg types from result type for i64 operations
        let args_are_i64 = test_case.args.iter().any(|a| a.is_64bit());
        let result_is_i64 = test_case.expected.as_ref().map_or(false, |e| e.is_64bit());

        if args_are_i64 && test_case.args.len() == 2 {
            let arg1 = test_case.args[0].as_u64();
            let arg2 = test_case.args[1].as_u64();
            let arg1_lo = (arg1 & 0xFFFFFFFF) as u32;
            let arg1_hi = ((arg1 >> 32) & 0xFFFFFFFF) as u32;
            let arg2_lo = (arg2 & 0xFFFFFFFF) as u32;
            let arg2_hi = ((arg2 >> 32) & 0xFFFFFFFF) as u32;

            if result_is_i64 {
                tc.push_str(&format!(
                    "    ${{result}}=    Execute Function I64    ${{ELF}}    {}    {}    {}    {}    {}\n",
                    func_addr_var, arg1_lo, arg1_hi, arg2_lo, arg2_hi
                ));
                if let Some(expected) = &test_case.expected {
                    let expected64 = expected.as_u64();
                    tc.push_str(&format!(
                        "    Should Be Equal As Integers    ${{result}}    {}    \
                         msg={} should return {} but got ${{result}}\n",
                        expected64, test_case.function, expected64
                    ));
                }
            } else {
                tc.push_str(&format!(
                    "    ${{result}}=    Execute Function I64 To I32    ${{ELF}}    {}    {}    {}    {}    {}\n",
                    func_addr_var, arg1_lo, arg1_hi, arg2_lo, arg2_hi
                ));
                if let Some(expected) = &test_case.expected {
                    tc.push_str(&format!(
                        "    Should Be Equal As Integers    ${{result}}    {}    \
                         msg={} should return {} but got ${{result}}\n",
                        expected.as_u32() as i32,
                        test_case.function,
                        expected.as_u32() as i32
                    ));
                }
            }
        } else if args_are_i64 && test_case.args.len() == 1 {
            let arg = test_case.args[0].as_u64();
            let arg_lo = (arg & 0xFFFFFFFF) as u32;
            let arg_hi = ((arg >> 32) & 0xFFFFFFFF) as u32;

            if result_is_i64 {
                tc.push_str(&format!(
                    "    ${{result}}=    Execute Function I64    ${{ELF}}    {}    {}    {}    0    0\n",
                    func_addr_var, arg_lo, arg_hi
                ));
                if let Some(expected) = &test_case.expected {
                    let expected64 = expected.as_u64();
                    tc.push_str(&format!(
                        "    Should Be Equal As Integers    ${{result}}    {}    \
                         msg={} should return {} but got ${{result}}\n",
                        expected64, test_case.function, expected64
                    ));
                }
            } else {
                tc.push_str(&format!(
                    "    ${{result}}=    Execute Function I64 Unary To I32    ${{ELF}}    {}    {}    {}\n",
                    func_addr_var, arg_lo, arg_hi
                ));
                if let Some(expected) = &test_case.expected {
                    tc.push_str(&format!(
                        "    Should Be Equal As Integers    ${{result}}    {}    \
                         msg={} should return {} but got ${{result}}\n",
                        expected.as_u32() as i32,
                        test_case.function,
                        expected.as_u32() as i32
                    ));
                }
            }
        } else {
            // Standard i32 function
            tc.push_str(&format!(
                "    ${{result}}=    Execute Function    ${{ELF}}    {}",
                func_addr_var
            ));
            for arg in &test_case.args {
                tc.push_str(&format!("    {}", arg.as_u32() as i32));
            }
            tc.push_str("\n");

            if let Some(expected) = &test_case.expected {
                tc.push_str(&format!(
                    "    Should Be Equal As Integers    ${{result}}    {}    \
                     msg={} should return {} but got ${{result}}\n",
                    expected.as_u32() as i32,
                    test_case.function,
                    expected.as_u32() as i32
                ));
            }
        }

        tc
    }
}

/// High-level test orchestrator for WAST→Synth→Renode pipeline
pub struct WastTestRunner {
    config: SynthTestConfig,
    _stats: WastTestStats,
}

impl WastTestRunner {
    pub fn new(config: SynthTestConfig) -> Self {
        Self {
            config,
            _stats: WastTestStats::default(),
        }
    }

    /// Parse WAST file and generate test artifacts
    pub fn prepare(&self, wast_path: &Path) -> Result<PreparedTests> {
        let parsed = WastParser::parse_file(wast_path)?;

        tracing::info!(
            "Parsed WAST: {} modules, {} assert_return tests, {} skipped",
            parsed.stats.modules_loaded,
            parsed.stats.assert_return_count,
            parsed.stats.skipped
        );

        Ok(PreparedTests {
            parsed,
            config: self.config.clone(),
        })
    }
}

/// Tests ready for execution
#[derive(Debug)]
pub struct PreparedTests {
    pub parsed: ParsedWast,
    pub config: SynthTestConfig,
}

impl PreparedTests {
    /// Generate Robot Framework test file
    pub fn generate_robot(&self, output_path: &Path) -> Result<()> {
        RobotGenerator::generate(&self.parsed, &self.config, output_path)?;
        Ok(())
    }

    /// Get list of test cases
    pub fn test_cases(&self) -> &[WastTestCase] {
        &self.parsed.test_cases
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_wast() {
        let wast = r#"
(module
  (func (export "add") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.add))

(assert_return (invoke "add" (i32.const 5) (i32.const 3)) (i32.const 8))
(assert_return (invoke "add" (i32.const 0) (i32.const 0)) (i32.const 0))
(assert_return (invoke "add" (i32.const -1) (i32.const 1)) (i32.const 0))
"#;

        let result = WastParser::parse_str(wast);
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());

        let parsed = result.unwrap();
        assert_eq!(parsed.stats.modules_loaded, 1);
        assert_eq!(parsed.stats.assert_return_count, 3);
        assert_eq!(parsed.test_cases.len(), 3);

        // Check first test case
        let first = &parsed.test_cases[0];
        assert_eq!(first.function, "add");
        assert_eq!(first.args, vec![Value::I32(5), Value::I32(3)]);
        assert_eq!(first.expected, Some(Value::I32(8)));
    }

    #[test]
    fn test_robot_generation() {
        let wast = r#"
(module
  (func (export "add") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.add))

(assert_return (invoke "add" (i32.const 5) (i32.const 3)) (i32.const 8))
"#;
        let parsed = WastParser::parse_str(wast).unwrap();
        let config = SynthTestConfig::default();

        let robot =
            RobotGenerator::generate(&parsed, &config, Path::new("/tmp/test_robot.robot")).unwrap();

        assert!(robot.contains("WAST add_1"));
        assert!(robot.contains("Should Be Equal As Integers"));
        assert!(robot.contains("Execute Function"));
    }
}
