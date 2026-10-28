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
use std::collections::{BTreeMap, HashMap};
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
        if symbol.kind() == object::SymbolKind::Text
            && let Ok(name) = symbol.name()
            && !name.starts_with('$')
            && !name.starts_with('.')
            && !name.is_empty()
        {
            let addr = symbol.address() as u32;
            symbols.insert(name.to_string(), addr);
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

/// Name the value type of a WAST argument, for the drop-reason counters
/// (#1570). Exhaustive over the core variants on purpose: a new `wast`
/// variant must be named here, not folded into a catch-all.
fn wast_arg_type_name(arg: &WastArg) -> &'static str {
    match arg {
        WastArg::Core(core) => match core {
            WastArgCore::I32(_) => "i32",
            WastArgCore::I64(_) => "i64",
            WastArgCore::F32(_) => "f32",
            WastArgCore::F64(_) => "f64",
            WastArgCore::V128(_) => "v128",
            WastArgCore::RefNull(_) | WastArgCore::RefExtern(_) | WastArgCore::RefHost(_) => "ref",
        },
        #[allow(unreachable_patterns)]
        _ => "component",
    }
}

/// Name the value type of a WAST expected result (see [`wast_arg_type_name`]).
/// An f32/f64 NaN pattern (`nan:canonical` / `nan:arithmetic`) is an `f32` /
/// `f64` result like any other float.
fn wast_ret_type_name(ret: &WastRet) -> &'static str {
    match ret {
        WastRet::Core(core) => match core {
            WastRetCore::I32(_) => "i32",
            WastRetCore::I64(_) => "i64",
            WastRetCore::F32(_) => "f32",
            WastRetCore::F64(_) => "f64",
            WastRetCore::V128(_) => "v128",
            WastRetCore::RefNull(_)
            | WastRetCore::RefExtern(_)
            | WastRetCore::RefHost(_)
            | WastRetCore::RefFunc(_)
            | WastRetCore::RefAny
            | WastRetCore::RefEq
            | WastRetCore::RefArray
            | WastRetCore::RefStruct
            | WastRetCore::RefI31
            | WastRetCore::RefI31Shared => "ref",
            WastRetCore::Either(_) => "either",
        },
        #[allow(unreachable_patterns)]
        _ => "component",
    }
}

/// Name a non-invoke execution form (`assert_return (get ...)` etc.).
fn wast_execute_kind(exec: &WastExecute) -> &'static str {
    match exec {
        WastExecute::Invoke(_) => "invoke",
        WastExecute::Wat(_) => "wat",
        WastExecute::Get { .. } => "get",
    }
}

/// Convert every argument, or name the first one we cannot represent.
fn convert_args(args: &[WastArg]) -> std::result::Result<Vec<Value>, &'static str> {
    args.iter()
        .map(|a| convert_wast_arg_to_value(a).map_err(|_| wast_arg_type_name(a)))
        .collect()
}

/// Outcome of converting one directive into a test case: kept, or dropped
/// with a machine-readable reason that the caller COUNTS (#1570).
enum Converted {
    Kept(WastTestCase),
    Dropped(String),
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
///
/// #1570: a directive the parser cannot turn into a test case is COUNTED,
/// never silently dropped. `assert_return_count` is the number KEPT;
/// `assert_return_seen` is the number of `assert_return` directives in the
/// file, and `assert_return_seen == assert_return_count +
/// assert_return_dropped` always holds. Every drop (assert_return,
/// assert_trap and invoke alike) is also tallied in `dropped_by_reason` under
/// a `<directive>:<cause>:<detail>` key — e.g. `assert_return:arg:f32`,
/// `assert_return:result:f64`, `assert_return:exec:get`. Only the FIRST
/// unsupported value of a directive names its reason (arguments are checked
/// before results). So a consumer can tell "this file has no value-checking
/// tests" from "every one of them was thrown away".
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct WastTestStats {
    pub modules_loaded: usize,
    pub assert_return_count: usize,
    pub assert_trap_count: usize,
    pub invoke_count: usize,
    pub passed: usize,
    pub failed: usize,
    /// Unsupported directives plus dropped `assert_trap`s (pre-#1570
    /// meaning, unchanged). Dropped `assert_return`/`invoke` directives are
    /// counted in their own fields below, not here.
    pub skipped: usize,
    /// `assert_return` directives encountered (kept + dropped).
    #[serde(default)]
    pub assert_return_seen: usize,
    /// `assert_return` directives that could NOT be turned into a test case
    /// (non-i32/i64 value, or a non-invoke execution).
    #[serde(default)]
    pub assert_return_dropped: usize,
    /// `assert_trap` directives that could not be turned into a test case
    /// (also counted in `skipped`, as before #1570).
    #[serde(default)]
    pub assert_trap_dropped: usize,
    /// Bare `invoke` directives that could not be turned into a test case.
    #[serde(default)]
    pub invoke_dropped: usize,
    /// KEPT `assert_return`s whose expectation lists more than one result:
    /// only the FIRST result is carried in `WastTestCase::expected`, so the
    /// rest are not graded.
    #[serde(default)]
    pub assert_return_multi_value_truncated: usize,
    /// Every dropped directive, tallied by reason (deterministic order).
    #[serde(default)]
    pub dropped_by_reason: BTreeMap<String, usize>,
}

impl WastTestStats {
    /// Total directives dropped for an unrepresentable value or execution
    /// form (assert_return + assert_trap + invoke).
    pub fn dropped_total(&self) -> usize {
        self.dropped_by_reason.values().sum()
    }

    fn record_drop(&mut self, reason: String) {
        *self.dropped_by_reason.entry(reason).or_insert(0) += 1;
    }
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

        if result.stats.dropped_total() > 0 {
            tracing::warn!(
                "WAST: dropped {} directive(s) the test model cannot represent \
                 ({} of {} assert_return): {:?}",
                result.stats.dropped_total(),
                result.stats.assert_return_dropped,
                result.stats.assert_return_seen,
                result.stats.dropped_by_reason
            );
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
                result.stats.assert_return_seen += 1;
                match Self::process_assert_return(&exec, &results, test_counter) {
                    Converted::Kept(test_case) => {
                        if results.len() > 1 {
                            result.stats.assert_return_multi_value_truncated += 1;
                        }
                        result.test_cases.push(test_case);
                        result.stats.assert_return_count += 1;
                    }
                    Converted::Dropped(reason) => {
                        result.stats.assert_return_dropped += 1;
                        result.stats.record_drop(format!("assert_return:{reason}"));
                    }
                }
            }

            WastDirective::AssertTrap { exec, message, .. } => {
                match Self::process_assert_trap(&exec, message, test_counter) {
                    Converted::Kept(test_case) => {
                        result.test_cases.push(test_case);
                        result.stats.assert_trap_count += 1;
                    }
                    Converted::Dropped(reason) => {
                        result.stats.skipped += 1;
                        result.stats.assert_trap_dropped += 1;
                        result.stats.record_drop(format!("assert_trap:{reason}"));
                    }
                }
            }

            WastDirective::Invoke(invoke) => match Self::process_invoke(&invoke, test_counter) {
                Converted::Kept(test_case) => {
                    result.test_cases.push(test_case);
                    result.stats.invoke_count += 1;
                }
                Converted::Dropped(reason) => {
                    result.stats.invoke_dropped += 1;
                    result.stats.record_drop(format!("invoke:{reason}"));
                }
            },

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
    ) -> Converted {
        let invoke = match exec {
            WastExecute::Invoke(inv) => inv,
            other => return Converted::Dropped(format!("exec:{}", wast_execute_kind(other))),
        };

        // Convert arguments
        let args = match convert_args(&invoke.args) {
            Ok(a) => a,
            Err(ty) => {
                tracing::debug!("Dropping assert_return with unsupported {ty} arg");
                return Converted::Dropped(format!("arg:{ty}"));
            }
        };

        // Convert expected results
        let mut expected = Vec::with_capacity(results.len());
        for r in results {
            match convert_wast_ret_to_value(r) {
                Ok(v) => expected.push(v),
                Err(_) => {
                    let ty = wast_ret_type_name(r);
                    tracing::debug!("Dropping assert_return with unsupported {ty} result");
                    return Converted::Dropped(format!("result:{ty}"));
                }
            }
        }
        // Only single return for now; a multi-value expectation is counted
        // as truncated by the caller.
        let expected = expected.into_iter().next();

        *test_counter += 1;

        Converted::Kept(WastTestCase {
            name: format!("{}_{}", invoke.name, test_counter),
            function: invoke.name.to_string(),
            args,
            expected,
            expected_trap: None,
            source_offset: invoke.span.offset(),
            test_type: WastTestType::AssertReturn,
        })
    }

    fn process_assert_trap(
        exec: &WastExecute,
        message: &str,
        test_counter: &mut usize,
    ) -> Converted {
        let invoke = match exec {
            WastExecute::Invoke(inv) => inv,
            other => return Converted::Dropped(format!("exec:{}", wast_execute_kind(other))),
        };

        // Convert arguments
        let args = match convert_args(&invoke.args) {
            Ok(a) => a,
            Err(ty) => {
                tracing::debug!("Dropping assert_trap with unsupported {ty} arg");
                return Converted::Dropped(format!("arg:{ty}"));
            }
        };

        *test_counter += 1;

        Converted::Kept(WastTestCase {
            name: format!("trap_{}_{}", invoke.name, test_counter),
            function: invoke.name.to_string(),
            args,
            expected: None,
            expected_trap: Some(message.to_string()),
            source_offset: invoke.span.offset(),
            test_type: WastTestType::AssertTrap,
        })
    }

    fn process_invoke(invoke: &WastInvoke, test_counter: &mut usize) -> Converted {
        let args = match convert_args(&invoke.args) {
            Ok(a) => a,
            Err(ty) => return Converted::Dropped(format!("arg:{ty}")),
        };

        *test_counter += 1;

        Converted::Kept(WastTestCase {
            name: format!("invoke_{}_{}", invoke.name, test_counter),
            function: invoke.name.to_string(),
            args,
            expected: None,
            expected_trap: None,
            source_offset: invoke.span.offset(),
            test_type: WastTestType::Invoke,
        })
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
            function_address: 0xA1, // 0xA0 with Thumb bit (Cortex-M layout)
            function_addresses: HashMap::new(),
            default_handler_address: 0x9C, // Default_Handler (after 28-byte startup at 0x80)
            trap_handler_address: 0x9E,    // Trap_Handler (after Default_Handler)
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
                let var_name = func_name.replace(['-', '.'], "_").to_uppercase();
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
        robot.push('\n');

        // Test Cases
        robot.push_str("*** Test Cases ***\n");
        let mut included = 0;
        let mut skipped = 0;
        for test_case in &parsed.test_cases {
            if options.should_include(&test_case.function) {
                match test_case.test_type {
                    WastTestType::AssertReturn => {
                        robot.push_str(&Self::generate_test_case_with_config(test_case, config));
                        robot.push('\n');
                        included += 1;
                    }
                    WastTestType::AssertTrap => {
                        robot.push_str(&Self::generate_trap_test_case(test_case, config));
                        robot.push('\n');
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
        let result_is_i64 = test_case.expected.as_ref().is_some_and(|e| e.is_64bit());

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
            tc.push_str("    ${result}=    Execute Function    ${ELF}    ${FUNC_ADDR}");
            for arg in &test_case.args {
                tc.push_str(&format!("    {}", arg.as_u32() as i32));
            }
            tc.push('\n');

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
            let var_name = func_name.replace(['-', '.'], "_").to_uppercase();
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
        tc.push('\n');

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
        let result_is_i64 = test_case.expected.as_ref().is_some_and(|e| e.is_64bit());

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
            tc.push('\n');

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
            "Parsed WAST: {} modules, {} of {} assert_return tests kept ({} dropped: {:?}), {} skipped",
            parsed.stats.modules_loaded,
            parsed.stats.assert_return_count,
            parsed.stats.assert_return_seen,
            parsed.stats.assert_return_dropped,
            parsed.stats.dropped_by_reason,
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

    /// #1570 red-first: every directive the test model cannot represent is
    /// COUNTED by reason, and kept + dropped conserves the directive count.
    /// On the pre-fix parser the f32/f64/v128/get assert_returns vanished
    /// with no counter at all (`assert_return_count` 2, nothing else moved).
    #[test]
    fn unrepresentable_directives_are_counted_by_reason_1570() {
        let wast = r#"
(module
  (global (export "g") i32 (i32.const 7))
  (func (export "add") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.add)
  (func (export "two") (result i32 i32) i32.const 1 i32.const 2)
  (func (export "fneg") (param f32) (result f32) local.get 0 f32.neg)
  (func (export "fconst") (param i32) (result f32) f32.const 1.5)
  (func (export "dnan") (param i32) (result f64) f64.const nan)
  (func (export "vid") (param v128) (result i32) i32.const 0)
  (func (export "fdiv") (param f64) (result i32) i32.const 0))

(assert_return (invoke "add" (i32.const 5) (i32.const 3)) (i32.const 8))
(assert_return (invoke "two") (i32.const 1) (i32.const 2))
(assert_return (invoke "fneg" (f32.const 1.0)) (f32.const -1.0))
(assert_return (invoke "fneg" (f32.const 2.0)) (f32.const -2.0))
(assert_return (invoke "fconst" (i32.const 0)) (f32.const 1.5))
(assert_return (invoke "dnan" (i32.const 0)) (f64.const nan:canonical))
(assert_return (invoke "dnan" (i32.const 1)) (f64.const nan:arithmetic))
(assert_return (invoke "vid" (v128.const i32x4 0 0 0 0)) (i32.const 0))
(assert_return (get "g") (i32.const 7))
(assert_trap (invoke "fdiv" (f64.const 0.0)) "integer divide by zero")
(invoke "fneg" (f32.const 3.0))
(invoke "add" (i32.const 1) (i32.const 2))
"#;
        let parsed = WastParser::parse_str(wast).unwrap();
        let st = &parsed.stats;

        // Kept: the i32 add and the (truncated) multi-value case.
        assert_eq!(st.assert_return_count, 2);
        assert_eq!(st.assert_return_multi_value_truncated, 1);
        // Seen = kept + dropped: nothing leaves without a trace.
        assert_eq!(st.assert_return_seen, 9);
        assert_eq!(st.assert_return_dropped, 7);
        assert_eq!(
            st.assert_return_seen,
            st.assert_return_count + st.assert_return_dropped
        );

        let mut want = BTreeMap::new();
        want.insert("assert_return:arg:f32".to_string(), 2);
        want.insert("assert_return:result:f32".to_string(), 1);
        want.insert("assert_return:result:f64".to_string(), 2);
        want.insert("assert_return:arg:v128".to_string(), 1);
        want.insert("assert_return:exec:get".to_string(), 1);
        want.insert("assert_trap:arg:f64".to_string(), 1);
        want.insert("invoke:arg:f32".to_string(), 1);
        assert_eq!(st.dropped_by_reason, want);

        // Per-directive totals agree with the reason table.
        let by_prefix = |p: &str| -> usize {
            st.dropped_by_reason
                .iter()
                .filter(|(k, _)| k.starts_with(p))
                .map(|(_, v)| *v)
                .sum()
        };
        assert_eq!(by_prefix("assert_return:"), st.assert_return_dropped);
        assert_eq!(by_prefix("assert_trap:"), st.assert_trap_dropped);
        assert_eq!(by_prefix("invoke:"), st.invoke_dropped);
        assert_eq!(st.dropped_total(), 9);

        // Pre-#1570 counters keep their meaning: the dropped assert_trap is
        // still in `skipped`; dropped assert_return/invoke are not.
        assert_eq!(st.skipped, 1);
        assert_eq!(st.assert_trap_dropped, 1);
        assert_eq!(st.invoke_count, 1);
        assert_eq!(st.invoke_dropped, 1);
        assert_eq!(parsed.test_cases.len(), 3);
    }
}
