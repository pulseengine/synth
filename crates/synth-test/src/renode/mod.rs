//! Renode control interfaces for programmatic test execution
//!
//! This module provides abstractions for controlling Renode emulator,
//! supporting multiple backends (Telnet, GDB, pyrenode3 in future).

pub mod telnet;

use anyhow::Result;

/// Result of executing a function in Renode
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExecutionResult {
    /// Function returned normally with a value in r0
    Return(u32),
    /// Function trapped (fault, exception)
    Trap(TrapReason),
    /// Execution timed out
    Timeout,
}

/// Reason for a trap during execution
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrapReason {
    /// Integer divide by zero
    IntegerDivideByZero,
    /// Integer overflow (e.g., MIN_INT / -1)
    IntegerOverflow,
    /// Out of bounds memory access
    OutOfBoundsMemory,
    /// Unreachable instruction executed
    Unreachable,
    /// Unknown/unclassified trap
    Unknown(String),
}

impl TrapReason {
    /// Match against WAST trap message
    pub fn matches_wast_message(&self, msg: &str) -> bool {
        match self {
            TrapReason::IntegerDivideByZero => msg == "integer divide by zero",
            TrapReason::IntegerOverflow => msg == "integer overflow",
            TrapReason::OutOfBoundsMemory => msg == "out of bounds memory access",
            TrapReason::Unreachable => msg == "unreachable",
            TrapReason::Unknown(_) => false,
        }
    }
}

/// Configuration for Renode connection
#[derive(Debug, Clone)]
pub struct RenodeConfig {
    /// Host to connect to
    pub host: String,
    /// Telnet/Monitor port
    pub monitor_port: u16,
    /// GDB server port (optional)
    pub gdb_port: Option<u16>,
    /// Path to platform description file
    pub platform_file: String,
    /// Command timeout in milliseconds
    pub timeout_ms: u64,
}

impl Default for RenodeConfig {
    fn default() -> Self {
        Self {
            host: "localhost".to_string(),
            monitor_port: 1234,
            gdb_port: Some(3333),
            platform_file: "synth_cortex_m.repl".to_string(),
            timeout_ms: 5000,
        }
    }
}

/// Trait for Renode controller implementations
pub trait RenodeController: Send {
    /// Connect to Renode
    fn connect(&mut self) -> Result<()>;

    /// Disconnect from Renode
    fn disconnect(&mut self) -> Result<()>;

    /// Create a new machine
    fn create_machine(&mut self, name: &str) -> Result<()>;

    /// Load platform description
    fn load_platform(&mut self, path: &str) -> Result<()>;

    /// Load ELF binary
    fn load_elf(&mut self, path: &str) -> Result<()>;

    /// Set a register value
    fn set_register(&mut self, reg: u32, value: u32) -> Result<()>;

    /// Get a register value
    fn get_register(&mut self, reg: u32) -> Result<u32>;

    /// Set program counter
    fn set_pc(&mut self, addr: u32) -> Result<()>;

    /// Step N instructions
    fn step(&mut self, count: u32) -> Result<()>;

    /// Reset the machine (keep ELF loaded)
    fn reset(&mut self) -> Result<()>;

    /// Execute a function with given arguments and return result
    fn execute_function(
        &mut self,
        func_addr: u32,
        args: &[u32],
        max_steps: u32,
    ) -> Result<ExecutionResult>;
}

/// Helper to convert signed i32 to unsigned u32 for register storage
pub fn to_unsigned(value: i32) -> u32 {
    value as u32
}

/// Helper to convert unsigned u32 back to signed i32
pub fn to_signed(value: u32) -> i32 {
    value as i32
}
