//! QEMU Integration for Synth
//!
//! This crate provides QEMU emulation support for testing generated ARM binaries

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

/// QEMU runner for ARM binaries
pub struct QemuRunner {
    qemu_path: PathBuf,
    board: QemuBoard,
    timeout: Duration,
}

/// Supported QEMU board configurations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QemuBoard {
    /// Netduino 2 (STM32F205)
    Netduino2,
    /// STM32 P103 (STM32F103)
    Stm32P103,
    /// STM32F4Discovery (STM32F407)
    Stm32F4Discovery,
    /// Custom board
    Custom,
}

impl QemuBoard {
    fn machine_name(&self) -> &'static str {
        match self {
            QemuBoard::Netduino2 => "netduino2",
            QemuBoard::Stm32P103 => "stm32-p103",
            QemuBoard::Stm32F4Discovery => "stm32f4-discovery",
            QemuBoard::Custom => "none",
        }
    }
}

/// QEMU execution result
#[derive(Debug)]
pub struct QemuResult {
    pub exit_code: Option<i32>,
    pub stdout: String,
    pub stderr: String,
    pub duration: Duration,
    pub timed_out: bool,
}

impl QemuRunner {
    /// Create a new QEMU runner
    pub fn new(qemu_path: impl AsRef<Path>, board: QemuBoard) -> Self {
        Self {
            qemu_path: qemu_path.as_ref().to_path_buf(),
            board,
            timeout: Duration::from_secs(10),
        }
    }

    /// Create with default QEMU path
    pub fn with_default_path(board: QemuBoard) -> Self {
        let home = std::env::var("HOME").unwrap_or_else(|_| ".".to_string());
        let qemu_path = Path::new(&home).join(".local/bin/qemu-system-arm");
        Self::new(qemu_path, board)
    }

    /// Set execution timeout
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    /// Run a binary in QEMU
    pub fn run(&self, binary: impl AsRef<Path>) -> Result<QemuResult, QemuError> {
        let binary_path = binary.as_ref();

        if !binary_path.exists() {
            return Err(QemuError::BinaryNotFound(binary_path.to_path_buf()));
        }

        let start = std::time::Instant::now();

        let mut cmd = Command::new(&self.qemu_path);
        cmd.arg("-M")
            .arg(self.board.machine_name())
            .arg("-nographic")
            .arg("-kernel")
            .arg(binary_path)
            .arg("-serial")
            .arg("stdio")
            .arg("-monitor")
            .arg("none")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        let output = cmd
            .output()
            .map_err(|e| QemuError::ExecutionFailed(e.to_string()))?;

        let duration = start.elapsed();
        let timed_out = duration >= self.timeout;

        Ok(QemuResult {
            exit_code: output.status.code(),
            stdout: String::from_utf8_lossy(&output.stdout).to_string(),
            stderr: String::from_utf8_lossy(&output.stderr).to_string(),
            duration,
            timed_out,
        })
    }

    /// Run with trace output (instruction trace)
    pub fn run_with_trace(&self, binary: impl AsRef<Path>) -> Result<QemuResult, QemuError> {
        let binary_path = binary.as_ref();

        if !binary_path.exists() {
            return Err(QemuError::BinaryNotFound(binary_path.to_path_buf()));
        }

        let start = std::time::Instant::now();

        let mut cmd = Command::new(&self.qemu_path);
        cmd.arg("-M")
            .arg(self.board.machine_name())
            .arg("-nographic")
            .arg("-kernel")
            .arg(binary_path)
            .arg("-d")
            .arg("in_asm,exec") // Enable instruction trace
            .arg("-D")
            .arg("/tmp/qemu-trace.log") // Save trace to file
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        let output = cmd
            .output()
            .map_err(|e| QemuError::ExecutionFailed(e.to_string()))?;

        let duration = start.elapsed();

        Ok(QemuResult {
            exit_code: output.status.code(),
            stdout: String::from_utf8_lossy(&output.stdout).to_string(),
            stderr: String::from_utf8_lossy(&output.stderr).to_string(),
            duration,
            timed_out: duration >= self.timeout,
        })
    }

    /// Check if QEMU is available
    pub fn check_available(&self) -> bool {
        self.qemu_path.exists()
    }

    /// Get QEMU version
    pub fn version(&self) -> Result<String, QemuError> {
        let output = Command::new(&self.qemu_path)
            .arg("--version")
            .output()
            .map_err(|e| QemuError::ExecutionFailed(e.to_string()))?;

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }
}

/// QEMU error types
#[derive(Debug)]
pub enum QemuError {
    BinaryNotFound(PathBuf),
    ExecutionFailed(String),
    TimeoutExceeded,
    InvalidOutput,
}

impl std::fmt::Display for QemuError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QemuError::BinaryNotFound(path) => write!(f, "Binary not found: {}", path.display()),
            QemuError::ExecutionFailed(msg) => write!(f, "QEMU execution failed: {}", msg),
            QemuError::TimeoutExceeded => write!(f, "QEMU execution timeout exceeded"),
            QemuError::InvalidOutput => write!(f, "Invalid QEMU output"),
        }
    }
}

impl std::error::Error for QemuError {}

/// Helper for asserting QEMU output
pub fn assert_output_contains(result: &QemuResult, expected: &str) -> bool {
    result.stdout.contains(expected) || result.stderr.contains(expected)
}

/// Helper for extracting GPIO writes from output
pub fn extract_gpio_writes(result: &QemuResult) -> Vec<(u32, u32)> {
    let mut writes = Vec::new();

    for line in result.stdout.lines() {
        if line.contains("GPIO write") {
            // Parse GPIO write: "GPIO write: addr=0x40020018, value=0x00000020"
            if let Some(addr_start) = line.find("addr=") {
                if let Some(val_start) = line.find("value=") {
                    let addr_str = &line[addr_start + 5..addr_start + 15];
                    let val_str = &line[val_start + 6..val_start + 16];

                    if let (Ok(addr), Ok(val)) = (
                        u32::from_str_radix(&addr_str[2..], 16),
                        u32::from_str_radix(&val_str[2..], 16),
                    ) {
                        writes.push((addr, val));
                    }
                }
            }
        }
    }

    writes
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_qemu_board_names() {
        assert_eq!(QemuBoard::Netduino2.machine_name(), "netduino2");
        assert_eq!(QemuBoard::Stm32P103.machine_name(), "stm32-p103");
        assert_eq!(
            QemuBoard::Stm32F4Discovery.machine_name(),
            "stm32f4-discovery"
        );
    }

    #[test]
    fn test_qemu_runner_creation() {
        let runner = QemuRunner::with_default_path(QemuBoard::Netduino2);
        assert_eq!(runner.board, QemuBoard::Netduino2);
        assert_eq!(runner.timeout, Duration::from_secs(10));
    }

    #[test]
    fn test_qemu_runner_timeout() {
        let runner = QemuRunner::with_default_path(QemuBoard::Netduino2)
            .with_timeout(Duration::from_secs(5));
        assert_eq!(runner.timeout, Duration::from_secs(5));
    }

    #[test]
    fn test_assert_output_contains() {
        let result = QemuResult {
            exit_code: Some(0),
            stdout: "Hello from QEMU!".to_string(),
            stderr: String::new(),
            duration: Duration::from_secs(1),
            timed_out: false,
        };

        assert!(assert_output_contains(&result, "Hello from QEMU!"));
        assert!(!assert_output_contains(&result, "Not present"));
    }

    #[test]
    fn test_extract_gpio_writes() {
        let result = QemuResult {
            exit_code: Some(0),
            stdout: "GPIO write: addr=0x40020018, value=0x00000020\nGPIO write: addr=0x40020018, value=0x00200000\n".to_string(),
            stderr: String::new(),
            duration: Duration::from_secs(1),
            timed_out: false,
        };

        let writes = extract_gpio_writes(&result);
        assert_eq!(writes.len(), 2);
        assert_eq!(writes[0], (0x40020018, 0x00000020));
        assert_eq!(writes[1], (0x40020018, 0x00200000));
    }
}
