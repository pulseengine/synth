//! Telnet-based Renode controller
//!
//! Connects to Renode's Monitor interface via telnet and sends commands.
//! This is the simplest and most portable way to control Renode.

use super::{ExecutionResult, RenodeConfig, RenodeController, TrapReason};

/// Cortex-M Configurable Fault Status Register address
const CFSR_ADDR: u32 = 0xE000ED28;
/// Bit 25 in CFSR indicates divide by zero
const CFSR_DIVBYZERO_BIT: u32 = 1 << 25;
/// Default handler address (infinite loop) for Synth-generated ELFs
const DEFAULT_HANDLER_ADDR: u32 = 0x8C;
use anyhow::{Context, Result};
use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpStream;
use std::time::Duration;

/// Telnet-based Renode controller
pub struct TelnetController {
    config: RenodeConfig,
    stream: Option<TcpStream>,
    reader: Option<BufReader<TcpStream>>,
    machine_created: bool,
}

impl TelnetController {
    /// Create a new telnet controller with the given configuration
    pub fn new(config: RenodeConfig) -> Self {
        Self {
            config,
            stream: None,
            reader: None,
            machine_created: false,
        }
    }

    /// Send a command and read the response
    fn send_command(&mut self, cmd: &str) -> Result<String> {
        let stream = self.stream.as_mut().context("Not connected to Renode")?;

        // Send command with newline
        stream
            .write_all(format!("{}\n", cmd).as_bytes())
            .context("Failed to send command")?;
        stream.flush()?;

        // Read response until we get the prompt
        let reader = self.reader.as_mut().context("No reader available")?;
        let mut response = String::new();
        let mut line = String::new();

        loop {
            line.clear();
            match reader.read_line(&mut line) {
                Ok(0) => break, // EOF
                Ok(_) => {
                    // Check for prompt (ends with ") " or "(machine) ")
                    if line.trim().ends_with(')') || line.contains("(monitor)") {
                        break;
                    }
                    response.push_str(&line);
                }
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => break,
                Err(e) => return Err(e.into()),
            }
        }

        Ok(response.trim().to_string())
    }

    /// Parse a register value from Renode's response
    fn parse_register_value(response: &str) -> Result<u32> {
        // Renode returns values like "0x00000008" or just "8"
        let clean = response.trim();
        if clean.starts_with("0x") || clean.starts_with("0X") {
            u32::from_str_radix(&clean[2..], 16).context("Failed to parse hex register value")
        } else {
            clean
                .parse::<u32>()
                .or_else(|_| {
                    // Try parsing as signed and convert
                    clean.parse::<i32>().map(|v| v as u32)
                })
                .context("Failed to parse register value")
        }
    }

    /// Read 32-bit value from memory address
    fn read_memory(&mut self, addr: u32) -> Result<u32> {
        let response = self.send_command(&format!("sysbus ReadDoubleWord 0x{:08X}", addr))?;
        Self::parse_register_value(&response)
    }

    /// Get the program counter
    fn get_pc(&mut self) -> Result<u32> {
        let response = self.send_command("cpu PC")?;
        Self::parse_register_value(&response)
    }

    /// Classify a trap based on fault status registers
    fn classify_trap(&mut self) -> Result<TrapReason> {
        // Read CFSR (Configurable Fault Status Register)
        let cfsr = self.read_memory(CFSR_ADDR).unwrap_or(0);

        if cfsr & CFSR_DIVBYZERO_BIT != 0 {
            return Ok(TrapReason::IntegerDivideByZero);
        }

        // Check for other fault bits in CFSR
        // Bits 0-7: MemManage faults
        // Bits 8-15: BusFault
        // Bits 16-31: UsageFault
        if cfsr & 0xFF != 0 {
            return Ok(TrapReason::OutOfBoundsMemory);
        }

        Ok(TrapReason::Unknown(format!("CFSR=0x{:08X}", cfsr)))
    }
}

impl RenodeController for TelnetController {
    fn connect(&mut self) -> Result<()> {
        let addr = format!("{}:{}", self.config.host, self.config.monitor_port);
        let stream = TcpStream::connect(&addr)
            .with_context(|| format!("Failed to connect to Renode at {}", addr))?;

        stream.set_read_timeout(Some(Duration::from_millis(self.config.timeout_ms)))?;
        stream.set_write_timeout(Some(Duration::from_millis(self.config.timeout_ms)))?;

        let reader = BufReader::new(stream.try_clone()?);
        self.stream = Some(stream);
        self.reader = Some(reader);

        // Read initial banner/prompt
        let mut buf = [0u8; 1024];
        if let Some(s) = self.stream.as_mut() {
            let _ = s.read(&mut buf); // Ignore initial output
        }

        Ok(())
    }

    fn disconnect(&mut self) -> Result<()> {
        self.stream = None;
        self.reader = None;
        self.machine_created = false;
        Ok(())
    }

    fn create_machine(&mut self, name: &str) -> Result<()> {
        self.send_command(&format!("mach create \"{}\"", name))?;
        self.machine_created = true;
        Ok(())
    }

    fn load_platform(&mut self, path: &str) -> Result<()> {
        self.send_command(&format!("machine LoadPlatformDescription @{}", path))?;
        Ok(())
    }

    fn load_elf(&mut self, path: &str) -> Result<()> {
        self.send_command(&format!("sysbus LoadELF @{}", path))?;
        Ok(())
    }

    fn set_register(&mut self, reg: u32, value: u32) -> Result<()> {
        self.send_command(&format!("cpu SetRegisterUnsafe {} {}", reg, value))?;
        Ok(())
    }

    fn get_register(&mut self, reg: u32) -> Result<u32> {
        let response = self.send_command(&format!("cpu GetRegisterUnsafe {}", reg))?;
        Self::parse_register_value(&response)
    }

    fn set_pc(&mut self, addr: u32) -> Result<()> {
        self.send_command(&format!("cpu PC 0x{:X}", addr))?;
        Ok(())
    }

    fn step(&mut self, count: u32) -> Result<()> {
        self.send_command(&format!("cpu Step {}", count))?;
        Ok(())
    }

    fn reset(&mut self) -> Result<()> {
        self.send_command("machine Reset")?;
        Ok(())
    }

    fn execute_function(
        &mut self,
        func_addr: u32,
        args: &[u32],
        max_steps: u32,
    ) -> Result<ExecutionResult> {
        // Set up arguments in r0-r3 (AAPCS calling convention)
        for (i, &arg) in args.iter().take(4).enumerate() {
            self.set_register(i as u32, arg)?;
        }

        // Set PC to function address (with Thumb bit if needed)
        self.set_pc(func_addr)?;

        // Execute
        self.step(max_steps)?;

        // Check for trap by examining PC
        let pc = self.get_pc()?;

        // If PC is at the default handler, we hit a fault
        if pc == DEFAULT_HANDLER_ADDR || pc == DEFAULT_HANDLER_ADDR | 1 {
            let trap_reason = self.classify_trap()?;
            return Ok(ExecutionResult::Trap(trap_reason));
        }

        // Read result from r0
        let result = self.get_register(0)?;

        Ok(ExecutionResult::Return(result))
    }
}

impl Drop for TelnetController {
    fn drop(&mut self) {
        let _ = self.disconnect();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_register_value() {
        assert_eq!(TelnetController::parse_register_value("8").unwrap(), 8);
        assert_eq!(TelnetController::parse_register_value("0x8").unwrap(), 8);
        assert_eq!(
            TelnetController::parse_register_value("0xFFFFFFFF").unwrap(),
            0xFFFFFFFF
        );
        assert_eq!(
            TelnetController::parse_register_value("-1").unwrap(),
            0xFFFFFFFF
        );
    }
}
