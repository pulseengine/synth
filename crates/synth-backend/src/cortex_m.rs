//! Cortex-M specific code generation
//!
//! Generates vector tables, startup code, and runtime support for ARM Cortex-M targets.

/// Cortex-M vector table generator
pub struct VectorTable {
    /// Initial stack pointer value
    pub initial_sp: u32,
    /// Reset handler address
    pub reset_handler: u32,
    /// NMI handler address (optional, defaults to infinite loop)
    pub nmi_handler: Option<u32>,
    /// HardFault handler address (optional, defaults to infinite loop)
    pub hardfault_handler: Option<u32>,
}

impl VectorTable {
    /// Create a minimal vector table with just SP and reset handler
    pub fn minimal(initial_sp: u32, reset_handler: u32) -> Self {
        Self {
            initial_sp,
            reset_handler,
            nmi_handler: None,
            hardfault_handler: None,
        }
    }

    /// Generate the vector table as bytes
    ///
    /// Returns a 16-entry vector table (64 bytes) suitable for basic Cortex-M operation
    pub fn generate(&self, default_handler: u32) -> Vec<u8> {
        let mut table = Vec::with_capacity(64);

        // Entry 0: Initial SP
        table.extend_from_slice(&self.initial_sp.to_le_bytes());

        // Entry 1: Reset handler (must have bit 0 set for Thumb mode)
        table.extend_from_slice(&(self.reset_handler | 1).to_le_bytes());

        // Entry 2: NMI handler
        let nmi = self.nmi_handler.unwrap_or(default_handler) | 1;
        table.extend_from_slice(&nmi.to_le_bytes());

        // Entry 3: HardFault handler
        let hardfault = self.hardfault_handler.unwrap_or(default_handler) | 1;
        table.extend_from_slice(&hardfault.to_le_bytes());

        // Entries 4-15: MemManage, BusFault, UsageFault, Reserved, SVCall, etc.
        for _ in 4..16 {
            table.extend_from_slice(&(default_handler | 1).to_le_bytes());
        }

        table
    }
}

/// Cortex-M startup code generator
pub struct StartupCode {
    /// Stack top address
    pub stack_top: u32,
    /// Entry point (main function)
    pub entry_point: u32,
    /// Data section start (in RAM)
    pub data_start: u32,
    /// Data section end (in RAM)
    pub data_end: u32,
    /// Data load address (in flash)
    pub data_load: u32,
    /// BSS section start
    pub bss_start: u32,
    /// BSS section end
    pub bss_end: u32,
}

impl StartupCode {
    /// Create minimal startup that just jumps to entry point
    pub fn minimal(entry_point: u32) -> Self {
        Self {
            stack_top: 0x2000_0000 + 64 * 1024, // 64KB RAM, stack at top
            entry_point,
            data_start: 0,
            data_end: 0,
            data_load: 0,
            bss_start: 0,
            bss_end: 0,
        }
    }

    /// Generate Thumb-2 startup code (reset handler)
    ///
    /// This generates minimal startup code that:
    /// 1. Sets up the stack pointer (already done by hardware from vector table)
    /// 2. Initializes R11 as linear memory base (0x20000000)
    /// 3. Calls the entry point
    /// 4. Loops forever if entry returns
    pub fn generate_thumb(&self) -> Vec<u8> {
        let mut code = Vec::new();

        // Reset handler entry point
        // The stack pointer is already set by hardware from vector table[0]

        // Initialize R11 with linear memory base address (0x20000000)
        // This is used for WASM linear memory access: LDR Rd, [R11, Raddr]
        // Thumb-2 MOVW R11, #0x0000 (low 16 bits)
        // Encoding: 1111 0 i 10 0 1 0 0 imm4 | 0 imm3 Rd imm8
        // For R11=0x0000: i=0, imm4=0, imm3=0, imm8=0
        code.extend_from_slice(&[0x40, 0xF2, 0x00, 0x0B]); // MOVW R11, #0

        // Thumb-2 MOVT R11, #0x2000 (high 16 bits)
        // Encoding: 1111 0 i 10 1 1 0 0 imm4 | 0 imm3 Rd imm8
        // For 0x2000: imm4=2, i=0, imm3=0, imm8=0
        code.extend_from_slice(&[0xC2, 0xF2, 0x00, 0x0B]); // MOVT R11, #0x2000

        // Load entry point into R0
        // LDR r0, [pc, #offset] (load from PC+4+offset, aligned)
        // After MOVW+MOVT (8 bytes), we have: LDR, BLX, B, padding, literal
        // PC = current + 4 (Thumb pipeline)
        // Literal is at PC + 4 (after BLX and B.W)
        code.extend_from_slice(&[0x01, 0x48]); // LDR r0, [pc, #4]

        // Thumb encoding for: BLX r0
        code.extend_from_slice(&[0x80, 0x47]); // BLX r0

        // Thumb encoding for: B . (infinite loop)
        code.extend_from_slice(&[0xfe, 0xe7]); // B . (branch to self)

        // Padding to align literal pool (need 2 bytes to align to 4)
        code.extend_from_slice(&[0x00, 0x00]); // NOP padding

        // Literal pool: entry point address (with Thumb bit set)
        code.extend_from_slice(&(self.entry_point | 1).to_le_bytes());

        code
    }

    /// Generate a default exception handler (infinite loop)
    pub fn generate_default_handler() -> Vec<u8> {
        // Thumb encoding for: B . (infinite loop)
        vec![0xfe, 0xe7]
    }
}

/// Memory layout for Cortex-M target
#[derive(Debug, Clone)]
pub struct MemoryLayout {
    /// Flash base address
    pub flash_base: u32,
    /// Flash size in bytes
    pub flash_size: u32,
    /// RAM base address
    pub ram_base: u32,
    /// RAM size in bytes
    pub ram_size: u32,
}

impl MemoryLayout {
    /// STM32F407 memory layout
    pub fn stm32f407() -> Self {
        Self {
            flash_base: 0x0800_0000,
            flash_size: 1024 * 1024, // 1MB
            ram_base: 0x2000_0000,
            ram_size: 128 * 1024, // 128KB (main SRAM)
        }
    }

    /// nRF52840 memory layout
    pub fn nrf52840() -> Self {
        Self {
            flash_base: 0x0000_0000,
            flash_size: 1024 * 1024, // 1MB
            ram_base: 0x2000_0000,
            ram_size: 256 * 1024, // 256KB
        }
    }

    /// Generic Cortex-M layout (suitable for QEMU/Renode testing)
    pub fn generic() -> Self {
        Self {
            flash_base: 0x0000_0000,
            flash_size: 256 * 1024, // 256KB
            ram_base: 0x2000_0000,
            ram_size: 64 * 1024, // 64KB
        }
    }

    /// Get stack top address (end of RAM)
    pub fn stack_top(&self) -> u32 {
        self.ram_base + self.ram_size
    }
}

/// Build a complete Cortex-M binary with vector table and startup code
pub struct CortexMBuilder {
    layout: MemoryLayout,
    code: Vec<u8>,
    entry_name: String,
}

impl CortexMBuilder {
    /// Create a new Cortex-M builder with the given memory layout
    pub fn new(layout: MemoryLayout) -> Self {
        Self {
            layout,
            code: Vec::new(),
            entry_name: "main".to_string(),
        }
    }

    /// Set the function code
    pub fn with_code(mut self, code: Vec<u8>) -> Self {
        self.code = code;
        self
    }

    /// Set the entry point name
    pub fn with_entry_name(mut self, name: &str) -> Self {
        self.entry_name = name.to_string();
        self
    }

    /// Build complete flash image with vector table + startup + code
    ///
    /// Returns (flash_image, entry_point_address)
    pub fn build(&self) -> (Vec<u8>, u32) {
        let mut image = Vec::new();

        // Calculate addresses
        let vector_table_size = 64; // 16 entries * 4 bytes
        let startup_offset = vector_table_size;

        // Generate startup code first to know its size
        let startup = StartupCode::minimal(0); // Placeholder entry
        let startup_code = startup.generate_thumb();
        let startup_size = startup_code.len() as u32;

        // Default handler comes after startup
        let default_handler_offset = startup_offset + startup_size as usize;
        let default_handler = StartupCode::generate_default_handler();
        let default_handler_size = default_handler.len() as u32;

        // User code comes after default handler, aligned to 4 bytes
        let code_offset = ((default_handler_offset + default_handler_size as usize + 3) / 4) * 4;
        let code_addr = self.layout.flash_base + code_offset as u32;

        // Now regenerate startup with correct entry point
        let startup = StartupCode::minimal(code_addr);
        let startup_code = startup.generate_thumb();

        // Generate vector table
        let reset_handler_addr = self.layout.flash_base + startup_offset as u32;
        let default_handler_addr = self.layout.flash_base + default_handler_offset as u32;

        let vector_table = VectorTable::minimal(self.layout.stack_top(), reset_handler_addr);
        let vector_table_data = vector_table.generate(default_handler_addr);

        // Build the image
        image.extend_from_slice(&vector_table_data);
        image.extend_from_slice(&startup_code);
        image.extend_from_slice(&default_handler);

        // Pad to code offset
        while image.len() < code_offset {
            image.push(0);
        }

        // Add user code
        image.extend_from_slice(&self.code);

        (image, code_addr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vector_table_generation() {
        let vt = VectorTable::minimal(0x2001_0000, 0x0800_0040);
        let data = vt.generate(0x0800_0080);

        // Check size (16 entries * 4 bytes)
        assert_eq!(data.len(), 64);

        // Check initial SP
        let sp = u32::from_le_bytes([data[0], data[1], data[2], data[3]]);
        assert_eq!(sp, 0x2001_0000);

        // Check reset handler (with Thumb bit)
        let reset = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);
        assert_eq!(reset, 0x0800_0041); // Original | 1
    }

    #[test]
    fn test_startup_code_generation() {
        let startup = StartupCode::minimal(0x0800_0100);
        let code = startup.generate_thumb();

        // Should generate some code
        assert!(!code.is_empty());

        // Should be even length (Thumb alignment)
        assert_eq!(code.len() % 2, 0);

        // Should contain the entry point in the literal pool
        let entry_bytes = &code[code.len() - 4..];
        let entry = u32::from_le_bytes([
            entry_bytes[0],
            entry_bytes[1],
            entry_bytes[2],
            entry_bytes[3],
        ]);
        assert_eq!(entry, 0x0800_0101); // With Thumb bit
    }

    #[test]
    fn test_memory_layout() {
        let stm32 = MemoryLayout::stm32f407();
        assert_eq!(stm32.flash_base, 0x0800_0000);
        assert_eq!(stm32.stack_top(), 0x2002_0000); // 128KB RAM

        let nrf = MemoryLayout::nrf52840();
        assert_eq!(nrf.flash_base, 0x0000_0000);
        assert_eq!(nrf.stack_top(), 0x2004_0000); // 256KB RAM
    }

    #[test]
    fn test_cortex_m_builder() {
        let layout = MemoryLayout::generic();

        // Simple function that returns 42
        // Thumb: MOV r0, #42; BX lr
        let code = vec![
            0x2a, 0x20, // MOV r0, #42
            0x70, 0x47, // BX lr
        ];

        let builder = CortexMBuilder::new(layout).with_code(code);
        let (image, entry) = builder.build();

        // Image should start with vector table
        assert!(image.len() >= 64);

        // First word should be stack pointer (end of RAM)
        let sp = u32::from_le_bytes([image[0], image[1], image[2], image[3]]);
        assert_eq!(sp, 0x2001_0000); // 64KB RAM

        // Entry point should be after startup code
        assert!(entry > 64);
    }
}
