//! ARM Cortex-M Vector Table Generation
//!
//! Generates the interrupt vector table required for ARM Cortex-M startup

use synth_core::Result;

/// Vector table entry
#[derive(Debug, Clone)]
pub struct VectorEntry {
    /// Handler name
    pub name: String,
    /// Address (0 for unresolved)
    pub address: u32,
    /// Is this a weak symbol
    pub weak: bool,
}

/// ARM Cortex-M Vector Table
pub struct VectorTable {
    /// Initial stack pointer value
    pub initial_sp: u32,
    /// Reset handler address
    pub reset_handler: u32,
    /// Exception and interrupt handlers
    pub handlers: Vec<VectorEntry>,
}

impl VectorTable {
    /// Create a new vector table for Cortex-M
    pub fn new_cortex_m(stack_top: u32) -> Self {
        let mut handlers = Vec::new();

        // Cortex-M standard exceptions (16 entries)
        handlers.push(VectorEntry {
            name: "NMI_Handler".to_string(),
            address: 0,
            weak: true,
        });
        handlers.push(VectorEntry {
            name: "HardFault_Handler".to_string(),
            address: 0,
            weak: false, // HardFault is critical
        });
        handlers.push(VectorEntry {
            name: "MemManage_Handler".to_string(),
            address: 0,
            weak: true,
        });
        handlers.push(VectorEntry {
            name: "BusFault_Handler".to_string(),
            address: 0,
            weak: true,
        });
        handlers.push(VectorEntry {
            name: "UsageFault_Handler".to_string(),
            address: 0,
            weak: true,
        });
        // Reserved entries (4)
        for _ in 0..4 {
            handlers.push(VectorEntry {
                name: "Reserved".to_string(),
                address: 0,
                weak: true,
            });
        }
        handlers.push(VectorEntry {
            name: "SVC_Handler".to_string(),
            address: 0,
            weak: true,
        });
        handlers.push(VectorEntry {
            name: "DebugMon_Handler".to_string(),
            address: 0,
            weak: true,
        });
        handlers.push(VectorEntry {
            name: "Reserved".to_string(),
            address: 0,
            weak: true,
        });
        handlers.push(VectorEntry {
            name: "PendSV_Handler".to_string(),
            address: 0,
            weak: true,
        });
        handlers.push(VectorEntry {
            name: "SysTick_Handler".to_string(),
            address: 0,
            weak: true,
        });

        // External interrupts (typically 16-240 depending on device)
        // For PoC, add 16 generic IRQ handlers
        for i in 0..16 {
            handlers.push(VectorEntry {
                name: format!("IRQ{}_Handler", i),
                address: 0,
                weak: true,
            });
        }

        Self {
            initial_sp: stack_top,
            reset_handler: 0,
            handlers,
        }
    }

    /// Generate vector table as binary data
    pub fn generate_binary(&self) -> Result<Vec<u8>> {
        let mut data = Vec::new();

        // Entry 0: Initial stack pointer
        data.extend_from_slice(&self.initial_sp.to_le_bytes());

        // Entry 1: Reset handler
        // Thumb mode requires LSB set to 1
        let reset_addr = self.reset_handler | 1;
        data.extend_from_slice(&reset_addr.to_le_bytes());

        // Remaining handlers
        for handler in &self.handlers {
            let addr = if handler.address != 0 {
                handler.address | 1 // Thumb mode bit
            } else {
                0 // Will be resolved by linker
            };
            data.extend_from_slice(&addr.to_le_bytes());
        }

        Ok(data)
    }

    /// Generate assembly source for vector table
    pub fn generate_assembly(&self) -> String {
        let mut asm = String::new();

        asm.push_str("    .syntax unified\n");
        asm.push_str("    .cpu cortex-m3\n");
        asm.push_str("    .fpu softvfp\n");
        asm.push_str("    .thumb\n\n");

        asm.push_str("    .section .isr_vector,\"a\",%progbits\n");
        asm.push_str("    .type g_pfnVectors, %object\n");
        asm.push_str("    .size g_pfnVectors, .-g_pfnVectors\n\n");

        asm.push_str("g_pfnVectors:\n");
        asm.push_str(&format!("    .word _estack\n"));
        asm.push_str("    .word Reset_Handler\n");

        for handler in &self.handlers {
            asm.push_str(&format!("    .word {}\n", handler.name));
        }

        asm.push_str("\n");

        // Define weak default handlers
        asm.push_str("    .weak NMI_Handler\n");
        asm.push_str("    .thumb_set NMI_Handler,Default_Handler\n\n");

        for handler in &self.handlers {
            if handler.weak && handler.name != "Reserved" {
                asm.push_str(&format!("    .weak {}\n", handler.name));
                asm.push_str(&format!("    .thumb_set {},Default_Handler\n", handler.name));
            }
        }

        asm.push_str("\n");
        asm.push_str("    .section .text.Default_Handler,\"ax\",%progbits\n");
        asm.push_str("Default_Handler:\n");
        asm.push_str("Infinite_Loop:\n");
        asm.push_str("    b Infinite_Loop\n");
        asm.push_str("    .size Default_Handler, .-Default_Handler\n");

        asm
    }

    /// Get total size in bytes
    pub fn size_bytes(&self) -> usize {
        // SP + Reset + handlers
        4 + 4 + (self.handlers.len() * 4)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vector_table_creation() {
        let vt = VectorTable::new_cortex_m(0x20010000);
        assert_eq!(vt.initial_sp, 0x20010000);
        assert!(vt.handlers.len() > 15); // At least standard exceptions
    }

    #[test]
    fn test_vector_table_binary_generation() {
        let mut vt = VectorTable::new_cortex_m(0x20010000);
        vt.reset_handler = 0x08000100;

        let binary = vt.generate_binary().unwrap();

        // Check initial SP
        let sp = u32::from_le_bytes([binary[0], binary[1], binary[2], binary[3]]);
        assert_eq!(sp, 0x20010000);

        // Check reset handler (with Thumb bit)
        let reset = u32::from_le_bytes([binary[4], binary[5], binary[6], binary[7]]);
        assert_eq!(reset, 0x08000101); // LSB set for Thumb
    }

    #[test]
    fn test_vector_table_size() {
        let vt = VectorTable::new_cortex_m(0x20010000);
        let size = vt.size_bytes();
        let binary = vt.generate_binary().unwrap();
        assert_eq!(size, binary.len());
    }

    #[test]
    fn test_assembly_generation() {
        let vt = VectorTable::new_cortex_m(0x20010000);
        let asm = vt.generate_assembly();

        assert!(asm.contains(".syntax unified"));
        assert!(asm.contains("g_pfnVectors:"));
        assert!(asm.contains("Reset_Handler"));
        assert!(asm.contains("Default_Handler"));
    }

    #[test]
    fn test_thumb_mode_bit() {
        let mut vt = VectorTable::new_cortex_m(0x20010000);
        vt.reset_handler = 0x08000100; // Even address
        vt.handlers[0].address = 0x08000200;

        let binary = vt.generate_binary().unwrap();

        // Reset handler should have bit 0 set
        let reset = u32::from_le_bytes([binary[4], binary[5], binary[6], binary[7]]);
        assert_eq!(reset & 1, 1);

        // First handler should have bit 0 set
        let handler = u32::from_le_bytes([binary[8], binary[9], binary[10], binary[11]]);
        assert_eq!(handler & 1, 1);
    }
}
