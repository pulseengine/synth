//! Reset Handler Code Generation
//!
//! Generates the Reset_Handler startup code for ARM Cortex-M

use crate::arm_encoder::ArmEncoder;
use synth_core::Result;
use synth_synthesis::{ArmOp, MemAddr, Operand2, Reg};

/// Reset handler generator
pub struct ResetHandlerGenerator {
    /// Stack top address
    stack_top: u32,
    /// Data section start in RAM
    data_start: u32,
    /// Data section end in RAM
    data_end: u32,
    /// Data section load address in Flash
    data_load_addr: u32,
    /// BSS section start
    bss_start: u32,
    /// BSS section end
    bss_end: u32,
}

impl ResetHandlerGenerator {
    /// Create a new reset handler generator
    pub fn new() -> Self {
        Self {
            stack_top: 0x20010000,      // 64KB RAM top
            data_start: 0x20000000,     // RAM start
            data_end: 0x20000100,       // 256 bytes data
            data_load_addr: 0x08001000, // Flash location
            bss_start: 0x20000100,      // After data
            bss_end: 0x20001000,        // 3.75KB BSS
        }
    }

    /// Configure memory regions
    pub fn with_memory_layout(
        mut self,
        stack_top: u32,
        data_start: u32,
        data_end: u32,
        data_load: u32,
        bss_start: u32,
        bss_end: u32,
    ) -> Self {
        self.stack_top = stack_top;
        self.data_start = data_start;
        self.data_end = data_end;
        self.data_load_addr = data_load;
        self.bss_start = bss_start;
        self.bss_end = bss_end;
        self
    }

    /// Generate ARM instructions for reset handler
    #[allow(clippy::vec_init_then_push)]
    pub fn generate_instructions(&self) -> Vec<ArmOp> {
        let mut instrs = Vec::new();

        // Copy .data section from Flash to RAM
        // R0 = source (Flash load address)
        // R1 = destination (RAM data start)
        // R2 = end address (RAM data end)

        // Load data_load_addr into R0 using MOVW/MOVT (full 32-bit)
        instrs.push(ArmOp::Movw {
            rd: Reg::R0,
            imm16: (self.data_load_addr & 0xFFFF) as u16,
        });
        instrs.push(ArmOp::Movt {
            rd: Reg::R0,
            imm16: (self.data_load_addr >> 16) as u16,
        });

        // Load data_start into R1
        instrs.push(ArmOp::Movw {
            rd: Reg::R1,
            imm16: (self.data_start & 0xFFFF) as u16,
        });
        instrs.push(ArmOp::Movt {
            rd: Reg::R1,
            imm16: (self.data_start >> 16) as u16,
        });

        // Load data_end into R2
        instrs.push(ArmOp::Movw {
            rd: Reg::R2,
            imm16: (self.data_end & 0xFFFF) as u16,
        });
        instrs.push(ArmOp::Movt {
            rd: Reg::R2,
            imm16: (self.data_end >> 16) as u16,
        });

        // .data copy loop: copy words from Flash (R0) to RAM (R1) until R1 == R2
        // .Lcopy_check:
        instrs.push(ArmOp::Label {
            name: ".Lcopy_check".to_string(),
        });
        instrs.push(ArmOp::Cmp {
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        });
        // BHS .Lcopy_done (branch if R1 >= R2, i.e., done)
        instrs.push(ArmOp::Bhs {
            label: ".Lcopy_done".to_string(),
        });
        // LDR R3, [R0], #4 — load word from source, post-increment
        // Using explicit load + add since post-increment may not be available
        instrs.push(ArmOp::Ldr {
            rd: Reg::R3,
            addr: MemAddr {
                base: Reg::R0,
                offset: 0,
                offset_reg: None,
            },
        });
        instrs.push(ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Imm(4),
        });
        // STR R3, [R1], #4 — store word to dest, post-increment
        instrs.push(ArmOp::Str {
            rd: Reg::R3,
            addr: MemAddr {
                base: Reg::R1,
                offset: 0,
                offset_reg: None,
            },
        });
        instrs.push(ArmOp::Add {
            rd: Reg::R1,
            rn: Reg::R1,
            op2: Operand2::Imm(4),
        });
        // B .Lcopy_check
        instrs.push(ArmOp::B {
            label: ".Lcopy_check".to_string(),
        });
        instrs.push(ArmOp::Label {
            name: ".Lcopy_done".to_string(),
        });

        // Zero .bss section
        // R0 = bss start, R1 = bss end, R2 = zero value
        instrs.push(ArmOp::Movw {
            rd: Reg::R0,
            imm16: (self.bss_start & 0xFFFF) as u16,
        });
        instrs.push(ArmOp::Movt {
            rd: Reg::R0,
            imm16: (self.bss_start >> 16) as u16,
        });

        instrs.push(ArmOp::Movw {
            rd: Reg::R1,
            imm16: (self.bss_end & 0xFFFF) as u16,
        });
        instrs.push(ArmOp::Movt {
            rd: Reg::R1,
            imm16: (self.bss_end >> 16) as u16,
        });

        instrs.push(ArmOp::Mov {
            rd: Reg::R2,
            op2: Operand2::Imm(0),
        });

        // .bss zero loop: zero words from R0 to R1
        // .Lzero_check:
        instrs.push(ArmOp::Label {
            name: ".Lzero_check".to_string(),
        });
        instrs.push(ArmOp::Cmp {
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        });
        // BHS .Lzero_done (branch if R0 >= R1)
        instrs.push(ArmOp::Bhs {
            label: ".Lzero_done".to_string(),
        });
        instrs.push(ArmOp::Str {
            rd: Reg::R2,
            addr: MemAddr {
                base: Reg::R0,
                offset: 0,
                offset_reg: None,
            },
        });
        instrs.push(ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Imm(4),
        });
        // B .Lzero_check
        instrs.push(ArmOp::B {
            label: ".Lzero_check".to_string(),
        });
        instrs.push(ArmOp::Label {
            name: ".Lzero_done".to_string(),
        });

        // Call main
        instrs.push(ArmOp::Bl {
            label: "main".to_string(),
        });

        // Infinite loop after main returns
        instrs.push(ArmOp::B {
            label: ".".to_string(), // Branch to self
        });

        instrs
    }

    /// Generate complete reset handler assembly
    pub fn generate_assembly(&self) -> String {
        let mut asm = String::new();

        asm.push_str("    .syntax unified\n");
        asm.push_str("    .cpu cortex-m3\n");
        asm.push_str("    .fpu softvfp\n");
        asm.push_str("    .thumb\n\n");

        asm.push_str("    .section .text.Reset_Handler\n");
        asm.push_str("    .weak Reset_Handler\n");
        asm.push_str("    .type Reset_Handler, %function\n");
        asm.push_str("Reset_Handler:\n");

        // Copy .data section
        asm.push_str("    /* Copy data section from Flash to RAM */\n");
        asm.push_str("    ldr r0, =_sidata      /* start of .data in Flash */\n");
        asm.push_str("    ldr r1, =_sdata       /* start of .data in RAM */\n");
        asm.push_str("    ldr r2, =_edata       /* end of .data in RAM */\n");
        asm.push_str("    movs r3, #0\n");
        asm.push_str("    b LoopCopyDataInit\n\n");

        asm.push_str("CopyDataInit:\n");
        asm.push_str("    ldr r4, [r0, r3]\n");
        asm.push_str("    str r4, [r1, r3]\n");
        asm.push_str("    adds r3, r3, #4\n\n");

        asm.push_str("LoopCopyDataInit:\n");
        asm.push_str("    adds r4, r1, r3\n");
        asm.push_str("    cmp r4, r2\n");
        asm.push_str("    bcc CopyDataInit\n\n");

        // Zero .bss section
        asm.push_str("    /* Zero fill .bss section */\n");
        asm.push_str("    ldr r2, =_sbss\n");
        asm.push_str("    ldr r4, =_ebss\n");
        asm.push_str("    movs r3, #0\n");
        asm.push_str("    b LoopFillZerobss\n\n");

        asm.push_str("FillZerobss:\n");
        asm.push_str("    str r3, [r2]\n");
        asm.push_str("    adds r2, r2, #4\n\n");

        asm.push_str("LoopFillZerobss:\n");
        asm.push_str("    cmp r2, r4\n");
        asm.push_str("    bcc FillZerobss\n\n");

        // Call static constructors (C++)
        asm.push_str("    /* Call static constructors */\n");
        asm.push_str("    bl __libc_init_array\n\n");

        // Call main
        asm.push_str("    /* Call main() */\n");
        asm.push_str("    bl main\n\n");

        // Infinite loop
        asm.push_str("LoopForever:\n");
        asm.push_str("    b LoopForever\n\n");

        asm.push_str("    .size Reset_Handler, .-Reset_Handler\n");

        asm
    }

    /// Generate binary code for reset handler
    pub fn generate_binary(&self) -> Result<Vec<u8>> {
        self.generate_binary_for_isa(false)
    }

    /// Generate binary code for reset handler with ISA selection
    pub fn generate_binary_for_isa(&self, thumb_mode: bool) -> Result<Vec<u8>> {
        let encoder = if thumb_mode {
            ArmEncoder::new_thumb2()
        } else {
            ArmEncoder::new_arm32()
        };
        let instrs = self.generate_instructions();

        let mut code = Vec::new();
        for instr in &instrs {
            let encoded = encoder.encode(instr)?;
            code.extend_from_slice(&encoded);
        }

        Ok(code)
    }
}

impl Default for ResetHandlerGenerator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reset_handler_creation() {
        let handler = ResetHandlerGenerator::new();
        assert_eq!(handler.stack_top, 0x20010000);
    }

    #[test]
    fn test_reset_handler_instructions() {
        let handler = ResetHandlerGenerator::new();
        let instrs = handler.generate_instructions();
        assert!(!instrs.is_empty());

        // Should end with branch to main and infinite loop
        assert!(matches!(instrs[instrs.len() - 2], ArmOp::Bl { .. }));
        assert!(matches!(instrs[instrs.len() - 1], ArmOp::B { .. }));
    }

    #[test]
    fn test_reset_handler_binary() {
        let handler = ResetHandlerGenerator::new();
        let binary = handler.generate_binary().unwrap();
        assert!(!binary.is_empty());
        assert_eq!(binary.len() % 4, 0); // ARM32 instructions are 4 bytes
    }

    #[test]
    fn test_reset_handler_assembly() {
        let handler = ResetHandlerGenerator::new();
        let asm = handler.generate_assembly();

        assert!(asm.contains("Reset_Handler:"));
        assert!(asm.contains("CopyDataInit"));
        assert!(asm.contains("FillZerobss"));
        assert!(asm.contains("bl main"));
    }

    #[test]
    fn test_custom_memory_layout() {
        let handler = ResetHandlerGenerator::new().with_memory_layout(
            0x20020000, // 128KB RAM
            0x20000000, 0x20000200, 0x08002000, 0x20000200, 0x20002000,
        );

        assert_eq!(handler.stack_top, 0x20020000);
        assert_eq!(handler.data_start, 0x20000000);
    }
}
