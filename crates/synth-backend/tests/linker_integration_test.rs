//! Linker Script Integration Test
//!
//! Tests complete linker script generation for real embedded targets

use synth_backend::{LinkerScriptGenerator, MemoryRegion};

#[test]
fn test_stm32f4_linker_script() {
    // Generate linker script for STM32F4 (512KB Flash, 128KB RAM)
    let generator = LinkerScriptGenerator::new_stm32();
    let script = generator.generate().expect("Failed to generate");

    // Verify memory regions
    assert!(script.contains("FLASH (rx): ORIGIN = 0x08000000, LENGTH = 0x80000"));
    assert!(script.contains("RAM (rwx): ORIGIN = 0x20000000, LENGTH = 0x20000"));

    // Verify entry point
    assert!(script.contains("ENTRY(Reset_Handler)"));

    // Verify sections
    assert!(script.contains(".isr_vector"));
    assert!(script.contains(".text"));
    assert!(script.contains(".rodata"));
    assert!(script.contains(".data"));
    assert!(script.contains(".bss"));

    // Verify symbols for startup code
    assert!(script.contains("_sdata"));
    assert!(script.contains("_edata"));
    assert!(script.contains("_sbss"));
    assert!(script.contains("_ebss"));
    assert!(script.contains("_estack"));

    println!("Generated STM32F4 linker script:");
    println!("{}", script);
}

#[test]
fn test_stm32f1_linker_script() {
    // Generate linker script for STM32F1 (64KB Flash, 20KB RAM)
    let mut generator = LinkerScriptGenerator::new();

    generator.add_region(MemoryRegion {
        name: "FLASH".to_string(),
        origin: 0x08000000,
        length: 64 * 1024,
        attributes: "rx".to_string(),
    });

    generator.add_region(MemoryRegion {
        name: "RAM".to_string(),
        origin: 0x20000000,
        length: 20 * 1024,
        attributes: "rwx".to_string(),
    });

    let script = generator
        .with_entry_point("Reset_Handler".to_string())
        .with_stack_size(2048)
        .with_heap_size(0)
        .generate()
        .expect("Failed to generate");

    assert!(script.contains("LENGTH = 0x10000")); // 64KB
    assert!(script.contains("LENGTH = 0x5000"));  // 20KB
    assert!(script.contains("_stack_size = 0x800")); // 2KB stack
}

#[test]
fn test_rp2040_linker_script() {
    // Generate linker script for RP2040 (2MB Flash, 264KB RAM)
    let mut generator = LinkerScriptGenerator::new();

    generator.add_region(MemoryRegion {
        name: "FLASH".to_string(),
        origin: 0x10000000,  // RP2040 XIP Flash
        length: 2 * 1024 * 1024,
        attributes: "rx".to_string(),
    });

    generator.add_region(MemoryRegion {
        name: "RAM".to_string(),
        origin: 0x20000000,
        length: 264 * 1024,
        attributes: "rwx".to_string(),
    });

    let script = generator
        .with_entry_point("_entry".to_string())
        .with_stack_size(8192)
        .with_heap_size(32768)
        .generate()
        .expect("Failed to generate");

    assert!(script.contains("0x10000000")); // XIP Flash origin
    assert!(script.contains("ENTRY(_entry)"));
    assert!(script.contains("_heap_size = 0x8000")); // 32KB heap
}

#[test]
fn test_nordic_nrf52_linker_script() {
    // Generate linker script for Nordic nRF52 (512KB Flash, 64KB RAM)
    let mut generator = LinkerScriptGenerator::new();

    generator.add_region(MemoryRegion {
        name: "FLASH".to_string(),
        origin: 0x00000000,  // nRF52 Flash at 0x0
        length: 512 * 1024,
        attributes: "rx".to_string(),
    });

    generator.add_region(MemoryRegion {
        name: "RAM".to_string(),
        origin: 0x20000000,
        length: 64 * 1024,
        attributes: "rwx".to_string(),
    });

    let script = generator.generate().expect("Failed to generate");

    assert!(script.contains("0x00000000")); // Flash at 0x0
    assert!(script.contains("0x80000"));    // 512KB
}

#[test]
fn test_linker_script_file_generation() {
    // Test writing to file
    let generator = LinkerScriptGenerator::new_stm32();

    let temp_file = "/tmp/test_linker.ld";
    generator.generate_to_file(temp_file).expect("Failed to write");

    // Verify file exists and contains expected content
    let contents = std::fs::read_to_string(temp_file).expect("Failed to read");
    assert!(contents.contains("MEMORY"));
    assert!(contents.contains("SECTIONS"));

    // Cleanup
    std::fs::remove_file(temp_file).ok();
}

#[test]
fn test_alignment_requirements() {
    let generator = LinkerScriptGenerator::new_stm32();
    let script = generator.generate().expect("Failed to generate");

    // Vector table must be 128-byte aligned (ARM Cortex-M requirement)
    assert!(script.contains("ALIGN(128)"));

    // Data sections should be 4-byte aligned
    let align_4_count = script.matches("ALIGN(4)").count();
    assert!(align_4_count > 5);

    // Stack should be 8-byte aligned (ARM EABI requirement)
    assert!(script.contains("ALIGN(8)"));
}

#[test]
fn test_section_placement() {
    let generator = LinkerScriptGenerator::new_stm32();
    let script = generator.generate().expect("Failed to generate");

    // ISR vector should be in FLASH
    assert!(script.contains(".isr_vector :") && script.contains("} >FLASH"));

    // Text should be in FLASH
    assert!(script.contains(".text :") && script.contains("} >FLASH"));

    // Data should be in RAM but loaded from FLASH
    assert!(script.contains(".data :") && script.contains(">RAM AT> FLASH"));

    // BSS should be in RAM only
    assert!(script.contains(".bss :") && script.contains("} >RAM"));
}

#[test]
fn test_startup_symbols() {
    let generator = LinkerScriptGenerator::new_stm32();
    let script = generator.generate().expect("Failed to generate");

    // Data initialization symbols (used by reset handler)
    assert!(script.contains("_sidata"));  // Load address
    assert!(script.contains("_sdata"));   // Start in RAM
    assert!(script.contains("_edata"));   // End in RAM

    // BSS symbols (used by reset handler)
    assert!(script.contains("_sbss"));
    assert!(script.contains("_ebss"));
    assert!(script.contains("__bss_start__"));
    assert!(script.contains("__bss_end__"));

    // Stack symbol (used by vector table)
    assert!(script.contains("_estack"));
}

#[test]
fn test_cpp_support() {
    let generator = LinkerScriptGenerator::new_stm32();
    let script = generator.generate().expect("Failed to generate");

    // C++ constructor/destructor arrays
    assert!(script.contains(".preinit_array"));
    assert!(script.contains(".init_array"));
    assert!(script.contains(".fini_array"));

    // Array symbols
    assert!(script.contains("__preinit_array_start"));
    assert!(script.contains("__init_array_start"));
    assert!(script.contains("__fini_array_start"));
}

#[test]
fn test_exception_handling() {
    let generator = LinkerScriptGenerator::new_stm32();
    let script = generator.generate().expect("Failed to generate");

    // ARM exception handling sections
    assert!(script.contains(".ARM.extab"));
    assert!(script.contains(".ARM.exidx"));
    assert!(script.contains("__exidx_start"));
    assert!(script.contains("__exidx_end"));
}
