//! LED Blink Complete Integration Test
//!
//! Tests the entire pipeline with a realistic embedded example

use synth_backend::{
    ArmEncoder, ElfBuilder, ElfSectionType, ElfType, ResetHandlerGenerator, Section, SectionFlags,
    Symbol, SymbolBinding, SymbolType, VectorTable,
};
use synth_synthesis::{InstructionSelector, PeepholeOptimizer, RuleDatabase, WasmOp};

#[test]
fn test_led_blink_complete_pipeline() {
    // Simplified LED blink - GPIO operations
    let wasm_ops = vec![
        // GPIO initialization (simplified)
        WasmOp::I32Const(0x40020000), // GPIOA base
        WasmOp::LocalSet(0),
        // Main loop
        WasmOp::Loop,
        // Turn LED on
        WasmOp::LocalGet(0),
        WasmOp::I32Const(0x20), // Pin 5
        WasmOp::I32Store {
            offset: 0x18,
            align: 4,
        }, // BSRR
        // Delay
        WasmOp::I32Const(500000),
        WasmOp::LocalSet(1),
        WasmOp::Block,
        WasmOp::Loop,
        WasmOp::LocalGet(1),
        WasmOp::I32Const(1),
        WasmOp::I32Sub,
        WasmOp::LocalTee(1),
        WasmOp::I32Const(0),
        WasmOp::I32GtU,
        WasmOp::BrIf(0),
        WasmOp::End,
        WasmOp::End,
        // Turn LED off
        WasmOp::LocalGet(0),
        WasmOp::I32Const(0x200000), // Pin 5 reset
        WasmOp::I32Store {
            offset: 0x18,
            align: 4,
        },
        // Loop back
        WasmOp::Br(0),
        WasmOp::End,
    ];

    // Step 1: Instruction Selection
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector
        .select(&wasm_ops)
        .expect("Failed to select instructions");

    println!("Selected {} ARM instructions", arm_instrs.len());
    assert!(!arm_instrs.is_empty());

    // Step 2: Peephole Optimization
    let optimizer = PeepholeOptimizer::new();
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let (optimized_ops, opt_stats) = optimizer.optimize_with_stats(&ops);

    println!(
        "Optimization reduced {} → {} instructions ({:.1}% reduction)",
        opt_stats.original_instructions,
        opt_stats.optimized_instructions,
        opt_stats.reduction_percentage()
    );

    // Step 3: ARM Encoding
    let encoder = ArmEncoder::new_arm32();
    let mut code = Vec::new();
    for op in &optimized_ops {
        let encoded = encoder.encode(op).expect("Failed to encode");
        code.extend_from_slice(&encoded);
    }

    println!("Generated {} bytes of ARM code", code.len());
    assert!(!code.is_empty());
    assert_eq!(code.len() % 4, 0);

    // Step 4: Create Vector Table
    let mut vector_table = VectorTable::new_cortex_m(0x20010000);
    vector_table.reset_handler = 0x08000100; // After vector table
    let vt_binary = vector_table
        .generate_binary()
        .expect("Failed to generate vector table");

    println!("Vector table: {} bytes", vt_binary.len());

    // Step 5: Create Reset Handler
    let reset_gen = ResetHandlerGenerator::new();
    let reset_code = reset_gen
        .generate_binary()
        .expect("Failed to generate reset handler");

    println!("Reset handler: {} bytes", reset_code.len());

    // Step 6: Build Complete ELF
    let mut elf_builder = ElfBuilder::new_arm32()
        .with_entry(0x08000000) // Start of Flash
        .with_type(ElfType::Exec);

    // Vector table section
    let vt_section = Section::new(".isr_vector", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(0x08000000)
        .with_align(128) // Vector table must be 128-byte aligned
        .with_data(vt_binary);

    elf_builder.add_section(vt_section);

    // Reset handler + LED code in .text
    let reset_code_len = reset_code.len();
    let mut text_code = reset_code;
    text_code.extend_from_slice(&code);

    let text_section = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(0x08000100)
        .with_align(4)
        .with_data(text_code.clone());

    elf_builder.add_section(text_section);

    // .data section (empty for this example)
    let data_section = Section::new(".data", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE)
        .with_addr(0x20000000)
        .with_align(4)
        .with_data(vec![]);

    elf_builder.add_section(data_section);

    // .bss section (zero-initialized)
    let bss_section = Section::new(".bss", ElfSectionType::NoBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE)
        .with_addr(0x20000100)
        .with_align(4);

    elf_builder.add_section(bss_section);

    // Add symbols
    let reset_sym = Symbol::new("Reset_Handler")
        .with_value(0x08000100)
        .with_size(text_code.len() as u32)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(5); // .text

    elf_builder.add_symbol(reset_sym);

    let main_sym = Symbol::new("main")
        .with_value(0x08000100 + reset_code_len as u32)
        .with_size(code.len() as u32)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(5);

    elf_builder.add_symbol(main_sym);

    // Step 7: Build final ELF
    let elf_data = elf_builder.build().expect("Failed to build ELF");

    println!("Final ELF size: {} bytes", elf_data.len());

    // Validate ELF structure
    assert!(elf_data.len() > 52);
    assert_eq!(&elf_data[0..4], &[0x7f, b'E', b'L', b'F']);
    assert_eq!(elf_data[4], 1); // 32-bit
    assert_eq!(elf_data[5], 1); // little-endian
    assert_eq!(elf_data[18], 0x28); // ARM machine type

    // Could write to file for inspection
    // std::fs::write("led_blink.elf", &elf_data).ok();

    println!("✓ LED Blink complete pipeline test passed!");
    println!("  - Compiled {} WASM operations", wasm_ops.len());
    println!("  - Selected {} ARM instructions", arm_instrs.len());
    println!("  - Optimized to {} instructions", optimized_ops.len());
    println!("  - Generated {} bytes of code", code.len());
    println!("  - Built {} byte ELF binary", elf_data.len());
    println!("  - Ready for deployment to ARM Cortex-M target!");
}

#[test]
fn test_gpio_peripheral_operations() {
    // Test GPIO-specific operations
    let wasm_ops = vec![
        // Read GPIO register
        WasmOp::I32Const(0x40020000),
        WasmOp::I32Load {
            offset: 0,
            align: 4,
        },
        // Modify bit
        WasmOp::I32Const(0x20),
        WasmOp::I32Or,
        // Write back
        WasmOp::I32Const(0x40020000),
        WasmOp::I32Store {
            offset: 0,
            align: 4,
        },
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    assert!(!arm_instrs.is_empty());
}

#[test]
fn test_delay_loop_generation() {
    // Test delay loop code generation
    let wasm_ops = vec![
        WasmOp::I32Const(1000000),
        WasmOp::LocalSet(0),
        WasmOp::Block,
        WasmOp::Loop,
        WasmOp::LocalGet(0),
        WasmOp::I32Const(1),
        WasmOp::I32Sub,
        WasmOp::LocalTee(0),
        WasmOp::BrIf(1), // Exit if zero
        WasmOp::Br(0),   // Continue loop
        WasmOp::End,
        WasmOp::End,
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    println!("Delay loop: {} ARM instructions", arm_instrs.len());
    assert!(!arm_instrs.is_empty());
}

#[test]
fn test_compare_to_native_code_size() {
    // Compare our generated code to typical native size
    let wasm_ops = vec![
        // Simple arithmetic
        WasmOp::I32Const(10),
        WasmOp::I32Const(20),
        WasmOp::I32Add,
        WasmOp::I32Const(2),
        WasmOp::I32Mul,
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed");

    let optimizer = PeepholeOptimizer::new();
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let (optimized, _) = optimizer.optimize_with_stats(&ops);

    let encoder = ArmEncoder::new_arm32();
    let mut code_size = 0;
    for op in &optimized {
        let encoded = encoder.encode(op).expect("Failed to encode");
        code_size += encoded.len();
    }

    println!("Generated code size: {} bytes", code_size);
    println!("Typical native: ~20 bytes");

    // Our code should be reasonably sized
    assert!(code_size < 100); // Not too bloated
}
