//! End-to-End Integration Test
//!
//! Tests the complete pipeline: WASM → ARM → ELF

use synth_backend::{
    ArmEncoder, ElfBuilder, ElfSectionType, Section, SectionFlags, Symbol, SymbolBinding,
    SymbolType,
};
use synth_synthesis::{InstructionSelector, RuleDatabase, WasmOp};

#[test]
fn test_end_to_end_pipeline() {
    // Step 1: Create simple WASM operations
    let wasm_ops = vec![WasmOp::I32Const(42), WasmOp::I32Const(10), WasmOp::I32Add];

    // Step 2: Select ARM instructions
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector
        .select(&wasm_ops)
        .expect("Failed to select instructions");

    // Should have generated some ARM instructions
    assert!(!arm_instrs.is_empty());

    // Step 3: Encode ARM instructions to binary
    let encoder = ArmEncoder::new_arm32();
    let mut code = Vec::new();

    for arm_instr in &arm_instrs {
        let encoded = encoder
            .encode(&arm_instr.op)
            .expect("Failed to encode instruction");
        code.extend_from_slice(&encoded);
    }

    // Should have generated some code
    assert!(!code.is_empty());
    // ARM32 instructions are 4 bytes each
    assert_eq!(code.len() % 4, 0);

    // Step 4: Package into ELF file
    let mut elf_builder = ElfBuilder::new_arm32().with_entry(0x8000);

    // Add .text section with code
    let text_section = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(0x8000)
        .with_align(4)
        .with_data(code.clone());

    elf_builder.add_section(text_section);

    // Add a symbol for the code
    let main_sym = Symbol::new("_start")
        .with_value(0x8000)
        .with_size(code.len() as u32)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(4); // .text is section 4

    elf_builder.add_symbol(main_sym);

    // Step 5: Build ELF file
    let elf_data = elf_builder.build().expect("Failed to build ELF");

    // Validate ELF structure
    assert!(elf_data.len() > 52); // At least ELF header
    assert_eq!(&elf_data[0..4], &[0x7f, b'E', b'L', b'F']); // ELF magic
    assert_eq!(elf_data[4], 1); // 32-bit
    assert_eq!(elf_data[5], 1); // little-endian

    // Verify entry point
    let entry_bytes = &elf_data[24..28];
    let entry = u32::from_le_bytes([
        entry_bytes[0],
        entry_bytes[1],
        entry_bytes[2],
        entry_bytes[3],
    ]);
    assert_eq!(entry, 0x8000);

    println!("✓ End-to-end pipeline test passed!");
    println!("  - Generated {} WASM ops", wasm_ops.len());
    println!("  - Selected {} ARM instructions", arm_instrs.len());
    println!("  - Encoded {} bytes of code", code.len());
    println!("  - Built {} byte ELF file", elf_data.len());
}

#[test]
fn test_wasm_arithmetic_to_elf() {
    // More complex arithmetic
    let wasm_ops = vec![
        WasmOp::I32Const(5),
        WasmOp::I32Const(3),
        WasmOp::I32Mul,
        WasmOp::I32Const(2),
        WasmOp::I32Add,
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    let encoder = ArmEncoder::new_arm32();
    let mut code = Vec::new();
    for instr in &arm_instrs {
        let encoded = encoder.encode(&instr.op).expect("Failed to encode");
        code.extend_from_slice(&encoded);
    }

    let mut elf_builder = ElfBuilder::new_arm32().with_entry(0x8000);

    let text = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(0x8000)
        .with_align(4)
        .with_data(code);

    elf_builder.add_section(text);

    let elf_data = elf_builder.build().expect("Failed to build");

    assert!(elf_data.len() > 52);
    assert_eq!(&elf_data[0..4], &[0x7f, b'E', b'L', b'F']);
}

#[test]
fn test_wasm_memory_operations_to_elf() {
    let wasm_ops = vec![
        WasmOp::I32Const(100),
        WasmOp::I32Store {
            offset: 0,
            align: 4,
        },
        WasmOp::I32Load {
            offset: 0,
            align: 4,
        },
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    let encoder = ArmEncoder::new_arm32();
    let mut code = Vec::new();
    for instr in &arm_instrs {
        let encoded = encoder.encode(&instr.op).expect("Failed to encode");
        code.extend_from_slice(&encoded);
    }

    assert!(!code.is_empty());
    assert_eq!(code.len() % 4, 0);

    let mut elf_builder = ElfBuilder::new_arm32().with_entry(0x8000);

    let text = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(0x8000)
        .with_align(4)
        .with_data(code.clone());

    elf_builder.add_section(text);

    // Add .data section
    let data = Section::new(".data", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE)
        .with_addr(0x8100)
        .with_align(4)
        .with_data(vec![0u8; 64]);

    elf_builder.add_section(data);

    let elf_data = elf_builder.build().expect("Failed to build");

    assert!(elf_data.len() > 52);
    assert_eq!(&elf_data[0..4], &[0x7f, b'E', b'L', b'F']);

    println!("✓ Memory operations test passed!");
    println!("  - Generated {} bytes of code", code.len());
    println!("  - ELF size: {} bytes", elf_data.len());
}

#[test]
fn test_complete_function_to_elf() {
    // Simulate a simple function: add(a, b) { return a + b; }
    let wasm_ops = vec![
        WasmOp::LocalGet(0), // Load param a
        WasmOp::LocalGet(1), // Load param b
        WasmOp::I32Add,      // Add them
                             // Return is implicit
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    let encoder = ArmEncoder::new_arm32();
    let mut code = Vec::new();
    for instr in &arm_instrs {
        let encoded = encoder.encode(&instr.op).expect("Failed to encode");
        code.extend_from_slice(&encoded);
    }

    let mut elf_builder = ElfBuilder::new_arm32().with_entry(0x8000);

    let text = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(0x8000)
        .with_align(4)
        .with_data(code.clone());

    elf_builder.add_section(text);

    // Add function symbol
    let add_func = Symbol::new("add")
        .with_value(0x8000)
        .with_size(code.len() as u32)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(4);

    elf_builder.add_symbol(add_func);

    let elf_data = elf_builder.build().expect("Failed to build");

    assert!(elf_data.len() > 52);
    assert_eq!(&elf_data[0..4], &[0x7f, b'E', b'L', b'F']);

    println!("✓ Complete function test passed!");
    println!("  - Function 'add' compiled successfully");
    println!("  - Code size: {} bytes", code.len());
}

#[test]
fn test_selector_stats() {
    let wasm_ops = vec![
        WasmOp::I32Const(1),
        WasmOp::I32Const(2),
        WasmOp::I32Add,
        WasmOp::I32Const(3),
        WasmOp::I32Mul,
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let _arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    let stats = selector.get_stats();
    println!("Selection stats:");
    println!("  - Registers used: {}", stats.total_registers_used);
    println!("  - Variables mapped: {}", stats.variables_mapped);

    assert!(stats.total_registers_used > 0);
}
