//! Minimal Demo: Compile WASM add function to ARM ELF
//!
//! This demonstrates the working compilation pipeline:
//! WASM ops -> ARM instructions -> Binary -> ELF
//!
//! Run with: cargo run --example compile_add

use std::fs::File;
use std::io::Write;

use synth_backend::{
    ArmEncoder, ElfBuilder, ElfSectionType, Section, SectionFlags, Symbol, SymbolBinding,
    SymbolType,
};
use synth_synthesis::{InstructionSelector, RuleDatabase, WasmOp};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Synth Minimal Demo: WASM -> ARM ELF ===\n");

    // Step 1: Define WASM operations for add(a, b) function
    // Equivalent to: (func (param $a i32) (param $b i32) (result i32)
    //                  local.get $a
    //                  local.get $b
    //                  i32.add)
    let wasm_ops = vec![
        WasmOp::LocalGet(0), // Load param a
        WasmOp::LocalGet(1), // Load param b
        WasmOp::I32Add,      // Add them
    ];

    println!("Step 1: WASM Operations");
    println!("  Input: add(a, b) = a + b");
    println!("  WASM ops: {:?}\n", wasm_ops);

    // Step 2: Select ARM instructions
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops)?;

    println!("Step 2: ARM Instruction Selection");
    println!("  Generated {} ARM instructions:", arm_instrs.len());
    for (i, instr) in arm_instrs.iter().enumerate() {
        println!("    {}: {:?}", i, instr.op);
    }
    println!();

    // Step 3: Encode to ARM binary
    let encoder = ArmEncoder::new_arm32();
    let mut code = Vec::new();

    for instr in &arm_instrs {
        let encoded = encoder.encode(&instr.op)?;
        code.extend_from_slice(&encoded);
    }

    println!("Step 3: ARM Binary Encoding");
    println!("  Generated {} bytes of machine code", code.len());
    print!("  Hex: ");
    for byte in &code {
        print!("{:02x} ", byte);
    }
    println!("\n");

    // Step 4: Build ELF file
    let mut elf_builder = ElfBuilder::new_arm32().with_entry(0x8000);

    // Add .text section with code
    let text_section = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(0x8000)
        .with_align(4)
        .with_data(code.clone());

    elf_builder.add_section(text_section);

    // Add function symbol
    let add_sym = Symbol::new("add")
        .with_value(0x8000)
        .with_size(code.len() as u32)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(4);

    elf_builder.add_symbol(add_sym);

    // Build ELF
    let elf_data = elf_builder.build()?;

    println!("Step 4: ELF Generation");
    println!("  ELF size: {} bytes", elf_data.len());
    println!("  Entry point: 0x8000");

    // Verify ELF header
    assert_eq!(&elf_data[0..4], &[0x7f, b'E', b'L', b'F'], "Invalid ELF magic");
    println!("  ELF magic: valid");

    // Step 5: Write to file
    let output_path = "add.elf";
    let mut file = File::create(output_path)?;
    file.write_all(&elf_data)?;

    println!("\nStep 5: Output");
    println!("  Written to: {}", output_path);
    println!("\n=== Compilation successful! ===");
    println!("\nTo inspect: arm-none-eabi-objdump -d {}", output_path);

    Ok(())
}
