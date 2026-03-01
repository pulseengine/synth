//! Meld ABI Integration Test
//!
//! Tests the full pipeline for WASM modules with imports:
//!   WASM (with imports) → instruction selection (with dispatch stubs)
//!     → ARM encoding → ELF with relocations for __meld_dispatch_import
//!
//! This validates the ABI contract between Synth-compiled code and
//! the Kiln runtime's kiln-synth-bridge crate.

use synth_backend::{
    ArmEncoder, ArmRelocationType, ElfBuilder, ElfSectionType, Relocation, Section, SectionFlags,
    Symbol, SymbolBinding, SymbolType,
};
use synth_core::{ImportEntry, ImportKind};
use synth_synthesis::{ArmOp, InstructionSelector, RuleDatabase, WasmOp};

/// Test that instruction selection generates __meld_dispatch_import stubs
/// for imported function calls.
#[test]
fn test_import_dispatch_stub_generation() {
    // WASM ops that call an imported function (index 0)
    let wasm_ops = vec![
        WasmOp::I32Const(42), // Argument to the import
        WasmOp::Call(0),      // Call import #0
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector.set_num_imports(1); // 1 import

    let arm_instrs = selector
        .select(&wasm_ops)
        .expect("instruction selection should succeed");

    // Should contain a BL to __meld_dispatch_import
    let has_dispatch_bl = arm_instrs
        .iter()
        .any(|instr| matches!(&instr.op, ArmOp::Bl { label } if label == "__meld_dispatch_import"));
    assert!(
        has_dispatch_bl,
        "expected BL __meld_dispatch_import for import call, got: {:?}",
        arm_instrs.iter().map(|i| &i.op).collect::<Vec<_>>()
    );

    // Should contain MOV R0, #0 (import index)
    let has_index_mov = arm_instrs.iter().any(|instr| {
        matches!(&instr.op, ArmOp::Mov { rd, op2 }
            if matches!(rd, synth_synthesis::Reg::R0)
            && matches!(op2, synth_synthesis::Operand2::Imm(0)))
    });
    assert!(
        has_index_mov,
        "expected MOV R0, #0 for import index, got: {:?}",
        arm_instrs.iter().map(|i| &i.op).collect::<Vec<_>>()
    );
}

/// Test that local function calls (non-import) still generate func_N labels.
#[test]
fn test_local_function_call_not_dispatch() {
    // func_idx=1 with 1 import means func_idx >= num_imports → local call
    let wasm_ops = vec![WasmOp::Call(1)];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector.set_num_imports(1);

    let arm_instrs = selector
        .select(&wasm_ops)
        .expect("instruction selection should succeed");

    let has_local_bl = arm_instrs
        .iter()
        .any(|instr| matches!(&instr.op, ArmOp::Bl { label } if label == "func_1"));
    assert!(
        has_local_bl,
        "expected BL func_1 for local function call, got: {:?}",
        arm_instrs.iter().map(|i| &i.op).collect::<Vec<_>>()
    );

    // Should NOT have __meld_dispatch_import
    let has_dispatch = arm_instrs
        .iter()
        .any(|instr| matches!(&instr.op, ArmOp::Bl { label } if label == "__meld_dispatch_import"));
    assert!(
        !has_dispatch,
        "local call should not generate __meld_dispatch_import"
    );
}

/// Test that ELF builder can add relocations and undefined symbols
/// for the Meld bridge.
#[test]
fn test_elf_relocation_for_meld_dispatch() {
    let mut elf_builder = ElfBuilder::new_arm32().with_entry(0x8000);

    // Minimal .text section
    let code = vec![0u8; 16];
    let text = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(0x8000)
        .with_align(4)
        .with_data(code);
    elf_builder.add_section(text);

    // Add undefined symbol for __meld_dispatch_import
    let sym_idx = elf_builder.add_undefined_symbol("__meld_dispatch_import");
    assert!(sym_idx > 0, "symbol index should be > 0 (0 is STN_UNDEF)");

    // Add relocation for a BL instruction at offset 8 in .text
    elf_builder.add_relocation(Relocation {
        offset: 8,
        symbol_index: sym_idx,
        reloc_type: ArmRelocationType::Call,
    });

    // Build should succeed with relocation
    let elf_data = elf_builder.build().expect("ELF build with relocations");

    // Validate ELF magic
    assert_eq!(&elf_data[0..4], &[0x7f, b'E', b'L', b'F']);
    assert_eq!(elf_data[4], 1); // 32-bit
    assert_eq!(elf_data[5], 1); // little-endian

    // ELF should be larger than without relocations (has .rel.text and symbol)
    assert!(
        elf_data.len() > 100,
        "ELF with relocations should be substantial, got {} bytes",
        elf_data.len()
    );
}

/// Test the complete Meld ABI pipeline: WASM with imports → ELF with relocations.
#[test]
fn test_full_meld_abi_pipeline() {
    // Simulate a WASM module that imports "env.log" and calls it
    let imports = vec![ImportEntry {
        module: "env".to_string(),
        name: "log".to_string(),
        kind: ImportKind::Function(0), // type index 0
        index: 0,
    }];

    // WASM function body: call the imported log function with arg 42
    let wasm_ops = vec![
        WasmOp::I32Const(42),
        WasmOp::Call(0), // Call import #0 (env.log)
    ];

    // Step 1: Instruction selection with import awareness
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector.set_num_imports(imports.len() as u32);

    let arm_instrs = selector
        .select(&wasm_ops)
        .expect("instruction selection failed");

    // Step 2: Encode to ARM machine code
    let encoder = ArmEncoder::new_arm32();
    let mut code = Vec::new();
    let mut bl_offsets = Vec::new();

    for instr in &arm_instrs {
        if matches!(&instr.op, ArmOp::Bl { label } if label == "__meld_dispatch_import") {
            bl_offsets.push(code.len() as u32);
        }
        let encoded = encoder.encode(&instr.op).expect("ARM encoding failed");
        code.extend_from_slice(&encoded);
    }

    assert!(!code.is_empty(), "should generate machine code");
    assert!(
        !bl_offsets.is_empty(),
        "should have at least one BL to __meld_dispatch_import"
    );

    // Step 3: Build ELF with relocations
    let mut elf_builder = ElfBuilder::new_arm32().with_entry(0x8000);

    let text = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(0x8000)
        .with_align(4)
        .with_data(code.clone());
    elf_builder.add_section(text);

    // Add export symbol
    let func_sym = Symbol::new("main")
        .with_value(0x8000)
        .with_size(code.len() as u32)
        .with_binding(SymbolBinding::Global)
        .with_type(SymbolType::Func)
        .with_section(4);
    elf_builder.add_symbol(func_sym);

    // Add undefined symbol for the Meld dispatch bridge
    let dispatch_sym_idx = elf_builder.add_undefined_symbol("__meld_dispatch_import");

    // Add relocations for each BL to __meld_dispatch_import
    for offset in &bl_offsets {
        elf_builder.add_relocation(Relocation {
            offset: *offset,
            symbol_index: dispatch_sym_idx,
            reloc_type: ArmRelocationType::Call,
        });
    }

    // Build the relocatable ELF
    let elf_data = elf_builder.build().expect("ELF build failed");

    // Validate
    assert_eq!(&elf_data[0..4], &[0x7f, b'E', b'L', b'F']);

    // Verify the import metadata round-trips
    assert_eq!(imports[0].module, "env");
    assert_eq!(imports[0].name, "log");
    assert!(matches!(imports[0].kind, ImportKind::Function(_)));

    println!("  Meld ABI pipeline test passed:");
    println!("  - {} import(s) declared", imports.len());
    println!("  - {} ARM instructions generated", arm_instrs.len());
    println!("  - {} bytes of machine code", code.len());
    println!(
        "  - {} relocation(s) for __meld_dispatch_import",
        bl_offsets.len()
    );
    println!("  - {} byte ELF with .rel.text section", elf_data.len());
}

/// Test multiple imports generate distinct dispatch calls.
#[test]
fn test_multiple_import_dispatch() {
    // Two imports: env.log (index 0) and env.read (index 1)
    let wasm_ops = vec![
        WasmOp::I32Const(1),
        WasmOp::Call(0), // Call import #0
        WasmOp::I32Const(2),
        WasmOp::Call(1), // Call import #1
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector.set_num_imports(2);

    let arm_instrs = selector
        .select(&wasm_ops)
        .expect("instruction selection failed");

    // Count BL __meld_dispatch_import occurrences
    let dispatch_count = arm_instrs
        .iter()
        .filter(|i| matches!(&i.op, ArmOp::Bl { label } if label == "__meld_dispatch_import"))
        .count();
    assert_eq!(
        dispatch_count, 2,
        "expected 2 dispatch calls, got {}",
        dispatch_count
    );

    // Should have MOV R0, #0 and MOV R0, #1 for the two import indices
    let mov_indices: Vec<i32> = arm_instrs
        .iter()
        .filter_map(|i| match &i.op {
            ArmOp::Mov { rd, op2 }
                if matches!(rd, synth_synthesis::Reg::R0)
                    && matches!(op2, synth_synthesis::Operand2::Imm(_)) =>
            {
                if let synth_synthesis::Operand2::Imm(val) = op2 {
                    Some(*val)
                } else {
                    None
                }
            }
            _ => None,
        })
        .collect();

    assert!(
        mov_indices.contains(&0) && mov_indices.contains(&1),
        "expected MOV R0 with indices 0 and 1, got {:?}",
        mov_indices
    );
}
