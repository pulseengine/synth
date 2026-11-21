//! Import call boundary — selector and ELF-builder level.
//!
//! An imported function is called ONE way: a direct AAPCS call, `BL func_N`
//! (rewritten to the bare wasm field name by the relocatable ELF builder), on
//! a host-linked (`relocatable`) compile. The legacy Meld dispatch lowering
//! (`MOV R0, #index; BL __meld_dispatch_import`) passed the import index and
//! none of the wasm arguments (#1699) and is gone: a compile for the
//! self-contained image declines an import call loudly instead.
//!
//! The executed proof is `crates/synth-oracle/tests/import_boundary_oracle.rs`;
//! these tests pin the lowering's shape at the API the backends call.

use synth_backend::{
    ArmEncoder, ArmRelocationType, ElfBuilder, ElfSectionType, Relocation, Section, SectionFlags,
    Symbol, SymbolBinding, SymbolType,
};
use synth_core::{ImportEntry, ImportKind};
use synth_synthesis::{ArmOp, InstructionSelector, RuleDatabase, WasmOp};

fn bl_labels(instrs: &[synth_synthesis::ArmInstruction]) -> Vec<String> {
    instrs
        .iter()
        .filter_map(|i| {
            if let ArmOp::Bl { label } = &i.op {
                Some(label.clone())
            } else {
                None
            }
        })
        .collect()
}

/// #1699: without the host-link configuration there is no way to call an
/// import, and neither selector entry point emits one — a loud decline, never
/// the dispatch stub.
#[test]
fn test_import_call_without_host_link_declines_1699() {
    let wasm_ops = vec![
        WasmOp::I32Const(42), // Argument to the import
        WasmOp::Call(0),      // Call import #0
    ];
    let db = RuleDatabase::with_standard_rules();

    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector.set_num_imports(1);
    selector.set_func_arg_counts(vec![1], Vec::new());
    let err = selector
        .select_with_stack(&wasm_ops, 0)
        .expect_err("a self-contained compile must decline an import call");
    assert!(err.to_string().contains("#1699"), "{err}");

    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector.set_num_imports(1);
    let err = selector
        .select(&wasm_ops)
        .expect_err("select_default has no import call lowering");
    assert!(err.to_string().contains("#1699"), "{err}");
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
/// for an import the host linker resolves.
#[test]
fn test_elf_relocation_for_an_import_symbol() {
    let mut elf_builder = ElfBuilder::new_arm32().with_entry(0x8000);

    // Minimal .text section
    let code = vec![0u8; 16];
    let text = Section::new(".text", ElfSectionType::ProgBits)
        .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
        .with_addr(0x8000)
        .with_align(4)
        .with_data(code);
    elf_builder.add_section(text);

    // Add an undefined symbol for the import, under its field name
    let sym_idx = elf_builder.add_undefined_symbol("log");
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

/// The complete pipeline: WASM with an import → direct AAPCS call → ELF with
/// a relocation against the import's own symbol.
#[test]
fn test_full_import_call_pipeline() {
    // A WASM module that imports "env.log" and calls it.
    let imports = [ImportEntry {
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

    // Step 1: host-linked instruction selection
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector.set_num_imports(imports.len() as u32);
    selector.set_func_arg_counts(vec![1], Vec::new());
    selector.set_func_result_counts(vec![0]);
    selector.set_relocatable(true);

    let arm_instrs = selector
        .select_with_stack(&wasm_ops, 0)
        .expect("instruction selection failed");
    assert_eq!(
        bl_labels(&arm_instrs),
        vec!["func_0".to_string()],
        "one direct call, no dispatch stub"
    );

    // Step 2: Encode to ARM machine code
    let encoder = ArmEncoder::new_arm32();
    let mut code = Vec::new();
    let mut bl_offsets = Vec::new();

    for instr in &arm_instrs {
        if matches!(&instr.op, ArmOp::Bl { .. }) {
            bl_offsets.push(code.len() as u32);
        }
        let encoded = encoder.encode(&instr.op).expect("ARM encoding failed");
        code.extend_from_slice(&encoded);
    }

    assert!(!code.is_empty(), "should generate machine code");
    assert_eq!(bl_offsets.len(), 1);

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

    // The import is an undefined symbol under its BARE field name.
    let import_sym_idx = elf_builder.add_undefined_symbol(&imports[0].name);

    for offset in &bl_offsets {
        elf_builder.add_relocation(Relocation {
            offset: *offset,
            symbol_index: import_sym_idx,
            reloc_type: ArmRelocationType::Call,
        });
    }

    // Build the relocatable ELF
    let elf_data = elf_builder.build().expect("ELF build failed");

    // Validate
    assert_eq!(&elf_data[0..4], &[0x7f, b'E', b'L', b'F']);
    assert!(
        !elf_data
            .windows(b"__meld_dispatch_import".len())
            .any(|w| w == b"__meld_dispatch_import"),
        "no dispatch symbol"
    );
    assert!(matches!(imports[0].kind, ImportKind::Function(_)));
}

/// Two imports are two direct calls, each to its own symbol, with the
/// argument in R0 — never an import index.
#[test]
fn test_multiple_imports_are_direct_calls() {
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
    selector.set_func_arg_counts(vec![1, 1], Vec::new());
    selector.set_func_result_counts(vec![0, 0]);
    selector.set_relocatable(true);

    let arm_instrs = selector
        .select_with_stack(&wasm_ops, 0)
        .expect("instruction selection failed");

    assert_eq!(
        bl_labels(&arm_instrs),
        vec!["func_0".to_string(), "func_1".to_string()]
    );
}
