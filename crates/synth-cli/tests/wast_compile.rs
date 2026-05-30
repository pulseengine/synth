//! Integration tests: compile every WAST file through synth and verify ELF output.
//!
//! This tests the full pipeline: WAST → parse → decode → instruction select → encode → ELF.
//! Each WAST file in tests/wast/ is compiled with --all-exports --cortex-m.

use std::path::{Path, PathBuf};
use std::process::Command;

fn synth_binary() -> PathBuf {
    // cargo sets this for integration tests
    let mut path = std::env::current_exe()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    path.push("synth");
    path
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn wast_dir() -> PathBuf {
    workspace_root().join("tests").join("wast")
}

/// Compile a single WAST file and assert success
fn compile_wast(wast_file: &Path) -> PathBuf {
    let stem = wast_file.file_stem().unwrap().to_str().unwrap();
    let output = std::env::temp_dir().join(format!("synth_test_{}.elf", stem));

    let result = Command::new(synth_binary())
        .args([
            "compile",
            wast_file.to_str().unwrap(),
            "--all-exports",
            "--cortex-m",
            "-o",
            output.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run synth binary");

    let stdout = String::from_utf8_lossy(&result.stdout);
    let stderr = String::from_utf8_lossy(&result.stderr);

    assert!(
        result.status.success(),
        "synth compile failed for {}:\nstdout: {}\nstderr: {}",
        wast_file.display(),
        stdout,
        stderr,
    );

    // Verify the output file exists and looks like an ELF
    assert!(
        output.exists(),
        "Output ELF not created: {}",
        output.display()
    );
    let data = std::fs::read(&output).unwrap();
    assert!(data.len() > 52, "ELF file too small: {} bytes", data.len());
    assert_eq!(&data[0..4], b"\x7fELF", "Not a valid ELF file");

    // Check it's ARM (e_machine = 0x28 = 40)
    assert_eq!(data[18], 0x28, "Not an ARM ELF (e_machine)");

    output
}

// --- Individual WAST file compile tests ---

#[test]
fn compile_i32_arithmetic() {
    compile_wast(&wast_dir().join("i32_arithmetic.wast"));
}

#[test]
fn compile_i32_compare() {
    compile_wast(&wast_dir().join("i32_compare.wast"));
}

#[test]
fn compile_i32_eq_simple() {
    compile_wast(&wast_dir().join("i32_eq_simple.wast"));
}

#[test]
fn compile_i32_shift() {
    compile_wast(&wast_dir().join("i32_shift.wast"));
}

#[test]
fn compile_i32_rotate() {
    compile_wast(&wast_dir().join("i32_rotate.wast"));
}

#[test]
fn compile_i32_bitcount() {
    compile_wast(&wast_dir().join("i32_bitcount.wast"));
}

#[test]
fn compile_i32_div() {
    compile_wast(&wast_dir().join("i32_div.wast"));
}

#[test]
fn compile_i32_rem() {
    compile_wast(&wast_dir().join("i32_rem.wast"));
}

#[test]
fn compile_i32_memory() {
    compile_wast(&wast_dir().join("i32_memory.wast"));
}

#[test]
fn compile_control_select() {
    compile_wast(&wast_dir().join("control_select.wast"));
}

#[test]
fn compile_control_if() {
    compile_wast(&wast_dir().join("control_if.wast"));
}

#[test]
fn compile_control_loop() {
    compile_wast(&wast_dir().join("control_loop.wast"));
}

#[test]
fn compile_control_nested_select() {
    compile_wast(&wast_dir().join("control_nested_select.wast"));
}

#[test]
fn compile_control_br_if_select() {
    compile_wast(&wast_dir().join("control_br_if_select.wast"));
}

#[test]
fn compile_control_nested_loop() {
    compile_wast(&wast_dir().join("control_nested_loop.wast"));
}

#[test]
fn compile_control_factorial() {
    compile_wast(&wast_dir().join("control_factorial.wast"));
}

#[test]
fn compile_control_loop_if() {
    compile_wast(&wast_dir().join("control_loop_if.wast"));
}

#[test]
fn compile_i64_arithmetic() {
    compile_wast(&wast_dir().join("i64_arithmetic.wast"));
}

#[test]
fn compile_i64_compare() {
    compile_wast(&wast_dir().join("i64_compare.wast"));
}

#[test]
fn compile_i64_shift() {
    compile_wast(&wast_dir().join("i64_shift.wast"));
}

#[test]
fn compile_i64_mul() {
    compile_wast(&wast_dir().join("i64_mul.wast"));
}

#[test]
fn compile_i64_div() {
    compile_wast(&wast_dir().join("i64_div.wast"));
}

/// M3 Static Linking PoC: compile a WAT module with an import and verify
/// that the output is a relocatable ELF with:
///   - ET_REL file type
///   - __meld_dispatch_import as an undefined symbol
///   - .rel.text section with R_ARM_CALL relocations
///   - .meld_import_table metadata section
///   - call_log function symbol
#[test]
fn compile_import_call_produces_relocatable_elf() {
    let wat = workspace_root()
        .join("tests")
        .join("integration")
        .join("import_call.wat");

    assert!(wat.exists(), "import_call.wat not found: {}", wat.display());

    let output = std::env::temp_dir().join("synth_test_import_call.o");

    let result = Command::new(synth_binary())
        .args([
            "compile",
            wat.to_str().unwrap(),
            "--no-optimize",
            "-o",
            output.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run synth binary");

    let stdout = String::from_utf8_lossy(&result.stdout);
    let stderr = String::from_utf8_lossy(&result.stderr);

    assert!(
        result.status.success(),
        "synth compile failed:\nstdout: {}\nstderr: {}",
        stdout,
        stderr,
    );

    let data = std::fs::read(&output).unwrap();

    // ELF magic
    assert_eq!(&data[0..4], b"\x7fELF", "Not a valid ELF file");

    // 32-bit, little-endian
    assert_eq!(data[4], 1, "Expected 32-bit ELF");
    assert_eq!(data[5], 1, "Expected little-endian ELF");

    // ET_REL (e_type = 1, at offset 16, 2 bytes LE)
    let e_type = u16::from_le_bytes([data[16], data[17]]);
    assert_eq!(e_type, 1, "Expected ET_REL (1), got {}", e_type);

    // ARM architecture (e_machine = 0x28 at offset 18)
    assert_eq!(data[18], 0x28, "Expected ARM architecture");

    // Check that __meld_dispatch_import is in the string table
    let meld_sym = b"__meld_dispatch_import";
    let has_meld_sym = data
        .windows(meld_sym.len())
        .any(|w| w == meld_sym.as_slice());
    assert!(
        has_meld_sym,
        "__meld_dispatch_import symbol not found in ELF"
    );

    // Check that call_log function name is in the string table
    let call_log = b"call_log";
    let has_call_log = data
        .windows(call_log.len())
        .any(|w| w == call_log.as_slice());
    assert!(has_call_log, "call_log function symbol not found in ELF");

    // Check for .rel.text section name
    let rel_text = b".rel.text";
    let has_rel_text = data
        .windows(rel_text.len())
        .any(|w| w == rel_text.as_slice());
    assert!(has_rel_text, ".rel.text section not found in ELF");

    // Check for .meld_import_table section name
    let import_table = b".meld_import_table";
    let has_import_table = data
        .windows(import_table.len())
        .any(|w| w == import_table.as_slice());
    assert!(
        has_import_table,
        ".meld_import_table section not found in ELF"
    );

    // Check that the import metadata contains "env" and "log"
    let has_env = data.windows(3).any(|w| w == b"env");
    assert!(has_env, "Import module name 'env' not found in metadata");

    // Verify stdout mentions relocations
    assert!(
        stdout.contains("Relocations:") || stdout.contains("relocatable"),
        "Output should mention relocations:\n{}",
        stdout
    );
}

/// PR #86 patch coverage: --relocatable flag must force ET_REL output even
/// when the wasm has no imports (so no implicit relocations would be
/// emitted). Uses an existing import-free WAST file from the suite.
#[test]
fn compile_with_relocatable_flag_forces_et_rel() {
    let wast_file = wast_dir().join("i32_arithmetic.wast");
    assert!(wast_file.exists(), "i32_arithmetic.wast missing");
    let output = std::env::temp_dir().join("synth_test_relocatable.o");

    let result = Command::new(synth_binary())
        .args([
            "compile",
            wast_file.to_str().unwrap(),
            "--all-exports",
            "--cortex-m",
            "--relocatable",
            "-o",
            output.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run synth binary");

    let stderr = String::from_utf8_lossy(&result.stderr);
    let stdout = String::from_utf8_lossy(&result.stdout);
    assert!(
        result.status.success(),
        "synth compile --relocatable failed:\nstdout: {}\nstderr: {}",
        stdout,
        stderr,
    );
    assert!(output.exists(), "output not created");

    let data = std::fs::read(&output).unwrap();
    assert_eq!(&data[0..4], b"\x7fELF", "not an ELF");
    // ET_REL == 1
    let e_type = u16::from_le_bytes([data[16], data[17]]);
    assert_eq!(
        e_type, 1,
        "--relocatable should produce ET_REL (1), got {}",
        e_type
    );
}

/// PR #86 patch coverage: without --relocatable, an import-free wasm should
/// still produce ET_EXEC. This is the negative case to make sure we haven't
/// silently changed default behaviour.
#[test]
fn compile_without_relocatable_flag_produces_et_exec_for_no_imports() {
    let wast_file = wast_dir().join("i32_arithmetic.wast");
    let output = std::env::temp_dir().join("synth_test_no_relocatable.elf");

    let result = Command::new(synth_binary())
        .args([
            "compile",
            wast_file.to_str().unwrap(),
            "--all-exports",
            "--cortex-m",
            "-o",
            output.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run synth binary");

    assert!(
        result.status.success(),
        "default compile (no --relocatable) failed: stderr={}",
        String::from_utf8_lossy(&result.stderr),
    );
    let data = std::fs::read(&output).unwrap();
    let e_type = u16::from_le_bytes([data[16], data[17]]);
    assert_eq!(
        e_type, 2,
        "default (no --relocatable, no imports) should be ET_EXEC (2)"
    );
}

/// Verify that all expected WAST files exist (catch typos/renames)
#[test]
fn all_wast_files_present() {
    let dir = wast_dir();
    assert!(
        dir.exists(),
        "WAST test directory missing: {}",
        dir.display()
    );

    let files: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "wast"))
        .collect();

    assert!(
        files.len() >= 20,
        "Expected at least 20 WAST files, found {}",
        files.len()
    );
}

/// Regression test for #167: a module with an INTERNAL call (no imports)
/// must compile to a relocatable object whose internal call carries an
/// `R_ARM_THM_CALL` relocation against the callee's `func_{index}` symbol —
/// i.e. it is actually linkable. Before the fix, internal calls produced
/// neither a relocation nor a `func_N` symbol (the object was non-linkable:
/// the call was a `bl #0` placeholder branching to a garbage address).
#[test]
fn compile_internal_call_is_linkable_167() {
    use object::{Object, ObjectSection, ObjectSymbol};

    let wat = workspace_root()
        .join("tests")
        .join("integration")
        .join("internal_call.wat");
    assert!(
        wat.exists(),
        "internal_call.wat not found: {}",
        wat.display()
    );

    let output = std::env::temp_dir().join("synth_test_internal_call.o");
    let result = Command::new(synth_binary())
        .args([
            "compile",
            wat.to_str().unwrap(),
            "--target",
            "cortex-m4f",
            "--all-exports",
            "--relocatable",
            "-o",
            output.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run synth binary");
    assert!(
        result.status.success(),
        "synth compile failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr),
    );

    let data = std::fs::read(&output).unwrap();
    let elf = object::File::parse(&*data).expect("parse ARM ELF object");

    // A `func_0` symbol must be defined so internal `BL func_0` resolves.
    let has_func_sym = elf.symbols().any(|s| s.name() == Ok("func_0"));
    assert!(
        has_func_sym,
        "internal call target symbol `func_0` not defined in the object (#167)"
    );

    // The internal call must carry an R_ARM_THM_CALL (10) relocation — NOT
    // R_ARM_CALL (28, ARM mode), and not be absent entirely.
    const R_ARM_THM_CALL: u32 = 10;
    let mut thm_call_relocs = 0usize;
    for section in elf.sections() {
        for (_off, reloc) in section.relocations() {
            if let object::RelocationFlags::Elf { r_type } = reloc.flags()
                && r_type == R_ARM_THM_CALL
            {
                thm_call_relocs += 1;
            }
        }
    }
    assert!(
        thm_call_relocs >= 1,
        "expected at least one R_ARM_THM_CALL relocation for the internal call (#167), found {}",
        thm_call_relocs
    );

    // #174: the BL placeholder must carry a -4 addend (`ff f7 fe ff`, the bytes
    // gas emits for a relocatable `bl`) so the relocation nets to S, not S+4.
    // A 0xF800 placeholder (`00 f0 00 f8`) would land one instruction late.
    let text = elf
        .section_by_name(".text")
        .and_then(|s| s.data().ok())
        .expect(".text section");
    let correct_placeholder = [0xFF, 0xF7, 0xFE, 0xFF];
    let bad_placeholder = [0x00, 0xF0, 0x00, 0xF8];
    assert!(
        text.windows(4).any(|w| w == correct_placeholder),
        "compiled .text must contain the -4 BL placeholder ff f7 fe ff (#174)"
    );
    assert!(
        !text.windows(4).any(|w| w == bad_placeholder),
        "compiled .text must not contain the S+4 BL placeholder 00 f0 00 f8 (#174)"
    );

    let _ = std::fs::remove_file(&output);
}

/// Regression test for #173: a call to a wasm IMPORT must relocate against the
/// import's field name (e.g. `host_fn`), so the object resolves against a real
/// host that defines that symbol — NOT a generic `func_N` the host never
/// defines. synth knows the name (it logs it); it must reach the symbol table.
#[test]
fn compile_import_call_uses_field_name_173() {
    use object::{Object, ObjectSymbol};

    let wat = workspace_root()
        .join("tests")
        .join("integration")
        .join("import_field_name.wat");
    assert!(
        wat.exists(),
        "import_field_name.wat not found: {}",
        wat.display()
    );

    let output = std::env::temp_dir().join("synth_test_import_field_name.o");
    let result = Command::new(synth_binary())
        .args([
            "compile",
            wat.to_str().unwrap(),
            "--target",
            "cortex-m4f",
            "--all-exports",
            "--relocatable",
            "-o",
            output.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run synth binary");
    assert!(
        result.status.success(),
        "synth compile failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr),
    );

    let data = std::fs::read(&output).unwrap();
    let elf = object::File::parse(&*data).expect("parse ARM ELF object");

    // The import's field name must be an UNDEFINED symbol the host resolves.
    let has_field_name = elf
        .symbols()
        .any(|s| s.name() == Ok("host_fn") && s.is_undefined());
    assert!(
        has_field_name,
        "import call must produce an undefined symbol named after the wasm field (`host_fn`) (#173)"
    );

    // And it must NOT name the import as a generic `func_0`.
    let has_generic_import_label = elf
        .symbols()
        .any(|s| s.name() == Ok("func_0") && s.is_undefined());
    assert!(
        !has_generic_import_label,
        "import call must not be left as a generic `func_0` symbol (#173)"
    );

    let _ = std::fs::remove_file(&output);
}

/// Regression test for #178/#180: the optimized (default) path miscompiled a
/// pointer-param `i32.load` — the `add ip, ip, r0` that forms `base + operand`
/// was emitted as the corrupt 16-bit `adds r4, r5, r1` (bytes `6c 18`), because
/// the Thumb encoder used the 16-bit ADD form for the high register R12,
/// overflowing its 3-bit fields and dropping the address operand. Root-cause was
/// the encoder (fixed: high regs → 32-bit ADD.W), NOT a fixed-address fold. The
/// optimized output is now correct AND keeps optimizing (it is no longer
/// declined to `select_with_stack`), so it legitimately differs from
/// `--no-optimize` in instruction selection while computing the same address.
#[test]
fn pointer_deref_optimized_uses_address_operand_178_180() {
    use object::{Object, ObjectSection};

    let wat = workspace_root()
        .join("tests")
        .join("integration")
        .join("ptr_deref.wat");
    assert!(wat.exists(), "ptr_deref.wat not found: {}", wat.display());

    let out = std::env::temp_dir().join("synth_ptr_opt.o");
    let result = Command::new(synth_binary())
        .args([
            "compile",
            wat.to_str().unwrap(),
            "--target",
            "cortex-m4f",
            "--all-exports",
            "--relocatable",
            "-o",
            out.to_str().unwrap(),
        ])
        .output()
        .expect("run synth");
    assert!(
        result.status.success(),
        "compile failed: {}",
        String::from_utf8_lossy(&result.stderr)
    );
    let data = std::fs::read(&out).unwrap();
    let elf = object::File::parse(&*data).expect("parse ELF");
    let text = elf
        .section_by_name(".text")
        .and_then(|s| s.data().ok())
        .expect(".text")
        .to_vec();
    let _ = std::fs::remove_file(&out);

    // The bug signature: corrupt 16-bit `adds r4, r5, r1` = 0x186C = bytes 6C 18.
    // Must be absent — the high-register base+addr ADD must not truncate.
    let corrupt_adds = [0x6c, 0x18];
    assert!(
        !text.windows(2).any(|w| w == corrupt_adds),
        "optimized .text contains the corrupt 16-bit ADDS (operand dropped) — #178/#180 regressed"
    );

    // The fix signature: 32-bit `add.w ip, ip, rN` = EB0C 0Cmm = bytes 0C EB ?? 0C.
    // The address operand is folded into the base via R12, so this must appear.
    let has_add_w_ip = text
        .windows(4)
        .any(|w| w[0] == 0x0c && w[1] == 0xeb && w[3] == 0x0c);
    assert!(
        has_add_w_ip,
        "optimized .text must contain `add.w ip, ip, rN` (base + address operand) — #180"
    );
}
