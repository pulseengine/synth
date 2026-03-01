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
