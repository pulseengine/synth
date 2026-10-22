//! RQ-89-RELOCSINGLE (#1565) — `--relocatable` on the ARM single-function path.
//!
//! The defect: `synth compile m.wasm -t cortex-m4 -n a --relocatable -o a.o`
//! exited 0 and wrote an ET_EXEC image with its own `Reset_Handler`,
//! byte-identical to the same command WITHOUT `--relocatable` — an artifact no
//! host linker accepts as input (`cannot use executable file as input to a
//! link`), while `--all-exports --relocatable` on the same module correctly
//! wrote ET_REL. aarch64 and RV32 already honoured the flag on both paths.
//!
//! The fix HONOURS the flag: the request is rerouted onto the module path
//! restricted to the one requested root, so the object is what
//! `--all-exports --relocatable` emits for that function. This test pins:
//!
//!   * ET_REL, no `Reset_Handler`, the export symbol a DEFINED global FUNC,
//!     the other exports ABSENT — on cortex-m3/m4/m7 (Thumb-2) and cortex-r5
//!     (A32, whose single-function builder was ET_EXEC too), for `-n` and
//!     `--func-index`;
//!   * the export's bytes EQUAL its bytes in the `--all-exports --relocatable`
//!     object (same direct selector, #197 — the single-function self-contained
//!     path uses a different one, so wrapping its bytes would not match);
//!   * a non-exported callee is pulled into the object (#235 closure) and no
//!     symbol is left undefined;
//!   * the loud refusals for the shapes that cannot be honoured (a
//!     non-exported `--func-index` root, a built-in demo);
//!   * the negative control: WITHOUT `--relocatable` the single-function
//!     output is still the self-contained ET_EXEC image.
//!
//! Red against the pre-fix binary (every ET_REL assertion reads ET_EXEC and
//! finds `Reset_Handler`; both refusals exit 0). Link-and-execute evidence
//! (`a(41) == 42` under unicorn after a real `arm-none-eabi-ld` link) lives in
//! scripts/repro/relocatable_single_function_1565_differential.py.

use object::read::elf::ElfFile32;
use object::{Object, ObjectSection, ObjectSymbol, SymbolKind};
use std::path::{Path, PathBuf};
use std::process::Command;

const TWO_EXPORTS: &str = r#"(module
  (func (export "a") (param i32) (result i32) (i32.add (local.get 0) (i32.const 1)))
  (func (export "b") (param i32) (result i32) (i32.mul (local.get 0) (i32.const 2))))
"#;

/// `entry` calls a NON-exported helper; `other` is an unrelated export.
const WITH_HELPER: &str = r#"(module
  (func $helper (param i32) (result i32) (i32.mul (local.get 0) (i32.const 3)))
  (func (export "entry") (param i32) (result i32)
    (i32.add (call $helper (local.get 0)) (i32.const 5)))
  (func (export "other") (param i32) (result i32) (i32.sub (local.get 0) (i32.const 1))))
"#;

const ET_EXEC: u16 = 2;
const ET_REL: u16 = 1;

fn workdir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("synth-1565-{}-{tag}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn write_wat(dir: &Path, text: &str) -> PathBuf {
    let p = dir.join("m.wat");
    std::fs::write(&p, text).unwrap();
    p
}

/// Run `synth compile <args>`; return (success, combined output).
fn synth(args: &[&str]) -> (bool, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_synth"))
        .arg("compile")
        .args(args)
        .output()
        .expect("run synth");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stderr).into_owned() + &String::from_utf8_lossy(&out.stdout),
    )
}

fn compile(input: &Path, out: &Path, flags: &[&str]) -> Vec<u8> {
    let mut args = vec![input.to_str().unwrap(), "-o", out.to_str().unwrap()];
    args.extend_from_slice(flags);
    let (ok, text) = synth(&args);
    assert!(ok, "synth compile {flags:?} failed: {text}");
    std::fs::read(out).unwrap()
}

fn e_type(data: &[u8]) -> u16 {
    u16::from_le_bytes([data[16], data[17]])
}

/// (name, defined, global, kind) for every named symbol.
fn symbols(data: &[u8]) -> Vec<(String, bool, bool, SymbolKind)> {
    let obj = ElfFile32::<object::Endianness>::parse(data).expect("parse ELF");
    obj.symbols()
        .filter_map(|s| {
            let n = s.name().ok()?.to_string();
            (!n.is_empty()).then(|| (n, !s.is_undefined(), s.is_global(), s.kind()))
        })
        .collect()
}

/// The bytes a defined FUNC symbol covers in its section (Thumb bit masked).
fn func_bytes(data: &[u8], name: &str) -> Vec<u8> {
    let obj = ElfFile32::<object::Endianness>::parse(data).expect("parse ELF");
    let sym = obj
        .symbols()
        .find(|s| s.name() == Ok(name))
        .unwrap_or_else(|| panic!("symbol {name} missing"));
    let sec = obj
        .section_by_index(sym.section_index().expect("defined"))
        .unwrap();
    let base = sec.address();
    let off = ((sym.address() & !1) - base) as usize;
    sec.data().unwrap()[off..off + sym.size() as usize].to_vec()
}

fn assert_relocatable_object_for(data: &[u8], want: &str, absent: &[&str], ctx: &str) {
    assert_eq!(
        e_type(data),
        ET_REL,
        "#1565 {ctx}: --relocatable must write ET_REL (1), got e_type {}",
        e_type(data)
    );
    let syms = symbols(data);
    assert!(
        !syms.iter().any(|s| s.0 == "Reset_Handler"),
        "#1565 {ctx}: a relocatable object must carry no Reset_Handler: {syms:?}"
    );
    assert!(
        syms.iter()
            .any(|s| s.0 == want && s.1 && s.2 && s.3 == SymbolKind::Text),
        "#1565 {ctx}: `{want}` must be a DEFINED GLOBAL FUNC: {syms:?}"
    );
    for a in absent {
        assert!(
            !syms.iter().any(|s| s.0 == *a),
            "#1565 {ctx}: only the requested root's closure ships; `{a}` must be absent: {syms:?}"
        );
    }
    assert!(
        syms.iter().all(|s| s.1),
        "#1565 {ctx}: no undefined symbol may remain: {syms:?}"
    );
}

#[test]
fn single_function_relocatable_is_et_rel_on_every_arm_target_1565() {
    let dir = workdir("targets");
    let wat = write_wat(&dir, TWO_EXPORTS);
    for target in ["cortex-m3", "cortex-m4", "cortex-m7", "cortex-r5"] {
        let single = compile(
            &wat,
            &dir.join(format!("{target}_a.o")),
            &["-t", target, "-n", "a", "--relocatable"],
        );
        assert_relocatable_object_for(&single, "a", &["b"], &format!("{target} -n a"));

        let by_index = compile(
            &wat,
            &dir.join(format!("{target}_i1.o")),
            &["-t", target, "--func-index", "1", "--relocatable"],
        );
        assert_relocatable_object_for(&by_index, "b", &["a"], &format!("{target} --func-index 1"));

        // Consistent with the module path: the export's code is the code
        // `--all-exports --relocatable` emits for it.
        let all = compile(
            &wat,
            &dir.join(format!("{target}_all.o")),
            &["-t", target, "--all-exports", "--relocatable"],
        );
        assert_eq!(e_type(&all), ET_REL);
        assert_eq!(
            func_bytes(&single, "a"),
            func_bytes(&all, "a"),
            "#1565 {target}: `a` must be the bytes the --all-exports --relocatable object carries"
        );
        assert_eq!(func_bytes(&by_index, "b"), func_bytes(&all, "b"));
    }
}

#[test]
fn single_function_relocatable_pulls_in_its_non_exported_callee_1565() {
    let dir = workdir("helper");
    let wat = write_wat(&dir, WITH_HELPER);
    let data = compile(
        &wat,
        &dir.join("entry.o"),
        &["-t", "cortex-m4", "-n", "entry", "--relocatable"],
    );
    assert_relocatable_object_for(&data, "entry", &["other"], "-n entry (calls $helper)");
    // $helper is function 0: its body must be IN the object (#235 closure),
    // so the BL from `entry` resolves inside the object (no undefined symbol,
    // asserted above).
    let syms = symbols(&data);
    assert!(
        syms.iter().any(|s| s.0 == "func_0" && s.1),
        "#1565: the non-exported callee must ship in the object: {syms:?}"
    );
}

#[test]
fn non_exported_func_index_with_relocatable_is_refused_loudly_1565() {
    let dir = workdir("nonexported");
    let wat = write_wat(&dir, WITH_HELPER);
    let out = dir.join("helper.o");
    let (ok, text) = synth(&[
        wat.to_str().unwrap(),
        "-o",
        out.to_str().unwrap(),
        "-t",
        "cortex-m4",
        "--func-index",
        "0",
        "--relocatable",
    ]);
    assert!(
        !ok,
        "#1565: a non-exported root cannot be honoured relocatably and must fail: {text}"
    );
    assert!(
        text.contains("#1565") && text.contains("not exported"),
        "#1565: expected the explicit refusal, got: {text}"
    );
    assert!(
        !out.exists(),
        "#1565: a refused compile must write no object"
    );
}

#[test]
fn demo_with_relocatable_is_refused_loudly_1565() {
    let dir = workdir("demo");
    let out = dir.join("demo.o");
    let (ok, text) = synth(&[
        "--demo",
        "add",
        "-o",
        out.to_str().unwrap(),
        "-t",
        "cortex-m4",
        "--relocatable",
    ]);
    assert!(!ok, "#1565: --demo --relocatable must fail: {text}");
    assert!(
        text.contains("#1565") && text.contains("--relocatable"),
        "#1565: expected the explicit refusal, got: {text}"
    );
}

/// Negative control: the flag is the ONLY trigger. Without it the
/// single-function path still writes the self-contained image.
#[test]
fn single_function_without_relocatable_is_still_self_contained_1565() {
    let dir = workdir("control");
    let wat = write_wat(&dir, TWO_EXPORTS);
    let data = compile(&wat, &dir.join("a.elf"), &["-t", "cortex-m4", "-n", "a"]);
    assert_eq!(e_type(&data), ET_EXEC);
    assert!(symbols(&data).iter().any(|s| s.0 == "Reset_Handler"));
}
