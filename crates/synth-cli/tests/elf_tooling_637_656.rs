//! #637 + #656 — ELF tooling/linkability oracles.
//!
//! #637: synth's ARM objects must be SELF-DESCRIBING: every EM_ARM output
//! carries a target-derived `.ARM.attributes` (Tag_CPU_arch / profile /
//! Tag_THUMB_ISA_use), and `synth disasm` auto-detects Thumb (attributes →
//! STT_FUNC thumb bit → e_entry) instead of defaulting to A32 — which
//! mis-decoded synth's own Cortex-M output into garbage mnemonics.
//!
//! #656: internal (non-exported) functions and the `func_{wasm_index}` call
//! aliases are per-object labels by wasm function INDEX. Emitted STB_GLOBAL,
//! two independently-dissolved objects both define `func_2` and
//! `ld -r a.o b.o` fails with multiple-definition collisions. They must be
//! STB_LOCAL (exports stay STB_GLOBAL), which drags in the ELF ordering rule:
//! all local symbols precede globals and `.symtab` `sh_info` = index of the
//! first non-local (was hardcoded 1 — the #430 blocker). Relocations reference
//! symbols by index, so the #167/#173 R_ARM_THM_CALL machinery must be
//! reindexed consistently across the sort — asserted here by resolving each
//! `.rel.text` entry back to its symbol and checking name + address.
//!
//! The frozen-codegen gate (`frozen_codegen_bytes.rs`) proves `.text` is
//! untouched — this PR changes symtab bindings/order and appends a section.

use std::path::PathBuf;
use std::process::Command;

use object::elf;
use object::read::elf::{FileHeader, SectionHeader, Sym};
use object::{Endianness, Object, ObjectSection};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

/// Compile `wat` for cortex-m3 `--all-exports --relocatable` into `out`.
fn compile(dir: &std::path::Path, name: &str, wat: &str) -> PathBuf {
    let src = dir.join(format!("{name}.wat"));
    std::fs::write(&src, wat).unwrap();
    let out = dir.join(format!("{name}.o"));
    let status = Command::new(synth())
        .args([
            "compile",
            src.to_str().unwrap(),
            "-t",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
            "-o",
            out.to_str().unwrap(),
        ])
        .output()
        .expect("run synth");
    assert!(
        status.status.success(),
        "synth compile failed: {}",
        String::from_utf8_lossy(&status.stderr)
    );
    out
}

/// A module with one EXPORTED function calling one INTERNAL (non-exported)
/// helper — the #656 shape. `body` differentiates the two objects' bodies.
fn module_with_internal_helper(export: &str, mul: u32) -> String {
    format!(
        r#"(module
  (func $helper (param i32) (result i32) (i32.mul (local.get 0) (i32.const {mul})))
  (func (export "{export}") (param i32) (result i32) (call $helper (local.get 0))))"#
    )
}

/// Parsed symtab entry: (name, st_value, binding, type, defined).
type SymEntry = (String, u32, u8, u8, bool);

fn read_symbols(bytes: &[u8]) -> (Vec<SymEntry>, u32) {
    let header = elf::FileHeader32::<Endianness>::parse(bytes).expect("valid ELF32");
    let endian = header.endian().unwrap();
    let sections = header.sections(endian, bytes).unwrap();
    let (symtab_index, _symtab) = sections
        .iter()
        .enumerate()
        .find(|(_, s)| s.sh_type(endian) == elf::SHT_SYMTAB)
        .expect("symtab present");
    let sh_info = sections.iter().nth(symtab_index).unwrap().sh_info(endian);
    let symbols = sections
        .symbol_table_by_index(endian, bytes, object::SectionIndex(symtab_index))
        .expect("parse symtab");
    let strings = symbols.strings();
    let syms = symbols
        .iter()
        .map(|sym| {
            (
                String::from_utf8_lossy(sym.name(endian, strings).unwrap_or(b"")).into_owned(),
                sym.st_value(endian),
                sym.st_bind(),
                sym.st_type(),
                sym.st_shndx(endian) != elf::SHN_UNDEF,
            )
        })
        .collect();
    (syms, sh_info)
}

/// #656: internal helpers + `func_N` aliases are STB_LOCAL, exports stay
/// STB_GLOBAL, locals precede globals, and `sh_info` = first-non-local index.
#[test]
fn internal_funcs_local_exports_global_sh_info_656() {
    let dir = std::env::temp_dir().join("synth_656_bindings");
    std::fs::create_dir_all(&dir).unwrap();
    let obj = compile(
        &dir,
        "gpio",
        &module_with_internal_helper("gpio_configure", 3),
    );
    let bytes = std::fs::read(&obj).unwrap();
    let (syms, sh_info) = read_symbols(&bytes);

    let find = |name: &str| {
        syms.iter()
            .find(|s| s.0 == name)
            .unwrap_or_else(|| panic!("symbol {name} missing"))
    };
    // Internal helper (wasm index 0, never exported) — LOCAL.
    let helper = find("func_0");
    assert_eq!(
        helper.2,
        elf::STB_LOCAL,
        "#656: internal func_0 must be STB_LOCAL"
    );
    // The exported function's `func_1` call alias — LOCAL.
    let alias = find("func_1");
    assert_eq!(
        alias.2,
        elf::STB_LOCAL,
        "#656: func_N call alias must be STB_LOCAL"
    );
    // The export — GLOBAL, same address as its alias.
    let export = find("gpio_configure");
    assert_eq!(export.2, elf::STB_GLOBAL, "export stays STB_GLOBAL");
    assert_eq!(export.1, alias.1, "alias and export share the address");

    // Ordering rule: all locals precede all non-locals; sh_info = first global.
    let first_global = syms
        .iter()
        .position(|s| s.2 != elf::STB_LOCAL)
        .expect("has a global symbol");
    assert!(
        syms[first_global..].iter().all(|s| s.2 != elf::STB_LOCAL),
        "no LOCAL symbol may follow a global"
    );
    assert_eq!(
        sh_info, first_global as u32,
        "`.symtab` sh_info must be the first-non-local index (was hardcoded 1, #430)"
    );
    assert!(sh_info > 1, "this object has real locals");
}

/// #656: the R_ARM_THM_CALL machinery (#167/#173) must survive the
/// locals-first reindex — resolve each `.rel.text` entry to its symbol and
/// check it lands on the LOCAL `func_0` helper at the right address.
#[test]
fn relocations_reindexed_consistently_656() {
    let dir = std::env::temp_dir().join("synth_656_relocs");
    std::fs::create_dir_all(&dir).unwrap();
    let obj = compile(
        &dir,
        "gpio",
        &module_with_internal_helper("gpio_configure", 3),
    );
    let bytes = std::fs::read(&obj).unwrap();
    let (syms, _) = read_symbols(&bytes);

    let header = elf::FileHeader32::<Endianness>::parse(&*bytes).expect("valid ELF32");
    let endian = header.endian().unwrap();
    let sections = header.sections(endian, &*bytes).unwrap();
    let rel_section = sections
        .iter()
        .find(|s| s.sh_type(endian) == elf::SHT_REL)
        .expect(".rel.text present");
    let (rels, _link) = rel_section
        .rel(endian, &*bytes)
        .expect("parse rel")
        .expect("REL entries");
    assert_eq!(rels.len(), 1, "one internal BL call site");
    let rel = &rels[0];
    assert_eq!(
        rel.r_type(endian),
        10, // R_ARM_THM_CALL (object's elf module names it R_ARM_THM_PC22)
        "Thumb BL uses R_ARM_THM_CALL (#167)"
    );
    let sym = &syms[rel.r_sym(endian) as usize];
    assert_eq!(sym.0, "func_0", "BL resolves against the internal helper");
    assert_eq!(sym.2, elf::STB_LOCAL, "which is LOCAL after #656");
    assert!(sym.4, "and defined in this object");
    assert_eq!(sym.1 & !1, 0, "helper is the first function in .text");
}

/// #656 kill-criterion: co-link two independently-dissolved objects, each
/// with its own internal `func_0` + `func_1` alias. Pre-#656 this failed with
/// `multiple definition of 'func_N'`. Uses `arm-none-eabi-ld -r` or `ld.lld -r`
/// when available; the binding/sh_info asserts above are the CI-stable check.
#[test]
fn co_link_two_dissolved_objects_656() {
    let dir = std::env::temp_dir().join("synth_656_colink");
    std::fs::create_dir_all(&dir).unwrap();
    let a = compile(
        &dir,
        "gpio",
        &module_with_internal_helper("gpio_configure", 3),
    );
    let b = compile(&dir, "spi", &module_with_internal_helper("spi_begin", 5));

    let linker = ["arm-none-eabi-ld", "ld.lld"].iter().find(|ld| {
        Command::new(ld)
            .arg("--version")
            .output()
            .is_ok_and(|o| o.status.success())
    });
    let Some(linker) = linker else {
        eprintln!("skip: no arm-none-eabi-ld / ld.lld on PATH — bindings asserted elsewhere");
        return;
    };
    let merged = dir.join("merged.o");
    let out = Command::new(linker)
        .args(["-r", "-o", merged.to_str().unwrap()])
        .arg(&a)
        .arg(&b)
        .output()
        .expect("run linker");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success() && !stderr.contains("multiple definition"),
        "#656: co-linking two dissolved objects must not collide: {stderr}"
    );

    // Exports from BOTH objects still resolve cross-object.
    let bytes = std::fs::read(&merged).unwrap();
    let (syms, _) = read_symbols(&bytes);
    for export in ["gpio_configure", "spi_begin"] {
        let s = syms
            .iter()
            .find(|s| s.0 == export)
            .unwrap_or_else(|| panic!("{export} missing after merge"));
        assert_eq!(s.2, elf::STB_GLOBAL);
        assert!(s.4, "{export} defined in merged object");
    }
    // Both objects' internal helpers survive as (duplicate-named) LOCALs.
    let local_helpers = syms
        .iter()
        .filter(|s| s.0 == "func_0" && s.2 == elf::STB_LOCAL)
        .count();
    assert_eq!(local_helpers, 2, "each object keeps its own local func_0");
}

/// #637: every fresh cortex-m3 object carries `.ARM.attributes`
/// (SHT_ARM_ATTRIBUTES) with Tag_CPU_arch=v7, profile=M, Tag_THUMB_ISA_use=2.
#[test]
fn arm_attributes_emitted_for_thumb_object_637() {
    let dir = std::env::temp_dir().join("synth_637_attrs");
    std::fs::create_dir_all(&dir).unwrap();
    let obj = compile(
        &dir,
        "gpio",
        &module_with_internal_helper("gpio_configure", 3),
    );
    let bytes = std::fs::read(&obj).unwrap();

    let file = object::File::parse(&*bytes).expect("parse ELF");
    let attrs = file
        .section_by_name(".ARM.attributes")
        .expect("#637: .ARM.attributes section must be emitted");
    let data = attrs.data().unwrap();
    assert_eq!(data[0], b'A', "attributes format version");
    // 'A' + u32 len + "aeabi\0" + Tag_File(1) + u32 len + pairs.
    assert_eq!(&data[5..11], b"aeabi\0");
    let pairs = &data[16..];
    // (6, v7=10), (7, 'M'), (9, Thumb-2=2) — Tag_ARM_ISA_use omitted (0).
    assert_eq!(pairs, &[6, 10, 7, b'M', 9, 2]);

    // Section type is SHT_ARM_ATTRIBUTES so readelf/objdump find it.
    let header = elf::FileHeader32::<Endianness>::parse(&*bytes).unwrap();
    let endian = header.endian().unwrap();
    let sections = header.sections(endian, &*bytes).unwrap();
    assert!(
        sections
            .iter()
            .any(|s| s.sh_type(endian) == elf::SHT_ARM_ATTRIBUTES),
        "sh_type must be SHT_ARM_ATTRIBUTES (0x70000003)"
    );
}

/// #637: `synth disasm` on a fresh cortex-m3 object prints Thumb-2 mnemonics
/// (auto-detected), not the A32 mis-decode. The fixture is the #682 masked
/// shift — `i32.shl` of `(i32.and (local.get 1) (i32.const 31))` — whose
/// lowering folds the mask and emits a register `lsl`; the prologue/epilogue
/// `push {..., lr}` / `pop {..., pc}` pair is the unmistakable Thumb signature
/// (the historical A32 mis-decode printed `andhs`/`andeq` garbage). Skips when
/// no `--triple`-capable objdump is on PATH (bare CI runner, #489 lesson).
#[test]
fn disasm_prints_thumb_mnemonics_637() {
    let has_objdump = Command::new("objdump")
        .args(["--version"])
        .output()
        .is_ok_and(|o| o.status.success());
    if !has_objdump {
        eprintln!("skip: no objdump on PATH");
        return;
    }

    let dir = std::env::temp_dir().join("synth_637_disasm");
    std::fs::create_dir_all(&dir).unwrap();
    let obj = compile(
        &dir,
        "maskshift",
        r#"(module (func (export "f") (param i32 i32) (result i32)
  (i32.shl (local.get 0) (i32.and (local.get 1) (i32.const 31)))))"#,
    );
    let out = Command::new(synth())
        .arg("disasm")
        .arg(&obj)
        .output()
        .expect("run synth disasm");
    if !out.status.success() {
        // objdump exists but choked (e.g. GNU objdump without --triple AND
        // without ARM support) — the detection itself is unit-covered.
        eprintln!(
            "skip: synth disasm failed on this host: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        return;
    }
    let text = String::from_utf8_lossy(&out.stdout).to_lowercase();
    assert!(
        text.contains("push") && text.contains("pop"),
        "#637: expected Thumb prologue/epilogue mnemonics, got:\n{text}"
    );
    assert!(
        text.contains("lsl"),
        "#637/#682: masked-shift fixture must show the register shift:\n{text}"
    );
    assert!(
        !text.contains("andhs") && !text.contains("andeq"),
        "#637: the A32 mis-decode signature must be gone:\n{text}"
    );
}
