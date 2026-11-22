//! Refs #1761: on a multi-module `.wast`, a call is bound within its OWN
//! module.
//!
//! The merge lays every module out in one `func_N` label space, but each
//! module keeps its own function index space: index 0 is import 0 in a
//! module that has an import, and the first defined function in a module
//! that has none. The ARM relocatable ELF builder mapped `func_N` to the
//! field name of import N of the MERGED import table at every call site, so
//! the recursive `call 0` of an import-free module became `bl g0`, another
//! module's import, in an object that defines `func_0` itself. Exit 0.
//!
//! Measured on main 6641efec and on the v0.92 batch 1 tree (7e604df2):
//!
//! ```text
//! $ synth compile three.wast --target cortex-m4 --all-exports --relocatable -o three.o
//!   28: R_ARM_THM_CALL  g0        <- inside `a`
//!   48: R_ARM_THM_CALL  g1        <- inside `b`
//! nm: T a, t func_0, T b, t func_2, U g0, U g1
//! ```
//!
//! This file reads the relocation and symbol tables on the default
//! `cargo test --workspace` build. The executed comparison (kiln against the
//! linked object under unicorn) is
//! `crates/synth-oracle/tests/wast_merge_call_binding_1761.rs`.

use std::path::PathBuf;
use std::process::Command;

use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget};

/// The issue's file. Module 1 has no import and calls its own function 0;
/// module 2's import 0 is `g0`, and it calls only `g1`.
const ISSUE: &str = r#"(module
  (func (export "a") (param i32) (result i32)
    local.get 0 i32.eqz if (result i32) i32.const 7
    else local.get 0 i32.const 1 i32.sub call 0 end))
(module
  (import "env" "g0" (func $g0 (param i32) (result i32)))
  (import "env" "g1" (func $g1 (param i32) (result i32)))
  (func (export "b") (param i32) (result i32) local.get 0 call $g1))
"#;

/// Both modules import, with different counts: module 1's function 1 is
/// DEFINED (it has one import), while the merged table's import 1 is `g1`.
/// Module 1 also calls import 0, which the two modules agree on.
const FEWER_IMPORTS: &str = r#"(module
  (import "env" "g0" (func $g0 (param i32) (result i32)))
  (func (export "a") (param i32) (result i32)
    local.get 0 i32.eqz if (result i32) i32.const 40 call $g0
    else local.get 0 i32.const 1 i32.sub call 1 end))
(module
  (import "env" "g0" (func $g0 (param i32) (result i32)))
  (import "env" "g1" (func $g1 (param i32) (result i32)))
  (func (export "b") (param i32) (result i32) local.get 0 call $g0))
"#;

const ARM: &[&str] = &["--target", "cortex-m4", "--relocatable"];
const ARM_DEFAULT: &[&str] = &["--target", "cortex-m4"];
const RV32: &[&str] = &["-b", "riscv", "--target", "riscv32imac", "--relocatable"];
const A64: &[&str] = &["-b", "aarch64", "--relocatable"];

fn compile(tag: &str, wast: &str, flags: &[&str]) -> Result<Vec<u8>, String> {
    let dir = std::env::temp_dir().join(format!("synth-1761-{}-{tag}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let (src, out) = (dir.join("m.wast"), dir.join("m.o"));
    std::fs::write(&src, wast).expect("write source");
    let o = Command::new(PathBuf::from(env!("CARGO_BIN_EXE_synth")))
        .arg("compile")
        .arg(&src)
        .args(flags)
        .arg("--all-exports")
        .arg("-o")
        .arg(&out)
        .output()
        .expect("synth runs");
    if o.status.success() {
        Ok(std::fs::read(&out).expect("object written"))
    } else {
        Err(String::from_utf8_lossy(&o.stderr).into_owned())
    }
}

/// What one call relocation is bound to: the function whose address the
/// symbol is defined at, or the undefined symbol's name.
#[derive(Debug, PartialEq, Eq)]
enum Bound {
    Defined(String),
    Undefined(String),
}

fn defined(name: &str) -> Bound {
    Bound::Defined(name.to_string())
}

fn undefined(name: &str) -> Bound {
    Bound::Undefined(name.to_string())
}

/// Every `.text` relocation in offset order, resolved through the symbol
/// table. A defined target is named by the EXPORTED symbol at its address,
/// so `func_0` and `a` read the same.
fn call_bindings(elf: &[u8]) -> Vec<Bound> {
    let file = object::File::parse(elf).expect("an object file");
    let text = file.section_by_name(".text").expect(".text");
    let mut relocs: Vec<_> = text.relocations().collect();
    relocs.sort_by_key(|(off, _)| *off);
    relocs
        .into_iter()
        .map(|(_, r)| {
            let RelocationTarget::Symbol(si) = r.target() else {
                panic!("a relocation that names no symbol");
            };
            let sym = file.symbol_by_index(si).expect("relocation symbol");
            let name = sym.name().expect("symbol name").to_string();
            if sym.is_undefined() {
                return Bound::Undefined(name);
            }
            let exported = file
                .symbols()
                .filter(|s| s.is_global() && !s.is_undefined())
                .filter(|s| s.section_index() == sym.section_index())
                .find(|s| s.address() == sym.address())
                .map(|s| s.name().expect("symbol name").to_string());
            Bound::Defined(exported.unwrap_or(name))
        })
        .collect()
}

fn undefined_symbols(elf: &[u8]) -> Vec<String> {
    let file = object::File::parse(elf).expect("an object file");
    let mut names: Vec<String> = file
        .symbols()
        .filter(|s| s.is_undefined())
        .filter_map(|s| s.name().ok().map(str::to_string))
        .filter(|n| !n.is_empty())
        .collect();
    names.sort();
    names.dedup();
    names
}

/// The issue, on ARM: the call inside `a` is `a`'s own, and `g0` (which no
/// module calls) is not referenced at all.
#[test]
fn arm_binds_a_recursive_call_to_its_own_function() {
    for (leg, flags) in [("relocatable", ARM), ("default", ARM_DEFAULT)] {
        let elf = compile(&format!("issue-arm-{leg}"), ISSUE, flags).expect("compiles");
        assert_eq!(
            call_bindings(&elf),
            [defined("a"), undefined("g1")],
            "{leg}: [the call in `a`, the call in `b`]"
        );
        assert_eq!(undefined_symbols(&elf), ["g1"], "{leg}");
    }
}

/// A defined index below the merged import count, beside a real import
/// call from the same function: each binds to what ITS module means.
#[test]
fn arm_tells_a_defined_index_from_an_import_per_call_site() {
    for (leg, flags) in [("relocatable", ARM), ("default", ARM_DEFAULT)] {
        let elf = compile(&format!("fewer-arm-{leg}"), FEWER_IMPORTS, flags).expect("compiles");
        assert_eq!(
            call_bindings(&elf),
            [undefined("g0"), defined("a"), undefined("g0")],
            "{leg}: [a -> g0, a -> a, b -> g0]"
        );
        assert_eq!(
            undefined_symbols(&elf),
            ["g0"],
            "{leg}: `g1` is never called"
        );
    }
}

/// The RV32 twin. It was right before #1761 (a defined function shadowed
/// the import label when the two maps were merged) and takes the same
/// per-call-site rule now.
#[test]
fn rv32_binds_the_same_way() {
    let elf = compile("issue-rv32", ISSUE, RV32).expect("compiles");
    assert_eq!(call_bindings(&elf), [defined("a"), undefined("g1")]);
    assert_eq!(undefined_symbols(&elf), ["g1"]);
    let elf = compile("fewer-rv32", FEWER_IMPORTS, RV32).expect("compiles");
    assert_eq!(
        call_bindings(&elf),
        [undefined("g0"), defined("a"), undefined("g0")]
    );
    assert_eq!(undefined_symbols(&elf), ["g0"]);
}

/// The AArch64 twin lowers no import call on the `.wast` merge and refuses
/// both files, naming the call it cannot place. A refusal, not wrong code.
#[test]
fn a64_refuses_the_import_call() {
    for (tag, wast, label) in [
        ("issue", ISSUE, "func_1"),
        ("fewer", FEWER_IMPORTS, "func_0"),
    ] {
        let err = compile(&format!("{tag}-a64"), wast, A64).expect_err("refused");
        assert!(
            err.contains(&format!(
                "targets symbol '{label}', which this object does not place"
            )),
            "{tag}: {err}"
        );
    }
}
