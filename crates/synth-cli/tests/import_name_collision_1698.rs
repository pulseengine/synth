//! RQ-91-NAMECOLL (#1698): a called import whose field name equals a symbol
//! the object defines (here, the module's own export) must REFUSE on every
//! backend that turns an import call into a symbol. It used to bind the call
//! to the export, with rc 0. The paired control, the same module with the
//! export renamed, must keep the import as an undefined GLOBAL symbol that a
//! `.text` relocation targets: the #173/#197 embedder contract, unchanged.
//!
//! The execution differential against wasmtime is
//! `scripts/repro/import_name_collision_1698_differential.py`.

use std::process::Command;

use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget, SymbolIndex};

mod artifact_guard;

const COLLIDING: &str = r#"(module
  (import "env" "get" (func $imp (result i32)))
  (func (export "get") (result i32) i32.const 7)
  (func (export "use_import") (result i32) call $imp))"#;

const TWO_MODULES: &str = r#"(module
  (import "a" "get" (func $a (result i32)))
  (import "b" "get" (func $b (result i32)))
  (func (export "use_a") (result i32) call $a)
  (func (export "use_b") (result i32) call $b))"#;

const CONFIGS: &[&[&str]] = &[
    &["--target", "cortex-m4", "--relocatable"],
    &["--target", "cortex-r5", "--relocatable"],
    &["-b", "riscv", "--relocatable"],
    &["-b", "aarch64", "--relocatable"],
];

fn write_wat(tag: &str, src: &str) -> std::path::PathBuf {
    let p = artifact_guard::unique_artifact(tag, "wat");
    std::fs::write(&p, src).expect("write wat");
    p
}

fn compile(wat: &std::path::Path, out: &std::path::Path, flags: &[&str]) -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_synth"));
    cmd.args(["compile", wat.to_str().unwrap(), "--all-exports"])
        .args(flags)
        .args(["-o", out.to_str().unwrap()]);
    cmd
}

fn assert_refused(src: &str, tag: &str, needles: &[&str]) {
    let wat = write_wat(tag, src);
    for flags in CONFIGS {
        let out = artifact_guard::unique_artifact(tag, "o");
        let o = compile(&wat, &out, flags).output().expect("run synth");
        let text =
            String::from_utf8_lossy(&o.stderr).to_string() + &String::from_utf8_lossy(&o.stdout);
        assert!(
            !o.status.success(),
            "{flags:?}: must refuse, compiled:\n{text}"
        );
        for n in needles {
            assert!(
                text.contains(n),
                "{flags:?}: diagnostic lacks {n:?}:\n{text}"
            );
        }
        assert!(!out.exists(), "{flags:?}: refused but wrote an object");
    }
}

#[test]
fn import_named_like_own_export_refuses_on_every_backend_1698() {
    assert_refused(
        COLLIDING,
        "namecoll_1698",
        &["`env`.`get`", "symbol `get`", "#1698"],
    );
}

#[test]
fn same_field_from_two_modules_refuses_on_every_backend_1698() {
    assert_refused(
        TWO_MODULES,
        "namecoll_dup_1698",
        &["`a`.`get` and `b`.`get`", "#1698"],
    );
}

#[test]
fn renamed_export_keeps_the_import_undefined_and_relocated_1698() {
    let wat = write_wat(
        "namecoll_ctrl_1698",
        &COLLIDING.replace("(export \"get\")", "(export \"get7\")"),
    );
    for flags in CONFIGS {
        let out = artifact_guard::unique_artifact("namecoll_ctrl_1698", "o");
        let data = artifact_guard::compile_bytes_or_panic(
            &mut compile(&wat, &out, flags),
            &out,
            "control",
        );
        let obj = object::File::parse(&*data).expect("parse object");
        let get = obj
            .symbols()
            .find(|s| s.name() == Ok("get"))
            .unwrap_or_else(|| panic!("{flags:?}: no `get` symbol"));
        assert!(get.is_undefined(), "{flags:?}: `get` must be SHN_UNDEF");
        assert!(get.is_global(), "{flags:?}: `get` must be GLOBAL");
        let idx: SymbolIndex = get.index();
        let text = obj.section_by_name(".text").expect(".text");
        let hits = text
            .relocations()
            .filter(|(_, r)| r.target() == RelocationTarget::Symbol(idx))
            .count();
        assert_eq!(
            hits, 1,
            "{flags:?}: one call relocation must target the undefined `get`"
        );
    }
}
