//! The host-link derivation (#1696, #1758) is keyed on the functions the
//! compile RETAINS, per module.
//!
//! A module that calls a function import is compiled as the `--relocatable`
//! object. Two shapes must NOT be caught by that rule, because nothing in
//! the emitted image calls an import:
//!
//! - the only import call sits in a function no export, table entry or start
//!   function reaches (the #235 closure drops it), and
//! - in a multi-module `.wast`, a module with no imports makes a LOCAL call
//!   whose index is below ANOTHER module's import count.
//!
//! Both are correct self-contained images on main. The paired controls show
//! the rule still fires when the call is reachable.

use std::process::Command;

mod artifact_guard;

const DEAD_CALL: &str = r#"(module
  (import "env" "g" (func $g (param i32) (result i32)))
  (memory 1)
  (func $dead (param i32) (result i32) local.get 0 call $g)
  (func (export "ld") (param i32) (result i32) local.get 0 i32.load))"#;

/// The same module with the import call reachable from an export.
const LIVE_CALL: &str = r#"(module
  (import "env" "g" (func $g (param i32) (result i32)))
  (memory 1)
  (func $live (param i32) (result i32) local.get 0 call $g)
  (func (export "ld") (param i32) (result i32) local.get 0 call $live i32.load))"#;

/// The dead-call module without the dead function and its import: what the
/// image must be, byte for byte.
const NO_IMPORT: &str = r#"(module
  (memory 1)
  (func (export "ld") (param i32) (result i32) local.get 0 i32.load))"#;

/// Module A (no imports) calls its own function 0; module B declares an
/// import it never calls.
const WAST_LOCAL_CALL_BESIDE_AN_IMPORT: &str = r#"(module
  (func $h (param i32) (result i32) local.get 0 i32.const 1 i32.add)
  (func (export "a") (param i32) (result i32) local.get 0 call $h))
(module
  (import "env" "g" (func $g (param i32) (result i32)))
  (func (export "b") (param i32) (result i32) local.get 0))"#;

/// Module A alone: what its function `a` must compile to.
const WAST_MODULE_A_ALONE: &str = r#"(module
  (func $h (param i32) (result i32) local.get 0 i32.const 1 i32.add)
  (func (export "a") (param i32) (result i32) local.get 0 call $h))"#;

const TARGETS: &[&[&str]] = &[
    &["--target", "cortex-m4"],
    &["--cortex-m"],
    &["--target", "cortex-m3"],
    &["--target", "cortex-m7dp"],
];

struct Built {
    ok: bool,
    bytes: Vec<u8>,
    log: String,
}

fn build(tag: &str, ext: &str, src: &str, flags: &[&str]) -> Built {
    let input = artifact_guard::unique_artifact(tag, ext);
    std::fs::write(&input, src).expect("write input");
    let out = artifact_guard::unique_artifact(tag, "o");
    let o = Command::new(env!("CARGO_BIN_EXE_synth"))
        .arg("compile")
        .arg(&input)
        .arg("--all-exports")
        .args(flags)
        .arg("-o")
        .arg(&out)
        .output()
        .expect("run synth");
    let log = format!(
        "{}{}",
        String::from_utf8_lossy(&o.stdout),
        String::from_utf8_lossy(&o.stderr)
    );
    let bytes = if o.status.success() {
        artifact_guard::read_artifact(&out).unwrap_or_else(|e| panic!("{e}"))
    } else {
        Vec::new()
    };
    let _ = std::fs::remove_file(&input);
    let _ = std::fs::remove_file(&out);
    Built {
        ok: o.status.success(),
        bytes,
        log,
    }
}

fn e_type(elf: &[u8]) -> u16 {
    u16::from_le_bytes([elf[16], elf[17]])
}

const ET_REL: u16 = 1;
const ET_EXEC: u16 = 2;
const SWITCH_NOTICE: &str = "module calls imported function(s)";

#[test]
fn an_import_call_in_dead_code_does_not_make_the_image_an_object() {
    for flags in TARGETS {
        let dead = build("hostlink_dead", "wat", DEAD_CALL, flags);
        assert!(dead.ok, "{flags:?}: {}", dead.log);
        assert_eq!(
            e_type(&dead.bytes),
            ET_EXEC,
            "{flags:?}: a module whose only import call is unreachable became an object"
        );
        assert!(
            !dead.log.contains(SWITCH_NOTICE),
            "{flags:?}: announced a switch to a relocatable object: {}",
            dead.log
        );
        // The dropped function and the uncalled import leave no trace: the
        // image is the one the module without them compiles to.
        let plain = build("hostlink_plain", "wat", NO_IMPORT, flags);
        assert!(plain.ok, "{flags:?}: {}", plain.log);
        assert!(
            dead.bytes == plain.bytes,
            "{flags:?}: the image differs from the import-free module's"
        );

        // Paired control: reachable, the same call makes it the object.
        let live = build("hostlink_live", "wat", LIVE_CALL, flags);
        assert!(live.ok, "{flags:?}: {}", live.log);
        assert_eq!(e_type(&live.bytes), ET_REL, "{flags:?}");
        assert!(live.log.contains(SWITCH_NOTICE), "{flags:?}: {}", live.log);
        let rel = build(
            "hostlink_live_rel",
            "wat",
            LIVE_CALL,
            &[flags, &["--relocatable"][..]].concat(),
        );
        assert!(rel.ok, "{flags:?}: {}", rel.log);
        assert!(
            live.bytes == rel.bytes,
            "{flags:?}: not the --relocatable object"
        );
    }
}

#[test]
fn a_local_call_is_not_an_import_call_because_another_module_imports() {
    for flags in TARGETS {
        let merged = build(
            "hostlink_wast",
            "wast",
            WAST_LOCAL_CALL_BESIDE_AN_IMPORT,
            flags,
        );
        assert!(
            merged.ok,
            "{flags:?}: module A's local call was refused: {}",
            merged.log
        );
        assert_eq!(e_type(&merged.bytes), ET_EXEC, "{flags:?}");
        assert!(!merged.log.contains(SWITCH_NOTICE), "{flags:?}");
        assert!(!merged.log.contains("#1699"), "{flags:?}: {}", merged.log);
        // Module A's functions are compiled as they are alone.
        let alone = build("hostlink_wast_a", "wat", WAST_MODULE_A_ALONE, flags);
        assert!(alone.ok, "{flags:?}: {}", alone.log);
        for name in ["a", "func_0"] {
            assert_eq!(
                function_bytes(&merged.bytes, name),
                function_bytes(&alone.bytes, name),
                "{flags:?}: `{name}` differs from module A compiled alone"
            );
        }
    }
}

/// The bytes of the function symbol `name`, from the symbol table.
fn function_bytes(elf: &[u8], name: &str) -> Vec<u8> {
    use object::{Object, ObjectSection, ObjectSymbol};
    let file = object::File::parse(elf).expect("parse ELF");
    let sym = file
        .symbols()
        .find(|s| s.name() == Ok(name) && s.kind() == object::SymbolKind::Text)
        .unwrap_or_else(|| panic!("no function symbol `{name}`"));
    let sec = file
        .section_by_index(sym.section_index().expect("defined"))
        .expect("section");
    let data = sec.data().expect("section data");
    let start = ((sym.address() & !1) - sec.address()) as usize;
    let size = sym.size() as usize;
    assert!(size > 0, "`{name}` has no size");
    data[start..start + size].to_vec()
}
