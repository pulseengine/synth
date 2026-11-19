//! RQ-91-X86SKEL (#1741): `synth compile -b x86_64` through the real binary.
//!
//! The accepted shape writes an ELF64 `EM_X86_64` `ET_REL` with
//! `.note.GNU-stack`; every refusal — an unlowered op, a module-level shape,
//! a flag the x86-64 path does not accept, a non-x86 target — exits non-zero,
//! NAMES its cause, and writes NO object (the output path is pre-seeded with a
//! sentinel and must be untouched).

use std::path::{Path, PathBuf};
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn dir() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("x86_64_skeleton_1741-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn run(wat: &str, flags: &[&str]) -> (bool, String, PathBuf) {
    let d = dir();
    let input = d.join("m.wat");
    std::fs::write(&input, wat).unwrap();
    let out = d.join("m.o");
    std::fs::write(&out, b"SENTINEL").unwrap();
    let o = Command::new(synth())
        .arg("compile")
        .arg(&input)
        .args(flags)
        .arg("-o")
        .arg(&out)
        .output()
        .expect("run synth");
    let stderr = String::from_utf8_lossy(&o.stderr).into_owned();
    (o.status.success(), stderr, out)
}

fn untouched(out: &Path) -> bool {
    std::fs::read(out).unwrap() == b"SENTINEL"
}

const ADD: &str = r#"(module (func (export "add") (param i32 i32) (result i32)
  local.get 0 local.get 1 i32.add))"#;

#[test]
fn add_compiles_to_an_x86_64_et_rel_with_the_stack_note() {
    for flags in [
        &["-b", "x86_64", "--relocatable"][..],
        &["-b", "x86_64"][..],
        &[
            "-b",
            "x86_64",
            "--relocatable",
            "--all-exports",
            "--target",
            "x86_64",
        ][..],
        &["-b", "x86_64", "--safety-bounds", "software"][..],
        &["-b", "x86_64", "--safety-bounds", "none"][..],
    ] {
        let (ok, stderr, out) = run(ADD, flags);
        assert!(ok, "{flags:?}: {stderr}");
        let e = std::fs::read(&out).unwrap();
        assert_eq!(&e[..5], b"\x7fELF\x02", "{flags:?}: not ELF64");
        assert_eq!(u16::from_le_bytes([e[16], e[17]]), 1, "ET_REL");
        assert_eq!(u16::from_le_bytes([e[18], e[19]]), 62, "EM_X86_64");
        assert!(e.windows(16).any(|w| w == b".note.GNU-stack\0"));
    }
}

#[test]
fn every_refusal_names_its_cause_and_writes_nothing() {
    let cases: &[(&str, &[&str], &str)] = &[
        (
            r#"(module (func (export "f") (param i32 i32) (result i32)
                 local.get 0 local.get 1 i32.sub))"#,
            &[],
            "I32Sub",
        ),
        (
            r#"(module (memory 1) (func (export "f") (param i32) (result i32)
                 local.get 0 i32.load))"#,
            &[],
            "linear memory",
        ),
        (
            r#"(module (func (export "f") (param i64) (result i64) local.get 0))"#,
            &[],
            "i64",
        ),
        (ADD, &["--emit-wcet"], "--emit-wcet"),
        (
            ADD,
            &["--cortex-m", "--debug-line"],
            "--cortex-m, --debug-line",
        ),
        (ADD, &["--object-format", "macho"], "--object-format macho"),
        (ADD, &["--safety-bounds", "mask"], "--safety-bounds mask"),
        (
            ADD,
            &["--target", "cortex-a53"],
            "does not accept --target cortex-a53",
        ),
        (ADD, &["--func-name", "add"], "--func-name"),
        // REVIEW_13 F3: used to exit 0 with the export missing from the object.
        (
            r#"(module (func (export "func_0") (param i32) (result i32) local.get 0))"#,
            &[],
            "same name as its own object-local label `func_0`",
        ),
    ];
    for (wat, extra, needle) in cases {
        let mut flags = vec!["-b", "x86_64"];
        flags.extend_from_slice(extra);
        let (ok, stderr, out) = run(wat, &flags);
        assert!(!ok, "{flags:?} {needle}: exit 0");
        assert!(
            stderr.contains(needle),
            "{flags:?}: `{needle}` not in: {stderr}"
        );
        assert!(untouched(&out), "{flags:?}: an object was written");
    }
}

/// `--target x86_64` with the default (arm) backend is refused and points at
/// `-b x86_64`, rather than building a wrong-ISA object.
#[test]
fn an_x86_target_without_the_backend_is_refused() {
    let (ok, stderr, out) = run(ADD, &["--target", "x86_64"]);
    assert!(!ok);
    assert!(stderr.contains("-b x86_64"), "{stderr}");
    assert!(untouched(&out));
}

#[test]
fn the_backend_is_listed() {
    let o = Command::new(synth()).arg("backends").output().unwrap();
    let s = String::from_utf8_lossy(&o.stdout);
    assert!(
        s.lines().any(|l| l.trim_start().starts_with("x86_64 ")),
        "{s}"
    );
}
