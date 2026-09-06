//! #1168 (RQ-63-WASTCLOSURE) — the `.wast` input path must apply the #235
//! reachable-callgraph closure, and a relocation against a function this
//! object does not place must be refused WHATEVER the reason.
//!
//! Measured on main @ 362f7f82 (v0.62.0 + 3), the same two-function module in
//! two formats:
//!
//! ```text
//! $ synth compile m.wat  -b arm --target cortex-m3 --relocatable --all-exports -o a.o
//! Compiled 2 functions        symtab: func_0 func_1 pub, no UNDEF     exit 0
//! $ synth compile m.wast -b arm --target cortex-m3 --relocatable --all-exports -o b.o
//! Compiled 1 functions        symtab: func_1 pub, UNDEF func_0        exit 0
//! $ arm-none-eabi-ld b.o      undefined reference to `func_0'
//! ```
//!
//! cortex-r5 and rv32imac shipped the same dangling object at exit 0; the
//! self-contained `--cortex-m` leg (the one `spec_compile_census.py` measures)
//! silently flipped to a link-me ET_REL; aarch64 refused only because its ELF
//! builder refuses any unplaced relocation target (#851/#1013) — and its
//! message asserted "the symbol was declined earlier; see the preceding
//! warning" when nothing had been declined and no warning had been printed.
//!
//! Two independent fixes, both pinned here:
//!   (a) the `.wast` merge applies the closure PER MODULE, seeded from the
//!       exports that survive the last-module-wins override;
//!   (b) the #1102 dangling-reference gate is keyed on "not placed in this
//!       object" (per owning module), not on the DECLINED set — so a callee
//!       that was never compiled is refused exactly like one that declined.
//!
//! The multi-module merge shares ONE `func_N` label space; a direct call whose
//! label another module's retained function also defines would bind to
//! whichever body was laid out last — measured on main as a silently WRONG
//! object at exit 0 (`wast_multi_module_label_collision_refuses` below). That
//! shape now refuses with a reason naming the call.
//!
//! Every RED case was verified against the unfixed baseline binary before
//! this test was written (exit 0 + `U func_0`, or exit 0 + mis-bound call);
//! the controls hold on both binaries. The execution half — link with a real
//! linker and run vs wasmtime on all five backend legs — is
//! `scripts/repro/wast_callgraph_closure_1168_differential.py`.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use object::{Object, ObjectKind, ObjectSymbol, SymbolScope};

fn synth() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_synth"))
}

fn workdir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("synth-1168-{tag}"));
    std::fs::create_dir_all(&d).expect("temp dir");
    d
}

/// The issue's minimal module: a non-exported helper reached only by `call`.
const MODULE: &str = r#"(module
  (func $helper (result i32) i32.const 42)
  (func (export "pub") (result i32) call $helper))
"#;

fn minimal_wast() -> String {
    format!("{MODULE}(assert_return (invoke \"pub\") (i32.const 42))\n")
}

/// Module 0's export `g` calls its OWN index 0 (`f`); module 1 re-exports `f`
/// at index 1 (index 0 is an unexported pad nothing reaches). `g` survives,
/// module 0's `f` is superseded as a NAME but still reachable from `g` — it
/// must ship as the file-local callee `func_0`, never as a second GLOBAL `f`.
/// No referenced label collides (`func_1` is defined twice but called by
/// nobody), so this merge is sound.
const SUPERSEDED_CALLEE_WAST: &str = r#"(module
  (func (export "f") (result i32) i32.const 1)
  (func (export "g") (result i32) (i32.add (call 0) (i32.const 10))))
(module
  (func $pad (result i32) i32.const 0)
  (func (export "f") (result i32) i32.const 100))
(assert_return (invoke "g") (i32.const 11))
(assert_return (invoke "f") (i32.const 100))
"#;

/// Module 0's `g` calls index 0 (`f`); module 1's `h` is ALSO index 0 and
/// survives. One object, one `func_0` label: on main the call bound to
/// whichever body the ELF builder registered last — `g` returned `h`'s value.
const LABEL_COLLISION_WAST: &str = r#"(module
  (func (export "f") (result i32) i32.const 1)
  (func (export "g") (result i32) (call 0)))
(module
  (func (export "h") (result i32) i32.const 2))
(assert_return (invoke "g") (i32.const 1))
"#;

/// A retained callee that DECLINES on rv32 (offset past the immediate range,
/// the #1102 fixture) — as a `.wast`. Before the closure it was never
/// compiled and the object shipped with `U synth_func_0`; now it is retained,
/// declines, and the gate refuses under the #1102 wording.
const DECLINED_CALLEE_WAST: &str = r#"(module
  (memory 32)
  (func $big (param i32) (result i32)
    (i32.load offset=1048588 (local.get 0)))
  (func (export "entry") (param i32) (result i32)
    (call $big (local.get 0))))
(assert_return (invoke "entry" (i32.const 0)) (i32.const 0))
"#;

fn compile(dir: &Path, src_name: &str, text: &str, out_name: &str, args: &[&str]) -> Output {
    let src = dir.join(src_name);
    std::fs::write(&src, text).expect("write source");
    let obj = dir.join(out_name);
    // The temp workdir persists across runs — a stale object from an earlier
    // run would make the "no object left behind" assertions vacuous.
    let _ = std::fs::remove_file(&obj);
    let mut c = Command::new(synth());
    c.arg("compile").arg(src.to_str().unwrap());
    c.args(args);
    c.args(["-o", obj.to_str().unwrap()]);
    c.output().expect("run synth compile")
}

fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

fn combined(o: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&o.stdout),
        String::from_utf8_lossy(&o.stderr)
    )
}

struct Symtab {
    kind: ObjectKind,
    defined: Vec<String>,
    globals: Vec<String>,
    undefined: Vec<String>,
}

/// Read the symbol table by TYPE through `object` — never by section name
/// (synth's ARM objects name their symtab with an empty string) and never
/// from disassembly text.
fn symtab(path: &Path) -> Symtab {
    let bytes = std::fs::read(path).expect("read object");
    let file = object::File::parse(&*bytes).expect("parse ELF");
    let mut t = Symtab {
        kind: file.kind(),
        defined: Vec::new(),
        globals: Vec::new(),
        undefined: Vec::new(),
    };
    for s in file.symbols() {
        let Ok(name) = s.name() else { continue };
        if name.is_empty() {
            continue;
        }
        if s.is_undefined() {
            t.undefined.push(name.to_string());
        } else if s.is_definition() {
            t.defined.push(name.to_string());
            if s.scope() != SymbolScope::Compilation {
                t.globals.push(name.to_string());
            }
        }
    }
    t.defined.sort();
    t.globals.sort();
    t.undefined.sort();
    t
}

const LEGS: &[(&str, &[&str])] = &[
    (
        "m3-reloc",
        &[
            "-b",
            "arm",
            "--target",
            "cortex-m3",
            "--relocatable",
            "--all-exports",
        ],
    ),
    ("m3-selfcontained", &["--cortex-m", "--all-exports"]),
    (
        "r5-reloc",
        &[
            "-b",
            "arm",
            "--target",
            "cortex-r5",
            "--relocatable",
            "--all-exports",
        ],
    ),
    (
        "rv32-reloc",
        &[
            "-b",
            "riscv",
            "--target",
            "riscv32imac-unknown-none-elf",
            "--relocatable",
            "--all-exports",
        ],
    ),
    (
        "a64-reloc",
        &[
            "-b",
            "aarch64",
            "--target",
            "cortex-a53",
            "--relocatable",
            "--all-exports",
        ],
    ),
];

/// RED on main for every leg (3 x exit 0 + `U func_0`/`U synth_func_0`, the
/// self-contained leg an ET_REL, aarch64 exit 1): the minimal `.wast` now
/// compiles BOTH functions and the object has no undefined symbol at all.
#[test]
fn wast_minimal_repro_is_complete_on_every_backend() {
    for (tag, args) in LEGS {
        let dir = workdir(&format!("min-{tag}"));
        let out = compile(&dir, "m.wast", &minimal_wast(), "m.o", args);
        let all = combined(&out);
        assert_eq!(out.status.code(), Some(0), "[{tag}] exit\n{all}");
        assert!(
            all.contains("Compiled 2 functions"),
            "[{tag}] the helper must be compiled alongside the export\n{all}"
        );
        let t = symtab(&dir.join("m.o"));
        assert!(
            t.undefined.is_empty(),
            "[{tag}] object carries undefined symbol(s): {:?}",
            t.undefined
        );
        assert!(
            t.defined.iter().any(|n| n == "func_0") && t.defined.iter().any(|n| n == "pub"),
            "[{tag}] helper func_0 + export pub must both be defined: {:?}",
            t.defined
        );
        if *tag == "m3-selfcontained" {
            assert_eq!(
                t.kind,
                ObjectKind::Executable,
                "[{tag}] the self-contained image must be ET_EXEC — a dangling callee \
                 used to flip it to a link-me ET_REL silently"
            );
        }
    }
}

/// The `.wast` path now retains exactly what the `.wat` path retains, in the
/// same (definition) order — so a single-module `.wast` produces the SAME
/// BYTES as its `.wat`. Also pins that the merge's function order is
/// deterministic (it was `HashMap::into_values()` order before).
#[test]
fn wast_and_wat_produce_identical_objects_for_a_single_module() {
    let dir = workdir("wat-eq");
    let args = &[
        "-b",
        "arm",
        "--target",
        "cortex-m3",
        "--relocatable",
        "--all-exports",
    ];
    let a = compile(&dir, "m.wat", MODULE, "a.o", args);
    let b = compile(&dir, "m.wast", &minimal_wast(), "b.o", args);
    assert_eq!(a.status.code(), Some(0), "{}", stderr(&a));
    assert_eq!(b.status.code(), Some(0), "{}", stderr(&b));
    let (wa, wb) = (
        std::fs::read(dir.join("a.o")).unwrap(),
        std::fs::read(dir.join("b.o")).unwrap(),
    );
    assert!(
        wa == wb,
        ".wat and .wast objects differ ({} vs {} bytes) — the two input paths must \
         agree on the retained set and its order",
        wa.len(),
        wb.len()
    );
}

/// A superseded export that a surviving export of ITS module still reaches
/// ships as a file-local callee (`func_0`), never as a second GLOBAL of the
/// winning name; the winner is the only global `f`.
#[test]
fn wast_multi_module_superseded_export_is_retained_as_callee() {
    let dir = workdir("superseded");
    let out = compile(
        &dir,
        "s.wast",
        SUPERSEDED_CALLEE_WAST,
        "s.o",
        &[
            "-b",
            "arm",
            "--target",
            "cortex-m3",
            "--relocatable",
            "--all-exports",
        ],
    );
    let all = combined(&out);
    assert_eq!(out.status.code(), Some(0), "{all}");
    assert!(
        all.contains("Compiled 3 functions"),
        "g, its callee (module 0's superseded f) and module 1's f\n{all}"
    );
    let t = symtab(&dir.join("s.o"));
    assert!(t.undefined.is_empty(), "UNDEF: {:?}", t.undefined);
    assert_eq!(
        t.globals.iter().filter(|n| *n == "f").count(),
        1,
        "exactly one GLOBAL `f` (the last module's); globals = {:?}",
        t.globals
    );
    assert!(
        t.defined.iter().any(|n| n == "func_0") && t.globals.iter().any(|n| n == "g"),
        "module 0's f must survive as the local callee func_0 beside global g: {:?}",
        t.defined
    );
}

/// RED on main (exit 0, object written, `g`'s call bound to `h`): a direct
/// call whose label another module's retained function also defines refuses
/// with a reason naming the call — never a silently mis-bound object.
#[test]
fn wast_multi_module_label_collision_refuses() {
    let dir = workdir("collision");
    let out = compile(
        &dir,
        "c.wast",
        LABEL_COLLISION_WAST,
        "c.o",
        &[
            "-b",
            "arm",
            "--target",
            "cortex-m3",
            "--relocatable",
            "--all-exports",
        ],
    );
    let err = stderr(&out);
    assert_eq!(
        out.status.code(),
        Some(1),
        "expected the clean refusal (exit 1); 0 means a mis-bound object shipped, \
         101 means a panic.\nstderr:\n{err}"
    );
    assert!(
        !err.contains("panicked at"),
        "refusal delivered via panic.\nstderr:\n{err}"
    );
    assert!(
        err.contains("#1168") && err.contains("'g' (module 0) calls function index 0"),
        "refusal must name the class and the mis-bindable call.\nstderr:\n{err}"
    );
    assert!(
        !dir.join("c.o").exists(),
        "refused compile still wrote an output object"
    );
}

/// RED on main (exit 0 + `U synth_func_0`): a callee the closure now retains
/// and the backend then DECLINES hits the #1102 gate on the `.wast` path too
/// — the decline wording, because a 'skipping function' warning DID precede.
#[test]
fn wast_declined_callee_hits_the_1102_gate_rv32() {
    let dir = workdir("declined-rv32");
    let out = compile(
        &dir,
        "d.wast",
        DECLINED_CALLEE_WAST,
        "d.o",
        &[
            "-b",
            "riscv",
            "--target",
            "riscv32imac-unknown-none-elf",
            "--relocatable",
            "--all-exports",
        ],
    );
    let err = stderr(&out);
    assert!(
        err.contains("warning: skipping function 'func_0'") && err.contains("immediate 1048588"),
        "fixture no longer trips the decline this test depends on — premise gone.\n{err}"
    );
    assert_eq!(out.status.code(), Some(1), "clean refusal expected\n{err}");
    assert!(
        err.contains("#1102") && err.contains("'entry' -> 'func_0'"),
        "a declined retained callee keeps the #1102 wording.\n{err}"
    );
    assert!(
        !dir.join("d.o").exists(),
        "refused compile still wrote an object"
    );
}
