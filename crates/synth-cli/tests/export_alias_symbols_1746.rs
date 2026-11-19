//! #1746 — every export name of a function is a defined GLOBAL symbol.
//!
//! A wasm module may export one function index under several names;
//! wit-bindgen does it for every component-model export (`wdg_refresh` AND
//! `gust:hal/wdg@0.1.0#refresh`). Measured on the v0.91 base (`4d80d9d6`):
//! the decoder kept ONE name per index (the last declared), so every
//! relocatable writer — ARM ELF32 (direct and optimized selector), RV32,
//! AArch64 ELF and Mach-O — defined that one name and dropped the rest with
//! exit 0. A consumer linking by a dropped name got an undefined symbol at
//! link time, and #952 never fired because the function itself was emitted.
//!
//! The oracle reads the object's SYMBOL TABLE with the `object` crate — never
//! `synth disasm` or `nm` text — and derives the expected names from the
//! input module's own export section (parsed here with `wasmparser`), not
//! from a hand list:
//!
//! 1. every export name resolves to a DEFINED, GLOBAL function symbol;
//! 2. all names of one index share one address and one section (and, on ELF,
//!    one size);
//! 3. PAIRED CONTROL: the same module with each index exported ONCE (under
//!    the name main kept) compiles to byte-identical `.text`, and its symbol
//!    table is exactly the aliased object's minus the alias names — aliases
//!    add symbols and move nothing.
//!
//! Plus: `--func-name` selects a function by ANY of its export names (main
//! refused `-n <non-last name>` as "not found"), the #952 refusal names the
//! aliases of a skipped export, and a name no symbol table can carry is
//! refused loudly instead of shipped.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use object::{Object, ObjectSection, ObjectSymbol, SymbolKind};

mod artifact_guard;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

/// Function 0 under three names (one component-model shaped, with `:`, `/`,
/// `@` and `#`); function 1 once; function 2 twice, and it CALLS function 0
/// so an in-object relocation crosses the aliased index.
const ALIASED: &str = r#"(module
  (func $add (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (func $sub (param i32 i32) (result i32) local.get 0 local.get 1 i32.sub)
  (func $twice (param i32) (result i32) local.get 0 local.get 0 call $add)
  (export "add" (func $add))
  (export "gust:hal/wdg@0.1.0#refresh" (func $add))
  (export "sub" (func $sub))
  (export "add_alias" (func $add))
  (export "gust:hal/wdg@0.1.0#is-running" (func $twice))
  (export "twice" (func $twice)))"#;

/// The control: each index exported once, under the LAST-declared name (the
/// one the pre-#1746 decoder kept).
const ONCE: &str = r#"(module
  (func $add (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (func $sub (param i32 i32) (result i32) local.get 0 local.get 1 i32.sub)
  (func $twice (param i32) (result i32) local.get 0 local.get 0 call $add)
  (export "sub" (func $sub))
  (export "add_alias" (func $add))
  (export "twice" (func $twice)))"#;

/// The ARM OPTIMIZED path: no `--relocatable`, but the import call forces an
/// ET_REL through the optimized selector.
const ALIASED_IMPORT: &str = r#"(module
  (import "env" "ext" (func $ext (param i32) (result i32)))
  (func $f (param i32) (result i32) local.get 0 call $ext)
  (export "gust:hal/wdg@0.1.0#lock" (func $f))
  (export "f" (func $f)))"#;

const ONCE_IMPORT: &str = r#"(module
  (import "env" "ext" (func $ext (param i32) (result i32)))
  (func $f (param i32) (result i32) local.get 0 call $ext)
  (export "f" (func $f)))"#;

/// One object-producing invocation.
struct Path_ {
    tag: &'static str,
    args: &'static [&'static str],
    macho: bool,
}

const MODULE_PATHS: &[Path_] = &[
    Path_ {
        tag: "arm-direct",
        args: &[
            "-b",
            "arm",
            "-t",
            "cortex-m4",
            "--all-exports",
            "--relocatable",
        ],
        macho: false,
    },
    Path_ {
        tag: "arm-r5-direct",
        args: &[
            "-b",
            "arm",
            "-t",
            "cortex-r5",
            "--all-exports",
            "--relocatable",
        ],
        macho: false,
    },
    Path_ {
        tag: "rv32",
        args: &["-b", "riscv", "--all-exports", "--relocatable"],
        macho: false,
    },
    Path_ {
        tag: "a64-elf",
        args: &["-b", "aarch64", "--all-exports", "--relocatable"],
        macho: false,
    },
    Path_ {
        tag: "a64-macho",
        args: &[
            "-b",
            "aarch64",
            "--all-exports",
            "--relocatable",
            "--object-format",
            "macho",
        ],
        macho: true,
    },
];

fn work(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("synth-1746-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn compile(dir: &Path, name: &str, wat: &str, args: &[&str]) -> Vec<u8> {
    let src = dir.join(format!("{name}.wat"));
    std::fs::write(&src, wat).unwrap();
    let out = dir.join(format!("{name}.o"));
    let mut cmd = Command::new(synth());
    cmd.arg("compile").arg(&src).args(args).arg("-o").arg(&out);
    artifact_guard::compile_artifact_or_panic(&mut cmd, &out, name)
}

/// Export names per function index, from the module's own export section.
fn exports_by_index(wat: &str) -> BTreeMap<u32, Vec<String>> {
    let wasm = wat::parse_str(wat).unwrap();
    let mut m: BTreeMap<u32, Vec<String>> = BTreeMap::new();
    for payload in wasmparser::Parser::new(0).parse_all(&wasm) {
        if let wasmparser::Payload::ExportSection(r) = payload.unwrap() {
            for e in r {
                let e = e.unwrap();
                if e.kind == wasmparser::ExternalKind::Func {
                    m.entry(e.index).or_default().push(e.name.to_string());
                }
            }
        }
    }
    m
}

/// One defined symbol as the object states it.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Def {
    name: String,
    address: u64,
    size: u64,
    section: String,
    global: bool,
    func: bool,
}

/// Every DEFINED symbol, keyed by name (Mach-O's leading `_` stripped).
fn defined_symbols(bytes: &[u8], macho: bool) -> BTreeMap<String, Vec<Def>> {
    let file = object::File::parse(bytes).expect("synth object parses");
    let mut m: BTreeMap<String, Vec<Def>> = BTreeMap::new();
    for s in file.symbols() {
        if s.is_undefined() || s.kind() == SymbolKind::Section || s.kind() == SymbolKind::File {
            continue;
        }
        let raw = s.name().expect("UTF-8 symbol name");
        if raw.is_empty() {
            continue;
        }
        let name = if macho {
            raw.strip_prefix('_')
                .unwrap_or_else(|| panic!("Mach-O symbol without `_`: {raw}"))
        } else {
            raw
        };
        let section = s
            .section_index()
            .and_then(|i| file.section_by_index(i).ok())
            .map(|sec| sec.name().unwrap_or("?").to_string())
            .unwrap_or_default();
        m.entry(name.to_string()).or_default().push(Def {
            name: name.to_string(),
            address: s.address(),
            size: s.size(),
            section,
            global: s.is_global(),
            func: s.kind() == SymbolKind::Text,
        });
    }
    m
}

fn text_bytes(bytes: &[u8]) -> Vec<u8> {
    let file = object::File::parse(bytes).unwrap();
    let sec = file
        .sections()
        .find(|s| matches!(s.name(), Ok(".text") | Ok("__text")))
        .expect(".text section");
    sec.data().unwrap().to_vec()
}

/// The #1746 assertion: every export name of every index is ONE defined
/// GLOBAL function symbol, and all names of an index agree on address,
/// section and (ELF) size. Returns the alias names checked.
fn assert_every_export_defined(
    ctx: &str,
    syms: &BTreeMap<String, Vec<Def>>,
    exports: &BTreeMap<u32, Vec<String>>,
    macho: bool,
    only: Option<u32>,
) -> usize {
    let mut aliases = 0;
    for (idx, names) in exports {
        if only.is_some_and(|o| o != *idx) {
            continue;
        }
        let mut seen: Option<&Def> = None;
        for name in names {
            let defs = syms.get(name).unwrap_or_else(|| {
                panic!(
                    "[{ctx}] export {name:?} of function {idx} is NOT defined in the \
                     object (#1746); defined: {:?}",
                    syms.keys().collect::<Vec<_>>()
                )
            });
            let globals: Vec<&Def> = defs.iter().filter(|d| d.global).collect();
            assert_eq!(
                globals.len(),
                1,
                "[{ctx}] export {name:?} must be exactly one GLOBAL definition, got {defs:?}"
            );
            let d = globals[0];
            assert!(
                d.func,
                "[{ctx}] export {name:?} is not a function symbol: {d:?}"
            );
            if let Some(first) = seen {
                aliases += 1;
                assert_eq!(
                    (d.address, &d.section),
                    (first.address, &first.section),
                    "[{ctx}] alias {name:?} and {:?} of function {idx} must share one address",
                    first.name
                );
                if !macho {
                    assert_eq!(
                        d.size, first.size,
                        "[{ctx}] alias {name:?} and {:?} of function {idx} must share one size",
                        first.name
                    );
                }
            } else {
                seen = Some(d);
            }
        }
    }
    aliases
}

/// The PAIRED control: `.text` identical, and the aliased symbol table is the
/// control's plus exactly the alias names.
fn assert_aliases_only_add_symbols(
    ctx: &str,
    aliased: &[u8],
    control: &[u8],
    macho: bool,
    alias_names: &BTreeSet<String>,
) {
    assert_eq!(
        text_bytes(aliased),
        text_bytes(control),
        "[{ctx}] .text moved: export aliases must add symbols only (#1746)"
    );
    let a = defined_symbols(aliased, macho);
    let c = defined_symbols(control, macho);
    let a_minus: BTreeMap<_, _> = a
        .iter()
        .filter(|(n, _)| !alias_names.contains(*n))
        .map(|(n, v)| (n.clone(), v.clone()))
        .collect();
    assert_eq!(
        a_minus, c,
        "[{ctx}] the aliased object's symbols minus the aliases must equal the control's"
    );
    for n in alias_names {
        assert!(a.contains_key(n), "[{ctx}] alias {n:?} absent");
        assert!(
            !c.contains_key(n),
            "[{ctx}] control unexpectedly defines {n:?}"
        );
    }
}

fn alias_names(aliased: &str, once: &str) -> BTreeSet<String> {
    let a: BTreeSet<String> = exports_by_index(aliased).into_values().flatten().collect();
    let o: BTreeSet<String> = exports_by_index(once).into_values().flatten().collect();
    a.difference(&o).cloned().collect()
}

#[test]
fn every_export_name_is_a_global_symbol_on_every_relocatable_path() {
    let exports = exports_by_index(ALIASED);
    let aliases = alias_names(ALIASED, ONCE);
    assert_eq!(aliases.len(), 3, "fixture: three alias names");
    // Every path runs even after one fails, so a red names EACH writer that
    // drops a name rather than only the first.
    let failed: Vec<&str> = MODULE_PATHS
        .iter()
        .filter(|p| {
            std::panic::catch_unwind(|| {
                let dir = work(p.tag);
                let obj = compile(&dir, "aliased", ALIASED, p.args);
                let ctl = compile(&dir, "once", ONCE, p.args);
                let syms = defined_symbols(&obj, p.macho);
                let n = assert_every_export_defined(p.tag, &syms, &exports, p.macho, None);
                assert_eq!(n, 3, "[{}] three aliases checked", p.tag);
                assert_aliases_only_add_symbols(p.tag, &obj, &ctl, p.macho, &aliases);
            })
            .is_err()
        })
        .map(|p| p.tag)
        .collect();
    assert!(failed.is_empty(), "#1746 fails on: {failed:?}");
}

#[test]
fn arm_optimized_path_defines_every_export_name() {
    // No `--relocatable`: the import call makes the optimized ARM path emit
    // an ET_REL — the second ARM writer route #1746 names.
    let args = &["-b", "arm", "-t", "cortex-m4", "--all-exports"];
    let dir = work("arm-opt");
    let obj = compile(&dir, "aliased", ALIASED_IMPORT, args);
    let ctl = compile(&dir, "once", ONCE_IMPORT, args);
    let file = object::File::parse(&*obj).unwrap();
    assert_eq!(
        file.kind(),
        object::ObjectKind::Relocatable,
        "the import must force ET_REL"
    );
    let exports = exports_by_index(ALIASED_IMPORT);
    let n = assert_every_export_defined(
        "arm-opt",
        &defined_symbols(&obj, false),
        &exports,
        false,
        None,
    );
    assert_eq!(n, 1);
    assert_aliases_only_add_symbols(
        "arm-opt",
        &obj,
        &ctl,
        false,
        &alias_names(ALIASED_IMPORT, ONCE_IMPORT),
    );
}

#[test]
fn internal_call_still_binds_to_the_aliased_function() {
    // `twice` calls function 0. Adding alias symbols appends symtab entries,
    // so the call relocation must still name a symbol AT function 0's address.
    for p in MODULE_PATHS {
        let dir = work(&format!("{}-reloc", p.tag));
        let obj = compile(&dir, "aliased", ALIASED, p.args);
        let file = object::File::parse(&*obj).unwrap();
        // Function 0 by the name main also kept, so this non-regression
        // check reads the same on both trees.
        let add = &defined_symbols(&obj, p.macho)["add_alias"][0];
        let text = file
            .sections()
            .find(|s| matches!(s.name(), Ok(".text") | Ok("__text")))
            .unwrap();
        let mut targets = Vec::new();
        for (_, r) in text.relocations() {
            if let object::RelocationTarget::Symbol(si) = r.target() {
                let s = file.symbol_by_index(si).unwrap();
                targets.push((s.name().unwrap().to_string(), s.address()));
            }
        }
        assert!(
            !targets.is_empty(),
            "[{}] the call must carry a relocation",
            p.tag
        );
        for (name, addr) in &targets {
            assert_eq!(
                *addr, add.address,
                "[{}] the call relocates against {name:?} at {addr:#x}, not function 0 at {:#x}",
                p.tag, add.address
            );
        }
    }
}

#[test]
fn func_name_selects_by_any_export_name() {
    // Before #1746 `-n` matched only the LAST-declared name of an aliased index
    // ("Function 'add' not found"). The single-function writers (RV32, AArch64)
    // and the ARM `-n --relocatable` reroute (#1565) define every name.
    let exports = exports_by_index(ALIASED);
    let singles: &[(&str, &[&str], bool)] = &[
        ("rv32-n", &["-b", "riscv", "--relocatable"], false),
        ("a64-n", &["-b", "aarch64", "--relocatable"], false),
        (
            "a64-macho-n",
            &["-b", "aarch64", "--relocatable", "--object-format", "macho"],
            true,
        ),
        (
            "arm-n",
            &["-b", "arm", "-t", "cortex-m4", "--relocatable"],
            false,
        ),
    ];
    let mut failed = Vec::new();
    for (tag, args, macho) in singles {
        for pick in ["add", "gust:hal/wdg@0.1.0#refresh", "add_alias"] {
            let ok = std::panic::catch_unwind(|| {
                let dir = work(&format!("{tag}-{}", pick.len()));
                let mut a: Vec<&str> = args.to_vec();
                a.extend(["-n", pick]);
                let obj = compile(&dir, "single", ALIASED, &a);
                let n = assert_every_export_defined(
                    &format!("{tag} -n {pick}"),
                    &defined_symbols(&obj, *macho),
                    &exports,
                    *macho,
                    Some(0),
                );
                assert_eq!(n, 2);
            })
            .is_ok();
            if !ok {
                failed.push(format!("{tag} -n {pick}"));
            }
        }
    }
    assert!(failed.is_empty(), "#1746 --func-name fails on: {failed:?}");
}

#[test]
fn skipped_export_refusal_names_its_aliases() {
    // #952 on an aliased export: every name it takes with it is named.
    let wat = r#"(module
  (func $g (param i32 i64) (result i32) (local.get 0))
  (func (export "f") (export "gust:x/y@0.1.0#f") (result i32)
    (call $g (i32.const 7) (i64.const 9))))"#;
    let dir = work("952");
    let src = dir.join("m.wat");
    std::fs::write(&src, wat).unwrap();
    let out = Command::new(synth())
        .arg("compile")
        .arg(&src)
        .args([
            "-b",
            "arm",
            "-t",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
            "-o",
        ])
        .arg(dir.join("m.o"))
        .output()
        .unwrap();
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(!out.status.success(), "a skipped export must refuse (#952)");
    assert!(
        err.contains("gust:x/y@0.1.0#f (also exported as f)"),
        "the #952 refusal must name every export name of the skipped function: {err}"
    );
}

#[test]
fn unemittable_export_names_are_refused_on_every_path() {
    // Each module exports function 0 under a good name AND one bad name, so
    // the bad one is an ALIAS (it must not be dropped) — and, for the bad
    // name declared last, the primary too.
    let bad: &[(&str, &str, &str)] = &[
        ("empty", "\"\"", "it is empty"),
        ("nul", "\"x\\00y\"", "NUL byte"),
        ("label", "\"func_1\"", "call label for function 1"),
        ("reserved", "\"__synth_globals\"", "reserved for synth"),
    ];
    let paths: Vec<&[&str]> = MODULE_PATHS
        .iter()
        .map(|p| p.args)
        .chain([&["-b", "riscv", "--relocatable", "-n", "a"] as &[&str]])
        .collect();
    for (tag, name, why) in bad {
        for order in [0, 1] {
            let exports = if order == 0 {
                format!("(export \"a\" (func $a)) (export {name} (func $a))")
            } else {
                format!("(export {name} (func $a)) (export \"a\" (func $a))")
            };
            let wat = format!(
                "(module (func $a (result i32) i32.const 1) \
                 (func $b (result i32) i32.const 2) (export \"b\" (func $b)) {exports})"
            );
            for args in &paths {
                // The single-function writers place ONE function and no call,
                // so a label-shaped name collides with nothing there.
                if *tag == "label" && args.contains(&"-n") {
                    continue;
                }
                let dir = work(&format!("bad-{tag}-{order}"));
                let src = dir.join("m.wat");
                std::fs::write(&src, &wat).unwrap();
                let obj = dir.join("m.o");
                let _ = std::fs::remove_file(&obj);
                let out = Command::new(synth())
                    .arg("compile")
                    .arg(&src)
                    .args(*args)
                    .arg("-o")
                    .arg(&obj)
                    .output()
                    .unwrap();
                let err = String::from_utf8_lossy(&out.stderr);
                assert!(
                    !out.status.success(),
                    "[{tag}/{order} {args:?}] export {name} must be refused, exit 0"
                );
                assert!(
                    err.contains("cannot be emitted as a symbol") && err.contains(why),
                    "[{tag}/{order} {args:?}] refusal must say why: {err}"
                );
                assert!(
                    !obj.exists(),
                    "[{tag}/{order}] a refused compile wrote {obj:?}"
                );
            }
        }
    }
}

#[test]
fn own_label_import_label_and_component_names_are_accepted() {
    // Negative controls for the refusal: an export spelled like its OWN
    // index's label; one spelled like an IMPORT's label (RQ-91-NAMECOLL,
    // #1698, rewrites import calls to the field name, and its oracle executes
    // this shape); and the component-model punctuation. All are emittable.
    let own = r#"(module (func $a (result i32) i32.const 1)
  (export "func_0" (func $a)) (export "gust:hal/wdg@0.1.0#start" (func $a)) (export "a" (func $a)))"#;
    let import = r#"(module (import "env" "get" (func $imp (result i32)))
  (func $a (result i32) i32.const 7)
  (func $u (result i32) call $imp)
  (export "func_0" (func $a)) (export "a" (func $a)) (export "use_import" (func $u)))"#;
    for (name, wat) in [("own", own), ("import", import)] {
        let exports = exports_by_index(wat);
        for p in MODULE_PATHS {
            let dir = work(&format!("ok-{name}-{}", p.tag));
            let obj = compile(&dir, "ok", wat, p.args);
            let n = assert_every_export_defined(
                p.tag,
                &defined_symbols(&obj, p.macho),
                &exports,
                p.macho,
                None,
            );
            assert!(n >= 1, "[{name} {}] an alias was checked", p.tag);
        }
    }
}
