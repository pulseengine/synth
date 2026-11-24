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

/// Two aliased functions and a caller that calls function 1, then function 0.
/// Function 0's aliases are appended to the symbol table BEFORE function 1's
/// symbols, so an alias that is added without being counted shifts every
/// later symbol index — and the call to function 1 would relocate against
/// whatever symbol now sits at the old index.
const CALLS: &str = r#"(module
  (func $add (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (func $sub (param i32 i32) (result i32) local.get 0 local.get 1 i32.sub)
  (func $both (param i32) (result i32)
    local.get 0 local.get 0 call $sub local.get 0 call $add)
  (export "add" (func $add))
  (export "gust:hal/wdg@0.1.0#refresh" (func $add))
  (export "add_alias" (func $add))
  (export "sub" (func $sub))
  (export "sub_alias" (func $sub))
  (export "both" (func $both)))"#;

#[test]
fn internal_calls_still_bind_to_their_callees() {
    // Each call relocation, in code order, must resolve to a symbol AT its
    // callee's address: function 1 first, then function 0. Red under a
    // mutant that adds an ARM alias symbol without counting it (the call to
    // function 1 then binds to an alias of function 0).
    let mut failed = Vec::new();
    for p in MODULE_PATHS {
        let ok = std::panic::catch_unwind(|| {
            let dir = work(&format!("{}-calls", p.tag));
            let obj = compile(&dir, "calls", CALLS, p.args);
            let file = object::File::parse(&*obj).unwrap();
            let syms = defined_symbols(&obj, p.macho);
            let at = |n: &str| syms[n].iter().find(|d| d.global).unwrap().address;
            let want = vec![at("sub"), at("add")];
            assert_ne!(want[0], want[1]);
            let text = file
                .sections()
                .find(|s| matches!(s.name(), Ok(".text") | Ok("__text")))
                .unwrap();
            let mut relocs: Vec<(u64, String, u64)> = Vec::new();
            for (off, r) in text.relocations() {
                if let object::RelocationTarget::Symbol(si) = r.target() {
                    let s = file.symbol_by_index(si).unwrap();
                    relocs.push((off, s.name().unwrap().to_string(), s.address()));
                }
            }
            relocs.sort();
            let got: Vec<u64> = relocs.iter().map(|r| r.2).collect();
            assert_eq!(
                got, want,
                "[{}] the calls relocate against {relocs:?}, not function 1 then function 0",
                p.tag
            );
        })
        .is_ok();
        if !ok {
            failed.push(p.tag);
        }
    }
    assert!(failed.is_empty(), "#1746 call binding fails on: {failed:?}");
}

/// The multi-module `.wast` merge: a later module's export supersedes an
/// earlier module's on EVERY name, not only on each function's last-declared
/// one. Module 1 exports `x` and `y`; module 3 re-exports `y`, so module 1's
/// body keeps `x`. Module 2 exports `a` and `z`; module 4 re-exports `a` as a
/// NON-last name, so `a` is module 4's body (with `w`) and module 2 keeps `z`.
const MERGE_WAST: &str = r#"
(module (func (result i32) i32.const 1) (export "x" (func 0)) (export "y" (func 0)))
(module (func (result i32) i32.const 2) (export "a" (func 0)) (export "z" (func 0)))
(module (func (result i32) i32.const 3) (export "y" (func 0)))
(module (func (result i32) i32.const 4) (export "a" (func 0)) (export "w" (func 0)))
"#;

#[test]
fn wast_merge_supersedes_every_export_name() {
    let merge_paths = [&MODULE_PATHS[0], &MODULE_PATHS[2], &MODULE_PATHS[3]];
    for p in merge_paths {
        let dir = work(&format!("{}-merge", p.tag));
        let src = dir.join("m.wast");
        std::fs::write(&src, MERGE_WAST).unwrap();
        let out = dir.join("m.o");
        let mut cmd = Command::new(synth());
        cmd.arg("compile")
            .arg(&src)
            .args(p.args)
            .arg("-o")
            .arg(&out);
        let obj = artifact_guard::compile_artifact_or_panic(&mut cmd, &out, "merge");
        let syms = defined_symbols(&obj, p.macho);
        let at = |n: &str| -> u64 {
            let g: Vec<&Def> = syms
                .get(n)
                .unwrap_or_else(|| panic!("[{}] `{n}` is not defined: {syms:?}", p.tag))
                .iter()
                .filter(|d| d.global)
                .collect();
            assert_eq!(g.len(), 1, "[{}] `{n}`: one GLOBAL, got {g:?}", p.tag);
            g[0].address
        };
        let (x, y, z, a, w) = (at("x"), at("y"), at("z"), at("a"), at("w"));
        assert_eq!(a, w, "[{}] `a` must be module 4's body, with `w`", p.tag);
        assert_ne!(a, z, "[{}] `a` must not stay on module 2's body", p.tag);
        assert_ne!(
            x, y,
            "[{}] `y` must be module 3's body, not module 1's",
            p.tag
        );
        let bodies: BTreeSet<u64> = [x, y, z, a].into_iter().collect();
        assert_eq!(bodies.len(), 4, "[{}] four distinct bodies", p.tag);
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
    // #952 on an aliased export: every name it takes with it is named. The
    // export is declined by #929 (an i64 argument of a `call_indirect`; the
    // direct-call form of this fixture compiles since #1785).
    let wat = r#"(module
  (type $t (func (param i32 i64) (result i32)))
  (table 1 funcref)
  (elem (i32.const 0) $g)
  (func $g (type $t) (local.get 0))
  (func (export "f") (export "gust:x/y@0.1.0#f") (result i32)
    (call_indirect (type $t) (i32.const 7) (i64.const 9) (i32.const 0))))"#;
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
    // Negative controls for the refusal, every one emitted with each export
    // name GLOBAL: an export spelled like its OWN index's label, declared
    // first, LAST (the primary name — before the fix it came out LOCAL on ARM
    // and AArch64, exit 0) and ALONE; one spelled like an IMPORT's label
    // (RQ-91-NAMECOLL, #1698, rewrites import calls to the field name, and
    // its oracle executes this shape); one naming NO function (`func_99` in a
    // two-function module, accepted on main); and component punctuation.
    let cases: &[(&str, &str)] = &[
        (
            "own-first",
            r#"(module (func $a (result i32) i32.const 1)
  (export "func_0" (func $a)) (export "gust:hal/wdg@0.1.0#start" (func $a)) (export "a" (func $a)))"#,
        ),
        (
            "own-last",
            r#"(module (func $a (result i32) i32.const 1)
  (export "a" (func $a)) (export "gust:hal/wdg@0.1.0#start" (func $a)) (export "func_0" (func $a)))"#,
        ),
        (
            "own-only",
            r#"(module (func $a (result i32) i32.const 1) (export "func_0" (func $a)))"#,
        ),
        (
            "import",
            r#"(module (import "env" "get" (func $imp (result i32)))
  (func $a (result i32) i32.const 7)
  (func $u (result i32) call $imp)
  (export "func_0" (func $a)) (export "a" (func $a)) (export "use_import" (func $u)))"#,
        ),
        (
            "no-such-function",
            r#"(module (func $a (result i32) i32.const 1) (func $b (result i32) i32.const 2)
  (export "a" (func $a)) (export "func_99" (func $b)) (export "b" (func $b)))"#,
        ),
    ];
    let mut failed = Vec::new();
    for (name, wat) in cases {
        let exports = exports_by_index(wat);
        for p in MODULE_PATHS {
            let ok = std::panic::catch_unwind(|| {
                let dir = work(&format!("ok-{name}-{}", p.tag));
                let obj = compile(&dir, "ok", wat, p.args);
                assert_every_export_defined(
                    &format!("{name} {}", p.tag),
                    &defined_symbols(&obj, p.macho),
                    &exports,
                    p.macho,
                    None,
                );
            })
            .is_ok();
            if !ok {
                failed.push(format!("{name} {}", p.tag));
            }
        }
    }
    assert!(
        failed.is_empty(),
        "#1746 accepted names fail on: {failed:?}"
    );
}

#[test]
fn self_contained_images_are_not_refused() {
    // The refusal is a RELOCATABLE-object rule: self-contained images carry
    // no alias symbols and compile these modules as before #1746 (measured
    // byte-identical to main 4d80d9d6 on all four shapes).
    let shapes = [
        r#"(export "" (func $a))"#,
        r#"(export "__synth_thing" (func $a))"#,
        r#"(export "func_1" (func $a))"#,
        r#"(export "func_99" (func $b))"#,
    ];
    for (k, extra) in shapes.iter().enumerate() {
        let wat = format!(
            "(module (func $a (result i32) i32.const 1) (func $b (result i32) i32.const 2) \
             (export \"a\" (func $a)) (export \"b\" (func $b)) {extra})"
        );
        for args in [
            &[
                "-b",
                "arm",
                "-t",
                "cortex-m4",
                "--cortex-m",
                "--all-exports",
            ][..],
            &["-b", "arm", "-t", "cortex-r5", "--all-exports"][..],
        ] {
            let dir = work(&format!("sc-{k}-{}", args[3]));
            let obj = compile(&dir, "sc", &wat, args);
            let file = object::File::parse(&*obj).unwrap();
            assert_eq!(
                file.kind(),
                object::ObjectKind::Executable,
                "[{extra} {args:?}] a self-contained image"
            );
        }
    }
}
