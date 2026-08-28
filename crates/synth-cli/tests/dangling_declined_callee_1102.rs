//! #1102 (RQ-61-DANGLE) — a RETAINED function that relocates against a
//! function this compile DECLINED must fail the compile loudly, on EVERY
//! backend. Before the fix the object shipped with exit 0 and could never
//! link.
//!
//! Measured on v0.60.0 (main @ 23a0b546), minimal module — an INTERNAL
//! function declines on rv32, the exported caller is retained:
//!
//! ```text
//! $ synth compile dangle.wat -b riscv --target riscv32imac-unknown-none-elf \
//!     --all-exports --relocatable -o d.o
//! warning: skipping function 'func_0': ... immediate 1048588 too large ...
//! warning: 1 of 2 functions were skipped (not in output): func_0
//! $ echo $?            # -> 0
//! $ ld.lld d.o         # -> undefined symbol: synth_func_0
//! ```
//!
//! `synth_func_0` names a function the module itself DEFINES, so no linker
//! input can ever resolve it: the object is not partial, it is UNLINKABLE.
//! The #952 guard is keyed on declined REQUESTED EXPORTS and the #1013
//! refusal lives only in the aarch64 ELF builder — an internal decline
//! referenced by a retained export slipped past both. Also measured on the
//! SAME baseline: ARM Thumb-2 and A32 ship the identical shape (dangling
//! `func_N` GLOBAL UNDEF in `.rel.text`/symtab, exit 0) — the "ARM has no
//! symtab" theory was a probe artifact: the ARM builder emits its symtab
//! section with an EMPTY name string, so a probe by section NAME misses it;
//! `readelf -sW` (by section type) shows it.
//!
//! The fix is one driver-level gate in `compile_all_exports` — the site where
//! the two facts (which functions were skipped, which relocations the
//! retained functions carry) already meet for all four backends — matching
//! the aarch64 #1013 policy. Deliberately NOT waived by
//! `--allow-skipped-exports`: that flag accepts a PARTIAL object, not an
//! unlinkable one. Deliberately NOT a stub/trap body for the declined callee
//! and NOT a dropped call — both would turn an unlinkable object into a
//! WRONG one.
//!
//! All refusal fixtures were verified RED (exit 0 + dangling UNDEF) against
//! the unfixed baseline binary before this test was written; the negative
//! controls were verified exit-0 on BOTH binaries (and the whole
//! `scripts/repro` corpus x 5 legs is byte-identical old-vs-new: 835 pairs,
//! 0 differing, 3 rv32 pairs newly-declined — each proven unlinkable-before
//! by an UNDEF `synth_func_N` in the old object).

use std::path::PathBuf;
use std::process::{Command, Output};

fn synth() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_synth"))
}

fn workdir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("synth-1102-{tag}"));
    std::fs::create_dir_all(&d).expect("temp dir");
    d
}

/// The minimal reported shape: `$big` is INTERNAL (not exported), declines on
/// rv32 (memory offset 1048588 exceeds the selector's immediate range), and
/// the retained export `entry` calls it.
const DANGLING_INTERNAL: &str = r#"(module
  (memory 32)
  (func $big (param i32) (result i32)
    (i32.load offset=1048588 (local.get 0)))
  (func (export "entry") (param i32) (result i32)
    (call $big (local.get 0))))
"#;

/// gale's `gpio-thin` shape, minimized: TWO retained exports reference the
/// same declined internal function (`--gc-sections` could not save this one),
/// plus one export that never touches it.
const DANGLING_MULTI_EXPORT: &str = r#"(module
  (memory 32)
  (func $big (param i32) (result i32)
    (i32.load offset=1048588 (local.get 0)))
  (func (export "gpio_get") (param i32) (result i32)
    (call $big (local.get 0)))
  (func (export "gpio_set") (param i32) (result i32)
    (call $big (i32.add (local.get 0) (i32.const 4))))
  (func (export "gpio_ok") (result i32) (i32.const 1)))
"#;

/// The same decline with NO dangling reference: the offending function is
/// exported (so it is compiled and declines) but nothing retained calls it.
/// Under `--allow-skipped-exports` (the corpus-sweep shape) this must stay a
/// routine exit-0 partial object — the inverse failure of the fix would be
/// refusing every module that merely contains a decline.
const DECLINE_WITHOUT_REFERENCE: &str = r#"(module
  (memory 32)
  (func (export "big") (param i32) (result i32)
    (i32.load offset=1048588 (local.get 0)))
  (func (export "entry") (param i32) (result i32)
    (i32.add (local.get 0) (i32.const 1))))
"#;

/// ARM/A32 decline shape (the rv32 fixture's large offset COMPILES on ARM):
/// an internal `$hard` returns f64, which a soft-float target refuses
/// (GI-FPU-002); its direct caller `$helper` declines too (f64 at the
/// AAPCS-VFP boundary), and the retained export `f` calls `$helper` — a
/// dangling `func_1` reloc. This is the exact fixture #952 used as its
/// "helper-only skip" negative control; measured on the baseline it ships
/// `f` with a GLOBAL UNDEF `func_1`, i.e. it was the #1102 defect all along.
const ARM_DANGLING_HELPER: &str = r#"(module
  (func $hard (result f64) (f64.sqrt (f64.const 2.0)))
  (func $helper (result i32) (call $hard) (drop) (i32.const 1))
  (func (export "f") (result i32) (call $helper)))
"#;

fn compile(dir: &std::path::Path, wat: &str, out_name: &str, args: &[&str]) -> Output {
    let src = dir.join("m.wat");
    std::fs::write(&src, wat).expect("write wat");
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

/// The full refusal contract, shared by every leg: the decline anchor still
/// fired (so the assertions judge THIS defect, not some unrelated failure),
/// the exit is the clean-error 1 (not 0 = shipped, not 101 = panic), the
/// reason names the class and the dangling edge, and no object is left.
fn assert_refusal(out: &Output, dir: &std::path::Path, out_name: &str, edge: &str, anchor: &str) {
    let err = stderr(out);
    assert!(
        err.contains("skipping function") && err.contains(anchor),
        "fixture no longer trips the decline this test depends on (anchor \
         '{anchor}') — premise gone, revisit rather than pass on some other \
         error.\nstderr:\n{err}"
    );
    assert_eq!(
        out.status.code(),
        Some(1),
        "expected the clean refusal (exit 1); 0 means an unlinkable object \
         was shipped (#1102), 101 means a panic.\nstderr:\n{err}"
    );
    assert!(
        !err.contains("panicked at") && !err.contains("RUST_BACKTRACE"),
        "refusal was delivered via panic, not a clean error.\nstderr:\n{err}"
    );
    assert!(
        err.contains("#1102") && err.contains(edge),
        "refusal must name the #1102 class and the dangling edge {edge}.\nstderr:\n{err}"
    );
    assert!(
        !dir.join(out_name).exists(),
        "refused compile still wrote an output object"
    );
}

const RV32: &[&str] = &[
    "-b",
    "riscv",
    "--target",
    "riscv32imac-unknown-none-elf",
    "--all-exports",
    "--relocatable",
];

/// RED on the unfixed binary (exited 0 with a dangling `synth_func_0`): the
/// reported minimal module refuses on rv32.
#[test]
fn rv32_dangling_internal_refuses() {
    let dir = workdir("rv32-min");
    let out = compile(&dir, DANGLING_INTERNAL, "d.o", RV32);
    assert_refusal(
        &out,
        &dir,
        "d.o",
        "'entry' -> 'func_0'",
        "immediate 1048588",
    );
}

/// RED on the unfixed binary: gale's multi-export shape — BOTH retained
/// callers are named in the refusal, so the diagnostic scales past the
/// minimal module.
#[test]
fn rv32_multi_export_names_every_dangling_caller() {
    let dir = workdir("rv32-multi");
    let out = compile(&dir, DANGLING_MULTI_EXPORT, "m.o", RV32);
    assert_refusal(
        &out,
        &dir,
        "m.o",
        "'gpio_get' -> 'func_0'",
        "immediate 1048588",
    );
    assert!(
        stderr(&out).contains("'gpio_set' -> 'func_0'"),
        "the second dangling caller must be named too.\nstderr:\n{}",
        stderr(&out)
    );
}

/// The #952 escape hatch does NOT waive the refusal: that flag accepts a
/// PARTIAL object (a requested export absent, counted downstream), which is
/// categorically different from an UNLINKABLE one. The aarch64 #1013 builder
/// refusal was likewise unconditional — this pins the same policy here.
#[test]
fn allow_skipped_exports_does_not_waive_the_refusal() {
    let dir = workdir("rv32-flag");
    let mut args = RV32.to_vec();
    args.push("--allow-skipped-exports");
    let out = compile(&dir, DANGLING_INTERNAL, "d.o", &args);
    assert_refusal(
        &out,
        &dir,
        "d.o",
        "'entry' -> 'func_0'",
        "immediate 1048588",
    );
}

/// RED on the unfixed binary (exit 0, GLOBAL UNDEF `func_1` in the object):
/// ARM Thumb-2 `--relocatable` refuses the same class. This is the fixture
/// #952 previously used as its "helper-only skips stay exit 0" negative
/// control — measured, that control was shipping an unlinkable object.
#[test]
fn arm_thumb2_relocatable_refuses() {
    let dir = workdir("arm-reloc");
    let out = compile(
        &dir,
        ARM_DANGLING_HELPER,
        "a.o",
        &[
            "-b",
            "arm",
            "-t",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
        ],
    );
    assert_refusal(&out, &dir, "a.o", "'f' -> 'func_1'", "GI-FPU-002");
}

/// RED on the unfixed binary: WITHOUT `--relocatable` the dangling reloc
/// counted as an external reference and silently flipped the output to
/// ET_REL — same unlinkable object, one more surprise. Refuses now.
#[test]
fn arm_thumb2_default_refuses() {
    let dir = workdir("arm-default");
    let out = compile(
        &dir,
        ARM_DANGLING_HELPER,
        "a2.o",
        &["-b", "arm", "-t", "cortex-m3", "--all-exports"],
    );
    assert_refusal(&out, &dir, "a2.o", "'f' -> 'func_1'", "GI-FPU-002");
}

/// RED on the unfixed binary: A32 (cortex-r5) refuses too — the fix is one
/// backend-agnostic gate, not a per-backend patch.
#[test]
fn a32_cortex_r5_refuses() {
    let dir = workdir("a32");
    let out = compile(
        &dir,
        ARM_DANGLING_HELPER,
        "r.o",
        &[
            "-b",
            "arm",
            "-t",
            "cortex-r5",
            "--all-exports",
            "--relocatable",
        ],
    );
    assert_refusal(&out, &dir, "r.o", "'f' -> 'func_1'", "GI-FPU-002");
}

/// NEGATIVE CONTROL (exit 0 on BOTH the unfixed and fixed binary): the same
/// decline with NO retained reference stays a routine corpus-sweep skip —
/// object emitted. Protects against the inverse failure: a guard drawn so
/// wide it refuses every module containing a decline, converting working
/// compiles into refusals ("we got stricter" hiding "we broke reach").
#[test]
fn decline_without_reference_still_exits_zero_rv32() {
    let dir = workdir("ctrl-rv32");
    let mut args = RV32.to_vec();
    args.push("--allow-skipped-exports");
    let out = compile(&dir, DECLINE_WITHOUT_REFERENCE, "c.o", &args);
    let err = stderr(&out);
    assert!(
        err.contains("skipping function 'big'"),
        "control must actually exercise a decline to mean anything.\nstderr:\n{err}"
    );
    assert_eq!(
        out.status.code(),
        Some(0),
        "a decline with no dangling reference must stay a routine exit-0 \
         skip.\nstderr:\n{err}"
    );
    assert!(dir.join("c.o").exists(), "control object was not emitted");
}

/// NEGATIVE CONTROL, ARM leg: same property on Thumb-2.
#[test]
fn decline_without_reference_still_exits_zero_arm() {
    let dir = workdir("ctrl-arm");
    let out = compile(
        &dir,
        DECLINE_WITHOUT_REFERENCE,
        "c.o",
        &[
            "-b",
            "arm",
            "-t",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
            "--allow-skipped-exports",
        ],
    );
    let err = stderr(&out);
    // On ARM the big-offset function COMPILES (no decline) — so this control
    // asserts the plain no-skip path is untouched instead.
    assert_eq!(
        out.status.code(),
        Some(0),
        "ARM control must stay exit 0.\nstderr:\n{err}"
    );
    assert!(dir.join("c.o").exists(), "control object was not emitted");
}
