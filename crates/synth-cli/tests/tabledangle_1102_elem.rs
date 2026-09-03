//! RQ-62-TABLEDANGLE (#1102 residual) — a DECLINED function reachable ONLY
//! through the funcref TABLE must fail the compile loudly on every backend.
//!
//! #1102's fix matches relocation symbols against the skipped function's
//! index labels, which is complete for DIRECT calls (verified in #1116). An
//! `elem` segment naming a declined function puts it in the table with NO
//! direct call site, so no relocation carries its index label and the #1102
//! gate sees nothing.
//!
//! Measured red-first on the UNFIXED binary (main @ b552fb4c, v0.61), with
//! the fixture below (`$bad` declines everywhere via a v128 op the decoder
//! loud-marks; a DYNAMIC-index `call_indirect` so the dispatch cannot be
//! devirtualized — with `i32.const 0` the ARM relocatable path folds the
//! dispatch to a direct call and the table never materializes):
//!
//! | path                          | exit | object | notes                          |
//! |-------------------------------|------|--------|--------------------------------|
//! | ARM Thumb-2 `--relocatable`   | 0    | ships  | links CLEAN (`arm-none-eabi-ld`|
//! |                               |      |        | exit 0) — no symbol at all for |
//! |                               |      |        | the declined slot; the R11     |
//! |                               |      |        | table region is embedder-      |
//! |                               |      |        | populated and slot 1 is        |
//! |                               |      |        | UNPOPULATABLE (code in no      |
//! |                               |      |        | object). THE LIVE HOLE.        |
//! | A32 cortex-r5 `--relocatable` | 0    | ships  | identical shape                |
//! | ARM `--cortex-m` (self-cont.) | 1    | none   | #275 broken-dispatch-table bail|
//! | RV32 (esp32c3/rv32imac)       | 1    | none   | `call_indirect` itself declines|
//! |                               |      |        | -> export skipped -> #952      |
//! | aarch64                       | 1    | none   | substrate table's `b func_N`   |
//! |                               |      |        | reloc hits the ELF builder's   |
//! |                               |      |        | #851/#1013 refusal             |
//!
//! The fix is a driver-level gate beside the #1102 one (the site where
//! `skipped_funcs`, `compiled_funcs` and the decoded funcref slots already
//! meet for all four backends): a RETAINED function performing
//! `call_indirect` + a funcref slot naming a skipped function refuses the
//! compile. It stands DOWN on the self-contained path, whose image builder's
//! #275 slot bail is pinned by `call_indirect_275_selfcontained.rs`; on
//! aarch64 it fires before the builder, whose #851 refusal stays as
//! defense-in-depth (the same layering as the direct-call class). It is
//! scoped to a retained dispatch: a skipped elem target in a module whose
//! compiled code never dispatches is the ordinary partial-object skip.
//!
//! NOT widened speculatively: the gate keys on the decoded funcref-slot
//! image (`funcref_region_slots`) and the wasm op stream, not on any new
//! relocation-label pattern — so the #1116 "direct-call relocations are
//! always index-labelled" completeness claim is neither reused nor extended.

use std::path::PathBuf;
use std::process::{Command, Output};

fn synth() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_synth"))
}

fn workdir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("synth-1102-elem-{tag}"));
    std::fs::create_dir_all(&d).expect("temp dir");
    d
}

/// The red-first shape: `$bad` is in the table (slot 1) with NO direct call
/// site, and declines on EVERY backend (the decoder marks the v128 op, each
/// backend refuses the marked function). The dispatch index is a runtime
/// parameter so no path can devirtualize the `call_indirect` away.
const ELEM_DECLINED_DYN: &str = r#"(module
  (type $t (func (result i32)))
  (table 2 funcref)
  (func $good (type $t) i32.const 7)
  (func $bad (type $t)
    v128.const i64x2 0 0
    i64x2.extract_lane 0
    i32.wrap_i64)
  (func (export "run") (param i32) (result i32)
    local.get 0
    call_indirect (type $t))
  (elem (i32.const 0) $good $bad))
"#;

/// Negative control: identical shape, every table function compiles.
const ELEM_ALL_GOOD: &str = r#"(module
  (type $t (func (result i32)))
  (table 2 funcref)
  (func $good (type $t) i32.const 7)
  (func $also_good (type $t) i32.const 9)
  (func (export "run") (param i32) (result i32)
    local.get 0
    call_indirect (type $t))
  (elem (i32.const 0) $good $also_good))
"#;

/// Precision control: a declined function EXISTS and a retained dispatch
/// EXISTS, but the declined function is NOT in the table — the gate must not
/// fire (under `--allow-skipped-exports`, the declined export is a routine
/// partial-object skip).
const DECLINED_NOT_IN_TABLE: &str = r#"(module
  (type $t (func (result i32)))
  (table 1 funcref)
  (func $good (type $t) i32.const 7)
  (func (export "bad") (type $t)
    v128.const i64x2 0 0
    i64x2.extract_lane 0
    i32.wrap_i64)
  (func (export "run") (param i32) (result i32)
    local.get 0
    call_indirect (type $t))
  (elem (i32.const 0) $good))
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

/// The refusal contract for the table class: the decline anchor fired (so
/// the assertions judge THIS defect), the exit is the clean-error 1, the
/// reason names the class and the dead slot, and no object is left behind.
fn assert_table_refusal(out: &Output, dir: &std::path::Path, out_name: &str) {
    let err = stderr(out);
    assert!(
        err.contains("skipping function 'func_1'") && err.contains("#680"),
        "fixture no longer trips the v128 decline this test depends on — \
         premise gone, revisit rather than pass on some other error.\nstderr:\n{err}"
    );
    assert_eq!(
        out.status.code(),
        Some(1),
        "expected the clean refusal (exit 1); 0 means an object with an \
         unpopulatable dispatch table was shipped, 101 means a panic.\nstderr:\n{err}"
    );
    assert!(
        !err.contains("panicked at") && !err.contains("RUST_BACKTRACE"),
        "refusal was delivered via panic, not a clean error.\nstderr:\n{err}"
    );
    assert!(
        err.contains("RQ-62-TABLEDANGLE") && err.contains("slot 1 -> function 1"),
        "refusal must name the table class and the dead slot.\nstderr:\n{err}"
    );
    assert!(
        !dir.join(out_name).exists(),
        "refused compile still wrote an output object"
    );
}

/// RED on the unfixed binary (exit 0, object shipped, linked clean with the
/// declined function's code in no object): ARM Thumb-2 `--relocatable`.
#[test]
fn arm_thumb2_relocatable_refuses_table_dangle() {
    let dir = workdir("arm-rel");
    let out = compile(
        &dir,
        ELEM_DECLINED_DYN,
        "a.o",
        &["--target", "cortex-m3", "--relocatable"],
    );
    assert_table_refusal(&out, &dir, "a.o");
}

/// RED on the unfixed binary (identical shape to Thumb-2): A32 cortex-r5.
#[test]
fn a32_cortex_r5_relocatable_refuses_table_dangle() {
    let dir = workdir("a32-rel");
    let out = compile(
        &dir,
        ELEM_DECLINED_DYN,
        "r.o",
        &["--target", "cortex-r5", "--relocatable"],
    );
    assert_table_refusal(&out, &dir, "r.o");
}

/// `--allow-skipped-exports` must NOT waive the refusal — that flag accepts
/// a PARTIAL object, not one whose dispatch table cannot be populated.
#[test]
fn allow_skipped_exports_does_not_waive_table_refusal() {
    let dir = workdir("arm-rel-waive");
    let out = compile(
        &dir,
        ELEM_DECLINED_DYN,
        "w.o",
        &[
            "--target",
            "cortex-m3",
            "--relocatable",
            "--allow-skipped-exports",
        ],
    );
    assert_table_refusal(&out, &dir, "w.o");
}

/// aarch64 already refused (the substrate table's `b func_N` trampoline hit
/// the ELF builder's #851/#1013 refusal, exit 1); the driver gate now fires
/// first with the uniform message, the builder refusal staying as
/// defense-in-depth. This leg pins the driver gate; a fall-through to the
/// builder message would mean the gate stopped covering aarch64.
#[test]
fn aarch64_refuses_table_dangle_at_driver() {
    let dir = workdir("a64");
    let out = compile(&dir, ELEM_DECLINED_DYN, "a64.o", &["-b", "aarch64"]);
    assert_table_refusal(&out, &dir, "a64.o");
}

/// RV32's table path is unreachable UPSTREAM: `call_indirect` itself is a
/// loud per-function decline, so the dispatching export is skipped and #952
/// exits non-zero. This leg pins that upstream guard BIDIRECTIONALLY — if
/// RV32 ever gains `call_indirect`, the #952 anchor disappears and this test
/// goes red, forcing the table-dangle question to be re-answered for RV32
/// rather than silently inheriting an unverified "covered".
#[test]
fn rv32_upstream_call_indirect_decline_guards_table_path() {
    let dir = workdir("rv32");
    let out = compile(
        &dir,
        ELEM_DECLINED_DYN,
        "rv.o",
        &["-b", "riscv", "--target", "esp32c3", "--relocatable"],
    );
    let err = stderr(&out);
    assert!(
        err.contains("skipping function 'run'") && err.contains("CallIndirect"),
        "RV32 no longer declines call_indirect — the table-dangle gate's \
         RV32 coverage rested on this upstream decline; re-verify the table \
         path red-first before trusting it.\nstderr:\n{err}"
    );
    assert_eq!(
        out.status.code(),
        Some(1),
        "expected #952 to refuse the skipped export.\nstderr:\n{err}"
    );
    assert!(
        err.contains("#952"),
        "expected the #952 gate.\nstderr:\n{err}"
    );
    assert!(
        !dir.join("rv.o").exists(),
        "refused compile still wrote an output object"
    );
}

/// The self-contained path keeps its own pinned refusal: the cortex-m image
/// builder's #275 broken-dispatch-table bail (the driver gate stands down
/// there so the slot-precise, test-pinned message is preserved).
#[test]
fn arm_selfcontained_keeps_275_bail() {
    let dir = workdir("arm-sc");
    let out = compile(
        &dir,
        ELEM_DECLINED_DYN,
        "sc.elf",
        &["--cortex-m", "--target", "cortex-m3"],
    );
    let err = stderr(&out);
    assert_eq!(out.status.code(), Some(1), "stderr:\n{err}");
    assert!(
        err.contains("refusing to link a broken dispatch table"),
        "the self-contained path must keep its #275 bail.\nstderr:\n{err}"
    );
    assert!(!dir.join("sc.elf").exists());
}

/// Negative control: every table function compiles — all paths that accepted
/// the module before the gate still accept it.
#[test]
fn all_good_table_still_compiles() {
    for (tag, args) in [
        (
            "good-arm-rel",
            &["--target", "cortex-m3", "--relocatable"][..],
        ),
        ("good-a64", &["-b", "aarch64"][..]),
        ("good-arm-sc", &["--cortex-m", "--target", "cortex-m3"][..]),
    ] {
        let dir = workdir(tag);
        let out = compile(&dir, ELEM_ALL_GOOD, "g.elf", args);
        let err = stderr(&out);
        assert_eq!(
            out.status.code(),
            Some(0),
            "control module must still compile ({tag}).\nstderr:\n{err}"
        );
        assert!(
            dir.join("g.elf").exists(),
            "control object was not emitted ({tag})"
        );
    }
}

/// Precision control: a decline + a retained dispatch, but the declined
/// function is NOT in the table — the gate must not fire.
#[test]
fn declined_function_outside_table_does_not_trip_gate() {
    let dir = workdir("outside");
    let out = compile(
        &dir,
        DECLINED_NOT_IN_TABLE,
        "o.o",
        &[
            "--target",
            "cortex-m3",
            "--relocatable",
            "--allow-skipped-exports",
        ],
    );
    let err = stderr(&out);
    assert!(
        err.contains("skipping function 'bad'"),
        "control's decline premise gone.\nstderr:\n{err}"
    );
    assert_eq!(
        out.status.code(),
        Some(0),
        "a declined function outside the table must stay a routine \
         partial-object skip.\nstderr:\n{err}"
    );
    assert!(dir.join("o.o").exists(), "control object was not emitted");
}
