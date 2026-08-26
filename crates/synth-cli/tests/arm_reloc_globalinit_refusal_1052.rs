//! RQ-59-GLOBALINIT (#1052) — the ARM plain relocatable path must REFUSE a
//! module whose global INITIALIZERS it does not materialize.
//!
//! Pre-fix behaviour (the filed bug): `(global (mut i32) (i32.const 42))`
//! plus a `global.get` export compiled exit-0 on `--relocatable` to an
//! object whose entire text is `push; ldr.w r0,[r9]; pop` — 0x2A appears
//! NOWHERE in the ELF. wasmtime returns 42; synth returns whatever the
//! embedder happened to leave at R9. This is OUTSIDE the documented embedder
//! contract: the contract reserves R9 as the globals-table BASE
//! (`select_with_stack.rs`: "Load global value from globals table (R9 =
//! globals base)"), and no sentence anywhere assigns initializer EVALUATION
//! to the embedder — in explicit contrast to the data-segment sentence
//! ("the embedder populates its init segments") that made #1041 a
//! refusal-with-flag rather than a miscompile. Every other path ships the
//! inits (`--native-pointer-abi` #237, aarch64 #851), materializes them at
//! reset (self-contained, #649 — which treated exactly this class as a BUG
//! there), or loud-skips (RV32, #643). The plain relocatable path alone did
//! none of the three.
//!
//! The assertion here is deliberately about the REFUSAL — a clean non-zero
//! exit plus a reason string naming the global initializers — and NOT about
//! the absence of the initializer bytes from the object. Absence was already
//! true on the broken behaviour and would make this test vacuously green;
//! that same weaker-property shape (the #643 harness's "zeroed globals table
//! (inits are 0)" fixture) is exactly how this bug survived.
//!
//! `--embedder-global-init` is the explicit escape hatch (the #952 /
//! #1041 `--embedder-data-init` shape): it declares the embedder evaluates
//! the module's global initializers and seeds the R9 table before any export
//! runs — and changes no emitted byte.
//!
//! Materializing the initializers on this path is capability work
//! (v0.60, alongside VCR-REACH-002), not this fix.

use std::path::PathBuf;
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

/// Write an inline wat to a temp file and return its path.
fn wat_file(name: &str, wat: &str) -> PathBuf {
    let dir = std::env::temp_dir().join("synth_globalinit_1052_tests");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let p = dir.join(name);
    std::fs::write(&p, wat).expect("write wat");
    p
}

fn out_path(input: &std::path::Path, extra: &[&str]) -> PathBuf {
    std::env::temp_dir()
        .join("synth_globalinit_1052_tests")
        .join(format!(
            "{}_{}.o",
            input.file_stem().unwrap().to_str().unwrap(),
            extra.join("").replace(['-', '/', ' '], "")
        ))
}

fn compile(input: &std::path::Path, extra: &[&str]) -> std::process::Output {
    let out = out_path(input, extra);
    let mut args = vec![
        "compile",
        input.to_str().unwrap(),
        "--all-exports",
        "-o",
        out.to_str().unwrap(),
    ];
    args.extend_from_slice(extra);
    Command::new(synth())
        .args(&args)
        .output()
        .expect("run synth")
}

fn stderr(out: &std::process::Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

/// A refusal must be loud AND precise: non-zero exit + a reason naming the
/// global initializers (the multi_memory_406 house rule).
fn assert_refused(out: &std::process::Output, must_mention: &[&str], ctx: &str) {
    assert!(
        !out.status.success(),
        "{ctx}: expected a loud refusal, got success (exit 0 is the #1052 \
         silent-drop bug).\nstderr: {}",
        stderr(out)
    );
    let err = stderr(out);
    for needle in must_mention {
        assert!(
            err.contains(needle),
            "{ctx}: refusal does not mention '{needle}'.\nstderr: {err}"
        );
    }
}

/// The filed repro: a nonzero `i32.const` initializer on a defined global,
/// compiled `--relocatable` for a Thumb-2 target. Must refuse loudly.
#[test]
fn nonzero_i32_global_init_on_relocatable_refuses_loudly() {
    let f = wat_file(
        "nonzero_i32_init.wat",
        r#"(module
      (global $g (mut i32) (i32.const 42))
      (func (export "get") (result i32) global.get $g))"#,
    );
    let out = compile(&f, &["--relocatable", "--target", "cortex-m4"]);
    assert_refused(
        &out,
        &["global initializer", "#1052"],
        "nonzero i32 global init on --relocatable",
    );
}

/// Same class on the A32 (cortex-r5) relocatable path — the guard is
/// per-path, not per-encoding.
#[test]
fn nonzero_i32_global_init_on_a32_relocatable_refuses_loudly() {
    let f = wat_file(
        "nonzero_i32_init_a32.wat",
        r#"(module
      (global $g (mut i32) (i32.const 42))
      (func (export "get") (result i32) global.get $g))"#,
    );
    let out = compile(&f, &["--relocatable", "--target", "cortex-r5"]);
    assert_refused(
        &out,
        &["global initializer", "#1052"],
        "nonzero i32 global init on cortex-r5 --relocatable",
    );
}

/// A nonzero `i64.const` initializer — BOTH words dropped pre-fix (#649's
/// self-contained sibling). Must refuse on the relocatable path.
#[test]
fn nonzero_i64_global_init_on_relocatable_refuses_loudly() {
    let f = wat_file(
        "nonzero_i64_init.wat",
        r#"(module
      (global $c (mut i64) (i64.const 0x123456789ABCDEF0))
      (func (export "get_lo") (result i32)
        (i32.wrap_i64 (global.get $c))))"#,
    );
    let out = compile(&f, &["--relocatable", "--target", "cortex-m4"]);
    assert_refused(
        &out,
        &["global initializer", "#1052"],
        "nonzero i64 global init on --relocatable",
    );
}

/// An integer global whose init expr is NOT a compile-time constant
/// (`global.get` of an imported global) decodes to `init: None` — the value
/// cannot be proven zero, so shipping a zero-implied slot is the same
/// silent-drop class. Must refuse.
#[test]
fn nonconst_int_global_init_on_relocatable_refuses_loudly() {
    let f = wat_file(
        "nonconst_init.wat",
        r#"(module
      (import "env" "base" (global $base i32))
      (global $g (mut i32) (global.get $base))
      (func (export "get") (result i32) global.get $g))"#,
    );
    let out = compile(&f, &["--relocatable", "--target", "cortex-m4"]);
    assert_refused(
        &out,
        &["global initializer", "#1052"],
        "non-const integer global init on --relocatable",
    );
}

/// An external function import forces ET_REL even WITHOUT `--relocatable` —
/// the same builder runs, so the same silent drop happened there. Must
/// refuse too.
#[test]
fn nonzero_global_init_on_import_forced_etrel_refuses_loudly() {
    let f = wat_file(
        "nonzero_init_import.wat",
        r#"(module
      (import "env" "ext" (func $ext (param i32) (result i32)))
      (global $g (mut i32) (i32.const 42))
      (func (export "get") (result i32) global.get $g call $ext))"#,
    );
    let out = compile(&f, &["--target", "cortex-m4"]);
    assert_refused(
        &out,
        &["global initializer", "#1052"],
        "nonzero global init on import-forced ET_REL",
    );
}

/// `--native-pointer-abi` with NO linear memory: the `__synth_globals`
/// region is never emitted (`linear_memory_bytes == 0`), so the nonzero
/// init does not reach the object there either — the same guard must catch
/// it (pre-fix the object shipped an UNDEFINED `__synth_globals` and no
/// init image). The guard's predicate is "do the initializers actually
/// materialize", not "which flag was passed".
#[test]
fn native_pointer_abi_without_memory_refuses_loudly() {
    let f = wat_file(
        "npa_nomem.wat",
        r#"(module
      (global $g (mut i32) (i32.const 42))
      (func (export "get") (result i32) global.get $g))"#,
    );
    let out = compile(
        &f,
        &[
            "--relocatable",
            "--native-pointer-abi",
            "--target",
            "cortex-m4",
        ],
    );
    assert_refused(
        &out,
        &["global initializer", "#1052"],
        "nonzero global init on --native-pointer-abi without linear memory",
    );
}

/// `--embedder-global-init` is the explicit acknowledgment of the embedder
/// contract (the integrator instantiates the module, evaluates its global
/// initializers, and seeds the R9 table before any export runs). With it,
/// the same module compiles exit 0 — and the emitted object is
/// byte-identical to the object of a zero-init twin module compiled WITHOUT
/// the flag: the initializer value appears nowhere in either object, which
/// is precisely the contract the flag acknowledges (and the frozen-anchor
/// guarantee: the flag adds nothing to the object).
#[test]
fn embedder_global_init_flag_compiles_with_identical_object() {
    let flagged = wat_file(
        "nonzero_init_flagged.wat",
        r#"(module
      (global $g (mut i32) (i32.const 42))
      (func (export "get") (result i32) global.get $g))"#,
    );
    let flagged_extra = [
        "--relocatable",
        "--embedder-global-init",
        "--target",
        "cortex-m4",
    ];
    let out = compile(&flagged, &flagged_extra);
    assert!(
        out.status.success(),
        "--embedder-global-init must convert the refusal into the \
         acknowledged embedder contract.\nstderr: {}",
        stderr(&out)
    );

    let zero_twin = wat_file(
        "zero_init_twin.wat",
        r#"(module
      (global $g (mut i32) (i32.const 0))
      (func (export "get") (result i32) global.get $g))"#,
    );
    let twin_extra = ["--relocatable", "--target", "cortex-m4"];
    let out2 = compile(&zero_twin, &twin_extra);
    assert!(
        out2.status.success(),
        "zero-init twin must compile without any flag.\nstderr: {}",
        stderr(&out2)
    );

    let flagged_bytes = std::fs::read(out_path(&flagged, &flagged_extra)).expect("flagged object");
    let twin_bytes = std::fs::read(out_path(&zero_twin, &twin_extra)).expect("twin object");
    assert_eq!(
        flagged_bytes, twin_bytes,
        "--embedder-global-init object must be byte-identical to the \
         zero-init twin's object — the flag suppresses only the refusal and \
         the init value reaches no emitted byte (the acknowledged contract)"
    );
}

/// Green control against over-refusal: all-zero constant initializers still
/// compile with exit 0 — the #643 fixture shape (and every zeroed-scratch
/// harness) stays green, because a zeroed embedder table IS those modules'
/// correct initial state.
#[test]
fn zero_init_globals_on_relocatable_still_compile() {
    let f = wat_file(
        "zero_inits.wat",
        r#"(module
      (global $c (mut i64) (i64.const 0))
      (global $k (mut i32) (i32.const 0))
      (func (export "get32") (result i32) global.get $k)
      (func (export "get_lo") (result i32)
        (i32.wrap_i64 (global.get $c))))"#,
    );
    let out = compile(&f, &["--relocatable", "--target", "cortex-m4"]);
    assert!(
        out.status.success(),
        "zero-init globals on --relocatable must still compile.\nstderr: {}",
        stderr(&out)
    );
}

/// Green control: the self-contained Cortex-M image MATERIALIZES nonzero
/// initializers at reset (#649) — no refusal there, and the initializer
/// byte actually appears in the image (the non-vacuity anchor: this path
/// proves the same module is compilable when the inits genuinely ship).
#[test]
fn self_contained_path_still_materializes_nonzero_inits() {
    let f = wat_file(
        "nonzero_init_selfcontained.wat",
        r#"(module
      (memory 1)
      (global $g (mut i32) (i32.const 42))
      (func (export "get") (result i32) global.get $g))"#,
    );
    let extra = ["--target", "cortex-m4"];
    let out = compile(&f, &extra);
    assert!(
        out.status.success(),
        "self-contained path must still compile (it materializes inits at \
         reset, #649).\nstderr: {}",
        stderr(&out)
    );
    let bytes = std::fs::read(out_path(&f, &extra)).expect("object");
    assert!(
        bytes.windows(1).any(|w| w == [0x2A]),
        "self-contained image must carry the initializer byte 0x2A (#649)"
    );
}

/// Green control: `--native-pointer-abi` WITH a linear memory ships the
/// globals region as `.data` slots carrying the init values (#237) — no
/// refusal, and 0x2A is in the object.
#[test]
fn native_pointer_abi_with_memory_still_ships_inits() {
    let f = wat_file(
        "nonzero_init_npa.wat",
        r#"(module
      (memory 1)
      (global $g (mut i32) (i32.const 42))
      (func (export "get") (result i32) global.get $g))"#,
    );
    let extra = [
        "--relocatable",
        "--native-pointer-abi",
        "--target",
        "cortex-m4",
    ];
    let out = compile(&f, &extra);
    assert!(
        out.status.success(),
        "--native-pointer-abi with memory ships the globals region — must \
         not refuse.\nstderr: {}",
        stderr(&out)
    );
    let bytes = std::fs::read(out_path(&f, &extra)).expect("object");
    assert!(
        bytes.windows(1).any(|w| w == [0x2A]),
        "--native-pointer-abi object must carry the initializer byte (#237)"
    );
}

/// Green control: a FLOAT global's uncaptured initializer stays the
/// GI-FPU-001 (#369/#648) lane — float-global ACCESS loud-skips, and a
/// module whose exports never touch the float global must not be refused by
/// the #1052 guard (nothing in the emitted code can observe the slot).
#[test]
fn untouched_float_global_on_relocatable_still_compiles() {
    let f = wat_file(
        "float_global_untouched.wat",
        r#"(module
      (global $f (mut f32) (f32.const 1.5))
      (func (export "pure") (param i32) (result i32) local.get 0))"#,
    );
    let out = compile(&f, &["--relocatable", "--target", "cortex-m4"]);
    assert!(
        out.status.success(),
        "untouched float global must stay the GI-FPU-001 lane, not a #1052 \
         refusal.\nstderr: {}",
        stderr(&out)
    );
}
