//! #275 — self-contained `call_indirect`: emission + residual declines.
//!
//! The v0.42 #717 interim (loud-decline on the whole self-contained path) was
//! CONVERTED in v0.47: the Thumb-2 `--cortex-m` image path
//! (`build_multi_func_cortex_m_elf`) lowers `call_indirect` through a
//! flash-resident funcref table appended after the function code and
//! addressed PC-RELATIVE (an `LdrSym` literal-pool word against
//! `__synth_func_table`, patched post-layout) — NEVER via R11, the
//! linear-memory base the #717 collision corrupted. Execution (incl. the
//! §4.4.8 OOB / type-mismatch / null traps) is gated by
//! `scripts/repro/call_indirect_275_selfcontained_execution_differential.py`.
//!
//! This locks:
//!  1. self-contained `--cortex-m` (Thumb-2): the `call_indirect` function
//!     now EMITS (with the `#275 funcref table` diagnostic) alongside the
//!     other functions — no more #717 loud-skip;
//!  2. RESIDUAL: A32/Cortex-R5 self-contained still LOUD-declines with a
//!     `#275` diagnostic — its builder emits no funcref table, so a dispatch
//!     would be the silent R11 collision;
//!  3. `--relocatable`: the SAME module still emits `entry` with its guarded
//!     R11 dispatch — the host-linked path (a runtime places the table
//!     region at R11) is untouched (the #642/#650/#664/#676 oracles gate its
//!     bytes).

use std::process::Command;

use object::{Object, ObjectSymbol};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join("call_indirect_275_selfcontained.wat")
}

fn has_symbol(bytes: &[u8], name: &str) -> bool {
    let obj = object::File::parse(bytes).expect("parse object");
    obj.symbols().any(|s| s.name() == Ok(name))
}

/// #275 converted: the self-contained Thumb-2 `--cortex-m` image EMITS the
/// `call_indirect` function, dispatching through the flash-resident funcref
/// table (never R11).
#[test]
fn test_275_selfcontained_call_indirect_emits() {
    let path = fixture();
    let elf = "/tmp/ci275_selfcontained.elf";
    let out = Command::new(synth())
        .args([
            "compile",
            path.to_str().unwrap(),
            "--cortex-m",
            "--target",
            "cortex-m3",
            "-o",
            elf,
        ])
        .output()
        .expect("run synth");

    assert!(
        out.status.success(),
        "compile failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        !stderr.contains("skipping function 'entry'"),
        "entry must compile now (regression to the #717 loud-decline), got:\n{stderr}"
    );
    assert!(
        format!("{stdout}{stderr}").contains("#275 funcref table"),
        "the flash funcref table must be emitted (diagnostic missing), got:\n{stdout}\n{stderr}"
    );

    let bytes = std::fs::read(elf).expect("read elf");
    for f in ["entry", "func_1", "func_2", "func_3"] {
        assert!(
            has_symbol(&bytes, f),
            "{f} must be in the self-contained image (#275)"
        );
    }
}

/// RESIDUAL decline: A32/Cortex-R5 self-contained (not the cortex-m image
/// builder) still refuses `call_indirect` loudly — no funcref table is
/// emitted there, so a dispatch would be the #717 silent R11 collision.
#[test]
fn test_275_selfcontained_a32_still_declines_loudly() {
    let path = fixture();
    let elf = "/tmp/ci275_selfcontained_r5.elf";
    let out = Command::new(synth())
        .args([
            "compile",
            path.to_str().unwrap(),
            "--target",
            "cortex-r5",
            "-o",
            elf,
        ])
        .output()
        .expect("run synth");

    // The overall compile still succeeds (skip-and-continue), but the decline
    // is LOUD — the diagnostic names #275.
    assert!(
        out.status.success(),
        "compile should skip-and-continue: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("skipping function 'entry'"),
        "the A32 self-contained call_indirect must stay a LOUD skip, got:\n{stderr}"
    );
    assert!(
        stderr.contains("#275"),
        "the decline diagnostic must name #275, got:\n{stderr}"
    );
    assert!(
        stderr.contains("were skipped"),
        "the skip must be surfaced in the summary count, got:\n{stderr}"
    );
    let bytes = std::fs::read(elf).expect("read elf");
    assert!(
        !has_symbol(&bytes, "entry"),
        "`entry` must NOT be emitted on the A32 self-contained path — a \
         declined function is absent, not a silent colliding dispatch (#275)"
    );
}

/// RESIDUAL decline: a self-contained module with IMPORTED functions keeps
/// the loud #275 decline — imports force ET_REL output, whose host runtime
/// owns the R11 table region; the flash-table lowering must not fire there.
#[test]
fn test_275_selfcontained_with_imports_still_declines_loudly() {
    let wat = r#"(module
      (import "env" "ext" (func $ext (param i32) (result i32)))
      (memory 1)
      (type $un (func (param i32) (result i32)))
      (func $easy (type $un) (i32.add (local.get 0) (i32.const 1)))
      (func (export "go") (param i32 i32) (result i32)
        (call_indirect (type $un) (local.get 0) (local.get 1)))
      (table 1 funcref) (elem (i32.const 0) $easy))"#;
    let src = "/tmp/ci275_imports.wat";
    std::fs::write(src, wat).expect("write fixture");
    let out = Command::new(synth())
        .args([
            "compile",
            src,
            "--cortex-m",
            "--target",
            "cortex-m3",
            "-o",
            "/tmp/ci275_imports.elf",
        ])
        .output()
        .expect("run synth");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("skipping function 'go'") && stderr.contains("#275"),
        "a self-contained module WITH imports must keep the loud #275 \
         call_indirect decline (ET_REL output owns the table region), got:\n{stderr}"
    );
}

/// LOUD bail (never a silent zero-linked slot): a funcref-table slot whose
/// target function was loud-skipped (uncompilable) fails the whole compile
/// with a named error — linking 0 would silently turn a callable slot into a
/// trap.
#[test]
fn test_275_skipped_table_target_fails_loudly() {
    let wat = r#"(module
      (memory 1)
      (type $un (func (param i32) (result i32)))
      (func $hard (type $un)
        (i32.trunc_f64_s (f64.sqrt (f64.convert_i32_s (local.get 0)))))
      (func $easy (type $un) (i32.add (local.get 0) (i32.const 1)))
      (func (export "go") (param i32 i32) (result i32)
        (call_indirect (type $un) (local.get 0) (local.get 1)))
      (table 2 funcref) (elem (i32.const 0) $easy $hard))"#;
    let src = "/tmp/ci275_skiptarget.wat";
    std::fs::write(src, wat).expect("write fixture");
    let out = Command::new(synth())
        .args([
            "compile",
            src,
            "--cortex-m",
            "--target",
            "cortex-m3", // soft-float: the f64 target function loud-skips (#369)
            "-o",
            "/tmp/ci275_skiptarget.elf",
        ])
        .output()
        .expect("run synth");
    assert!(
        !out.status.success(),
        "a dispatch table with a skipped target must FAIL the compile, not \
         link a broken table"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("refusing to link a broken dispatch table"),
        "the failure must name the broken-table refusal (#275), got:\n{stderr}"
    );
}

/// The `--relocatable` (host-linked) path is UNTOUCHED: the same module still
/// emits `entry` with its guarded dispatch — the runtime places the R11 table
/// region there, so the dispatch is sound (the #642/#650/#664/#676 oracles
/// gate its exact bytes).
#[test]
fn test_275_relocatable_call_indirect_untouched() {
    let path = fixture();
    for target in ["cortex-m3", "cortex-r5"] {
        let elf = format!("/tmp/ci275_reloc_{target}.o");
        let out = Command::new(synth())
            .args([
                "compile",
                path.to_str().unwrap(),
                "--target",
                target,
                "--all-exports",
                "--relocatable",
                "--no-optimize",
                "-o",
                &elf,
            ])
            .output()
            .expect("run synth");
        assert!(
            out.status.success(),
            "relocatable compile failed ({target}): {}",
            String::from_utf8_lossy(&out.stderr)
        );
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            !stderr.contains("skipping function 'entry'"),
            "relocatable path must NOT decline entry ({target}):\n{stderr}"
        );
        let bytes = std::fs::read(&elf).expect("read object");
        assert!(
            has_symbol(&bytes, "entry"),
            "relocatable path must still emit `entry` with its dispatch ({target}) — #275 \
             must not touch the host-linked path"
        );
    }
}
