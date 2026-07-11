//! #275 — the self-contained `--cortex-m` `call_indirect` silent-miscompile
//! close (outcome B: loud decline).
//!
//! The self-contained image path (`build_multi_func_cortex_m_elf`, i.e. no
//! `--relocatable`) has no runtime to populate the contiguous R11 funcref-table
//! region — R11 is the linear-memory base — so the guarded dispatch would load
//! function pointers from linear-memory DATA (a silent miscompile: `entry`
//! compiled to `exit 0, 0 skips` but stored garbage). Until the dedicated
//! func-table fix (silicon-gated) lands, the self-contained path DECLINES
//! `call_indirect` LOUDLY (AFD-008: an unlowerable op must `Err`, never
//! silently continue).
//!
//! This locks:
//!  1. self-contained: the `call_indirect` function is LOUD-skipped (a `#275`
//!     diagnostic + a skip count) and is ABSENT from the output — no silent
//!     colliding dispatch is emitted; the non-`call_indirect` functions still
//!     compile;
//!  2. `--relocatable`: the SAME module still emits `entry` with its guarded
//!     dispatch — the host-linked path (a runtime places the table region at
//!     R11) is untouched (the #642/#650/#664/#676 oracles gate its bytes).

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

/// Outcome B: self-contained `--cortex-m` DECLINES `call_indirect` loudly —
/// the function is skipped (named, counted) and absent from the ELF, never a
/// silent colliding dispatch.
#[test]
fn test_275_selfcontained_call_indirect_declines_loudly() {
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

    // The overall compile still succeeds (skip-and-continue), but the decline
    // is LOUD — the diagnostic names #275 and the linear-memory collision.
    assert!(
        out.status.success(),
        "compile should skip-and-continue: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("skipping function 'entry'"),
        "the call_indirect function must be a LOUD skip, got:\n{stderr}"
    );
    assert!(
        stderr.contains("#275"),
        "the decline diagnostic must name #275, got:\n{stderr}"
    );
    assert!(
        stderr.contains("were skipped"),
        "the skip must be surfaced in the summary count, got:\n{stderr}"
    );

    // The declined function is ABSENT from the output — no silent dispatch.
    let bytes = std::fs::read(elf).expect("read elf");
    assert!(
        !has_symbol(&bytes, "entry"),
        "`entry` must NOT be emitted — a declined function is absent, not a \
         silent colliding dispatch (#275)"
    );
    // The non-call_indirect functions still compile (the decline is scoped to
    // the call_indirect function, not the whole module).
    for f in ["func_1", "func_2", "func_3"] {
        assert!(
            has_symbol(&bytes, f),
            "{f} must still compile — only the call_indirect function declines"
        );
    }
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
