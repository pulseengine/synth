//! #921 — an `unmodeled-op` decline must NAME the op and its byte offset.
//!
//! gale ran `--emit-wcet` over a real 31-function object and got 9
//! `unmodeled-op` declines carrying only `{name, reason, note}`. That says the
//! cycle model has a hole and which FUNCTION fell in it, but not which
//! INSTRUCTION — so the only way forward was hand-bisecting the object. Every
//! other decline reason is actionable on its face (`loop` → prove a trip count,
//! `call` → an import, correctly); this one was not.
//!
//! ## Why this test runs the BINARY and not the library
//!
//! The first version of the fix threaded the site through `function_wcet` only,
//! which is NOT the path the CLI takes — the CLI goes through the composer
//! (`wcet_compose`). Every unit test on the patched path passed while every
//! real sidecar still emitted `op: null`. The end-to-end run is what caught it,
//! so the regression test is end-to-end too: it asserts on the JSON a consumer
//! actually receives.

use std::path::PathBuf;
use std::process::Command;

fn synth_binary() -> PathBuf {
    // Resolved by cargo, so this survives `cargo llvm-cov`'s relocated layout
    // (the #908 lesson: a two-`parent()`-hop walk yielded a nonexistent path
    // under coverage and held the whole job red).
    PathBuf::from(env!("CARGO_BIN_EXE_synth"))
}

/// `memory.size` lowers to `ArmOp::MemorySize`, which `op_cost` deliberately
/// leaves unclassified — the shortest local reproduction of gale's decline.
///
/// #936 RETARGET: this test originally reproduced the decline via `i64.load`
/// (`ArmOp::I64Ldr`). #936 priced `I64Const`/`I64Ldr`/`I64Str` (gale's actual 9
/// `unmodeled-op` declines on a real `gust:os` composite resolved to exactly
/// those two opcode FAMILIES), so `i64.load` no longer declines — exactly the
/// "good problem" this test's own non-vacuity check was written to catch (see
/// below), and the test moved to `i32.wrap_i64`.
///
/// RQ-59-WCETI64 RETARGET (second time, same rule): pricing the #936 audit's
/// residual four (`I32WrapI64`, `I64ExtendI32S`/`I64ExtendI32U`, `I64Sub`)
/// un-declined `i32.wrap_i64` too. Retargeted at `memory.size` — measured
/// STILL a live `unmodeled-op op=MemorySize` decline on the direct/relocatable
/// selector (probed alongside `f32.add`, which does not COMPILE on cortex-m4,
/// and the i64 binops/compares, which the selector expands to priced 32-bit
/// primitives before the WCET pass sees them). That asymmetry is exactly why
/// naming the op matters — the reason string alone cannot distinguish which of
/// the unclassified family a given function tripped over.
const FIXTURE: &str = r#"(module
  (memory 1)
  (func (export "f") (result i32)
    memory.size))
"#;

#[test]
fn unmodeled_op_decline_names_the_op_and_offset() {
    let dir = std::env::temp_dir().join("synth-wcet-921");
    std::fs::create_dir_all(&dir).expect("temp dir");
    let wat = dir.join("memory_size.wat");
    let obj = dir.join("memory_size.o");
    std::fs::write(&wat, FIXTURE).expect("write fixture");

    let out = Command::new(synth_binary())
        .args([
            "compile",
            wat.to_str().unwrap(),
            "-o",
            obj.to_str().unwrap(),
            "--target",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
            "--emit-wcet",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "compile failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let sidecar = PathBuf::from(format!("{}.wcet.json", obj.display()));
    let text = std::fs::read_to_string(&sidecar).expect("sidecar written");
    let doc: serde_json::Value = serde_json::from_str(&text).expect("sidecar is JSON");

    let declined: Vec<&serde_json::Value> = doc["functions"]
        .as_array()
        .expect("functions array")
        .iter()
        .filter(|f| f.get("reason").is_some())
        .collect();

    // NON-VACUITY: if the fixture ever stops declining (a good thing — it would
    // mean the cycle model grew to cover `MemorySize`), this test must FAIL
    // rather than pass over an empty set. A green assertion about no records is
    // the exact shape #890/#910 exist to reject. (#936: this is exactly what
    // happened to the ORIGINAL `i64.load` fixture, and RQ-59-WCETI64 repeated
    // it on the `i32.wrap_i64` retarget — retargeted again, not deleted; see
    // the FIXTURE doc comment above.)
    assert!(
        !declined.is_empty(),
        "fixture no longer declines — if `MemorySize` is now costed, retarget \
         this test at another unclassified op rather than deleting the assertion"
    );

    let d = declined
        .iter()
        .find(|f| f["reason"] == "unmodeled-op")
        .expect("the memory.size fixture declines `unmodeled-op`");

    assert_eq!(
        d["op"], "MemorySize",
        "the decline must NAME the op (#921); got {d}"
    );
    assert!(
        d["offset"].is_u64(),
        "the decline must carry a byte offset (#921); got {d}"
    );
}

/// The fields are ADDITIVE: a decline that names no specific op must not grow
/// null keys, or every existing consumer's schema check sees new fields.
#[test]
fn declines_without_a_site_do_not_emit_the_new_keys() {
    use synth_core::wcet::{WcetDecline, WcetFunction};

    let f = WcetFunction::declined("g", WcetDecline::Loop);
    let json = serde_json::to_string(&f).expect("serialize");
    assert!(
        !json.contains("\"op\""),
        "absent site must be OMITTED, not null: {json}"
    );
    assert!(
        !json.contains("\"offset\""),
        "absent site must be OMITTED, not null: {json}"
    );
}
