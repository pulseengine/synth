//! #503-i64 + #587 — direct-selector i64 completeness guards.
//!
//! Two honest-skip classes closed end-to-end:
//!
//! * **#503-i64**: any 64-bit (i64/f64) param AAPCS-passed on the STACK (past
//!   R3, or even-align-spilled) used to loud-skip the whole function
//!   ("#518/#503: an i64/f64 param is AAPCS-passed past R3"). The width-aware
//!   `aapcs_param_layout` incoming homing now lowers every shape in
//!   `scripts/repro/i64_stack_param_503.wat` (falcon func_58/func_163/func_164
//!   class).
//! * **#587**: an i64-dense function whose simultaneous pair spills exceed the
//!   fixed 8-slot pool used to loud-skip ("i64 spill-slot pool exhausted" —
//!   falcon func_60/func_73). The backend's `pool-grow` recovery retry now
//!   reruns the full ladder with the pool sized from the operand-stack-depth
//!   bound — strictly LAST, after the #474 promotion-off fallback, so every
//!   function that compiled before is produced by exactly the old path
//!   (`promotion_never_causes_compile_failure_474` + the frozen byte gate
//!   prove bit-identity).
//!
//! Execution correctness (vs wasmtime under unicorn) is gated by
//! `scripts/repro/i64_stack_param_503_differential.py` and
//! `scripts/repro/i64_spill_pool_587_differential.py`; these tests pin the
//! compile-side contract: no skips, and #587 lands on the pool-grow rung.

use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join(name)
}

fn compile(wat: &str, out: &str, extra_env: &[(&str, &str)]) -> std::process::Output {
    let mut cmd = Command::new(synth());
    for (k, v) in extra_env {
        cmd.env(k, v);
    }
    cmd.args([
        "compile",
        fixture(wat).to_str().unwrap(),
        "-o",
        out,
        "-b",
        "arm",
        "--target",
        "cortex-m4",
        "--relocatable",
        "--all-exports",
    ])
    .output()
    .expect("failed to run synth")
}

/// #503-i64: every previously-declined i64-stack-param shape compiles — zero
/// skipped functions in the fixture.
#[test]
fn i64_stack_param_shapes_compile_without_skips_503() {
    let out = compile("i64_stack_param_503.wat", "/tmp/cli_503.o", &[]);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "compile failed:\n{stderr}");
    assert!(
        !stderr.contains("skipping function"),
        "an i64-stack-param shape was skipped (the #503-i64 class regressed):\n{stderr}"
    );
}

/// #587: the pool-exhausting i64-dense function compiles, and it does so on
/// the `pool-grow` recovery rung (not by accident on an earlier rung — that
/// would make this test vacuous as a pool-grow guard).
#[test]
fn i64_spill_pool_exhaustion_rescued_by_pool_grow_587() {
    let out = compile(
        "i64_spill_pool_587.wat",
        "/tmp/cli_587.o",
        &[("SYNTH_RECOVERY_STATS", "1")],
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "compile failed:\n{stderr}");
    assert!(
        !stderr.contains("skipping function"),
        "the i64-dense function was skipped (the #587 pool-grow rung regressed):\n{stderr}"
    );
    assert!(
        stderr.contains("rung=pool-grow result=ok"),
        "expected the pool-grow rung to produce the result (recovery stats):\n{stderr}"
    );
}
