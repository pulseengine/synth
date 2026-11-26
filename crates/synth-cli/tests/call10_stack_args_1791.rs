//! Refs #1785 — the CALL10 regression (#1791).
//!
//! `caller` passes ten i32 arguments to a local callee: its own param plus
//! nine constants. Ten values outlive the nine allocatable registers, so one is
//! spilled while the constants are materialized. The #1785 lane made a
//! spilled argument's reload avoid every register an already-popped argument
//! holds; with nine popped arguments live nothing was left, and the compile
//! refused `caller` with "register exhaustion" (#952 exit). The six stack
//! arguments are now stored to their outgoing slots before that reload, which
//! frees their registers.
//!
//! Executed against wasmtime by `scripts/repro/stack_args_503_differential.py`
//! (the CALL10 case); this test pins that the compile is accepted. `SYNTH` may
//! name another binary (e.g. a pre-fix one, to see it red).

use std::path::PathBuf;
use std::process::Command;

const CALL10: &str = r#"(module
  (func $callee (param i32 i32 i32 i32 i32 i32 i32 i32 i32 i32) (result i32)
    local.get 0 local.get 4 i32.add local.get 9 i32.add local.get 5 i32.sub)
  (func (export "caller") (param i32) (result i32)
    local.get 0
    i32.const 10 i32.const 20 i32.const 30 i32.const 40
    i32.const 50 i32.const 60 i32.const 70 i32.const 80 i32.const 90
    call $callee))"#;

#[test]
fn ten_arg_call_with_a_spilled_argument_compiles_1791() {
    let synth = std::env::var_os("SYNTH")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_BIN_EXE_synth")));
    let dir = std::env::temp_dir().join(format!("synth-1791-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let src = dir.join("call10.wat");
    std::fs::write(&src, CALL10).unwrap();
    let obj = dir.join("call10.o");
    let out = Command::new(&synth)
        .arg("compile")
        .arg(&src)
        .args([
            "--target",
            "cortex-m4",
            "--all-exports",
            "--relocatable",
            "-o",
        ])
        .arg(&obj)
        .output()
        .expect("run synth");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success() && !err.contains("skipping function"),
        "CALL10 must compile with `caller` emitted (#1791): {err}"
    );
}
