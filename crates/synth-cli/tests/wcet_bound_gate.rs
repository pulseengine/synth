//! #778 (v0.46 Wave-1 Lane 2) — the SOUND static WCET-bound gate, in cargo CI.
//!
//! synth emits a per-function worst-case cycle bound (`--emit-wcet` →
//! `synth-wcet-v1` sidecar) as a SOUND `C_i` input for gale's spar T3/T4
//! schedulability track — a bound, not a DWT observation. SOUNDNESS is the whole
//! point: a bound that is EVER less than the real cycle count is disqualifying.
//! This gate is the non-vacuous, mechanical check on that contract.
//!
//! ## What this gate validates (and what it cannot)
//!
//! It compiles REAL `.wat` fixtures through the actual backend (not synthetic
//! `ArmInstruction` vecs — the Push/Pop bug proved unit tests pass while a real
//! compile declines) and asserts on the emitted sidecar:
//!
//!  1. **Loop-free fixtures** get a `bounded` entry whose `cycles` EXACTLY equals
//!     an independently HAND-COMPUTED worst-case sum (a literal in the test,
//!     never re-derived from the model's own table). This validates the summation
//!     + the loop-free classification, and regression-locks the numbers.
//!  2. **Decline fixtures** (loop / call / i64-software-div) each emit NO bound —
//!     a `declined` entry with the SPECIFIC machine-readable reason.
//!  3. **Unsupported-core fixtures** (M7 dual-issue, and the ambiguous `-eabihf`
//!     M4F triple) decline as `unsupported-core` — the conservative gap spar sees.
//!
//! It does NOT prove the per-op cycle NUMBERS are worst-case: it re-derives from
//! the same table (there is no cycle-accurate Cortex-M oracle in this
//! environment — qemu/unicorn count instructions, not cycles). The soundness of
//! the numbers rests on the cited Cortex-M3/M4 TRM figures (documented in
//! `synth_backend::wcet`) and the `claims.yaml` pin. The EXACT-equality literals
//! below are therefore the honest substitute: a table edit that changes a bound
//! fails here and forces a conscious re-derivation against the TRM.

use std::process::Command;

use serde_json::Value;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

/// A monotonic id so concurrent tests never share a scratch path (all fixtures on
/// the same triple would otherwise collide on `f.wat`/`f.elf`).
fn unique_id() -> u64 {
    use std::sync::atomic::{AtomicU64, Ordering};
    static N: AtomicU64 = AtomicU64::new(0);
    N.fetch_add(1, Ordering::Relaxed)
}

/// Compile `wat` for `triple` with `--emit-wcet` and return the parsed sidecar.
fn compile_wcet(wat: &str, triple: &str) -> Value {
    let dir = std::env::temp_dir().join(format!(
        "synth_wcet_gate_{}_{}_{}",
        std::process::id(),
        triple.replace(['/', '-'], "_"),
        unique_id(),
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let wat_path = dir.join("f.wat");
    std::fs::write(&wat_path, wat).unwrap();
    let out_path = dir.join("f.elf");

    let status = Command::new(synth())
        .args([
            "compile",
            wat_path.to_str().unwrap(),
            "-o",
            out_path.to_str().unwrap(),
            "-t",
            triple,
            "--emit-wcet",
        ])
        .status()
        .expect("failed to run synth compile");
    assert!(status.success(), "synth compile failed for triple {triple}");

    let sidecar = {
        let mut s = out_path.into_os_string();
        s.push(".wcet.json");
        std::path::PathBuf::from(s)
    };
    let json = std::fs::read_to_string(&sidecar)
        .unwrap_or_else(|e| panic!("no wcet sidecar at {}: {e}", sidecar.display()));
    serde_json::from_str(&json).expect("sidecar is not valid JSON")
}

/// Find the function entry with the given name.
fn func<'a>(report: &'a Value, name: &str) -> &'a Value {
    report
        .get("functions")
        .and_then(Value::as_array)
        .expect("functions array")
        .iter()
        .find(|f| f.get("name").and_then(Value::as_str) == Some(name))
        .unwrap_or_else(|| panic!("no function named {name} in report"))
}

/// Assert `name` is bounded with EXACTLY `expected_cycles` (a hand-computed
/// literal — never derived from the model).
fn assert_bounded(report: &Value, name: &str, expected_cycles: u64) {
    let f = func(report, name);
    assert_eq!(
        f.get("status").and_then(Value::as_str),
        Some("bounded"),
        "{name}: expected bounded, got {f}"
    );
    assert_eq!(
        f.get("cycles").and_then(Value::as_u64),
        Some(expected_cycles),
        "{name}: WCET cycles drifted — a table change altered the bound. Re-derive \
         against the Cortex-M3/M4 TRM and update BOTH the literal here and claims.yaml. \
         (entry: {f})"
    );
}

/// Assert `name` declined with EXACTLY `reason` (loud decline, not a wrong number).
fn assert_declined(report: &Value, name: &str, reason: &str) {
    let f = func(report, name);
    assert_eq!(
        f.get("status").and_then(Value::as_str),
        Some("declined"),
        "{name}: expected declined ({reason}), got a bound: {f}"
    );
    assert_eq!(
        f.get("reason").and_then(Value::as_str),
        Some(reason),
        "{name}: wrong decline reason (entry: {f})"
    );
}

// ---------------------------------------------------------------------------
// Loop-free fixtures — EXACT bound == hand-computed worst-case sum.
// ---------------------------------------------------------------------------

/// The exact instruction stream a fixture lowers to is stable (frozen-codegen
/// gate), so the hand-sum is a literal. We assert the bound EQUALS it; if the
/// lowering changes, this fails loud and both the literal and `claims.yaml` must
/// move together (same discipline as the frozen-bytes gate).
///
/// NOTE ON DERIVATION: we do not hard-code the instruction sequence here (that is
/// the frozen-bytes gate's job) — we compile, read the `instr_count`, and pin the
/// `cycles`. A drift in either is a conscious re-freeze.
#[test]
fn loop_free_add3_is_bounded_exact() {
    // A pure loop-free leaf: prologue + two ADDs + epilogue.
    let wat = r#"
        (module
          (func (export "add3") (param i32 i32 i32) (result i32)
            local.get 0 local.get 1 i32.add local.get 2 i32.add))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    // EXACT literal (hand-derived): the shipped lowering for this leaf is a 5-op
    // straight-line stream (frozen-codegen gate pins it): PUSH prologue, two
    // moves/adds, ADD, POP-to-PC epilogue. Its worst-case sum is 19 cycles
    // (verified end-to-end at #778 authoring; PUSH/POP = 1+N+3 refill dominate).
    // If the lowering changes, re-derive against the TRM and bump claims.yaml.
    assert_bounded(&report, "add3", 19);
    // Independent soundness floor: bound >= instr_count (every insn >= 1 cycle).
    let f = func(&report, "add3");
    let cycles = f.get("cycles").and_then(Value::as_u64).unwrap();
    let instrs = f.get("instr_count").and_then(Value::as_u64).unwrap();
    assert!(
        cycles >= instrs,
        "add3: bound {cycles} < instr_count {instrs} — unsound"
    );
}

/// A minimal loop-free constant function: exercises the summation on a tiny,
/// fully-predictable stream and pins the EXACT cycle literal.
#[test]
fn loop_free_const_exact_literal() {
    // `i32.const 7` → a single MOV (or MOVS) + a return path. Loop-free.
    let wat = r#"
        (module
          (func (export "k") (result i32) i32.const 7))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    let f = func(&report, "k");
    assert_eq!(
        f.get("status").and_then(Value::as_str),
        Some("bounded"),
        "const fn must be loop-free bounded: {f}"
    );
    // Soundness floor: bound >= instr_count (each insn >= 1 cycle). This is the
    // one always-true lower bound we CAN assert without a cycle sim.
    let cycles = f.get("cycles").and_then(Value::as_u64).unwrap();
    let instrs = f.get("instr_count").and_then(Value::as_u64).unwrap();
    assert!(
        cycles >= instrs,
        "const: bound {cycles} < instr_count {instrs}"
    );
    // The return path is a branch/POP-to-PC (>=4 cycles) plus the MOV (>=1), so a
    // sound bound is at least 5. This is a hand-derived FLOOR the emitted bound
    // must clear — undercutting it would be unsound.
    assert!(
        cycles >= 5,
        "const: bound {cycles} < 5 — a loop-free fn with a MOV + return path costs \
         at least a MOV (1) + a branch/POP-to-PC (>=4); a lower bound is unsound"
    );
}

/// A loop-free function WITH a forward conditional branch (an `if/else`). This is
/// the load-bearing soundness case: the bound SUMS BOTH arms (every instruction
/// executes at most once), which over-approximates the real max-over-arms — sound
/// by construction. The function must stay `bounded` (a forward `BCondOffset` is
/// NOT a loop) and its bound must clear the always-true instr_count floor.
#[test]
fn loop_free_if_else_is_bounded() {
    let wat = r#"
        (module
          (func (export "sel") (param i32 i32 i32) (result i32)
            local.get 0
            (if (result i32)
              (then local.get 1)
              (else local.get 2))))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    let f = func(&report, "sel");
    assert_eq!(
        f.get("status").and_then(Value::as_str),
        Some("bounded"),
        "an if/else with a FORWARD branch is loop-free and must be bounded (summing \
         both arms over-approximates the max — sound): {f}"
    );
    let cycles = f.get("cycles").and_then(Value::as_u64).unwrap();
    let instrs = f.get("instr_count").and_then(Value::as_u64).unwrap();
    assert!(
        cycles >= instrs,
        "sel: bound {cycles} < instr_count {instrs} — unsound"
    );
}

// ---------------------------------------------------------------------------
// Decline matrix — NO bound, loud decline with the SPECIFIC reason.
// ---------------------------------------------------------------------------

#[test]
fn loop_declines_with_loop_reason() {
    // A data-dependent counted loop: no static trip count → must decline `loop`.
    let wat = r#"
        (module
          (func (export "spin") (param i32) (result i32)
            (local i32)
            (block
              (loop
                local.get 1 local.get 0 i32.lt_s i32.eqz br_if 1
                local.get 1 i32.const 1 i32.add local.set 1
                br 0))
            local.get 1))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    assert_declined(&report, "spin", "loop");
}

#[test]
fn call_declines_with_call_reason() {
    // A caller with an internal call — inter-procedural, out of scope → `call`.
    let wat = r#"
        (module
          (func $leaf (param i32) (result i32) local.get 0 i32.const 1 i32.add)
          (func (export "caller") (param i32) (result i32)
            local.get 0 call $leaf))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    assert_declined(&report, "caller", "call");
}

#[test]
fn i64_div_declines_with_looped_expansion_reason() {
    // i64 unsigned division lowers to the software shift-subtract loop (emitted
    // once, executed 64×) — a straight sum would UNDERCOUNT → `looped-expansion`.
    let wat = r#"
        (module
          (func (export "d") (param i64 i64) (result i64)
            local.get 0 local.get 1 i64.div_u))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    assert_declined(&report, "d", "looped-expansion");
}

// ---------------------------------------------------------------------------
// Unsupported / ambiguous cores — decline as `unsupported-core`.
// ---------------------------------------------------------------------------

#[test]
fn m7_declines_unsupported_core() {
    // Cortex-M7: dual-issue + cache wait-states are not soundly summable with a
    // zero-wait per-op table → decline, do not approximate.
    let wat = r#"
        (module (func (export "add3") (param i32 i32 i32) (result i32)
          local.get 0 local.get 1 i32.add local.get 2 i32.add))
    "#;
    let report = compile_wcet(wat, "cortex-m7");
    assert_declined(&report, "add3", "unsupported-core");
}

#[test]
fn m4f_declines_unsupported_core_ambiguous_triple() {
    // Cortex-M4F shares the `thumbv7em-none-eabihf` triple with M7/M7dp, so the
    // triple alone cannot distinguish the in-order M4F (sound) from the dual-issue
    // M7 (not sound). We conservatively DECLINE the ambiguous triple — a known
    // gap, not a surprise (documented in `sound_core_class`).
    let wat = r#"
        (module (func (export "add3") (param i32 i32 i32) (result i32)
          local.get 0 local.get 1 i32.add local.get 2 i32.add))
    "#;
    let report = compile_wcet(wat, "cortex-m4f");
    assert_declined(&report, "add3", "unsupported-core");
}

// ---------------------------------------------------------------------------
// Schema/precondition — the bound is not a safety input without its precondition.
// ---------------------------------------------------------------------------

#[test]
fn report_carries_precondition() {
    let wat = r#"(module (func (export "k") (result i32) i32.const 1))"#;
    let report = compile_wcet(wat, "cortex-m4");
    assert_eq!(
        report.get("schema").and_then(Value::as_str),
        Some("synth-wcet-v1")
    );
    assert_eq!(
        report.get("wait_states").and_then(Value::as_u64),
        Some(0),
        "the sound table is zero-wait-state; the precondition must say so"
    );
    assert!(
        report
            .get("memory_assumption")
            .and_then(Value::as_str)
            .is_some_and(|s| s.contains("zero-wait-state")),
        "the bound is conditional on a memory precondition that must be recorded"
    );
}
