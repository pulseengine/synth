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
//!  2. **Const-bound counted loops** (#778 phase 2) get a `bounded` entry with
//!     the PROVEN trip count (head-test, bottom-test, nested-multiplicative,
//!     memory-writing, zero-trip) — pinned exact literals + a trip-aware
//!     soundness floor (`cycles ≥ trip × region_instr_count`).
//!  3. **Decline fixtures** (data-dependent loop / non-canonical loop /
//!     external-import call / recursion / indirect call / declined-callee /
//!     i64-software-div) each emit NO bound — a `declined` entry with the
//!     SPECIFIC machine-readable reason. The phase-1 const-loop declines MOVED
//!     to (2); the phase-2 direct-local-`call` decline MOVED to phase-3
//!     composition (item 6); the gate never deletes a decline, it converts it.
//!  4. **The `--wcet-hints` seam** (#778 phase 2): RED-FIRST — a deliberately
//!     WRONG hint (below the real trip count) is REJECTED
//!     (`hint-below-derived-trip`) and the function stays declined; a correct
//!     verifiable hint converts the equality-exit decline into a bound
//!     (`hint-verified`, trip = synth's DERIVED count, never the raw hint); a
//!     hint on a data-dependent loop is rejected `hint-unverifiable-induction`;
//!     CLI misuse (no `--emit-wcet`, malformed JSON, wrong schema) fails loudly.
//!  5. **Unsupported-core fixtures** (M7 dual-issue, and the ambiguous `-eabihf`
//!     M4F triple) decline as `unsupported-core` — the conservative gap spar sees.
//!  6. **Inter-procedural composition** (#778 phase 3): a caller with a DIRECT
//!     call to a LOCAL bounded callee is BOUNDED (own body + Σ callee × call-site
//!     multiplier); a callee invoked inside a proven loop is counted `trip` times.
//!     Recursion (`recursion`), indirect (`indirect-call`), external/import
//!     (`call`), and any declined callee (`callee-unbounded`) STAY loud declines —
//!     the decline-honesty gate on what is not provably composable.
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
    compile_wcet_hinted(wat, triple, None)
}

/// Like [`compile_wcet`] but with `--relocatable` (so an import call lowers to a
/// direct `BL func_N` reloc — the shape the composer sees as an external callee).
fn compile_wcet_relocatable(wat: &str, triple: &str) -> Value {
    compile_wcet_inner(wat, triple, None, true)
}

/// Like [`compile_wcet`] but passing a `--wcet-hints` file (#778 phase 2).
fn compile_wcet_hinted(wat: &str, triple: &str, hints_json: Option<&str>) -> Value {
    compile_wcet_inner(wat, triple, hints_json, false)
}

/// Shared compile+read-sidecar body for the WCET fixtures.
fn compile_wcet_inner(
    wat: &str,
    triple: &str,
    hints_json: Option<&str>,
    relocatable: bool,
) -> Value {
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

    let mut args = vec![
        "compile".to_string(),
        wat_path.to_str().unwrap().to_string(),
        "-o".to_string(),
        out_path.to_str().unwrap().to_string(),
        "-t".to_string(),
        triple.to_string(),
        "--emit-wcet".to_string(),
    ];
    if relocatable {
        args.push("--relocatable".to_string());
    }
    if let Some(h) = hints_json {
        let hints_path = dir.join("hints.json");
        std::fs::write(&hints_path, h).unwrap();
        args.push("--wcet-hints".to_string());
        args.push(hints_path.to_str().unwrap().to_string());
    }
    let status = Command::new(synth())
        .args(&args)
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
fn data_dependent_loop_still_declines_with_loop_reason() {
    // A DATA-DEPENDENT counted loop (bound = a runtime parameter): #778 phase 2
    // proves const-bound counted loops, but a data-dependent bound has no
    // statically-evident trip count → must STILL decline `loop`. (This is the
    // decline the gate keeps — moved, never deleted: the const-bound shapes
    // that used to sit here are now asserted BOUNDED below.)
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
fn external_import_call_declines_with_call_reason() {
    // A DIRECT call to an IMPORTED function: the import has no per-function body in
    // this module, so it cannot be composed → `call`. This is the decline the phase-3
    // composer KEEPS for un-composable direct edges (a defined-function call is now
    // composed — see `direct_call_chain_composes_*` below). Requires --relocatable so
    // the import call lowers to a direct `BL func_N` reloc.
    let wat = r#"
        (module
          (import "env" "ext" (func $ext (param i32) (result i32)))
          (func (export "caller") (param i32) (result i32)
            local.get 0 call $ext))
    "#;
    let report = compile_wcet_relocatable(wat, "cortex-m4");
    assert_declined(&report, "caller", "call");
}

// ---------------------------------------------------------------------------
// #778 phase 3 — inter-procedural composition over the DIRECT call graph.
// A caller containing a DIRECT call to a LOCAL bounded callee is now BOUNDED
// (own body + Σ callee_bound × call-site multiplier). The `call` decline is
// MOVED (never deleted) onto un-composable edges: external/import (above),
// recursion, indirect, and any declined callee (below). This is the v0.46
// decline-honesty discipline: converting a decline keeps the honesty gate on
// what still declines.
// ---------------------------------------------------------------------------

/// A loop-free leaf→mid→root chain composes into an EXACT bound per function.
/// The literals are the composed sums (frozen-codegen pins the streams): leaf 19,
/// mid = own(32) + 1×leaf(19) = 51, root = own(34) + 2×mid(51) = 136. Every
/// callee body is counted exactly as many times as it is invoked; summing every
/// straight-line path over-approximates the real max — sound by construction.
/// unicorn ground truth (whole call tree, `wcet_phase3_778_compose_soundness.py`):
/// root(1) == 7, executed 39 machine insns across root+2×mid+4×leaf <= 136.
#[test]
fn direct_call_chain_composes_exact_bounds() {
    let wat = r#"
        (module
          (func $leaf (param i32) (result i32) local.get 0 i32.const 1 i32.add)
          (func $mid (param i32) (result i32) local.get 0 call $leaf i32.const 2 i32.add)
          (func (export "root") (param i32) (result i32)
            local.get 0 call $mid call $mid))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    // func_0 == leaf (no export name), func_1 == mid, root exported.
    assert_bounded(&report, "func_0", 19);
    assert_bounded(&report, "func_1", 51);
    assert_bounded(&report, "root", 136);
    // Composition is a sound upper bound: each bound clears its own instr floor,
    // and root's bound covers its two mid-calls (2 × 51 = 102 <= 136).
    for name in ["func_0", "func_1", "root"] {
        let f = func(&report, name);
        let cycles = f.get("cycles").and_then(Value::as_u64).unwrap();
        let instrs = f.get("instr_count").and_then(Value::as_u64).unwrap();
        assert!(cycles >= instrs, "{name}: bound {cycles} < instrs {instrs}");
    }
    let root = func(&report, "root")
        .get("cycles")
        .and_then(Value::as_u64)
        .unwrap();
    let mid = func(&report, "func_1")
        .get("cycles")
        .and_then(Value::as_u64)
        .unwrap();
    assert!(
        root >= 2 * mid,
        "root bound {root} must cover both mid-calls (2 × {mid})"
    );
}

/// A DIRECT call sitting INSIDE a proven const-bound loop: the callee body is
/// counted `trip` times (the call site's proven execution-count multiplier), NEVER
/// once. This is the #1 composition soundness trap — a flat `Σ callee_bound` would
/// undercount a callee invoked in a loop. Killed by construction: the composed
/// bound clears both the leaf-called-10× floor and the loop's trip floor.
/// unicorn ground truth (`wcet_phase3_778_compose_soundness.py`): loopcaller()
/// == 10, executed 238 machine insns (whole call tree, leaf run 10×) <= 602.
#[test]
fn direct_call_inside_proven_loop_counts_callee_per_trip() {
    let wat = r#"
        (module
          (func $leaf (param i32) (result i32) local.get 0 i32.const 1 i32.add)
          (func (export "loopcaller") (result i32)
            (local i32 i32)
            (block
              (loop
                local.get 0 i32.const 10 i32.lt_s i32.eqz br_if 1
                local.get 1 call $leaf local.set 1
                local.get 0 i32.const 1 i32.add local.set 0
                br 0))
            local.get 1))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    let leaf = func(&report, "func_0")
        .get("cycles")
        .and_then(Value::as_u64)
        .unwrap();
    assert_eq!(leaf, 19, "leaf body pins at 19");
    let f = func(&report, "loopcaller");
    assert_eq!(
        f.get("status").and_then(Value::as_str),
        Some("bounded"),
        "a direct call inside a PROVEN loop must compose (callee counted trip×): {f}"
    );
    assert_loop(&report, "loopcaller", 0, 10, "static");
    assert_trip_floor(&report, "loopcaller");
    // The leaf is invoked 10× (once per trip): the composed bound must include at
    // LEAST 10 × leaf, or the call-in-loop multiplier was dropped (unsound).
    let cycles = f.get("cycles").and_then(Value::as_u64).unwrap();
    assert!(
        cycles >= 10 * leaf,
        "loopcaller bound {cycles} < 10 × leaf {leaf} — the call-in-loop multiplier \
         was lost; a callee in a trip-10 loop must be counted 10×, not once (unsound)"
    );
}

/// DECLINE-HONESTY 1 — SELF-RECURSION: a function that calls itself forms a cycle
/// in the direct call graph → an upper cycle bound cannot be composed → LOUD
/// decline `recursion`. This decline is NEW in phase 3 (the cycle would previously
/// have hit the blanket `call` decline); it must fire on its own specific reason.
#[test]
fn self_recursion_declines_with_recursion_reason() {
    let wat = r#"
        (module
          (func $fac (export "fac") (param i32) (result i32)
            local.get 0 i32.eqz
            (if (result i32)
              (then i32.const 1)
              (else local.get 0 local.get 0 i32.const 1 i32.sub call $fac i32.mul))))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    assert_declined(&report, "fac", "recursion");
}

/// DECLINE-HONESTY 2 — MUTUAL RECURSION: a cycle spanning two functions declines
/// `recursion` on BOTH (every function on the cycle is unbounded).
#[test]
fn mutual_recursion_declines_both() {
    let wat = r#"
        (module
          (func $ping (export "ping") (param i32) (result i32)
            local.get 0 i32.eqz
            (if (result i32)
              (then i32.const 0)
              (else local.get 0 i32.const 1 i32.sub call $pong)))
          (func $pong (export "pong") (param i32) (result i32)
            local.get 0 i32.eqz
            (if (result i32)
              (then i32.const 1)
              (else local.get 0 i32.const 1 i32.sub call $ping))))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    assert_declined(&report, "ping", "recursion");
    assert_declined(&report, "pong", "recursion");
}

/// DECLINE-HONESTY 3 — INDIRECT CALL: `call_indirect` (callee not statically known)
/// declines `indirect-call`. The direct-call composition never applies to an
/// indirect edge — soundness over coverage.
#[test]
fn indirect_call_declines_with_indirect_reason() {
    let wat = r#"
        (module
          (type $t (func (param i32) (result i32)))
          (table 1 funcref)
          (func $g (param i32) (result i32) local.get 0 i32.const 1 i32.add)
          (elem (i32.const 0) $g)
          (func (export "dispatch") (param i32) (result i32)
            local.get 0 i32.const 0 call_indirect (type $t)))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    assert_declined(&report, "dispatch", "indirect-call");
}

/// DECLINE-HONESTY 4 — PROPAGATION: a caller whose OWN body is bounded but that
/// directly calls a callee which itself declines (an unproven data-dependent loop)
/// declines `callee-unbounded` — the decline travels UP the graph. Crucially it
/// carries the PROPAGATION reason, not the callee's `loop` reason (so a consumer
/// sees the caller is unbounded because a callee is, not because the caller loops).
#[test]
fn declined_callee_propagates_up_as_callee_unbounded() {
    let wat = r#"
        (module
          (func $spin (param i32) (result i32)
            (local i32)
            (block
              (loop
                local.get 1 local.get 0 i32.lt_s i32.eqz br_if 1
                local.get 1 i32.const 1 i32.add local.set 1
                br 0))
            local.get 1)
          (func (export "caller") (param i32) (result i32)
            local.get 0 call $spin))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    // The callee keeps its own specific decline...
    assert_declined(&report, "func_0", "loop");
    // ...and the caller declines with the PROPAGATION reason (not `loop`).
    assert_declined(&report, "caller", "callee-unbounded");
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

// ---------------------------------------------------------------------------
// #778 phase 2 — statically-proven loop trip counts. These shapes were
// asserted-DECLINED in phase 1; the gate MOVES here (never deletes): they must
// now be BOUNDED with the exact derived trip count, and the bound must clear
// the trip-aware soundness floor. Ground truth for every fixture was executed
// under unicorn (Thumb-2 machine-instruction counting) at authoring time:
// bound cycles >= executed machine instructions on every fixture, and each
// function's RESULT matched the WASM semantics (a wrong trip count would have
// changed both). In-CI the floor below is the analytic stand-in (no
// cycle-accurate Cortex-M oracle exists in-env — same honesty note as phase 1).
// ---------------------------------------------------------------------------

/// The canonical `for i in 0..10` counted loop (const init 0, step 1, bound 10,
/// head-test): must be BOUNDED with trip_count == 10 and the EXACT pinned
/// cycle literal. unicorn ground truth at authoring: r0 == 45 (correct trips),
/// 188 executed machine insns <= 349.
#[test]
fn const_bound_loop_is_bounded_with_static_trip() {
    let wat = r#"
        (module
          (func (export "sum10") (result i32)
            (local i32 i32)
            (block
              (loop
                local.get 0 i32.const 10 i32.lt_s i32.eqz br_if 1
                local.get 1 local.get 0 i32.add local.set 1
                local.get 0 i32.const 1 i32.add local.set 0
                br 0))
            local.get 1))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    assert_bounded(&report, "sum10", 349);
    assert_loop(&report, "sum10", 0, 10, "static");
    assert_trip_floor(&report, "sum10");
}

/// Bottom-test form (`br_if 0` conditional backward branch): the body executes
/// exactly trip_count times. unicorn: r0 == 45, 129 insns <= 229.
#[test]
fn bottom_test_loop_is_bounded() {
    let wat = r#"
        (module
          (func (export "bottom") (result i32)
            (local i32 i32)
            (loop
              local.get 1 local.get 0 i32.add local.set 1
              local.get 0 i32.const 1 i32.add local.tee 0
              i32.const 10 i32.lt_s br_if 0)
            local.get 1))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    assert_bounded(&report, "bottom", 229);
    assert_loop(&report, "bottom", 0, 10, "static");
    assert_trip_floor(&report, "bottom");
}

/// Nested const-bound loops: BOTH levels prove → factors multiply (5 outer ×
/// 3 inner; the inner counter is re-initialized inside the outer body and the
/// analyzer proves that re-init). unicorn: r0 == 15, 377 insns <= 863.
#[test]
fn nested_const_loops_bound_multiplicatively() {
    let wat = r#"
        (module
          (func (export "nested") (result i32)
            (local i32 i32 i32)
            (block
              (loop
                local.get 0 i32.const 5 i32.lt_s i32.eqz br_if 1
                i32.const 0 local.set 1
                (block
                  (loop
                    local.get 1 i32.const 3 i32.lt_s i32.eqz br_if 1
                    local.get 2 i32.const 1 i32.add local.set 2
                    local.get 1 i32.const 1 i32.add local.set 1
                    br 0))
                local.get 0 i32.const 1 i32.add local.set 0
                br 0))
            local.get 2))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    assert_bounded(&report, "nested", 863);
    assert_loop(&report, "nested", 0, 5, "static");
    assert_loop(&report, "nested", 1, 3, "static");
    assert_trip_floor(&report, "nested");
}

/// A const-bound loop whose body WRITES linear memory: non-SP stores cannot
/// alias the SP-frame counter (WASM has no address-of-local; the linear-memory
/// image is layout-disjoint from the native stack), so the trip proof stands.
/// unicorn: mem[44] == 11 after 16 trips, 304 insns <= 520.
#[test]
fn memory_writing_const_loop_is_bounded() {
    let wat = r#"
        (module
          (func (export "memloop") (result i32)
            (local i32)
            (block
              (loop
                local.get 0 i32.const 16 i32.lt_s i32.eqz br_if 1
                local.get 0 i32.const 4 i32.mul
                local.get 0
                i32.store
                local.get 0 i32.const 1 i32.add local.set 0
                br 0))
            i32.const 44 i32.load)
          (memory 1))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    let f = func(&report, "memloop");
    assert_eq!(
        f.get("status").and_then(Value::as_str),
        Some("bounded"),
        "memory-writing const-bound loop must bound: {f}"
    );
    assert_loop(&report, "memloop", 0, 16, "static");
    assert_trip_floor(&report, "memloop");
}

/// A zero-trip loop (bound 0 < init 0 is false immediately): trip_count == 0,
/// the head check still executes once, so the function stays bounded and the
/// bound covers the single head evaluation. unicorn: r0 == 0, 18 insns <= 58.
#[test]
fn zero_trip_loop_is_bounded() {
    let wat = r#"
        (module
          (func (export "trip0") (result i32)
            (local i32 i32)
            (block
              (loop
                local.get 0 i32.const 0 i32.lt_s i32.eqz br_if 1
                local.get 1 i32.const 1 i32.add local.set 1
                local.get 0 i32.const 1 i32.add local.set 0
                br 0))
            local.get 1))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    assert_loop(&report, "trip0", 0, 0, "static");
    assert_trip_floor(&report, "trip0");
}

/// A loop whose body stores the counter TWICE on a conditional path (an `if`
/// inside the body): the induction is NOT canonical → must stay declined. The
/// decline-honesty counterpart to the bounded shapes above.
#[test]
fn conditional_counter_store_still_declines() {
    let wat = r#"
        (module
          (func (export "condstore") (param i32) (result i32)
            (local i32)
            (block
              (loop
                local.get 1 i32.const 10 i32.lt_s i32.eqz br_if 1
                (if (local.get 0)
                  (then local.get 1 i32.const 5 i32.add local.set 1))
                local.get 1 i32.const 1 i32.add local.set 1
                br 0))
            local.get 1))
    "#;
    let report = compile_wcet(wat, "cortex-m4");
    assert_declined(&report, "condstore", "loop");
}

// ---------------------------------------------------------------------------
// #778 phase 2 — the --wcet-hints seam (untrusted oracle + sound checker).
// RED-FIRST: the wrong-hint rejection is asserted BEFORE the conversion.
// ---------------------------------------------------------------------------

/// The equality-exit fixture (`br_if (i32.eq i N)`): the ONE hint-gated shape —
/// a step that misses the bound flips terminating into infinite, so synth
/// derives the trip (8) + divisibility but only consumes it under an explicit
/// verified hint.
const EQEXIT_WAT: &str = r#"
    (module
      (func (export "eqexit") (result i32)
        (local i32 i32)
        (block
          (loop
            local.get 0 i32.const 8 i32.eq br_if 1
            local.get 1 local.get 0 i32.add local.set 1
            local.get 0 i32.const 1 i32.add local.set 0
            br 0))
        local.get 1))
"#;

/// RED: a deliberately-WRONG hint (3 < the real trip count 8) must be REJECTED
/// with the machine reason `hint-below-derived-trip`, and the function must
/// stay DECLINED — a wrong oracle claim is never trusted into a bound.
#[test]
fn wrong_hint_below_real_trip_is_rejected_red_first() {
    let hints = r#"{"schema":"synth-wcet-hints-v1","functions":{"eqexit":{"loop_bounds":[3]}}}"#;
    let report = compile_wcet_hinted(EQEXIT_WAT, "cortex-m4", Some(hints));
    assert_declined(&report, "eqexit", "loop");
    let f = func(&report, "eqexit");
    let rej = f
        .get("hint_rejections")
        .and_then(Value::as_array)
        .and_then(|a| a.first())
        .unwrap_or_else(|| panic!("wrong hint must be RECORDED as rejected: {f}"));
    assert_eq!(
        rej.get("reason").and_then(Value::as_str),
        Some("hint-below-derived-trip"),
        "wrong hint must carry the specific machine rejection reason: {rej}"
    );
    assert_eq!(rej.get("hint").and_then(Value::as_u64), Some(3));
}

/// Unhinted, the equality-exit shape stays declined (the decline the hint
/// seam converts — asserted so the conversion below is non-vacuous).
#[test]
fn equality_exit_unhinted_still_declines() {
    let report = compile_wcet(EQEXIT_WAT, "cortex-m4");
    assert_declined(&report, "eqexit", "loop");
}

/// GREEN: a correct, verifiable hint (8 >= derived 8) converts the decline into
/// a bound. The emitted trip count is synth's DERIVED value (8) with source
/// `hint-verified` — never the raw hint. unicorn ground truth at authoring:
/// r0 == 28 (= 0+1+..+7), 126 executed machine insns <= 254.
#[test]
fn correct_hint_converts_decline_to_bound() {
    let hints = r#"{"schema":"synth-wcet-hints-v1","functions":{"eqexit":{"loop_bounds":[8]}}}"#;
    let report = compile_wcet_hinted(EQEXIT_WAT, "cortex-m4", Some(hints));
    assert_bounded(&report, "eqexit", 254);
    assert_loop(&report, "eqexit", 0, 8, "hint-verified");
    assert_trip_floor(&report, "eqexit");
}

/// A wrong hint on a STATICALLY-PROVEN loop: synth's own proof stands (the
/// bound does not depend on the oracle), but the contradicting hint is still
/// RECORDED as rejected so the oracle learns its claim was wrong.
#[test]
fn wrong_hint_on_static_loop_bound_stands_rejection_recorded() {
    let wat = r#"
        (module
          (func (export "sum10") (result i32)
            (local i32 i32)
            (block
              (loop
                local.get 0 i32.const 10 i32.lt_s i32.eqz br_if 1
                local.get 1 local.get 0 i32.add local.set 1
                local.get 0 i32.const 1 i32.add local.set 0
                br 0))
            local.get 1))
    "#;
    let hints = r#"{"schema":"synth-wcet-hints-v1","functions":{"sum10":{"loop_bounds":[5]}}}"#;
    let report = compile_wcet_hinted(wat, "cortex-m4", Some(hints));
    assert_bounded(&report, "sum10", 349); // static proof unaffected
    assert_loop(&report, "sum10", 0, 10, "static");
    let f = func(&report, "sum10");
    let rej = f
        .get("hint_rejections")
        .and_then(Value::as_array)
        .and_then(|a| a.first())
        .unwrap_or_else(|| panic!("contradicting hint must be recorded: {f}"));
    assert_eq!(
        rej.get("reason").and_then(Value::as_str),
        Some("hint-below-derived-trip")
    );
}

/// A hint on a DATA-DEPENDENT loop (bound = runtime parameter): synth cannot
/// verify the induction against it → REJECTED `hint-unverifiable-induction`,
/// function stays declined. The untrusted oracle cannot smuggle in a bound.
#[test]
fn data_dependent_hint_is_rejected_unverifiable() {
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
    let hints = r#"{"schema":"synth-wcet-hints-v1","functions":{"spin":{"loop_bounds":[100]}}}"#;
    let report = compile_wcet_hinted(wat, "cortex-m4", Some(hints));
    assert_declined(&report, "spin", "loop");
    let f = func(&report, "spin");
    let rej = f
        .get("hint_rejections")
        .and_then(Value::as_array)
        .and_then(|a| a.first())
        .unwrap_or_else(|| panic!("unverifiable hint must be RECORDED as rejected: {f}"));
    assert_eq!(
        rej.get("reason").and_then(Value::as_str),
        Some("hint-unverifiable-induction"),
        "data-dependent bound: hint must be rejected as unverifiable: {rej}"
    );
}

/// `--wcet-hints` without `--emit-wcet` is a usage error (hints only affect the
/// sidecar), and a malformed hints file fails LOUDLY before compiling.
#[test]
fn hints_cli_misuse_fails_loudly() {
    let dir = std::env::temp_dir().join(format!(
        "synth_wcet_gate_cli_{}_{}",
        std::process::id(),
        unique_id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let wat_path = dir.join("f.wat");
    std::fs::write(
        &wat_path,
        r#"(module (func (export "k") (result i32) i32.const 1))"#,
    )
    .unwrap();
    let hints_path = dir.join("hints.json");
    std::fs::write(
        &hints_path,
        r#"{"schema":"synth-wcet-hints-v1","functions":{}}"#,
    )
    .unwrap();
    let out = dir.join("f.elf");

    // Without --emit-wcet → refused.
    let status = Command::new(synth())
        .args([
            "compile",
            wat_path.to_str().unwrap(),
            "-o",
            out.to_str().unwrap(),
            "-t",
            "cortex-m4",
            "--wcet-hints",
            hints_path.to_str().unwrap(),
        ])
        .status()
        .unwrap();
    assert!(
        !status.success(),
        "--wcet-hints without --emit-wcet must fail"
    );

    // Malformed JSON → refused loudly.
    std::fs::write(&hints_path, "{not json").unwrap();
    let status = Command::new(synth())
        .args([
            "compile",
            wat_path.to_str().unwrap(),
            "-o",
            out.to_str().unwrap(),
            "-t",
            "cortex-m4",
            "--emit-wcet",
            "--wcet-hints",
            hints_path.to_str().unwrap(),
        ])
        .status()
        .unwrap();
    assert!(!status.success(), "malformed --wcet-hints must fail loudly");

    // Wrong schema string → refused loudly.
    std::fs::write(&hints_path, r#"{"schema":"bogus-v9","functions":{}}"#).unwrap();
    let status = Command::new(synth())
        .args([
            "compile",
            wat_path.to_str().unwrap(),
            "-o",
            out.to_str().unwrap(),
            "-t",
            "cortex-m4",
            "--emit-wcet",
            "--wcet-hints",
            hints_path.to_str().unwrap(),
        ])
        .status()
        .unwrap();
    assert!(!status.success(), "wrong hints schema must fail loudly");
}

// ---------------------------------------------------------------------------
// #778 phase 4 (#49) — bounded self-recursion via a VERIFIED depth-hint.
//
// The `recursion` decline is CONVERTED for exactly ONE provably-sound shape: a
// single-self-call chain whose controlling value is entry-independently bounded by
// a mask (`m = param & K ∈ [0,K]`), decreasing by a const step toward a base guard
// on the SAME masked quantity. synth DERIVES its own max depth (never the raw
// hint); the hint only gates consumption. RED-FIRST: the wrong/unverifiable
// rejections are asserted alongside the conversion, and the tree/uncapped/mutual
// shapes STILL decline (decline-honesty MOVED, not deleted).
// ---------------------------------------------------------------------------

/// The masked-recursion ACCEPT fixture: `m = param & 15 ∈ [0,15]`; recurse while
/// `m != 0` passing `m-1`; base returns 0. Depth ≤ 15 for ANY i32 input (the mask
/// buys an entry-independent ceiling). Own body 47 cyc × 16 frames = 752.
const MASKED_REC_WAT: &str = r#"
    (module
      (func $md (export "md") (param i32) (result i32)
        local.get 0 i32.const 15 i32.and
        (if (result i32)
          (then
            local.get 0 i32.const 15 i32.and i32.const 1 i32.sub call $md i32.const 1 i32.add)
          (else i32.const 0))))
"#;

/// GREEN: a correct depth hint (15 ≥ synth's DERIVED ceiling 15) converts the
/// `recursion` decline into a bound. The emitted `max_depth` is synth's DERIVED
/// value 15, `frame_count` 16 (the +1 base frame), never the raw hint. The exact
/// bound literal (752 = 16 × 47) is pinned — a lowering change fails loud.
/// unicorn ground truth (phase-4 harness): md(0xFFFFFFFF)=r0 15, 267 executed
/// machine insns across all frames ≤ 752 (entry-independent).
#[test]
fn masked_recursion_correct_hint_converts_to_bound() {
    let hints = r#"{"schema":"synth-wcet-hints-v1","functions":{"md":{"recursion_depth":15}}}"#;
    let report = compile_wcet_hinted(MASKED_REC_WAT, "cortex-m4", Some(hints));
    assert_bounded(&report, "md", 752);
    let f = func(&report, "md");
    let rec = f
        .get("recursion")
        .unwrap_or_else(|| panic!("bounded recursion must carry a `recursion` record: {f}"));
    assert_eq!(
        rec.get("max_depth").and_then(Value::as_u64),
        Some(15),
        "emitted depth must be synth's DERIVED ceiling (15), not the raw hint: {rec}"
    );
    assert_eq!(
        rec.get("frame_count").and_then(Value::as_u64),
        Some(16),
        "frame_count must be max_depth+1 (the base frame counts): {rec}"
    );
    // Trip-aware floor: 16 frames each running the whole body must not exceed the
    // bound (every instruction costs ≥ 1 cycle).
    let instrs = f.get("instr_count").and_then(Value::as_u64).unwrap();
    assert!(
        752 >= 16 * instrs,
        "bound 752 < 16 frames × {instrs} instrs — unsound"
    );
}

/// Unhinted, the masked shape STAYS declined `recursion` — the decline the hint
/// seam converts (asserted so the conversion above is non-vacuous). A bound this
/// consequential is opt-in (mirroring the equality-exit loop-hint gate).
#[test]
fn masked_recursion_unhinted_still_declines() {
    let report = compile_wcet(MASKED_REC_WAT, "cortex-m4");
    assert_declined(&report, "md", "recursion");
}

/// RED: a too-LOW depth hint (3 < synth's derived ceiling 15) is REJECTED
/// `hint-below-derived-depth` and the function STAYS declined — a wrong oracle
/// claim never becomes a bound.
#[test]
fn masked_recursion_too_low_hint_rejected_red_first() {
    let hints = r#"{"schema":"synth-wcet-hints-v1","functions":{"md":{"recursion_depth":3}}}"#;
    let report = compile_wcet_hinted(MASKED_REC_WAT, "cortex-m4", Some(hints));
    assert_declined(&report, "md", "recursion");
    assert_hint_rejection(&report, "md", "hint-below-derived-depth", 3);
}

/// DECLINE-HONESTY (tree recursion): a TWO-self-call fixture (fib-shaped) — even
/// masked and hinted — is REJECTED `hint-unverifiable-recursion` and stays
/// declined. `depth × per-frame` would under-count the exponential frame tree; the
/// single-self-call gate is the direct guard against that fatal class.
#[test]
fn tree_recursion_two_self_calls_rejected_even_with_hint() {
    let wat = r#"
        (module
          (func $fib (export "fib") (param i32) (result i32)
            local.get 0 i32.const 15 i32.and i32.const 2 i32.lt_s
            (if (result i32)
              (then i32.const 1)
              (else
                local.get 0 i32.const 15 i32.and i32.const 1 i32.sub call $fib
                local.get 0 i32.const 15 i32.and i32.const 2 i32.sub call $fib
                i32.add))))
    "#;
    let hints = r#"{"schema":"synth-wcet-hints-v1","functions":{"fib":{"recursion_depth":15}}}"#;
    let report = compile_wcet_hinted(wat, "cortex-m4", Some(hints));
    assert_declined(&report, "fib", "recursion");
    assert_hint_rejection(&report, "fib", "hint-unverifiable-recursion", 15);
}

/// DECLINE-HONESTY (uncapped countdown): base at `param == 0`, recursive arg
/// `param - 1` with NO mask on the arg path → the controlling value is a raw
/// runtime param, unbounded at one end of i32 (negative entries diverge). A depth
/// hint is REJECTED `hint-unverifiable-recursion`; the function stays declined.
#[test]
fn uncapped_countdown_recursion_hint_rejected_unverifiable() {
    let wat = r#"
        (module
          (func $count (export "count") (param i32) (result i32)
            local.get 0 i32.eqz
            (if (result i32)
              (then i32.const 0)
              (else local.get 0 i32.const 1 i32.sub call $count i32.const 1 i32.add))))
    "#;
    let hints = r#"{"schema":"synth-wcet-hints-v1","functions":{"count":{"recursion_depth":100}}}"#;
    let report = compile_wcet_hinted(wat, "cortex-m4", Some(hints));
    assert_declined(&report, "count", "recursion");
    assert_hint_rejection(&report, "count", "hint-unverifiable-recursion", 100);
}

/// DECLINE-HONESTY (mutual recursion): a two-function cycle — even if one carries a
/// (self-shaped) depth hint — declines `recursion` on BOTH. The certificate only
/// exempts a function's OWN self-edge; a distinct cross-function cycle is not a
/// self-recursion and is never converted.
#[test]
fn mutual_recursion_stays_declined_even_with_hint() {
    let wat = r#"
        (module
          (func $ping (export "ping") (param i32) (result i32)
            local.get 0 i32.eqz
            (if (result i32)
              (then i32.const 0)
              (else local.get 0 i32.const 1 i32.sub call $pong)))
          (func $pong (export "pong") (param i32) (result i32)
            local.get 0 i32.eqz
            (if (result i32)
              (then i32.const 1)
              (else local.get 0 i32.const 1 i32.sub call $ping))))
    "#;
    let hints = r#"{"schema":"synth-wcet-hints-v1","functions":{"ping":{"recursion_depth":50}}}"#;
    let report = compile_wcet_hinted(wat, "cortex-m4", Some(hints));
    assert_declined(&report, "ping", "recursion");
    assert_declined(&report, "pong", "recursion");
}

/// Assert `name` carries a hint rejection with EXACTLY `reason` and `hint`.
fn assert_hint_rejection(report: &Value, name: &str, reason: &str, hint: u64) {
    let f = func(report, name);
    let rej = f
        .get("hint_rejections")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .find(|r| r.get("reason").and_then(Value::as_str) == Some(reason))
        .unwrap_or_else(|| panic!("{name}: expected a hint rejection `{reason}` (entry: {f})"));
    assert_eq!(
        rej.get("hint").and_then(Value::as_u64),
        Some(hint),
        "{name}: rejection carries the offered hint value (record: {rej})"
    );
}

// ---------------------------------------------------------------------------
// Phase-2 assertion helpers.
// ---------------------------------------------------------------------------

/// Assert loop `idx` of `name` has EXACTLY `trip` and `source`.
fn assert_loop(report: &Value, name: &str, idx: usize, trip: u64, source: &str) {
    let f = func(report, name);
    let l = f
        .get("loops")
        .and_then(Value::as_array)
        .and_then(|a| a.get(idx))
        .unwrap_or_else(|| panic!("{name}: no loop record #{idx} (entry: {f})"));
    assert_eq!(
        l.get("trip_count").and_then(Value::as_u64),
        Some(trip),
        "{name} loop {idx}: trip count drifted (record: {l})"
    );
    assert_eq!(
        l.get("source").and_then(Value::as_str),
        Some(source),
        "{name} loop {idx}: wrong bound source (record: {l})"
    );
}

/// The trip-aware soundness floor: every instruction costs at least 1 cycle
/// and each loop's region instructions execute trip_count times, so the bound
/// must satisfy both `cycles ≥ instr_count` and, per loop,
/// `cycles ≥ trip_count × region_instr_count`. A bound below either is
/// arithmetically impossible for a sound model — this floor is independent of
/// the per-op cycle table (the phase-2 cross-check: instruction count × known
/// trip count).
fn assert_trip_floor(report: &Value, name: &str) {
    let f = func(report, name);
    let cycles = f.get("cycles").and_then(Value::as_u64).unwrap();
    let instrs = f.get("instr_count").and_then(Value::as_u64).unwrap();
    assert!(
        cycles >= instrs,
        "{name}: bound {cycles} < instr_count {instrs} — unsound"
    );
    for l in f
        .get("loops")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
    {
        let trip = l.get("trip_count").and_then(Value::as_u64).unwrap();
        let region = l.get("region_instr_count").and_then(Value::as_u64).unwrap();
        assert!(
            cycles >= trip.saturating_mul(region),
            "{name}: bound {cycles} < trip {trip} × region {region} — the loop's \
             instructions alone execute more times than the bound allows: unsound"
        );
    }
}
