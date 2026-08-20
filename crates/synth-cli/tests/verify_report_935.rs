//! #935 — `synth verify` must report the rules it APPLIED AND DECLINED, not
//! only the ones it verified, so a consumer can compute a coverage
//! denominator.
//!
//! Before this gate, a module whose functions contained e.g. 29 `i32.const`
//! printed `Verification summary: 8 verified, 0 failed, 0 unknown` — reading
//! as complete while the const rule (whose Rocq theorem was Admitted, #933)
//! was skipped WITHOUT REPORTING. The vacuity class this locks out: a report
//! that only ever prints zeros for declines.
//!
//! Non-vacuity contract enforced here:
//! - the fixture has KNOWN declines (`i32.const`, `local.get`) and the report
//!   must SHOW them, with non-zero counts and machine reasons;
//! - `i32.shl` must be VERIFIED, not declined (#981): its lowering is routed
//!   to the #975-modelled register-shift ops, so a reappearing
//!   `immediate-shift-encoding` decline is a wiring regression;
//! - the summary denominator must equal verified + failed + unknown + declined;
//! - declined register-operations must name the Rocq theorem they defer to
//!   (the #933 join key: a decline is only covered if that theorem is Qed).
//!
//! Requires the `verify` feature (the SMT half must actually run):
//! `cargo test -p synth-cli --features verify --test verify_report_935`.

use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

/// Fixture with a deliberately known op census in the exported function:
/// 4× i32.const, 2× local.get (declined), plus SMT-verifiable
/// and/add/sub/shl (`i32.shl` verified since #981).
const FIXTURE_WAT: &str = r#"(module
  (func (export "mix") (param i32 i32) (result i32)
    local.get 0
    i32.const 255
    i32.and
    local.get 1
    i32.const 3
    i32.shl
    i32.add
    i32.const 65536
    i32.sub
    i32.const 1
    i32.add))
"#;

struct Artifacts {
    dir: std::path::PathBuf,
    stdout: String,
    report: serde_json::Value,
}

fn run_verify_with_report(tag: &str) -> Artifacts {
    let dir = std::env::temp_dir().join(format!(
        "synth_verify_report_935_{}_{}",
        tag,
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let wat = dir.join("fixture.wat");
    let elf = dir.join("fixture.elf");
    let report_path = dir.join("report.json");
    std::fs::write(&wat, FIXTURE_WAT).expect("write fixture wat");

    let compile = Command::new(synth())
        .args([
            "compile",
            wat.to_str().unwrap(),
            "-o",
            elf.to_str().unwrap(),
            "--all-exports",
        ])
        .output()
        .expect("run synth compile");
    assert!(
        compile.status.success(),
        "compile failed:\n{}\n{}",
        String::from_utf8_lossy(&compile.stdout),
        String::from_utf8_lossy(&compile.stderr)
    );

    let verify = Command::new(synth())
        .args([
            "verify",
            wat.to_str().unwrap(),
            elf.to_str().unwrap(),
            "--emit-verify-report",
            report_path.to_str().unwrap(),
        ])
        .output()
        .expect("run synth verify");
    let stdout = String::from_utf8_lossy(&verify.stdout).into_owned();
    assert!(
        verify.status.success(),
        "verify failed:\n{}\n{}",
        stdout,
        String::from_utf8_lossy(&verify.stderr)
    );

    let report: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&report_path).expect("sidecar must be written"),
    )
    .expect("sidecar must be valid JSON");

    Artifacts {
        dir,
        stdout,
        report,
    }
}

#[test]
fn declines_are_reported_with_counts_reasons_and_rocq_join_keys() {
    let a = run_verify_with_report("declines");

    // Console: the summary must carry the decline half of the denominator.
    assert!(
        a.stdout.contains("declined"),
        "summary must mention declines:\n{}",
        a.stdout
    );
    assert!(
        a.stdout.contains("Module rule inventory:"),
        "module-level inventory line missing:\n{}",
        a.stdout
    );
    // The known declines must be NAMED with counts on the console too.
    assert!(
        a.stdout.contains("I32Const × 4: register-operation"),
        "i32.const decline (count 4) not reported:\n{}",
        a.stdout
    );

    // Sidecar: schema + the known declines with counts, reasons, join keys.
    assert_eq!(a.report["schema"], "synth-verify-v1");
    let rules = a.report["functions"][0]["rules"]
        .as_array()
        .expect("rules array");

    let find = |name: &str| {
        rules
            .iter()
            .find(|r| r["rule"] == name)
            .unwrap_or_else(|| panic!("rule {name} missing from inventory"))
    };

    let konst = find("I32Const");
    assert_eq!(konst["status"], "declined");
    assert_eq!(konst["reason"], "register-operation");
    assert_eq!(konst["rocq_theorem"], "i32_const_correct");
    assert_eq!(konst["count"], 4, "i32.const occurrence count must be real");

    let lget = find("LocalGet");
    assert_eq!(lget["status"], "declined");
    assert_eq!(lget["reason"], "register-operation");
    assert_eq!(lget["rocq_theorem"], "local_get_correct");
    assert_eq!(lget["count"], 2);

    // #981: i32.shl is no longer declined — the shift rules are routed to the
    // #975-modelled `Rm<7:0>` register-shift ops and SMT-verified against the
    // SHIPPED sel_dsl lowering (AND #31 + LSL (reg)). This assertion is the
    // red-first gate: on the pre-#981 wiring it fails with
    // status == "declined", reason == "immediate-shift-encoding".
    let shl = find("I32Shl");
    assert_eq!(shl["status"], "verified");
    assert_eq!(shl["smt_rule"], "i32.shl → AND #31 + LSL (reg)");

    // The SMT half still runs and reports — verified rules are in the SAME
    // inventory (one object, one denominator).
    let and = find("I32And");
    assert_eq!(and["status"], "verified");
    assert_eq!(and["smt_rule"], "i32.and → AND");

    let _ = std::fs::remove_dir_all(&a.dir);
}

#[test]
fn summary_denominator_includes_declines_and_is_internally_consistent() {
    let a = run_verify_with_report("denominator");

    let s = &a.report["summary"];
    let verified = s["verified"].as_u64().unwrap();
    let failed = s["failed"].as_u64().unwrap();
    let unknown = s["unknown"].as_u64().unwrap();
    let declined = s["declined"].as_u64().unwrap();
    let kinds = s["applied_rule_kinds"].as_u64().unwrap();

    // The vacuity class this issue exists for: declines silently zero. The
    // fixture is BUILT to decline — a zero here means the reporter went
    // vacuous again.
    assert!(
        declined > 0,
        "fixture has known declines; a zero declined count is the #935 vacuity"
    );

    // Denominator: every applied rule kind is accounted for, no fourth bucket.
    assert_eq!(
        kinds,
        verified + failed + unknown + declined,
        "applied_rule_kinds must equal the sum of all statuses"
    );

    // Cross-check the summary against the per-function records it aggregates.
    let mut per_fn_declined = 0u64;
    let mut per_fn_total = 0u64;
    for f in a.report["functions"].as_array().unwrap() {
        for r in f["rules"].as_array().unwrap() {
            per_fn_total += 1;
            if r["status"] == "declined" {
                per_fn_declined += 1;
            }
        }
    }
    assert_eq!(declined, per_fn_declined);
    assert_eq!(kinds, per_fn_total);

    // Per-reason instruction totals must be non-zero for the known classes.
    let by_reason = &s["declined_by_reason"];
    assert!(
        by_reason["register-operation"]["instructions"]
            .as_u64()
            .unwrap()
            >= 6,
        "register-operation must count the 4 consts + 2 local.gets"
    );

    let _ = std::fs::remove_dir_all(&a.dir);
}
