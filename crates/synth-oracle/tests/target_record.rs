//! RQ-91-TARGETRECORD (Refs #1741): the `target-record` binary end to end.
//!
//! One run on cortex-m4 (a linked target) and cortex-m0plus (no linked image)
//! with an EMPTY corpus directory. The written file must validate against the
//! vendored consumer schema; every target must carry all four facts (none
//! omitted); the empty corpus must read `ran: false` (never a passing row);
//! the target with no image must read `ran: false` with zero executed vectors;
//! and the linked target's execution leg must pass with its controls red.
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary.

#![cfg(feature = "exec")]

use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;
use synth_oracle::record::validate_against_consumer_schema;

fn scratch() -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("target-record-{}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

#[test]
fn record_is_schema_valid_and_never_omits_a_fact() {
    let dir = scratch();
    let empty = dir.join("no-corpus");
    std::fs::create_dir_all(&empty).unwrap();
    let out = dir.join("north-star-input.O1.json");
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_target-record"));
    if let Ok(s) = synth_oracle::synth::synth_binary() {
        cmd.env("SYNTH", s);
    }
    let o = cmd
        .args(["--targets", "cortex-m4,cortex-m0plus", "--spec-dir"])
        .arg(&empty)
        .arg("--work")
        .arg(dir.join("work"))
        .arg("--out")
        .arg(&out)
        .args(["--require-pass", "cortex-m4/execution_match"])
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&o.stdout);
    eprintln!("{stdout}{}", String::from_utf8_lossy(&o.stderr));
    assert!(o.status.success(), "target-record failed: {:?}", o.status);

    let rec: Value = serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    validate_against_consumer_schema(&rec).unwrap();
    let facts = rec["facts"].as_array().unwrap();
    let get = |id: &str| -> &Value {
        facts
            .iter()
            .find(|f| f["id"] == id)
            .unwrap_or_else(|| panic!("fact {id} omitted"))
    };
    for t in ["cortex-m4", "cortex-m0plus"] {
        for field in ["reach", "execution_match", "wcet", "hardware_run"] {
            let f = get(&format!("{t}/{field}"));
            assert_eq!(f["detail"]["target"], t);
            assert_eq!(f["detail"]["field"], field);
        }
    }
    assert_eq!(facts.len(), 8);

    // The empty corpus: did not run, did not pass, value null.
    for t in ["cortex-m4", "cortex-m0plus"] {
        let r = get(&format!("{t}/reach"));
        assert_eq!(
            (r["ran"].as_bool(), r["pass"].as_bool()),
            (Some(false), Some(false)),
            "{r}"
        );
        assert!(r["detail"]["value"].is_null());
    }
    // No linked image: zero vectors, ran=false.
    let x = get("cortex-m0plus/execution_match");
    assert_eq!(
        (x["ran"].as_bool(), x["pass"].as_bool()),
        (Some(false), Some(false))
    );
    assert_eq!(x["detail"]["executed_vectors"], 0);
    // The linked target executed, at or above its floor, with its controls red.
    let x = get("cortex-m4/execution_match");
    assert_eq!(x["pass"], true, "{x}");
    assert_eq!(x["control_failed_as_expected"], true);
    assert!(x["detail"]["executed_vectors"].as_u64().unwrap() >= 3024);
    assert_eq!(x["detail"]["value"]["wrong"], 0);
    assert_eq!(x["detail"]["cpu_model_readback"], 9, "Cortex-M4 model id");
    // Hardware is never claimed.
    for t in ["cortex-m4", "cortex-m0plus"] {
        let h = get(&format!("{t}/hardware_run"));
        assert_eq!(
            (h["ran"].as_bool(), h["pass"].as_bool()),
            (Some(false), Some(false))
        );
    }
    assert!(stdout.contains("schema-valid, 8 facts"));
}
