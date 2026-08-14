//! #944 — the compiler-introduced object-branch attribution gate.
//!
//! Issue #944 surfaced object conditional branches the `synth-provenance-v1`
//! map could not explain: they trace to no source-level DECISION, because
//! synth's lowering introduced them (bulk-memory expansion loops, division
//! trap guards) or because the source decision family was uncovered (`if`).
//! The fix gives each such branch a machine-readable `origin` derived from
//! the encode-time `line_map` — the op whose lowering emitted the branch —
//! restricted to op families whose branch shape was verified by disassembly.
//!
//! This gate holds the floor in BOTH directions:
//!
//!   (1) UNATTRIBUTED FLOOR = 0 for the fixture: every object conditional
//!       branch either resolves to a covered source decision or carries a
//!       named origin. A new unattributed branch (new lowering, regressed
//!       classification) turns this red.
//!
//!   (2) NO EXCUSE-WIDENING: the per-origin counts are pinned EXACTLY
//!       (1 fill-loop, 3 copy-loop, 3+1+1+1 division guards) and the origin
//!       vocabulary is a closed set. Reaching "0 unattributed" by
//!       blanket-labeling (the failure mode #944's own follow-up data warned
//!       about — a plausible label tested and found wrong) changes these
//!       counts or mints a new label, and turns this red too.
//!
//! The `if` half: a structured `if` decision must be COVERED (a `preserved`
//! "If" entry whose conditional branch resolves), not bucketed with the
//! introduced branches — that mis-bucketing was the other half of #944.

use serde_json::Value;
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

/// The closed origin vocabulary. Adding a value here requires disassembly
/// verification of the op family's branch shape (see
/// `synth_core::provenance::introduced_branch_origin`) — that is the
/// deliberate friction that keeps "0 unattributed" honest.
const VERIFIED_ORIGINS: &[&str] = &[
    "bulk-memory-fill-loop",
    "bulk-memory-copy-loop",
    "division-trap-guard",
];

#[test]
fn introduced_branches_carry_verified_origins_944() {
    let path = fixture("provenance_introduced_944.wat");
    let out = "/tmp/prov_introduced_944.elf";
    let sidecar = "/tmp/prov_introduced_944.elf.provenance.json";
    let _ = std::fs::remove_file(sidecar);

    let res = Command::new(synth())
        .args([
            "compile",
            path.to_str().unwrap(),
            "-o",
            out,
            "--target",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
            "--emit-provenance",
        ])
        .output()
        .expect("run synth");
    assert!(
        res.status.success(),
        "synth compile failed: {}",
        String::from_utf8_lossy(&res.stderr)
    );

    let map: Value =
        serde_json::from_slice(&std::fs::read(sidecar).expect("sidecar written")).expect("json");
    assert_eq!(map["schema"], "synth-provenance-v1");
    let funcs = map["functions"].as_array().expect("functions");

    let by_name = |n: &str| -> &Value {
        funcs
            .iter()
            .find(|f| f["name"] == n)
            .unwrap_or_else(|| panic!("function '{n}' missing from provenance map"))
    };
    let origins = |f: &Value| -> Vec<String> {
        f["object_cond_branches"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|b| b["resolved"] == false)
            .map(|b| {
                b["origin"]
                    .as_str()
                    .map(str::to_string)
                    .unwrap_or_else(|| "UNATTRIBUTED".to_string())
            })
            .collect()
    };

    // --- (2) exact per-origin counts: the no-excuse-widening pin. ---
    let mut bulk = origins(by_name("bulk"));
    bulk.sort();
    assert_eq!(
        bulk,
        vec![
            "bulk-memory-copy-loop",
            "bulk-memory-copy-loop",
            "bulk-memory-copy-loop",
            "bulk-memory-fill-loop",
        ],
        "memory.fill must introduce exactly 1 loop-bound branch and memory.copy \
         exactly 3 (overlap-direction + two copy-loop bounds)"
    );
    assert_eq!(
        origins(by_name("divs")),
        vec!["division-trap-guard"; 3],
        "i32.div_s must introduce exactly 3 guard branches (div-by-zero + the \
         INT_MIN/-1 overflow pair)"
    );
    for f in ["divu", "rems", "remu"] {
        assert_eq!(
            origins(by_name(f)),
            vec!["division-trap-guard"],
            "{f} must introduce exactly the div-by-zero guard branch"
        );
    }

    // --- the `if` half: a source decision, covered and resolved. ---
    let decide = by_name("decide");
    let if_entries: Vec<&Value> = decide["entries"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e["op"] == "If")
        .collect();
    assert_eq!(
        if_entries.len(),
        1,
        "the if decision must be a covered entry"
    );
    assert_eq!(if_entries[0]["kind"], "preserved");
    assert!(
        !if_entries[0]["object_pcs"].as_array().unwrap().is_empty(),
        "the If entry must carry its object realization"
    );
    let decide_branches = decide["object_cond_branches"].as_array().unwrap();
    assert!(
        !decide_branches.is_empty(),
        "the if must produce a real object conditional branch"
    );
    for b in decide_branches {
        assert_eq!(
            b["resolved"], true,
            "the if decision's branch must RESOLVE (it is a source decision, \
             not a compiler-introduced branch): {b}"
        );
    }

    // --- (1) module-wide unattributed floor = 0, with a closed vocabulary. ---
    let mut total_introduced = 0usize;
    for f in funcs {
        for b in f["object_cond_branches"].as_array().unwrap() {
            if b["resolved"] == true {
                assert!(
                    b["origin"].is_null(),
                    "a resolved branch must not carry an introduced origin: {b}"
                );
                continue;
            }
            total_introduced += 1;
            let origin = b["origin"].as_str().unwrap_or_else(|| {
                panic!(
                    "UNATTRIBUTED object conditional branch in '{}' at pc {} — \
                     the #944 floor is 0 for this fixture. Either a new lowering \
                     introduced an unclassified branch (verify its shape by \
                     disassembly and extend introduced_branch_origin) or the \
                     classification regressed. Note: {:?}",
                    f["name"], b["pc"], b["note"]
                )
            });
            assert!(
                VERIFIED_ORIGINS.contains(&origin),
                "origin '{origin}' is not in the closed, disassembly-verified \
                 vocabulary {VERIFIED_ORIGINS:?} — widening the vocabulary \
                 requires verifying the new family's branch shape first"
            );
            // Every introduced branch anchors at the introducing op's wasm
            // byte offset — the consumer's join key.
            assert!(
                b["instruction_offset"].is_number(),
                "an introduced branch must carry its introducing op's offset: {b}"
            );
        }
    }
    // The fixture is known to introduce exactly 10 branches (4 bulk + 6 div).
    assert_eq!(
        total_introduced, 10,
        "fixture must exercise exactly the 10 verified introduced branches"
    );
}
