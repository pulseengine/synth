//! VCR-DEC-003 (#396, witness#130) — the `synth-provenance-v1` reconciliation gate.
//!
//! This is the NON-VACUOUS half of the lane. It compiles a multi-branch fixture
//! that FOLDS and SPLITS branches (a `select` fused to a predicated IT-block
//! move, and a `br_table` split into N object branches), then parses the emitted
//! `synth-provenance-v1` sidecar as an INDEPENDENT consumer (like witness's
//! reconciler would) and asserts the two properties #396 exists to guarantee:
//!
//!   (a) every object-level conditional branch resolves to a source WASM
//!       condition — checked against the map's `object_cond_branches` list,
//!       which synth derives from the REAL object-branch side-table
//!       (`BranchMap`), NOT by re-walking the wasm branch ops (that would be
//!       vacuous — it could never catch a branch it didn't already expect);
//!
//!   (b) a folded/eliminated source condition is explicitly recorded as folded
//!       with its object realization (the predicated instruction) — NOT silently
//!       dropped.
//!
//! Plus the coverage the fixture guarantees: the map carries a `preserved`
//! br_if, a `folded-predication` select, and a `split-into-object-branches`
//! br_table, each with a non-empty object realization.
//!
//! The fusion flag (`SYNTH_CMP_SELECT_FUSE=1`) is REQUIRED for the fold to fire;
//! the test drives it explicitly and then PROVES the fold actually happened
//! (folded-predication entry present with predicated object PCs, and NO object
//! conditional branch traces back to the select) — so it tests a real fold, not
//! a mislabeled preserved branch.

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

/// Compile the fixture with fusion + provenance on; return the parsed map.
fn compile_and_parse_provenance(fix: &str, out_stem: &str) -> Value {
    let path = fixture(fix);
    let out = format!("/tmp/{out_stem}.elf");
    let sidecar = format!("/tmp/{out_stem}.elf.provenance.json");
    let _ = std::fs::remove_file(&sidecar);

    let res = Command::new(synth())
        .env("SYNTH_CMP_SELECT_FUSE", "1")
        .args([
            "compile",
            path.to_str().unwrap(),
            "-o",
            &out,
            "--target",
            "cortex-m4",
            "--all-exports",
            "--relocatable",
            "--emit-provenance",
        ])
        .output()
        .expect("run synth");
    assert!(
        res.status.success(),
        "synth compile failed for {fix}: {}",
        String::from_utf8_lossy(&res.stderr)
    );

    let bytes = std::fs::read(&sidecar)
        .unwrap_or_else(|e| panic!("provenance sidecar {sidecar} not written: {e}"));
    serde_json::from_slice(&bytes).expect("sidecar is valid JSON")
}

/// The whole-lane reconciliation gate.
#[test]
fn provenance_reconciles_folded_and_split_branches_396() {
    let map = compile_and_parse_provenance("provenance_branches_396.wat", "prov_recon_396");

    // Schema pin — witness keys off this exact version string.
    assert_eq!(
        map["schema"], "synth-provenance-v1",
        "schema string is the witness contract; do not change without coordinating witness#130"
    );

    let funcs = map["functions"].as_array().expect("functions array");
    assert_eq!(funcs.len(), 1, "fixture has one exported function");
    let f = &funcs[0];
    let entries = f["entries"].as_array().expect("entries array");

    // Collect entries by kind.
    let by_kind = |k: &str| -> Vec<&Value> { entries.iter().filter(|e| e["kind"] == k).collect() };
    let preserved = by_kind("preserved");
    let folded = by_kind("folded-predication");
    let split = by_kind("split-into-object-branches");

    // --- Coverage: all three covered transformations are present. ---
    assert!(
        !preserved.is_empty(),
        "expected a preserved br_if/br entry — got kinds {:?}",
        entries.iter().map(|e| &e["kind"]).collect::<Vec<_>>()
    );
    assert!(
        !folded.is_empty(),
        "expected a folded-predication (select) entry — the FOLD must have fired \
         (SYNTH_CMP_SELECT_FUSE=1). Got kinds {:?}",
        entries.iter().map(|e| &e["kind"]).collect::<Vec<_>>()
    );
    assert!(
        !split.is_empty(),
        "expected a split-into-object-branches (br_table) entry"
    );

    // --- (b) The folded condition is recorded AS folded, with its object
    //         realization (the predicated instruction) — NOT missing. ---
    for e in &folded {
        assert_eq!(
            e["op"], "Select",
            "folded-predication must originate at a select"
        );
        let pcs = e["object_pcs"].as_array().expect("object_pcs array");
        assert!(
            !pcs.is_empty(),
            "a folded select must carry its object realization (the predicated move), \
             not an empty realization — entry {e}"
        );
        // The witness join key is present and plausible.
        assert!(
            e["instruction_offset"].is_number(),
            "folded entry must carry the wasm byte-offset join key: {e}"
        );
    }

    // Prove the fold is a REAL fold, not a mislabeled branch: no object
    // conditional branch may trace back to a select op index. (A select that did
    // NOT fold would appear as an object branch here.)
    let ocbs = f["object_cond_branches"]
        .as_array()
        .expect("object_cond_branches array");
    let select_op_indices: std::collections::HashSet<i64> = folded
        .iter()
        .map(|e| e["wasm_op_index"].as_i64().unwrap())
        .collect();
    for b in ocbs {
        if let Some(idx) = b["wasm_op_index"].as_i64() {
            assert!(
                !select_op_indices.contains(&idx),
                "an object conditional branch traces back to a folded select (op {idx}) — \
                 the fuse did not actually fold; the folded-predication label would be a lie"
            );
        }
    }

    // --- split: count present and object realization non-empty. ---
    for e in &split {
        assert_eq!(e["op"], "BrTable");
        assert!(
            e["count"].as_u64().unwrap_or(0) >= 1,
            "a br_table split must record its object-branch count: {e}"
        );
        assert!(
            !e["object_pcs"].as_array().unwrap().is_empty(),
            "a br_table split must carry its object branch PCs: {e}"
        );
    }

    // --- (a) EVERY object-level conditional branch resolves to a source WASM
    //         condition. This iterates the REAL object branches (not the wasm
    //         ops), so it is the non-vacuous completeness check. Any unresolved
    //         branch (i64-expansion / trap-guard) would be surfaced here with a
    //         note — for THIS fixture there are none, and we assert that. ---
    assert!(
        !ocbs.is_empty(),
        "fixture must produce at least one real object conditional branch to reconcile"
    );
    for b in ocbs {
        let resolved = b["resolved"].as_bool().unwrap_or(false);
        assert!(
            resolved,
            "object conditional branch at pc {} did NOT resolve to a source condition \
             (note: {:?}). Every object branch must reconcile back — an unresolved branch \
             is an only-in-synth divergence that must be covered or explicitly justified.",
            b["pc"], b["note"]
        );
        // A resolved branch carries its source join key.
        assert!(
            b["instruction_offset"].is_number(),
            "a resolved object branch must carry the wasm byte-offset of its source condition: {b}"
        );
    }

    // --- Cross-check: every object cond branch's source op appears as a covered
    //     entry of the right kind (br_if -> preserved, br_table -> split). This
    //     is the source<->object correspondence #396 is about, both directions. ---
    let entry_offsets_preserved: std::collections::HashSet<i64> = preserved
        .iter()
        .map(|e| e["instruction_offset"].as_i64().unwrap())
        .collect();
    let entry_offsets_split: std::collections::HashSet<i64> = split
        .iter()
        .map(|e| e["instruction_offset"].as_i64().unwrap())
        .collect();
    for b in ocbs {
        let off = b["instruction_offset"].as_i64().unwrap();
        assert!(
            entry_offsets_preserved.contains(&off) || entry_offsets_split.contains(&off),
            "object branch at wasm offset {off} has no matching source entry (preserved/split) — \
             the reconciliation would be incomplete"
        );
    }
}
