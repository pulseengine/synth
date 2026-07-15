//! VCR-DEC-003 (#396, witness#130) — the `synth-provenance-v1` branch-transformation map.
//!
//! synth's lowering changes the branch structure between the WASM source and the
//! ARM object: cmp→select fusion collapses a `select` into a predicated IT-block
//! move (no branch), `br_table` splits one WASM branch into a cascade of object
//! branches, constant-condition guards get elided. witness measures MC/DC on the
//! WASM component; to certify the OBJECT it must reconcile each object-level
//! branch/condition back to its source condition. This module emits the map that
//! makes that reconciliation possible.
//!
//! ## Schema (`synth-provenance-v1`)
//!
//! A JSON sidecar. The witness-facing join key is `(func_index,
//! instruction_offset)` where `instruction_offset` is the ABSOLUTE wasm byte
//! offset of the source op (synth's `op_offsets`, same origin as walrus
//! `InstrLocId` — see VCR-DEC-003). Each entry additionally carries the OBJECT
//! realization (`object_pcs`) so a consumer can map a source condition to the
//! machine code it became — the piece the roadmap's terse schema left implicit
//! but the reconciliation gate needs.
//!
//! `kind ∈`
//! - `preserved` — a 1:1 `br_if`/`br` that stayed a real object branch.
//! - `folded-predication` — a `select` fused to predicated (IT-block) moves; a
//!   decision with NO object branch. `object_pcs` point at the predicated moves.
//! - `split-into-object-branches` — a `br_table` that became N object branches;
//!   `count` = N.
//! - `eliminated-constant` — a source branch/condition dropped before codegen
//!   (constant-fold / fact-spec guard elision). `object_pcs` is empty; the
//!   omission is RECORDED, not silently missing.
//!
//! ## What the map lets a consumer prove (the non-vacuous gate)
//!
//! (a) every object-level conditional branch resolves to a source WASM condition
//!     — carried in `object_cond_branches`, derived from the real object-branch
//!     side-table ([`crate::backend::BranchMap`]), NOT re-walked from the wasm
//!     branch ops (which would be vacuous);
//! (b) a folded/eliminated source condition is explicitly recorded with its
//!     object realization (or its absence), NOT dropped.
//!
//! ## Bounded v1 — covered vs uncovered
//!
//! COVERED solidly: `br_if`, `br` (preserved), `select` (folded-predication),
//! `br_table` (split), constant-eliminated branch ops. Every object conditional
//! branch that does NOT resolve to one of these source ops is surfaced in
//! `object_cond_branches` with `resolved: false` and a `note` (e.g. an `i64`
//! expansion branch or a div/mem trap guard) — an "only-in-synth"-style
//! divergence the consumer SEES rather than a silent gap. Naming the uncovered
//! ones is the deliverable's explicit follow-up boundary.

use serde::{Deserialize, Serialize};

use crate::backend::{BranchClass, BranchMap, LineMap};
use crate::wasm_op::WasmOp;

/// The schema version string embedded at the top of the sidecar.
pub const SCHEMA: &str = "synth-provenance-v1";

/// The transformation a source branch/condition underwent on the way to object code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ProvKind {
    /// 1:1 `br_if`/`br` that stayed a real object branch.
    Preserved,
    /// `select` fused to predicated moves (no object branch).
    FoldedPredication,
    /// `br_table` split into N object branches (`count` = N).
    SplitIntoObjectBranches,
    /// Source branch/condition dropped before codegen (constant / fact-spec).
    EliminatedConstant,
}

/// One source-level branch/condition and what it became in the object.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProvEntry {
    /// Witness join key: ABSOLUTE wasm byte offset of the source op.
    pub instruction_offset: u32,
    /// Index of the source op within the (compiled) op stream — diagnostic.
    pub wasm_op_index: usize,
    /// The source WASM op mnemonic (e.g. `"BrIf"`, `"Select"`, `"BrTable"`).
    pub op: String,
    /// How synth transformed it.
    pub kind: ProvKind,
    /// Object PCs (function-relative machine offsets) that realize this source
    /// op's control flow. Empty for `eliminated-constant`.
    pub object_pcs: Vec<u32>,
    /// For `split-into-object-branches`: the object-branch count. Omitted otherwise.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub count: Option<usize>,
    /// Optional scry#51 reachability evidence for an `eliminated-constant` entry
    /// (justified-infeasible). Reserved for a later increment; `None` in v1.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub scry_evidence: Option<String>,
}

/// One object-level conditional branch, and whether it reconciled to a covered
/// source condition. This is the (a)-clause carrier: derived from the REAL
/// object-branch side-table, so a branch synth emitted that no covered source op
/// explains shows up here with `resolved: false` (surfaced, not hidden).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObjectCondBranch {
    /// Function-relative machine offset of the conditional branch.
    pub pc: u32,
    /// The wasm op index this branch traces back to (via `line_map`), if any.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub wasm_op_index: Option<usize>,
    /// Absolute wasm byte offset of that source op, if resolvable.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub instruction_offset: Option<u32>,
    /// True iff this branch resolves to a covered source condition (`br_if` /
    /// `br_table`). False = an uncovered/only-in-synth object branch (e.g. an
    /// i64-expansion or trap-guard branch) — a v1 follow-up, surfaced not hidden.
    pub resolved: bool,
    /// Human note when `resolved` is false.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
}

/// Provenance for one compiled function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionProvenance {
    pub func_index: u32,
    pub name: String,
    pub entries: Vec<ProvEntry>,
    pub object_cond_branches: Vec<ObjectCondBranch>,
}

/// The whole-module `synth-provenance-v1` map.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProvenanceMap {
    pub schema: String,
    pub module: String,
    pub functions: Vec<FunctionProvenance>,
}

impl ProvenanceMap {
    pub fn new(module: impl Into<String>) -> Self {
        ProvenanceMap {
            schema: SCHEMA.to_string(),
            module: module.into(),
            functions: Vec::new(),
        }
    }

    /// Serialize to pretty JSON.
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("ProvenanceMap serializes")
    }
}

/// Is this a source op the map covers as a branch/condition?
fn source_op_name(op: &WasmOp) -> Option<&'static str> {
    match op {
        WasmOp::BrIf(_) => Some("BrIf"),
        WasmOp::Br(_) => Some("Br"),
        WasmOp::BrTable { .. } => Some("BrTable"),
        WasmOp::Select => Some("Select"),
        _ => None,
    }
}

/// Derive provenance for one function from the CLI-available data.
///
/// - `ops` / `op_offsets` are index-aligned (the stream the backend compiled and
///   its per-op absolute wasm byte offsets, already fact-spec-filtered upstream).
/// - `line_map` / `branch_map` are index-aligned (one entry per emitted machine
///   instruction: `(pc, wasm_op_index)` and `(pc, class)`).
/// - `eliminated`: `(wasm_op_index_in_original_stream, op_name)` for branch/
///   condition ops that constant-folding / fact-spec dropped before codegen.
pub fn derive_function_provenance(
    func_index: u32,
    name: &str,
    ops: &[WasmOp],
    op_offsets: &[u32],
    line_map: &LineMap,
    branch_map: &BranchMap,
    eliminated: &[(usize, String)],
) -> FunctionProvenance {
    // For each op index, collect the object PCs whose branch_map class matters.
    // line_map and branch_map are parallel; zip them.
    let mut entries: Vec<ProvEntry> = Vec::new();

    for (op_idx, op) in ops.iter().enumerate() {
        let Some(op_name) = source_op_name(op) else {
            continue;
        };
        let instruction_offset = op_offsets.get(op_idx).copied().unwrap_or(0);

        // Object realizations of this op: the machine instructions whose
        // line_map op-index == op_idx AND whose branch class is a branch or a
        // predicated move (skip the data-processing setup instructions).
        let mut cond_pcs = Vec::new();
        let mut uncond_pcs = Vec::new();
        let mut pred_pcs = Vec::new();
        for ((pc, oi), (_pc2, class)) in line_map.iter().zip(branch_map.iter()) {
            if *oi != Some(op_idx) {
                continue;
            }
            match class {
                BranchClass::CondBranch => cond_pcs.push(*pc),
                BranchClass::UncondBranch => uncond_pcs.push(*pc),
                BranchClass::Predicated => pred_pcs.push(*pc),
                BranchClass::Other => {}
            }
        }

        let (kind, object_pcs, count) = match op {
            WasmOp::BrIf(_) => (ProvKind::Preserved, cond_pcs.clone(), None),
            WasmOp::Br(_) => (ProvKind::Preserved, uncond_pcs.clone(), None),
            WasmOp::BrTable { .. } => {
                let n = cond_pcs.len();
                let mut all = cond_pcs.clone();
                all.extend(uncond_pcs.iter().copied());
                (ProvKind::SplitIntoObjectBranches, all, Some(n))
            }
            WasmOp::Select => (ProvKind::FoldedPredication, pred_pcs.clone(), None),
            _ => unreachable!("source_op_name gated the match"),
        };

        entries.push(ProvEntry {
            instruction_offset,
            wasm_op_index: op_idx,
            op: op_name.to_string(),
            kind,
            object_pcs,
            count,
            scry_evidence: None,
        });
    }

    // Eliminated-constant entries: branch/condition ops dropped before codegen.
    for (orig_idx, op_name) in eliminated {
        entries.push(ProvEntry {
            instruction_offset: 0,
            wasm_op_index: *orig_idx,
            op: op_name.clone(),
            kind: ProvKind::EliminatedConstant,
            object_pcs: Vec::new(),
            count: None,
            scry_evidence: None,
        });
    }

    // (a)-clause carrier: enumerate the REAL object conditional branches and
    // reconcile each back to its source op via line_map. A branch that traces to
    // a covered condition (BrIf / BrTable) is resolved; anything else is an
    // uncovered/only-in-synth branch, surfaced with a note.
    let mut object_cond_branches: Vec<ObjectCondBranch> = Vec::new();
    for ((pc, oi), (_pc2, class)) in line_map.iter().zip(branch_map.iter()) {
        if *class != BranchClass::CondBranch {
            continue;
        }
        let (resolved, note, instruction_offset) = match oi {
            Some(idx) => match ops.get(*idx) {
                Some(WasmOp::BrIf(_)) | Some(WasmOp::BrTable { .. }) => {
                    (true, None, op_offsets.get(*idx).copied())
                }
                Some(other) => (
                    false,
                    Some(format!(
                        "object conditional branch from non-branch source op {other:?} \
                         (uncovered in v1: i64-expansion / trap-guard / bounds-check branch)"
                    )),
                    op_offsets.get(*idx).copied(),
                ),
                None => (
                    false,
                    Some(
                        "object conditional branch traces to an out-of-range op index".to_string(),
                    ),
                    None,
                ),
            },
            None => (
                false,
                Some(
                    "object conditional branch with no source op (prologue/epilogue synth branch)"
                        .to_string(),
                ),
                None,
            ),
        };
        object_cond_branches.push(ObjectCondBranch {
            pc: *pc,
            wasm_op_index: *oi,
            instruction_offset,
            resolved,
            note,
        });
    }

    FunctionProvenance {
        func_index,
        name: name.to_string(),
        entries,
        object_cond_branches,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserved_brif_and_folded_select() {
        // op[0] BrIf, op[1] Select.
        let ops = vec![WasmOp::BrIf(0), WasmOp::Select];
        let op_offsets = vec![10u32, 20u32];
        // Object: BrIf → cmp(other)@0x00 + bcc(cond)@0x04; Select → predicated mov@0x08.
        let line_map: LineMap = vec![(0x00, Some(0)), (0x04, Some(0)), (0x08, Some(1))];
        let branch_map: BranchMap = vec![
            (0x00, BranchClass::Other),
            (0x04, BranchClass::CondBranch),
            (0x08, BranchClass::Predicated),
        ];
        let fp = derive_function_provenance(0, "f", &ops, &op_offsets, &line_map, &branch_map, &[]);

        let brif = &fp.entries[0];
        assert_eq!(brif.kind, ProvKind::Preserved);
        assert_eq!(brif.object_pcs, vec![0x04]);
        assert_eq!(brif.instruction_offset, 10);

        let sel = &fp.entries[1];
        assert_eq!(sel.kind, ProvKind::FoldedPredication);
        assert_eq!(sel.object_pcs, vec![0x08]);

        // (a): the one object cond branch resolves to the BrIf.
        assert_eq!(fp.object_cond_branches.len(), 1);
        assert!(fp.object_cond_branches[0].resolved);
        assert_eq!(fp.object_cond_branches[0].instruction_offset, Some(10));
    }

    #[test]
    fn unresolved_object_branch_is_surfaced_not_hidden() {
        // An I32DivU whose object lowering emits a trap-guard conditional branch.
        let ops = vec![WasmOp::I32DivU];
        let op_offsets = vec![30u32];
        let line_map: LineMap = vec![(0x00, Some(0))];
        let branch_map: BranchMap = vec![(0x00, BranchClass::CondBranch)];
        let fp = derive_function_provenance(0, "g", &ops, &op_offsets, &line_map, &branch_map, &[]);
        // No covered source entries (I32DivU isn't a covered source branch)...
        assert!(fp.entries.is_empty());
        // ...but the object branch is NOT missing: it's surfaced unresolved.
        assert_eq!(fp.object_cond_branches.len(), 1);
        assert!(!fp.object_cond_branches[0].resolved);
        assert!(fp.object_cond_branches[0].note.is_some());
    }

    #[test]
    fn eliminated_constant_is_recorded() {
        let ops: Vec<WasmOp> = vec![];
        let op_offsets: Vec<u32> = vec![];
        let line_map: LineMap = vec![];
        let branch_map: BranchMap = vec![];
        let fp = derive_function_provenance(
            0,
            "h",
            &ops,
            &op_offsets,
            &line_map,
            &branch_map,
            &[(3, "BrIf".to_string())],
        );
        assert_eq!(fp.entries.len(), 1);
        assert_eq!(fp.entries[0].kind, ProvKind::EliminatedConstant);
        assert!(fp.entries[0].object_pcs.is_empty());
    }
}
