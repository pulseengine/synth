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
//! GATE-EXERCISED: `br_if`, `br` (preserved), `select` (folded-predication),
//! `br_table` (split), `if` (preserved — the structured-decision conditional
//! branch, #944). `eliminated-constant` is WIRED (schema + emitter, correct
//! byte-offset join key) but not yet gate-exercised — a fixture that drops a
//! covered branch op is a v1 follow-up. Every object conditional branch that does
//! NOT resolve to one of the covered source ops is surfaced in
//! `object_cond_branches` with `resolved: false` — and, since #944, with a
//! machine-readable `origin` naming WHY synth introduced it when the introducing
//! op family is one whose lowering is verified to emit exactly that control flow
//! (see [`introduced_branch_origin`]). An introduced branch whose family is NOT
//! in that verified map stays `origin: None` with the op named in the note — an
//! unexplained-but-declared branch beats a confident wrong label (#944's own
//! finding: a plausible "guard" label for these was tested and found wrong).
//!
//! ## Compiler-introduced branch origins (#944)
//!
//! `origin` values are kebab-case and each is backed by disassembly-verified
//! lowering shape on the direct/relocatable ARM path:
//! - `bulk-memory-fill-loop` — `memory.fill` expands to a byte-store loop; its
//!   one conditional branch is the loop bound test (`cmp; bhs` — zero-trip safe).
//! - `bulk-memory-copy-loop` — `memory.copy` (memmove semantics) expands to an
//!   overlap-direction test (`cmp dst,src; bhi`) plus a forward- and a
//!   backward-copy loop bound test: exactly three conditional branches.
//! - `division-trap-guard` — `i32.div_s` emits the divide-by-zero guard plus the
//!   two-test `INT_MIN / -1` overflow guard (three branches, each skipping a
//!   `udf`); `i32.div_u` / `i32.rem_s` / `i32.rem_u` emit the zero guard alone.
//!
//! These fields are ADDITIVE on the `synth-provenance-v1` wire format: the
//! deployed consumer (witness `object-disposition`, whose serde ignores unknown
//! fields) keeps parsing maps that carry them.

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
    /// `br_table` / `if`). False = a compiler-introduced object branch —
    /// surfaced not hidden, and carrying `origin` when its introducing op
    /// family is in the verified classification (#944).
    pub resolved: bool,
    /// #944: machine-readable origin for a compiler-introduced branch
    /// (`resolved: false`), derived from the source op the branch's encode-time
    /// `line_map` entry traces to — never guessed. `None` for a resolved branch,
    /// and for an introduced branch whose op family is not in the verified map
    /// (declared-unattributed; the gate pins that count). Additive field: absent
    /// on the wire when `None`, so pre-#944 consumers are unaffected.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub origin: Option<String>,
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

/// Is this a source op the map covers as a branch/condition? Returns its
/// mnemonic if so. Public so the CLI can classify eliminated (fact-spec-dropped)
/// ops with the SAME coverage predicate the emitter uses.
pub fn covered_source_op_name(op: &WasmOp) -> Option<&'static str> {
    source_op_name(op)
}

/// Is this a source op the map covers as a branch/condition?
fn source_op_name(op: &WasmOp) -> Option<&'static str> {
    match op {
        WasmOp::BrIf(_) => Some("BrIf"),
        WasmOp::Br(_) => Some("Br"),
        WasmOp::BrTable { .. } => Some("BrTable"),
        WasmOp::Select => Some("Select"),
        // #944: `if` is a real source decision — its conditional branch was
        // previously mis-bucketed with the compiler-introduced branches.
        WasmOp::If => Some("If"),
        _ => None,
    }
}

/// #944: the machine-readable origin of a compiler-introduced conditional
/// branch, keyed by the source op whose LOWERING emits it (known exactly — the
/// encode-time `line_map` records which op each machine instruction came from).
///
/// Deliberately narrow: an op family is listed ONLY once its lowering's branch
/// shape has been verified by disassembly (see the module header for each
/// family's shape). Anything else returns `None` and stays declared-unattributed
/// — mislabelling a branch is worse than declaring it unexplained (#944).
pub fn introduced_branch_origin(op: &WasmOp) -> Option<&'static str> {
    match op {
        // memory.fill byte-store loop: one bound-test branch (zero-trip safe).
        WasmOp::MemoryFill => Some("bulk-memory-fill-loop"),
        // memory.copy memmove expansion: overlap-direction test + forward- and
        // backward-copy loop bound tests (three branches).
        WasmOp::MemoryCopy => Some("bulk-memory-copy-loop"),
        // WASM trap semantics: divide-by-zero guard (all four), plus the
        // INT_MIN/-1 overflow guard pair for `i32.div_s`.
        WasmOp::I32DivS | WasmOp::I32DivU | WasmOp::I32RemS | WasmOp::I32RemU => {
            Some("division-trap-guard")
        }
        _ => None,
    }
}

/// Derive provenance for one function from the CLI-available data.
///
/// - `ops` / `op_offsets` are index-aligned (the stream the backend compiled and
///   its per-op absolute wasm byte offsets, already fact-spec-filtered upstream).
/// - `line_map` / `branch_map` are index-aligned (one entry per emitted machine
///   instruction: `(pc, wasm_op_index)` and `(pc, class)`).
/// - `eliminated`: `(wasm_op_index_in_original_stream, op_name,
///   absolute_wasm_byte_offset)` for branch/condition ops that constant-folding
///   / fact-spec dropped before codegen. The offset is the ORIGINAL-stream byte
///   offset (the witness join key), NOT derivable from `op_offsets` here (which
///   is the filtered/kept table) — the caller looks it up in the unfiltered
///   side-table.
pub fn derive_function_provenance(
    func_index: u32,
    name: &str,
    ops: &[WasmOp],
    op_offsets: &[u32],
    line_map: &LineMap,
    branch_map: &BranchMap,
    eliminated: &[(usize, String, u32)],
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
            // #944: an `if` decision is realized by its conditional branch, like
            // a `br_if` (its then-end unconditional jump is control flow, not
            // the decision).
            WasmOp::BrIf(_) | WasmOp::If => (ProvKind::Preserved, cond_pcs.clone(), None),
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
    for (orig_idx, op_name, byte_offset) in eliminated {
        entries.push(ProvEntry {
            instruction_offset: *byte_offset,
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
        let (resolved, origin, note, instruction_offset) = match oi {
            Some(idx) => match ops.get(*idx) {
                Some(WasmOp::BrIf(_)) | Some(WasmOp::BrTable { .. }) | Some(WasmOp::If) => {
                    (true, None, None, op_offsets.get(*idx).copied())
                }
                Some(other) => {
                    // #944: a compiler-introduced branch. When the introducing
                    // op family's branch shape is verified, carry its
                    // machine-readable origin; otherwise declare it
                    // unattributed with the op named — never guess a label.
                    let origin = introduced_branch_origin(other);
                    let note = match origin {
                        Some(o) => format!(
                            "compiler-introduced: {o} — emitted lowering source op {other:?} \
                             (serves that op's WASM semantics; not a source-level decision)"
                        ),
                        None => format!(
                            "object conditional branch from non-branch source op {other:?} \
                             (unattributed: op family not in the verified origin map, #944)"
                        ),
                    };
                    (
                        false,
                        origin.map(str::to_string),
                        Some(note),
                        op_offsets.get(*idx).copied(),
                    )
                }
                None => (
                    false,
                    None,
                    Some(
                        "object conditional branch traces to an out-of-range op index".to_string(),
                    ),
                    None,
                ),
            },
            None => (
                false,
                None,
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
            origin,
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
        // ...but the object branch is NOT missing: it's surfaced unresolved,
        // and (#944) with its verified machine-readable origin.
        assert_eq!(fp.object_cond_branches.len(), 1);
        assert!(!fp.object_cond_branches[0].resolved);
        assert!(fp.object_cond_branches[0].note.is_some());
        assert_eq!(
            fp.object_cond_branches[0].origin.as_deref(),
            Some("division-trap-guard")
        );
    }

    /// #944: an `if` decision's conditional branch is a SOURCE decision —
    /// covered (preserved entry) and resolved, not a compiler-introduced branch.
    #[test]
    fn if_decision_branch_is_covered_and_resolved() {
        let ops = vec![WasmOp::If];
        let op_offsets = vec![50u32];
        let line_map: LineMap = vec![(0x00, Some(0)), (0x04, Some(0))];
        let branch_map: BranchMap = vec![
            (0x00, BranchClass::Other),      // the cmp
            (0x04, BranchClass::CondBranch), // the beq to the else/end arm
        ];
        let fp = derive_function_provenance(0, "f", &ops, &op_offsets, &line_map, &branch_map, &[]);
        assert_eq!(fp.entries.len(), 1);
        assert_eq!(fp.entries[0].op, "If");
        assert_eq!(fp.entries[0].kind, ProvKind::Preserved);
        assert_eq!(fp.entries[0].object_pcs, vec![0x04]);
        assert_eq!(fp.object_cond_branches.len(), 1);
        assert!(fp.object_cond_branches[0].resolved);
        assert!(fp.object_cond_branches[0].origin.is_none());
    }

    /// #944 classified origins: bulk-memory expansion branches carry the
    /// verified origin of the op whose lowering emitted them.
    #[test]
    fn bulk_memory_branches_carry_verified_origin() {
        let ops = vec![WasmOp::MemoryFill, WasmOp::MemoryCopy];
        let op_offsets = vec![10u32, 20u32];
        // fill: one loop-bound branch; copy: direction test + two loop bounds.
        let line_map: LineMap = vec![
            (0x00, Some(0)),
            (0x08, Some(1)),
            (0x10, Some(1)),
            (0x20, Some(1)),
        ];
        let branch_map: BranchMap = vec![
            (0x00, BranchClass::CondBranch),
            (0x08, BranchClass::CondBranch),
            (0x10, BranchClass::CondBranch),
            (0x20, BranchClass::CondBranch),
        ];
        let fp = derive_function_provenance(0, "b", &ops, &op_offsets, &line_map, &branch_map, &[]);
        let origins: Vec<_> = fp
            .object_cond_branches
            .iter()
            .map(|b| b.origin.as_deref())
            .collect();
        assert_eq!(
            origins,
            vec![
                Some("bulk-memory-fill-loop"),
                Some("bulk-memory-copy-loop"),
                Some("bulk-memory-copy-loop"),
                Some("bulk-memory-copy-loop"),
            ]
        );
        // Each also carries the introducing op's byte offset — the join anchor.
        assert_eq!(
            fp.object_cond_branches[0].instruction_offset,
            Some(10),
            "fill branch anchors at the memory.fill op offset"
        );
    }

    /// #944 negative control (non-vacuity): the origin map must NOT blanket-label.
    /// A conditional branch tracing to an op family whose lowering shape has not
    /// been disassembly-verified stays declared-unattributed (`origin: None`) —
    /// widening the map without verification is exactly the failure mode the
    /// gate exists to prevent.
    #[test]
    fn unverified_op_family_stays_declared_unattributed() {
        let ops = vec![WasmOp::I64Shl];
        let op_offsets = vec![70u32];
        let line_map: LineMap = vec![(0x00, Some(0))];
        let branch_map: BranchMap = vec![(0x00, BranchClass::CondBranch)];
        let fp = derive_function_provenance(0, "u", &ops, &op_offsets, &line_map, &branch_map, &[]);
        let b = &fp.object_cond_branches[0];
        assert!(!b.resolved);
        assert!(b.origin.is_none(), "must not invent an origin: {:?}", b.origin);
        assert!(
            b.note.as_deref().unwrap_or("").contains("unattributed"),
            "the note must declare the gap, not guess: {:?}",
            b.note
        );
    }

    /// #944: a branch with NO source op at all (prologue/epilogue) is declared,
    /// not silently labeled.
    #[test]
    fn no_source_op_branch_is_declared() {
        let ops: Vec<WasmOp> = vec![];
        let op_offsets: Vec<u32> = vec![];
        let line_map: LineMap = vec![(0x00, None)];
        let branch_map: BranchMap = vec![(0x00, BranchClass::CondBranch)];
        let fp = derive_function_provenance(0, "p", &ops, &op_offsets, &line_map, &branch_map, &[]);
        let b = &fp.object_cond_branches[0];
        assert!(!b.resolved);
        assert!(b.origin.is_none());
        assert!(b.note.is_some());
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
            &[(3, "BrIf".to_string(), 42)],
        );
        assert_eq!(fp.entries.len(), 1);
        assert_eq!(fp.entries[0].kind, ProvKind::EliminatedConstant);
        assert!(fp.entries[0].object_pcs.is_empty());
        // The witness join key is the real byte offset, not a hardcoded 0.
        assert_eq!(fp.entries[0].instruction_offset, 42);
    }
}
