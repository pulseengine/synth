//! `safe-accesses.json` ingestion — VCR-MEM-004 / #901.
//!
//! scry (the PROVER, scry#114 / FEAT-046) emits a **non-exhaustive** list of
//! wasm memory accesses its sound abstract interpretation proved in-bounds
//! against the memory's guaranteed MINIMUM size. synth consumes it to skip
//! emitting the `--safety-bounds software` guard at exactly those sites: the
//! elision is proof-carrying (scry proves the access, synth's Rocq suite
//! proves the lowering) and attested (`sigil` reads the sidecar this module
//! emits).
//!
//! ```json
//! { "schema": "scry/safe-accesses/v1", "scry_version": "3.2.4",
//!   "module_sha256": "<hex>", "memory_min_bytes": 65536,
//!   "proven_safe": [ { "func": 4, "pc": 41, "op": "i32.load", "width": 4 } ] }
//! ```
//!
//! # Why this file is nearly all refusal logic
//!
//! Eliding a bounds check on a stale or mis-keyed analysis is a **memory-safety
//! hole**, not a stale optimization. So every question this module can ask is
//! answered fail-closed, and "fail closed" always means the SAME thing: an
//! EMPTY [`synth_memory::ProvenSafeSites`]-shaped verdict set, which degrades
//! the module to the ordinary software bounds check. It never means an error
//! and never means partial trust.
//!
//! 1. **`module_sha256` mismatch ⇒ refuse.** Verified against the exact bytes
//!    handed to the decoder — i.e. AFTER `.wat` parsing, after loom, and after
//!    the #418 arena-bind rewrite. That is deliberate: those rewrites shift
//!    function and operator indices, so binding the hash to the post-rewrite
//!    bytes makes index skew and byte skew the SAME gate. A file produced for
//!    the pre-rewrite module simply fails the hash and elides nothing.
//! 2. **`memory_min_bytes` disagreement ⇒ refuse.** The verdicts are proven
//!    against scry's declared floor; if synth's declared minimum for this
//!    module differs, every verdict is unsound HERE. A matching hash implies
//!    the two agree, so a mismatch means the producer is broken — and trusting
//!    a broken prover is the hole this module exists to close.
//! 3. **Wrong/absent schema, malformed JSON, unreadable file ⇒ refuse** with a
//!    diagnostic and exit 0. This is the `wsc.facts` fail-safe skew rule
//!    ([`crate::wsc_facts`], loom#231 Q4) applied to a JSON carrier: the
//!    verdicts are an optional accelerator, so no input may turn a successful
//!    compile into a failed one.
//! 4. **The key is self-checking.** `(func, pc)` is the wasmparser operator
//!    index space: `pc` is the 0-based index of the operator within the
//!    function body — the space scry's own guard refinement walks
//!    (`ops[pc..pc+4]`, scry#114 §2) and the space synth's `op_offsets`
//!    side-table and #494's elision marks are already stated in.
//!    [`ProvenSafeIngest::validate_function`] checks each entry against the
//!    DECODED stream: the op at `pc` must exist, must be a memory access, and
//!    its access width must equal the declared `width`. An entry that fails is
//!    DROPPED with a counted diagnostic. So if a producer ever emits byte
//!    offsets instead of operator indices, essentially every entry fails and
//!    the build elides NOTHING loudly — instead of stripping the guard off the
//!    wrong access silently.
//!
//! Absence from `proven_safe` means **"not proven"**, never "unsafe": an
//! unlisted site keeps its guard.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};

use crate::wasm_op::WasmOp;

/// The producer schema this consumer understands (scry#114).
pub const SAFE_ACCESSES_SCHEMA: &str = "scry/safe-accesses/v1";

/// The attestation schema synth emits for sigil.
pub const ELISION_ATTESTATION_SCHEMA: &str = "synth-proven-safe-elisions-v1";

// =============================================================================
// The producer document
// =============================================================================

/// One access site scry claims to have proven in-bounds.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SafeSite {
    /// Full wasm function index (imported functions first, then local ones) —
    /// the same space as `FunctionOps::index`.
    pub func: u32,
    /// 0-based operator index within the function body.
    pub pc: u32,
    /// The operator mnemonic scry saw (e.g. `"i32.load"`). Diagnostic only —
    /// the WIDTH is what gets machine-checked, since it is the field whose
    /// disagreement would change which bytes are covered.
    #[serde(default)]
    pub op: String,
    /// Access width in bytes. Checked against the decoded op.
    pub width: u32,
}

/// The raw `safe-accesses.json` shape. Unknown fields are IGNORED
/// (forward-compatible with a newer scry adding `premises`/`counts`
/// alongside), but the fields synth's soundness rests on are all required —
/// a missing one is a parse failure, hence a refusal.
#[derive(Debug, Clone, Deserialize)]
struct RawDocument {
    schema: String,
    #[serde(default)]
    scry_version: String,
    module_sha256: String,
    memory_min_bytes: u64,
    #[serde(default)]
    proven_safe: Vec<SafeSite>,
}

// =============================================================================
// Ingestion
// =============================================================================

/// The result of ingesting a `safe-accesses.json`. TOTAL by design — there is
/// deliberately no `Result` in [`ingest`]'s return type, mirroring
/// [`crate::wsc_facts::parse_wsc_facts`]: no input may turn a successful
/// compile into a failed one.
///
/// When [`ProvenSafeIngest::accepted`] is false, [`ProvenSafeIngest::offered`]
/// is EMPTY — a refused document is not trusted piecemeal — and
/// [`ProvenSafeIngest::refusal`] names why.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ProvenSafeIngest {
    /// Did the document clear every whole-file gate (schema, hash, memory
    /// floor)? False ⇒ elide nothing.
    pub accepted: bool,
    /// `Some(reason)` exactly when `accepted` is false.
    pub refusal: Option<String>,
    /// The producer version string, for the attestation. Empty if absent or
    /// the document was unreadable.
    pub scry_version: String,
    /// The `module_sha256` the document declared (hex, as written). Empty when
    /// the document did not parse.
    pub declared_module_sha256: String,
    /// The sha256 synth computed over the module it is actually compiling.
    pub actual_module_sha256: String,
    /// The `memory_min_bytes` the document declared.
    pub declared_memory_min_bytes: u64,
    /// Sites the document offered, once the whole-file gates passed. These are
    /// candidates: each still faces [`ProvenSafeIngest::validate_function`].
    pub offered: Vec<SafeSite>,
    /// Human-facing diagnostics (warnings). Never an error.
    pub diagnostics: Vec<String>,
}

impl ProvenSafeIngest {
    /// A refusal: nothing trusted, one named reason.
    fn refuse(reason: impl Into<String>) -> Self {
        let reason = reason.into();
        Self {
            accepted: false,
            diagnostics: vec![reason.clone()],
            refusal: Some(reason),
            ..Self::default()
        }
    }

    /// Sites this document offered for one function, in `pc` order.
    pub fn offered_for_func(&self, func: u32) -> Vec<&SafeSite> {
        let mut v: Vec<&SafeSite> = self.offered.iter().filter(|s| s.func == func).collect();
        v.sort_by_key(|s| s.pc);
        v
    }

    /// **The self-checking key.** Validate this function's offered sites
    /// against the operator stream synth actually decoded, and return the
    /// operator indices that survive — the per-site elision marks.
    ///
    /// An entry is DROPPED (with a diagnostic pushed into `notes`) when:
    /// - `pc` is out of range for this function's op count;
    /// - the op at `pc` is not a linear-memory access;
    /// - the op's access width differs from the declared `width`.
    ///
    /// Dropping rather than refusing the whole file is deliberate and matches
    /// the `wsc.facts` per-record rule: a newer scry proving an access class
    /// synth does not guard must not invalidate the sites it does guard. The
    /// safety direction is preserved either way — a dropped entry keeps its
    /// guard.
    pub fn validate_function(
        &self,
        func: u32,
        ops: &[WasmOp],
        notes: &mut Vec<String>,
    ) -> Vec<usize> {
        let mut marks = Vec::new();
        for site in self.offered_for_func(func) {
            let idx = site.pc as usize;
            let Some(op) = ops.get(idx) else {
                notes.push(format!(
                    "func {func} pc {} — out of range (function has {} operators); \
                     entry DROPPED, guard retained. If the producer emitted wasm BYTE \
                     OFFSETS, the key space is wrong: `pc` is the 0-based OPERATOR index",
                    site.pc,
                    ops.len()
                ));
                continue;
            };
            let Some(actual_width) = access_width(op) else {
                notes.push(format!(
                    "func {func} pc {} — the operator there is {op:?}, not a linear-memory \
                     access; entry DROPPED, guard retained (claimed op '{}')",
                    site.pc, site.op
                ));
                continue;
            };
            if actual_width != site.width {
                notes.push(format!(
                    "func {func} pc {} — declared width {} B disagrees with the decoded \
                     operator {op:?} ({actual_width} B); entry DROPPED, guard retained",
                    site.pc, site.width
                ));
                continue;
            }
            marks.push(idx);
        }
        marks.sort_unstable();
        marks.dedup();
        marks
    }
}

/// Access width in bytes of a linear-memory operator, or `None` when the
/// operator is not a linear-memory access.
///
/// This is the width the BOUNDS CHECK covers (the number of bytes touched),
/// not the value width: `i32.load8_u` touches 1 byte, `i64.load32_u` touches 4.
pub fn access_width(op: &WasmOp) -> Option<u32> {
    Some(match op {
        WasmOp::I32Load8S { .. }
        | WasmOp::I32Load8U { .. }
        | WasmOp::I32Store8 { .. }
        | WasmOp::I64Load8S { .. }
        | WasmOp::I64Load8U { .. }
        | WasmOp::I64Store8 { .. } => 1,
        WasmOp::I32Load16S { .. }
        | WasmOp::I32Load16U { .. }
        | WasmOp::I32Store16 { .. }
        | WasmOp::I64Load16S { .. }
        | WasmOp::I64Load16U { .. }
        | WasmOp::I64Store16 { .. } => 2,
        WasmOp::I32Load { .. }
        | WasmOp::I32Store { .. }
        | WasmOp::I64Load32S { .. }
        | WasmOp::I64Load32U { .. }
        | WasmOp::I64Store32 { .. }
        | WasmOp::F32Load { .. }
        | WasmOp::F32Store { .. } => 4,
        WasmOp::I64Load { .. }
        | WasmOp::I64Store { .. }
        | WasmOp::F64Load { .. }
        | WasmOp::F64Store { .. } => 8,
        WasmOp::V128Load { .. } | WasmOp::V128Store { .. } => 16,
        _ => return None,
    })
}

/// Ingest a `safe-accesses.json`, binding it to `module_bytes` (the EXACT
/// bytes synth is compiling) and to `memory_min_bytes` (synth's own declared
/// linear-memory minimum). Total: every input yields a verdict, never an error.
///
/// `module_bytes` must be the post-`.wat`-parse, post-loom, post-arena-bind
/// buffer handed to the decoder — see the module docs for why that choice
/// makes index skew and byte skew one gate.
pub fn ingest(path: &Path, module_bytes: &[u8], memory_min_bytes: u32) -> ProvenSafeIngest {
    let actual = hex_sha256(module_bytes);

    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            return ProvenSafeIngest {
                actual_module_sha256: actual,
                ..ProvenSafeIngest::refuse(format!(
                    "--proven-safe {}: cannot read the file ({e}); NO bounds guard is \
                     elided (fail closed) and the compile continues unchanged",
                    path.display()
                ))
            };
        }
    };

    let doc: RawDocument = match serde_json::from_str(&text) {
        Ok(d) => d,
        Err(e) => {
            return ProvenSafeIngest {
                actual_module_sha256: actual,
                ..ProvenSafeIngest::refuse(format!(
                    "--proven-safe {}: not a well-formed `{SAFE_ACCESSES_SCHEMA}` document \
                     ({e}); NO bounds guard is elided (fail closed) and the compile \
                     continues unchanged",
                    path.display()
                ))
            };
        }
    };

    if doc.schema != SAFE_ACCESSES_SCHEMA {
        return ProvenSafeIngest {
            actual_module_sha256: actual,
            scry_version: doc.scry_version.clone(),
            declared_module_sha256: doc.module_sha256.clone(),
            declared_memory_min_bytes: doc.memory_min_bytes,
            ..ProvenSafeIngest::refuse(format!(
                "--proven-safe {}: schema is '{}', expected '{SAFE_ACCESSES_SCHEMA}'; \
                 NO bounds guard is elided (fail closed)",
                path.display(),
                doc.schema
            ))
        };
    }

    // ---- GATE 1: the verdicts must be bound to THIS module. ----
    // A stale analysis is a memory-safety hole, not a stale optimization.
    if !doc.module_sha256.eq_ignore_ascii_case(&actual) {
        return ProvenSafeIngest {
            actual_module_sha256: actual.clone(),
            scry_version: doc.scry_version.clone(),
            declared_module_sha256: doc.module_sha256.clone(),
            declared_memory_min_bytes: doc.memory_min_bytes,
            ..ProvenSafeIngest::refuse(format!(
                "--proven-safe {}: REFUSED — module_sha256 mismatch. The file was produced \
                 for {}, but this compile's module hashes to {actual}. Eliding a bounds \
                 check on a stale analysis is a memory-safety hole, not a stale \
                 optimization, so NO guard is elided. (The hash covers the bytes handed to \
                 the decoder — after .wat parsing, after loom, and after the #418 \
                 arena-bind rewrite — so a module rewrite that shifts operator indices \
                 lands here too.)",
                path.display(),
                if doc.module_sha256.is_empty() {
                    "<empty>"
                } else {
                    &doc.module_sha256
                }
            ))
        };
    }

    // ---- GATE 2: the verdicts must be proven against THIS memory floor. ----
    // A matching hash implies these agree; a mismatch means the producer is
    // broken, and a broken prover must not be trusted.
    if doc.memory_min_bytes != u64::from(memory_min_bytes) {
        return ProvenSafeIngest {
            actual_module_sha256: actual,
            scry_version: doc.scry_version.clone(),
            declared_module_sha256: doc.module_sha256.clone(),
            declared_memory_min_bytes: doc.memory_min_bytes,
            ..ProvenSafeIngest::refuse(format!(
                "--proven-safe {}: REFUSED — memory_min_bytes disagreement. The verdicts \
                 were proven against a {} B floor; synth's declared linear-memory minimum \
                 for this module is {memory_min_bytes} B. The module_sha256 MATCHED, so \
                 these should be equal — a disagreement means the producer is broken, and \
                 verdicts from a broken prover are not trusted. NO guard is elided.",
                path.display(),
                doc.memory_min_bytes
            ))
        };
    }

    let mut diagnostics = Vec::new();
    if doc.proven_safe.is_empty() {
        diagnostics.push(format!(
            "--proven-safe {}: accepted, but the document proves ZERO access sites — \
             nothing to elide (every guard is retained)",
            path.display()
        ));
    }

    ProvenSafeIngest {
        accepted: true,
        refusal: None,
        scry_version: doc.scry_version,
        declared_module_sha256: doc.module_sha256,
        actual_module_sha256: actual,
        declared_memory_min_bytes: doc.memory_min_bytes,
        offered: doc.proven_safe,
        diagnostics,
    }
}

/// Lowercase hex sha256 — the `module_sha256` convention.
pub fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut s = String::with_capacity(64);
    for b in digest {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// =============================================================================
// Attestation (loop step 6 — what sigil reads)
// =============================================================================

/// One elided site, as attested.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttestedElision {
    pub func: u32,
    /// Operator index within the function body.
    pub pc: u32,
    pub op: String,
    pub width: u32,
    /// Who authorized this elision. `"scry/safe-accesses/v1"` today; the
    /// field exists so a future site elided on a DIFFERENT authority (e.g.
    /// #494's per-site ordeal certificate) is distinguishable in one file.
    pub authority: String,
}

/// The `synth-proven-safe-elisions-v1` sidecar.
///
/// **Emitted on refusal too**, carrying `accepted: false` plus the reason and
/// the offered-but-not-elided count. A sidecar that only appears on success is
/// a brag sheet, not an attestation: sigil must be able to tell "nothing to
/// elide" from "file rejected".
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ElisionAttestation {
    pub schema: String,
    /// `CARGO_PKG_VERSION` of the synth that produced the ELF.
    pub synth_version: String,
    /// The producer's version string, as declared.
    pub scry_version: String,
    /// The sha256 synth computed over the module it compiled. This is the
    /// authoritative binding — `declared_module_sha256` is what the file said.
    pub module_sha256: String,
    pub declared_module_sha256: String,
    /// Synth's declared linear-memory minimum, in bytes.
    pub memory_min_bytes: u32,
    pub declared_memory_min_bytes: u64,
    /// The `--safety-bounds` mode in force. Elisions only change emitted bytes
    /// under `software`; any other mode is recorded so an auditor sees why the
    /// elision count is zero.
    pub safety_bounds: String,
    /// Did the document clear the whole-file gates?
    pub accepted: bool,
    /// Why not, when `accepted` is false.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub refusal: Option<String>,
    /// How many sites the document offered.
    pub sites_offered: usize,
    /// How many survived key validation AND were actually stripped.
    pub sites_elided: usize,
    /// Offered sites that were dropped — bad key, wrong width, a specialized
    /// function, or a non-`software` bounds mode. `offered - elided`.
    pub sites_not_elided: usize,
    /// The elision set proper.
    pub elisions: Vec<AttestedElision>,
    /// Every warning the ingestion and validation emitted, verbatim.
    pub diagnostics: Vec<String>,
}

impl ElisionAttestation {
    /// Serialize to pretty JSON.
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("ElisionAttestation serializes")
    }

    /// `foo.elf` → `foo.proven-safe-elisions.json`, mirroring
    /// [`crate::SafetyManifest::sidecar_path`]'s shape.
    pub fn sidecar_path(elf_path: &Path) -> PathBuf {
        let mut p = elf_path.to_path_buf();
        let stem = elf_path
            .file_stem()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| "out".to_string());
        p.set_file_name(format!("{stem}.proven-safe-elisions.json"));
        p
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn write_tmp(name: &str, body: &str) -> PathBuf {
        let dir = std::env::temp_dir().join("proven_safe_901_unit");
        std::fs::create_dir_all(&dir).expect("mk tempdir");
        let p = dir.join(name);
        let mut f = std::fs::File::create(&p).expect("create");
        f.write_all(body.as_bytes()).expect("write");
        p
    }

    const MODULE: &[u8] = b"\0asm\x01\0\0\0 pretend this is a module";

    fn doc(hash: &str, min: u64, sites: &str) -> String {
        format!(
            r#"{{ "schema": "scry/safe-accesses/v1", "scry_version": "3.2.4",
                  "module_sha256": "{hash}", "memory_min_bytes": {min},
                  "premises": {{ "bounded_memory": true }},
                  "counts": {{ "access_sites": 9, "proven_safe": 1 }},
                  "proven_safe": [{sites}] }}"#
        )
    }

    // ---- PROPERTY 1: fail closed on module_sha256 mismatch ------------------

    #[test]
    fn hash_mismatch_refuses_everything_901() {
        let stale = "0".repeat(64);
        let p = write_tmp(
            "stale.json",
            &doc(
                &stale,
                65536,
                r#"{"func":0,"pc":1,"op":"i32.load","width":4}"#,
            ),
        );
        let r = ingest(&p, MODULE, 65536);
        assert!(!r.accepted, "a stale analysis must never be accepted");
        assert!(
            r.offered.is_empty(),
            "a refused document is not trusted piecemeal"
        );
        let why = r.refusal.expect("a refusal names its reason");
        assert!(why.contains("module_sha256 mismatch"), "{why}");
        // Both values are named so the operator can tell WHICH module it was for.
        assert!(why.contains(&stale), "{why}");
        assert!(why.contains(&hex_sha256(MODULE)), "{why}");
    }

    #[test]
    fn matching_hash_is_accepted_and_case_insensitive_901() {
        let h = hex_sha256(MODULE).to_uppercase();
        let p = write_tmp(
            "good.json",
            &doc(&h, 65536, r#"{"func":0,"pc":1,"op":"i32.load","width":4}"#),
        );
        let r = ingest(&p, MODULE, 65536);
        assert!(r.accepted, "{:?}", r.refusal);
        assert_eq!(r.offered.len(), 1);
        assert_eq!(r.scry_version, "3.2.4");
    }

    /// Any change to the module — a single flipped byte, which is what a
    /// pre-compile rewrite looks like — refuses.
    #[test]
    fn one_flipped_module_byte_refuses_901() {
        let p = write_tmp(
            "flip.json",
            &doc(
                &hex_sha256(MODULE),
                65536,
                r#"{"func":0,"pc":1,"op":"i32.load","width":4}"#,
            ),
        );
        let mut rewritten = MODULE.to_vec();
        rewritten.push(0x00);
        let r = ingest(&p, &rewritten, 65536);
        assert!(!r.accepted);
        assert!(r.refusal.unwrap().contains("module_sha256 mismatch"));
    }

    // ---- PROPERTY: fail closed on the memory floor --------------------------

    #[test]
    fn memory_min_bytes_disagreement_refuses_901() {
        let p = write_tmp(
            "floor.json",
            &doc(
                &hex_sha256(MODULE),
                131072,
                r#"{"func":0,"pc":1,"op":"i32.load","width":4}"#,
            ),
        );
        let r = ingest(&p, MODULE, 65536);
        assert!(!r.accepted);
        let why = r.refusal.unwrap();
        assert!(why.contains("memory_min_bytes disagreement"), "{why}");
        assert!(why.contains("131072") && why.contains("65536"), "{why}");
    }

    // ---- PROPERTY: malformed ⇒ no elisions, a diagnostic, never an error ----

    #[test]
    fn malformed_missing_and_wrong_schema_all_refuse_without_erroring_901() {
        let h = hex_sha256(MODULE);
        let cases = vec![
            ("missing", None),
            ("garbage.json", Some("this is not json {{{".to_string())),
            ("empty.json", Some(String::new())),
            (
                "wrongschema.json",
                Some(doc(&h, 65536, "").replace(SAFE_ACCESSES_SCHEMA, "scry/safe-accesses/v2")),
            ),
            (
                "nohash.json",
                Some(r#"{"schema":"scry/safe-accesses/v1","memory_min_bytes":65536}"#.to_string()),
            ),
            (
                "sitegarbage.json",
                Some(doc(&h, 65536, r#"{"func":"four","pc":1,"width":4}"#)),
            ),
        ];
        for (name, body) in cases {
            let p = match body {
                Some(b) => write_tmp(name, &b),
                None => std::env::temp_dir().join("proven_safe_901_unit/definitely-absent.json"),
            };
            let r = ingest(&p, MODULE, 65536);
            assert!(!r.accepted, "'{name}' must not be accepted");
            assert!(r.offered.is_empty(), "'{name}' offered sites");
            assert!(r.refusal.is_some(), "'{name}' refused without a reason");
            assert!(!r.diagnostics.is_empty(), "'{name}' refused silently");
        }
    }

    #[test]
    fn unknown_fields_are_tolerated_901() {
        // A newer scry adding fields must not break an older synth.
        let p = write_tmp(
            "future.json",
            &format!(
                r#"{{ "schema": "scry/safe-accesses/v1", "scry_version": "9.9.9",
                      "module_sha256": "{}", "memory_min_bytes": 65536,
                      "brand_new_field": {{ "nested": [1,2,3] }},
                      "proven_safe": [{{"func":0,"pc":1,"op":"i32.load","width":4,
                                        "confidence":"high"}}] }}"#,
                hex_sha256(MODULE)
            ),
        );
        let r = ingest(&p, MODULE, 65536);
        assert!(r.accepted, "{:?}", r.refusal);
        assert_eq!(r.offered.len(), 1);
    }

    #[test]
    fn accepted_but_empty_is_diagnosed_901() {
        let p = write_tmp("none.json", &doc(&hex_sha256(MODULE), 65536, ""));
        let r = ingest(&p, MODULE, 65536);
        assert!(r.accepted);
        assert!(r.offered.is_empty());
        assert!(
            r.diagnostics
                .iter()
                .any(|d| d.contains("ZERO access sites")),
            "an accepted-but-vacuous document must say so: {:?}",
            r.diagnostics
        );
    }

    // ---- PROPERTY 4: the key is self-checking -------------------------------

    fn ops() -> Vec<WasmOp> {
        vec![
            WasmOp::LocalGet(0), // 0
            WasmOp::I32Load {
                offset: 0,
                align: 2,
            }, // 1  — 4 B
            WasmOp::LocalGet(0), // 2
            WasmOp::I32Load8U {
                offset: 1,
                align: 0,
            }, // 3  — 1 B
            WasmOp::I32Add,      // 4
            WasmOp::I64Store {
                offset: 8,
                align: 3,
            }, // 5  — 8 B
        ]
    }

    #[test]
    fn valid_sites_become_marks_901() {
        let p = write_tmp(
            "marks.json",
            &doc(
                &hex_sha256(MODULE),
                65536,
                r#"{"func":0,"pc":5,"op":"i64.store","width":8},
                   {"func":0,"pc":1,"op":"i32.load","width":4},
                   {"func":0,"pc":3,"op":"i32.load8_u","width":1}"#,
            ),
        );
        let r = ingest(&p, MODULE, 65536);
        let mut notes = Vec::new();
        assert_eq!(r.validate_function(0, &ops(), &mut notes), vec![1, 3, 5]);
        assert!(notes.is_empty(), "{notes:?}");
    }

    /// If the producer ever emits wasm BYTE OFFSETS instead of operator
    /// indices, the entries fall out of range or land on non-access operators —
    /// so the build elides nothing LOUDLY instead of stripping the wrong guard.
    #[test]
    fn byte_offsets_instead_of_op_indices_elide_nothing_loudly_901() {
        let p = write_tmp(
            "byteoffsets.json",
            &doc(
                &hex_sha256(MODULE),
                65536,
                r#"{"func":0,"pc":41,"op":"i32.load","width":4},
                   {"func":0,"pc":137,"op":"i32.load8_u","width":1}"#,
            ),
        );
        let r = ingest(&p, MODULE, 65536);
        assert!(
            r.accepted,
            "the FILE is well formed — only the keys are wrong"
        );
        let mut notes = Vec::new();
        assert_eq!(
            r.validate_function(0, &ops(), &mut notes),
            Vec::<usize>::new()
        );
        assert_eq!(notes.len(), 2);
        assert!(
            notes.iter().all(|n| n.contains("out of range")),
            "{notes:?}"
        );
        assert!(notes[0].contains("OPERATOR index"), "{notes:?}");
    }

    #[test]
    fn non_access_operator_is_dropped_901() {
        let p = write_tmp(
            "nonaccess.json",
            &doc(
                &hex_sha256(MODULE),
                65536,
                r#"{"func":0,"pc":4,"op":"i32.load","width":4}"#,
            ),
        );
        let mut notes = Vec::new();
        let marks = ingest(&p, MODULE, 65536).validate_function(0, &ops(), &mut notes);
        assert_eq!(marks, Vec::<usize>::new());
        assert!(notes[0].contains("not a linear-memory access"), "{notes:?}");
    }

    #[test]
    fn width_disagreement_is_dropped_901() {
        // pc 3 is an i32.load8_u (1 B) but the file claims 4 B: the file and
        // the module disagree about which BYTES are covered — drop it.
        let p = write_tmp(
            "width.json",
            &doc(
                &hex_sha256(MODULE),
                65536,
                r#"{"func":0,"pc":3,"op":"i32.load","width":4},
                   {"func":0,"pc":1,"op":"i32.load","width":4}"#,
            ),
        );
        let mut notes = Vec::new();
        let marks = ingest(&p, MODULE, 65536).validate_function(0, &ops(), &mut notes);
        assert_eq!(
            marks,
            vec![1],
            "the sound entry survives, the skewed one does not"
        );
        assert_eq!(notes.len(), 1);
        assert!(
            notes[0].contains("disagrees with the decoded operator"),
            "{notes:?}"
        );
    }

    #[test]
    fn sites_are_keyed_per_function_901() {
        let p = write_tmp(
            "perfunc.json",
            &doc(
                &hex_sha256(MODULE),
                65536,
                r#"{"func":7,"pc":1,"op":"i32.load","width":4}"#,
            ),
        );
        let r = ingest(&p, MODULE, 65536);
        let mut notes = Vec::new();
        // Function 0 gets nothing: the verdict is func 7's.
        assert_eq!(
            r.validate_function(0, &ops(), &mut notes),
            Vec::<usize>::new()
        );
        assert!(notes.is_empty());
        assert_eq!(r.validate_function(7, &ops(), &mut notes), vec![1]);
    }

    // ---- access_width ------------------------------------------------------

    #[test]
    fn access_width_covers_the_bytes_touched_not_the_value_width_901() {
        assert_eq!(
            access_width(&WasmOp::I64Load32U {
                offset: 0,
                align: 2
            }),
            Some(4)
        );
        assert_eq!(
            access_width(&WasmOp::I64Store8 {
                offset: 0,
                align: 0
            }),
            Some(1)
        );
        assert_eq!(
            access_width(&WasmOp::I32Load16S {
                offset: 0,
                align: 1
            }),
            Some(2)
        );
        assert_eq!(
            access_width(&WasmOp::F64Load {
                offset: 0,
                align: 3
            }),
            Some(8)
        );
        assert_eq!(access_width(&WasmOp::I32Add), None);
        assert_eq!(access_width(&WasmOp::LocalGet(0)), None);
    }

    // ---- attestation -------------------------------------------------------

    #[test]
    fn attestation_sidecar_path_mirrors_the_safety_manifest_901() {
        assert_eq!(
            ElisionAttestation::sidecar_path(Path::new("/tmp/foo.elf")),
            PathBuf::from("/tmp/foo.proven-safe-elisions.json")
        );
        assert_eq!(
            ElisionAttestation::sidecar_path(Path::new("out")),
            PathBuf::from("out.proven-safe-elisions.json")
        );
    }

    #[test]
    fn refusal_is_attested_not_hidden_901() {
        let a = ElisionAttestation {
            schema: ELISION_ATTESTATION_SCHEMA.to_string(),
            synth_version: "0.55.0".to_string(),
            scry_version: "3.2.4".to_string(),
            module_sha256: "aa".repeat(32),
            declared_module_sha256: "bb".repeat(32),
            memory_min_bytes: 65536,
            declared_memory_min_bytes: 65536,
            safety_bounds: "software".to_string(),
            accepted: false,
            refusal: Some("module_sha256 mismatch".to_string()),
            sites_offered: 8,
            sites_elided: 0,
            sites_not_elided: 8,
            elisions: Vec::new(),
            diagnostics: vec!["refused".to_string()],
        };
        let json = a.to_json();
        // sigil must be able to tell "nothing to elide" from "file rejected".
        assert!(json.contains("\"accepted\": false"));
        assert!(json.contains("module_sha256 mismatch"));
        assert!(json.contains("\"sites_offered\": 8"));
        assert!(json.contains("\"sites_elided\": 0"));
        let back: ElisionAttestation = serde_json::from_str(&json).expect("round-trips");
        assert_eq!(back, a);
    }
}
