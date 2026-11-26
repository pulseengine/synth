//! P3 async host-intrinsic classification and honest degradation (#80).
//!
//! When Meld lowers a P3 (Component Model async) component to a core module,
//! the output imports RFC #46 async host intrinsics (`stream.read`,
//! `stream.write`, `waitable-set.wait`, `task.return`, `error-context.new`,
//! `future.read`, …). Synth compiles each import *call site* to a native
//! `BL <field-name>` into kiln-builtins via the existing relocatable host-link
//! path (#197) — the raw call lowering already exists and is unchanged.
//!
//! What this module adds is the missing *semantic gate* (#80): a compiler that
//! blindly emits `BL stream.read` would silently miscompile — the intrinsic
//! needs bounds-checked linear-memory buffers and register save/restore across
//! a scheduler yield, none of which synth generates yet. The #275-style honest
//! degradation is: LOWER exactly the ONE family we can compile correctly, and
//! LOUD-DECLINE every other family BY NAME with a machine reason, rather than
//! emitting a call that will misbehave at runtime.
//!
//! ## Bounded scope (#80)
//!
//! - **Lowered op: `error-context.drop`.** This is a pure scalar handle
//!   operation — it takes one error-context handle (`i32`) and returns nothing,
//!   touching no linear-memory buffer and never yielding. It marshals like any
//!   AAPCS C call (handle in `r0`), so the existing field-name `BL` path
//!   compiles it correctly today. This is the ONE op we can honestly claim.
//!   The lowering decision is made PER OP, not per family (see
//!   [`LOWERED_FIELDS`]).
//! - **Declined (everything else), each with a named [`AsyncDecline`]:**
//!   `error-context.new` / `.debug-message` (they pass a linmem message
//!   pointer — the SAME bounds-checked buffer class as stream, NOT scalar),
//!   `stream` (bounds-checked buffer memory layout — issue §3), `future`
//!   (readable/writable-end buffer protocol), `waitable`/`task` (register
//!   save/restore across the `waitable-set.wait` yield — issue §4).
//!
//! The intrinsic namespace and per-family field prefixes are the CONTRACT
//! synth compiles against; they are pinned here (single source) citing
//! RFC #46 until Meld's lowering fixes the canonical strings cross-repo
//! (meld#94).
//!
//! ## Dead legacy imports (P3-BUILTINS I1, pulseengine/meld#693)
//!
//! A declined import that the module never references (no `call`,
//! `return_call` or `ref.func`, no element-segment entry, no export, not the
//! start function) is ACCEPTED: it cannot be reached, gets no symbol and no
//! relocation, and so carries no obligation. Any reference keeps the decline
//! unchanged. See [`gate_async_imports`].

use std::collections::BTreeSet;

/// The import module namespace P3-async intrinsics are imported under.
///
/// Meld lowers P3 async components with imports in this module (RFC #46 async
/// ABI). Only imports in this namespace are subject to async classification;
/// every other import is untouched (so non-async modules stay byte-identical).
pub const ASYNC_MODULE: &str = "pulseengine:async";

/// The async intrinsic families synth distinguishes (#80).
///
/// The lowered/declined decision is made PER OP (field name), not per family
/// — within `error-context` only `.drop` is a scalar handle op; `.new` and
/// `.debug-message` transfer a message string through linear memory (canonical
/// ABI) and are declined alongside the buffer families. See [`is_lowered_field`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsyncFamily {
    /// `error-context.*` — error-context resource ops. Only `.drop` (scalar
    /// handle) is lowered; `.new` / `.debug-message` are declined (linmem
    /// message buffer, same class as stream).
    ErrorContext,
    /// `stream.*` — typed stream read/write over linear-memory buffers.
    /// **Declined** (buffer memory layout + bounds checks unimplemented).
    Stream,
    /// `future.*` — single-shot readable/writable ends. **Declined.**
    Future,
    /// `waitable-set.*` / `task.*` — scheduler yield points. **Declined**
    /// (register save/restore across yield unimplemented).
    WaitableTask,
}

/// The exact intrinsic FIELDS synth lowers today (#80). Deliberately a single
/// unambiguously-scalar op: `error-context.drop` takes one error-context handle
/// (i32) and returns nothing — it touches no linear-memory buffer and does not
/// yield, so the existing AAPCS field-name BL path compiles it correctly. Every
/// other async intrinsic (including `error-context.new` /
/// `error-context.debug-message`, which pass a linmem message pointer) is
/// declined. Widening this set requires an end-to-end test proving the pointer
/// arguments lower against the linmem base — a named follow-up.
pub const LOWERED_FIELDS: &[&str] = &["error-context.drop"];

/// Whether synth currently lowers this exact intrinsic field to native ARM.
pub fn is_lowered_field(field: &str) -> bool {
    LOWERED_FIELDS.contains(&field)
}

impl AsyncFamily {
    /// Classify an intrinsic field name into its family. Returns `None` for a
    /// field name that is not a recognized P3-async intrinsic (an unknown
    /// import in the async namespace — also a decline, see [`classify`]).
    ///
    /// Matching is by the `.`-separated resource prefix, matching the RFC #46
    /// `resource.method` naming (`stream.read`, `error-context.new`, …).
    pub fn from_field(field: &str) -> Option<Self> {
        let resource = field.split('.').next().unwrap_or(field);
        match resource {
            "error-context" => Some(AsyncFamily::ErrorContext),
            "stream" => Some(AsyncFamily::Stream),
            "future" => Some(AsyncFamily::Future),
            "waitable-set" | "waitable" | "task" => Some(AsyncFamily::WaitableTask),
            _ => None,
        }
    }

    /// A stable machine-readable family tag for diagnostics.
    pub const fn tag(self) -> &'static str {
        match self {
            AsyncFamily::ErrorContext => "error-context",
            AsyncFamily::Stream => "stream",
            AsyncFamily::Future => "future",
            AsyncFamily::WaitableTask => "waitable-task",
        }
    }
}

/// A refused P3-async import — the machine reason it cannot be compiled (#80).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AsyncDecline {
    /// The offending import field (e.g. `stream.read`).
    pub field: String,
    /// The classified family, if recognized (`None` = unknown async import).
    pub family: Option<AsyncFamily>,
    /// The machine reason string.
    pub reason: String,
}

impl core::fmt::Display for AsyncDecline {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "#80 async-intrinsic decline: {}", self.reason)
    }
}

/// The outcome of classifying a single import against the async contract.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AsyncClassification {
    /// Not a P3-async import (wrong module namespace). Untouched by #80.
    NotAsync,
    /// A P3-async import in a family synth lowers. The call flows through the
    /// existing field-name `BL` path unchanged; the carried field is the
    /// symbol name that path relocates against.
    Lowered {
        /// The lowered family (always [`AsyncFamily::ErrorContext`] today).
        family: AsyncFamily,
        /// The import field / `BL` target symbol.
        field: String,
    },
    /// A P3-async import synth refuses to compile (a declined family or an
    /// unknown async intrinsic).
    Declined(AsyncDecline),
}

/// Classify one import (`module` / `field`) against the P3-async contract (#80).
///
/// - Import module != [`ASYNC_MODULE`] → [`AsyncClassification::NotAsync`]
///   (byte-invisible: non-async modules are completely unaffected).
/// - `error-context.*` → [`AsyncClassification::Lowered`].
/// - a recognized-but-unlowered family (`stream`/`future`/`waitable`/`task`) →
///   [`AsyncClassification::Declined`] naming the family and the missing
///   capability.
/// - an unrecognized field in the async namespace → `Declined` (unknown
///   intrinsic — refuse rather than blindly `BL` an unspecified contract).
pub fn classify(module: &str, field: &str) -> AsyncClassification {
    if module != ASYNC_MODULE {
        return AsyncClassification::NotAsync;
    }
    // Lowering is decided PER OP, not per family: only the exact scalar ops in
    // LOWERED_FIELDS pass; a recognized family with an unlowered field (e.g.
    // error-context.new, which carries a linmem message pointer) is declined.
    if is_lowered_field(field) {
        let family = AsyncFamily::from_field(field)
            .expect("a LOWERED_FIELDS entry must classify into a family");
        return AsyncClassification::Lowered {
            family,
            field: field.to_string(),
        };
    }
    match AsyncFamily::from_field(field) {
        Some(fam) => AsyncClassification::Declined(AsyncDecline {
            field: field.to_string(),
            family: Some(fam),
            reason: decline_reason(fam, field),
        }),
        None => AsyncClassification::Declined(AsyncDecline {
            field: field.to_string(),
            family: None,
            reason: format!(
                "unknown P3-async intrinsic '{ASYNC_MODULE}::{field}' — synth \
                 will not emit a call against an unspecified async contract \
                 (RFC #46); recognized families: error-context (lowered), \
                 stream / future / waitable-set / task (declined)"
            ),
        }),
    }
}

/// The per-family machine reason for a declined intrinsic.
fn decline_reason(family: AsyncFamily, field: &str) -> String {
    let ns = ASYNC_MODULE;
    match family {
        AsyncFamily::ErrorContext => format!(
            "'{ns}::{field}' (error-context family) not compiled: only \
             error-context.drop (a scalar handle op) is lowered. This op \
             transfers a message string through linear memory (canonical ABI), \
             which needs the same bounds-checked linmem-base-relative buffer \
             lowering as the stream family that synth does not yet generate \
             (#80). Use error-context.drop, or link this op against a host that \
             owns the buffer protocol."
        ),
        AsyncFamily::Stream => format!(
            "'{ns}::{field}' (stream family) not compiled: synth does not yet \
             generate the bounds-checked linear-memory buffer layout the stream \
             read/write intrinsics require (#80 §3). Lower only error-context.drop \
             for now, or link the stream intrinsic against a host that owns the \
             buffer protocol."
        ),
        AsyncFamily::Future => format!(
            "'{ns}::{field}' (future family) not compiled: the readable/writable-\
             end buffer transfer protocol is unimplemented (#80 §3). Only \
             error-context.drop is lowered."
        ),
        AsyncFamily::WaitableTask => format!(
            "'{ns}::{field}' (waitable/task family) not compiled: synth does not \
             yet save/restore register state across the scheduler yield at \
             waitable-set.wait (#80 §4). Only error-context.drop is lowered."
        ),
    }
}

/// Every function index the module REFERENCES, read from the module bytes
/// (P3-BUILTINS I1, pulseengine/meld#693).
///
/// A function index is referenced when any of these names it:
/// - a `call`, `return_call` or `ref.func` operator in ANY function body;
/// - a `ref.func` in any constant expression: global initializers, table
///   initializers, element-segment items and offsets, data-segment offsets;
/// - an element segment's plain function-index list (active, passive or
///   declared segments alike — a declared segment is what licenses a
///   `ref.func`, so it counts on its own);
/// - a function export (re-exporting an import keeps it live);
/// - the start section.
///
/// These are the only places the binary format can name a function: in
/// wasmparser 0.263 the operators carrying a function index are exactly
/// `Call`, `RefFunc` and `ReturnCall`. Indices are in the FULL function index
/// space (imports first), the space [`crate::ImportEntry::index`] uses for
/// function imports.
///
/// Fail-closed: any parse error returns `Err`, and the caller must then treat
/// every import as live (see [`gate_async_imports`]).
pub fn referenced_function_indices(wasm: &[u8]) -> anyhow::Result<BTreeSet<u32>> {
    use wasmparser::{ElementItems, ElementKind, ExternalKind, Payload, TableInit};
    let mut refs = BTreeSet::new();
    for payload in wasmparser::Parser::new(0).parse_all(wasm) {
        match payload? {
            Payload::CodeSectionEntry(body) => {
                for op in body.get_operators_reader()? {
                    note_func_ref(&op?, &mut refs);
                }
            }
            Payload::GlobalSection(reader) => {
                for g in reader {
                    scan_const_expr(&g?.init_expr, &mut refs)?;
                }
            }
            Payload::TableSection(reader) => {
                for t in reader {
                    if let TableInit::Expr(e) = t?.init {
                        scan_const_expr(&e, &mut refs)?;
                    }
                }
            }
            Payload::ElementSection(reader) => {
                for elem in reader {
                    let elem = elem?;
                    if let ElementKind::Active { offset_expr, .. } = &elem.kind {
                        scan_const_expr(offset_expr, &mut refs)?;
                    }
                    match elem.items {
                        ElementItems::Functions(funcs) => {
                            for f in funcs {
                                refs.insert(f?);
                            }
                        }
                        ElementItems::Expressions(_, exprs) => {
                            for e in exprs {
                                scan_const_expr(&e?, &mut refs)?;
                            }
                        }
                    }
                }
            }
            Payload::DataSection(reader) => {
                for d in reader {
                    if let wasmparser::DataKind::Active { offset_expr, .. } = &d?.kind {
                        scan_const_expr(offset_expr, &mut refs)?;
                    }
                }
            }
            Payload::ExportSection(reader) => {
                for e in reader {
                    let e = e?;
                    if e.kind == ExternalKind::Func {
                        refs.insert(e.index);
                    }
                }
            }
            Payload::StartSection { func, .. } => {
                refs.insert(func);
            }
            _ => {}
        }
    }
    Ok(refs)
}

fn note_func_ref(op: &wasmparser::Operator<'_>, refs: &mut BTreeSet<u32>) {
    use wasmparser::Operator::{Call, RefFunc, ReturnCall};
    match op {
        Call { function_index } | ReturnCall { function_index } | RefFunc { function_index } => {
            refs.insert(*function_index);
        }
        _ => {}
    }
}

fn scan_const_expr(
    expr: &wasmparser::ConstExpr<'_>,
    refs: &mut BTreeSet<u32>,
) -> anyhow::Result<()> {
    for op in expr.get_operators_reader() {
        note_func_ref(&op?, refs);
    }
    Ok(())
}

/// A declined `pulseengine:async` function import that the module never
/// references, so it is accepted and emits no symbol (P3-BUILTINS I1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeadAsyncImport {
    /// The import field (e.g. `stream_new`).
    pub field: String,
    /// The import's index in the full function index space.
    pub func_index: u32,
}

/// The #80 gate over a module's imports (P3-BUILTINS I1).
///
/// meld's fused output (pulseengine/meld#693) still imports legacy
/// `pulseengine:async` functions (`stream_new`, `stream_write`) that nothing in
/// the module references. Such an import cannot be reached at run time: an
/// ET_REL object has no instantiation step, and an import with no reference
/// gets no symbol and no relocation, so there is nothing to bind.
///
/// For each FUNCTION import that [`classify`] declines:
/// - not in [`referenced_function_indices`] → returned as a
///   [`DeadAsyncImport`] (accepted);
/// - referenced in any way → `Err` with the classifier's decline, unchanged;
/// - the reference scan itself failed → `Err` with the same decline
///   (fail-closed: an unprovable "dead" is treated as live).
///
/// Lowered and non-async imports are untouched. The reference scan runs only
/// when a declined import exists, so a module without one costs nothing.
pub fn gate_async_imports(
    imports: &[crate::ImportEntry],
    wasm: &[u8],
) -> Result<Vec<DeadAsyncImport>, AsyncDecline> {
    let mut refs: Option<Option<BTreeSet<u32>>> = None;
    let mut dead = Vec::new();
    for imp in imports {
        if !matches!(imp.kind, crate::ImportKind::Function(_)) {
            continue;
        }
        if let AsyncClassification::Declined(d) = classify(&imp.module, &imp.name) {
            let refs = refs.get_or_insert_with(|| referenced_function_indices(wasm).ok());
            match refs {
                Some(r) if !r.contains(&imp.index) => dead.push(DeadAsyncImport {
                    field: imp.name.clone(),
                    func_index: imp.index,
                }),
                _ => return Err(d),
            }
        }
    }
    Ok(dead)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decoded_imports(wasm: &[u8]) -> Vec<crate::ImportEntry> {
        crate::decode_wasm_module(wasm)
            .expect("fixture decodes")
            .imports
    }

    fn gate_wat(wat: &str) -> Result<Vec<DeadAsyncImport>, AsyncDecline> {
        let wasm = wat::parse_str(wat).expect("fixture assembles");
        gate_async_imports(&decoded_imports(&wasm), &wasm)
    }

    /// RED-FIRST (I1, pulseengine/meld#693): a legacy `pulseengine:async`
    /// import with NO reference is accepted as dead. Before I1 there was no
    /// gate to accept it; the CLI refused it with the #80 decline.
    #[test]
    fn dead_legacy_import_is_accepted() {
        let dead = gate_wat(
            r#"(module
                 (import "pulseengine:async" "stream_new" (func (result i64)))
                 (func (export "f") (result i32) i32.const 7))"#,
        )
        .expect("a dead legacy import must be accepted");
        assert_eq!(
            dead,
            vec![DeadAsyncImport {
                field: "stream_new".into(),
                func_index: 0
            }]
        );
    }

    /// The four LIVE shapes keep the classifier's decline, unchanged:
    /// called, placed in a table by an elem segment, `ref.func`, re-exported.
    /// Plus the start section and a global initializer, the two remaining
    /// places that can name a function. (A `ref.func` in a function body is
    /// valid only when the index is also declared by an elem segment, an
    /// export or a global initializer, so the "ref.func" case is caught twice;
    /// the code-body scan is kept for modules that skip validation.)
    #[test]
    fn live_legacy_import_keeps_the_decline() {
        let imp = r#"(import "pulseengine:async" "stream_new" (func $sn (result i64)))"#;
        let cases = [
            (
                "call",
                format!(r#"(module {imp} (func (export "f") (result i64) call $sn))"#),
            ),
            (
                "elem",
                format!(r#"(module {imp} (table 1 funcref) (elem (i32.const 0) $sn))"#),
            ),
            (
                "ref.func",
                format!(
                    r#"(module {imp} (elem declare func $sn)
                         (func (export "f") (result funcref) ref.func $sn))"#
                ),
            ),
            (
                "re-export",
                format!(r#"(module {imp} (export "sn" (func $sn)))"#),
            ),
            (
                "global",
                format!(r#"(module {imp} (global funcref (ref.func $sn)))"#),
            ),
            (
                "start",
                r#"(module (import "pulseengine:async" "stream_new" (func $sn)) (start $sn))"#
                    .to_string(),
            ),
        ];
        let expected = match classify(ASYNC_MODULE, "stream_new") {
            AsyncClassification::Declined(d) => d,
            other => panic!("stream_new must classify Declined, got {other:?}"),
        };
        for (what, wat) in cases {
            assert_eq!(
                gate_wat(&wat),
                Err(expected.clone()),
                "{what}: a live legacy import must keep the #80 decline"
            );
        }
    }

    /// Only the referenced one of two legacy imports is live; the gate
    /// refuses on it (and stops), whatever the order.
    #[test]
    fn one_live_import_among_dead_ones_refuses() {
        let r = gate_wat(
            r#"(module
                 (import "pulseengine:async" "stream_new" (func (result i64)))
                 (import "pulseengine:async" "stream_write" (func $w (param i32) (result i32)))
                 (func (export "f") (result i32) i32.const 0 call $w))"#,
        );
        match r {
            Err(d) => assert_eq!(d.field, "stream_write"),
            Ok(dead) => panic!("stream_write is called, got accepted {dead:?}"),
        }
    }

    /// Fail-closed: when the reference scan cannot parse the bytes, a declined
    /// import is treated as live.
    #[test]
    fn unparseable_bytes_fail_closed() {
        let wasm = wat::parse_str(
            r#"(module (import "pulseengine:async" "stream_new" (func (result i64))))"#,
        )
        .unwrap();
        let imports = decoded_imports(&wasm);
        assert!(gate_async_imports(&imports, &wasm[..wasm.len() - 1]).is_err());
        assert!(gate_async_imports(&imports, b"not wasm").is_err());
        assert!(gate_async_imports(&imports, b"").is_err());
    }

    /// A non-async or lowered import never triggers the scan or a decline.
    #[test]
    fn non_async_and_lowered_imports_pass_untouched() {
        let dead = gate_wat(
            r#"(module
                 (import "env" "stream_new" (func $e (result i64)))
                 (import "pulseengine:async" "error-context.drop" (func $d (param i32)))
                 (func (export "f") call $e drop i32.const 0 call $d))"#,
        )
        .unwrap();
        assert!(dead.is_empty());
        // Unparseable bytes: no declined import, so no scan, so no error.
        assert_eq!(gate_async_imports(&[], b"not wasm"), Ok(vec![]));
    }

    /// The lowered op: `error-context.drop` (scalar handle) is recognized and
    /// passes through to the field-name BL path.
    #[test]
    fn error_context_drop_is_lowered() {
        assert_eq!(
            classify(ASYNC_MODULE, "error-context.drop"),
            AsyncClassification::Lowered {
                family: AsyncFamily::ErrorContext,
                field: "error-context.drop".to_string(),
            }
        );
        assert!(is_lowered_field("error-context.drop"));
    }

    /// RED-FIRST soundness (#80): the OTHER error-context ops carry a linmem
    /// message pointer and are DECLINED with the buffer reason — NOT lowered as
    /// if scalar (would silently miscompile the pointer arg).
    #[test]
    fn error_context_buffer_ops_are_declined() {
        for field in ["error-context.new", "error-context.debug-message"] {
            match classify(ASYNC_MODULE, field) {
                AsyncClassification::Declined(d) => {
                    assert_eq!(d.family, Some(AsyncFamily::ErrorContext));
                    assert!(d.reason.contains("buffer"), "{field}: {}", d.reason);
                    assert!(d.reason.contains("linear memory"), "{field}: {}", d.reason);
                }
                other => panic!("{field} must be declined (linmem buffer), got {other:?}"),
            }
            assert!(!is_lowered_field(field));
        }
    }

    /// RED-FIRST (#80): the stream family is declined BY NAME with the buffer
    /// reason.
    #[test]
    fn stream_is_declined_by_name() {
        let c = classify(ASYNC_MODULE, "stream.read");
        match c {
            AsyncClassification::Declined(d) => {
                assert_eq!(d.family, Some(AsyncFamily::Stream));
                assert!(d.reason.contains("stream"));
                assert!(d.reason.contains("buffer"));
                assert!(d.to_string().contains("stream.read"));
            }
            other => panic!("stream.read should be declined, got {other:?}"),
        }
    }

    /// RED-FIRST (#80): future and waitable/task families are declined.
    #[test]
    fn future_and_waitable_are_declined() {
        assert!(matches!(
            classify(ASYNC_MODULE, "future.read"),
            AsyncClassification::Declined(d) if d.family == Some(AsyncFamily::Future)
        ));
        assert!(matches!(
            classify(ASYNC_MODULE, "waitable-set.wait"),
            AsyncClassification::Declined(d) if d.family == Some(AsyncFamily::WaitableTask)
        ));
        assert!(matches!(
            classify(ASYNC_MODULE, "task.return"),
            AsyncClassification::Declined(d) if d.family == Some(AsyncFamily::WaitableTask)
        ));
    }

    /// An unknown intrinsic in the async namespace is declined (not blindly
    /// lowered).
    #[test]
    fn unknown_async_intrinsic_is_declined() {
        match classify(ASYNC_MODULE, "quantum.entangle") {
            AsyncClassification::Declined(d) => {
                assert_eq!(d.family, None);
                assert!(d.reason.contains("unknown"));
            }
            other => panic!("unknown intrinsic should decline, got {other:?}"),
        }
    }

    /// Byte-invisibility: a NON-async import is untouched (NotAsync). This is
    /// what keeps frozen fixtures / ordinary modules bit-identical.
    #[test]
    fn non_async_import_is_untouched() {
        assert_eq!(classify("env", "print_i32"), AsyncClassification::NotAsync);
        assert_eq!(
            classify("wasi:cli/stdout", "write"),
            AsyncClassification::NotAsync
        );
        // Same field names under a DIFFERENT module are NOT async either.
        assert_eq!(
            classify("env", "stream.read"),
            AsyncClassification::NotAsync
        );
    }

    /// The per-op lowered set is exactly `error-context.drop` and nothing
    /// else — non-vacuous in both directions.
    #[test]
    fn lowered_field_set_is_exact() {
        assert_eq!(LOWERED_FIELDS, &["error-context.drop"]);
        assert!(is_lowered_field("error-context.drop"));
        for f in [
            "error-context.new",
            "error-context.debug-message",
            "stream.read",
            "future.read",
            "waitable-set.wait",
            "task.return",
        ] {
            assert!(!is_lowered_field(f), "{f} must not be lowered");
        }
    }
}
