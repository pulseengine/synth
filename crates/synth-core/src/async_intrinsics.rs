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

#[cfg(test)]
mod tests {
    use super::*;

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
