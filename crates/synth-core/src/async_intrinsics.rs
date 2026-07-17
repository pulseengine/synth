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
//! - **Lowered family: `error-context`.** Its intrinsics are pure scalar
//!   handle operations (`error-context.new`, `error-context.debug-message`,
//!   `error-context.drop`) — no linear-memory buffer transfer, no scheduler
//!   yield, no callback trampoline. They marshal like any AAPCS C call
//!   (handle in `r0`, result in `r0`), so the existing field-name `BL` path
//!   compiles them correctly today. This is the ONE family we can honestly
//!   claim.
//! - **Declined families:** `stream` (needs bounds-checked buffer memory
//!   layout — issue §3), `future` (needs the readable/writable-end buffer
//!   protocol), `waitable`/`task` (needs register save/restore across the
//!   `waitable-set.wait` yield — issue §4). Each is refused with a named
//!   [`AsyncDecline`] carrying the exact reason.
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsyncFamily {
    /// `error-context.*` — pure scalar handle ops. **Lowered.**
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

    /// Whether synth can currently lower this family to native ARM.
    pub const fn is_lowered(self) -> bool {
        matches!(self, AsyncFamily::ErrorContext)
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
    match AsyncFamily::from_field(field) {
        Some(fam) if fam.is_lowered() => AsyncClassification::Lowered {
            family: fam,
            field: field.to_string(),
        },
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
        AsyncFamily::ErrorContext => {
            // Unreachable — error-context is lowered — but keep total.
            format!("'{ns}::{field}' unexpectedly declined (error-context is lowered)")
        }
        AsyncFamily::Stream => format!(
            "'{ns}::{field}' (stream family) not compiled: synth does not yet \
             generate the bounds-checked linear-memory buffer layout the stream \
             read/write intrinsics require (#80 §3). Lower only error-context \
             for now, or link the stream intrinsic against a host that owns the \
             buffer protocol."
        ),
        AsyncFamily::Future => format!(
            "'{ns}::{field}' (future family) not compiled: the readable/writable-\
             end buffer transfer protocol is unimplemented (#80 §3). Only \
             error-context is lowered."
        ),
        AsyncFamily::WaitableTask => format!(
            "'{ns}::{field}' (waitable/task family) not compiled: synth does not \
             yet save/restore register state across the scheduler yield at \
             waitable-set.wait (#80 §4). Only error-context is lowered."
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The lowered family: error-context intrinsics are recognized and pass
    /// through to the field-name BL path.
    #[test]
    fn error_context_is_lowered() {
        for field in [
            "error-context.new",
            "error-context.debug-message",
            "error-context.drop",
        ] {
            assert_eq!(
                classify(ASYNC_MODULE, field),
                AsyncClassification::Lowered {
                    family: AsyncFamily::ErrorContext,
                    field: field.to_string(),
                },
                "{field} should be lowered"
            );
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

    /// The lowered family flips the is_lowered predicate; declined ones do not.
    #[test]
    fn is_lowered_predicate_is_non_vacuous() {
        assert!(AsyncFamily::ErrorContext.is_lowered());
        assert!(!AsyncFamily::Stream.is_lowered());
        assert!(!AsyncFamily::Future.is_lowered());
        assert!(!AsyncFamily::WaitableTask.is_lowered());
    }
}
