//! #778 (v0.46 Wave-1 Lane 2) — the `synth-wcet-v1` static worst-case-cycle map.
//!
//! synth holds the EXACT final instruction sequence of every compiled function,
//! so it is the natural owner of a SOUND static per-function worst-case execution
//! time (WCET) bound. gale's schedulability track (spar T3/T4) computes a
//! machine-checked response-time bound, but its per-task cost inputs (`C_i`) are
//! only DWT high-water-marks — *observations*, not *bounds* — and a hard build
//! gate forbids sizing budgets from DWT. This sidecar supplies the missing SOUND
//! input: a cycle bound that is provably ≥ any real execution of the function.
//!
//! ## Soundness contract (the whole point)
//!
//! A bound that is EVER less than the real cycle count is a defect. This module
//! is therefore deliberately conservative and DECLINES loudly rather than emit a
//! number it cannot defend:
//!
//! - **Loop-free functions** get an EXACT-form bound: every instruction in the
//!   final stream executes at most once, so the bound is the SUM of each
//!   instruction's documented worst-case cycles. Summing every instruction
//!   (including both arms of an `if/else`) is an over-estimate, hence sound; no
//!   path enumeration is needed.
//! - **Loops with statically-evident trip counts** (#778 phase 2): a canonical
//!   counted loop — const-initialized counter, const step, const bound, single
//!   backward branch — whose trip count synth PROVES from the final instruction
//!   stream gets `trip × body-worst + overhead` as an upper bound; every
//!   instruction's cost is multiplied by its proven worst-case execution count.
//!   Nested loops multiply only when EVERY level proves.
//! - **Everything else** — any loop synth cannot prove a trip count for
//!   (data-dependent bounds, non-canonical shapes), any residual/external
//!   label branch (unknown direction), any call (`Bl`/`Blx`, inter-procedural),
//!   any op whose encoder expansion contains an internal runtime loop
//!   (`i64` software div/rem), any unsupported core class — is DECLINED with a
//!   machine-readable reason. gale cannot size a budget from an unsound number,
//!   so a decline is strictly better than a guess.
//!
//! `--wcet-hints` (#778 phase 2, the scry seam) supplies UNTRUSTED per-loop
//! trip-count hints; each is soundly CHECKED against synth's own induction
//! proof before use and REJECTED with a machine reason otherwise (see
//! [`WcetHints`] / [`WcetHintReject`]). Richer hint certificates (data-dependent
//! bounds) and inter-procedural composition remain the named scry / spar
//! follow-ups, explicitly OUT of scope.
//!
//! ## Precondition — a bound without its assumptions is not a safety input
//!
//! The per-instruction cycle numbers are documented worst cases for the
//! **Cortex-M3 / Cortex-M4(F)** in-order pipeline under a **zero-wait-state**
//! instruction memory (flash accelerator / I-cache hit). The bound is CONDITIONAL
//! on that precondition, which is recorded in the JSON (`core_class`,
//! `wait_states`, `memory_assumption`) so the T4 consumer knows exactly what it
//! holds under. Cortex-M7 (dual-issue + caches with wait-states that can make
//! actual cycles EXCEED a zero-wait straight sum) is DECLINED, not
//! approximated — soundness over coverage.
//!
//! ## Schema (`synth-wcet-v1`)
//!
//! A JSON sidecar written next to the object (`<output>.wcet.json`). Purely
//! additive metadata: it is derived from the already-decided instruction stream
//! and never touches `.text`, so the emitted bytes are byte-identical whether or
//! not the bound is emitted (frozen-safe).

use serde::{Deserialize, Serialize};

/// The schema version string embedded at the top of the sidecar.
pub const SCHEMA: &str = "synth-wcet-v1";

/// The schema string a `--wcet-hints` file must carry (#778 phase 2).
pub const HINTS_SCHEMA: &str = "synth-wcet-hints-v1";

/// Why a function could not receive a sound static cycle bound. Each variant is a
/// distinct, machine-readable decline reason so a consumer (spar T4) can tell an
/// unbounded loop from an inter-procedural edge from an unsupported core.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WcetDecline {
    /// A backward branch in the final instruction stream — a loop — whose trip
    /// count synth could NOT statically prove (#778 phase 2 proves canonical
    /// const-init/const-step/const-bound counted loops; equality-exit shapes
    /// additionally need a verified `--wcet-hints` entry). Data-dependent
    /// bounds remain the scry loop-bound-inference follow-up.
    Loop,
    /// A DIRECT call (`Bl func_N`) that could not be composed into a bound because
    /// the callee is unbounded or unresolvable in THIS module — an external/imported
    /// callee (a WASM import, `__meld_dispatch_import`, or an `__aeabi_*` runtime
    /// helper: it has no per-function body in this module to sum). #778 phase 3
    /// composes direct calls to LOCAL, bounded callees over the direct call graph;
    /// this reason remains for the direct edges that cannot be composed.
    Call,
    /// A cycle in the direct call graph (self-recursion or mutual recursion). An
    /// upper cycle bound cannot be composed from a call graph that revisits a frame
    /// an unbounded number of times, so every function on the cycle DECLINES. This
    /// is the #778 phase-3 decline-honesty guard: composition only bounds an acyclic
    /// direct call graph.
    Recursion,
    /// An INDIRECT call (`Blx <reg>` / `call_indirect` / a function-pointer
    /// dispatch such as `__meld_dispatch_import`): the callee is not statically
    /// known, so its bound cannot be composed. Declined, not guessed. (#778 phase 3.)
    IndirectCall,
    /// A caller whose own body is bounded but that DIRECTLY calls a callee which
    /// itself declined (transitively): a decline must PROPAGATE up the call graph —
    /// a caller cannot be bounded while a callee it invokes is unbounded. (#778
    /// phase 3.) The `note()` names the first unbounded callee for diagnosis.
    CalleeUnbounded,
    /// A residual/external label branch (`B`/`Bcc`/… still carrying a label): its
    /// direction is not statically known here, so it cannot be proven loop-free.
    UnresolvedBranch,
    /// An op whose encoder expansion contains an internal RUNTIME loop (the `i64`
    /// software div/rem shift-subtract: emitted once but executed 64×). Its body
    /// bytes appear once in the stream, so a straight sum would undercount — a
    /// sound bound needs a per-op `trip × body` model, a named follow-up.
    LoopedExpansion,
    /// The target core class is not soundly summable with a zero-wait per-op table
    /// (Cortex-M7/M7dp: dual-issue + cache wait-states). Declined, not
    /// approximated.
    UnsupportedCore,
    /// An op the cycle model has not classified.
    ///
    /// This comment used to claim the variant was "never emitted in a released
    /// build (the classifier is exhaustive with no wildcard)". That conflated
    /// two different things and was FALSE: `op_cost` has no wildcard arm, so it
    /// is exhaustive in the *compiler's* sense, but a large number of its arms
    /// return `Unmodeled` deliberately — every `i64` pseudo-op (`I64Add`,
    /// `I64Const`, `I64Ldr`, `I64Str`, `I64ExtendI32S/U`, `I32WrapI64`, the i64
    /// compares) and the whole MVE/Helium f32 vector family. Exhaustive over
    /// variants is not the same as costed for every variant.
    ///
    /// gale hit it immediately (#921): 9 of 31 functions on a real object, the
    /// second-largest decline category, clustered in time/timer code.
    ///
    /// WHICH op that is, we could not say from here — reproducing gale's object
    /// needs meld + loom + the composite. That inability IS the issue. Locally
    /// `i64.load` reproduces the decline (`I64Ldr`), while `i64.add`,
    /// `i64.ge_s` and `i64.extend_i32_u` all come out BOUNDED because the
    /// selector expands them before the WCET pass sees them — so "it will be
    /// the i64 family" was a guess worth not shipping. The `op` field is what
    /// answers it, on gale's object rather than by inference from ours.
    ///
    /// The decline now names the OP and its BYTE OFFSET (see the `op`/`offset`
    /// fields on [`WcetFunction::Declined`]) so a consumer gets a bounded
    /// request against the cycle model instead of a 31-function bisect.
    UnmodeledOp,
}

impl WcetDecline {
    /// A short human-readable explanation, embedded alongside the machine reason.
    pub fn note(&self) -> &'static str {
        match self {
            WcetDecline::Loop => {
                "backward branch (loop) without a statically-proven trip count — \
                 canonical const-bound counted loops are proven automatically; \
                 equality-exit shapes need a verified --wcet-hints entry; \
                 data-dependent bounds are the scry loop-bound-inference follow-up"
            }
            WcetDecline::Call => {
                "direct call to an external/imported/unresolvable callee with no \
                 per-function bound in this module — cannot compose an \
                 inter-procedural bound (local direct calls ARE composed, #778 phase 3)"
            }
            WcetDecline::Recursion => {
                "cycle in the direct call graph (self- or mutual recursion) — an \
                 upper cycle bound cannot be composed from a recursive call graph"
            }
            WcetDecline::IndirectCall => {
                "indirect call (Blx <reg> / call_indirect / function-pointer \
                 dispatch) — the callee is not statically known, cannot compose"
            }
            WcetDecline::CalleeUnbounded => {
                "a directly-called callee is itself unbounded — the decline \
                 propagates up the call graph (a caller cannot be bounded while a \
                 callee it invokes is unbounded)"
            }
            WcetDecline::UnresolvedBranch => {
                "residual external/unresolved label branch — direction not \
                 statically known, cannot prove loop-free"
            }
            WcetDecline::LoopedExpansion => {
                "op expands to an internal runtime loop (i64 software div/rem, \
                 executed 64×) — straight sum would undercount"
            }
            WcetDecline::UnsupportedCore => {
                "core class not soundly summable with a zero-wait per-op table \
                 (Cortex-M7 dual-issue + cache wait-states)"
            }
            WcetDecline::UnmodeledOp => "op not classified by the cycle model",
        }
    }
}

/// How a loop's trip count was established (#778 phase 2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WcetLoopBoundSource {
    /// Fully static proof: const-initialized counter, const step, const bound,
    /// exit-guaranteeing comparison — the trip count is derived by synth alone.
    Static,
    /// The loop is an equality-exit shape synth only bounds under an explicit
    /// `--wcet-hints` assertion; the hint was CHECKED against synth's own derived
    /// trip count (divisibility + monotonicity + derived ≤ hint) before use. The
    /// emitted trip count is still synth's DERIVED value, never the raw hint.
    HintVerified,
    /// (#778 phase 5) The loop's exit bound is a DATA-DEPENDENT masked ceiling
    /// (`i REL (x & K)` for a runtime `x`): the real per-iteration bound lies in
    /// `[0, K]` for ANY input (`x & K ∈ [0,K]`), so synth DERIVES the worst-case
    /// trip as the MAX over both endpoints of that interval (`rhs = K` and
    /// `rhs = 0`, both required to terminate) — an entry-independent ceiling.
    /// Like [`HintVerified`] this is HINT-GATED: the derived trip is consumed
    /// only under an explicit `--wcet-hints` entry the derived count respects
    /// (`derived ≤ hint`); the emitted trip is synth's DERIVED value, never the
    /// raw hint. A distinct source (not `HintVerified`) so the sidecar states the
    /// extra data-dependent-ceiling assumption the bound rests on.
    MaskCeiling,
}

/// One proven-bounded loop inside a bounded function (#778 phase 2). Loops are
/// listed in ascending `head_offset` order — the SAME order `--wcet-hints`
/// `loop_bounds` entries are matched by.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WcetLoopBound {
    /// Byte offset of the loop head (backward-branch target) within the function.
    pub head_offset: u64,
    /// The PROVEN maximum number of body executions (full iterations).
    pub trip_count: u64,
    /// Number of instructions inside the loop region (head..=backward branch),
    /// so a consumer can cross-check `cycles ≥ trip_count × region_instr_count`
    /// (every instruction costs ≥ 1 cycle).
    pub region_instr_count: usize,
    /// How the trip count was established.
    pub source: WcetLoopBoundSource,
    /// The hint value consumed (present iff `source == HintVerified` or a
    /// redundant hint was cross-checked against a static proof).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hint: Option<u64>,
}

/// Machine-readable reason a `--wcet-hints` entry was REJECTED (#778 phase 2).
/// The hint file is UNTRUSTED input: a hint is only ever consumed after synth
/// verifies the loop's induction against it; everything else lands here.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WcetHintReject {
    /// The hint is SMALLER than synth's own derived trip count — a wrong hint.
    /// Trusting it would emit a bound < a real execution (the fatal class).
    HintBelowDerivedTrip,
    /// synth could not verify the loop's induction against the hint (counter not
    /// provably monotonic toward a statically-known bound ≤ hint — e.g. a
    /// data-dependent bound register, a non-canonical shape, or an equality exit
    /// whose step does not divide the distance). An unverifiable hint is never
    /// trusted into a bound.
    HintUnverifiableInduction,
    /// The hint indexes a loop that does not exist in this function's final
    /// instruction stream.
    HintUnknownLoop,
    /// A recursion-depth hint (`recursion_depth`) was offered but synth could NOT
    /// verify the self-recursion is a single-self-call chain whose controlling
    /// value is entry-independently bounded (a masked-slot counter decreasing by a
    /// const step toward a base guard on the SAME masked quantity). Without an
    /// entry-independent ceiling the true depth is runtime-unbounded, so the hint
    /// is never trusted into a bound. (#778 phase 4 / #49.)
    HintUnverifiableRecursion,
    /// A recursion-depth hint is SMALLER than synth's own DERIVED maximum depth
    /// (the entry-independent ceiling proven from the masked-slot induction). A
    /// hint below the derived depth is a wrong oracle claim — trusting it would
    /// emit a bound < a real execution (the fatal class). (#778 phase 4 / #49.)
    HintBelowDerivedDepth,
}

impl WcetHintReject {
    /// A short human-readable explanation, embedded alongside the machine reason.
    pub fn note(&self) -> &'static str {
        match self {
            WcetHintReject::HintBelowDerivedTrip => {
                "hint is below synth's derived trip count — a wrong hint; \
                 trusting it would emit an unsound bound"
            }
            WcetHintReject::HintUnverifiableInduction => {
                "loop induction not verifiable against the hint (counter not \
                 provably monotonic toward a statically-known bound ≤ hint) — \
                 an unverifiable hint is never trusted into a bound"
            }
            WcetHintReject::HintUnknownLoop => {
                "hint indexes a loop that does not exist in the final \
                 instruction stream"
            }
            WcetHintReject::HintUnverifiableRecursion => {
                "recursion-depth hint not verifiable — the self-recursion is not a \
                 single-self-call chain whose controlling value is entry-independently \
                 bounded (masked-slot counter decreasing by a const step toward a base \
                 guard on the same masked quantity); depth is runtime-unbounded, so \
                 the hint is never trusted into a bound"
            }
            WcetHintReject::HintBelowDerivedDepth => {
                "recursion-depth hint is below synth's derived maximum depth (the \
                 entry-independent ceiling proven from the masked-slot induction) — \
                 a wrong hint; trusting it would emit an unsound bound"
            }
        }
    }
}

/// One rejected hint, recorded in the sidecar so the oracle (scry) sees exactly
/// which of its claims synth refused and why.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WcetHintRejection {
    /// Index into the function's `loop_bounds` hint array (== loop order by
    /// ascending head offset).
    pub loop_index: usize,
    /// Byte offset of the loop head this hint addressed, when the loop exists.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub head_offset: Option<u64>,
    /// The rejected hint value.
    pub hint: u64,
    /// Machine-readable rejection reason.
    pub reason: WcetHintReject,
    /// Human-readable note (`reason.note()`).
    pub note: String,
}

/// (#778 phase 4 / #49) The self-recursion record carried on a bounded function
/// whose bound was composed via a verified recursion-depth certificate, so the
/// sidecar states exactly how the frame count was established (and that a hint gated
/// it — the derived depth is still synth's own).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WcetRecursionBound {
    /// The DERIVED maximum recursion depth (entry-independent ceiling).
    pub max_depth: u64,
    /// The number of frames folded into the bound (`max_depth + 1`, counting the
    /// base frame). Diagnostic — lets a consumer cross-check `cycles ≥ frames`.
    pub frame_count: u64,
    /// The `--wcet-hints` `recursion_depth` value that gated the certificate (the
    /// emitted `max_depth` is synth's DERIVED value, never this raw hint).
    pub hint: u64,
}

/// (#1063) The durable per-function hint-key contract, emitted in the sidecar so
/// a consumer joins against the key `--wcet-hints` will actually accept instead
/// of re-deriving it from mangled symbols (a hand-written mirror of a shipped
/// decision — the class this project removes, not adds).
///
/// `key` is chosen by [`assign_hint_keys`], in priority order: the export name;
/// else the `name`-section name with its non-content-derived mangling components
/// stripped ([`stable_name_key`]) when that stripped form is unique in the
/// module; else the raw `name`-section name; else `func_<index>` as the last
/// resort. `build_local` is scry#137's flag: `true` means the key is NOT
/// expected to survive an unrelated rebuild (a raw mangled name still carrying
/// its crate disambiguator, or a bare index), so a hints file keyed on it must
/// be regenerated per build.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WcetHintKey {
    /// The canonical key a `--wcet-hints` entry addresses this function by.
    pub key: String,
    /// `true` when the key churns across rebuilds (raw disambiguated mangling,
    /// or an index): usable only against the build that emitted this sidecar.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub build_local: bool,
}

/// The per-function result: either a sound cycle bound or a loud decline.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
pub enum WcetFunction {
    /// A sound upper bound on this function's execution in cycles.
    Bounded {
        /// Function name (WASM export or generated).
        name: String,
        /// The sound worst-case cycle bound. For a loop-free function this is the
        /// SUM of each instruction's documented worst-case cycles (each executes
        /// at most once). For a function whose loops ALL have proven trip counts
        /// (#778 phase 2) each instruction's cost is multiplied by its proven
        /// worst-case execution count. Always ≥ any real execution under the
        /// stated precondition.
        cycles: u64,
        /// Number of ARM instructions summed (diagnostic).
        instr_count: usize,
        /// Proven loops (empty for a loop-free function), ascending head offset.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        loops: Vec<WcetLoopBound>,
        /// (#778 phase 4 / #49) Present iff this bound was composed via a verified
        /// self-recursion certificate; states the derived depth + frame count.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        recursion: Option<WcetRecursionBound>,
        /// Hints that were rejected (the static proof stands independently).
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        hint_rejections: Vec<WcetHintRejection>,
        /// (#1063) The key `--wcet-hints` matches this function on, plus its
        /// build-locality — filled by the module driver, absent on sidecars
        /// predating the field (additive).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        hint_key: Option<WcetHintKey>,
    },
    /// No bound emitted — a loud decline with a machine-readable reason. A decline
    /// is emitted (rather than the function omitted) so the map is COMPLETE: a
    /// consumer sees every function is either bounded or explicitly unbounded,
    /// never silently missing.
    Declined {
        /// Function name.
        name: String,
        /// Machine-readable reason.
        reason: WcetDecline,
        /// Human-readable note (`reason.note()`).
        note: String,
        /// (#921) The op that caused the decline, as its `ArmOp` variant name
        /// (`I64Add`, `MveDivF32`, …). Emitted for `unmodeled-op`, where the
        /// reason alone left a consumer nothing to act on but a hand-bisect.
        ///
        /// ADDITIVE and optional: absent for every other reason, and absent
        /// when it cannot be determined, so existing consumers are unaffected.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        op: Option<String>,
        /// (#921) Byte offset of that op within the function, from the REAL
        /// encoder — the same source of truth `WcetLoopBound::head_offset`
        /// uses, so the two are cross-referenceable in one disassembly.
        ///
        /// `None` when any preceding op is one the encoder refuses: an offset
        /// that cannot be computed is OMITTED, never approximated, because a
        /// wrong offset sends a consumer to the wrong instruction.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        offset: Option<u64>,
        /// Hints that were offered for this function and rejected.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        hint_rejections: Vec<WcetHintRejection>,
        /// (#1063) The key `--wcet-hints` matches this function on, plus its
        /// build-locality — filled by the module driver, absent on sidecars
        /// predating the field (additive).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        hint_key: Option<WcetHintKey>,
    },
}

impl WcetFunction {
    /// Construct a decline, filling in the note from the reason.
    pub fn declined(name: impl Into<String>, reason: WcetDecline) -> Self {
        let note = reason.note().to_string();
        WcetFunction::Declined {
            name: name.into(),
            reason,
            note,
            op: None,
            offset: None,
            hint_rejections: Vec::new(),
            hint_key: None,
        }
    }

    /// (#921) Construct a decline that NAMES the offending op and its byte
    /// offset. Used for `unmodeled-op`, whose reason string alone left a
    /// consumer with nothing to act on but a hand-bisect of the whole object.
    ///
    /// `offset` is `None` when the byte position could not be computed from the
    /// real encoder; the op name is still emitted, because "which instruction"
    /// is the actionable half even without "where".
    pub fn declined_at(
        name: impl Into<String>,
        reason: WcetDecline,
        op: impl Into<String>,
        offset: Option<u64>,
    ) -> Self {
        let note = reason.note().to_string();
        WcetFunction::Declined {
            name: name.into(),
            reason,
            note,
            op: Some(op.into()),
            offset,
            hint_rejections: Vec::new(),
            hint_key: None,
        }
    }

    /// Construct a decline carrying rejected-hint records.
    pub fn declined_with_rejections(
        name: impl Into<String>,
        reason: WcetDecline,
        hint_rejections: Vec<WcetHintRejection>,
    ) -> Self {
        let note = reason.note().to_string();
        WcetFunction::Declined {
            name: name.into(),
            reason,
            note,
            op: None,
            offset: None,
            hint_rejections,
            hint_key: None,
        }
    }

    /// The function name this entry is keyed by in the sidecar.
    pub fn name(&self) -> &str {
        match self {
            WcetFunction::Bounded { name, .. } | WcetFunction::Declined { name, .. } => name,
        }
    }

    /// (#1063) Rewrite this entry to its durable identity: the display name plus
    /// the hint-key contract the driver assigned. Called by the module driver
    /// after composition (composition works in compile names, `func_<idx>` for
    /// internal functions).
    pub fn set_identity(&mut self, display_name: &str, key: &WcetHintKey) {
        match self {
            WcetFunction::Bounded { name, hint_key, .. }
            | WcetFunction::Declined { name, hint_key, .. } => {
                *name = display_name.to_string();
                *hint_key = Some(key.clone());
            }
        }
    }
}

/// (#1063) Derive the STABLE form of a `name`-section name — the part of the
/// name that IS content-derived, with the components that churn per build
/// stripped. Measured motivation (gale #1063 / scry#123): Rust v0 mangling
/// carries a crate disambiguator (`Cs942N1ctoMYm_`) hashed from crate metadata
/// (compiler version, feature flags, …) — NOT from the function's content — and
/// 43–45 % of function identities churn per build for exactly this reason. A
/// hints key that churns every build trades an unaddressable decline for an
/// unreliable one, so the key strips:
///
/// - every v0 crate-root disambiguator `C s <base62>+ _` → `C` (scry#137 tier 1;
///   local disambiguators like closures' `s_0` are source-order-derived and are
///   KEPT — only the crate-metadata hash is stripped);
/// - a legacy-mangling content hash suffix `17h<16 hex>E` → `E`, and its
///   demangled form `::h<16 hex>` at the end of the name.
///
/// The scan is textual, not a full mangling parse: a pathological identifier
/// that CONTAINS the pattern strips too. That is deliberate — both sides of the
/// join (this function emitting `hint_key` and the author copying it from the
/// sidecar) use the same derivation, so consistency is what matters; a
/// pathological merge of two distinct names is caught by [`assign_hint_keys`]'s
/// uniqueness check and demoted to a build-local raw key, never silently
/// mis-keyed.
pub fn stable_name_key(raw: &str) -> String {
    // v0 mangling: crate-root disambiguator `C s <base62>+ _` → `C`.
    let b = raw.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(b.len());
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'C' && i + 1 < b.len() && b[i + 1] == b's' {
            let mut j = i + 2;
            while j < b.len() && b[j].is_ascii_alphanumeric() {
                j += 1;
            }
            if j > i + 2 && j < b.len() && b[j] == b'_' {
                out.push(b'C');
                i = j + 1;
                continue;
            }
        }
        out.push(b[i]);
        i += 1;
    }
    // Only removed ASCII substrings above, so this cannot fail; the fallback is
    // pure defense.
    let mut out = String::from_utf8(out).unwrap_or_else(|_| raw.to_string());
    if !out.is_ascii() {
        return out;
    }
    // Legacy mangling: `…17h<16 hex>E` → `…E`.
    if out.len() >= 20 && out.ends_with('E') {
        let tail = &out[out.len() - 20..out.len() - 1];
        if let Some(hex) = tail.strip_prefix("17h")
            && hex.bytes().all(|c| c.is_ascii_hexdigit())
        {
            out.truncate(out.len() - 20);
            out.push('E');
            return out;
        }
    }
    // Demangled legacy hash: trailing `::h<16 hex>`.
    if out.len() >= 19 {
        let tail = &out[out.len() - 19..];
        if let Some(hex) = tail.strip_prefix("::h")
            && hex.bytes().all(|c| c.is_ascii_hexdigit())
        {
            out.truncate(out.len() - 19);
        }
    }
    out
}

/// (#1063) A compiled function's identity inputs, as the module driver knows
/// them: full-index-space index, export name (if exported), and `name`-section
/// name (if the module carries one for it).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WcetFnIdentity {
    /// Full function index (imports first — the space `func_<index>` names).
    pub index: u32,
    /// The export name, when the function is exported.
    pub export_name: Option<String>,
    /// The `name`-section name, when present (debug metadata, untrusted-benign).
    pub debug_name: Option<String>,
}

/// (#1063) The assigned identity for one function: what the backend compiled it
/// as, what the sidecar displays, the canonical hint key, and every key a
/// `--wcet-hints` entry may address it by.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WcetKeyAssignment {
    /// The name the backend compiled under (export name, else `func_<index>`) —
    /// the key composition and the resolved hints map work in.
    pub compile_name: String,
    /// The sidecar display name: export name, else the RAW `name`-section name
    /// (so a consumer can join against symbols), else `func_<index>`.
    pub display_name: String,
    /// The canonical hint key + build-locality (see [`WcetHintKey`]).
    pub hint_key: WcetHintKey,
    /// Every key a hints entry may address this function by (the canonical key,
    /// plus the raw `name`-section name when it is unambiguous). `func_<index>`
    /// is deliberately NOT accepted for a function that carries a real name: an
    /// index silently retargets when an unrelated edit renumbers the space,
    /// which is worse than no key (#1063).
    pub accepted_keys: Vec<String>,
}

/// (#1063) Assign every function its durable WCET identity. Key priority:
/// export name → stripped `name`-section name (when unique module-wide and not
/// shadowing an export) → raw `name`-section name (unique, not shadowing;
/// build-local) → `func_<index>` (build-local last resort). Uniqueness is
/// checked over ALL functions' candidate names so two functions can never be
/// assigned the same stable key; residual cross-tier collisions are additionally
/// rejected as ambiguous at resolution time ([`resolve_hint_keys`]), so an
/// ambiguous key is never silently applied to the wrong function.
pub fn assign_hint_keys(fns: &[WcetFnIdentity]) -> Vec<WcetKeyAssignment> {
    use std::collections::{HashMap, HashSet};
    let exports: HashSet<&str> = fns
        .iter()
        .filter_map(|f| f.export_name.as_deref())
        .collect();
    let mut stripped_counts: HashMap<String, usize> = HashMap::new();
    let mut raw_counts: HashMap<&str, usize> = HashMap::new();
    for f in fns {
        if let Some(d) = f.debug_name.as_deref() {
            *stripped_counts.entry(stable_name_key(d)).or_default() += 1;
            *raw_counts.entry(d).or_default() += 1;
        }
    }
    fns.iter()
        .map(|f| {
            let fallback = format!("func_{}", f.index);
            let raw_ok = |d: &str| raw_counts.get(d).copied() == Some(1) && !exports.contains(d);
            let (compile_name, display_name, key, build_local) =
                match (&f.export_name, &f.debug_name) {
                    (Some(e), _) => (e.clone(), e.clone(), e.clone(), false),
                    (None, Some(d)) => {
                        let stripped = stable_name_key(d);
                        if stripped_counts.get(&stripped).copied() == Some(1)
                            && !exports.contains(stripped.as_str())
                        {
                            (fallback.clone(), d.clone(), stripped, false)
                        } else if raw_ok(d) {
                            (fallback.clone(), d.clone(), d.clone(), true)
                        } else {
                            (fallback.clone(), d.clone(), fallback.clone(), true)
                        }
                    }
                    (None, None) => (fallback.clone(), fallback.clone(), fallback.clone(), true),
                };
            let mut accepted = vec![key.clone()];
            // The raw name-section name is always an accepted alias when it is
            // unambiguous — a hint keyed on the symbol the author sees in a
            // disassembly must land (or be loudly rejected), never be ignored.
            if let Some(d) = f.debug_name.as_deref()
                && raw_ok(d)
                && !accepted.iter().any(|k| k == d)
            {
                accepted.push(d.to_string());
            }
            WcetKeyAssignment {
                compile_name,
                display_name,
                hint_key: WcetHintKey { key, build_local },
                accepted_keys: accepted,
            }
        })
        .collect()
}

/// (#1063) The outcome of resolving a `--wcet-hints` file against the module's
/// key assignments: the re-keyed hints map (keyed by COMPILE name, the key the
/// backend's per-function verifier looks up), which original keys resolved to
/// which function, and a named diagnostic for every entry that was NOT consumed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WcetHintResolution {
    /// The hints, re-keyed by compile name, ready for the backend.
    pub hints: WcetHints,
    /// `(original key, compile_name)` for every entry that resolved.
    pub resolved: Vec<(String, String)>,
    /// One named, human-readable reason per entry that was NOT consumed — the
    /// driver prints each. An ignored-because-unmatched hint and a rejected
    /// hint look identical to a `$?` check; the named reason is the difference.
    pub diagnostics: Vec<String>,
}

/// (#1063) Resolve every `--wcet-hints` entry against the module's accepted
/// keys. Each entry either resolves to exactly one function (and is re-keyed to
/// that function's compile name) or produces a NAMED diagnostic:
/// ambiguous key, duplicate entry, refused index key (the function carries a
/// real name — an index is not an identity), or unknown key. No entry is ever
/// silently ignored.
pub fn resolve_hint_keys(
    hints: WcetHints,
    assignments: &[WcetKeyAssignment],
) -> WcetHintResolution {
    use std::collections::HashMap;
    let mut by_key: HashMap<&str, Vec<usize>> = HashMap::new();
    for (i, a) in assignments.iter().enumerate() {
        for k in &a.accepted_keys {
            let v = by_key.entry(k.as_str()).or_default();
            if !v.contains(&i) {
                v.push(i);
            }
        }
    }
    let mut out = WcetHints {
        schema: hints.schema,
        functions: std::collections::BTreeMap::new(),
    };
    let mut resolved: Vec<(String, String)> = Vec::new();
    let mut diagnostics: Vec<String> = Vec::new();
    for (k, entry) in hints.functions {
        match by_key.get(k.as_str()).map(Vec::as_slice) {
            Some([i]) => {
                let a = &assignments[*i];
                if out.functions.contains_key(&a.compile_name) {
                    diagnostics.push(format!(
                        "--wcet-hints key '{k}' duplicates an earlier entry for function \
                         '{}' — this entry was not consumed (wcet-hint-key-duplicate, #1063)",
                        a.display_name
                    ));
                } else {
                    out.functions.insert(a.compile_name.clone(), entry);
                    resolved.push((k, a.compile_name.clone()));
                }
            }
            Some(many) => diagnostics.push(format!(
                "--wcet-hints key '{k}' is AMBIGUOUS in this module ({} functions accept \
                 it) — the hint was not consumed (wcet-hint-key-ambiguous, #1063)",
                many.len()
            )),
            None => {
                // An index key for a function that carries a real name is
                // REFUSED by design, and the diagnostic names the key to use:
                // an index silently retargets when an unrelated edit adds or
                // removes an earlier function, converting a decline for a
                // function whose shape nobody looked at.
                if let Some(a) = assignments
                    .iter()
                    .find(|a| a.compile_name == k && !a.accepted_keys.iter().any(|ak| *ak == k))
                {
                    diagnostics.push(format!(
                        "--wcet-hints key '{k}' is an INDEX key, but that function carries \
                         the name '{}' — an index is not an identity (it silently retargets \
                         when the index space shifts), so it is refused; key the hint on \
                         '{}' instead (wcet-hint-key-index-refused, #1063)",
                        a.display_name, a.hint_key.key
                    ));
                } else {
                    diagnostics.push(format!(
                        "--wcet-hints names function '{k}' which is not in this module — \
                         the hint was not consumed (wcet-hint-key-unknown)"
                    ));
                }
            }
        }
    }
    WcetHintResolution {
        hints: out,
        resolved,
        diagnostics,
    }
}

/// (#778 phase 4 / #49) A proven SELF-recursion certificate: the function is a
/// single-self-call chain whose controlling value is entry-independently bounded
/// (a masked-slot counter decreasing by a const step toward a base guard on the
/// SAME masked quantity), so its maximum recursion DEPTH is DERIVED (not
/// hint-supplied) as an entry-independent ceiling. The composer folds the self-edge
/// as `frame_count × frame_cost` (`frame_count = max_depth + 1`, counting the base
/// frame) instead of declining `Recursion`.
///
/// A certificate is attached ONLY after the depth was cross-checked against a
/// `--wcet-hints` `recursion_depth` entry (the untrusted oracle asserts intent;
/// synth's derived ceiling is what is emitted). Without a hint the recursion still
/// declines (a bound this consequential is opt-in, mirroring the equality-exit
/// loop-hint gate). `self_label` is the function's own `func_<idx>` self-call label
/// so the composer can identify and special-case exactly that edge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WcetRecursionCert {
    /// The self-call `BL` label (`func_<idx>`) this certificate authorizes.
    pub self_label: String,
    /// The DERIVED maximum recursion depth (entry-independent ceiling). The base
    /// frame is NOT included here — the composer uses `max_depth + 1` frames.
    pub max_depth: u64,
    /// The hint value that gated this certificate (recorded for the sidecar; the
    /// emitted depth is always the derived `max_depth`, never the raw hint).
    pub hint: u64,
}

/// One direct call site inside a composable function (#778 phase 3). Records the
/// callee's `BL` label (`func_<idx>` for a local/relocatable-import call) and the
/// per-instruction execution-count multiplier of the `BL` (1 outside any loop; the
/// enclosing loop's proven trip product when the call sits inside a proven counted
/// loop, so a call in a loop is counted `trip` times, never once).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WcetCallSite {
    /// The `BL` target label as emitted by the selector (`func_<wasm_index>` for a
    /// direct local/import call; any other label is a runtime helper → external).
    pub callee_label: String,
    /// The call site's worst-case execution count (product of enclosing proven loop
    /// trip factors; 1 outside any loop). `u128` to survive deep nesting without
    /// wrapping, matching the loop-multiplier domain.
    pub multiplier: u128,
}

/// The per-function INTERMEDIATE result of the WCET pass BEFORE inter-procedural
/// composition (#778 phase 3). The backend produces one of these per function; the
/// module-level composer ([`crate::wcet`] consumers call `synth_backend::wcet_compose`)
/// resolves each function's direct call sites against the whole module and emits the
/// final [`WcetFunction`] (a composed bound, or a propagated/recursion/indirect
/// decline).
///
/// Splitting the pass in two keeps composition a PURE function over already-decided
/// per-function facts: `own_cycles` already prices every non-call instruction
/// (including each `BL`'s branch overhead) at its proven execution count, so the
/// composed total is `own_cycles + Σ_site multiplier_site × callee_total` — the
/// per-site multiplier makes a call inside a proven loop sound by construction.
/// (#921) Where a decline happened: which op, and where in the function.
/// Travels through the intermediate so composition can carry it to the sidecar.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WcetDeclineSite {
    /// `ArmOp` variant name — `I64Add`, `MveDivF32`, …
    pub op: String,
    /// Byte offset within the function; `None` when it could not be computed
    /// from the real encoder (omitted rather than estimated).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub offset: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WcetIntermediate {
    /// The function declines for a reason INDEPENDENT of composition (an unproven
    /// loop, an internal looped expansion, an unsupported core, an unresolved label
    /// branch, an indirect call, or an unmodeled op). Carried straight through to a
    /// [`WcetFunction::Declined`]; composition never rescues these.
    Declined {
        /// (#921) The op that caused the decline, when it names one.
        site: Option<WcetDeclineSite>,
        name: String,
        reason: WcetDecline,
        hint_rejections: Vec<WcetHintRejection>,
    },
    /// The function's own body is bounded; its final bound depends only on resolving
    /// the recorded direct call sites against the module's other functions.
    Composable {
        name: String,
        /// The summed worst-case cost of every instruction in the final stream
        /// (each priced at its documented worst case × its proven execution-count
        /// multiplier), INCLUDING each direct `BL`'s branch overhead. The callee
        /// bodies are added by the composer via `call_sites`.
        own_cycles: u64,
        /// Number of ARM instructions summed (diagnostic, carried to the bound).
        instr_count: usize,
        /// The direct call sites to resolve at compose time.
        call_sites: Vec<WcetCallSite>,
        /// Proven loops inside this function (carried to the bound unchanged).
        loops: Vec<WcetLoopBound>,
        /// (#778 phase 4 / #49) A proven self-recursion certificate, when this
        /// function is a bounded single-self-call chain with a verified depth hint.
        /// The composer folds the self-edge as `(max_depth+1) × frame_cost` instead
        /// of declining `Recursion`. `None` for a non-recursive function or an
        /// unverifiable/unhinted recursion (which still declines).
        recursion_cert: Option<WcetRecursionCert>,
        /// Hints rejected while analyzing this function (carried to the bound).
        hint_rejections: Vec<WcetHintRejection>,
    },
}

impl WcetIntermediate {
    /// The compiled function name this intermediate is for.
    pub fn name(&self) -> &str {
        match self {
            WcetIntermediate::Declined { name, .. } | WcetIntermediate::Composable { name, .. } => {
                name
            }
        }
    }
}

/// The parsed `--wcet-hints` file (`synth-wcet-hints-v1`) — an UNTRUSTED oracle
/// input (#778 phase 2, the scry integration seam). Per function, an ordered
/// array of claimed loop-trip-count upper bounds, matched to loops by ascending
/// head offset (entry N = N-th loop head in the function; `null` skips a loop).
/// Every entry is soundly CHECKED before use: synth re-derives the loop's trip
/// count from its own induction proof and consumes the hint only when the
/// derived count is ≤ the hint. A wrong or unverifiable hint is rejected with a
/// machine reason ([`WcetHintReject`]) — never trusted into a bound.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct WcetHints {
    /// Must equal [`HINTS_SCHEMA`].
    pub schema: String,
    /// Per-function hint arrays, keyed by the compiled function name.
    #[serde(default)]
    pub functions: std::collections::BTreeMap<String, WcetFunctionHints>,
}

/// Per-function loop-bound hints.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct WcetFunctionHints {
    /// Claimed trip-count upper bounds, one per loop in ascending-head-offset
    /// order; `null` leaves that loop unhinted.
    #[serde(default)]
    pub loop_bounds: Vec<Option<u64>>,
    /// (#778 phase 4 / #49) An UNTRUSTED claimed maximum SELF-recursion depth for
    /// this function. Consulted only when synth has proven the function is a
    /// single-self-call chain whose controlling value is entry-independently bounded
    /// (a masked-slot counter): synth then DERIVES its own maximum depth from the
    /// mask+step+base induction and cross-checks this hint (`hint < derived` →
    /// `hint-below-derived-depth`). A hint on a function whose recursion synth cannot
    /// so verify is REJECTED (`hint-unverifiable-recursion`) and never trusted. The
    /// emitted bound always uses synth's DERIVED depth, never the raw hint.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub recursion_depth: Option<u64>,
}

/// The full `synth-wcet-v1` sidecar: schema header, precondition, and per-function
/// bounds/declines.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WcetReport {
    /// Schema version (`synth-wcet-v1`).
    pub schema: String,
    /// The compiled module name (for diagnostics).
    pub module: String,
    /// The core class the cycle table is written for (e.g. `"cortex-m4"`). The
    /// bound is CONDITIONAL on this core.
    pub core_class: String,
    /// Assumed instruction-memory wait states (0 for the sound zero-wait table).
    pub wait_states: u32,
    /// Human statement of the memory precondition the bound holds under.
    pub memory_assumption: String,
    /// Per-function bound or decline. Complete: one entry per compiled function.
    pub functions: Vec<WcetFunction>,
}

impl WcetReport {
    /// Start an empty report for `module`, targeting `core_class` under the sound
    /// zero-wait precondition.
    pub fn new(module: impl Into<String>, core_class: impl Into<String>) -> Self {
        WcetReport {
            schema: SCHEMA.to_string(),
            module: module.into(),
            core_class: core_class.into(),
            wait_states: 0,
            memory_assumption:
                "zero-wait-state instruction memory (flash accelerator / I-cache hit); \
                 in-order single-issue pipeline; documented per-instruction worst-case cycles"
                    .to_string(),
            functions: Vec::new(),
        }
    }

    /// Serialize to pretty JSON.
    pub fn to_json(&self) -> serde_json::Result<String> {
        serde_json::to_string_pretty(self)
    }

    /// Resolve the sidecar path (`<output>.wcet.json`) next to the ELF output.
    pub fn sidecar_path(output: &std::path::Path) -> std::path::PathBuf {
        let mut s = output.as_os_str().to_os_string();
        s.push(".wcet.json");
        std::path::PathBuf::from(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounded_and_declined_roundtrip() {
        let mut r = WcetReport::new("m", "cortex-m4");
        r.functions.push(WcetFunction::Bounded {
            name: "leaf".into(),
            cycles: 42,
            instr_count: 7,
            loops: Vec::new(),
            recursion: None,
            hint_rejections: Vec::new(),
            hint_key: None,
        });
        r.functions
            .push(WcetFunction::declined("spins", WcetDecline::Loop));
        let json = r.to_json().unwrap();
        let back: WcetReport = serde_json::from_str(&json).unwrap();
        assert_eq!(r, back);
        // Decline reason is machine-readable and carries a note.
        assert!(json.contains("\"reason\": \"loop\""));
        assert!(json.contains("synth-wcet-v1"));
    }

    #[test]
    fn sidecar_path_appends_suffix() {
        let p = WcetReport::sidecar_path(std::path::Path::new("out/app.elf"));
        assert_eq!(p, std::path::PathBuf::from("out/app.elf.wcet.json"));
    }

    // ── #1063: durable hint keys ────────────────────────────────────────────

    /// The v0 crate disambiguator (gale's measured churner, scry#123) strips;
    /// content-derived components survive.
    #[test]
    fn stable_key_strips_v0_crate_disambiguator() {
        assert_eq!(
            stable_name_key("_RNvCs942N1ctoMYm_4fixt12inner_eqexit"),
            "_RNvC4fixt12inner_eqexit"
        );
        // Multiple crate refs in one path all strip.
        assert_eq!(
            stable_name_key("_RNvNtCs942N1ctoMYm_4core3fmt3num__Cs1AbCd_5other"),
            "_RNvNtC4core3fmt3num__C5other"
        );
        // Local (closure) disambiguators like `s_0` are source-order-derived
        // and are KEPT — only the crate-metadata hash after `C` strips.
        assert_eq!(
            stable_name_key("_RNCNvCs942N1ctoMYm_4main4mains_0"),
            "_RNCNvC4main4mains_0"
        );
    }

    /// Legacy mangling and demangled hash suffixes strip; a non-mangled name is
    /// unchanged.
    #[test]
    fn stable_key_strips_legacy_hashes_and_keeps_plain_names() {
        assert_eq!(
            stable_name_key("_ZN4core3fmt9Formatter3pad17h2b9e27d1f4d3ba32E"),
            "_ZN4core3fmt9Formatter3padE"
        );
        assert_eq!(
            stable_name_key("core::fmt::Formatter::pad::h2b9e27d1f4d3ba32"),
            "core::fmt::Formatter::pad"
        );
        assert_eq!(stable_name_key("memcpy"), "memcpy");
        assert_eq!(stable_name_key("entry"), "entry");
    }

    fn idents() -> Vec<WcetFnIdentity> {
        vec![
            WcetFnIdentity {
                index: 0,
                export_name: None,
                debug_name: Some("_RNvCs942N1ctoMYm_4fixt12inner_eqexit".into()),
            },
            WcetFnIdentity {
                index: 1,
                export_name: Some("entry".into()),
                debug_name: Some("_RNvCs942N1ctoMYm_4fixt5entry".into()),
            },
            WcetFnIdentity {
                index: 2,
                export_name: None,
                debug_name: None,
            },
        ]
    }

    /// Export name wins; a unique stripped name-section name is the stable key
    /// (raw name accepted as an alias); a nameless function keeps `func_<idx>`
    /// flagged build-local.
    #[test]
    fn assign_priority_export_then_stripped_then_index() {
        let a = assign_hint_keys(&idents());
        assert_eq!(a[0].compile_name, "func_0");
        assert_eq!(a[0].display_name, "_RNvCs942N1ctoMYm_4fixt12inner_eqexit");
        assert_eq!(a[0].hint_key.key, "_RNvC4fixt12inner_eqexit");
        assert!(!a[0].hint_key.build_local);
        assert!(
            a[0].accepted_keys
                .iter()
                .any(|k| k == "_RNvCs942N1ctoMYm_4fixt12inner_eqexit"),
            "raw name-section name must be an accepted alias"
        );
        assert!(
            !a[0].accepted_keys.iter().any(|k| k == "func_0"),
            "an index key is refused once the function carries a name"
        );
        assert_eq!(a[1].hint_key.key, "entry");
        assert!(!a[1].hint_key.build_local);
        assert_eq!(a[2].hint_key.key, "func_2");
        assert!(a[2].hint_key.build_local, "an index is not an identity");
    }

    /// Two functions whose stripped keys collide demote to their RAW names
    /// (build-local) — a churning key is disclosed, never silently unstable.
    #[test]
    fn assign_demotes_stripped_collision_to_raw_build_local() {
        let fns = vec![
            WcetFnIdentity {
                index: 0,
                export_name: None,
                debug_name: Some("_RNvCsAAAA_4c3f".into()),
            },
            WcetFnIdentity {
                index: 1,
                export_name: None,
                debug_name: Some("_RNvCsBBBB_4c3f".into()),
            },
        ];
        let a = assign_hint_keys(&fns);
        assert_eq!(a[0].hint_key.key, "_RNvCsAAAA_4c3f");
        assert!(a[0].hint_key.build_local);
        assert_eq!(a[1].hint_key.key, "_RNvCsBBBB_4c3f");
        assert!(a[1].hint_key.build_local);
    }

    /// Resolution re-keys to compile names, and every non-consumed entry gets a
    /// NAMED diagnostic — never a silent ignore.
    #[test]
    fn resolve_rekeys_and_names_every_refusal() {
        let a = assign_hint_keys(&idents());
        let mut h = WcetHints {
            schema: HINTS_SCHEMA.into(),
            functions: std::collections::BTreeMap::new(),
        };
        let entry = WcetFunctionHints {
            loop_bounds: vec![Some(8)],
            recursion_depth: None,
        };
        // stable key, raw alias (duplicate of the same function), refused index
        // key, and an unknown name.
        h.functions
            .insert("_RNvC4fixt12inner_eqexit".into(), entry.clone());
        h.functions.insert(
            "_RNvCs942N1ctoMYm_4fixt12inner_eqexit".into(),
            entry.clone(),
        );
        h.functions.insert("func_0".into(), entry.clone());
        h.functions.insert("nosuch".into(), entry);
        let res = resolve_hint_keys(h, &a);
        assert!(res.hints.functions.contains_key("func_0"));
        assert_eq!(res.resolved.len(), 1);
        assert_eq!(res.diagnostics.len(), 3);
        assert!(
            res.diagnostics
                .iter()
                .any(|d| d.contains("wcet-hint-key-duplicate"))
        );
        assert!(
            res.diagnostics
                .iter()
                .any(|d| d.contains("wcet-hint-key-index-refused")
                    && d.contains("_RNvC4fixt12inner_eqexit"))
        );
        assert!(
            res.diagnostics
                .iter()
                .any(|d| d.contains("not in this module"))
        );
    }
}
