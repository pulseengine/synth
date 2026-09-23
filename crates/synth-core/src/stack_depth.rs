//! RQ-71-STACKDEPTH (#1341) types: the per-function stack profile and the
//! settled per-export answer.
//!
//! These live in synth-core for the same reason `WcetIntermediate` does —
//! `CompiledFunction` carries one, and synth-core cannot depend on the
//! backend. The ANALYSIS (which needs `ArmInstruction` and the tripwired
//! `may_move_sp` enumeration) stays in `synth_backend::stack_depth`.
//!
//! The composition rule is a MAX over the call tree, not a trip-weighted
//! sum: a callee invoked 1000 times in a loop costs 1000x the cycles and
//! ONCE the stack. See the backend module's docs for why that distinction
//! is what makes this a sibling of the WCET pass rather than a field on it.

use serde::{Deserialize, Serialize};

/// Why no finite stack bound exists. Deliberately NOT `WcetDecline`: the two
/// sets differ (see the module docs), and sharing the enum would silently tie
/// a stack refusal to a cycle-counting one.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum StackDecline {
    /// A cycle in the direct call graph — no finite depth exists.
    Recursion,
    /// `call_indirect`: the callee set is not statically known, so neither is
    /// the depth below this point.
    IndirectCall,
    /// A direct call to a function outside this module (an import). Its frame
    /// belongs to code synth did not emit.
    ExternalCall,
    /// A callee declined, and a decline propagates UP: a caller cannot be
    /// bounded by an unbounded subtree.
    CalleeUnbounded,
    /// An instruction moves SP in a way this walker cannot price. The
    /// give-up direction is a DECLINE, never a lower bound.
    UnknownSpMove,
}

impl StackDecline {
    /// The machine-readable reason string carried into the sidecar. The
    /// `stack_depth_1341.py` oracle asserts on these exact spellings.
    pub fn as_str(&self) -> &'static str {
        match self {
            StackDecline::Recursion => "recursion",
            StackDecline::IndirectCall => "call_indirect",
            StackDecline::ExternalCall => "external-call",
            StackDecline::CalleeUnbounded => "callee-unbounded",
            StackDecline::UnknownSpMove => "unknown-sp-move",
        }
    }
}

/// One function's own stack behaviour, before composition.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StackFrame {
    pub name: String,
    /// Maximum bytes below entry SP reached ANYWHERE in this function's own
    /// body — prologue plus any transient push inside an expansion. Excludes
    /// callees; composition adds the deepest one.
    pub own_bytes: u64,
    /// Direct-call labels (`func_<idx>`), in program order. Duplicates are kept:
    /// resolving them is the composer's job, and the MAX is insensitive to
    /// repeats anyway.
    pub calls: Vec<String>,
    /// Set when this function alone cannot be bounded.
    pub decline: Option<StackDecline>,
}

/// The settled answer for one function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StackResult {
    Bounded { name: String, bytes: u64 },
    Declined { name: String, reason: StackDecline },
}

/// The `synth-stack-v1` sidecar: one entry per compiled function, each either a
/// bounded maximum native stack depth or a NAMED decline.
///
/// Keyed `exports` rather than `functions` because the number an embedder needs
/// is per ENTRY POINT — it sizes the region a call into that export will use.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StackReport {
    pub schema: String,
    pub module: String,
    pub exports: Vec<StackEntry>,
}

/// One export's settled answer, flattened for the sidecar.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StackEntry {
    pub name: String,
    /// `"bounded"` or `"declined"`.
    pub status: String,
    /// Present when bounded: the maximum bytes of native stack a call into this
    /// export can consume, across the whole direct call tree.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bytes: Option<u64>,
    /// Present when declined: the machine-readable reason.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

impl StackReport {
    pub fn new(module: impl Into<String>) -> Self {
        StackReport {
            schema: "synth-stack-v1".to_string(),
            module: module.into(),
            exports: Vec::new(),
        }
    }

    /// `<output>.stack.json`, beside the object — the same shape `--emit-wcet`
    /// uses, so a build step finds both the same way.
    pub fn sidecar_path(output: &std::path::Path) -> std::path::PathBuf {
        let mut s = output.as_os_str().to_os_string();
        s.push(".stack.json");
        std::path::PathBuf::from(s)
    }

    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }
}

impl From<StackResult> for StackEntry {
    fn from(r: StackResult) -> Self {
        match r {
            StackResult::Bounded { name, bytes } => StackEntry {
                name,
                status: "bounded".to_string(),
                bytes: Some(bytes),
                reason: None,
            },
            StackResult::Declined { name, reason } => StackEntry {
                name,
                status: "declined".to_string(),
                bytes: None,
                reason: Some(reason.as_str().to_string()),
            },
        }
    }
}
