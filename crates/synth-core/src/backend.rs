//! Backend trait and registry for multi-backend compilation
//!
//! Every compiler backend (ARM, aWsm, wasker, w2c2) implements the `Backend`
//! trait, allowing the CLI and verification framework to treat them uniformly.

use crate::target::TargetSpec;
use crate::wasm_decoder::DecodedModule;
use crate::wasm_op::WasmOp;
use crate::wsc_facts::WscFact;
use std::collections::HashMap;
use thiserror::Error;

/// Errors from backend compilation
#[derive(Debug, Error)]
pub enum BackendError {
    #[error("compilation failed: {0}")]
    CompilationFailed(String),

    #[error("backend not available: {0}")]
    NotAvailable(String),

    #[error("unsupported configuration: {0}")]
    UnsupportedConfig(String),

    #[error("external tool error: {0}")]
    ExternalToolError(String),
}

/// Memory-bounds safety strategy. Phase 1 of `docs/binary-safety-design.md` §3.1.
///
/// - `Mpu`/PMP: rely on hardware (ARM MPU or RV32 PMP) — no inline check.
/// - `Software`: emit a `CMP/BHS Trap_Handler` (ARM) or `bgeu addr, mem_size, ebreak` (RV32)
///   before every load/store.
/// - `Mask`: emit `AND addr, addr, #(mem_size - 1)` — only valid when memory size
///   is a power of two. Wraps on OOB rather than trapping (fuzz-profile semantics).
/// - `None`: no bounds enforcement.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SafetyBounds {
    /// No bounds check (caller assumes the WASM module is trusted)
    #[default]
    None,
    /// ARM MPU / RV32 PMP — hardware enforcement, no inline guard
    Mpu,
    /// Software CMP/BHS (ARM) or BGEU+EBREAK (RV32) per access
    Software,
    /// AND-mask, requires power-of-two memory size
    Mask,
}

impl SafetyBounds {
    /// Parse the `--safety-bounds` argument value.
    pub fn parse(s: &str) -> std::result::Result<Self, String> {
        match s {
            "none" => Ok(SafetyBounds::None),
            "mpu" | "pmp" => Ok(SafetyBounds::Mpu),
            "software" | "soft" => Ok(SafetyBounds::Software),
            "mask" | "masking" => Ok(SafetyBounds::Mask),
            other => Err(format!(
                "unknown --safety-bounds value '{}'; expected one of: none, mpu, software, mask",
                other
            )),
        }
    }

    /// String form used in the safety manifest.
    pub fn as_str(self) -> &'static str {
        match self {
            SafetyBounds::None => "none",
            SafetyBounds::Mpu => "mpu",
            SafetyBounds::Software => "software",
            SafetyBounds::Mask => "mask",
        }
    }
}

/// Configuration for a compilation run
#[derive(Debug, Clone)]
pub struct CompileConfig {
    /// Optimization level (0 = none, 1 = fast, 2 = default, 3 = aggressive)
    pub opt_level: u8,
    /// Target specification
    pub target: TargetSpec,
    /// Legacy: enable software bounds checking for memory operations.
    /// Deprecated in favor of `safety_bounds`. When set, equivalent to
    /// `SafetyBounds::Software`. Kept for backwards compatibility with
    /// callers that haven't migrated yet.
    pub bounds_check: bool,
    /// Phase-1 unified safety-bounds knob. If `bounds_check` is `true` and
    /// this is `None`, the legacy field wins (back-compat). If both are set,
    /// `safety_bounds` wins.
    pub safety_bounds: SafetyBounds,
    /// Hardware profile name (e.g. "nrf52840", "stm32f407")
    pub hardware: String,
    /// Skip optimization passes (direct instruction selection)
    pub no_optimize: bool,
    /// Use Loom-compatible optimization preset
    pub loom_compat: bool,
    /// Number of imported functions (calls to indices below this use Meld dispatch)
    pub num_imports: u32,
    /// AAPCS integer-argument count per function, indexed by full WASM function
    /// index (imports first, then locals). Lets `Call` marshal the right number
    /// of operand-stack values into R0–R3 (issue #195). Empty = pass no args
    /// (pre-#195 behaviour).
    pub func_arg_counts: Vec<u32>,
    /// AAPCS integer-argument count per function type, indexed by type index.
    /// Used by `call_indirect` (issue #195).
    pub type_arg_counts: Vec<u32>,
    /// Produce relocatable (ET_REL) host-link output. When set, the backend
    /// uses the direct instruction selector (`select_with_stack`) rather than
    /// the optimized path: the optimizer materializes an *absolute* linear-
    /// memory base (0x20000100) and does not preserve caller-saved registers
    /// across calls, both wrong for a host-linked object where the linmem base
    /// is supplied via `fp` at runtime and callees follow AAPCS. Imports are
    /// also emitted as direct `func_N` BLs (resolved to the wasm field name)
    /// instead of `__meld_dispatch_import`. (#197 — follow-up to #188/#171.)
    pub relocatable: bool,

    /// #237: emit wasm function-static data as a base-independent `.data`
    /// section (`__synth_wasm_data`) addressed via MOVW/MOVT symbol relocations,
    /// so a host-pointer drop-in (linmem base = 0 for native `*ptr` derefs)
    /// doesn't mis-resolve the statics. Off by default — only the leaves'
    /// base-relative `[R11+const]` path is used unless explicitly requested.
    pub native_pointer_abi: bool,

    /// #237: wasm linear-memory minimum size in bytes — the full static-data
    /// extent (initialized `(data)` segments plus the zero-init/BSS region).
    /// Under `native_pointer_abi`, a const memory address below this is a wasm
    /// static → symbol-relative; any address beyond it is a runtime host pointer
    /// → `[R11=0 + addr]`.
    pub linear_memory_bytes: u32,

    /// #237: the wasm stack-pointer global as `(index, init_value)`, if the
    /// module has one. Under `native_pointer_abi` the backend register-promotes
    /// it: `global.get` materializes `__synth_wasm_data + init` (the real stack
    /// top) and the init value doubles as the static-data base that separates
    /// pointer consts (`>= init`) from frame-size scalars (`< init`).
    pub stack_pointer_global: Option<(u32, i32)>,
    /// #311: per-function (full index) / per-type "returns i64" — the call
    /// lowering must tag i64 results as a register pair or the hi half is
    /// invisible to liveness.
    pub func_ret_i64: Vec<bool>,
    pub type_ret_i64: Vec<bool>,
    /// #643: byte width of each defined global's storage slot, indexed by
    /// global index — 4 for i32/f32, 8 for i64/f64, 16 for v128 (from the
    /// module's global section). The globals table is laid out by SUMMING
    /// these widths: an i64 global needs a register-PAIR store/load at
    /// `[R9, off]`/`[R9, off+4]`, and every later global's offset shifts.
    /// Empty ⇒ every global assumed 4 bytes (the legacy `idx * 4` layout;
    /// hand-built op streams and i32-only modules are byte-identical).
    pub global_widths: Vec<u32>,
    /// #359: declared parameter widths per *function* (full index, imports
    /// first): `func_params_i64[f][k]` is true when param `k` of function `f` is
    /// i64/f64. The AAPCS stack-argument path needs the *declared* widths
    /// (op-stream inference can't see an unused i64 param that still shifts the
    /// incoming-stack layout). The source of truth — a per-function driver loop
    /// (`compile_module` / the CLI loop) indexes it by `func.index` and copies
    /// the slice into [`current_func_params_i64`] before each `compile_function`.
    /// Empty → every param assumed i32 (the legacy path; keeps every function
    /// with <=4 params, or all-i32 params, byte-identical).
    pub func_params_i64: Vec<Vec<bool>>,
    /// #359: declared parameter widths of the function CURRENTLY being compiled
    /// — `current_func_params_i64[k]` is true when param `k` is i64/f64. Set per
    /// function (a cheap clone of the config) from [`func_params_i64`] by the
    /// driver loop, because `compile_function` is shared across backends and
    /// carries no function index. Empty → assume i32.
    pub current_func_params_i64: Vec<bool>,
    /// #457: DECLARED parameter count of the function CURRENTLY being compiled,
    /// from the module's type section (`func_arg_counts[func.index]`). Set per
    /// function by the driver loops like [`current_func_params_i64`].
    ///
    /// The backends otherwise INFER the param count from local-access patterns
    /// (`count_params`: a local whose first access is a read is assumed to be a
    /// param) — which cannot distinguish a param from a read-before-write
    /// non-param local. WASM zero-initializes non-param locals, so such a local
    /// must read 0; the inference instead homed it in a parameter register and
    /// read caller garbage (#457). The backends cap the inferred count at this
    /// declared count when it is present, which reclassifies exactly the
    /// read-before-write locals (an inferred count can only exceed the declared
    /// one via a read-first index >= the declared count) and leaves every other
    /// function's codegen byte-identical.
    ///
    /// `None` → declared signature unknown (hand-built op streams, direct
    /// `compile_function` callers) → pure inference, the legacy behaviour.
    pub current_func_param_count: Option<u32>,
    /// #509: blocktype-arity side-table of the function CURRENTLY being compiled
    /// — `(param_count, result_count)` of the k-th `Block`/`Loop`/`If` in its op
    /// stream (ordinal-keyed; see [`FunctionOps::block_arity`]). Set per function
    /// by the driver loop (like [`current_func_params_i64`]). The direct selector
    /// uses it to land a value carried by `br`/`br_if`/`br_table` in the target
    /// block's designated result register instead of dropping it. Empty → every
    /// block treated as void (the legacy lowering; hand-built op streams).
    ///
    /// [`FunctionOps::block_arity`]: crate::wasm_decoder::FunctionOps::block_arity
    pub current_func_block_arity: Vec<(u8, u8)>,

    /// #543 Phase 1 — integrator-marked volatile linear-memory segments (the DMA
    /// transfer window). Each range `[base, base+len)` names a region of the fused
    /// linear memory that an EXTERNAL agent (the DMA engine, modelled by gale as a
    /// Component-Model `own<buffer>` handoff — gale decision `DD-DMA-REGION-001`,
    /// gale#124) rewrites out-of-band. Loads and stores whose address falls inside
    /// a marked range must eventually be treated as VOLATILE: not cached, hoisted,
    /// or reordered across the transfer boundary.
    ///
    /// PHASE-2 CONTRACT (implemented — issue #543): the optimizer's
    /// address-caching passes HONOR these ranges. Consumption points:
    ///  - the #468 base-CSE / const-address-fold
    ///    (`optimizer_bridge::plan_base_cse`, DEFAULT-ON, opt-out
    ///    `SYNTH_BASE_CSE=0`): a const-address access whose 4-byte window
    ///    intersects a marked range is EXCLUDED from the fold set — it keeps
    ///    its verbatim per-access materialize-and-access codegen, while
    ///    accesses outside the range still fold;
    ///  - const-CSE (`liveness::apply_const_cse` wired in `arm_backend.rs`,
    ///    DEFAULT-ON, opt-out `SYNTH_CONST_CSE=0`; the former bridge-level
    ///    inline cache is retired, #242): declines WHOLESALE while any range is
    ///    marked — a cached constant cannot be classified address-vs-data at
    ///    that level, so the conservative stance for statically-unknown
    ///    addressing is to re-materialize every constant at each occurrence.
    ///
    /// Passes that only touch SP-relative frame slots (stack-reload forwarding,
    /// frame-slot DCE, spill re-choice) are unaffected by design: these ranges
    /// are LINEAR-MEMORY addresses, and frame slots are never linmem. Nothing on
    /// the pipeline deletes, forwards, or reorders a linear-memory access (IR CSE
    /// deliberately never CSEs `MemLoad`s; DCE removes only unreachable blocks),
    /// so every marked access is issued verbatim, in program order.
    ///
    /// Empty (the default): zero behavior change by construction — every gate
    /// reduces to the pre-#543 path, so the emitted `.text` is byte-identical
    /// with or without this code (the frozen-codegen gate holds). See rivet
    /// `VCR-DMA-001`.
    pub volatile_segments: Vec<VolatileRange>,

    /// VCR-PERF-002 Phase 1 (#494) — proven invariants forwarded by loom in
    /// the `wsc.facts` custom section (encoding:
    /// `docs/design/wsc-facts-encoding.md`; program:
    /// `docs/design/proof-carrying-specialization.md`), whole-module table
    /// keyed by `(func_index, value_id)`. The compile driver copies the
    /// current function's slice into [`current_func_facts`] (the
    /// `func_params_i64` → `current_func_params_i64` pattern), because
    /// `compile_function` carries no function index.
    ///
    /// PHASE-1 CONTRACT: threaded but NOT consumed — no codegen path reads
    /// facts, so emitted bytes are unchanged whether or not the module
    /// carries the section (locked by `wsc_facts_ingestion_494.rs`). Phase 2
    /// turns each fact into a premise for a flag-gated (`SYNTH_FACT_SPEC`),
    /// per-elision ordeal-validated specialization; the facts-absent compile
    /// stays byte-identical by construction (empty ⇒ every gate vacuous).
    ///
    /// [`current_func_facts`]: CompileConfig::current_func_facts
    pub wsc_facts: Vec<WscFact>,
    /// VCR-PERF-002 Phase 1 (#494): the `wsc.facts` invariants of the function
    /// CURRENTLY being compiled (`fact.func_index == func.index`), set per
    /// function by the driver loops like [`current_func_params_i64`]. This is
    /// the field a Phase-2 selector pass will read its premises from. Empty →
    /// no facts → no specialization may ever fire (the fail-safe default).
    ///
    /// [`current_func_params_i64`]: CompileConfig::current_func_params_i64
    pub current_func_facts: Vec<WscFact>,
    /// VCR-PERF-002 Phase 2b (#494, divisor-nonzero): op indices (into the op
    /// stream passed to `compile_function`) of `div`/`rem` ops whose
    /// DIVIDE-BY-ZERO trap guard is proven dead — the fact-spec pass
    /// discharged `UNSAT(P ∧ divisor == 0)` per site through the
    /// certificate-checked ordeal solver BEFORE the driver set this field.
    /// Consumed by the ARM direct selector (`select_with_stack`); every other
    /// path ignores it (guards stay — sound). Empty (the default) ⇒ every
    /// guard is emitted, byte-identical to today.
    pub fact_div_zero_elide: Vec<usize>,
    /// VCR-PERF-002 Phase 2b (#494): op indices of `div_s` ops whose
    /// `INT_MIN / -1` OVERFLOW trap guard is proven dead — a SEPARATE
    /// obligation (`UNSAT(P ∧ dividend == INT_MIN ∧ divisor == -1)`). A
    /// divisor-nonzero fact alone NEVER lands here: divisor ≠ 0 does not
    /// exclude -1 (#633/#634 two-guard distinction). Empty ⇒ guard emitted.
    pub fact_div_ovf_elide: Vec<usize>,
    /// #642: `call_indirect` guard inputs — the compile-time table size for
    /// the runtime bounds check and the per-expected-type closed-world type
    /// verdicts — computed from the decoded module by
    /// [`crate::wasm_decoder::DecodedModule::call_indirect_guards`] and set by
    /// the driver loops. The default (`table_size: None`, empty verdicts)
    /// DECLINES every `call_indirect` lowering: an unchecked indirect branch
    /// is never emitted (WASM Core §4.4.8 requires OOB/type-mismatch traps).
    pub call_indirect_guards: crate::wasm_decoder::CallIndirectGuards,
}

/// #543 — an integrator-marked volatile linear-memory segment (the DMA transfer
/// window): the half-open byte range `[base, base + len)` of the fused linear
/// memory that an external agent rewrites out-of-band. Parsed from the CLI
/// `--volatile-segment <base>:<len>` flag. See [`CompileConfig::volatile_segments`]
/// for the Phase-1/Phase-2 split.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VolatileRange {
    /// Start address of the volatile region, in linear-memory bytes.
    pub base: u32,
    /// Length of the volatile region, in bytes. The region is `[base, base+len)`.
    pub len: u32,
}

impl CompileConfig {
    /// Resolve the effective safety-bounds setting, honouring the legacy
    /// `bounds_check` field as a fallback. Used by backends to pick the
    /// inline-check shape.
    pub fn effective_safety_bounds(&self) -> SafetyBounds {
        match (self.safety_bounds, self.bounds_check) {
            (SafetyBounds::None, true) => SafetyBounds::Software,
            (s, _) => s,
        }
    }
}

impl Default for CompileConfig {
    fn default() -> Self {
        Self {
            opt_level: 2,
            target: TargetSpec::cortex_m4(),
            bounds_check: false,
            safety_bounds: SafetyBounds::None,
            hardware: String::new(),
            no_optimize: false,
            loom_compat: false,
            num_imports: 0,
            func_arg_counts: Vec::new(),
            type_arg_counts: Vec::new(),
            relocatable: false,
            native_pointer_abi: false,
            linear_memory_bytes: 0,
            stack_pointer_global: None,
            func_ret_i64: Vec::new(),
            type_ret_i64: Vec::new(),
            // #643: empty ⇒ legacy all-4-byte global slots (i32-only modules).
            global_widths: Vec::new(),
            func_params_i64: Vec::new(),
            current_func_params_i64: Vec::new(),
            // #457: None ⇒ declared signature unknown ⇒ param-count inference
            // only (unit tests / hand-built op streams); driver loops fill it.
            current_func_param_count: None,
            // #509: empty ⇒ legacy void-block lowering (unit tests / hand-built
            // op streams); the driver loops fill it per function.
            current_func_block_arity: Vec::new(),
            // #543 Phase 1: no volatile segments unless the CLI flag names them.
            // Empty ⇒ inert ⇒ emitted bytes unchanged.
            volatile_segments: Vec::new(),
            // VCR-PERF-002 Phase 1 (#494): no facts unless the module carries
            // a parseable `wsc.facts` section. Empty ⇒ inert (and Phase 1 has
            // no consumer anyway) ⇒ emitted bytes unchanged.
            wsc_facts: Vec::new(),
            current_func_facts: Vec::new(),
            // VCR-PERF-002 Phase 2b (#494): no guard-elision marks unless the
            // fact-spec pass discharged the per-site obligations. Empty ⇒
            // every div/rem trap guard is emitted, byte-identical.
            fact_div_zero_elide: Vec::new(),
            fact_div_ovf_elide: Vec::new(),
            // #642: no guard inputs ⇒ every call_indirect lowering declines
            // loudly (never an unchecked indirect branch). Driver loops fill
            // this from the decoded module.
            call_indirect_guards: crate::wasm_decoder::CallIndirectGuards::default(),
        }
    }
}

/// A relocation entry produced during compilation
///
/// Records that a BL instruction at `offset` bytes into the function's code
/// targets an external symbol (e.g., `__meld_dispatch_import`). The linker
/// resolves these when combining the Synth object with the Kiln bridge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelocKind {
    /// R_ARM_THM_CALL — a Thumb BL call site (the default; #167).
    ThmCall,
    /// R_ARM_MOVW_ABS_NC — the MOVW half of a symbol-relative address (#237).
    MovwAbs,
    /// R_ARM_MOVT_ABS — the MOVT half of a symbol-relative address (#237).
    MovtAbs,
    /// R_ARM_ABS32 — a 32-bit absolute address held in a `.text` literal-pool
    /// word, loaded via `LDR rX, [pc, #off]` (#345). The link-survivable
    /// replacement for the inline-immediate MOVW/MOVT-ABS pair: `ld`/bfd patches
    /// the data word at link time (`S + A`, the addend living in the word, REL
    /// semantics), which survives placement into a large multi-object image —
    /// whereas an inline-instruction MOVW_ABS immediate can be mangled.
    Abs32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeRelocation {
    /// Byte offset within the function's machine code where the reloc applies
    pub offset: u32,
    /// Target symbol name (e.g., "__meld_dispatch_import", "__synth_wasm_data")
    pub symbol: String,
    /// Which ARM relocation type to emit for this site.
    pub kind: RelocKind,
}

/// VCR-DBG-001: a per-instruction source map — `(machine_offset_within_code,
/// wasm_op_index)` pairs, one per emitted machine instruction. A `None` op-index
/// marks an instruction with no originating wasm op (prologue/epilogue, literal
/// pool). Consumed by the DWARF `.debug_line` emitter; empty when no source map
/// was produced.
pub type LineMap = Vec<(u32, Option<usize>)>;

/// A single compiled function
#[derive(Debug, Clone)]
pub struct CompiledFunction {
    /// Function name (from WASM export or generated)
    pub name: String,
    /// Raw machine code bytes
    pub code: Vec<u8>,
    /// Original WASM ops (retained for verification)
    pub wasm_ops: Vec<WasmOp>,
    /// Relocations for external symbol references (BL to bridge functions)
    pub relocations: Vec<CodeRelocation>,
    /// VCR-DBG-001: per-instruction source map for DWARF `.debug_line` emission —
    /// `(machine_offset_within_code, wasm_op_index)` captured at encode time, one
    /// entry per emitted machine instruction. A `None` op-index marks an
    /// instruction with no originating wasm op (prologue/epilogue, literal-pool
    /// word). This is purely additive metadata: it is never serialized unless
    /// `.debug_line` emission is requested, so the emitted `.text` is
    /// byte-identical with or without it. Empty for backends/paths that do not
    /// yet produce a source map (RISC-V, the optimized ARM path).
    pub line_map: LineMap,
}

/// Result of compiling a full module
#[derive(Debug)]
pub struct CompilationResult {
    /// Compiled functions
    pub functions: Vec<CompiledFunction>,
    /// Complete ELF binary (if backend produces one directly)
    pub elf: Option<Vec<u8>>,
    /// Name of the backend that produced this result
    pub backend_name: String,
}

/// What a backend can and cannot do
#[derive(Debug, Clone)]
pub struct BackendCapabilities {
    /// Backend produces complete ELF files (external backends like aWsm)
    pub produces_elf: bool,
    /// Backend supports per-rule verification (only our custom ARM backend)
    pub supports_rule_verification: bool,
    /// Backend supports binary-level verification (all backends via disassembly)
    pub supports_binary_verification: bool,
    /// Backend is an external tool (not a library)
    pub is_external: bool,
}

/// Trait that every compilation backend implements
pub trait Backend: Send + Sync {
    /// Human-readable backend name
    fn name(&self) -> &str;

    /// What this backend can do
    fn capabilities(&self) -> BackendCapabilities;

    /// Which targets this backend supports
    fn supported_targets(&self) -> Vec<TargetSpec>;

    /// Compile an entire decoded WASM module
    fn compile_module(
        &self,
        module: &DecodedModule,
        config: &CompileConfig,
    ) -> std::result::Result<CompilationResult, BackendError>;

    /// Compile a single function from WASM ops to machine code
    fn compile_function(
        &self,
        name: &str,
        ops: &[WasmOp],
        config: &CompileConfig,
    ) -> std::result::Result<CompiledFunction, BackendError>;

    /// Check if this backend is available (external tools installed, etc.)
    fn is_available(&self) -> bool;
}

/// Registry of available backends
pub struct BackendRegistry {
    backends: HashMap<String, Box<dyn Backend>>,
}

impl BackendRegistry {
    pub fn new() -> Self {
        Self {
            backends: HashMap::new(),
        }
    }

    /// Register a backend under its name
    pub fn register(&mut self, backend: Box<dyn Backend>) {
        let name = backend.name().to_string();
        self.backends.insert(name, backend);
    }

    /// Get a backend by name
    pub fn get(&self, name: &str) -> Option<&dyn Backend> {
        self.backends.get(name).map(|b| b.as_ref())
    }

    /// List all registered backends
    pub fn list(&self) -> Vec<&dyn Backend> {
        self.backends.values().map(|b| b.as_ref()).collect()
    }

    /// List backends that are actually available (installed and working)
    pub fn available(&self) -> Vec<&dyn Backend> {
        self.backends
            .values()
            .filter(|b| b.is_available())
            .map(|b| b.as_ref())
            .collect()
    }
}

impl Default for BackendRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_registry_empty() {
        let reg = BackendRegistry::new();
        assert!(reg.list().is_empty());
        assert!(reg.available().is_empty());
        assert!(reg.get("arm").is_none());
    }

    #[test]
    fn test_compile_config_default() {
        let config = CompileConfig::default();
        assert_eq!(config.opt_level, 2);
        assert!(!config.bounds_check);
        assert_eq!(config.safety_bounds, SafetyBounds::None);
        assert!(!config.no_optimize);
    }

    #[test]
    fn safety_bounds_parse_round_trip() {
        for s in ["none", "mpu", "software", "mask"] {
            let sb = SafetyBounds::parse(s).unwrap();
            assert_eq!(sb.as_str(), s);
        }
        assert_eq!(SafetyBounds::parse("pmp").unwrap(), SafetyBounds::Mpu);
        assert_eq!(SafetyBounds::parse("soft").unwrap(), SafetyBounds::Software);
        assert!(SafetyBounds::parse("nonsense").is_err());
    }

    #[test]
    fn effective_safety_bounds_legacy_promotes_to_software() {
        let cfg = CompileConfig {
            bounds_check: true,
            ..Default::default()
        };
        assert_eq!(cfg.effective_safety_bounds(), SafetyBounds::Software);
    }

    #[test]
    fn effective_safety_bounds_new_field_wins() {
        let cfg = CompileConfig {
            bounds_check: true,
            safety_bounds: SafetyBounds::Mpu,
            ..Default::default()
        };
        assert_eq!(cfg.effective_safety_bounds(), SafetyBounds::Mpu);
    }
}
