//! WASM Binary Decoder - Converts wasmparser operators to WasmOp sequences
//!
//! This module bridges the gap between parsed WASM binaries and any backend.
//! It extracts function bodies and converts wasmparser operators to our internal WasmOp format.

use crate::wasm_op::WasmOp;
use anyhow::{Context, Result};
use std::collections::HashMap;
use wasmparser::{ExternalKind, Parser, Payload};

/// Kind of a WASM import
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportKind {
    /// Imported function with type index
    Function(u32),
    /// Imported memory
    Memory,
    /// Imported table
    Table,
    /// Imported global
    Global,
}

/// A WASM import entry with full metadata
#[derive(Debug, Clone)]
pub struct ImportEntry {
    /// Module name (e.g., "wasi:cli/stdout" or "env")
    pub module: String,
    /// Field name (e.g., "write" or "memory")
    pub name: String,
    /// Import kind and associated data
    pub kind: ImportKind,
    /// Index of this import within its kind (e.g., function import index)
    pub index: u32,
}

/// WASM linear memory specification
#[derive(Debug, Clone)]
pub struct WasmMemory {
    /// Memory index
    pub index: u32,
    /// Initial size in pages (64KB each)
    pub initial_pages: u32,
    /// Maximum size in pages (if specified)
    pub max_pages: Option<u32>,
    /// Whether memory is shared (requires threads proposal)
    pub shared: bool,
}

/// A captured constant global initializer (#649). Only INTEGER `t.const` init
/// exprs are captured: `f32.const`/`f64.const` inits deliberately decode to
/// `None` — float-typed global ACCESS is the GI-FPU-001 (#369) loud-skip lane,
/// and fabricating a bit-pattern here must not quietly unskip it. Non-const
/// init exprs (e.g. `global.get` of an import) are not statically known and
/// also decode to `None`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GlobalInit {
    /// A leading `i32.const` initializer.
    I32(i32),
    /// A leading `i64.const` initializer — BOTH words must reach the emitted
    /// global slot (#649: `init_i32`-shaped capture silently zeroed these).
    I64(i64),
}

/// A WASM global's declaration — its initial value and mutability (#237).
/// Needed so the native-pointer ABI can recognize a global whose initializer is
/// a linear-memory address (e.g. `$__stack_pointer = 65536`) and make it
/// `__synth_wasm_data`-relative, rather than reading it from an R9 globals table
/// the self-contained drop-in object can't rely on.
#[derive(Debug, Clone)]
pub struct WasmGlobal {
    /// Global index (defined globals; imported globals are not counted here).
    pub index: u32,
    /// The captured constant initializer (#237/#649): `i32.const` or
    /// `i64.const`. Float/non-const init exprs decode to `None` — see
    /// [`GlobalInit`].
    pub init: Option<GlobalInit>,
    /// Whether the global is mutable.
    pub mutable: bool,
    /// #643: byte width of the global's storage slot, from its declared value
    /// type — 4 for i32/f32, 8 for i64/f64, 16 for v128. The globals table is
    /// laid out by SUMMING these widths (not `index * 4`): an i64 global needs
    /// room for both words, and every later global's offset shifts with it.
    pub slot_bytes: u32,
}

impl WasmMemory {
    /// Get initial size in bytes
    pub fn initial_bytes(&self) -> u32 {
        self.initial_pages * 65536
    }

    /// Get maximum size in bytes (or initial if not specified)
    pub fn max_bytes(&self) -> u32 {
        self.max_pages.unwrap_or(self.initial_pages) * 65536
    }
}

/// #642: one element segment's statically-decoded shape — see
/// [`DecodedModule::elem_segments`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElemSegmentInfo {
    /// #650: the table this ACTIVE segment initializes (0 for the pre-#650
    /// single-table form). Meaningless when `offset` is `None`.
    pub table_index: u32,
    /// Const i32 offset of an ACTIVE segment into its table; `None` =
    /// placement not statically verifiable (passive/declared segment or a
    /// non-const offset expression).
    pub offset: Option<u32>,
    /// The segment's function indices in slot order; `None` = contents not
    /// statically verifiable (an entry was not a plain `ref.func`).
    pub funcs: Option<Vec<u32>>,
}

/// #642/#650: one table's `call_indirect` guard inputs — see
/// [`CallIndirectGuards`] for the layout contract and soundness argument.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TableGuards {
    /// Compile-time size of this table (entries); `None` = no sound bound
    /// known (an imported table with growable limits).
    pub table_size: Option<u32>,
    /// #650: byte offset of this table's base within the contiguous R11
    /// region — `sum(size(0..N)) * 4`, a compile-time constant. `None` when
    /// any PRECEDING table's size is unknown (the base is then not a
    /// compile-time constant and the lowering declines).
    pub base_byte_offset: Option<u32>,
    /// Per expected-type index: `None` = closed-world type property VERIFIED
    /// against THIS table; `Some(reason)` = not verifiable (the lowering
    /// declines).
    pub type_reject: Vec<Option<String>>,
    /// #664: whether this table's image contains at least one uninitialized
    /// (null funcref) slot. WASM Core §4.4.8 requires a `call_indirect`
    /// reaching a null slot to TRAP — the closed-world type check verifies
    /// the INITIALIZED slots only, and the lowering must emit a runtime
    /// null check (pointer == 0 → trap) before the indirect branch when
    /// this is set. `false` for a fully-initialized table keeps today's
    /// exact dispatch bytes (no null check) BY CONSTRUCTION. Only
    /// meaningful when the type verdict is `None` (verified); reject paths
    /// decline before it is consulted.
    pub has_null_slots: bool,
    /// #676: this table's image is statically known but HETEROGENEOUS — its
    /// initialized slots span at least two distinct STRUCTURAL signature
    /// classes, so no expected type's closed world can hold
    /// (`type_reject[t]` is `Some` for every `t`) — yet the mismatch trap
    /// (WASM Core §4.4.8) IS dischargeable at runtime: the type-id sidecar
    /// (see [`CallIndirectGuards`]) carries each slot's structural class id,
    /// and the dispatch compares the indexed slot's id against the expected
    /// type's class id (a compile-time immediate), trapping on inequality.
    /// When set (and [`CallIndirectGuards::type_ids_byte_offset`] is known),
    /// the lowering emits that runtime check INSTEAD of declining. `false`
    /// keeps the pre-#676 behavior: verified tables dispatch unchecked
    /// (byte-identical), unverifiable tables decline.
    pub runtime_type_check: bool,
}

/// #642/#650: everything the `call_indirect` lowering needs to emit its
/// guards — computed once per module by
/// [`DecodedModule::call_indirect_guards`] and threaded to the instruction
/// selector via `CompileConfig`.
///
/// ## The R11 multi-table layout contract (#650)
///
/// The runtime/harness links every funcref table as ONE contiguous region of
/// raw 4-byte code pointers based at R11, in declaration order (imported
/// tables first): table 0 at `R11 + 0`, table N at
/// `R11 + sum(size(0..N)) * 4`. The offsets are compile-time constants
/// because tables are provably fixed-size (`table.grow`/`table.set` are
/// unsupported ops whose functions loud-skip at decode — #642). A
/// single-table module degenerates to the pre-#650 contract (table 0 at
/// R11, offset 0) BY CONSTRUCTION, keeping its emitted bytes identical.
///
/// WASM Core §4.4.8 requires `call_indirect` to trap when `index >=
/// table.size` and when the callee's type does not match the instruction's
/// expected type. The region stores no size fields and no type ids, so, per
/// table:
///  - the BOUNDS check is emitted at runtime against THAT table's
///    compile-time `table_size` immediate (sound: fixed-size, see above), and
///  - the TYPE check is discharged at COMPILE time: for expected type `t`,
///    `tables[n].type_reject[t]` is `None` only when every INITIALIZED slot
///    of table `n` verifiably holds a function whose signature structurally
///    equals type `t` (the closed-world property — no runtime mismatch is
///    then possible). Otherwise it holds the reason, and the lowering
///    declines LOUDLY rather than emit an unchecked indirect branch, and
///  - a NULL (uninitialized) slot traps at RUNTIME (#664): the layout
///    contract requires the runtime/harness to link every uninitialized
///    slot as a ZERO word (null funcref has no code address; 0 is never a
///    valid function pointer in the region), and when `has_null_slots` is
///    set the dispatch emits a null check on the loaded pointer
///    (`CMP #0` → trap) between the bounds guard and the indirect branch.
///    A fully-initialized table (`has_null_slots == false`) keeps the
///    pre-#664 dispatch bytes identical BY CONSTRUCTION, and
///  - a HETEROGENEOUS table (mixed signatures — the closed-world property
///    cannot hold for ANY expected type) is dispatched through a runtime
///    type check against the **type-id sidecar** (#676): a parallel `u32`
///    array the layout contract places at `R11 + type_ids_byte_offset`
///    (immediately after the LAST table's pointer words, i.e. at
///    `sum(size(0..num_tables)) * 4`), mirroring the pointer region slot
///    for slot — table N's type-ids start at
///    `R11 + type_ids_byte_offset + base_byte_offset(N)`. Each word is the
///    slot's STRUCTURAL signature class id: structurally-equal function
///    types share one dense id (1-based, first-occurrence order over the
///    type section); id **0 is reserved for null slots**, so the type
///    compare (expected ids are always >= 1) subsumes the #664 null trap
///    in the same `CMP`. The dispatch loads `type_id[idx]`, compares it
///    against the expected type's class id (compile-time immediate) and
///    traps (`UDF`) on mismatch — WASM Core §4.4.8's runtime type check —
///    before the pointer load and `BLX`. The sidecar words are emitted
///    into the relocatable object as the `.synth.table_type_ids` section
///    (non-ALLOC metadata, like `.meld_import_table`): the runtime/harness
///    that links the pointer region copies them to
///    `R11 + type_ids_byte_offset` verbatim — it never re-derives ids. A
///    module with NO heterogeneous table emits no sidecar and no runtime
///    type check anywhere: homogeneous dispatch bytes stay identical BY
///    CONSTRUCTION (the #650 offset-0 / #664 `null_check: false` trick).
///
///    pre-#664 dispatch bytes identical BY CONSTRUCTION.
///
/// ## Companion: the self-contained SRAM layout contract (#687)
///
/// The R11 register above is ALSO the linear-memory base register, whose
/// placement inside SRAM is governed by the self-contained image's stack
/// layout: `--stack-layout=high` (default) keeps linmem at the SRAM start
/// with the stack growing down from the top; `--stack-layout=low` reserves
/// the stack at the SRAM BOTTOM and shifts linmem/globals (and the optimized
/// path's absolute `0x2000_0100` base) up by the stack size, so an overflow
/// BusFaults below SRAM instead of silently corrupting them. The full layout
/// tables live on `build_multi_func_cortex_m_elf` in `synth-cli` (the builder
/// that owns the addresses). Relocatable/host-linked objects are NOT covered
/// — their linker script owns the layout, and the flag is refused there.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CallIndirectGuards {
    /// Per-table guard inputs, indexed by table index (imports first). The
    /// default (empty — no module context) DECLINES every `call_indirect`.
    pub tables: Vec<TableGuards>,
    /// #676: byte offset of the type-id sidecar within the R11 region — the
    /// total pointer-region size, `sum(size(0..num_tables)) * 4`. `Some`
    /// only when a sidecar exists: at least one table is heterogeneous
    /// (see [`TableGuards::runtime_type_check`]) AND every table's size is
    /// compile-time known (otherwise the sidecar base is not a constant and
    /// heterogeneous dispatches keep declining). `None` = no sidecar.
    pub type_ids_byte_offset: Option<u32>,
    /// #676: the sidecar image — one `u32` structural class id per slot
    /// across ALL tables in region order (0 = null slot). Emitted into the
    /// object as `.synth.table_type_ids`; empty exactly when
    /// `type_ids_byte_offset` is `None`. A table whose image is not
    /// statically known contributes ZERO words (it declines at the
    /// lowering, and 0 never equals an expected class id, so even a rogue
    /// dispatch would trap, not branch).
    pub type_ids_image: Vec<u32>,
    /// #676: per module type index, that type's structural class id
    /// (1-based, dense; structurally-equal duplicate types share an id).
    /// The expected-type immediate the dispatch compares against. Empty
    /// when `type_ids_byte_offset` is `None` (no sidecar — never consulted).
    pub type_class_ids: Vec<u32>,
}

impl CallIndirectGuards {
    /// Single-table (table 0 at R11 offset 0) guards — the pre-#650 shape,
    /// used by tests and single-table call sites.
    pub fn single_table(table_size: Option<u32>, type_reject: Vec<Option<String>>) -> Self {
        Self {
            tables: vec![TableGuards {
                table_size,
                base_byte_offset: Some(0),
                type_reject,
                has_null_slots: false,
                runtime_type_check: false,
            }],
            ..Self::default()
        }
    }
}

/// Decoded WASM module with functions and memory
#[derive(Debug, Clone)]
pub struct DecodedModule {
    /// Decoded functions
    pub functions: Vec<FunctionOps>,
    /// Linear memories
    pub memories: Vec<WasmMemory>,
    /// Data segments (offset, data) for memory initialization
    pub data_segments: Vec<(u32, Vec<u8>)>,
    /// Import entries (module name, field name, kind)
    pub imports: Vec<ImportEntry>,
    /// Number of imported functions (for distinguishing import calls from local calls)
    pub num_imported_funcs: u32,
    /// AAPCS integer-argument count per function, indexed by the *full* WASM
    /// function index (imported functions first, then locally-defined ones).
    /// Used by the backend to marshal call arguments into R0–R3 (issue #195).
    /// Counts every parameter as one slot (i64/f64 over-counted — see the
    /// backend's `set_func_arg_counts` scope note).
    pub func_arg_counts: Vec<u32>,
    /// AAPCS integer-argument count per *function type*, indexed by type index.
    /// Used by `call_indirect`, whose callee arg count comes from the static
    /// type index (issue #195).
    pub type_arg_counts: Vec<u32>,
    /// #311: whether each *function* (full index, imports first) returns i64 —
    /// the call lowering must tag the result as a register PAIR (r0:r1) or the
    /// hi half is invisible to liveness and the next constant clobbers it.
    pub func_ret_i64: Vec<bool>,
    /// #311: whether each *function type* returns i64 (for `call_indirect`).
    pub type_ret_i64: Vec<bool>,
    /// #359: declared parameter widths per *function* (full index, imports
    /// first): `func_params_i64[f][k]` is true when param `k` is i64/f64. The
    /// AAPCS stack-argument path needs the declared widths — op-stream inference
    /// can't see an unused i64 param that still shifts the incoming-stack layout.
    pub func_params_i64: Vec<Vec<bool>>,
    /// GI-FPU-002 (#619/#369): declared f32-param mask per *function* (full
    /// index, imports first): `func_params_f32[f][k]` is true when param `k` is
    /// f32. The direct selector homes hard-float f32 args in S0..S15 (AAPCS-VFP),
    /// which op-stream inference cannot recover for a pure-passthrough f32 param.
    pub func_params_f32: Vec<Vec<bool>>,
    /// Defined globals with their initializers (#237). Empty if the module has
    /// no global section. Used by the native-pointer ABI to make a global whose
    /// initializer is a linear-memory address (e.g. `$__stack_pointer`)
    /// self-contained rather than table-relative.
    pub globals: Vec<WasmGlobal>,
    /// Function indices that populate any table via an element segment (#275).
    /// These are the possible `call_indirect` targets — a function reached only
    /// through the table is invisible to direct-`call` reachability, so the
    /// whole-graph closure must treat every table entry as reachable once any
    /// reachable function performs a `call_indirect`. Empty for modules with no
    /// element section (every leaf/direct-call module), keeping output identical.
    pub elem_func_indices: Vec<u32>,
    /// #642: compile-time size (in entries) of table 0 — `table_sizes[0]`,
    /// kept as a convenience accessor. See [`Self::table_sizes`].
    pub table_size: Option<u32>,
    /// #650: compile-time size (in entries) per table, indexed by table index
    /// (imported tables first, then the table section, in declaration order).
    /// A DEFINED table's size is exact: `table.grow`/`table.set` are
    /// unsupported ops (their functions loud-skip at decode), so nothing
    /// synth compiles can resize or retype a table. An imported table only
    /// yields a sound bound when its limits pin the size (`max == initial`);
    /// otherwise its entry is `None` and the `call_indirect` lowering
    /// declines (for that table AND for any later table, whose base offset
    /// within the contiguous R11 region is then unknown).
    pub table_sizes: Vec<Option<u32>>,
    /// #642: per element segment, everything the closed-world `call_indirect`
    /// type check needs. `offset` is the const i32 placement of an ACTIVE
    /// segment into table `table_index` (`None` = passive/declared/non-const
    /// offset — statically unverifiable placement); `funcs` are the segment's
    /// function indices in slot order (`None` = an entry was not a plain
    /// `ref.func`, e.g. `ref.null` — statically unverifiable contents).
    pub elem_segments: Vec<ElemSegmentInfo>,
    /// #642: type index per function, indexed by the FULL function index
    /// (imports first, then locally-defined ones).
    pub func_type_indices: Vec<u32>,
    /// #642: canonical structural signature per type index (params/results
    /// rendered as a string) — used for the closed-world `call_indirect` type
    /// check, which must compare SIGNATURES, not raw type indices (a module
    /// may carry structurally-identical duplicate types).
    pub type_signatures: Vec<String>,
    /// VCR-PERF-002 Phase 1 (#494): proven invariants from loom's `wsc.facts`
    /// custom section, keyed by `(function index, value id)` — see
    /// `docs/design/wsc-facts-encoding.md` (schema v1) and
    /// [`crate::wsc_facts::parse_wsc_facts`]. FAIL-SAFE by contract (loom#231
    /// Q4): a missing/unparseable section or unknown version yields the empty
    /// vec, unknown fact kinds are skipped — never a decode error. Phase 1 is
    /// ingestion only: NO codegen path consumes these yet, so emitted bytes
    /// are unchanged whether or not a module carries the section.
    pub wsc_facts: Vec<crate::wsc_facts::WscFact>,
}

impl DecodedModule {
    /// #642/#650: compute the `call_indirect` guard inputs — per table, the
    /// compile-time size for the runtime bounds check, the base byte offset
    /// within the contiguous R11 region, and the per-expected-type
    /// closed-world verdict that discharges the type check at compile time.
    /// See [`CallIndirectGuards`] for the layout contract and soundness
    /// argument.
    pub fn call_indirect_guards(&self) -> CallIndirectGuards {
        let n_types = self.type_signatures.len();

        // A segment whose PLACEMENT is not statically attributable
        // (passive/declared segment, non-const offset, or a table index the
        // module does not declare) poisons EVERY table: `table.init` (itself
        // an unsupported op) or a computed offset could land its entries
        // anywhere, so no table's image is verifiable.
        let global_poison: Option<&'static str> = self
            .elem_segments
            .iter()
            .any(|seg| seg.offset.is_none() || seg.table_index as usize >= self.table_sizes.len())
            .then_some(
                "element segment is not statically verifiable (passive/declared \
                 segment, non-const offset, out-of-range table, or non-`ref.func` \
                 entry)",
            );

        // #676: structural signature classes — structurally-equal types share
        // one dense 1-based id (first-occurrence order over the type section);
        // id 0 is reserved for null slots. These feed the type-id sidecar and
        // the expected-type compare immediate of the runtime type check.
        let mut class_of_sig: std::collections::HashMap<&str, u32> =
            std::collections::HashMap::new();
        let mut type_class_ids: Vec<u32> = Vec::with_capacity(n_types);
        for sig in &self.type_signatures {
            let next = class_of_sig.len() as u32 + 1;
            type_class_ids.push(*class_of_sig.entry(sig.as_str()).or_insert(next));
        }

        let mut tables = Vec::with_capacity(self.table_sizes.len());
        // #676: per table, the slot class ids (None = image not statically
        // known) — concatenated into the sidecar image below.
        let mut per_table_slot_ids: Vec<Option<Vec<u32>>> =
            Vec::with_capacity(self.table_sizes.len());
        // Running word offset of the next table's base within the R11 region;
        // `None` once a table of unknown size is passed (every later base is
        // then not a compile-time constant).
        let mut base_words: Option<u32> = Some(0);
        for (n, &size) in self.table_sizes.iter().enumerate() {
            let base_byte_offset = base_words.and_then(|w| w.checked_mul(4));
            let (type_reject, has_null_slots, slot_class_ids) =
                self.table_type_reject(n as u32, size, global_poison, n_types, &type_class_ids);
            // #676: heterogeneous = the image is statically known and its
            // INITIALIZED slots span >= 2 distinct structural classes (null
            // slots — id 0 — don't count; a sparse homogeneous table stays
            // on the #664 verified-plus-null-check path, bytes identical).
            let runtime_type_check = slot_class_ids.as_ref().is_some_and(|ids| {
                let mut distinct: Vec<u32> = ids.iter().copied().filter(|&c| c != 0).collect();
                distinct.sort_unstable();
                distinct.dedup();
                distinct.len() >= 2
            });
            per_table_slot_ids.push(slot_class_ids);
            tables.push(TableGuards {
                table_size: size,
                base_byte_offset,
                type_reject,
                has_null_slots,
                runtime_type_check,
            });
            base_words = match (base_words, size) {
                (Some(w), Some(s)) => w.checked_add(s),
                _ => None,
            };
        }

        // #676: the sidecar exists only when some table actually needs the
        // runtime check AND the whole pointer region's size is compile-time
        // known (`base_words` survived every table) — otherwise the sidecar
        // base is not a constant and heterogeneous dispatches keep declining
        // (their `runtime_type_check` flag is cleared so the lowering sees a
        // plain reject).
        let any_hetero = tables.iter().any(|t| t.runtime_type_check);
        let type_ids_byte_offset = base_words
            .filter(|_| any_hetero)
            .and_then(|w| w.checked_mul(4));
        let type_ids_image = if type_ids_byte_offset.is_some() {
            self.table_sizes
                .iter()
                .zip(&per_table_slot_ids)
                .flat_map(|(&size, ids)| match ids {
                    Some(ids) => ids.clone(),
                    // Image not statically known: zero words (id 0 never
                    // matches an expected class id >= 1 — trap, not branch).
                    None => vec![0u32; size.unwrap_or(0) as usize],
                })
                .collect()
        } else {
            for t in &mut tables {
                t.runtime_type_check = false;
            }
            Vec::new()
        };
        CallIndirectGuards {
            tables,
            type_ids_byte_offset,
            type_ids_image,
            type_class_ids: if type_ids_byte_offset.is_some() {
                type_class_ids
            } else {
                Vec::new()
            },
        }
    }

    /// #642/#650: the closed-world type verdicts for ONE table — `None` per
    /// expected type when every INITIALIZED slot of table `n` verifiably
    /// holds a function of that exact structural signature; `Some(reason)`
    /// otherwise. The second component is `has_null_slots` (#664): whether
    /// the table image left any slot uninitialized — a `call_indirect`
    /// reaching one must TRAP at runtime (null check on the loaded pointer),
    /// which the lowering emits only when this is set. Reject paths return
    /// `false` (the verdict declines before the flag is consulted). The
    /// third component (#676) is the table's slot class ids — per slot, the
    /// structural signature class of the initializing function (0 for a
    /// null slot) — `Some` exactly when the table image is statically
    /// known; it feeds the type-id sidecar and the heterogeneity verdict.
    fn table_type_reject(
        &self,
        n: u32,
        size: Option<u32>,
        global_poison: Option<&str>,
        n_types: usize,
        type_class_ids: &[u32],
    ) -> (Vec<Option<String>>, bool, Option<Vec<u32>>) {
        let reject_all = |reason: String| (vec![Some(reason); n_types], false, None);

        if let Some(reason) = global_poison {
            return reject_all(reason.to_string());
        }
        let Some(size) = size else {
            return reject_all(format!(
                "table {n} has no compile-time-fixed size (imported table with \
                 growable limits)"
            ));
        };

        // Reconstruct the table image: slot -> initializing function index.
        let mut slots: Vec<Option<u32>> = vec![None; size as usize];
        for seg in self.elem_segments.iter().filter(|s| s.table_index == n) {
            let (Some(off), Some(funcs)) = (seg.offset, seg.funcs.as_ref()) else {
                // Placement is known (global_poison ruled `offset: None` out),
                // so this is an unverifiable CONTENTS case — it poisons only
                // the table it targets.
                return reject_all(format!(
                    "element segment targeting table {n} is not statically \
                     verifiable (non-`ref.func` entry)"
                ));
            };
            for (k, &f) in funcs.iter().enumerate() {
                let Some(slot) = slots.get_mut(off as usize + k) else {
                    return reject_all(format!(
                        "element segment (offset {off}, {} entries) writes past \
                         table {n}'s declared size {size}",
                        funcs.len()
                    ));
                };
                *slot = Some(f);
            }
        }
        // #664: an uninitialized slot is a null funcref — calling it must
        // trap (WASM Core §4.4.8). It no longer poisons the closed world
        // (pre-#664 it rejected EVERY type): the layout contract requires
        // null slots to be linked as ZERO words, so the lowering discharges
        // the trap at RUNTIME with a null check on the loaded pointer. The
        // type check below therefore covers the INITIALIZED slots only —
        // a null slot can never produce a live callee of the wrong type,
        // because the null check traps before the branch.
        let has_null_slots = slots.iter().any(|s| s.is_none());

        let rejects = (0..n_types)
            .map(|t| {
                for f in slots.iter().flatten() {
                    let Some(&fty) = self.func_type_indices.get(*f as usize) else {
                        return Some(format!(
                            "table {n} entry references function {f} with no known type"
                        ));
                    };
                    if self.type_signatures.get(fty as usize) != self.type_signatures.get(t) {
                        return Some(format!(
                            "table {n} entry (function {f}, type {fty}) has a different \
                             signature than expected type {t}"
                        ));
                    }
                }
                None
            })
            .collect();
        // #676: per-slot structural class ids (0 = null). `None` as soon as
        // any initializing function's type is unknown — the image is then
        // not statically classifiable and the table can neither verify nor
        // carry the runtime check (the rejects above already name it).
        let slot_class_ids: Option<Vec<u32>> = slots
            .iter()
            .map(|s| match s {
                None => Some(0u32),
                Some(f) => self
                    .func_type_indices
                    .get(*f as usize)
                    .and_then(|&fty| type_class_ids.get(fty as usize).copied()),
            })
            .collect();
        (rejects, has_null_slots, slot_class_ids)
    }
}

/// Decode a WASM binary and extract functions, memory, and data segments
pub fn decode_wasm_module(wasm_bytes: &[u8]) -> Result<DecodedModule> {
    let mut functions = Vec::new();
    let mut memories = Vec::new();
    let mut data_segments = Vec::new();
    let mut globals: Vec<WasmGlobal> = Vec::new();
    let mut imports = Vec::new();
    let mut func_index = 0u32;
    let mut num_imported_funcs = 0u32;
    let mut export_names: HashMap<u32, String> = HashMap::new();
    // #195: per-type AAPCS arg count (indexed by type index) and per-function
    // arg count (indexed by full function index: imports first, then locals).
    let mut type_arg_counts: Vec<u32> = Vec::new();
    let mut func_arg_counts: Vec<u32> = Vec::new();
    let mut type_ret_i64: Vec<bool> = Vec::new();
    let mut func_ret_i64: Vec<bool> = Vec::new();
    // #359: declared param widths per type / per function (full index).
    let mut type_params_i64: Vec<Vec<bool>> = Vec::new();
    let mut func_params_i64: Vec<Vec<bool>> = Vec::new();
    // GI-FPU-002 (#619/#369): per-type / per-function declared f32-param mask,
    // so the direct selector can home hard-float (AAPCS-VFP) f32 args in S0..S15
    // instead of the core-register (R0..R3) integer path. Independent of
    // `params_i64` (which lumps f64 with i64): an f32 param is neither.
    let mut type_params_f32: Vec<Vec<bool>> = Vec::new();
    let mut func_params_f32: Vec<Vec<bool>> = Vec::new();
    // #509: (param_count, result_count) per type index, for FuncType blocktypes.
    let mut type_block_arity: Vec<(u8, u8)> = Vec::new();
    let mut elem_func_indices: Vec<u32> = Vec::new();
    // #642/#650: call_indirect guard inputs — per-table fixed sizes (imports
    // first, then the table section, in declaration order), per-segment
    // static shapes, per-function type index, per-type canonical signature.
    let mut table_sizes: Vec<Option<u32>> = Vec::new();
    let mut elem_segments: Vec<ElemSegmentInfo> = Vec::new();
    let mut func_type_indices: Vec<u32> = Vec::new();
    let mut type_signatures: Vec<String> = Vec::new();
    // #394 Tier-1.x: function index → developer-facing name from the wasm
    // `name` custom section (function-names subsection). Applied to
    // `FunctionOps.debug_name` after the parse loop — the custom section
    // conventionally trails the code section, so the entries are not yet
    // available when each `CodeSectionEntry` is decoded.
    let mut name_section_names: HashMap<u32, String> = HashMap::new();
    // VCR-PERF-002 Phase 1 (#494): facts from loom's `wsc.facts` custom
    // section. `None` until (and unless) the first such section is seen —
    // duplicates are ignored (one prover, one section; encoding doc rule).
    let mut wsc_facts: Option<Vec<crate::wsc_facts::WscFact>> = None;
    // GI-FPU-001 (#369): f32/f64-typed globals in the FULL global index space
    // (imports first, then defined). `global.get`/`global.set` decode fine
    // (they are type-agnostic ops), but there is no float lowering: the
    // f32.const/f64.const initializer is silently dropped (`init_i32: None`
    // → slot zeroed), so a read returns 0.0 instead of the init — a silent
    // wrong value. Functions touching a float global loud-skip instead.
    let mut num_imported_globals = 0u32;
    let mut float_globals: std::collections::HashSet<u32> = std::collections::HashSet::new();
    // #680: v128-typed globals (same index space) — a SIMD access has no
    // lowering on any target, so touching one must loud-skip the function.
    let mut v128_globals: std::collections::HashSet<u32> = std::collections::HashSet::new();
    // #680: per-type "params/results contain v128" and its per-defined-function
    // projection — a v128 param/result is expressible with ZERO SIMD-proposal
    // operators in the body (`local.get 0` passthrough), so the operator-level
    // catch alone would miss it.
    let mut type_has_v128: Vec<bool> = Vec::new();
    let mut func_sig_has_v128: Vec<bool> = Vec::new();

    for payload in Parser::new(0).parse_all(wasm_bytes) {
        let payload = payload.context("Failed to parse WASM payload")?;

        match payload {
            Payload::TypeSection(reader) => {
                // Record the parameter count of each function type so calls can
                // marshal the right number of arguments (issue #195).
                for rec_group in reader {
                    let rec_group = rec_group.context("Failed to parse type")?;
                    for sub_ty in rec_group.types() {
                        // #509: blocktype arity per type index (saturated u8 —
                        // >255 params/results is far beyond anything the
                        // selector supports anyway, and the selector declines
                        // rather than trusting a saturated count).
                        type_block_arity.push(match &sub_ty.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(f) => (
                                u8::try_from(f.params().len()).unwrap_or(u8::MAX),
                                u8::try_from(f.results().len()).unwrap_or(u8::MAX),
                            ),
                            _ => (u8::MAX, u8::MAX),
                        });
                        let (count, ret_i64, params_i64) = match &sub_ty.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(func_ty) => (
                                func_ty.params().len() as u32,
                                func_ty
                                    .results()
                                    .first()
                                    .is_some_and(|t| *t == wasmparser::ValType::I64),
                                // #359: i64/f64 params occupy 8 bytes / a register
                                // pair under AAPCS. f32/f64 are not in scope for the
                                // stack-arg path (refused), but mark both 64-bit
                                // float and i64 so the guard catches them.
                                func_ty
                                    .params()
                                    .iter()
                                    .map(|t| {
                                        matches!(
                                            t,
                                            wasmparser::ValType::I64 | wasmparser::ValType::F64
                                        )
                                    })
                                    .collect::<Vec<bool>>(),
                            ),
                            _ => (0, false, Vec::new()),
                        };
                        // GI-FPU-002: declared f32-param mask for this type.
                        let params_f32 = match &sub_ty.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(func_ty) => func_ty
                                .params()
                                .iter()
                                .map(|t| matches!(t, wasmparser::ValType::F32))
                                .collect::<Vec<bool>>(),
                            _ => Vec::new(),
                        };
                        type_arg_counts.push(count);
                        type_ret_i64.push(ret_i64);
                        type_params_i64.push(params_i64);
                        type_params_f32.push(params_f32);
                        // #680: v128 anywhere in the signature.
                        type_has_v128.push(match &sub_ty.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(f) => f
                                .params()
                                .iter()
                                .chain(f.results())
                                .any(|t| *t == wasmparser::ValType::V128),
                            _ => false,
                        });
                        // #642: canonical structural signature for the
                        // closed-world call_indirect type check (compares
                        // SIGNATURES so duplicate types stay interchangeable).
                        type_signatures.push(match &sub_ty.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(f) => {
                                format!("{:?}->{:?}", f.params(), f.results())
                            }
                            other => format!("non-func:{other:?}"),
                        });
                    }
                }
            }
            Payload::ImportSection(reader) => {
                // wasmparser 0.221+ groups imports (the "compact imports"
                // proposal): the section reader yields `Imports` groups, each of
                // which may expand to several `Import`s. `into_imports()`
                // flattens groups back to individual `Import`s (preserving the
                // module/name/ty fields), keeping the per-import loop intact.
                for import in reader.into_imports() {
                    let import = import.context("Failed to parse import")?;
                    let (kind, idx) = match import.ty {
                        wasmparser::TypeRef::Func(type_idx) => {
                            let idx = num_imported_funcs;
                            num_imported_funcs += 1;
                            // Record the imported function's arg count at its
                            // full function index (imports come first).
                            func_type_indices.push(type_idx); // #642
                            func_arg_counts
                                .push(type_arg_counts.get(type_idx as usize).copied().unwrap_or(0));
                            func_ret_i64.push(
                                type_ret_i64
                                    .get(type_idx as usize)
                                    .copied()
                                    .unwrap_or(false),
                            );
                            func_params_i64.push(
                                type_params_i64
                                    .get(type_idx as usize)
                                    .cloned()
                                    .unwrap_or_default(),
                            );
                            func_params_f32.push(
                                type_params_f32
                                    .get(type_idx as usize)
                                    .cloned()
                                    .unwrap_or_default(),
                            );
                            (ImportKind::Function(type_idx), idx)
                        }
                        wasmparser::TypeRef::Memory(_) => (ImportKind::Memory, 0),
                        wasmparser::TypeRef::Table(t) => {
                            // #642: an imported table only yields a SOUND
                            // compile-time bound when its limits pin the size
                            // exactly (max == initial) — a growable import
                            // could be larger at runtime, and a bounds guard
                            // against `initial` would trap spec-valid calls.
                            // #650: imported tables take the leading table
                            // indices, in declaration order.
                            table_sizes.push(match (u32::try_from(t.initial), t.maximum) {
                                (Ok(init), Some(max)) if u64::from(init) == max => Some(init),
                                _ => None,
                            });
                            (ImportKind::Table, 0)
                        }
                        wasmparser::TypeRef::Global(g) => {
                            // GI-FPU-001 (#369): imported globals come first in
                            // the global index space — record float-typed ones
                            // so accesses loud-skip their function.
                            if matches!(
                                g.content_type,
                                wasmparser::ValType::F32 | wasmparser::ValType::F64
                            ) {
                                float_globals.insert(num_imported_globals);
                            }
                            // #680: v128-typed imported globals — same lane.
                            if g.content_type == wasmparser::ValType::V128 {
                                v128_globals.insert(num_imported_globals);
                            }
                            num_imported_globals += 1;
                            (ImportKind::Global, 0)
                        }
                        _ => continue,
                    };
                    imports.push(ImportEntry {
                        module: import.module.to_string(),
                        name: import.name.to_string(),
                        kind,
                        index: idx,
                    });
                }
            }
            Payload::FunctionSection(reader) => {
                // Each entry gives the type index of a locally-defined function,
                // in order. Their full function indices follow the imports, so
                // appending to `func_arg_counts` keeps it indexed by full index
                // (issue #195).
                for ty in reader {
                    let type_idx = ty.context("Failed to parse function type index")?;
                    func_type_indices.push(type_idx); // #642
                    func_arg_counts
                        .push(type_arg_counts.get(type_idx as usize).copied().unwrap_or(0));
                    func_ret_i64.push(
                        type_ret_i64
                            .get(type_idx as usize)
                            .copied()
                            .unwrap_or(false),
                    );
                    func_params_i64.push(
                        type_params_i64
                            .get(type_idx as usize)
                            .cloned()
                            .unwrap_or_default(),
                    );
                    func_params_f32.push(
                        type_params_f32
                            .get(type_idx as usize)
                            .cloned()
                            .unwrap_or_default(),
                    );
                    // #680: defined-function order matches code-entry order.
                    func_sig_has_v128.push(
                        type_has_v128
                            .get(type_idx as usize)
                            .copied()
                            .unwrap_or(false),
                    );
                }
            }
            Payload::TableSection(reader) => {
                // #642: a DEFINED table's compile-time size is exact — its
                // initial size is its permanent size, because nothing synth
                // compiles can resize it (`table.grow` is an unsupported op
                // whose function loud-skips at decode). #650: EVERY table is
                // recorded — the contiguous R11 region places table N at
                // byte offset `sum(size(0..N)) * 4`.
                for table in reader {
                    let table = table.context("Failed to parse table")?;
                    table_sizes.push(u32::try_from(table.ty.initial).ok());
                }
            }
            Payload::MemorySection(reader) => {
                for (idx, memory) in reader.into_iter().enumerate() {
                    let mem = memory.context("Failed to parse memory")?;
                    memories.push(WasmMemory {
                        index: idx as u32,
                        initial_pages: mem.initial as u32,
                        max_pages: mem.maximum.map(|m| m as u32),
                        shared: mem.shared,
                    });
                }
            }
            Payload::GlobalSection(reader) => {
                // #237/#649: capture each defined global's constant initializer
                // + mutability. The init is a const expr; we decode a leading
                // `i32.const` (the `$__stack_pointer`/data-layout shape) or
                // `i64.const` (#649: capturing only i32 silently ZEROED every
                // nonzero i64 init). f32/f64 inits stay `None` on purpose —
                // float global access is the GI-FPU-001 (#369) loud-skip lane —
                // as do non-const init exprs (`global.get` of an import).
                for (idx, global) in reader.into_iter().enumerate() {
                    let global = global.context("Failed to parse global")?;
                    let mut ops = global.init_expr.get_operators_reader();
                    let init = match ops.read() {
                        Ok(wasmparser::Operator::I32Const { value }) => {
                            Some(GlobalInit::I32(value))
                        }
                        Ok(wasmparser::Operator::I64Const { value }) => {
                            Some(GlobalInit::I64(value))
                        }
                        _ => None,
                    };
                    // #643: record the slot width from the DECLARED value type.
                    // i64/f64 globals occupy 8 bytes (a register pair on the
                    // 32-bit targets), v128 sixteen; laying every global out at
                    // `index * 4` silently dropped the high word of every i64.
                    let slot_bytes = match global.ty.content_type {
                        wasmparser::ValType::I64 | wasmparser::ValType::F64 => 8,
                        wasmparser::ValType::V128 => 16,
                        _ => 4,
                    };
                    // GI-FPU-001 (#369): a float-typed global's initializer is
                    // NOT captured (`init_i32` only decodes `i32.const`), so
                    // its slot would be silently zeroed — record it so any
                    // function accessing it loud-skips instead of reading a
                    // silently-wrong 0.0.
                    if matches!(
                        global.ty.content_type,
                        wasmparser::ValType::F32 | wasmparser::ValType::F64
                    ) {
                        float_globals.insert(num_imported_globals + idx as u32);
                    }
                    // #680: a v128-typed global's `v128.const` initializer is
                    // not captured either (slot zeroed) and an access moves 4
                    // of the 16 bytes — record it so accesses loud-skip.
                    if global.ty.content_type == wasmparser::ValType::V128 {
                        v128_globals.insert(num_imported_globals + idx as u32);
                    }
                    globals.push(WasmGlobal {
                        index: idx as u32,
                        init,
                        mutable: global.ty.mutable,
                        slot_bytes,
                    });
                }
            }
            Payload::DataSection(reader) => {
                for data in reader {
                    let data = data.context("Failed to parse data segment")?;
                    if let wasmparser::DataKind::Active {
                        memory_index: 0,
                        offset_expr,
                    } = data.kind
                    {
                        let mut ops = offset_expr.get_operators_reader();
                        if let Ok(wasmparser::Operator::I32Const { value }) = ops.read() {
                            data_segments.push((value as u32, data.data.to_vec()));
                        }
                    }
                }
            }
            Payload::ElementSection(reader) => {
                // #275: collect every function index that initializes a table.
                // These are the `call_indirect` targets the direct-call closure
                // cannot see; `reachable_from_exports` unions them in when a
                // reachable function does a `call_indirect`. Both element forms
                // are handled: a flat function-index list, and the const-expr
                // form whose `ref.func` entries name the functions.
                for elem in reader {
                    let elem = elem.context("Failed to parse element segment")?;
                    // #642/#650: the segment's static placement — a const i32
                    // offset of an ACTIVE segment into its target table (any
                    // table index: the R11 region is contiguous, #650);
                    // anything else is unverifiable and poisons the
                    // closed-world type check.
                    let (seg_table, seg_offset): (u32, Option<u32>) = match &elem.kind {
                        wasmparser::ElementKind::Active {
                            table_index,
                            offset_expr,
                        } => {
                            let mut ops = offset_expr.get_operators_reader();
                            let off = match ops.read() {
                                Ok(wasmparser::Operator::I32Const { value }) => {
                                    u32::try_from(value).ok()
                                }
                                _ => None,
                            };
                            (table_index.unwrap_or(0), off)
                        }
                        _ => (0, None),
                    };
                    let mut seg_funcs: Option<Vec<u32>> = Some(Vec::new());
                    match elem.items {
                        wasmparser::ElementItems::Functions(funcs) => {
                            for f in funcs {
                                let f = f.context("Failed to parse element func index")?;
                                elem_func_indices.push(f);
                                if let Some(v) = seg_funcs.as_mut() {
                                    v.push(f);
                                }
                            }
                        }
                        wasmparser::ElementItems::Expressions(_, exprs) => {
                            for expr in exprs {
                                let expr = expr.context("Failed to parse element expr")?;
                                // #642: an entry is verifiable only when it is
                                // a single plain `ref.func` (reader yields the
                                // op + the implicit `end`). `ref.null` or any
                                // computed entry poisons the segment.
                                let mut entry_func: Option<u32> = None;
                                let mut plain = true;
                                for (k, op) in expr.get_operators_reader().into_iter().enumerate() {
                                    match (k, op.context("Failed to parse element op")?) {
                                        (0, wasmparser::Operator::RefFunc { function_index }) => {
                                            elem_func_indices.push(function_index);
                                            entry_func = Some(function_index);
                                        }
                                        (_, wasmparser::Operator::End) => {}
                                        (_, wasmparser::Operator::RefFunc { function_index }) => {
                                            // Keep the pre-#642 reachability
                                            // behaviour: every ref.func seen
                                            // anywhere is a possible target.
                                            elem_func_indices.push(function_index);
                                            plain = false;
                                        }
                                        _ => plain = false,
                                    }
                                }
                                match (plain, entry_func, seg_funcs.as_mut()) {
                                    (true, Some(f), Some(v)) => v.push(f),
                                    _ => seg_funcs = None,
                                }
                            }
                        }
                    }
                    elem_segments.push(ElemSegmentInfo {
                        table_index: seg_table,
                        offset: seg_offset,
                        funcs: seg_funcs,
                    });
                }
            }
            Payload::ExportSection(exports) => {
                for export in exports {
                    let export = export.context("Failed to parse export")?;
                    if export.kind == ExternalKind::Func {
                        export_names.insert(export.index, export.name.to_string());
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                let (ops, op_offsets, block_arity, mut unsupported) =
                    decode_function_body(&body, &type_block_arity, &float_globals, &v128_globals)?;
                // #680: a v128 param/result reaches the body only through
                // type-agnostic ops (a `local.get 0` passthrough compiles to
                // a 4-byte `mov`), so flag the SIGNATURE even when the body
                // contains no SIMD-proposal operator.
                if unsupported.is_none()
                    && func_sig_has_v128
                        .get(func_index as usize)
                        .copied()
                        .unwrap_or(false)
                {
                    unsupported = Some(
                        "signature has a v128 param/result — no SIMD lowering \
                         for this target (#680)"
                            .to_string(),
                    );
                }
                let actual_index = num_imported_funcs + func_index;
                let export_name = export_names.get(&actual_index).cloned();

                functions.push(FunctionOps {
                    index: actual_index,
                    export_name,
                    debug_name: None, // filled from the `name` section after the loop
                    ops,
                    op_offsets,
                    unsupported,
                    block_arity,
                });
                func_index += 1;
            }
            Payload::CustomSection(c) => {
                // #394 Tier-1.x: the wasm `name` custom section.
                if let wasmparser::KnownCustom::Name(reader) = c.as_known() {
                    parse_name_section_func_names(reader, &mut name_section_names);
                }
                // VCR-PERF-002 Phase 1 (#494): loom's `wsc.facts` section.
                // `parse_wsc_facts` is TOTAL (fail-safe skew, loom#231 Q4):
                // any malformed payload decodes to the empty fact list WITH a
                // stderr diagnostic, never an error — facts are optional
                // accelerators and must not be able to change a compilation
                // outcome. First section wins.
                if c.name() == crate::wsc_facts::WSC_FACTS_SECTION_NAME && wsc_facts.is_none() {
                    let parsed = crate::wsc_facts::parse_wsc_facts(c.data());
                    if let Some(reason) = &parsed.section_ignored {
                        eprintln!(
                            "warning: ignoring unparseable `wsc.facts` custom section \
                             ({reason}) — facts are optional accelerators, compilation \
                             is unaffected (#494 fail-safe skew rule)"
                        );
                    } else if parsed.records_skipped > 0 {
                        eprintln!(
                            "warning: skipped {} unknown/undecodable `wsc.facts` \
                             record(s) (likely a newer loom emitter); {} known fact(s) \
                             kept, compilation is unaffected (#494 fail-safe skew rule)",
                            parsed.records_skipped,
                            parsed.facts.len()
                        );
                    }
                    wsc_facts = Some(parsed.facts);
                }
            }
            _ => {}
        }
    }

    apply_name_section(&mut functions, &name_section_names);

    Ok(DecodedModule {
        functions,
        memories,
        data_segments,
        imports,
        num_imported_funcs,
        func_arg_counts,
        type_arg_counts,
        func_ret_i64,
        type_ret_i64,
        func_params_i64,
        func_params_f32,
        globals,
        elem_func_indices,
        table_size: table_sizes.first().copied().flatten(),
        table_sizes,
        elem_segments,
        func_type_indices,
        type_signatures,
        wsc_facts: wsc_facts.unwrap_or_default(),
    })
}

/// Parse the function-names subsection of a wasm `name` custom section into
/// `out` (function index → developer-facing name, e.g.
/// `core::panicking::panic_fmt::h...`). Best-effort by design: the section is
/// DEBUG METADATA only, so a malformed entry is skipped rather than failing the
/// compile — no codegen path depends on it (#394 Tier-1.x).
fn parse_name_section_func_names(
    reader: wasmparser::NameSectionReader<'_>,
    out: &mut HashMap<u32, String>,
) {
    for subsection in reader.into_iter().flatten() {
        if let wasmparser::Name::Function(map) = subsection {
            for naming in map.into_iter().flatten() {
                out.insert(naming.index, naming.name.to_string());
            }
        }
    }
}

/// Fill each function's `debug_name` from the `name`-section map (keyed by the
/// FULL function index, imports first — the same index space `FunctionOps.index`
/// uses). A function without an entry keeps `None` (⇒ `func_N` downstream).
fn apply_name_section(functions: &mut [FunctionOps], names: &HashMap<u32, String>) {
    if names.is_empty() {
        return;
    }
    for f in functions {
        f.debug_name = names.get(&f.index).cloned();
    }
}

/// Decode a WASM binary and extract all function bodies as WasmOp sequences
pub fn decode_wasm_functions(wasm_bytes: &[u8]) -> Result<Vec<FunctionOps>> {
    let mut functions = Vec::new();
    let mut func_index = 0u32;
    let mut num_imported_funcs = 0u32;
    let mut export_names: HashMap<u32, String> = HashMap::new();
    let mut name_section_names: HashMap<u32, String> = HashMap::new();
    // #509: (param_count, result_count) per type index, for FuncType blocktypes.
    let mut type_block_arity: Vec<(u8, u8)> = Vec::new();
    // GI-FPU-001 (#369): float-typed globals (full index space, imports first)
    // whose accesses must loud-skip — see `decode_wasm_module`.
    let mut num_imported_globals = 0u32;
    let mut float_globals: std::collections::HashSet<u32> = std::collections::HashSet::new();
    // #680: v128-typed globals + v128 params/results — see `decode_wasm_module`.
    let mut v128_globals: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let mut type_has_v128: Vec<bool> = Vec::new();
    let mut func_sig_has_v128: Vec<bool> = Vec::new();

    for payload in Parser::new(0).parse_all(wasm_bytes) {
        let payload = payload.context("Failed to parse WASM payload")?;

        match payload {
            Payload::TypeSection(reader) => {
                // #509: the blocktype-arity side-table needs the type section
                // for `BlockType::FuncType(i)` lookups (the wasm binary format
                // places types before code, so the table is complete before any
                // `CodeSectionEntry` is decoded).
                for rec_group in reader {
                    let rec_group = rec_group.context("Failed to parse type")?;
                    for sub_ty in rec_group.types() {
                        type_block_arity.push(match &sub_ty.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(f) => (
                                u8::try_from(f.params().len()).unwrap_or(u8::MAX),
                                u8::try_from(f.results().len()).unwrap_or(u8::MAX),
                            ),
                            _ => (u8::MAX, u8::MAX),
                        });
                        // #680: v128 anywhere in the signature.
                        type_has_v128.push(match &sub_ty.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(f) => f
                                .params()
                                .iter()
                                .chain(f.results())
                                .any(|t| *t == wasmparser::ValType::V128),
                            _ => false,
                        });
                    }
                }
            }
            Payload::ImportSection(imports) => {
                // wasmparser 0.221+ compact-imports grouping — flatten groups
                // to individual imports (see the ImportSection handler above).
                for import in imports.into_imports() {
                    let import = import.context("Failed to parse import")?;
                    match import.ty {
                        wasmparser::TypeRef::Func(_) => num_imported_funcs += 1,
                        wasmparser::TypeRef::Global(g) => {
                            // GI-FPU-001 (#369): see `decode_wasm_module` —
                            // float-typed global accesses must loud-skip.
                            if matches!(
                                g.content_type,
                                wasmparser::ValType::F32 | wasmparser::ValType::F64
                            ) {
                                float_globals.insert(num_imported_globals);
                            }
                            // #680: v128-typed imported globals — same lane.
                            if g.content_type == wasmparser::ValType::V128 {
                                v128_globals.insert(num_imported_globals);
                            }
                            num_imported_globals += 1;
                        }
                        _ => {}
                    }
                }
            }
            Payload::FunctionSection(reader) => {
                // #680: defined-function type indices, in order — the per-
                // function v128-signature flag (`decode_wasm_module` gets this
                // from its existing FunctionSection handling).
                for ty in reader {
                    let type_idx = ty.context("Failed to parse function type index")?;
                    func_sig_has_v128.push(
                        type_has_v128
                            .get(type_idx as usize)
                            .copied()
                            .unwrap_or(false),
                    );
                }
            }
            Payload::GlobalSection(reader) => {
                // GI-FPU-001 (#369): record f32/f64-typed defined globals so
                // `decode_function_body` flags accesses (their initializer is
                // dropped on this path too — same silent-zero hazard).
                for (idx, global) in reader.into_iter().enumerate() {
                    let global = global.context("Failed to parse global")?;
                    if matches!(
                        global.ty.content_type,
                        wasmparser::ValType::F32 | wasmparser::ValType::F64
                    ) {
                        float_globals.insert(num_imported_globals + idx as u32);
                    }
                    // #680: v128-typed defined globals — same lane.
                    if global.ty.content_type == wasmparser::ValType::V128 {
                        v128_globals.insert(num_imported_globals + idx as u32);
                    }
                }
            }
            Payload::ExportSection(exports) => {
                for export in exports {
                    let export = export.context("Failed to parse export")?;
                    if export.kind == ExternalKind::Func {
                        export_names.insert(export.index, export.name.to_string());
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                let (ops, op_offsets, block_arity, mut unsupported) =
                    decode_function_body(&body, &type_block_arity, &float_globals, &v128_globals)?;
                // #680: v128 param/result — see `decode_wasm_module`.
                if unsupported.is_none()
                    && func_sig_has_v128
                        .get(func_index as usize)
                        .copied()
                        .unwrap_or(false)
                {
                    unsupported = Some(
                        "signature has a v128 param/result — no SIMD lowering \
                         for this target (#680)"
                            .to_string(),
                    );
                }
                let actual_index = num_imported_funcs + func_index;
                let export_name = export_names.get(&actual_index).cloned();

                functions.push(FunctionOps {
                    index: actual_index,
                    export_name,
                    debug_name: None, // filled from the `name` section after the loop
                    ops,
                    op_offsets,
                    unsupported,
                    block_arity,
                });
                func_index += 1;
            }
            Payload::CustomSection(c) => {
                // #394 Tier-1.x: the wasm `name` custom section.
                if let wasmparser::KnownCustom::Name(reader) = c.as_known() {
                    parse_name_section_func_names(reader, &mut name_section_names);
                }
            }
            _ => {}
        }
    }

    apply_name_section(&mut functions, &name_section_names);

    Ok(functions)
}

/// Decoded function with its WasmOp sequence
#[derive(Debug, Clone)]
pub struct FunctionOps {
    /// Function index in the module (includes imported functions)
    pub index: u32,
    /// Export name if this function is exported
    pub export_name: Option<String>,
    /// #394 Tier-1.x: the function's developer-facing name from the wasm `name`
    /// custom section (function-names subsection), e.g.
    /// `core::panicking::panic_fmt::h6651313c3e2c6c2f` — present for INTERNAL
    /// (non-exported) functions too, unlike `export_name`. DEBUG METADATA only:
    /// consumed by the `--debug-line` `DW_TAG_subprogram` emit (name priority:
    /// name-section > export name > `func_N`); no codegen or symbol-table path
    /// reads it, so emitted `.text`/`.symtab` are unchanged (frozen-safe).
    /// `None` when the module has no `name` section or no entry for this index.
    pub debug_name: Option<String>,
    /// The WASM operations in this function body
    pub ops: Vec<WasmOp>,
    /// VCR-DBG-001 step 1 (#394): module-relative wasm byte offset of each op in
    /// `ops` (same index → same op). This is the address space DWARF-for-wasm
    /// `.debug_line` keys on, so it is the bridge from synth's op-index
    /// `source_line` to the input wasm's DWARF (wasm-offset → source). PURELY
    /// ADDITIVE metadata: no codegen path reads it, so emitted `.text` is
    /// unchanged and the frozen fixtures stay bit-identical. Empty until consumed
    /// by the DWARF emitter (Tier 1).
    pub op_offsets: Vec<u32>,
    /// `Some(reason)` when the body contained a value-affecting operator the
    /// decoder cannot lower (e.g. scalar f32/f64 — #369, bulk-memory
    /// memory.copy/fill). Such an op would otherwise be silently *dropped*
    /// (`convert_operator` → `None`), leaving the operand stack wrong and the
    /// function a silent miscompile. The compile path LOUD-SKIPS a flagged
    /// function (diagnostic + symbol absent → link error names it) instead —
    /// the #180/#185 "unsupported op must Err, never silently continue"
    /// contract. `None` once every op decoded or was intentionally ignorable
    /// (Nop).
    pub unsupported: Option<String>,
    /// #509: blocktype arity side-table — `(param_count, result_count)` of the
    /// k-th `Block`/`Loop`/`If` op in `ops`, in order of appearance.
    /// ORDINAL-keyed, not op-index-keyed, on purpose: the backend may rewrite
    /// the op stream before selection (e.g. the #539 `i32.const 0; memory.grow`
    /// → `memory.size` fold), which shifts op indices but never adds/removes
    /// control ops, so the ordinal stays aligned. `BlockType::Empty → (0,0)`,
    /// `ValType → (0,1)`, `FuncType(i) →` counts from the type section
    /// (saturated to u8; an unresolvable type index records `(u8::MAX,
    /// u8::MAX)` so the selector declines loudly instead of miscompiling).
    /// This is what lets the direct selector land a value carried by
    /// `br`/`br_if`/`br_table` in the target block's designated result
    /// register instead of dropping it — `WasmOp::Block/Loop/If` stay bare
    /// unit variants (zero ripple through the backends' match sites), and an
    /// empty table (hand-built op streams in unit tests) keeps the legacy
    /// void-block lowering.
    pub block_arity: Vec<(u8, u8)>,
}

/// #509: `(param_count, result_count)` of a wasm blocktype, for the
/// [`FunctionOps::block_arity`] side-table. `type_block_arity` is the type
/// section's per-type-index counts (needed for the `FuncType` form); a missing
/// entry saturates to `(u8::MAX, u8::MAX)` so downstream declines loudly.
fn blocktype_arity(bt: &wasmparser::BlockType, type_block_arity: &[(u8, u8)]) -> (u8, u8) {
    match bt {
        wasmparser::BlockType::Empty => (0, 0),
        wasmparser::BlockType::Type(_) => (0, 1),
        wasmparser::BlockType::FuncType(i) => type_block_arity
            .get(*i as usize)
            .copied()
            .unwrap_or((u8::MAX, u8::MAX)),
    }
}

/// The per-function payload [`decode_function_body`] extracts: `(ops,
/// op_offsets, block_arity, unsupported)` — see the matching
/// [`FunctionOps`] fields for each component's contract.
type DecodedBody = (Vec<WasmOp>, Vec<u32>, Vec<(u8, u8)>, Option<String>);

/// Decode a single function body to WasmOp sequence.
///
/// Returns the ops plus `Some(reason)` if any operator was a value-affecting
/// op the decoder cannot lower (so the function must be loud-skipped, #369 —
/// not silently miscompiled by dropping the op).
fn decode_function_body(
    body: &wasmparser::FunctionBody,
    type_block_arity: &[(u8, u8)],
    float_globals: &std::collections::HashSet<u32>,
    v128_globals: &std::collections::HashSet<u32>,
) -> Result<DecodedBody> {
    let mut ops = Vec::new();
    // VCR-DBG-001 step 1: parallel to `ops` — the module-relative wasm byte
    // offset of each emitted op (the DWARF-for-wasm address space). Captured via
    // the offset-aware reader; pushed only when an op is pushed, so indices stay
    // aligned with `ops`. Additive metadata, no codegen consumer ⇒ frozen-safe.
    let mut op_offsets = Vec::new();
    // #509: ordinal blocktype-arity side-table — one entry per Block/Loop/If in
    // `ops` order (see `FunctionOps::block_arity`).
    let mut block_arity: Vec<(u8, u8)> = Vec::new();
    let mut unsupported: Option<String> = None;

    // #680: a v128-typed LOCAL is expressible with zero SIMD-proposal
    // operators (`local.get`/`local.set`/`local.tee` are type-agnostic), but
    // every selector lowers those as 4-byte (or 8-byte i64) register moves —
    // silently truncating the 16-byte value. Flag the declaration up front.
    for local in body.get_locals_reader()? {
        let (count, ty) = local.context("Failed to read local declaration")?;
        if unsupported.is_none() && count > 0 && ty == wasmparser::ValType::V128 {
            unsupported = Some(
                "declares a v128-typed local — no SIMD lowering for this \
                 target, accesses would silently truncate the 16-byte value \
                 (#680)"
                    .to_string(),
            );
        }
    }

    let ops_reader = body.get_operators_reader()?;
    for item in ops_reader.into_iter_with_offsets() {
        let (op, offset) = item.context("Failed to read operator")?;

        // #680: SIMD (v128) category-level honesty guard. Some SIMD ops decode
        // into `WasmOp` v128 variants that only a dead, never-wired Helium/MVE
        // prototype can select (`has_helium` is set by tests alone), so on
        // every real target they were silently dropped at selection —
        // `i32x4.add` compiled to an operand passthrough and `v128.store`
        // left memory unwritten. Catch the ENTIRE SIMD + relaxed-SIMD
        // proposal space here (macro-generated from wasmparser's operator
        // table — no hand-kept list to fall out of date) and route the
        // function through the same loud-skip/honest-bail lane as scalar
        // floats (GI-FPU-001). Targets with real SIMD hardware (Helium/MVE on
        // cortex-m55) can lift this once a lowering is actually wired.
        if unsupported.is_none() && is_simd_operator(&op) {
            unsupported = Some(format!(
                "{op:?}: no SIMD lowering for this target — the op would be \
                 silently dropped to a no-op (WASM SIMD proposal, #680)"
            ));
        }

        if let Some(wasm_op) = convert_operator(&op) {
            // #509: capture the blocktype arity BEFORE the enum flattens it away
            // (`WasmOp::Block/Loop/If` are unit variants by design).
            if let wasmparser::Operator::Block { blockty }
            | wasmparser::Operator::Loop { blockty }
            | wasmparser::Operator::If { blockty } = &op
            {
                block_arity.push(blocktype_arity(blockty, type_block_arity));
            }
            // GI-FPU-001 (#369): `global.get`/`global.set` decode fine (the
            // ops are type-agnostic), but an f32/f64-typed global has no
            // float lowering — its const initializer is dropped (slot zeroed),
            // so a read returns a silently-wrong 0.0. Flag the function for
            // the same loud-skip the scalar float ops get.
            if unsupported.is_none()
                && let WasmOp::GlobalGet(i) | WasmOp::GlobalSet(i) = &wasm_op
                && float_globals.contains(i)
            {
                unsupported = Some(format!(
                    "{wasm_op:?} on an f32/f64-typed global — float globals \
                     have no lowering, the initializer would be silently \
                     zeroed (GI-FPU-001)"
                ));
            }
            // #680: same hazard for v128-typed globals — `global.get`/
            // `global.set` decode fine, but there is no SIMD lowering: the
            // access would move 4 of the 16 bytes and the `v128.const`
            // initializer is never captured (slot zeroed).
            if unsupported.is_none()
                && let WasmOp::GlobalGet(i) | WasmOp::GlobalSet(i) = &wasm_op
                && v128_globals.contains(i)
            {
                unsupported = Some(format!(
                    "{wasm_op:?} on a v128-typed global — no SIMD lowering \
                     for this target (#680)"
                ));
            }
            ops.push(wasm_op);
            op_offsets.push(offset as u32);
        } else if unsupported.is_none() && !is_intentionally_ignored(&op) {
            // The op was DROPPED by `convert_operator` (`_ => None`) and is not
            // an intentional no-op (Nop) — record it so the
            // function is loud-skipped rather than silently miscompiled (#369).
            unsupported = Some(format!("{op:?}"));
        }
    }

    Ok((ops, op_offsets, block_arity, unsupported))
}

/// Operators that `convert_operator` returns `None` for *on purpose* — they
/// carry no value-affecting semantics for our backend, so dropping them is
/// correct (NOT a silent miscompile). Everything else that decodes to `None`
/// is an unsupported op that must loud-skip its function (#369).
///
/// #665: `Unreachable` is NOT on this list — it traps (WASM §4.4.5), so it
/// decodes to `WasmOp::Unreachable` and every backend lowers it to a trap
/// instruction (or loud-declines). Only `Nop` is genuinely ignorable.
fn is_intentionally_ignored(op: &wasmparser::Operator) -> bool {
    use wasmparser::Operator::*;
    matches!(op, Nop)
}

/// #680: is `op` from the WASM SIMD or relaxed-SIMD proposal?
///
/// CATEGORY-LEVEL by construction: the match is macro-generated from
/// `wasmparser::for_each_operator!`'s own proposal markers (`@simd` /
/// `@relaxed_simd`), so it covers the entire SIMD operator space of the
/// pinned wasmparser — there is no hand-kept op list that a new lane op,
/// load/store variant, or relaxed-SIMD instruction can silently fall out of.
/// Used to loud-skip functions with SIMD ops: no target has a SIMD lowering
/// wired today (the Helium/MVE selector arms are gated on a `has_helium`
/// flag only tests set), so a decoded v128 `WasmOp` was silently dropped at
/// selection — the #554-class miscompile this predicate closes.
fn is_simd_operator(op: &wasmparser::Operator) -> bool {
    macro_rules! define_match_operator {
        ($( @$proposal:ident $op:ident $({ $($arg:ident: $argty:ty),* })? => $visit:ident ($($ann:tt)*))*) => {
            match op {
                $(
                    wasmparser::Operator::$op { .. } => {
                        define_match_operator!(impl_one @$proposal)
                    }
                )*
                // `Operator` is non-exhaustive; an operator outside the
                // pinned wasmparser's own table cannot be produced by it.
                _ => false,
            }
        };
        (impl_one @simd) => { true };
        (impl_one @relaxed_simd) => { true };
        (impl_one @$proposal:ident) => { false };
    }
    wasmparser::for_each_operator!(define_match_operator)
}

/// Convert a wasmparser Operator to our WasmOp enum
fn convert_operator(op: &wasmparser::Operator) -> Option<WasmOp> {
    use wasmparser::Operator::*;

    match op {
        // Constants
        I32Const { value } => Some(WasmOp::I32Const(*value)),

        // i32 Arithmetic
        I32Add => Some(WasmOp::I32Add),
        I32Sub => Some(WasmOp::I32Sub),
        I32Mul => Some(WasmOp::I32Mul),
        I32DivS => Some(WasmOp::I32DivS),
        I32DivU => Some(WasmOp::I32DivU),
        I32RemS => Some(WasmOp::I32RemS),
        I32RemU => Some(WasmOp::I32RemU),

        // i64 Constants
        I64Const { value } => Some(WasmOp::I64Const(*value)),

        // i64 Arithmetic
        I64Add => Some(WasmOp::I64Add),
        I64Sub => Some(WasmOp::I64Sub),
        I64Mul => Some(WasmOp::I64Mul),
        I64DivS => Some(WasmOp::I64DivS),
        I64DivU => Some(WasmOp::I64DivU),
        I64RemS => Some(WasmOp::I64RemS),
        I64RemU => Some(WasmOp::I64RemU),

        // i64 Bitwise
        I64And => Some(WasmOp::I64And),
        I64Or => Some(WasmOp::I64Or),
        I64Xor => Some(WasmOp::I64Xor),
        I64Shl => Some(WasmOp::I64Shl),
        I64ShrS => Some(WasmOp::I64ShrS),
        I64ShrU => Some(WasmOp::I64ShrU),
        I64Rotl => Some(WasmOp::I64Rotl),
        I64Rotr => Some(WasmOp::I64Rotr),
        I64Clz => Some(WasmOp::I64Clz),
        I64Ctz => Some(WasmOp::I64Ctz),
        I64Popcnt => Some(WasmOp::I64Popcnt),
        I64Extend8S => Some(WasmOp::I64Extend8S),
        I64Extend16S => Some(WasmOp::I64Extend16S),
        I64Extend32S => Some(WasmOp::I64Extend32S),
        // i32<->i64 width conversions. Previously UNMAPPED → silently dropped,
        // which left an i32 value as a 64-bit operand with a garbage high half
        // (harmless when a following `i64.shl 32` discards it, but a latent
        // miscompile for extend-then-arithmetic, and it breaks width-correct
        // register allocation). (#204)
        I64ExtendI32U => Some(WasmOp::I64ExtendI32U),
        I64ExtendI32S => Some(WasmOp::I64ExtendI32S),
        I32WrapI64 => Some(WasmOp::I32WrapI64),

        // i64 Comparison
        I64Eqz => Some(WasmOp::I64Eqz),
        I64Eq => Some(WasmOp::I64Eq),
        I64Ne => Some(WasmOp::I64Ne),
        I64LtS => Some(WasmOp::I64LtS),
        I64LtU => Some(WasmOp::I64LtU),
        I64LeS => Some(WasmOp::I64LeS),
        I64LeU => Some(WasmOp::I64LeU),
        I64GtS => Some(WasmOp::I64GtS),
        I64GtU => Some(WasmOp::I64GtU),
        I64GeS => Some(WasmOp::I64GeS),
        I64GeU => Some(WasmOp::I64GeU),

        // Bitwise
        I32And => Some(WasmOp::I32And),
        I32Or => Some(WasmOp::I32Or),
        I32Xor => Some(WasmOp::I32Xor),
        I32Shl => Some(WasmOp::I32Shl),
        I32ShrS => Some(WasmOp::I32ShrS),
        I32ShrU => Some(WasmOp::I32ShrU),
        I32Rotl => Some(WasmOp::I32Rotl),
        I32Rotr => Some(WasmOp::I32Rotr),
        I32Clz => Some(WasmOp::I32Clz),
        I32Ctz => Some(WasmOp::I32Ctz),
        I32Popcnt => Some(WasmOp::I32Popcnt),
        I32Extend8S => Some(WasmOp::I32Extend8S),
        I32Extend16S => Some(WasmOp::I32Extend16S),

        // Comparison
        I32Eqz => Some(WasmOp::I32Eqz),
        I32Eq => Some(WasmOp::I32Eq),
        I32Ne => Some(WasmOp::I32Ne),
        I32LtS => Some(WasmOp::I32LtS),
        I32LtU => Some(WasmOp::I32LtU),
        I32LeS => Some(WasmOp::I32LeS),
        I32LeU => Some(WasmOp::I32LeU),
        I32GtS => Some(WasmOp::I32GtS),
        I32GtU => Some(WasmOp::I32GtU),
        I32GeS => Some(WasmOp::I32GeS),
        I32GeU => Some(WasmOp::I32GeU),

        // Memory
        I32Load { memarg } => Some(WasmOp::I32Load {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I32Store { memarg } => Some(WasmOp::I32Store {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        // #372: full-width i64 load/store. The selector already lowers these to
        // a lo/hi i32 register-pair access (`generate_i64_load/store_with_bounds_check`,
        // reusing the #171 pair regalloc) — only the decoder arm was missing, so
        // `i64.load`/`i64.store` fell through `_ => None` and (since v0.11.46)
        // loud-skipped their function. The narrow forms (I64Load8.. / I64Store32)
        // were already decoded below.
        I64Load { memarg } => Some(WasmOp::I64Load {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Store { memarg } => Some(WasmOp::I64Store {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),

        // Sub-word loads (i32)
        I32Load8S { memarg } => Some(WasmOp::I32Load8S {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I32Load8U { memarg } => Some(WasmOp::I32Load8U {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I32Load16S { memarg } => Some(WasmOp::I32Load16S {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I32Load16U { memarg } => Some(WasmOp::I32Load16U {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),

        // Sub-word stores (i32)
        I32Store8 { memarg } => Some(WasmOp::I32Store8 {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I32Store16 { memarg } => Some(WasmOp::I32Store16 {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),

        // Local/Global
        LocalGet { local_index } => Some(WasmOp::LocalGet(*local_index)),
        LocalSet { local_index } => Some(WasmOp::LocalSet(*local_index)),
        LocalTee { local_index } => Some(WasmOp::LocalTee(*local_index)),
        GlobalGet { global_index } => Some(WasmOp::GlobalGet(*global_index)),
        GlobalSet { global_index } => Some(WasmOp::GlobalSet(*global_index)),

        // Control flow
        Block { .. } => Some(WasmOp::Block),
        Loop { .. } => Some(WasmOp::Loop),
        Br { relative_depth } => Some(WasmOp::Br(*relative_depth)),
        BrIf { relative_depth } => Some(WasmOp::BrIf(*relative_depth)),
        // br_table: indexed multi-way branch. Previously UNMAPPED → silently
        // dropped, so the selector never emitted the index dispatch and control
        // fell straight into the first table arm — every br_table behaved as if
        // it always took target 0 (gale's binary-sem WAKE path never fired). The
        // jump-table relative depths + default depth are preserved in order.
        BrTable { targets } => {
            let default = targets.default();
            let tgts: Vec<u32> = targets.targets().filter_map(Result::ok).collect();
            Some(WasmOp::BrTable {
                targets: tgts,
                default,
            })
        }
        Return => Some(WasmOp::Return),
        Call { function_index } => Some(WasmOp::Call(*function_index)),
        CallIndirect {
            type_index,
            table_index,
            ..
        } => Some(WasmOp::CallIndirect {
            type_index: *type_index,
            table_index: *table_index,
        }),

        // End is needed for control flow pattern matching
        End => Some(WasmOp::End),

        // #665: `unreachable` MUST reach the backends — WASM Core §4.4.5
        // requires it to trap unconditionally. It was previously dropped here
        // (treated like Nop), so every backend compiled it to a no-op and
        // control FELL THROUGH panic!/abort/unreachable-default guards with
        // undefined register state. The selector arms (ARM: UDF #0, RV32:
        // ebreak) already existed; they just never received the op.
        Unreachable => Some(WasmOp::Unreachable),

        // Nop - skip (genuinely no semantics)
        Nop => None,

        // Drop is needed for br_if pattern matching
        Drop => Some(WasmOp::Drop),

        // Select
        Select => Some(WasmOp::Select),

        // If/Else - simplified handling
        If { .. } => Some(WasmOp::If),
        Else => Some(WasmOp::Else),

        // i64 sub-word loads
        I64Load8S { memarg } => Some(WasmOp::I64Load8S {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Load8U { memarg } => Some(WasmOp::I64Load8U {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Load16S { memarg } => Some(WasmOp::I64Load16S {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Load16U { memarg } => Some(WasmOp::I64Load16U {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Load32S { memarg } => Some(WasmOp::I64Load32S {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Load32U { memarg } => Some(WasmOp::I64Load32U {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),

        // i64 sub-word stores
        I64Store8 { memarg } => Some(WasmOp::I64Store8 {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Store16 { memarg } => Some(WasmOp::I64Store16 {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        I64Store32 { memarg } => Some(WasmOp::I64Store32 {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),

        // Memory management
        MemorySize { mem, .. } => Some(WasmOp::MemorySize(*mem)),
        MemoryGrow { mem, .. } => Some(WasmOp::MemoryGrow(*mem)),

        // Bulk memory (#374). The backend supports a single linear memory
        // (memory 0); any non-zero memory index falls through to `_ => None` and
        // loud-skips the function (GI-FPU-001 honesty contract) rather than
        // miscompiling a multi-memory copy. memory.copy reads dst/src memories;
        // memory.fill one. The selector lowers these to a bounds-checked byte
        // loop (see select_with_stack).
        MemoryCopy {
            dst_mem: 0,
            src_mem: 0,
        } => Some(WasmOp::MemoryCopy),
        MemoryFill { mem: 0 } => Some(WasmOp::MemoryFill),

        // ========================================================================
        // v128 SIMD operations (WASM SIMD proposal, 0xFD prefix)
        // ========================================================================
        V128Const { value } => {
            let mut bytes = [0u8; 16];
            bytes.copy_from_slice(value.bytes());
            Some(WasmOp::V128Const(bytes))
        }
        V128Load { memarg } => Some(WasmOp::V128Load {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        V128Store { memarg } => Some(WasmOp::V128Store {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),

        // v128 bitwise
        V128And => Some(WasmOp::V128And),
        V128Or => Some(WasmOp::V128Or),
        V128Xor => Some(WasmOp::V128Xor),
        V128Not => Some(WasmOp::V128Not),
        V128AndNot => Some(WasmOp::V128AndNot),

        // i8x16
        I8x16Add => Some(WasmOp::I8x16Add),
        I8x16Sub => Some(WasmOp::I8x16Sub),
        I8x16Neg => Some(WasmOp::I8x16Neg),
        I8x16Eq => Some(WasmOp::I8x16Eq),
        I8x16Ne => Some(WasmOp::I8x16Ne),
        I8x16LtS => Some(WasmOp::I8x16LtS),
        I8x16LtU => Some(WasmOp::I8x16LtU),
        I8x16GtS => Some(WasmOp::I8x16GtS),
        I8x16GtU => Some(WasmOp::I8x16GtU),
        I8x16LeS => Some(WasmOp::I8x16LeS),
        I8x16LeU => Some(WasmOp::I8x16LeU),
        I8x16GeS => Some(WasmOp::I8x16GeS),
        I8x16GeU => Some(WasmOp::I8x16GeU),
        I8x16Splat => Some(WasmOp::I8x16Splat),
        I8x16ExtractLaneS { lane } => Some(WasmOp::I8x16ExtractLaneS(*lane)),
        I8x16ExtractLaneU { lane } => Some(WasmOp::I8x16ExtractLaneU(*lane)),
        I8x16ReplaceLane { lane } => Some(WasmOp::I8x16ReplaceLane(*lane)),
        I8x16Shuffle { lanes } => Some(WasmOp::I8x16Shuffle(*lanes)),
        I8x16Swizzle => Some(WasmOp::I8x16Swizzle),

        // i16x8
        I16x8Add => Some(WasmOp::I16x8Add),
        I16x8Sub => Some(WasmOp::I16x8Sub),
        I16x8Mul => Some(WasmOp::I16x8Mul),
        I16x8Neg => Some(WasmOp::I16x8Neg),
        I16x8Eq => Some(WasmOp::I16x8Eq),
        I16x8Ne => Some(WasmOp::I16x8Ne),
        I16x8LtS => Some(WasmOp::I16x8LtS),
        I16x8LtU => Some(WasmOp::I16x8LtU),
        I16x8GtS => Some(WasmOp::I16x8GtS),
        I16x8GtU => Some(WasmOp::I16x8GtU),
        I16x8LeS => Some(WasmOp::I16x8LeS),
        I16x8LeU => Some(WasmOp::I16x8LeU),
        I16x8GeS => Some(WasmOp::I16x8GeS),
        I16x8GeU => Some(WasmOp::I16x8GeU),
        I16x8Splat => Some(WasmOp::I16x8Splat),
        I16x8ExtractLaneS { lane } => Some(WasmOp::I16x8ExtractLaneS(*lane)),
        I16x8ExtractLaneU { lane } => Some(WasmOp::I16x8ExtractLaneU(*lane)),
        I16x8ReplaceLane { lane } => Some(WasmOp::I16x8ReplaceLane(*lane)),

        // i32x4
        I32x4Add => Some(WasmOp::I32x4Add),
        I32x4Sub => Some(WasmOp::I32x4Sub),
        I32x4Mul => Some(WasmOp::I32x4Mul),
        I32x4Neg => Some(WasmOp::I32x4Neg),
        I32x4Eq => Some(WasmOp::I32x4Eq),
        I32x4Ne => Some(WasmOp::I32x4Ne),
        I32x4LtS => Some(WasmOp::I32x4LtS),
        I32x4LtU => Some(WasmOp::I32x4LtU),
        I32x4GtS => Some(WasmOp::I32x4GtS),
        I32x4GtU => Some(WasmOp::I32x4GtU),
        I32x4LeS => Some(WasmOp::I32x4LeS),
        I32x4LeU => Some(WasmOp::I32x4LeU),
        I32x4GeS => Some(WasmOp::I32x4GeS),
        I32x4GeU => Some(WasmOp::I32x4GeU),
        I32x4Splat => Some(WasmOp::I32x4Splat),
        I32x4ExtractLane { lane } => Some(WasmOp::I32x4ExtractLane(*lane)),
        I32x4ReplaceLane { lane } => Some(WasmOp::I32x4ReplaceLane(*lane)),

        // i64x2
        I64x2Add => Some(WasmOp::I64x2Add),
        I64x2Sub => Some(WasmOp::I64x2Sub),
        I64x2Mul => Some(WasmOp::I64x2Mul),
        I64x2Neg => Some(WasmOp::I64x2Neg),
        I64x2Eq => Some(WasmOp::I64x2Eq),
        I64x2Ne => Some(WasmOp::I64x2Ne),
        I64x2LtS => Some(WasmOp::I64x2LtS),
        I64x2GtS => Some(WasmOp::I64x2GtS),
        I64x2LeS => Some(WasmOp::I64x2LeS),
        I64x2GeS => Some(WasmOp::I64x2GeS),
        I64x2Splat => Some(WasmOp::I64x2Splat),
        I64x2ExtractLane { lane } => Some(WasmOp::I64x2ExtractLane(*lane)),
        I64x2ReplaceLane { lane } => Some(WasmOp::I64x2ReplaceLane(*lane)),

        // === Scalar f32 (GI-FPU-002 phase 1, #619/#369) ===
        // Un-dropped so the FPU targets (cortex-m4f/m7/m7dp) can route these to
        // the VFP selector arms in `select_with_stack`. The FPU gate lives at
        // the selector/validate layer (`requires_fpu()` + `set_target`): on a
        // non-FPU target (m0/m3/r5) these still honest-reject. f64 stays dropped
        // (phase 2 — M7DP D-registers). Only the wired scope is un-dropped; the
        // rest of the scalar f32 surface (abs/neg/sqrt/min/max/…) still falls to
        // `_ => None` and loud-skips its function until phase 1b wires it.
        F32Add => Some(WasmOp::F32Add),
        F32Sub => Some(WasmOp::F32Sub),
        F32Mul => Some(WasmOp::F32Mul),
        F32Div => Some(WasmOp::F32Div),
        F32Eq => Some(WasmOp::F32Eq),
        F32Ne => Some(WasmOp::F32Ne),
        F32Lt => Some(WasmOp::F32Lt),
        F32Le => Some(WasmOp::F32Le),
        F32Gt => Some(WasmOp::F32Gt),
        F32Ge => Some(WasmOp::F32Ge),
        F32Const { value } => Some(WasmOp::F32Const(f32::from_bits(value.bits()))),
        // #708 (phase 1b): `f32.load` un-dropped. The selector lowers it as the
        // proven `i32.load` address sequence (`[R11,idx]`→absolute-base rewrite +
        // bounds guard) into a core register, then a bit-exact `VMOV Sd,Rd`
        // (reinterpret) — a VLDR loads the same 4 bytes, so the bit pattern is
        // identical.
        F32Load { memarg } => Some(WasmOp::F32Load {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        // #719 (phase 1b): `f32.store` — the VFP-store twin of `f32.load`. The
        // selector moves the S-register value into a core register (`VMOV Rn,Sn`,
        // a reinterpret) and reuses the PROVEN `i32.store` address path; a VSTR
        // would write the same 4 bytes, so the stored word is bit-exact. (falcon
        // has 10 f32.store functions, #719.)
        F32Store { memarg } => Some(WasmOp::F32Store {
            offset: memarg.offset as u32,
            align: memarg.align as u32,
        }),
        // #719 (phase 1b): scalar f32 sign-family math — `VABS.F32` / `VNEG.F32`
        // and the `copysign` sign-bit splice. Pure single-precision VFP, no
        // numeric approximation; bit-exact across ±0.0 / NaN-sign / ±inf.
        F32Abs => Some(WasmOp::F32Abs),
        F32Neg => Some(WasmOp::F32Neg),
        F32Copysign => Some(WasmOp::F32Copysign),
        // #708 (phase 1b): the f32<->i32 bit-casts. Pure `VMOV` between a core
        // register and a single-precision S-register — no numeric conversion.
        F32ReinterpretI32 => Some(WasmOp::F32ReinterpretI32),
        I32ReinterpretF32 => Some(WasmOp::I32ReinterpretF32),
        F32ConvertI32S => Some(WasmOp::F32ConvertI32S),
        F32ConvertI32U => Some(WasmOp::F32ConvertI32U),
        I32TruncF32S => Some(WasmOp::I32TruncF32S),
        I32TruncF32U => Some(WasmOp::I32TruncF32U),

        // f32x4
        F32x4Add => Some(WasmOp::F32x4Add),
        F32x4Sub => Some(WasmOp::F32x4Sub),
        F32x4Mul => Some(WasmOp::F32x4Mul),
        F32x4Div => Some(WasmOp::F32x4Div),
        F32x4Abs => Some(WasmOp::F32x4Abs),
        F32x4Neg => Some(WasmOp::F32x4Neg),
        F32x4Sqrt => Some(WasmOp::F32x4Sqrt),
        F32x4Eq => Some(WasmOp::F32x4Eq),
        F32x4Ne => Some(WasmOp::F32x4Ne),
        F32x4Lt => Some(WasmOp::F32x4Lt),
        F32x4Le => Some(WasmOp::F32x4Le),
        F32x4Gt => Some(WasmOp::F32x4Gt),
        F32x4Ge => Some(WasmOp::F32x4Ge),
        F32x4Splat => Some(WasmOp::F32x4Splat),
        F32x4ExtractLane { lane } => Some(WasmOp::F32x4ExtractLane(*lane)),
        F32x4ReplaceLane { lane } => Some(WasmOp::F32x4ReplaceLane(*lane)),

        // Other operators not yet supported
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decode_simple_add() {
        let wat = r#"
            (module
                (func (export "add") (param i32 i32) (result i32)
                    local.get 0
                    local.get 1
                    i32.add
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert_eq!(functions[0].index, 0);
        assert_eq!(functions[0].export_name, Some("add".to_string()));
        assert_eq!(
            functions[0].ops,
            vec![
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32Add,
                WasmOp::End
            ]
        );
    }

    /// #204 regression: `i64.extend_i32_u`, `i64.extend_i32_s` and
    /// `i32.wrap_i64` must DECODE (they were previously unmapped → silently
    /// dropped by `convert_operator`, leaving an i32 value as a 64-bit operand
    /// with a garbage high half — the root cause of gale's miscompiled
    /// `(new_count << 32)` pack). The decoder must surface all three.
    #[test]
    fn test_decode_i64_i32_width_conversions() {
        let wat = r#"
            (module
                (func (export "conv") (param i32 i64) (result i32)
                    local.get 0
                    i64.extend_i32_u
                    local.get 0
                    i64.extend_i32_s
                    i64.add
                    local.get 1
                    i64.add
                    i32.wrap_i64
                )
            )
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let functions = decode_wasm_functions(&wasm).expect("decode");
        let ops = &functions[0].ops;
        assert!(
            ops.contains(&WasmOp::I64ExtendI32U),
            "i64.extend_i32_u must decode (not be dropped): {ops:?}"
        );
        assert!(
            ops.contains(&WasmOp::I64ExtendI32S),
            "i64.extend_i32_s must decode (not be dropped): {ops:?}"
        );
        assert!(
            ops.contains(&WasmOp::I32WrapI64),
            "i32.wrap_i64 must decode (not be dropped): {ops:?}"
        );
    }

    /// #204 WAKE-path regression: `br_table` must DECODE (it was unmapped in
    /// `convert_operator` → silently dropped, so the selector emitted no index
    /// dispatch and every `br_table` fell through to target 0 — gale's binary
    /// semaphore never took its WAKE branch). Targets + default are preserved.
    #[test]
    fn test_decode_br_table() {
        let wat = r#"
            (module
                (func (export "bt") (param i32) (result i32)
                    (block (block (block
                        local.get 0
                        br_table 2 0 1 2)
                      i32.const 30 return)
                      i32.const 20 return)
                    i32.const 10))
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let functions = decode_wasm_functions(&wasm).expect("decode");
        let bt = functions[0]
            .ops
            .iter()
            .find_map(|o| match o {
                WasmOp::BrTable { targets, default } => Some((targets.clone(), *default)),
                _ => None,
            })
            .expect("br_table must decode (not be dropped)");
        assert_eq!(bt.0, vec![2, 0, 1], "br_table targets preserved in order");
        assert_eq!(bt.1, 2, "br_table default preserved");
    }

    #[test]
    fn test_decode_arithmetic() {
        let wat = r#"
            (module
                (func (export "calc") (result i32)
                    i32.const 5
                    i32.const 3
                    i32.mul
                    i32.const 2
                    i32.add
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert_eq!(functions[0].export_name, Some("calc".to_string()));
        assert_eq!(
            functions[0].ops,
            vec![
                WasmOp::I32Const(5),
                WasmOp::I32Const(3),
                WasmOp::I32Mul,
                WasmOp::I32Const(2),
                WasmOp::I32Add,
                WasmOp::End,
            ]
        );
    }

    #[test]
    fn test_decode_multi_function_module() {
        let wat = r#"
            (module
                (func $helper)
                (func (export "add") (param i32 i32) (result i32)
                    local.get 0
                    local.get 1
                    i32.add
                )
                (func (export "sub") (param i32 i32) (result i32)
                    local.get 0
                    local.get 1
                    i32.sub
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 3);
        assert_eq!(functions[0].index, 0);
        assert_eq!(functions[0].export_name, None);
        assert_eq!(functions[1].index, 1);
        assert_eq!(functions[1].export_name, Some("add".to_string()));
        assert_eq!(functions[2].index, 2);
        assert_eq!(functions[2].export_name, Some("sub".to_string()));
    }

    #[test]
    fn test_decode_module_with_imports() {
        let wat = r#"
            (module
                (import "env" "log" (func $log (param i32)))
                (import "env" "memory" (memory 1))
                (func (export "run") (param i32)
                    local.get 0
                    call 0
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let module = decode_wasm_module(&wasm).expect("Failed to decode");

        // Should have 2 imports (1 func, 1 memory)
        assert_eq!(module.imports.len(), 2);
        assert_eq!(module.num_imported_funcs, 1);

        // First import is the function
        assert_eq!(module.imports[0].module, "env");
        assert_eq!(module.imports[0].name, "log");
        assert!(matches!(module.imports[0].kind, ImportKind::Function(_)));

        // Second import is memory
        assert_eq!(module.imports[1].module, "env");
        assert_eq!(module.imports[1].name, "memory");
        assert_eq!(module.imports[1].kind, ImportKind::Memory);

        // Should have 1 local function (index 1, because import is index 0)
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].index, 1);
        assert_eq!(module.functions[0].export_name, Some("run".to_string()));
    }

    #[test]
    fn test_find_function_by_export_name() {
        let wat = r#"
            (module
                (func $helper)
                (func (export "add") (param i32 i32) (result i32)
                    local.get 0
                    local.get 1
                    i32.add
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        let add_func = functions
            .iter()
            .find(|f| f.export_name.as_deref() == Some("add"))
            .expect("Should find 'add' function");

        assert_eq!(add_func.index, 1);
        assert!(add_func.ops.contains(&WasmOp::I32Add));
    }

    #[test]
    fn test_decode_subword_loads() {
        let wat = r#"
            (module
                (memory 1)
                (func (export "test") (param i32) (result i32)
                    local.get 0
                    i32.load8_u
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::I32Load8U {
            offset: 0,
            align: 0,
        }));
    }

    #[test]
    fn test_decode_subword_stores() {
        let wat = r#"
            (module
                (memory 1)
                (func (export "test") (param i32 i32)
                    local.get 0
                    local.get 1
                    i32.store8
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::I32Store8 {
            offset: 0,
            align: 0,
        }));
    }

    #[test]
    fn test_decode_memory_size_grow() {
        let wat = r#"
            (module
                (memory 1)
                (func (export "test") (result i32)
                    memory.size
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::MemorySize(0)));
    }

    #[test]
    fn test_decode_memory_grow() {
        let wat = r#"
            (module
                (memory 1)
                (func (export "test") (param i32) (result i32)
                    local.get 0
                    memory.grow
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::MemoryGrow(0)));
    }

    #[test]
    fn test_decode_bulk_memory_374() {
        // #374: memory.copy / memory.fill on the single linear memory decode to
        // the new WasmOp variants (was `_ => None` -> loud-skip).
        let wat = r#"
            (module
                (memory 1)
                (func (export "cpy") (param i32 i32 i32)
                    local.get 0 local.get 1 local.get 2 memory.copy)
                (func (export "fil") (param i32 i32 i32)
                    local.get 0 local.get 1 local.get 2 memory.fill)
            )
        "#;
        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");
        assert_eq!(functions.len(), 2);
        assert!(functions[0].ops.contains(&WasmOp::MemoryCopy));
        assert!(functions[1].ops.contains(&WasmOp::MemoryFill));
        // Neither function is flagged unsupported (they now lower).
        assert!(functions[0].unsupported.is_none());
        assert!(functions[1].unsupported.is_none());
    }

    #[test]
    fn test_decode_i64_subword_loads() {
        let wat = r#"
            (module
                (memory 1)
                (func (export "test") (param i32) (result i64)
                    local.get 0
                    i64.load8_s
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::I64Load8S {
            offset: 0,
            align: 0,
        }));
    }

    #[test]
    fn test_decode_all_subword_memory_ops() {
        // Test that all sub-word operations are decoded from WAT
        let wat = r#"
            (module
                (memory 1)
                (func (export "test") (param i32)
                    ;; i32 sub-word loads
                    local.get 0
                    i32.load8_s
                    drop
                    local.get 0
                    i32.load8_u
                    drop
                    local.get 0
                    i32.load16_s
                    drop
                    local.get 0
                    i32.load16_u
                    drop

                    ;; i32 sub-word stores
                    local.get 0
                    i32.const 42
                    i32.store8
                    local.get 0
                    i32.const 42
                    i32.store16

                    ;; i64 sub-word loads
                    local.get 0
                    i64.load8_s
                    drop
                    local.get 0
                    i64.load8_u
                    drop
                    local.get 0
                    i64.load16_s
                    drop
                    local.get 0
                    i64.load16_u
                    drop
                    local.get 0
                    i64.load32_s
                    drop
                    local.get 0
                    i64.load32_u
                    drop

                    ;; i64 sub-word stores
                    local.get 0
                    i64.const 42
                    i64.store8
                    local.get 0
                    i64.const 42
                    i64.store16
                    local.get 0
                    i64.const 42
                    i64.store32
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        let ops = &functions[0].ops;

        // Verify i32 sub-word ops are present
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I32Load8S { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I32Load8U { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I32Load16S { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I32Load16U { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I32Store8 { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I32Store16 { .. })));

        // Verify i64 sub-word ops are present
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Load8S { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Load8U { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Load16S { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Load16U { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Load32S { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Load32U { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Store8 { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Store16 { .. })));
        assert!(ops.iter().any(|o| matches!(o, WasmOp::I64Store32 { .. })));
    }

    #[test]
    fn test_decode_simd_i32x4_add() {
        let wat = r#"
            (module
                (func (export "add_v128") (param v128 v128) (result v128)
                    local.get 0
                    local.get 1
                    i32x4.add
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(
            functions[0].ops.contains(&WasmOp::I32x4Add),
            "Should decode i32x4.add: {:?}",
            functions[0].ops
        );
    }

    #[test]
    fn test_decode_simd_v128_const() {
        let wat = r#"
            (module
                (func (export "const_v128") (result v128)
                    v128.const i32x4 1 2 3 4
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(
            functions[0]
                .ops
                .iter()
                .any(|o| matches!(o, WasmOp::V128Const(_))),
            "Should decode v128.const: {:?}",
            functions[0].ops
        );
    }

    #[test]
    fn test_decode_simd_v128_load_store() {
        let wat = r#"
            (module
                (memory 1)
                (func (export "load_store") (param i32)
                    local.get 0
                    v128.load
                    local.get 0
                    v128.store
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        let ops = &functions[0].ops;
        assert!(
            ops.iter().any(|o| matches!(o, WasmOp::V128Load { .. })),
            "Should decode v128.load"
        );
        assert!(
            ops.iter().any(|o| matches!(o, WasmOp::V128Store { .. })),
            "Should decode v128.store"
        );
    }

    #[test]
    fn test_decode_simd_bitwise_ops() {
        let wat = r#"
            (module
                (func (export "bitwise") (param v128 v128) (result v128)
                    local.get 0
                    local.get 1
                    v128.and
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::V128And));
    }

    #[test]
    fn test_decode_simd_splat() {
        let wat = r#"
            (module
                (func (export "splat") (param i32) (result v128)
                    local.get 0
                    i32x4.splat
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::I32x4Splat));
    }

    #[test]
    fn test_decode_simd_extract_lane() {
        let wat = r#"
            (module
                (func (export "extract") (param v128) (result i32)
                    local.get 0
                    i32x4.extract_lane 2
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(
            functions[0].ops.contains(&WasmOp::I32x4ExtractLane(2)),
            "Should decode i32x4.extract_lane 2"
        );
    }

    #[test]
    fn test_decode_simd_f32x4_arithmetic() {
        let wat = r#"
            (module
                (func (export "f32x4_add") (param v128 v128) (result v128)
                    local.get 0
                    local.get 1
                    f32x4.add
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        assert!(functions[0].ops.contains(&WasmOp::F32x4Add));
    }

    #[test]
    fn test_369_scalar_float_op_flags_function_unsupported_not_dropped() {
        // GI-FPU-002 (#619): the in-scope scalar f32 ops (add/sub/mul/div,
        // comparisons, i32.trunc_f32_s/u, f32.convert_i32_s/u, f32.const) are
        // now DECODED (routed to the VFP selector on FPU targets), so `f32.add`
        // is no longer flagged. An out-of-scope scalar float op (`f64.add`,
        // phase 2) is STILL flagged (loud-skip), never silently dropped — the
        // #369 honesty contract holds for the not-yet-lowered surface. A
        // pure-integer function stays clean.
        let wat = r#"
            (module
                (func (export "fadd") (param f32 f32) (result f32)
                    local.get 0 local.get 1 f32.add)
                (func (export "dadd") (param f64 f64) (result f64)
                    local.get 0 local.get 1 f64.add)
                (func (export "iadd") (param i32 i32) (result i32)
                    local.get 0 local.get 1 i32.add))
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let functions = decode_wasm_functions(&wasm).expect("decode");
        let fadd = functions
            .iter()
            .find(|f| f.export_name.as_deref() == Some("fadd"))
            .unwrap();
        let dadd = functions
            .iter()
            .find(|f| f.export_name.as_deref() == Some("dadd"))
            .unwrap();
        let iadd = functions
            .iter()
            .find(|f| f.export_name.as_deref() == Some("iadd"))
            .unwrap();
        // In-scope f32 op: now decoded (reachable), not flagged.
        assert!(
            fadd.unsupported.is_none(),
            "GI-FPU-002: f32.add must now decode (not be flagged), got {:?}",
            fadd.unsupported
        );
        assert!(
            fadd.ops.contains(&WasmOp::F32Add),
            "f32.add must decode to WasmOp::F32Add: {:?}",
            fadd.ops
        );
        // Out-of-scope scalar double op: still flagged (phase 2), never dropped.
        assert!(
            dadd.unsupported.is_some(),
            "f64.add must still flag the function unsupported (phase 2), got {:?}",
            dadd.unsupported
        );
        assert!(
            iadd.unsupported.is_none(),
            "a pure-integer function must NOT be flagged: {:?}",
            iadd.unsupported
        );
    }

    #[test]
    fn test_369_float_global_access_flags_function_unsupported() {
        // GI-FPU-001 (#369): `global.get`/`global.set` on an f32/f64-typed
        // global decode fine (the ops are type-agnostic), but the float
        // initializer is dropped (`init_i32: None` -> slot zeroed), so a read
        // returned a silently-wrong 0.0 instead of the init (verified: the
        // 2.5f bit pattern 0x40200000 was absent from the output ELF). The
        // access must flag the function for the loud-skip path. Accesses to
        // integer globals stay clean.
        let wat = r#"
            (module
                (global $fg f32 (f32.const 2.5))
                (global $dg (mut f64) (f64.const 1.5))
                (global $ig (mut i32) (i32.const 7))
                (func (export "fget") (result f32) global.get $fg)
                (func (export "dset") (param f64) local.get 0 global.set $dg)
                (func (export "iget") (result i32) global.get $ig))
        "#;
        let wasm = wat::parse_str(wat).expect("parse");

        // Both decode entry points must flag (the CLI compiles through both:
        // decode_wasm_module on the all-exports/module paths,
        // decode_wasm_functions on the single-function path).
        let module = decode_wasm_module(&wasm).expect("decode module");
        for functions in [
            &module.functions,
            &decode_wasm_functions(&wasm).expect("decode fns"),
        ] {
            let by_name = |n: &str| {
                functions
                    .iter()
                    .find(|f| f.export_name.as_deref() == Some(n))
                    .unwrap()
            };
            let fget = by_name("fget");
            assert!(
                fget.unsupported.is_some(),
                "global.get of an f32 global must flag the function (loud-skip), got {:?}",
                fget.unsupported
            );
            let reason = fget.unsupported.as_deref().unwrap();
            assert!(
                reason.contains("GlobalGet") && reason.contains("GI-FPU-001"),
                "diagnostic should name the op and GI-FPU-001: {reason:?}"
            );
            let dset = by_name("dset");
            assert!(
                dset.unsupported
                    .as_deref()
                    .is_some_and(|r| r.contains("GlobalSet")),
                "global.set of an f64 global must flag the function, got {:?}",
                dset.unsupported
            );
            assert!(
                by_name("iget").unsupported.is_none(),
                "an i32 global access must NOT be flagged: {:?}",
                by_name("iget").unsupported
            );
        }
    }

    #[test]
    fn test_369_imported_float_global_shifts_index_space() {
        // GI-FPU-001 (#369): imported globals come FIRST in the global index
        // space. An imported f64 global at index 0 must be flagged, and the
        // defined i32 global at index 1 must NOT be mistaken for it.
        let wat = r#"
            (module
                (import "env" "fg" (global f64))
                (global $ig i32 (i32.const 3))
                (func (export "fget") (result f64) global.get 0)
                (func (export "iget") (result i32) global.get 1))
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let functions = decode_wasm_functions(&wasm).expect("decode");
        let by_name = |n: &str| {
            functions
                .iter()
                .find(|f| f.export_name.as_deref() == Some(n))
                .unwrap()
        };
        assert!(
            by_name("fget")
                .unsupported
                .as_deref()
                .is_some_and(|r| r.contains("GI-FPU-001")),
            "imported f64 global access must flag: {:?}",
            by_name("fget").unsupported
        );
        assert!(
            by_name("iget").unsupported.is_none(),
            "defined i32 global at shifted index 1 must NOT flag: {:?}",
            by_name("iget").unsupported
        );
    }

    #[test]
    fn test_680_simd_ops_flag_function_unsupported_not_dropped() {
        // #680: SIMD (v128) ops decode into WasmOp variants no production
        // target can select (`has_helium` is test-only), so they were silently
        // dropped at selection — `i32x4.add` compiled to an operand
        // passthrough (`mov r0,r1`) and shipped a wrong result. The issue's
        // exact reproducer must flag the function; the scalar sibling must
        // stay compilable (non-vacuity).
        let wat = r#"
            (module
                (memory 1)
                (func (export "vadd") (param i32 i32) (result i32)
                    (i32x4.extract_lane 2
                        (i32x4.add (i32x4.splat (local.get 0))
                                   (i32x4.splat (local.get 1)))))
                (func (export "vstore") (param i32 i32) (result i32)
                    (v128.store (i32.const 0) (i32x4.splat (local.get 0)))
                    (i32.load (i32.const 0)))
                (func (export "iadd") (param i32 i32) (result i32)
                    local.get 0 local.get 1 i32.add))
        "#;
        let wasm = wat::parse_str(wat).expect("parse");

        // Both decode entry points must flag (the CLI compiles through both).
        let module = decode_wasm_module(&wasm).expect("decode module");
        for functions in [
            &module.functions,
            &decode_wasm_functions(&wasm).expect("decode fns"),
        ] {
            let by_name = |n: &str| {
                functions
                    .iter()
                    .find(|f| f.export_name.as_deref() == Some(n))
                    .unwrap()
            };
            for name in ["vadd", "vstore"] {
                let reason = by_name(name).unsupported.as_deref();
                assert!(
                    reason.is_some(),
                    "{name}: v128 ops must flag the function (loud-skip), got None"
                );
                let reason = reason.unwrap();
                assert!(
                    reason.contains("no SIMD lowering for this target") && reason.contains("#680"),
                    "{name}: diagnostic must name the target gap and #680: {reason:?}"
                );
            }
            // The reason names the FIRST SIMD op hit (splat in both bodies).
            assert!(
                by_name("vadd")
                    .unsupported
                    .as_deref()
                    .unwrap()
                    .contains("I32x4Splat"),
                "diagnostic should name the op: {:?}",
                by_name("vadd").unsupported
            );
            assert!(
                by_name("iadd").unsupported.is_none(),
                "a scalar function in the same module must NOT be flagged: {:?}",
                by_name("iadd").unsupported
            );
        }
    }

    #[test]
    fn test_680_v128_local_and_signature_flag_function() {
        // #680: v128 VALUES are expressible with ZERO SIMD-proposal operators
        // in the body — a v128-typed local or a v128 param/result is reached
        // through type-agnostic `local.get`/`local.set`, which the selectors
        // lower as 4-byte moves (silent 16-byte truncation). Both must flag.
        let wat = r#"
            (module
                (func (export "vlocal") (result i32) (local v128)
                    i32.const 7)
                (func (export "vpass") (param v128) (result v128)
                    local.get 0)
                (func (export "scalar") (param i32) (result i32)
                    local.get 0))
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let module = decode_wasm_module(&wasm).expect("decode module");
        for functions in [
            &module.functions,
            &decode_wasm_functions(&wasm).expect("decode fns"),
        ] {
            let by_name = |n: &str| {
                functions
                    .iter()
                    .find(|f| f.export_name.as_deref() == Some(n))
                    .unwrap()
            };
            assert!(
                by_name("vlocal")
                    .unsupported
                    .as_deref()
                    .is_some_and(|r| r.contains("v128-typed local") && r.contains("#680")),
                "a v128-typed local declaration must flag: {:?}",
                by_name("vlocal").unsupported
            );
            assert!(
                by_name("vpass")
                    .unsupported
                    .as_deref()
                    .is_some_and(|r| r.contains("v128 param/result") && r.contains("#680")),
                "a v128 param/result signature must flag (op-free body!): {:?}",
                by_name("vpass").unsupported
            );
            assert!(
                by_name("scalar").unsupported.is_none(),
                "a scalar function must NOT be flagged: {:?}",
                by_name("scalar").unsupported
            );
        }
    }

    #[test]
    fn test_680_v128_global_access_flags_function() {
        // #680: `global.get`/`global.set` on a v128-typed global decode fine
        // (type-agnostic ops), but the access would move 4 of the 16 bytes and
        // the `v128.const` initializer is never captured. Same lane as the
        // float globals (#648/GI-FPU-001); imported globals shift the index
        // space (imports first). The i32-global sibling stays compilable.
        let wat = r#"
            (module
                (import "env" "vg" (global v128))
                (global $ig (mut i32) (i32.const 7))
                (global $dg (mut v128) (v128.const i32x4 1 2 3 4))
                (func (export "vget") global.get 0 drop)
                (func (export "iget") (result i32) global.get $ig))
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let module = decode_wasm_module(&wasm).expect("decode module");
        for functions in [
            &module.functions,
            &decode_wasm_functions(&wasm).expect("decode fns"),
        ] {
            let by_name = |n: &str| {
                functions
                    .iter()
                    .find(|f| f.export_name.as_deref() == Some(n))
                    .unwrap()
            };
            let reason = by_name("vget").unsupported.as_deref();
            assert!(
                reason.is_some_and(|r| r.contains("GlobalGet")
                    && r.contains("v128-typed global")
                    && r.contains("#680")),
                "global.get of an imported v128 global must flag: {reason:?}"
            );
            assert!(
                by_name("iget").unsupported.is_none(),
                "an i32 global access must NOT be flagged: {:?}",
                by_name("iget").unsupported
            );
        }
    }

    #[test]
    fn test_decode_simd_multiple_ops() {
        let wat = r#"
            (module
                (func (export "simd_ops") (param v128 v128 v128) (result v128)
                    ;; (a + b) * c
                    local.get 0
                    local.get 1
                    i32x4.add
                    local.get 2
                    i32x4.mul
                )
            )
        "#;

        let wasm = wat::parse_str(wat).expect("Failed to parse WAT with SIMD");
        let functions = decode_wasm_functions(&wasm).expect("Failed to decode");

        assert_eq!(functions.len(), 1);
        let ops = &functions[0].ops;
        assert!(ops.contains(&WasmOp::I32x4Add));
        assert!(ops.contains(&WasmOp::I32x4Mul));
    }

    /// VCR-DBG-001 step 1 (#394): the decoder records a module-relative wasm byte
    /// offset per emitted op — the DWARF-for-wasm address space that bridges
    /// synth's op-index `source_line` to the input wasm's `.debug_line`. Purely
    /// additive metadata (no codegen consumer ⇒ frozen fixtures byte-identical,
    /// verified separately); this test pins the structural invariants.
    #[test]
    fn test_decode_records_aligned_increasing_op_offsets_dbg001() {
        let wat = r#"
            (module
                (func (export "f") (param i32 i32) (result i32)
                    local.get 0
                    local.get 1
                    i32.add
                    i32.const 7
                    i32.mul))
        "#;
        let wasm = wat::parse_str(wat).expect("parse WAT");
        let functions = decode_wasm_functions(&wasm).expect("decode");
        let f = &functions[0];

        // One offset per emitted op, index-aligned with `ops`.
        assert_eq!(
            f.op_offsets.len(),
            f.ops.len(),
            "op_offsets must be parallel to ops"
        );
        assert!(!f.op_offsets.is_empty());

        // Byte offsets are strictly increasing through the body (each op consumes
        // at least one byte) and module-relative (well past the header).
        assert!(
            f.op_offsets.windows(2).all(|w| w[1] > w[0]),
            "wasm byte offsets must strictly increase: {:?}",
            f.op_offsets
        );
        assert!(
            f.op_offsets[0] >= 8,
            "module-relative offset is past the 8-byte wasm header"
        );
    }

    /// #237: the decoder captures a global's `i32.const` initializer + mutability,
    /// so the native-pointer ABI can recognize the stack-pointer global.
    #[test]
    fn test_decode_captures_global_initializer() {
        let wat = r#"
            (module
                (memory 2)
                (global $__stack_pointer (mut i32) (i32.const 65536))
                (global $immutable_const i32 (i32.const 7))
                (func (export "f") (result i32) global.get 0)
            )
        "#;
        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let module = decode_wasm_module(&wasm).expect("Failed to decode");

        assert_eq!(module.globals.len(), 2, "both globals captured");
        let sp = &module.globals[0];
        assert_eq!(sp.index, 0);
        assert_eq!(
            sp.init,
            Some(GlobalInit::I32(65536)),
            "stack-pointer init captured"
        );
        assert!(sp.mutable, "stack pointer is mutable");
        let c = &module.globals[1];
        assert_eq!(c.init, Some(GlobalInit::I32(7)));
        assert!(!c.mutable, "second global is immutable");
        assert_eq!(sp.slot_bytes, 4, "i32 global occupies one 4-byte slot");
        assert_eq!(c.slot_bytes, 4);
    }

    /// #643: the decoder records the DECLARED slot width per global — an i64
    /// (or f64) global occupies 8 bytes, so the globals-table layout can give
    /// it room for both words and shift every later global's offset.
    #[test]
    fn test_decode_records_global_slot_widths_643() {
        let wat = r#"
            (module
                (global $c (mut i64) (i64.const 0))
                (global $k (mut i32) (i32.const 0))
                (global $f (mut f64) (f64.const 0))
                (func (export "f") (result i32) global.get 1)
            )
        "#;
        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let module = decode_wasm_module(&wasm).expect("Failed to decode");

        assert_eq!(module.globals.len(), 3);
        assert_eq!(module.globals[0].slot_bytes, 8, "i64 global is 8 bytes");
        assert_eq!(module.globals[1].slot_bytes, 4, "i32 global is 4 bytes");
        assert_eq!(module.globals[2].slot_bytes, 8, "f64 global is 8 bytes");
    }

    /// #649: a nonzero `i64.const` initializer is captured as BOTH words — the
    /// `init_i32`-shaped capture dropped it to `None` and every consumer's
    /// `unwrap_or(0)` silently ZEROED the global. f32/f64 inits stay `None`
    /// (GI-FPU-001/#369 loud-skip lane — never fabricate a float bit-pattern).
    #[test]
    fn test_decode_captures_i64_global_initializer_649() {
        let wat = r#"
            (module
                (global $g (mut i64) (i64.const 0x123456789ABCDEF0))
                (global $n (mut i64) (i64.const -1))
                (global $f (mut f64) (f64.const 1.5))
                (global $h (mut f32) (f32.const 2.5))
                (func (export "f") (result i32) i32.const 0)
            )
        "#;
        let wasm = wat::parse_str(wat).expect("Failed to parse WAT");
        let module = decode_wasm_module(&wasm).expect("Failed to decode");

        assert_eq!(module.globals.len(), 4);
        assert_eq!(
            module.globals[0].init,
            Some(GlobalInit::I64(0x123456789ABCDEF0u64 as i64)),
            "nonzero i64 init captured with both words"
        );
        assert_eq!(module.globals[1].init, Some(GlobalInit::I64(-1)));
        assert_eq!(
            module.globals[2].init, None,
            "f64 init is NOT captured (GI-FPU-001 loud-skip lane)"
        );
        assert_eq!(
            module.globals[3].init, None,
            "f32 init is NOT captured (GI-FPU-001 loud-skip lane)"
        );
    }

    /// #509: the decoder records `(param_count, result_count)` for every
    /// `Block`/`Loop`/`If`, ordinal-keyed in op order, covering all three
    /// blocktype encodings: `Empty → (0,0)`, `ValType → (0,1)`, and
    /// `FuncType(i) →` counts from the type section (here a multi-result
    /// block, which wat encodes as a functype blocktype).
    #[test]
    fn test_decode_records_block_arity_side_table_509() {
        let wat = r#"
            (module
                (func (export "f") (param i32) (result i32)
                    (block (result i32)
                        (block (nop))
                        (local.get 0)
                        (if (result i32)
                            (then (i32.const 1))
                            (else (i32.const 2)))))
                (func (export "g") (result i32)
                    (block (result i32 i32)
                        (i32.const 1) (i32.const 2))
                    i32.add)
                (func (export "h") (param i32) (result i32)
                    (local.get 0)
                    (loop (param i32) (result i32))))
        "#;
        let wasm = wat::parse_str(wat).expect("parse WAT");

        // Both decode entry points must produce the same side-table.
        for functions in [
            decode_wasm_functions(&wasm).expect("decode"),
            decode_wasm_module(&wasm).expect("decode").functions,
        ] {
            // f: Block(result i32), Block(void), If(result i32) — in op order.
            assert_eq!(
                functions[0].block_arity,
                vec![(0, 1), (0, 0), (0, 1)],
                "f: ValType/Empty/ValType blocktypes"
            );
            // g: one multi-result block via a FuncType blocktype.
            assert_eq!(
                functions[1].block_arity,
                vec![(0, 2)],
                "g: functype blocktype result count from the type section"
            );
            // h: a parameterized loop — the input arity is what a br to the
            // header would carry (the #509 loud-decline discriminator).
            assert_eq!(
                functions[2].block_arity,
                vec![(1, 1)],
                "h: loop params captured"
            );
        }
    }

    /// #642: the decoder captures table 0's compile-time size, per-segment
    /// element shapes and per-function type indices, and the closed-world
    /// verdict VERIFIES a fully-covered homogeneous table.
    #[test]
    fn test_call_indirect_guards_closed_world_verified_642() {
        // The #642 repro shape: 3-entry table, fully covered, one signature.
        let wat = r#"
            (module
                (type $bin (func (param i32 i32) (result i32)))
                (table 3 funcref)
                (elem (i32.const 0) $add $sub $mul)
                (func $add (param i32 i32) (result i32)
                    (i32.add (local.get 0) (local.get 1)))
                (func $sub (param i32 i32) (result i32)
                    (i32.sub (local.get 0) (local.get 1)))
                (func $mul (param i32 i32) (result i32)
                    (i32.mul (local.get 0) (local.get 1)))
                (func (export "f") (param i32 i32) (result i32)
                    (call_indirect (type $bin)
                        (local.get 0) (i32.const 10) (local.get 1)))
            )
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let module = decode_wasm_module(&wasm).expect("decode");

        assert_eq!(module.table_size, Some(3), "table section min size");
        assert_eq!(module.table_sizes, vec![Some(3)], "#650 per-table sizes");
        assert_eq!(
            module.elem_segments,
            vec![ElemSegmentInfo {
                table_index: 0,
                offset: Some(0),
                funcs: Some(vec![0, 1, 2]),
            }]
        );
        // 2 type-section entries ($bin + the export's (i32 i32)->i32 dedups
        // to one in practice, but don't assume — just check func 0..2 share
        // a signature with type 0).
        assert_eq!(module.func_type_indices.len(), 4);

        let guards = module.call_indirect_guards();
        assert_eq!(guards.tables.len(), 1);
        assert_eq!(guards.tables[0].table_size, Some(3));
        assert_eq!(
            guards.tables[0].base_byte_offset,
            Some(0),
            "#650: a single-table module keeps table 0 at R11 offset 0 by construction"
        );
        // Type index 0 ($bin) must be VERIFIED: every table entry has its
        // exact signature.
        assert_eq!(
            guards.tables[0].type_reject.first(),
            Some(&None),
            "closed-world type check must verify the homogeneous table: {:?}",
            guards.tables[0].type_reject
        );
        assert!(
            !guards.tables[0].has_null_slots,
            "#664: a fully-initialized table must NOT request the runtime \
             null check (dispatch bytes stay identical by construction)"
        );
    }

    /// #642: a heterogeneous table (an entry whose signature differs from the
    /// expected type) must REJECT that expected type — the raw code-pointer
    /// table cannot be runtime-type-checked, so the lowering has to decline.
    #[test]
    fn test_call_indirect_guards_heterogeneous_table_rejects_642() {
        let wat = r#"
            (module
                (type $bin (func (param i32 i32) (result i32)))
                (type $un (func (param i32) (result i32)))
                (table 2 funcref)
                (elem (i32.const 0) $add $neg)
                (func $add (type $bin)
                    (i32.add (local.get 0) (local.get 1)))
                (func $neg (type $un)
                    (i32.sub (i32.const 0) (local.get 0)))
                (func (export "f") (param i32 i32) (result i32)
                    (call_indirect (type $bin)
                        (local.get 0) (i32.const 10) (local.get 1)))
            )
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let module = decode_wasm_module(&wasm).expect("decode");
        let guards = module.call_indirect_guards();
        assert_eq!(guards.tables[0].table_size, Some(2));
        // BOTH expected types must be rejected: the table holds one function
        // of each signature, so neither type's closed world holds.
        assert!(
            guards.tables[0].type_reject[0].is_some() && guards.tables[0].type_reject[1].is_some(),
            "heterogeneous table must reject every expected type: {:?}",
            guards.tables[0].type_reject
        );
        // #676: ... but the image is statically known, so the mismatch trap
        // is dischargeable at RUNTIME via the type-id sidecar.
        assert!(
            guards.tables[0].runtime_type_check,
            "heterogeneous-but-known table must offer the runtime check (#676)"
        );
        assert_eq!(
            guards.type_ids_byte_offset,
            Some(8),
            "sidecar sits after the 2-slot pointer region"
        );
        assert_eq!(
            guards.type_ids_image,
            vec![1, 2],
            "slot 0 = $bin (class 1), slot 1 = $un (class 2)"
        );
        assert_eq!(guards.type_class_ids, vec![1, 2]);
    }

    /// #664 (relaxes the #642 all-reject): an uninitialized table slot (elem
    /// covers less than the declared size) is a null funcref — calling it
    /// must trap, which is now discharged at RUNTIME (null check on the
    /// zero-linked pointer), so the closed-world verdict verifies the
    /// INITIALIZED slots and sets `has_null_slots` for the lowering.
    #[test]
    fn test_call_indirect_guards_null_slot_verifies_with_flag_664() {
        let wat = r#"
            (module
                (type $s (func (result i32)))
                (table 3 funcref)
                (elem (i32.const 0) $f0 $f1)
                (func $f0 (result i32) (i32.const 10))
                (func $f1 (result i32) (i32.const 11))
                (func (export "run") (param i32) (result i32)
                    (call_indirect (type $s) (local.get 0)))
            )
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let module = decode_wasm_module(&wasm).expect("decode");
        let guards = module.call_indirect_guards();
        assert_eq!(guards.tables[0].table_size, Some(3));
        assert_eq!(
            guards.tables[0].type_reject.first(),
            Some(&None),
            "initialized slots are homogeneous in $s — the verdict must \
             verify despite the null slot (#664): {:?}",
            guards.tables[0].type_reject
        );
        assert!(
            guards.tables[0].has_null_slots,
            "slot 2 is uninitialized — the lowering must emit the runtime \
             null check (#664)"
        );
    }

    /// #664: the falcon shape — a SPARSE table (only slots 1 and 3 of 4
    /// initialized, by two separate segments) verifies with the null flag;
    /// a sparse table whose INITIALIZED slots are heterogeneous still
    /// rejects (the runtime null check cannot discharge a TYPE mismatch).
    #[test]
    fn test_call_indirect_guards_sparse_table_664() {
        let wat = r#"
            (module
                (type $t (func (param i32) (result i32)))
                (table 4 4 funcref)
                (func $f1 (type $t) (i32.add (local.get 0) (i32.const 100)))
                (func $f3 (type $t) (i32.sub (i32.const 1000) (local.get 0)))
                (elem (i32.const 1) $f1)
                (elem (i32.const 3) $f3)
                (func (export "via") (param i32 i32) (result i32)
                    (call_indirect (type $t) (local.get 0) (local.get 1)))
            )
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let module = decode_wasm_module(&wasm).expect("decode");
        let guards = module.call_indirect_guards();
        assert_eq!(guards.tables[0].table_size, Some(4));
        assert_eq!(
            guards.tables[0].type_reject.first(),
            Some(&None),
            "slots 1,3 are homogeneous in $t — verified: {:?}",
            guards.tables[0].type_reject
        );
        assert!(guards.tables[0].has_null_slots, "slots 0,2 are null");

        // Heterogeneous INITIALIZED slots in a sparse table: still rejected.
        let wat = r#"
            (module
                (type $t (func (param i32) (result i32)))
                (type $u (func (param i32 i32) (result i32)))
                (table 4 4 funcref)
                (func $f1 (type $t) (local.get 0))
                (func $f3 (type $u) (i32.add (local.get 0) (local.get 1)))
                (elem (i32.const 1) $f1)
                (elem (i32.const 3) $f3)
                (func (export "via") (param i32 i32) (result i32)
                    (call_indirect (type $t) (local.get 0) (local.get 1)))
            )
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let module = decode_wasm_module(&wasm).expect("decode");
        let guards = module.call_indirect_guards();
        assert!(
            guards.tables[0].type_reject[0].is_some() && guards.tables[0].type_reject[1].is_some(),
            "a heterogeneous sparse table must still reject every type: {:?}",
            guards.tables[0].type_reject
        );
        // #676: the sparse-heterogeneous case is now dischargeable at
        // runtime too — null slots take the reserved class id 0, so ONE
        // sidecar compare covers both the type mismatch and the null trap.
        assert!(guards.tables[0].runtime_type_check, "#676 runtime check");
        assert_eq!(guards.type_ids_byte_offset, Some(16), "4 pointer slots");
        assert_eq!(
            guards.type_ids_image,
            vec![0, 1, 0, 2],
            "nulls at 0/2 carry the reserved id 0; $t slot 1 = class 1, \
             $u slot 3 = class 2"
        );
    }

    /// #676: the heterogeneous type-id sidecar — structural duplicate types
    /// share one class id (the meld 31-decls/25-distinct shape), null slots
    /// take the reserved id 0, and the sidecar base is the total pointer
    /// region size. A module with NO heterogeneous table gets NO sidecar
    /// (empty image, `None` offset) — homogeneous modules stay untouched.
    #[test]
    fn test_call_indirect_guards_heterogeneous_sidecar_676() {
        let wat = r#"
            (module
                (type $bin (func (param i32 i32) (result i32)))
                (type $un (func (param i32) (result i32)))
                (type $bin2 (func (param i32 i32) (result i32)))
                (table 5 5 funcref)
                (func $add (type $bin) (i32.add (local.get 0) (local.get 1)))
                (func $neg (type $un) (i32.sub (i32.const 0) (local.get 0)))
                (func $sub (type $bin2) (i32.sub (local.get 0) (local.get 1)))
                (elem (i32.const 0) func $add $neg $sub)
                (func (export "via2") (param i32 i32) (result i32)
                    (call_indirect (type $bin)
                        (local.get 0) (i32.const 3) (local.get 1)))
                (func (export "via1") (param i32 i32) (result i32)
                    (call_indirect (type $un) (local.get 0) (local.get 1)))
            )
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let module = decode_wasm_module(&wasm).expect("decode");
        let guards = module.call_indirect_guards();
        assert!(guards.tables[0].runtime_type_check);
        assert_eq!(
            guards.type_class_ids,
            vec![1, 2, 1],
            "$bin2 is a structural duplicate of $bin — one class id (#676)"
        );
        assert_eq!(
            guards.type_ids_image,
            vec![1, 2, 1, 0, 0],
            "slots: $add(bin)=1, $neg(un)=2, $sub(bin2 ≡ bin)=1, null, null"
        );
        assert_eq!(
            guards.type_ids_byte_offset,
            Some(20),
            "sidecar starts after the 5 pointer words"
        );

        // Homogeneous module → NO sidecar, no runtime check anywhere.
        let wat = r#"
            (module
                (type $t (func (param i32) (result i32)))
                (table 2 2 funcref)
                (func $f0 (type $t) (local.get 0))
                (func $f1 (type $t) (i32.const 7))
                (elem (i32.const 0) func $f0 $f1)
                (func (export "via") (param i32 i32) (result i32)
                    (call_indirect (type $t) (local.get 0) (local.get 1)))
            )
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let module = decode_wasm_module(&wasm).expect("decode");
        let guards = module.call_indirect_guards();
        assert!(!guards.tables[0].runtime_type_check);
        assert_eq!(guards.type_ids_byte_offset, None, "no heterogeneous table");
        assert!(guards.type_ids_image.is_empty());
        assert!(guards.type_class_ids.is_empty());
    }

    /// #642: no table at all → no compile-time bound → table_size None and
    /// every type rejected (the lowering declines).
    #[test]
    fn test_call_indirect_guards_no_table_642() {
        let wat = r#"
            (module
                (func (export "f") (param i32) (result i32) (local.get 0))
            )
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let module = decode_wasm_module(&wasm).expect("decode");
        assert_eq!(module.table_size, None);
        assert!(module.table_sizes.is_empty(), "#650: no tables declared");
        let guards = module.call_indirect_guards();
        assert!(
            guards.tables.is_empty(),
            "no table → no guard entry → every call_indirect declines"
        );
    }

    /// #642: duplicate-but-structurally-identical types stay interchangeable —
    /// the closed-world check compares SIGNATURES, not type indices.
    #[test]
    fn test_call_indirect_guards_duplicate_types_verified_642() {
        let wat = r#"
            (module
                (type $a (func (result i32)))
                (type $b (func (result i32)))
                (table 1 funcref)
                (elem (i32.const 0) $f)
                (func $f (type $a) (i32.const 7))
                (func (export "run") (param i32) (result i32)
                    (call_indirect (type $b) (local.get 0)))
            )
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let module = decode_wasm_module(&wasm).expect("decode");
        let guards = module.call_indirect_guards();
        // $f has type $a; the call expects $b — structurally identical, so
        // BOTH type indices must verify. (A third type — the export's
        // (i32)->i32 — is correctly rejected: different signature.)
        assert_eq!(
            &guards.tables[0].type_reject[0..2],
            &[None, None],
            "structural signature comparison must accept duplicate types: {:?}",
            guards.tables[0].type_reject
        );
        assert!(
            guards.tables[0].type_reject[2].is_some(),
            "the structurally-different third type must still be rejected"
        );
    }

    /// #650: TWO tables become a contiguous R11 region — table 0 at offset 0
    /// (byte-identical single-table degeneration), table 1 at
    /// `size(table 0) * 4`. Each table gets its OWN size, base offset, and
    /// per-type closed-world verdicts (segments only poison the table they
    /// target).
    #[test]
    fn test_call_indirect_guards_multi_table_650() {
        // The #650 repro shape: overlapping indices, distinct functions —
        // table0[1] != table1[1] (the aliasing canary).
        let wat = r#"
            (module
                (type $t (func (param i32) (result i32)))
                (type $u (func (param i32 i32) (result i32)))
                (table $t0 3 3 funcref)
                (table $t1 2 2 funcref)
                (func $a0 (type $t) (i32.add (local.get 0) (i32.const 100)))
                (func $a1 (type $t) (i32.add (local.get 0) (i32.const 200)))
                (func $a2 (type $t) (i32.add (local.get 0) (i32.const 300)))
                (func $b0 (type $u) (i32.add (local.get 0) (local.get 1)))
                (func $b1 (type $u) (i32.sub (local.get 0) (local.get 1)))
                (elem (table $t0) (i32.const 0) func $a0 $a1 $a2)
                (elem (table $t1) (i32.const 0) func $b0 $b1)
                (func (export "f") (param i32 i32) (result i32)
                    (call_indirect $t1 (type $u)
                        (local.get 0) (i32.const 10) (local.get 1)))
            )
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let module = decode_wasm_module(&wasm).expect("decode");
        assert_eq!(module.table_sizes, vec![Some(3), Some(2)]);
        assert_eq!(module.table_size, Some(3), "compat accessor = table 0");
        assert_eq!(
            module.elem_segments[0].table_index, 0,
            "segment 0 targets table 0"
        );
        assert_eq!(
            module.elem_segments[1],
            ElemSegmentInfo {
                table_index: 1,
                offset: Some(0),
                funcs: Some(vec![3, 4]),
            },
            "segment 1 is statically attributed to table 1 (#650)"
        );

        let guards = module.call_indirect_guards();
        assert_eq!(guards.tables.len(), 2);
        assert_eq!(guards.tables[0].table_size, Some(3));
        assert_eq!(guards.tables[0].base_byte_offset, Some(0));
        assert_eq!(guards.tables[1].table_size, Some(2));
        assert_eq!(
            guards.tables[1].base_byte_offset,
            Some(12),
            "table 1 base = size(table 0) * 4 within the contiguous R11 region"
        );
        // Table 0 is homogeneous in $t (type 0); table 1 in $u (type 1) —
        // each verifies ITS type and rejects the other's.
        assert_eq!(guards.tables[0].type_reject[0], None, "table 0 vs $t");
        assert!(guards.tables[0].type_reject[1].is_some(), "table 0 vs $u");
        assert!(guards.tables[1].type_reject[0].is_some(), "table 1 vs $t");
        assert_eq!(guards.tables[1].type_reject[1], None, "table 1 vs $u");
    }

    /// #650: an unknown-size table (growable import) declines ITSELF and
    /// makes every LATER table's base offset non-constant — but a table
    /// BEFORE it is unaffected.
    #[test]
    fn test_call_indirect_guards_unknown_size_poisons_later_bases_650() {
        let wat = r#"
            (module
                (type $t (func (result i32)))
                (import "env" "tbl" (table 4 funcref))
                (table $d 1 1 funcref)
                (func $f (type $t) (i32.const 7))
                (elem (table $d) (i32.const 0) func $f)
                (func (export "run") (param i32) (result i32)
                    (call_indirect $d (type $t) (local.get 0)))
            )
        "#;
        let wasm = wat::parse_str(wat).expect("parse");
        let module = decode_wasm_module(&wasm).expect("decode");
        assert_eq!(
            module.table_sizes,
            vec![None, Some(1)],
            "growable import (no max) has no sound compile-time size"
        );
        let guards = module.call_indirect_guards();
        assert_eq!(guards.tables[0].base_byte_offset, Some(0));
        assert!(
            guards.tables[0].type_reject.iter().all(|r| r.is_some()),
            "unknown-size table rejects every type"
        );
        assert_eq!(
            guards.tables[1].base_byte_offset, None,
            "a later table's base is not a compile-time constant when a \
             preceding table's size is unknown (#650)"
        );
        assert_eq!(guards.tables[1].table_size, Some(1));
    }
}
