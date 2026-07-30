//! #851 lane L3 — the aarch64 MODULE-LEVEL substrate: the WASM globals region
//! and the `call_indirect` funcref table.
//!
//! # Precondition status (stated plainly)
//!
//! Neither region is a precondition. Both are EMITTED BY SYNTH into the object
//! and reached with an `adrp` + `add :lo12:` pair against a symbol the same
//! object defines, so the linker places them and no register convention, no
//! startup, no linker script and no ambient input is required.
//!
//! This is deliberately DIFFERENT from `x28` (the linear-memory base, see
//! [`crate::selector`]'s `LINMEM_BASE`), which IS a precondition the embedder
//! supplies: synth emits nothing that establishes it. Lane L3 adds NO second
//! precondition — v0.53 made the `x28` one explicit precisely so that the next
//! feature would not quietly add another.
//!
//! # Why PC-relative and not a base register
//!
//! The ARM backend reaches its globals through R9 and its funcref table through
//! a literal-pool word, because a Cortex-M image has no linker to consult. The
//! aarch64 backend emits `ET_REL` and is always host-linked, so `adrp`+`add`
//! costs the same two instructions and needs no ambient register — which also
//! sidesteps the #275/#717 class outright: there is no base register to collide
//! with the linear-memory base.
//!
//! # Layouts
//!
//! **Globals (`__synth_globals`, in `.data`)** — ONE 8-BYTE SLOT PER GLOBAL,
//! `global k` at byte offset `k * 8`, regardless of declared width. An i32/f32
//! global occupies the low 4 bytes (read back through the `w` view) and an
//! i64/f64 global the full 8. This is NOT the ARM/#643 dense width-summed
//! layout: uniform 8-byte slots keep every slot naturally aligned for `ldr x`
//! (a dense layout puts an i64 at offset 4) and make the slot offset a constant
//! `k * 8` the selector can fold into the load/store immediate. Nothing outside
//! this backend reads the region, so the layouts need not agree.
//!
//! **Funcref table (`__synth_func_table`, in `.text`)** — ONE 8-BYTE SLOT PER
//! TABLE ENTRY across all tables in declaration order (the same contiguous
//! region order `DecodedModule::funcref_region_slots` describes), each:
//!
//! ```text
//!   +0  u32   structural class id of the slot's function (0 = null slot)
//!   +4  insn  `b func_N`  (an R_AARCH64_JUMP26 site) — or `brk #0` when null
//! ```
//!
//! The class-id word is DATA that lives in `.text`; it is never executed
//! (the dispatch branches to slot+4, never slot+0). A slot's trampoline is a
//! TAIL branch, so the dispatcher's `blr` sets `x30` and the callee returns
//! straight to the dispatcher.

use synth_core::backend::{CodeRelocation, FUNC_TABLE_SYMBOL, RelocKind};
use synth_core::wasm_decoder::{DecodedModule, GlobalInit, WasmGlobal};

use crate::elf::{DataBlob, ElfFunction};
use crate::encoder as enc;

/// The `.data` symbol naming the base of the emitted globals region.
pub const GLOBALS_SYMBOL: &str = "__synth_globals";

/// Bytes per emitted global slot — see the module docs (uniform, not dense).
pub const GLOBAL_SLOT_BYTES: u32 = 8;

/// Bytes per emitted funcref-table slot: `[u32 class id][b func_N]`.
pub const TABLE_SLOT_BYTES: u32 = 8;

/// The largest global index this lowering can address. `global.get` of an i32
/// global emits `ldr w, [xT, #k*8]`, whose SCALED 12-bit immediate is `k*2`, so
/// `k*2` must stay below 4096.
pub const MAX_GLOBALS: usize = 2048;

/// The largest table this lowering can bounds-check: the out-of-range guard is
/// `cmp w_idx, #size`, an unsigned 12-bit immediate.
pub const MAX_TABLE_SLOTS: usize = 4095;

/// The largest structural class id the type check can compare: `cmp w, #id`.
pub const MAX_CLASS_ID: u32 = 4095;

/// What the two aarch64 drivers must place in the object for the globals and
/// `call_indirect` lowerings to be sound.
#[derive(Debug, Default, Clone)]
pub struct Substrate {
    /// The `.data` image — empty when the module uses no globals.
    pub globals: DataBlob,
    /// The `.text`-resident funcref table (an `is_object` [`ElfFunction`] to be
    /// appended LAST, so real functions keep their `.text` offsets) — `None`
    /// when the module performs no `call_indirect`.
    pub table: Option<ElfFunction>,
    /// True when at least one region was emitted, i.e. when the selector may be
    /// told `a64_substrate_emitted`. A module using neither feature plans an
    /// EMPTY substrate and stays byte-identical.
    pub emitted: bool,
}

/// Everything [`plan`] needs, OWNED, so a driver that aggregates module state
/// can build it once while the decoded module is still whole and carry it to
/// wherever the ELF is assembled. Both aarch64 drivers do exactly that.
///
/// The two `uses_*` flags are set LAST, by the driver, from the op streams it
/// is actually about to compile.
#[derive(Debug, Default, Clone)]
pub struct PlanInputs {
    /// Defined globals with their decoded constant initializers.
    pub globals: Vec<WasmGlobal>,
    /// How many globals the module IMPORTS (their values arrive at
    /// instantiation, which this backend cannot perform).
    pub imported_globals: u32,
    /// Does any compiled function execute `global.get`/`global.set`?
    pub uses_globals: bool,
    /// The contiguous funcref-region image
    /// (`DecodedModule::funcref_region_slots`).
    pub funcref_slots: Vec<Option<u32>>,
    /// The matching per-slot structural class ids
    /// (`DecodedModule::funcref_region_class_ids`).
    pub funcref_class_ids: Vec<u32>,
    /// Per-table compile-time sizes (`DecodedModule::table_sizes`).
    pub table_sizes: Vec<Option<u32>>,
    /// Element segments, for the statically-verifiable-image check.
    pub elem_segments: Vec<synth_core::wasm_decoder::ElemSegmentInfo>,
    /// Number of imported functions — a table slot pointing at one has no
    /// `func_N` body in this object.
    pub num_imported_funcs: u32,
    /// Does any compiled function execute `call_indirect`?
    pub uses_call_indirect: bool,
    /// #851 lane L3 — the STRUCTURAL class id per function type, carried here
    /// so the driver can hand it to the selector's `ModuleCtx` without keeping
    /// the whole decoded module alive.
    pub type_class_ids: Vec<u32>,
    /// Result count per function type, same rationale.
    pub type_result_counts: Vec<u32>,
}

impl PlanInputs {
    /// Snapshot everything from a whole decoded module. The `uses_*` flags stay
    /// `false`; the driver sets them from the op streams it compiles.
    pub fn from_module(module: &DecodedModule) -> Self {
        Self {
            globals: module.globals.clone(),
            imported_globals: module
                .imports
                .iter()
                .filter(|i| matches!(i.kind, synth_core::ImportKind::Global))
                .count() as u32,
            uses_globals: false,
            funcref_slots: module.funcref_region_slots(),
            funcref_class_ids: module.funcref_region_class_ids(),
            table_sizes: module.table_sizes.clone(),
            elem_segments: module.elem_segments.clone(),
            num_imported_funcs: module.num_imported_funcs,
            uses_call_indirect: false,
            type_class_ids: module.structural_type_class_ids(),
            type_result_counts: module.type_result_counts.clone(),
        }
    }

    /// Set the two usage flags from an op-stream scan over the functions the
    /// driver will compile.
    pub fn with_usage(mut self, uses_globals: bool, uses_call_indirect: bool) -> Self {
        self.uses_globals = uses_globals;
        self.uses_call_indirect = uses_call_indirect;
        self
    }
}

/// Plan (and materialize) the module-level substrate.
///
/// Every `Err` is a LOUD DECLINE with a machine-readable reason — the compile
/// fails rather than shipping a region whose contents synth cannot vouch for.
/// The two features are planned INDEPENDENTLY: a module that uses only globals
/// never touches the table checks and vice versa.
pub fn plan(input: &PlanInputs) -> Result<Substrate, String> {
    let globals = if input.uses_globals {
        plan_globals(input)?
    } else {
        DataBlob::default()
    };
    let table = if input.uses_call_indirect {
        Some(plan_table(input)?)
    } else {
        None
    };
    Ok(Substrate {
        emitted: !globals.bytes.is_empty() || table.is_some(),
        globals,
        table,
    })
}

/// Build the `.data` globals image, or decline.
fn plan_globals(input: &PlanInputs) -> Result<DataBlob, String> {
    // An IMPORTED global's value is supplied by the host at instantiation.
    // This backend emits no instantiation step, so its slot would ship whatever
    // synth guessed — the silent-wrong-initial-value class. Decline.
    if input.imported_globals > 0 {
        return Err(format!(
            "module imports {} global(s), whose values are supplied at \
             instantiation — the aarch64 backend emits no instantiation step, so \
             the emitted region would ship a fabricated initial value; \
             loud-declining (#851)",
            input.imported_globals
        ));
    }
    if input.globals.is_empty() {
        return Err(
            "function executes global.get/global.set but the module declares no \
             globals — refusing to address an empty region (#851)"
                .into(),
        );
    }
    if input.globals.len() > MAX_GLOBALS {
        return Err(format!(
            "module declares {} globals; the aarch64 lowering addresses at most \
             {MAX_GLOBALS} (a `ldr w, [base, #k*8]` scaled 12-bit immediate); \
             loud-declining (#851)",
            input.globals.len()
        ));
    }

    let mut bytes = vec![0u8; input.globals.len() * GLOBAL_SLOT_BYTES as usize];
    for (k, g) in input.globals.iter().enumerate() {
        // A global whose declared type is not i32/i64 (f32/f64/v128), or whose
        // initializer is not a plain const, decodes to `init: None`. Shipping a
        // zero there is exactly the #757/#798 "region reads the wrong bytes"
        // class — decline instead.
        let off = k * GLOBAL_SLOT_BYTES as usize;
        match g.init {
            Some(GlobalInit::I32(v)) => {
                bytes[off..off + 4].copy_from_slice(&(v as u32).to_le_bytes());
            }
            Some(GlobalInit::I64(v)) => {
                bytes[off..off + 8].copy_from_slice(&(v as u64).to_le_bytes());
            }
            None => {
                return Err(format!(
                    "global {k} has no decoded constant initializer (a float, \
                     v128, or non-const init expression) — the emitted region \
                     would ship a WRONG initial value; loud-declining (#851)"
                ));
            }
        }
        if g.slot_bytes > GLOBAL_SLOT_BYTES {
            return Err(format!(
                "global {k} declares a {}-byte value type (v128); the aarch64 \
                 globals region uses {GLOBAL_SLOT_BYTES}-byte slots; \
                 loud-declining (#851)",
                g.slot_bytes
            ));
        }
    }
    Ok(DataBlob {
        bytes,
        symbols: vec![(GLOBALS_SYMBOL.to_string(), 0)],
    })
}

/// Build the `.text` funcref-table trampoline blob, or decline.
fn plan_table(input: &PlanInputs) -> Result<ElfFunction, String> {
    // 1. Every table must have a compile-time size, or its slots have no
    //    constant base offset within the region (and no sound bounds check).
    if input.table_sizes.is_empty() {
        return Err(
            "function executes call_indirect but the module declares no table — \
             loud-declining (#851)"
                .into(),
        );
    }
    for (n, size) in input.table_sizes.iter().enumerate() {
        if size.is_none() {
            return Err(format!(
                "table {n} has no compile-time size (an imported table whose \
                 limits do not pin it); neither its bounds check nor any later \
                 table's base offset is a constant — loud-declining (#851)"
            ));
        }
    }

    // 2. The table IMAGE must be statically verifiable. `funcref_region_slots`
    //    reports an unverifiable table as all-null, which would make EVERY
    //    dispatch trap — sound-looking but WRONG in the other direction (it
    //    traps where wasmtime calls). Detect and decline instead of shipping a
    //    silently-always-trapping table.
    for (i, seg) in input.elem_segments.iter().enumerate() {
        let (Some(off), Some(funcs)) = (seg.offset, seg.funcs.as_ref()) else {
            return Err(format!(
                "element segment {i} is not statically verifiable (passive or \
                 declared segment, non-constant offset, or a non-`ref.func` \
                 entry) — the emitted table would trap on entries wasm calls \
                 successfully; loud-declining (#851)"
            ));
        };
        let size = input
            .table_sizes
            .get(seg.table_index as usize)
            .copied()
            .flatten()
            .ok_or_else(|| {
                format!(
                    "element segment {i} targets table {} which the module does \
                     not declare — loud-declining (#851)",
                    seg.table_index
                )
            })?;
        if off as u64 + funcs.len() as u64 > size as u64 {
            return Err(format!(
                "element segment {i} writes {} entries at offset {off} of table \
                 {} (size {size}) — out of range; loud-declining (#851)",
                funcs.len(),
                seg.table_index
            ));
        }
    }

    // 3. Size + class-id immediates must fit the guard encodings.
    let slots = &input.funcref_slots;
    if slots.len() > MAX_TABLE_SLOTS {
        return Err(format!(
            "funcref region holds {} slots; the out-of-range guard compares \
             against an unsigned 12-bit immediate (at most {MAX_TABLE_SLOTS}) — \
             loud-declining (#851)",
            slots.len()
        ));
    }
    if slots.len() != input.funcref_class_ids.len() {
        return Err(format!(
            "internal: funcref slot/class-id lengths disagree ({} vs {}) — \
             loud-declining (#851)",
            slots.len(),
            input.funcref_class_ids.len()
        ));
    }
    if let Some(bad) = input.funcref_class_ids.iter().find(|c| **c > MAX_CLASS_ID) {
        return Err(format!(
            "module carries structural type class id {bad}; the type check \
             compares against an unsigned 12-bit immediate (at most \
             {MAX_CLASS_ID}) — loud-declining (#851)"
        ));
    }

    // 4. Emit the trampolines.
    let mut code: Vec<u8> = Vec::with_capacity(slots.len() * TABLE_SLOT_BYTES as usize);
    let mut relocations: Vec<CodeRelocation> = Vec::new();
    for (s, slot) in slots.iter().enumerate() {
        let class = input.funcref_class_ids[s];
        code.extend_from_slice(&class.to_le_bytes());
        match slot {
            Some(f) => {
                // A slot pointing at an IMPORTED function has no `func_N` body
                // in this object; import dispatch is declined on this backend,
                // so a `b func_N` would relocate against a symbol we never
                // place (and the ELF builder now panics rather than drop it).
                if *f < input.num_imported_funcs {
                    return Err(format!(
                        "table slot {s} holds imported function {f}; import \
                         dispatch is not supported on aarch64, so the table \
                         cannot carry a trampoline to it — loud-declining (#851)"
                    ));
                }
                relocations.push(CodeRelocation {
                    offset: (s as u32 * TABLE_SLOT_BYTES) + 4,
                    symbol: format!("func_{f}"),
                    kind: RelocKind::AArch64Jump26,
                });
                // `b #0` placeholder — the JUMP26 relocation supplies the imm26.
                code.extend_from_slice(&enc::b_uncond(0).to_le_bytes());
            }
            // A NULL slot: calling it must trap (WASM §4.4.8 "uninitialized
            // element"). Its class id is 0, which never equals an expected
            // class (>= 1), so the dispatch's type check traps FIRST; the `brk`
            // is the belt-and-braces second line of defence.
            None => code.extend_from_slice(&enc::brk(0).to_le_bytes()),
        }
    }
    Ok(ElfFunction {
        symbols: vec![FUNC_TABLE_SYMBOL.to_string()],
        code,
        relocations,
        is_object: true,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use synth_core::wasm_decoder::ElemSegmentInfo;

    fn g(index: u32, init: Option<GlobalInit>, slot_bytes: u32) -> WasmGlobal {
        WasmGlobal {
            index,
            init,
            mutable: true,
            slot_bytes,
        }
    }

    fn base() -> PlanInputs {
        PlanInputs::default()
    }

    /// A module using neither feature plans an EMPTY substrate — no `.data`, no
    /// table, `emitted == false` (so the selector keeps declining and every
    /// existing module's bytes are untouched).
    #[test]
    fn unused_features_plan_an_empty_substrate() {
        let s = plan(&base()).unwrap();
        assert!(s.globals.bytes.is_empty());
        assert!(s.table.is_none());
        assert!(!s.emitted);
    }

    /// The globals image carries the DECODED initial values at uniform 8-byte
    /// slots — an i32 in the low word, an i64 across both.
    #[test]
    fn globals_image_holds_initial_values_at_eight_byte_slots() {
        let gs = [
            g(0, Some(GlobalInit::I32(7)), 4),
            g(1, Some(GlobalInit::I64(-2)), 8),
            g(2, Some(GlobalInit::I32(-1)), 4),
        ];
        let s = plan(&PlanInputs {
            globals: gs.to_vec(),
            uses_globals: true,
            ..base()
        })
        .unwrap();
        assert_eq!(s.globals.bytes.len(), 24);
        assert_eq!(&s.globals.bytes[0..8], &7u64.to_le_bytes());
        assert_eq!(&s.globals.bytes[8..16], &(-2i64 as u64).to_le_bytes());
        // i32 -1 fills the LOW word only; the upper word stays zero.
        assert_eq!(
            &s.globals.bytes[16..24],
            &[0xFF, 0xFF, 0xFF, 0xFF, 0, 0, 0, 0]
        );
        assert_eq!(s.globals.symbols, vec![(GLOBALS_SYMBOL.to_string(), 0)]);
        assert!(s.emitted);
    }

    /// A global with no decoded constant initializer (float / non-const expr)
    /// must DECLINE — shipping a zero there is the wrong-initial-value class.
    #[test]
    fn global_without_const_initializer_declines() {
        let gs = [g(0, Some(GlobalInit::I32(1)), 4), g(1, None, 4)];
        let e = plan(&PlanInputs {
            globals: gs.to_vec(),
            uses_globals: true,
            ..base()
        })
        .unwrap_err();
        assert!(e.contains("global 1"), "{e}");
        assert!(e.contains("no decoded constant initializer"), "{e}");
    }

    /// An IMPORTED global declines: its value arrives at instantiation.
    #[test]
    fn imported_global_declines() {
        let gs = [g(0, Some(GlobalInit::I32(1)), 4)];
        let e = plan(&PlanInputs {
            globals: gs.to_vec(),
            imported_globals: 1,
            uses_globals: true,
            ..base()
        })
        .unwrap_err();
        assert!(e.contains("imports 1 global"), "{e}");
    }

    /// The table blob is `[u32 class][b func_N]` per slot, with a JUMP26
    /// relocation at slot+4 for every INITIALIZED slot and a `brk #0` (no
    /// relocation) for every null one.
    #[test]
    fn table_blob_layout_and_null_slot_traps() {
        let slots = [Some(0u32), None, Some(1u32)];
        let ids = [1u32, 0, 2];
        let sizes = [Some(3u32)];
        let segs = [ElemSegmentInfo {
            table_index: 0,
            offset: Some(0),
            funcs: Some(vec![0, 9, 1]),
        }];
        let s = plan(&PlanInputs {
            funcref_slots: slots.to_vec(),
            funcref_class_ids: ids.to_vec(),
            table_sizes: sizes.to_vec(),
            elem_segments: segs.to_vec(),
            uses_call_indirect: true,
            ..base()
        })
        .unwrap();
        let t = s.table.unwrap();
        assert!(t.is_object, "the table is DATA in .text, not a function");
        assert_eq!(t.symbols, vec![FUNC_TABLE_SYMBOL.to_string()]);
        assert_eq!(t.code.len(), 24);
        assert_eq!(&t.code[0..4], &1u32.to_le_bytes());
        assert_eq!(&t.code[4..8], &enc::b_uncond(0).to_le_bytes());
        // Null slot: class id 0 + an in-slot trap, and NO relocation.
        assert_eq!(&t.code[8..12], &0u32.to_le_bytes());
        assert_eq!(&t.code[12..16], &enc::brk(0).to_le_bytes());
        assert_eq!(&t.code[16..20], &2u32.to_le_bytes());
        assert_eq!(t.relocations.len(), 2);
        assert_eq!(t.relocations[0].offset, 4);
        assert_eq!(t.relocations[0].symbol, "func_0");
        assert_eq!(t.relocations[1].offset, 20);
        assert_eq!(t.relocations[1].symbol, "func_1");
        assert!(
            t.relocations
                .iter()
                .all(|r| matches!(r.kind, RelocKind::AArch64Jump26))
        );
    }

    /// An UNVERIFIABLE element segment must DECLINE, not ship an all-null table.
    /// `funcref_region_slots` degrades such a table to all-null, which would
    /// trap on every dispatch — sound-LOOKING but wrong in the other direction
    /// (wasmtime calls those entries successfully).
    #[test]
    fn unverifiable_element_segment_declines_rather_than_shipping_a_trap_table() {
        let slots = [None, None];
        let ids = [0u32, 0];
        let sizes = [Some(2u32)];
        // A passive/non-const segment: offset is None.
        let segs = [ElemSegmentInfo {
            table_index: 0,
            offset: None,
            funcs: Some(vec![0, 1]),
        }];
        let e = plan(&PlanInputs {
            funcref_slots: slots.to_vec(),
            funcref_class_ids: ids.to_vec(),
            table_sizes: sizes.to_vec(),
            elem_segments: segs.to_vec(),
            uses_call_indirect: true,
            ..base()
        })
        .unwrap_err();
        assert!(e.contains("not statically verifiable"), "{e}");
        assert!(e.contains("trap on entries wasm calls successfully"), "{e}");
    }

    /// A table of unknown compile-time size (a growable imported table) has no
    /// sound bounds check and no constant base — decline.
    #[test]
    fn unsized_table_declines() {
        let e = plan(&PlanInputs {
            table_sizes: vec![None],
            uses_call_indirect: true,
            ..base()
        })
        .unwrap_err();
        assert!(e.contains("no compile-time size"), "{e}");
    }

    /// A slot holding an IMPORTED function declines: this object places no
    /// `func_N` body for it, so the trampoline could not be relocated.
    #[test]
    fn table_slot_holding_an_import_declines() {
        let slots = [Some(0u32)];
        let ids = [1u32];
        let sizes = [Some(1u32)];
        let segs = [ElemSegmentInfo {
            table_index: 0,
            offset: Some(0),
            funcs: Some(vec![0]),
        }];
        let e = plan(&PlanInputs {
            funcref_slots: slots.to_vec(),
            funcref_class_ids: ids.to_vec(),
            table_sizes: sizes.to_vec(),
            elem_segments: segs.to_vec(),
            num_imported_funcs: 1,
            uses_call_indirect: true,
            ..base()
        })
        .unwrap_err();
        assert!(e.contains("imported function 0"), "{e}");
    }

    /// A table larger than the 12-bit bounds-guard immediate declines.
    #[test]
    fn oversized_table_declines() {
        let slots = vec![Some(0u32); MAX_TABLE_SLOTS + 1];
        let ids = vec![1u32; MAX_TABLE_SLOTS + 1];
        let sizes = [Some(slots.len() as u32)];
        let segs = [ElemSegmentInfo {
            table_index: 0,
            offset: Some(0),
            funcs: Some(vec![0; slots.len()]),
        }];
        let e = plan(&PlanInputs {
            funcref_slots: slots.to_vec(),
            funcref_class_ids: ids.to_vec(),
            table_sizes: sizes.to_vec(),
            elem_segments: segs.to_vec(),
            uses_call_indirect: true,
            ..base()
        })
        .unwrap_err();
        assert!(e.contains("unsigned 12-bit immediate"), "{e}");
    }
}
