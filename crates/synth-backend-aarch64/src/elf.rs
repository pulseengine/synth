//! Minimal `EM_AARCH64` ELF64 relocatable-object emitter — milestone-1b (#538),
//! extended for direct calls (#851).
//!
//! Produces an `ET_REL` object for AArch64 (`e_machine = 183`) with a single
//! `.text` (all function bodies concatenated), a `.symtab` exposing one or more
//! `STT_FUNC` symbols per function at its `.text` offset (each function
//! carries a LOCAL `func_N` label plus, when exported, its GLOBAL export name —
//! #1180), the two string tables, and — when any function has a call
//! relocation — a `.rela.text` section of `R_AARCH64_CALL26` entries so
//! `bl func_N` sites are linkable (#851). The object is host-linkable on arm64
//! ELF targets and its `.text` is directly runnable under a native or emulated
//! A64 core once relocated.

use synth_core::backend::{BackendError, CodeRelocation, RelocKind, SymbolBinding, locals_first};

/// R_AARCH64_CALL26 — the ELF relocation type for a `bl` 26-bit call site.
const R_AARCH64_CALL26: u32 = 283;
/// R_AARCH64_JUMP26 — the same 26-bit field on a plain `b` (no link). Used by
/// the `call_indirect` funcref-table trampolines (#851 lane L3).
const R_AARCH64_JUMP26: u32 = 282;
/// R_AARCH64_ADR_PREL_PG_HI21 — the `adrp` half of a PC-relative symbol address.
const R_AARCH64_ADR_PREL_PG_HI21: u32 = 275;
/// R_AARCH64_ADD_ABS_LO12_NC — the `add …, :lo12:sym` half of the same pair.
const R_AARCH64_ADD_ABS_LO12_NC: u32 = 277;

/// A compiled function to place in `.text`.
#[derive(Debug, Clone)]
pub struct ElfFunction {
    /// Symbol name aliases for this function's `.text` offset. The FIRST is
    /// the canonical in-object label — `func_N` (N = wasm function index), or
    /// `__synth_func_table` for the [`Self::is_object`] table — and is
    /// planned LOCAL: it is what this object's own `CALL26`/`JUMP26`
    /// relocations bind to (by symbol index), and it is the name a SECOND
    /// synth object also defines, so it must not take part in cross-object
    /// resolution (#1180 — the `duplicate symbol: func_1` class; ARM's #656
    /// policy, ported into the shared plan). Any following aliases are wasm
    /// EXPORT names and are planned GLOBAL — the names an embedder calls.
    /// The driver upholds this order (`build_multi_func_aarch64_elf`); the
    /// binding is assigned in [`plan_object`], once, for every container.
    pub symbols: Vec<String>,
    /// Function body machine code.
    pub code: Vec<u8>,
    /// Call relocations within this function's code (offsets are function-local;
    /// the builder rebases them to the `.text` offset). Empty for leaf functions.
    pub relocations: Vec<CodeRelocation>,
    /// #851 lane L3: this entry is DATA that happens to live in `.text` (the
    /// `call_indirect` funcref table: `[u32 class-id][b func_N]` slot records).
    /// Its symbols are emitted `STT_OBJECT` rather than `STT_FUNC` — the table
    /// is branched INTO at slot+4, never called at slot+0, and typing it as a
    /// function would misdescribe the object to any consumer.
    pub is_object: bool,
}

impl ElfFunction {
    /// A normal code function (`STT_FUNC` symbols).
    pub fn code(symbols: Vec<String>, code: Vec<u8>, relocations: Vec<CodeRelocation>) -> Self {
        Self {
            symbols,
            code,
            relocations,
            is_object: false,
        }
    }
}

/// #851 lane L3 — the synth-EMITTED `.data` image (the WASM globals region).
///
/// PRECONDITION STATUS, stated plainly: there is NONE. Unlike the `x28`
/// linear-memory base (an ambient input the embedder supplies — see
/// `selector::LINMEM_BASE`), the globals region is emitted BY synth into this
/// section, carrying each global's decoded constant initializer, and reached
/// from code by an `adrp`+`add :lo12:` pair against [`Self::symbols`]. The
/// linker places it; no register convention, no startup, no linker script and
/// no second ambient input is required.
#[derive(Debug, Default, Clone)]
pub struct DataBlob {
    /// The `.data` bytes (little-endian, already laid out).
    pub bytes: Vec<u8>,
    /// `(symbol name, byte offset within `.data`)` — e.g.
    /// `("__synth_globals", 0)`. Emitted as LOCAL `STT_OBJECT` (#1180): the
    /// region is reached only by this object's own `adrp`+`add :lo12:` pair,
    /// no embedder register names it (unlike ARM's R9 contract), and a second
    /// synth object carries its own `__synth_globals`.
    pub symbols: Vec<(String, u64)>,
}

const EHDR_SIZE: usize = 64;
const SHDR_SIZE: usize = 64;
const SYM_SIZE: usize = 24;
const RELA_SIZE: usize = 24;

fn push_u16(v: &mut Vec<u8>, x: u16) {
    v.extend_from_slice(&x.to_le_bytes());
}
fn push_u32(v: &mut Vec<u8>, x: u32) {
    v.extend_from_slice(&x.to_le_bytes());
}
fn push_u64(v: &mut Vec<u8>, x: u64) {
    v.extend_from_slice(&x.to_le_bytes());
}

/// RQ-64-MACHO: where a planned symbol lives. `Text`/`Data` are section
/// classes shared by every container this backend can write (ELF `.text` /
/// `.data`, Mach-O `__TEXT,__text` / `__DATA,__data`); `Undefined` is the
/// #1017 import external the host linker resolves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolPlace {
    Text,
    Data,
    Undefined,
}

/// RQ-64-MACHO: one symbol of the container-independent plan, in emission
/// order. `value` is the offset within its section (`0` for `Undefined`);
/// `is_object` selects the OBJECT (vs FUNC) type in containers that type
/// symbols; `binding` (#1180 / RQ-65-FUNCN) is whether the symbol takes part
/// in cross-object resolution — ELF `STB_LOCAL`/`STB_GLOBAL`, Mach-O `N_EXT`
/// clear/set — decided HERE so no writer decides it alone.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlannedSymbol {
    pub name: String,
    pub is_object: bool,
    pub binding: SymbolBinding,
    pub place: SymbolPlace,
    pub value: u64,
    pub size: u64,
}

/// RQ-64-MACHO: one resolved relocation — a `.text` offset, the backend's
/// relocation kind, and the index of its target in [`ObjectPlan::symbols`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlannedReloc {
    pub offset: u64,
    pub kind: RelocKind,
    pub symbol: usize,
}

/// RQ-64-MACHO: the container-independent object PLAN — everything a
/// relocatable object says, before any container says it.
///
/// This is the single source both writers consume: [`build_relocatable_object_full`]
/// (ELF `ET_REL`) and [`crate::macho::build_macho_object_full`] (Mach-O
/// `MH_OBJECT`). The `.text` bytes, the `.data` bytes, the symbol list (order,
/// type, BINDING, section, offset, size) and the resolved relocation list are
/// computed ONCE here, so the two containers cannot disagree on any of them by
/// construction — the byte-identity the RQ-64-MACHO oracle then checks from the
/// outside (`scripts/repro/macho_host_link_rq64_differential.py`) is a property
/// of this function, not of two writers happening to agree. A second
/// hand-written copy of the symbol-ordering, binding or #1013 rules in the
/// Mach-O writer would be exactly the mirror the North Star forbids.
///
/// #1180 / RQ-65-FUNCN: binding was the one thing v0.64's plan did NOT carry
/// (`elf.rs` hard-coded `STB_GLOBAL`, `macho.rs` set `N_EXT` on everything,
/// independently), which is why two synth objects collided on `func_1` in
/// both containers. It is now a field of every [`PlannedSymbol`], and the
/// symbol ORDER is already locals-first (`synth_core::backend::locals_first`,
/// the same function the ARM builder applies since #656), so a writer reads
/// [`ObjectPlan::local_count`] for its partition (`sh_info` / `LC_DYSYMTAB`)
/// and never sorts.
#[derive(Debug, Clone, Default)]
pub struct ObjectPlan {
    /// All function bodies concatenated in order, no padding (A64 bodies are
    /// whole words already).
    pub text: Vec<u8>,
    /// The synth-emitted `.data` image (empty when the module has no globals).
    pub data: Vec<u8>,
    /// Symbols in emission order: the LOCAL symbols first (every function's
    /// `func_N` label / the table, in function order, then the `.data`
    /// symbols), then the GLOBAL ones (wasm export names in function order,
    /// then the referenced undefined externals in first-listed order). This
    /// is the stable locals-first permutation of the natural
    /// (function-aliases, data, externals) order.
    pub symbols: Vec<PlannedSymbol>,
    /// Relocations in function order, offsets rebased to `.text`, `symbol`
    /// indexing the locals-first [`Self::symbols`].
    pub relocs: Vec<PlannedReloc>,
}

impl ObjectPlan {
    /// #1180: the number of `Local` symbols — the length of the locals-first
    /// prefix of [`Self::symbols`]. ELF's `.symtab` `sh_info` is this `+ 1`
    /// (the null symbol at index 0 counts as local); Mach-O's `LC_DYSYMTAB`
    /// `nlocalsym` / `iextdefsym` are exactly this. Both writers READ it.
    pub fn local_count(&self) -> usize {
        let n = self
            .symbols
            .iter()
            .take_while(|s| s.binding == SymbolBinding::Local)
            .count();
        debug_assert!(
            self.symbols[n..]
                .iter()
                .all(|s| s.binding != SymbolBinding::Local),
            "plan symbols must be locals-first"
        );
        n
    }
}

/// Compute the [`ObjectPlan`] for `functions` + `data` + `undefined_externals`.
/// The rules (symbol order, first-occurrence name resolution, the #1017
/// external allowlist, the #1013 unplaced-symbol refusal) are the ELF
/// builder's, moved here unchanged — the ELF output of every module is
/// byte-identical to the pre-plan builder (gated by the RQ-64-MACHO lane's
/// 140-object corpus diff and this file's tests).
pub fn plan_object(
    functions: &[ElfFunction],
    data: &DataBlob,
    undefined_externals: &[String],
) -> Result<ObjectPlan, BackendError> {
    // --- .text: concatenated bodies; record each function's .text offset. ---
    let mut text: Vec<u8> = Vec::new();
    let mut func_off: Vec<u64> = Vec::new();
    for f in functions {
        // A64 instructions are 4-byte aligned; bodies are whole words already.
        func_off.push(text.len() as u64);
        text.extend_from_slice(&f.code);
    }
    let have_data = !data.bytes.is_empty();

    // --- symbols: one per (function, symbol-alias), then .data, then externals
    // — collected in that natural order, then permuted locals-first below.
    // A name → index map so relocations resolve by symbol name; the FIRST
    // occurrence of a duplicated name wins (the pre-plan `or_insert` rule).
    //
    // #1180 / RQ-65-FUNCN — THE BINDING RULE, stated once for every container:
    // a name synth INVENTS for its own addressing (`func_N`, the funcref
    // table, `__synth_globals`) is LOCAL; a name the wasm module EXPOSES (an
    // export) or REQUIRES (an import) is GLOBAL. Nothing outside the object
    // needs the invented names — every reference to them is an in-object
    // relocation binding by symbol index — and a second synth object carries
    // the same invented names, so a GLOBAL binding made two objects a
    // `duplicate symbol` refusal in ELF and Mach-O alike. This is ARM's #656
    // policy ported to the plan, with one deliberate difference: ARM keeps
    // `__synth_globals` GLOBAL because its embedder contract loads R9 with
    // that address; this backend has no such register.
    let mut symbols: Vec<PlannedSymbol> = Vec::new();
    let mut sym_index: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    let mut push_sym = |name: &str,
                        is_object: bool,
                        binding: SymbolBinding,
                        place: SymbolPlace,
                        value: u64,
                        size: u64,
                        symbols: &mut Vec<PlannedSymbol>| {
        sym_index.entry(name.to_string()).or_insert(symbols.len());
        symbols.push(PlannedSymbol {
            name: name.to_string(),
            is_object,
            binding,
            place,
            value,
            size,
        });
    };
    for (i, f) in functions.iter().enumerate() {
        let off = func_off[i];
        let size = f.code.len() as u64;
        // #851 lane L3: the funcref table is DATA in `.text` — type it OBJECT so
        // the object does not claim a branch-table blob is a callable function.
        // #1180: `symbols[0]` is the in-object label (LOCAL); the rest are
        // export names (GLOBAL) — see `ElfFunction::symbols`.
        for (k, sym) in f.symbols.iter().enumerate() {
            let binding = if k == 0 {
                SymbolBinding::Local
            } else {
                SymbolBinding::Global
            };
            push_sym(
                sym,
                f.is_object,
                binding,
                SymbolPlace::Text,
                off,
                size,
                &mut symbols,
            );
        }
    }
    // #851 lane L3: synth-emitted `.data` symbols (the globals region base) —
    // LOCAL (#1180), reached only by this object's own adrp/add pair.
    if have_data {
        for (name, off) in &data.symbols {
            let size = data.bytes.len() as u64 - off.min(&(data.bytes.len() as u64));
            push_sym(
                name,
                true,
                SymbolBinding::Local,
                SymbolPlace::Data,
                *off,
                size,
                &mut symbols,
            );
        }
    }
    // #1017: undefined externals — the ARM `add_undefined_symbol` shape. Only
    // externals a relocation actually references are emitted, in first-listed
    // order; a name this object already places is skipped (the reloc binds to
    // the placed symbol, ARM parity).
    {
        let referenced: std::collections::HashSet<&str> = functions
            .iter()
            .flat_map(|f| &f.relocations)
            .map(|r| r.symbol.as_str())
            .collect();
        // Defined-name set derived from the same inputs `push_sym` consumed
        // (reading `sym_index` here would conflict with the closure's capture).
        let defined: std::collections::HashSet<&str> = functions
            .iter()
            .flat_map(|f| &f.symbols)
            .map(|s| s.as_str())
            .chain(data.symbols.iter().map(|(n, _)| n.as_str()))
            .collect();
        let mut seen: std::collections::HashSet<&str> = std::collections::HashSet::new();
        for name in undefined_externals {
            if referenced.contains(name.as_str())
                && !defined.contains(name.as_str())
                && seen.insert(name.as_str())
            {
                push_sym(
                    name,
                    false,
                    SymbolBinding::Global,
                    SymbolPlace::Undefined,
                    0,
                    0,
                    &mut symbols,
                );
            }
        }
    }

    // --- #1180: the locals-first order, from the ONE shared rule. ---
    // ELF requires every STB_LOCAL before every non-local (`sh_info` = first
    // non-local); Mach-O's LC_DYSYMTAB requires the same partition. Applying
    // `synth_core::backend::locals_first` HERE — the function the ARM builder
    // applies since #656 — means neither writer sorts, and the name → index
    // map is rewritten through the permutation so every relocation below
    // resolves against the emitted order. A stable sort keeps the natural
    // order inside each class, and the undefined externals (all GLOBAL, pushed
    // last) stay last, which is the defined-then-undefined half of the
    // Mach-O partition.
    let locals = locals_first(symbols.iter().map(|s| s.binding));
    let symbols: Vec<PlannedSymbol> = locals
        .order
        .iter()
        .map(|&old| symbols[old].clone())
        .collect();
    for idx in sym_index.values_mut() {
        *idx = locals.old_to_new[*idx];
    }

    // --- relocations, rebased to .text and resolved to a symbol index. ---
    let mut relocs: Vec<PlannedReloc> = Vec::new();
    for (i, f) in functions.iter().enumerate() {
        for r in &f.relocations {
            // A relocation against a symbol this object does not place: silently
            // dropping it would ship the unrelocated placeholder — `bl #0`
            // branches to itself, `adrp #0` addresses the WRONG page (a silent
            // miscompile, not a link error). This is NOT an internal invariant
            // (#1013): it is reachable from ordinary input whenever a retained
            // function calls a function the backend loud-declined (gale's
            // httparse corpus repro: a VCR-A64-CF-001 `br_table` decline of
            // `func_0`, called by `parse`). Refuse via `Err` — the #952 clean
            // non-zero exit with a reason naming the symbol — never a panic,
            // which reads as a synth bug and exits 101. (#1017: undefined
            // externals now EXIST in this builder, but only for the driver's
            // explicit allowlist — the module's imported functions. A symbol
            // that is neither placed nor allowlisted, i.e. a loud-declined
            // LOCAL callee, keeps this refusal.)
            //
            // #1168: this message used to assert "the symbol was declined
            // earlier; see the preceding warning" — a CAUSE, not an
            // observation. On the .wast exports-only merge the callee was
            // never declined, just never compiled, and there was no preceding
            // warning: the message named one that did not exist and sent the
            // investigator down the wrong path. The builder only knows the
            // symbol is unplaced; it says exactly that and lists the two ways
            // it can happen. The driver-level gate (#1102/#1168 in
            // synth-cli) normally refuses both before this builder runs, so
            // reaching this branch means a target slipped that gate.
            let Some(&sidx) = sym_index.get(&r.symbol) else {
                return Err(BackendError::CompilationFailed(format!(
                    "aarch64 ELF builder: relocation at .text+{} targets symbol \
                     '{}', which this object does not place — refusing to ship an \
                     unrelocated placeholder (#851/#1013). The symbol is neither a \
                     function this object defines nor an allowlisted import: \
                     either the function was loud-declined (then a 'skipping \
                     function' warning precedes this) or it was never compiled \
                     into this object at all (#1168 — no warning precedes this; \
                     the reachable-callgraph closure should have retained it). \
                     The driver-level #1102/#1168 gate normally refuses both \
                     before this builder runs.",
                    func_off[i] + r.offset as u64,
                    r.symbol
                )));
            };
            relocs.push(PlannedReloc {
                offset: func_off[i] + r.offset as u64,
                kind: r.kind,
                symbol: sidx,
            });
        }
    }

    Ok(ObjectPlan {
        text,
        data: data.bytes.clone(),
        symbols,
        relocs,
    })
}

/// Build an `EM_AARCH64` `ET_REL` object exposing each function's symbols as
/// GLOBAL `STT_FUNC` in `.text`, plus a `.rela.text` for any call relocations.
/// Data-free shorthand for [`build_relocatable_object_with_data`] — a module
/// with no globals emits byte-identical output to the pre-lane-L3 builder.
///
/// #1013: `Err` (never a panic) when a relocation targets a symbol this object
/// does not place — see [`build_relocatable_object_with_data`].
pub fn build_relocatable_object(functions: &[ElfFunction]) -> Result<Vec<u8>, BackendError> {
    build_relocatable_object_with_data(functions, &DataBlob::default())
}

/// Data-only shorthand for [`build_relocatable_object_full`] with no undefined
/// externals — every pre-#1017 caller keeps byte-identical output.
pub fn build_relocatable_object_with_data(
    functions: &[ElfFunction],
    data: &DataBlob,
) -> Result<Vec<u8>, BackendError> {
    build_relocatable_object_full(functions, data, &[])
}

/// Build an `EM_AARCH64` `ET_REL` object with an optional synth-emitted `.data`
/// section (#851 lane L3 — the WASM globals region, see [`DataBlob`]).
///
/// Section indices: `[0]=NULL [1]=.text [2]=.symtab [3]=.strtab [4]=.shstrtab`,
/// then `.data` (when non-empty) and `.rela.text` (when non-empty) appended in
/// that order. An EMPTY `DataBlob` reproduces the previous layout exactly, so
/// every module without globals stays byte-identical (the frozen-anchor
/// contract).
///
/// # Errors (#1013)
///
/// A relocation targeting a symbol this object does not place is `Err`, never
/// a panic: it is REACHABLE from ordinary input (a retained function calling a
/// function the backend loud-declined, e.g. VCR-A64-CF-001's `br_table`
/// threshold — gale's `httparse` corpus repro), so it must surface as the
/// #952-style clean refusal (exit 1, reason naming the symbol), not exit 101
/// with a `RUST_BACKTRACE` note that reads as an internal bug. The DECISION is
/// unchanged — an unrelocated `bl #0`/`adrp #0` placeholder is the
/// silent-miscompile class and never ships.
///
/// # Undefined externals (#1017 / VCR-REACH-002)
///
/// `undefined_externals` is the driver-supplied allowlist of symbols this
/// object may legitimately NOT place: the wasm module's imported functions,
/// under their import FIELD names (the ARM `--relocatable` #173/#197 contract,
/// ported). A relocation targeting one is emitted against a GLOBAL `STT_FUNC`
/// `SHN_UNDEF` symbol the host linker resolves — exactly the wasm2c/Wasker
/// undefined-symbol pattern. The list is an ALLOWLIST, not a policy change: a
/// relocation against any symbol that is neither placed nor listed still gets
/// the #1013 clean refusal, so a loud-declined LOCAL callee can never silently
/// become a link-time external. An external in the list that no relocation
/// references is NOT emitted (no symtab noise; unreferenced imports stay
/// invisible, matching ARM). A listed name that IS placed by this object binds
/// to the placed symbol (ARM parity — the defined symbol wins).
pub fn build_relocatable_object_full(
    functions: &[ElfFunction],
    data: &DataBlob,
    undefined_externals: &[String],
) -> Result<Vec<u8>, BackendError> {
    // RQ-64-MACHO: everything below the container line comes from the ONE plan
    // the Mach-O writer also consumes — see `plan_object`.
    let plan = plan_object(functions, data, undefined_externals)?;
    let text = &plan.text;

    let have_data = !data.bytes.is_empty();
    // Section indices. [0]=NULL [1]=.text [2]=.symtab [3]=.strtab [4]=.shstrtab;
    // `.data` (when present) is 5 and `.rela.text` follows. Fixing `.data` BEFORE
    // `.rela.text` keeps the data symbols' `st_shndx` independent of whether the
    // module has relocations.
    let idx_data: u16 = 5;

    // --- .strtab + .symtab: one symbol per planned symbol, PLAN ORDER — which
    // is already locals-first (`plan_object` applied the shared
    // `locals_first`), so ELF's "every STB_LOCAL precedes every non-local,
    // `sh_info` = index of the first non-local" holds by READING the plan,
    // never by sorting here (#1180). ---
    // st_info = (bind << 4) | type: the bind nibble IS `SymbolBinding`'s
    // discriminant (LOCAL=0, GLOBAL=1) and the type nibble is FUNC(2) /
    // OBJECT(1) — so a `func_N` label is 0x02, an export 0x12, the
    // `__synth_globals` / funcref-table OBJECTs 0x01, an import 0x12 at
    // SHN_UNDEF. shndx = 1 (.text) for code, `idx_data` for the `.data`
    // symbols, 0 (SHN_UNDEF) for the #1017 externals. Plan index i is ELF
    // symbol index i+1 (index 0 is the null symbol).
    let symtab_sh_info = plan.local_count() as u32 + 1;
    let mut strtab: Vec<u8> = vec![0];
    let mut symtab: Vec<u8> = Vec::new();
    symtab.extend_from_slice(&[0u8; SYM_SIZE]); // null symbol at index 0
    for f in &plan.symbols {
        let name_off = strtab.len() as u32;
        strtab.extend_from_slice(f.name.as_bytes());
        strtab.push(0);
        // #851 lane L3: the funcref table and the `.data` region are OBJECT.
        // #1180: the binding is the PLAN's — read, never decided here.
        let stt: u8 = if f.is_object { 1 } else { 2 };
        let info = ((f.binding as u8) << 4) | stt;
        let shndx: u16 = match f.place {
            SymbolPlace::Text => 1,
            SymbolPlace::Data => idx_data,
            SymbolPlace::Undefined => 0,
        };
        push_u32(&mut symtab, name_off); // st_name
        symtab.push(info); // st_info
        symtab.push(0); // st_other
        push_u16(&mut symtab, shndx); // st_shndx
        push_u64(&mut symtab, f.value); // st_value
        push_u64(&mut symtab, f.size); // st_size
    }

    // --- .rela.text: one entry per planned relocation. ---
    // ELF64 packs r_info = (sym_index << 32) | type (sym in the HIGH word).
    let mut rela: Vec<u8> = Vec::new();
    for r in &plan.relocs {
        // NO wildcard: a relocation kind this backend cannot express must
        // fail loudly here rather than be silently dropped (which would ship
        // an unrelocated `bl #0` / `adrp #0` — a branch-to-self or a wrong
        // address, the silent-miscompile class).
        let r_type = match r.kind {
            RelocKind::AArch64Call26 => R_AARCH64_CALL26,
            RelocKind::AArch64Jump26 => R_AARCH64_JUMP26,
            RelocKind::AArch64AdrPrelPgHi21 => R_AARCH64_ADR_PREL_PG_HI21,
            RelocKind::AArch64AddAbsLo12Nc => R_AARCH64_ADD_ABS_LO12_NC,
            other => panic!(
                "aarch64 ELF builder cannot emit relocation kind {other:?} \
                 (#851): only the four AArch64 kinds are expressible"
            ),
        };
        let sidx = r.symbol as u64 + 1;
        let r_info = (sidx << 32) | (r_type as u64);
        push_u64(&mut rela, r.offset);
        push_u64(&mut rela, r_info);
        push_u64(&mut rela, 0); // r_addend = 0
    }
    let have_rela = !rela.is_empty();

    // --- .shstrtab: section header names. ---
    let mut shstrtab: Vec<u8> = vec![0];
    let add_shstr = |sh: &mut Vec<u8>, s: &str| -> u32 {
        let o = sh.len() as u32;
        sh.extend_from_slice(s.as_bytes());
        sh.push(0);
        o
    };
    let n_text = add_shstr(&mut shstrtab, ".text");
    // .rela.text must precede .symtab in the string table only for readability;
    // order is arbitrary. Emit its name only when present.
    let n_rela = if have_rela {
        add_shstr(&mut shstrtab, ".rela.text")
    } else {
        0
    };
    let n_symtab = add_shstr(&mut shstrtab, ".symtab");
    let n_strtab = add_shstr(&mut shstrtab, ".strtab");
    let n_shstrtab = add_shstr(&mut shstrtab, ".shstrtab");
    let n_data = if have_data {
        add_shstr(&mut shstrtab, ".data")
    } else {
        0
    };

    // --- Section indices. ---
    // [0]=NULL [1]=.text [2]=.symtab [3]=.strtab [4]=.shstrtab, then (when
    // present) .data at 5 and .rela.text last. Keeping
    // .text=1/.symtab=2/.strtab=3/.shstrtab=4 stable preserves the milestone-1b
    // layout for call-free, globals-free modules (byte-identical) — the symtab
    // st_shndx=1 and e_shstrndx=4 are unchanged.
    // .symtab is section 2 (the .rela.text `sh_link`).
    let idx_symtab = 2u32;

    // --- Layout: ehdr | .text | .symtab | .strtab | .shstrtab | [.data] |
    //             [.rela] | shdrs. ---
    let text_off = EHDR_SIZE;
    let symtab_off = text_off + text.len();
    let strtab_off = symtab_off + symtab.len();
    let shstrtab_off = strtab_off + strtab.len();
    // 8-align .data (an i64 global slot must land naturally aligned).
    let data_off = {
        let base = shstrtab_off + shstrtab.len();
        base.div_ceil(8) * 8
    };
    let data_pad = if have_data {
        data_off - (shstrtab_off + shstrtab.len())
    } else {
        0
    };
    let after_data = if have_data {
        data_off + data.bytes.len()
    } else {
        shstrtab_off + shstrtab.len()
    };
    // 8-align .rela.text (SHT_RELA entries are 8-aligned).
    let rela_off = after_data.div_ceil(8) * 8;
    let rela_pad = rela_off - after_data;
    let after_content = if have_rela {
        rela_off + rela.len()
    } else {
        after_data
    };
    // 8-align the section-header table.
    let shdr_off = after_content.div_ceil(8) * 8;
    let shdr_pad = shdr_off - after_content;
    let num_sections: u16 = 5 + u16::from(have_data) + u16::from(have_rela);

    let mut out: Vec<u8> = Vec::new();

    // ELF header (Elf64_Ehdr).
    out.extend_from_slice(&[0x7F, b'E', b'L', b'F']); // magic
    out.push(2); // EI_CLASS = ELFCLASS64
    out.push(1); // EI_DATA = ELFDATA2LSB
    out.push(1); // EI_VERSION
    out.push(0); // EI_OSABI = SYSV
    out.extend_from_slice(&[0u8; 8]); // EI_ABIVERSION + pad
    push_u16(&mut out, 1); // e_type = ET_REL
    push_u16(&mut out, 183); // e_machine = EM_AARCH64
    push_u32(&mut out, 1); // e_version
    push_u64(&mut out, 0); // e_entry
    push_u64(&mut out, 0); // e_phoff
    push_u64(&mut out, shdr_off as u64); // e_shoff
    push_u32(&mut out, 0); // e_flags
    push_u16(&mut out, EHDR_SIZE as u16); // e_ehsize
    push_u16(&mut out, 0); // e_phentsize
    push_u16(&mut out, 0); // e_phnum
    push_u16(&mut out, SHDR_SIZE as u16); // e_shentsize
    push_u16(&mut out, num_sections); // e_shnum
    push_u16(&mut out, 4); // e_shstrndx = .shstrtab (section 4)
    debug_assert_eq!(out.len(), EHDR_SIZE);

    // Section data, in the order laid out above.
    out.extend_from_slice(text);
    out.extend_from_slice(&symtab);
    out.extend_from_slice(&strtab);
    out.extend_from_slice(&shstrtab);
    if have_data {
        out.extend_from_slice(&vec![0u8; data_pad]);
        out.extend_from_slice(&data.bytes);
    }
    if have_rela {
        out.extend_from_slice(&vec![0u8; rela_pad]);
        out.extend_from_slice(&rela);
    }
    out.extend_from_slice(&vec![0u8; shdr_pad]);
    debug_assert_eq!(out.len(), shdr_off);

    // Section headers (Elf64_Shdr).
    let mut shdr =
        |name, sh_type, flags, offset: usize, size: usize, link, info, align, entsize| {
            push_u32(&mut out, name);
            push_u32(&mut out, sh_type);
            push_u64(&mut out, flags);
            push_u64(&mut out, 0); // sh_addr
            push_u64(&mut out, offset as u64);
            push_u64(&mut out, size as u64);
            push_u32(&mut out, link);
            push_u32(&mut out, info);
            push_u64(&mut out, align);
            push_u64(&mut out, entsize);
        };
    // [0] NULL
    shdr(0, 0, 0, 0, 0, 0, 0, 0, 0);
    // [1] .text — PROGBITS, ALLOC|EXECINSTR (0x2|0x4), align 4
    shdr(n_text, 1, 0x6, text_off, text.len(), 0, 0, 4, 0);
    // [2] .symtab — SYMTAB(2), link=.strtab(3), info=first non-local symbol
    // index (#1180: `plan.local_count() + 1`, the null symbol counting as
    // local), align 8
    shdr(
        n_symtab,
        2,
        0,
        symtab_off,
        symtab.len(),
        3,
        symtab_sh_info,
        8,
        SYM_SIZE as u64,
    );
    // [3] .strtab — STRTAB(3)
    shdr(n_strtab, 3, 0, strtab_off, strtab.len(), 0, 0, 1, 0);
    // [4] .shstrtab — STRTAB(3)
    shdr(n_shstrtab, 3, 0, shstrtab_off, shstrtab.len(), 0, 0, 1, 0);
    // [5] .data — PROGBITS(1), ALLOC|WRITE (0x2|0x1), align 8. The synth-emitted
    // globals region (#851 lane L3): its bytes ARE the initial values, so no
    // startup, no linker script and no base-register precondition is needed.
    if have_data {
        shdr(n_data, 1, 0x3, data_off, data.bytes.len(), 0, 0, 8, 0);
    }
    // [5|6] .rela.text — RELA(4), link=.symtab(2), info=.text(1), align 8. Only
    // emitted when there is at least one relocation.
    if have_rela {
        shdr(
            n_rela,
            4,
            0,
            rela_off,
            rela.len(),
            idx_symtab,
            1, // info = .text section index
            8,
            RELA_SIZE as u64,
        );
    }

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn well_formed_header_and_symbols() {
        let obj = build_relocatable_object(&[
            ElfFunction::code(
                vec!["func_0".into(), "add".into()],
                vec![0, 0, 1, 0x0B, 0xE0, 0x03, 9, 0x2A, 0xC0, 0x03, 0x5F, 0xD6],
                vec![],
            ),
            ElfFunction::code(
                vec!["func_1".into(), "sub".into()],
                vec![0x62, 0, 4, 0x4B, 0xC0, 0x03, 0x5F, 0xD6],
                vec![],
            ),
        ])
        .expect("elf build");
        // ELF magic + class64 + LSB.
        assert_eq!(&obj[0..4], &[0x7F, b'E', b'L', b'F']);
        assert_eq!(obj[4], 2); // ELFCLASS64
        assert_eq!(obj[5], 1); // LSB
        // e_type = ET_REL, e_machine = EM_AARCH64.
        assert_eq!(u16::from_le_bytes([obj[16], obj[17]]), 1);
        assert_eq!(u16::from_le_bytes([obj[18], obj[19]]), 183);
        // e_shnum = 5 (no relocations).
        assert_eq!(u16::from_le_bytes([obj[60], obj[61]]), 5);
        // The object must contain all four symbol names.
        let s = String::from_utf8_lossy(&obj);
        assert!(s.contains("add") && s.contains("sub"));
        assert!(s.contains("func_0") && s.contains("func_1"));
    }

    #[test]
    fn call_reloc_produces_rela_text() {
        // A caller (func_1) with a `bl func_0` at byte offset 0.
        let obj = build_relocatable_object(&[
            ElfFunction::code(vec!["func_0".into()], vec![0xC0, 0x03, 0x5F, 0xD6], vec![]),
            ElfFunction::code(
                vec!["func_1".into(), "run".into()],
                vec![0x00, 0x00, 0x00, 0x94, 0xC0, 0x03, 0x5F, 0xD6], // bl #0 ; ret
                vec![CodeRelocation {
                    offset: 0,
                    symbol: "func_0".into(),
                    kind: RelocKind::AArch64Call26,
                }],
            ),
        ])
        .expect("elf build");
        // e_shnum = 6 (adds .rela.text).
        assert_eq!(u16::from_le_bytes([obj[60], obj[61]]), 6);
        let s = String::from_utf8_lossy(&obj);
        assert!(s.contains(".rela.text"));
        // The reloc r_offset points at func_1's bl: func_0 is 4 bytes, so func_1
        // starts at .text offset 4, reloc at 4+0 = 4. The r_info encodes the
        // symbol index of func_0 (index 1: null=0, func_0=1) in the high word and
        // type 283 in the low word. We can't easily locate the rela bytes by
        // structure here, but readelf -r on the emitted .o verifies it (the
        // differential harness links + runs, the ultimate check).
        assert_eq!(R_AARCH64_CALL26, 283);
    }

    /// Minimal ELF64 section walk: `(name, sh_type, sh_flags, offset, size)`.
    fn sections(obj: &[u8]) -> Vec<(String, u32, u64, usize, usize)> {
        let rd_u16 = |o: usize| u16::from_le_bytes([obj[o], obj[o + 1]]) as usize;
        let rd_u64 = |o: usize| u64::from_le_bytes(obj[o..o + 8].try_into().unwrap());
        let shoff = rd_u64(40) as usize;
        let shnum = rd_u16(60);
        let shstrndx = rd_u16(62);
        let hdr = |i: usize| shoff + i * SHDR_SIZE;
        let strtab_off = rd_u64(hdr(shstrndx) + 24) as usize;
        (0..shnum)
            .map(|i| {
                let b = hdr(i);
                let name_off =
                    strtab_off + u32::from_le_bytes(obj[b..b + 4].try_into().unwrap()) as usize;
                let end = obj[name_off..].iter().position(|c| *c == 0).unwrap() + name_off;
                (
                    String::from_utf8_lossy(&obj[name_off..end]).into_owned(),
                    u32::from_le_bytes(obj[b + 4..b + 8].try_into().unwrap()),
                    rd_u64(b + 8),
                    rd_u64(b + 24) as usize,
                    rd_u64(b + 32) as usize,
                )
            })
            .collect()
    }

    /// #851 lane L3: a `DataBlob` produces a real ALLOC|WRITE `.data` section
    /// holding EXACTLY the supplied bytes, plus a `STT_OBJECT` symbol pointing
    /// into it. This is the substrate that makes globals precondition-free —
    /// the initial values ship in the object.
    #[test]
    fn data_blob_emits_alloc_write_data_section_and_object_symbol() {
        let blob = DataBlob {
            bytes: vec![7, 0, 0, 0, 0, 0, 0, 0, 0xFF, 0xFF, 0, 0, 0, 0, 0, 0],
            symbols: vec![("__synth_globals".into(), 0)],
        };
        let obj = build_relocatable_object_with_data(
            &[ElfFunction::code(
                vec!["func_0".into(), "run".into()],
                vec![0xC0, 0x03, 0x5F, 0xD6],
                vec![],
            )],
            &blob,
        )
        .expect("elf build");
        let secs = sections(&obj);
        let data = secs
            .iter()
            .find(|s| s.0 == ".data")
            .expect(".data section missing");
        assert_eq!(data.1, 1, ".data must be SHT_PROGBITS");
        assert_eq!(data.2, 0x3, ".data must be SHF_ALLOC|SHF_WRITE");
        assert_eq!(&obj[data.3..data.3 + data.4], &blob.bytes[..]);
        // The `__synth_globals` symbol must be STT_OBJECT (0x11) in .data.
        let symtab = secs.iter().find(|s| s.0 == ".symtab").unwrap();
        let strtab = secs.iter().find(|s| s.0 == ".strtab").unwrap();
        let data_idx = secs.iter().position(|s| s.0 == ".data").unwrap() as u16;
        let mut found = false;
        for i in 0..symtab.4 / SYM_SIZE {
            let b = symtab.3 + i * SYM_SIZE;
            let no = strtab.3 + u32::from_le_bytes(obj[b..b + 4].try_into().unwrap()) as usize;
            let end = obj[no..].iter().position(|c| *c == 0).unwrap() + no;
            if &obj[no..end] == b"__synth_globals" {
                // #1180: LOCAL (bind 0) OBJECT (type 1) — a second synth object
                // carries its own `__synth_globals`.
                assert_eq!(obj[b + 4], 0x01, "globals symbol must be LOCAL OBJECT");
                assert_eq!(u16::from_le_bytes([obj[b + 6], obj[b + 7]]), data_idx);
                found = true;
            }
        }
        assert!(found, "__synth_globals symbol not emitted");
    }

    /// A globals-free, call-free module must be BYTE-IDENTICAL to the
    /// pre-lane-L3 builder — the frozen-anchor contract (an empty `DataBlob`
    /// adds no section, no symbol, no padding).
    #[test]
    fn empty_data_blob_is_byte_identical_to_the_data_free_builder() {
        let f = || {
            vec![ElfFunction::code(
                vec!["func_0".into(), "run".into()],
                vec![0xC0, 0x03, 0x5F, 0xD6],
                vec![],
            )]
        };
        assert_eq!(
            build_relocatable_object(&f()).expect("elf build"),
            build_relocatable_object_with_data(&f(), &DataBlob::default()).expect("elf build")
        );
        assert_eq!(
            u16::from_le_bytes([
                build_relocatable_object(&f()).expect("elf build")[60],
                build_relocatable_object(&f()).expect("elf build")[61]
            ]),
            5,
            "no .data / no .rela.text → the original 5-section layout"
        );
    }

    /// #851 lane L3: the funcref-table trampoline blob is DATA in `.text` —
    /// its symbol must be `STT_OBJECT`, and a `JUMP26` relocation must map to
    /// ELF type 282 (not the 283 a `bl` uses).
    #[test]
    fn func_table_object_symbol_and_jump26_reloc_type() {
        let obj = build_relocatable_object(&[
            ElfFunction::code(vec!["func_0".into()], vec![0xC0, 0x03, 0x5F, 0xD6], vec![]),
            ElfFunction {
                symbols: vec!["__synth_func_table".into()],
                // slot 0: [class id 1][b func_0]
                code: vec![1, 0, 0, 0, 0x00, 0x00, 0x00, 0x14],
                relocations: vec![CodeRelocation {
                    offset: 4,
                    symbol: "func_0".into(),
                    kind: RelocKind::AArch64Jump26,
                }],
                is_object: true,
            },
        ])
        .expect("elf build");
        let secs = sections(&obj);
        let rela = secs.iter().find(|s| s.0 == ".rela.text").unwrap();
        let r_info = u64::from_le_bytes(obj[rela.3 + 8..rela.3 + 16].try_into().unwrap());
        assert_eq!(
            (r_info & 0xFFFF_FFFF) as u32,
            R_AARCH64_JUMP26,
            "a trampoline `b func_N` must relocate as JUMP26 (282), not CALL26"
        );
        let symtab = secs.iter().find(|s| s.0 == ".symtab").unwrap();
        let strtab = secs.iter().find(|s| s.0 == ".strtab").unwrap();
        let mut found = false;
        for i in 0..symtab.4 / SYM_SIZE {
            let b = symtab.3 + i * SYM_SIZE;
            let no = strtab.3 + u32::from_le_bytes(obj[b..b + 4].try_into().unwrap()) as usize;
            let end = obj[no..].iter().position(|c| *c == 0).unwrap() + no;
            if &obj[no..end] == b"__synth_func_table" {
                // #1180: LOCAL OBJECT — the table is reached only by this
                // object's own adrp/add pair.
                assert_eq!(obj[b + 4], 0x01, "table symbol must be LOCAL OBJECT");
                found = true;
            }
        }
        assert!(found, "__synth_func_table symbol not emitted");
    }

    /// The ADRP/ADD symbol-address pair maps to ELF types 275 / 277.
    #[test]
    fn adrp_add_pair_reloc_types() {
        let obj = build_relocatable_object_with_data(
            &[ElfFunction::code(
                vec!["run".into()],
                vec![0; 8],
                vec![
                    CodeRelocation {
                        offset: 0,
                        symbol: "__synth_globals".into(),
                        kind: RelocKind::AArch64AdrPrelPgHi21,
                    },
                    CodeRelocation {
                        offset: 4,
                        symbol: "__synth_globals".into(),
                        kind: RelocKind::AArch64AddAbsLo12Nc,
                    },
                ],
            )],
            &DataBlob {
                bytes: vec![0; 8],
                symbols: vec![("__synth_globals".into(), 0)],
            },
        )
        .expect("elf build");
        let secs = sections(&obj);
        let rela = secs.iter().find(|s| s.0 == ".rela.text").unwrap();
        let ty = |i: usize| {
            (u64::from_le_bytes(
                obj[rela.3 + i * RELA_SIZE + 8..rela.3 + i * RELA_SIZE + 16]
                    .try_into()
                    .unwrap(),
            ) & 0xFFFF_FFFF) as u32
        };
        assert_eq!(ty(0), R_AARCH64_ADR_PREL_PG_HI21);
        assert_eq!(ty(1), R_AARCH64_ADD_ABS_LO12_NC);
    }

    /// #1013: a relocation against a symbol this object does not place — the
    /// gale corpus shape, a retained function calling a loud-declined one —
    /// must be `Err` (a clean refusal the CLI turns into exit 1), NEVER a
    /// panic (exit 101, reads as a synth bug). The message must name the
    /// dangling symbol and the #851 class so the refusal is actionable.
    #[test]
    fn dangling_reloc_symbol_is_err_not_panic() {
        let err = build_relocatable_object(&[ElfFunction::code(
            vec!["func_1".into(), "parse".into()],
            vec![0x00, 0x00, 0x00, 0x94, 0xC0, 0x03, 0x5F, 0xD6], // bl #0 ; ret
            vec![CodeRelocation {
                offset: 0,
                symbol: "func_0".into(), // declined — not placed in this object
                kind: RelocKind::AArch64Call26,
            }],
        )])
        .expect_err("a dangling relocation must refuse, not build");
        let msg = err.to_string();
        assert!(
            msg.contains("targets symbol 'func_0'")
                && msg.contains("does not place")
                && msg.contains("#851"),
            "refusal must name the dangling symbol and the #851 class: {msg}"
        );
    }

    /// #1017: a relocation against an ALLOWLISTED external builds, emitting a
    /// GLOBAL `STT_FUNC` symbol at `SHN_UNDEF` (shndx 0) that the relocation
    /// binds to — the wasm2c/Wasker undefined-symbol pattern, ARM #173/#197
    /// ported.
    #[test]
    fn allowlisted_external_emits_shn_undef_symbol_1017() {
        let obj = build_relocatable_object_full(
            &[ElfFunction::code(
                vec!["func_1".into(), "run".into()],
                vec![0x00, 0x00, 0x00, 0x94, 0xC0, 0x03, 0x5F, 0xD6], // bl #0 ; ret
                vec![CodeRelocation {
                    offset: 0,
                    symbol: "host_add".into(),
                    kind: RelocKind::AArch64Call26,
                }],
            )],
            &DataBlob::default(),
            &["host_add".into()],
        )
        .expect("an allowlisted external must build");
        // Symbols: [0]=null [1]=func_1 [2]=run [3]=host_add (SHN_UNDEF).
        let symtab_off = EHDR_SIZE + 8; // ehdr | .text (8 bytes) | .symtab
        let sym3 = symtab_off + 3 * SYM_SIZE;
        assert_eq!(obj[sym3 + 4], 0x12, "GLOBAL STT_FUNC");
        assert_eq!(
            u16::from_le_bytes([obj[sym3 + 6], obj[sym3 + 7]]),
            0,
            "st_shndx must be SHN_UNDEF"
        );
        // The single RELA entry binds to symbol index 3 with type CALL26.
        let strtab: &[u8] = &obj;
        assert!(
            strtab
                .windows(b"host_add\0".len())
                .any(|w| w == b"host_add\0"),
            "external name in .strtab"
        );
        let rela = sections(&obj)
            .into_iter()
            .find(|(n, ..)| n == ".rela.text")
            .expect(".rela.text present");
        let (off, len) = (rela.3, rela.4);
        assert_eq!(len, RELA_SIZE);
        let r_info = u64::from_le_bytes(obj[off + 8..off + 16].try_into().unwrap());
        assert_eq!(r_info >> 32, 3, "reloc binds to the SHN_UNDEF symbol");
        assert_eq!((r_info & 0xFFFF_FFFF) as u32, R_AARCH64_CALL26);
    }

    /// #1017: the allowlist is NOT a policy change — a relocation against a
    /// symbol that is neither placed nor allowlisted keeps the #1013 refusal
    /// even when OTHER externals are allowlisted, so a loud-declined local
    /// callee can never silently become a link-time external.
    #[test]
    fn unlisted_dangling_symbol_still_refuses_1017() {
        let err = build_relocatable_object_full(
            &[ElfFunction::code(
                vec!["func_1".into()],
                vec![0x00, 0x00, 0x00, 0x94, 0xC0, 0x03, 0x5F, 0xD6],
                vec![CodeRelocation {
                    offset: 0,
                    symbol: "func_0".into(), // declined local — NOT allowlisted
                    kind: RelocKind::AArch64Call26,
                }],
            )],
            &DataBlob::default(),
            &["host_add".into()], // allowlist names something else
        )
        .expect_err("an unlisted dangling symbol must still refuse");
        assert!(err.to_string().contains("targets symbol 'func_0'"));
    }

    /// #1017: an allowlisted external no relocation references is NOT emitted
    /// (no symtab noise), and an EMPTY allowlist is byte-identical to the
    /// two-argument builder (the frozen contract for import-free modules).
    #[test]
    fn unreferenced_external_and_empty_allowlist_are_invisible_1017() {
        let f = || {
            vec![ElfFunction::code(
                vec!["func_0".into(), "add".into()],
                vec![0x20, 0x00, 0x02, 0x0B, 0xC0, 0x03, 0x5F, 0xD6],
                vec![],
            )]
        };
        let base = build_relocatable_object_with_data(&f(), &DataBlob::default()).unwrap();
        let with_unreferenced =
            build_relocatable_object_full(&f(), &DataBlob::default(), &["host_add".into()])
                .unwrap();
        let with_empty = build_relocatable_object_full(&f(), &DataBlob::default(), &[]).unwrap();
        assert_eq!(
            base, with_unreferenced,
            "unreferenced external is invisible"
        );
        assert_eq!(base, with_empty, "empty allowlist is byte-identical");
    }

    /// `.symtab` as `(name, st_info, st_shndx, st_value)` per non-null entry,
    /// in emitted order, plus the section's `sh_info`.
    fn symtab(obj: &[u8]) -> (Vec<(String, u8, u16, u64)>, u32) {
        let secs = sections(obj);
        let rd_u64 = |o: usize| u64::from_le_bytes(obj[o..o + 8].try_into().unwrap());
        let shoff = rd_u64(40) as usize;
        let sym_idx = secs.iter().position(|s| s.0 == ".symtab").unwrap();
        let sh_info = u32::from_le_bytes(
            obj[shoff + sym_idx * SHDR_SIZE + 44..shoff + sym_idx * SHDR_SIZE + 48]
                .try_into()
                .unwrap(),
        );
        let symtab = &secs[sym_idx];
        let strtab = secs.iter().find(|s| s.0 == ".strtab").unwrap();
        let mut out = Vec::new();
        for i in 1..symtab.4 / SYM_SIZE {
            let b = symtab.3 + i * SYM_SIZE;
            let no = strtab.3 + u32::from_le_bytes(obj[b..b + 4].try_into().unwrap()) as usize;
            let end = obj[no..].iter().position(|c| *c == 0).unwrap() + no;
            out.push((
                String::from_utf8_lossy(&obj[no..end]).into_owned(),
                obj[b + 4],
                u16::from_le_bytes([obj[b + 6], obj[b + 7]]),
                rd_u64(b + 8),
            ));
        }
        (out, sh_info)
    }

    /// #1180 / RQ-65-FUNCN: the binding rule, the locals-first order, `sh_info`
    /// and the relocation remap across the permutation — on a fixture that
    /// interleaves every class (an exported function, a non-exported helper,
    /// the funcref table, a `.data` region, an import). Before #1180 every
    /// symbol here was 0x12/0x11 and `sh_info` was 1, which is the
    /// `duplicate symbol: func_1` collision when two such objects meet.
    #[test]
    fn func_n_local_exports_and_imports_global_locals_first_sh_info_1180() {
        let obj = build_relocatable_object_full(
            &[
                ElfFunction::code(
                    vec!["func_1".into(), "add".into()],
                    vec![0x00, 0x00, 0x00, 0x94, 0xC0, 0x03, 0x5F, 0xD6], // bl host_add; ret
                    vec![CodeRelocation {
                        offset: 0,
                        symbol: "host_add".into(),
                        kind: RelocKind::AArch64Call26,
                    }],
                ),
                ElfFunction::code(
                    vec!["func_2".into()],
                    vec![0x00, 0x00, 0x00, 0x90, 0x00, 0x00, 0x00, 0x91], // adrp; add
                    vec![
                        CodeRelocation {
                            offset: 0,
                            symbol: "__synth_globals".into(),
                            kind: RelocKind::AArch64AdrPrelPgHi21,
                        },
                        CodeRelocation {
                            offset: 4,
                            symbol: "__synth_globals".into(),
                            kind: RelocKind::AArch64AddAbsLo12Nc,
                        },
                    ],
                ),
                ElfFunction {
                    symbols: vec!["__synth_func_table".into()],
                    code: vec![1, 0, 0, 0, 0x00, 0x00, 0x00, 0x14], // [class 1][b func_1]
                    relocations: vec![CodeRelocation {
                        offset: 4,
                        symbol: "func_1".into(),
                        kind: RelocKind::AArch64Jump26,
                    }],
                    is_object: true,
                },
            ],
            &DataBlob {
                bytes: vec![0; 8],
                symbols: vec![("__synth_globals".into(), 0)],
            },
            &["host_add".into()],
        )
        .expect("elf build");
        let (syms, sh_info) = symtab(&obj);
        let names: Vec<&str> = syms.iter().map(|s| s.0.as_str()).collect();
        // Locals first (natural order within the class), then the export, then
        // the import — the stable locals-first permutation of the natural
        // (aliases, data, externals) order.
        assert_eq!(
            names,
            vec![
                "func_1",
                "func_2",
                "__synth_func_table",
                "__synth_globals",
                "add",
                "host_add"
            ]
        );
        let bind = |name: &str| syms.iter().find(|s| s.0 == name).unwrap().1 >> 4;
        let ty = |name: &str| syms.iter().find(|s| s.0 == name).unwrap().1 & 0xF;
        assert_eq!((bind("func_1"), ty("func_1")), (0, 2), "func_N: LOCAL FUNC");
        assert_eq!(
            (bind("func_2"), ty("func_2")),
            (0, 2),
            "helper label: LOCAL FUNC"
        );
        assert_eq!(
            (bind("__synth_func_table"), ty("__synth_func_table")),
            (0, 1),
            "table: LOCAL OBJECT"
        );
        assert_eq!(
            (bind("__synth_globals"), ty("__synth_globals")),
            (0, 1),
            "globals: LOCAL OBJECT"
        );
        assert_eq!((bind("add"), ty("add")), (1, 2), "export: GLOBAL FUNC");
        assert_eq!(
            (bind("host_add"), ty("host_add")),
            (1, 2),
            "import: GLOBAL FUNC"
        );
        assert_eq!(
            syms.iter().find(|s| s.0 == "host_add").unwrap().2,
            0,
            "import at SHN_UNDEF"
        );
        // The ELF rule: every STB_LOCAL precedes every non-local, and sh_info
        // is the index of the first non-local (null symbol = index 0).
        let first_global = syms.iter().position(|s| s.1 >> 4 != 0).unwrap();
        assert!(syms[first_global..].iter().all(|s| s.1 >> 4 != 0));
        assert_eq!(sh_info, first_global as u32 + 1);
        assert_eq!(sh_info, 5, "4 locals + the null symbol");
        // The alias pair shares one address, LOCAL and GLOBAL alike.
        assert_eq!(
            syms.iter().find(|s| s.0 == "func_1").unwrap().3,
            syms.iter().find(|s| s.0 == "add").unwrap().3
        );
        // Every relocation still names the RIGHT symbol after the permutation
        // (r_info's symbol index is 1-based into the emitted table).
        let secs = sections(&obj);
        let rela = secs.iter().find(|s| s.0 == ".rela.text").unwrap();
        let mut got = Vec::new();
        for i in 0..rela.4 / RELA_SIZE {
            let b = rela.3 + i * RELA_SIZE;
            let off = u64::from_le_bytes(obj[b..b + 8].try_into().unwrap());
            let info = u64::from_le_bytes(obj[b + 8..b + 16].try_into().unwrap());
            got.push((
                off,
                (info & 0xFFFF_FFFF) as u32,
                syms[(info >> 32) as usize - 1].0.clone(),
            ));
        }
        assert_eq!(
            got,
            vec![
                (0, R_AARCH64_CALL26, "host_add".to_string()),
                (8, R_AARCH64_ADR_PREL_PG_HI21, "__synth_globals".to_string()),
                (12, R_AARCH64_ADD_ABS_LO12_NC, "__synth_globals".to_string()),
                (20, R_AARCH64_JUMP26, "func_1".to_string()),
            ]
        );
    }

    /// #1180: two independently planned objects both define `func_1` — and
    /// both plan it LOCAL, which is what lets a host linker take the pair.
    /// (The link itself is the oracle's job; this pins the plan-level fact
    /// each container renders.)
    #[test]
    fn two_plans_both_define_func_1_local_1180() {
        let plan = |export: &str| {
            plan_object(
                &[ElfFunction::code(
                    vec!["func_1".into(), export.into()],
                    vec![0xC0, 0x03, 0x5F, 0xD6],
                    vec![],
                )],
                &DataBlob::default(),
                &[],
            )
            .unwrap()
        };
        for p in [plan("add"), plan("g")] {
            let f1 = p.symbols.iter().find(|s| s.name == "func_1").unwrap();
            assert_eq!(f1.binding, SymbolBinding::Local);
            assert_eq!(p.local_count(), 1);
            assert_eq!(p.symbols[1].binding, SymbolBinding::Global);
        }
    }
}
