//! The container-independent relocatable-object PLAN, and the ELF64 `ET_REL`
//! writer that lays a `RELA` object around it (RQ-91-X86OBJPLAN, #1741).
//!
//! Moved here unchanged from `synth-backend-aarch64/src/elf.rs` so a second
//! 64-bit backend (x86-64, VCR-X86-001) consumes the SAME plan instead of a
//! copy of it. What is machine-specific is passed in, never re-derived here:
//!
//! * the ELF `e_machine`, the `.text` section alignment and the
//!   [`RelocKind`] → ELF relocation-type map, as an [`ElfMachine`];
//! * every relocation ADDEND, carried by each instruction site
//!   ([`CodeRelocation::addend`]) into [`PlannedReloc::addend`]. An addend is
//!   a property of the instruction, not of the kind: on x86-64 the same
//!   `R_X86_64_PC32` needs -4 under `movq cell(%rip), %rax`, -5 under
//!   `cmpl $7, glob(%rip)` and -8 under `movl $7, glob(%rip)` (the trailing
//!   immediate sits between the field and the next instruction). A per-kind
//!   addend would be wrong for every RIP-relative instruction with an
//!   immediate, so this module has nowhere to put one.

use crate::backend::{BackendError, CodeRelocation, RelocKind, SymbolBinding, locals_first};

/// A compiled function to place in `.text`.
#[derive(Debug, Clone)]
pub struct ObjectFunction {
    /// Symbol name aliases for this function's `.text` offset. The FIRST is
    /// the canonical in-object label — `func_N` (N = wasm function index), or
    /// `__synth_func_table` for the [`Self::is_object`] table — and is
    /// planned LOCAL: it is what this object's own relocations bind to (by
    /// symbol index), and it is the name a SECOND synth object also defines,
    /// so it must not take part in cross-object resolution (#1180 — the
    /// `duplicate symbol: func_1` class; ARM's #656 policy, ported into the
    /// shared plan). Any following aliases are wasm EXPORT names and are
    /// planned GLOBAL — the names an embedder calls. The driver upholds this
    /// order (`build_multi_func_aarch64_elf`); the binding is assigned in
    /// [`plan_object`], once, for every container.
    pub symbols: Vec<String>,
    /// Function body machine code.
    pub code: Vec<u8>,
    /// Relocations within this function's code (offsets are function-local;
    /// the plan rebases them to the `.text` offset, and takes each one's
    /// addend from the site). Empty for leaf functions.
    pub relocations: Vec<CodeRelocation>,
    /// #851 lane L3: this entry is DATA that happens to live in `.text` (the
    /// `call_indirect` funcref table: `[u32 class-id][b func_N]` slot records).
    /// Its symbols are emitted `STT_OBJECT` rather than `STT_FUNC` — the table
    /// is branched INTO at slot+4, never called at slot+0, and typing it as a
    /// function would misdescribe the object to any consumer.
    pub is_object: bool,
}

impl ObjectFunction {
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
/// PRECONDITION STATUS, stated plainly: there is NONE. Unlike the aarch64
/// `x28` linear-memory base (an ambient input the embedder supplies), the
/// globals region is emitted BY synth into this section, carrying each
/// global's decoded constant initializer, and reached from code by a
/// PC-relative relocation against [`Self::symbols`]. The linker places it; no
/// register convention, no startup, no linker script and no second ambient
/// input is required.
#[derive(Debug, Default, Clone)]
pub struct DataBlob {
    /// The `.data` bytes (little-endian, already laid out).
    pub bytes: Vec<u8>,
    /// `(symbol name, byte offset within `.data`)` — e.g.
    /// `("__synth_globals", 0)`. Emitted as LOCAL `STT_OBJECT` (#1180): the
    /// region is reached only by this object's own relocations, no embedder
    /// register names it (unlike ARM's R9 contract), and a second synth object
    /// carries its own `__synth_globals`.
    pub symbols: Vec<(String, u64)>,
}

/// RQ-64-MACHO: where a planned symbol lives. `Text`/`Data` are section
/// classes shared by every container (ELF `.text` / `.data`, Mach-O
/// `__TEXT,__text` / `__DATA,__data`); `Undefined` is the #1017 import
/// external the host linker resolves.
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
/// relocation kind, the index of its target in [`ObjectPlan::symbols`], and
/// (RQ-91-X86OBJPLAN) the addend its instruction site declared.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlannedReloc {
    pub offset: u64,
    pub kind: RelocKind,
    pub symbol: usize,
    /// Copied from [`CodeRelocation::addend`] — never derived from `kind`.
    pub addend: i64,
}

/// RQ-64-MACHO: the container-independent object PLAN — everything a
/// relocatable object says, before any container says it.
///
/// This is the single source every writer consumes: [`write_elf64_rel`] (ELF
/// `ET_REL`) and the aarch64 Mach-O writer (`MH_OBJECT`). The `.text` bytes,
/// the `.data` bytes, the symbol list (order, type, BINDING, section, offset,
/// size) and the resolved relocation list are computed ONCE here, so two
/// containers cannot disagree on any of them by construction — the
/// byte-identity the RQ-64-MACHO oracle then checks from the outside
/// (`scripts/repro/macho_host_link_rq64_differential.py`) is a property of
/// this function, not of two writers happening to agree. A second
/// hand-written copy of the symbol-ordering, binding or #1013 rules in a
/// writer would be exactly the mirror the North Star forbids.
///
/// #1180 / RQ-65-FUNCN: binding is a field of every [`PlannedSymbol`], and
/// the symbol ORDER is already locals-first (`crate::backend::locals_first`,
/// the same function the ARM builder applies since #656), so a writer reads
/// [`ObjectPlan::local_count`] for its partition (`sh_info` / `LC_DYSYMTAB`)
/// and never sorts.
#[derive(Debug, Clone, Default)]
pub struct ObjectPlan {
    /// All function bodies concatenated in order, no padding.
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

/// RQ-91-NAMECOLL (#1698): every symbol name [`plan_object`] DEFINES (places)
/// for these inputs: each function's symbols (its `func_N` label, its export
/// name, the funcref table's `__synth_func_table`) and each `.data` symbol
/// (`__synth_globals`). This is the ONE derivation. `plan_object` decides
/// "placed or external" through it, and the driver checks a called import's
/// symbol against it.
pub fn defined_symbol_names<'a>(
    functions: &'a [ObjectFunction],
    data: &'a DataBlob,
) -> std::collections::HashSet<&'a str> {
    functions
        .iter()
        .flat_map(|f| &f.symbols)
        .map(|s| s.as_str())
        .chain(data.symbols.iter().map(|(n, _)| n.as_str()))
        .collect()
}

/// Compute the [`ObjectPlan`] for `functions` + `data` + `undefined_externals`.
/// The rules (symbol order, first-occurrence name resolution, the #1017
/// external allowlist, the #1013 unplaced-symbol refusal) are the aarch64 ELF
/// builder's, moved here unchanged — the ELF output of every module is
/// byte-identical to the pre-plan builder (gated by the RQ-64-MACHO lane's
/// 140-object corpus diff, and by RQ-91-X86OBJPLAN's two-binary diff of the
/// move). `producer` names the builder in the #1013 refusal.
pub fn plan_object(
    producer: &str,
    functions: &[ObjectFunction],
    data: &DataBlob,
    undefined_externals: &[String],
) -> Result<ObjectPlan, BackendError> {
    // --- .text: concatenated bodies; record each function's .text offset. ---
    let mut text: Vec<u8> = Vec::new();
    let mut func_off: Vec<u64> = Vec::new();
    for f in functions {
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
    // that address; a plan consumer has no such register.
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
        // export names (GLOBAL) — see `ObjectFunction::symbols`.
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
    // LOCAL (#1180), reached only by this object's own relocations.
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
    // order; a name this object already places is skipped. RQ-91-NAMECOLL
    // (#1698): that skip used to be where an import named like a placed symbol
    // silently bound to it ("ARM parity" — ARM had the same defect). The
    // driver (`build_multi_func_aarch64_elf`) now REFUSES a called import
    // whose name is in `defined_symbol_names` before this plan runs, so the
    // skip is reached only by an allowlisted name that no import call uses.
    {
        let referenced: std::collections::HashSet<&str> = functions
            .iter()
            .flat_map(|f| &f.relocations)
            .map(|r| r.symbol.as_str())
            .collect();
        // Defined-name set derived from the same inputs `push_sym` consumed
        // (reading `sym_index` here would conflict with the closure's capture).
        let defined = defined_symbol_names(functions, data);
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
    // `locals_first` HERE — the function the ARM builder applies since #656 —
    // means no writer sorts, and the name → index map is rewritten through
    // the permutation so every relocation below resolves against the emitted
    // order. A stable sort keeps the natural order inside each class, and the
    // undefined externals (all GLOBAL, pushed last) stay last, which is the
    // defined-then-undefined half of the Mach-O partition.
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
            // externals now EXIST in this plan, but only for the driver's
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
                    "{producer}: relocation at .text+{} targets symbol \
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
                addend: r.addend,
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

/// The machine-specific facts [`write_elf64_rel`] needs, and nothing else.
/// No addend lives here — see the module doc.
#[derive(Debug, Clone, Copy)]
pub struct ElfMachine {
    /// ELF `e_machine` (183 = `EM_AARCH64`, 62 = `EM_X86_64`).
    pub e_machine: u16,
    /// `.text` `sh_addralign`.
    pub text_align: u64,
    /// The relocation-type map. It must have NO wildcard that returns a
    /// type: a kind the machine cannot express panics there rather than ship
    /// an unrelocated placeholder (the silent-miscompile class).
    pub reloc_type: fn(RelocKind) -> u32,
}

pub(crate) const EHDR_SIZE: usize = 64;
pub(crate) const SHDR_SIZE: usize = 64;
pub(crate) const SYM_SIZE: usize = 24;
pub(crate) const RELA_SIZE: usize = 24;

fn push_u16(v: &mut Vec<u8>, x: u16) {
    v.extend_from_slice(&x.to_le_bytes());
}
fn push_u32(v: &mut Vec<u8>, x: u32) {
    v.extend_from_slice(&x.to_le_bytes());
}
fn push_u64(v: &mut Vec<u8>, x: u64) {
    v.extend_from_slice(&x.to_le_bytes());
}

/// Lay an ELF64 little-endian `ET_REL` object around `plan`.
///
/// Section indices: `[0]=NULL [1]=.text [2]=.symtab [3]=.strtab [4]=.shstrtab`,
/// then `.data` (when non-empty) and `.rela.text` (when non-empty) appended in
/// that order. An EMPTY `.data` reproduces the data-free layout exactly, so
/// every module without globals stays byte-identical (the frozen-anchor
/// contract). Each `.rela.text` entry's `r_addend` is the planned
/// relocation's own [`PlannedReloc::addend`].
pub fn write_elf64_rel(plan: &ObjectPlan, machine: &ElfMachine) -> Vec<u8> {
    let text = &plan.text;
    let data = &plan.data;

    let have_data = !data.is_empty();
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
        let r_type = (machine.reloc_type)(r.kind);
        let sidx = r.symbol as u64 + 1;
        let r_info = (sidx << 32) | (r_type as u64);
        push_u64(&mut rela, r.offset);
        push_u64(&mut rela, r_info);
        // r_addend: the SITE's addend (RQ-91-X86OBJPLAN), two's complement.
        rela.extend_from_slice(&r.addend.to_le_bytes());
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
        data_off + data.len()
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
    push_u16(&mut out, machine.e_machine); // e_machine
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
        out.extend_from_slice(data);
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
    // [1] .text — PROGBITS, ALLOC|EXECINSTR (0x2|0x4), the machine's alignment
    shdr(
        n_text,
        1,
        0x6,
        text_off,
        text.len(),
        0,
        0,
        machine.text_align,
        0,
    );
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
        shdr(n_data, 1, 0x3, data_off, data.len(), 0, 0, 8, 0);
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

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A test machine: e_machine 62 (`EM_X86_64`'s number, used only as a
    /// value here — no x86 code exists in this lane) and a map that gives the
    /// one kind it accepts a fixed type. Its map has no addend to give.
    fn test_machine() -> ElfMachine {
        fn ty(k: RelocKind) -> u32 {
            match k {
                RelocKind::AArch64Call26 => 2,
                other => panic!("test machine cannot emit {other:?}"),
            }
        }
        ElfMachine {
            e_machine: 62,
            text_align: 16,
            reloc_type: ty,
        }
    }

    /// The three x86-64 addends REVIEW_2 correction 4 measured (`movq` -4,
    /// `cmpl $imm8` -5, `movl $imm32` -8), on THREE sites of the SAME kind.
    fn three_site_function() -> Vec<ObjectFunction> {
        let site =
            |offset, addend| CodeRelocation::site(offset, "g", RelocKind::AArch64Call26, addend);
        vec![
            ObjectFunction::code(vec!["func_0".into()], vec![0x90; 8], vec![]),
            ObjectFunction::code(
                vec!["func_1".into(), "run".into()],
                vec![0x90; 32],
                vec![site(3, -4), site(13, -5), site(22, -8)],
            ),
        ]
    }

    fn rela_entries(obj: &[u8]) -> Vec<(u64, u64, i64)> {
        let rd = |o: usize, n: usize| {
            let mut b = [0u8; 8];
            b[..n].copy_from_slice(&obj[o..o + n]);
            u64::from_le_bytes(b)
        };
        let (shoff, shnum) = (rd(0x28, 8) as usize, rd(0x3C, 2) as usize);
        (0..shnum)
            .map(|i| shoff + i * SHDR_SIZE)
            .filter(|&sh| rd(sh + 4, 4) == 4) // SHT_RELA
            .flat_map(|sh| {
                let (off, size) = (rd(sh + 24, 8) as usize, rd(sh + 32, 8) as usize);
                (off..off + size)
                    .step_by(RELA_SIZE)
                    .map(|e| (rd(e, 8), rd(e + 8, 8), rd(e + 16, 8) as i64))
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    #[test]
    fn plan_carries_each_sites_addend_not_one_per_kind() {
        let data = DataBlob {
            bytes: vec![0; 8],
            symbols: vec![("g".into(), 0)],
        };
        let plan = plan_object("test", &three_site_function(), &data, &[]).unwrap();
        let got: Vec<(u64, i64)> = plan.relocs.iter().map(|r| (r.offset, r.addend)).collect();
        // Rebased by func_0's 8 bytes; every addend is the site's own.
        assert_eq!(got, vec![(11, -4), (21, -5), (30, -8)]);
        assert!(
            plan.relocs
                .iter()
                .all(|r| r.kind == RelocKind::AArch64Call26)
        );
    }

    #[test]
    fn elf_writer_emits_each_sites_addend_and_the_machine_facts() {
        let data = DataBlob {
            bytes: vec![0; 8],
            symbols: vec![("g".into(), 0)],
        };
        let plan = plan_object("test", &three_site_function(), &data, &[]).unwrap();
        let obj = write_elf64_rel(&plan, &test_machine());
        assert_eq!(u16::from_le_bytes([obj[18], obj[19]]), 62);
        // .text sh_addralign (section 1, offset 48 in its header) is the machine's.
        let shoff = u64::from_le_bytes(obj[0x28..0x30].try_into().unwrap()) as usize;
        let sh1 = shoff + SHDR_SIZE;
        assert_eq!(
            u64::from_le_bytes(obj[sh1 + 48..sh1 + 56].try_into().unwrap()),
            16
        );
        // Plan order is func_0, func_1, g (locals), then run (global), so
        // `g` is plan index 2 and ELF symbol index 3.
        let want: Vec<(u64, u64, i64)> = [(11, -4), (21, -5), (30, -8)]
            .iter()
            .map(|&(o, a)| (o, (3u64 << 32) | 2, a))
            .collect();
        assert_eq!(rela_entries(&obj), want);
    }
}
