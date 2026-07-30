//! Minimal `EM_AARCH64` ELF64 relocatable-object emitter — milestone-1b (#538),
//! extended for direct calls (#851).
//!
//! Produces an `ET_REL` object for AArch64 (`e_machine = 183`) with a single
//! `.text` (all function bodies concatenated), a `.symtab` exposing one or more
//! `STT_FUNC`/`GLOBAL` symbols per function at its `.text` offset (each function
//! carries a `func_N` symbol plus its export name when exported), the two string
//! tables, and — when any function has a call relocation — a `.rela.text`
//! section of `R_AARCH64_CALL26` entries so `bl func_N` sites are linkable
//! (#851). The object is host-linkable on arm64 ELF targets and its `.text` is
//! directly runnable under a native or emulated A64 core once relocated.

use synth_core::backend::{CodeRelocation, RelocKind};

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
    /// Symbol name aliases for this function's `.text` offset. The first is the
    /// canonical `func_N`; a distinct export name (if any) follows. All are
    /// emitted as GLOBAL symbols pointing at the same body.
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
    /// `("__synth_globals", 0)`. Emitted as GLOBAL `STT_OBJECT`.
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

/// Build an `EM_AARCH64` `ET_REL` object exposing each function's symbols as
/// GLOBAL `STT_FUNC` in `.text`, plus a `.rela.text` for any call relocations.
/// Data-free shorthand for [`build_relocatable_object_with_data`] — a module
/// with no globals emits byte-identical output to the pre-lane-L3 builder.
pub fn build_relocatable_object(functions: &[ElfFunction]) -> Vec<u8> {
    build_relocatable_object_with_data(functions, &DataBlob::default())
}

/// Build an `EM_AARCH64` `ET_REL` object with an optional synth-emitted `.data`
/// section (#851 lane L3 — the WASM globals region, see [`DataBlob`]).
///
/// Section indices: `[0]=NULL [1]=.text [2]=.symtab [3]=.strtab [4]=.shstrtab`,
/// then `.data` (when non-empty) and `.rela.text` (when non-empty) appended in
/// that order. An EMPTY `DataBlob` reproduces the previous layout exactly, so
/// every module without globals stays byte-identical (the frozen-anchor
/// contract).
pub fn build_relocatable_object_with_data(functions: &[ElfFunction], data: &DataBlob) -> Vec<u8> {
    // --- .text: concatenated bodies; record each function's .text offset. ---
    let mut text: Vec<u8> = Vec::new();
    let mut func_off: Vec<u64> = Vec::new();
    for f in functions {
        // A64 instructions are 4-byte aligned; bodies are whole words already.
        func_off.push(text.len() as u64);
        text.extend_from_slice(&f.code);
    }

    let have_data = !data.bytes.is_empty();
    // Section indices. [0]=NULL [1]=.text [2]=.symtab [3]=.strtab [4]=.shstrtab;
    // `.data` (when present) is 5 and `.rela.text` follows. Fixing `.data` BEFORE
    // `.rela.text` keeps the data symbols' `st_shndx` independent of whether the
    // module has relocations.
    let idx_data: u16 = 5;

    // --- .strtab + .symtab: one GLOBAL symbol per (function, symbol-alias). ---
    // st_info = (bind << 4) | type; GLOBAL=1, so FUNC(2) → 0x12 and OBJECT(1) →
    // 0x11. shndx = 1 (.text) for code, `idx_data` for the `.data` symbols.
    // Also build a name → symbol-index map so relocations resolve by symbol name.
    let mut strtab: Vec<u8> = vec![0];
    let mut symtab: Vec<u8> = Vec::new();
    symtab.extend_from_slice(&[0u8; SYM_SIZE]); // null symbol at index 0
    let mut sym_index: std::collections::HashMap<String, u32> = std::collections::HashMap::new();
    let mut next_sym_idx: u32 = 1;
    let mut push_sym =
        |name: &str, info: u8, shndx: u16, value: u64, size: u64, strtab: &mut Vec<u8>| {
            let name_off = strtab.len() as u32;
            strtab.extend_from_slice(name.as_bytes());
            strtab.push(0);
            push_u32(&mut symtab, name_off); // st_name
            symtab.push(info); // st_info
            symtab.push(0); // st_other
            push_u16(&mut symtab, shndx); // st_shndx
            push_u64(&mut symtab, value); // st_value
            push_u64(&mut symtab, size); // st_size
            sym_index.entry(name.to_string()).or_insert(next_sym_idx);
            next_sym_idx += 1;
        };
    for (i, f) in functions.iter().enumerate() {
        let off = func_off[i];
        let size = f.code.len() as u64;
        // #851 lane L3: the funcref table is DATA in `.text` — type it OBJECT so
        // the object does not claim a branch-table blob is a callable function.
        let info = if f.is_object { 0x11 } else { 0x12 };
        for sym in &f.symbols {
            push_sym(sym, info, 1, off, size, &mut strtab);
        }
    }
    // #851 lane L3: synth-emitted `.data` symbols (the globals region base).
    if have_data {
        for (name, off) in &data.symbols {
            let size = data.bytes.len() as u64 - off.min(&(data.bytes.len() as u64));
            push_sym(name, 0x11, idx_data, *off, size, &mut strtab);
        }
    }

    // --- .rela.text: one entry per code relocation (rebased to .text). ---
    // ELF64 packs r_info = (sym_index << 32) | type (sym in the HIGH word).
    let mut rela: Vec<u8> = Vec::new();
    for (i, f) in functions.iter().enumerate() {
        for r in &f.relocations {
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
            // A relocation against a symbol this object does not place is an
            // INTERNAL BUG, and silently dropping it ships the unrelocated
            // placeholder: `bl #0` branches to itself, `adrp #0` addresses the
            // WRONG page (a silent miscompile, not a link error). Panic — the
            // defensive-panic convention for backend invariants.
            let sidx = *sym_index.get(&r.symbol).unwrap_or_else(|| {
                panic!(
                    "aarch64 ELF builder: relocation at .text+{} targets symbol \
                     '{}', which this object does not place — refusing to ship an \
                     unrelocated placeholder (#851)",
                    func_off[i] + r.offset as u64,
                    r.symbol
                )
            });
            let r_offset = func_off[i] + r.offset as u64;
            let r_info = ((sidx as u64) << 32) | (r_type as u64);
            push_u64(&mut rela, r_offset);
            push_u64(&mut rela, r_info);
            push_u64(&mut rela, 0); // r_addend = 0
        }
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
    out.extend_from_slice(&text);
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
    // [2] .symtab — SYMTAB(2), link=.strtab(3), info=first-global(1), align 8
    shdr(
        n_symtab,
        2,
        0,
        symtab_off,
        symtab.len(),
        3,
        1,
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

    out
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
        ]);
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
        ]);
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
        );
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
                assert_eq!(obj[b + 4], 0x11, "globals symbol must be GLOBAL OBJECT");
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
            build_relocatable_object(&f()),
            build_relocatable_object_with_data(&f(), &DataBlob::default())
        );
        assert_eq!(
            u16::from_le_bytes([
                build_relocatable_object(&f())[60],
                build_relocatable_object(&f())[61]
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
        ]);
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
                assert_eq!(obj[b + 4], 0x11, "table symbol must be GLOBAL OBJECT");
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
        );
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
}
