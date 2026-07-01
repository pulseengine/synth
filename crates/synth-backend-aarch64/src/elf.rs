//! Minimal `EM_AARCH64` ELF64 relocatable-object emitter — milestone-1b (#538).
//!
//! Produces an `ET_REL` object for AArch64 (`e_machine = 183`) with a single
//! `.text` (all function bodies concatenated), a `.symtab` exposing one
//! `STT_FUNC`/`GLOBAL` symbol per function at its `.text` offset, and the two
//! string tables. Milestone-1b functions are leaf integer bodies with no external
//! references, so no relocation section is needed yet (`bl`/imports arrive with
//! calls in a later milestone). The object is host-linkable on arm64 ELF targets
//! (arm64 Linux/CI) and its `.text` is directly runnable under a native or
//! emulated A64 core.

/// A compiled function to place in `.text`.
pub struct ElfFunction {
    pub name: String,
    pub code: Vec<u8>,
}

const EHDR_SIZE: usize = 64;
const SHDR_SIZE: usize = 64;
const SYM_SIZE: usize = 24;

fn push_u16(v: &mut Vec<u8>, x: u16) {
    v.extend_from_slice(&x.to_le_bytes());
}
fn push_u32(v: &mut Vec<u8>, x: u32) {
    v.extend_from_slice(&x.to_le_bytes());
}
fn push_u64(v: &mut Vec<u8>, x: u64) {
    v.extend_from_slice(&x.to_le_bytes());
}

/// Build an `EM_AARCH64` `ET_REL` object exposing each function as a global
/// `STT_FUNC` symbol in `.text`.
pub fn build_relocatable_object(functions: &[ElfFunction]) -> Vec<u8> {
    // --- .text: concatenated bodies; record each function's (offset, size). ---
    let mut text: Vec<u8> = Vec::new();
    let mut placement: Vec<(u64, u64)> = Vec::new();
    for f in functions {
        // A64 instructions are 4-byte aligned; bodies are whole words already.
        placement.push((text.len() as u64, f.code.len() as u64));
        text.extend_from_slice(&f.code);
    }

    // --- .strtab: symbol names (index 0 is the empty string). ---
    let mut strtab: Vec<u8> = vec![0];
    let mut name_off: Vec<u32> = Vec::new();
    for f in functions {
        name_off.push(strtab.len() as u32);
        strtab.extend_from_slice(f.name.as_bytes());
        strtab.push(0);
    }

    // --- .symtab: [0]=NULL, then one GLOBAL STT_FUNC per function. ---
    // st_info = (bind << 4) | type; GLOBAL=1, FUNC=2 → 0x12. shndx = 1 (.text).
    let mut symtab: Vec<u8> = Vec::new();
    // null symbol
    symtab.extend_from_slice(&[0u8; SYM_SIZE]);
    for (i, _f) in functions.iter().enumerate() {
        let (off, size) = placement[i];
        push_u32(&mut symtab, name_off[i]); // st_name
        symtab.push(0x12); // st_info: GLOBAL FUNC
        symtab.push(0); // st_other
        push_u16(&mut symtab, 1); // st_shndx = .text (section 1)
        push_u64(&mut symtab, off); // st_value
        push_u64(&mut symtab, size); // st_size
    }

    // --- .shstrtab: section header names. ---
    let mut shstrtab: Vec<u8> = vec![0];
    let add_shstr = |sh: &mut Vec<u8>, s: &str| -> u32 {
        let o = sh.len() as u32;
        sh.extend_from_slice(s.as_bytes());
        sh.push(0);
        o
    };
    let n_text = add_shstr(&mut shstrtab, ".text");
    let n_symtab = add_shstr(&mut shstrtab, ".symtab");
    let n_strtab = add_shstr(&mut shstrtab, ".strtab");
    let n_shstrtab = add_shstr(&mut shstrtab, ".shstrtab");

    // --- Layout: ehdr | .text | .symtab | .strtab | .shstrtab | shdrs. ---
    let text_off = EHDR_SIZE;
    let symtab_off = text_off + text.len();
    let strtab_off = symtab_off + symtab.len();
    let shstrtab_off = strtab_off + strtab.len();
    let shdr_off = shstrtab_off + shstrtab.len();
    let num_sections = 5u16; // NULL, .text, .symtab, .strtab, .shstrtab

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
    debug_assert_eq!(out.len(), shdr_off);

    // Section headers (Elf64_Shdr × 5).
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

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn well_formed_header_and_symbols() {
        let obj = build_relocatable_object(&[
            ElfFunction {
                name: "add".into(),
                code: vec![0, 0, 1, 0x0B, 0xE0, 0x03, 9, 0x2A, 0xC0, 0x03, 0x5F, 0xD6],
            },
            ElfFunction {
                name: "sub".into(),
                code: vec![0x62, 0, 4, 0x4B, 0xC0, 0x03, 0x5F, 0xD6],
            },
        ]);
        // ELF magic + class64 + LSB.
        assert_eq!(&obj[0..4], &[0x7F, b'E', b'L', b'F']);
        assert_eq!(obj[4], 2); // ELFCLASS64
        assert_eq!(obj[5], 1); // LSB
        // e_type = ET_REL, e_machine = EM_AARCH64.
        assert_eq!(u16::from_le_bytes([obj[16], obj[17]]), 1);
        assert_eq!(u16::from_le_bytes([obj[18], obj[19]]), 183);
        // e_shnum = 5.
        assert_eq!(u16::from_le_bytes([obj[60], obj[61]]), 5);
        // The object must be non-trivial and contain both symbol names.
        let s = String::from_utf8_lossy(&obj);
        assert!(s.contains("add") && s.contains("sub"));
    }
}
