//! Mach-O `MH_OBJECT` writer for `CPU_TYPE_ARM64` — the SAME object plan the
//! ELF writer emits, in the container macOS loads (RQ-64-MACHO).
//!
//! WHY THIS EXISTS. `-b aarch64 --relocatable` emits a SysV ELF64 `ET_REL`
//! that arm64-Linux links and runs (RQ-64-ARM64LINUX). macOS cannot load that
//! container — Apple's `ld` answers `unknown file type` — but the instruction
//! bytes inside it are already the right ones: every relocation the backend
//! emits has an exact Mach-O arm64 equivalent with the same addend (zero), so
//! nothing about the code has to change, only the wrapper. That is the
//! artifact's thesis, and this writer is built so the thesis is TRUE BY
//! CONSTRUCTION rather than by two writers agreeing:
//!
//! * it consumes [`crate::elf::ObjectPlan`], the ONE plan
//!   [`crate::elf::build_relocatable_object_full`] also consumes — `.text`
//!   bytes, `.data` bytes, symbol order/type/section/offset, resolved
//!   relocations and the #1013/#1017 rules are computed once, in
//!   [`crate::elf::plan_object`], and this file only lays Mach-O around them;
//! * `scripts/repro/macho_host_link_rq64_differential.py` checks that from the
//!   OUTSIDE on every run (`.text == __text`, `.data == __data`, symbols 1:1,
//!   the relocation SET 1:1 under the type map) over every repo module the
//!   backend accepts, and on an arm64-macOS host links the object with Apple
//!   `ld` and EXECUTES it against wasmtime.
//!
//! WHAT IS EMITTED, and the decisions that are decisions:
//!
//! * Header `MH_MAGIC_64`, `CPU_TYPE_ARM64` / `CPU_SUBTYPE_ARM64_ALL`,
//!   `MH_OBJECT`, flags 0. `MH_SUBSECTIONS_VIA_SYMBOLS` is deliberately NOT
//!   set: with it the linker may split `__text` into per-symbol atoms and
//!   reorder or dead-strip them; without it the whole section is one atom and
//!   keeps exactly the ELF `.text` layout (the funcref table appended LAST, at
//!   the offset its `b func_N` trampolines were laid out for). Byte identity
//!   with the ELF path is the property under test; atomization is not
//!   claimed.
//! * One `LC_SEGMENT_64` (unnamed, the MH_OBJECT convention) holding
//!   `__TEXT,__text` (`S_ATTR_PURE_INSTRUCTIONS|S_ATTR_SOME_INSTRUCTIONS`,
//!   2^2-aligned) and, when the module has globals, `__DATA,__data`
//!   (2^3-aligned; an i64 slot lands naturally aligned). Section file offsets
//!   are congruent with their addresses (`offset = segment.fileoff + addr`),
//!   which is what an MH_OBJECT reader assumes.
//! * `LC_BUILD_VERSION` platform `PLATFORM_MACOS`, minos 11.0 (the first
//!   arm64 macOS), sdk 0, no tools. Without a platform load command Apple's
//!   `ld` warns that it is assuming macOS; the assumption is written down
//!   here instead. This is the ONE macOS-specific fact in the file — the
//!   rest is arm64 Mach-O.
//! * `LC_SYMTAB` + `LC_DYSYMTAB`. Symbol names carry the Darwin C prefix:
//!   wasm export `add` is `_add`, `func_3` is `_func_3`, the globals region
//!   is `___synth_globals`, and an import `host_add` is the undefined
//!   `_host_add` — so a C harness declares `extern int32_t add(int32_t,
//!   int32_t);` and defines `host_add` exactly as it would for any other
//!   object. Every symbol is `N_EXT` (the plan has no locals — `func_N` is
//!   GLOBAL on this backend, see #1180: two synth objects collide in one
//!   link here exactly as in ELF, `duplicate symbol '_func_1'`). The plan's
//!   order already partitions defined-then-undefined, which is what the
//!   `LC_DYSYMTAB` ranges require.
//! * `__text` relocations, one per planned relocation, all `r_extern` with
//!   `r_length` 2 (4 bytes):
//!   `AArch64Call26`/`AArch64Jump26` → `ARM64_RELOC_BRANCH26` (pc-relative —
//!   Mach-O uses one type for `b` and `bl`), `AArch64AdrPrelPgHi21` →
//!   `ARM64_RELOC_PAGE21` (pc-relative), `AArch64AddAbsLo12Nc` →
//!   `ARM64_RELOC_PAGEOFF12` (absolute page offset). Addends are zero in
//!   both containers, so no `ARM64_RELOC_ADDEND` is ever needed. NO wildcard:
//!   any other kind fails loudly, the ELF writer's rule.
//!
//! WHAT IS NOT CLAIMED: a dylib (no `-dylib` link is exercised — the object
//! is linked into an executable with the host's libSystem), any CPU type but
//! ARM64, any platform but macOS, and anything about the ISA — the sibling
//! unicorn oracles own that.

use synth_core::backend::{BackendError, RelocKind};

use crate::elf::{DataBlob, ElfFunction, ObjectPlan, SymbolPlace, plan_object};

const MH_MAGIC_64: u32 = 0xFEED_FACF;
/// `CPU_ARCH_ABI64 | CPU_TYPE_ARM`.
const CPU_TYPE_ARM64: u32 = 0x0100_000C;
const CPU_SUBTYPE_ARM64_ALL: u32 = 0;
const MH_OBJECT: u32 = 1;

const LC_SEGMENT_64: u32 = 0x19;
const LC_SYMTAB: u32 = 0x2;
const LC_DYSYMTAB: u32 = 0xB;
const LC_BUILD_VERSION: u32 = 0x32;
const PLATFORM_MACOS: u32 = 1;
/// `minos` 11.0.0 packed `xxxx.yy.zz` — the first macOS with arm64.
const MINOS_MACOS_11_0: u32 = 0x000B_0000;

const S_REGULAR: u32 = 0;
const S_ATTR_PURE_INSTRUCTIONS: u32 = 0x8000_0000;
const S_ATTR_SOME_INSTRUCTIONS: u32 = 0x0000_0400;
/// `VM_PROT_READ | VM_PROT_WRITE | VM_PROT_EXECUTE` — the MH_OBJECT segment
/// convention (protection is decided at link time, not here).
const VM_PROT_RWX: i32 = 7;

const N_EXT: u8 = 0x01;
const N_UNDF: u8 = 0x00;
const N_SECT: u8 = 0x0E;
const NO_SECT: u8 = 0;

const ARM64_RELOC_BRANCH26: u32 = 2;
const ARM64_RELOC_PAGE21: u32 = 3;
const ARM64_RELOC_PAGEOFF12: u32 = 4;

const HEADER_SIZE: usize = 32;
const SEGMENT_CMD_SIZE: usize = 72;
const SECTION_SIZE: usize = 80;
const BUILD_VERSION_CMD_SIZE: usize = 24;
const SYMTAB_CMD_SIZE: usize = 24;
const DYSYMTAB_CMD_SIZE: usize = 80;
const NLIST_SIZE: usize = 16;
const RELOC_SIZE: usize = 8;

/// The Darwin C symbol prefix. Applied to EVERY plan symbol, defined or
/// undefined, so the object interoperates with C the way `clang -c` output
/// does.
pub const DARWIN_SYMBOL_PREFIX: &str = "_";

fn push_u16(v: &mut Vec<u8>, x: u16) {
    v.extend_from_slice(&x.to_le_bytes());
}
fn push_u32(v: &mut Vec<u8>, x: u32) {
    v.extend_from_slice(&x.to_le_bytes());
}
fn push_i32(v: &mut Vec<u8>, x: i32) {
    v.extend_from_slice(&x.to_le_bytes());
}
fn push_u64(v: &mut Vec<u8>, x: u64) {
    v.extend_from_slice(&x.to_le_bytes());
}
fn push_name16(v: &mut Vec<u8>, name: &str) {
    let mut buf = [0u8; 16];
    let b = name.as_bytes();
    debug_assert!(b.len() <= 16);
    buf[..b.len()].copy_from_slice(b);
    v.extend_from_slice(&buf);
}
fn align8(x: usize) -> usize {
    x.div_ceil(8) * 8
}

/// Build a `CPU_TYPE_ARM64` `MH_OBJECT` from the same inputs the ELF builder
/// takes. `Err` exactly where [`crate::elf::build_relocatable_object_full`]
/// is `Err` (#1013 — a relocation against a symbol this object does not
/// place), because the plan is shared.
pub fn build_macho_object_full(
    functions: &[ElfFunction],
    data: &DataBlob,
    undefined_externals: &[String],
) -> Result<Vec<u8>, BackendError> {
    let plan = plan_object(functions, data, undefined_externals)?;
    Ok(build_macho_object_from_plan(&plan))
}

/// Lay Mach-O around an [`ObjectPlan`]. Pure: the plan is the only input.
pub fn build_macho_object_from_plan(plan: &ObjectPlan) -> Vec<u8> {
    let have_data = !plan.data.is_empty();
    let nsects: usize = 1 + usize::from(have_data);
    let sizeofcmds = SEGMENT_CMD_SIZE
        + nsects * SECTION_SIZE
        + BUILD_VERSION_CMD_SIZE
        + SYMTAB_CMD_SIZE
        + DYSYMTAB_CMD_SIZE;

    // --- addresses within the (single, vmaddr 0) segment, and file offsets
    //     congruent with them. ---
    let text_addr: u64 = 0;
    let data_addr: u64 = align8(plan.text.len()) as u64;
    let vmsize: u64 = if have_data {
        data_addr + plan.data.len() as u64
    } else {
        plan.text.len() as u64
    };
    let seg_fileoff = align8(HEADER_SIZE + sizeofcmds);
    let text_off = seg_fileoff + text_addr as usize;
    let data_off = seg_fileoff + data_addr as usize;
    let after_seg = seg_fileoff + vmsize as usize;

    // --- __text relocations ---
    let mut relocs: Vec<u8> = Vec::with_capacity(plan.relocs.len() * RELOC_SIZE);
    for r in &plan.relocs {
        // NO wildcard: a relocation kind this container cannot express fails
        // loudly rather than being dropped — an unrelocated `bl #0` /
        // `adrp #0` is the silent-miscompile class (the ELF writer's rule).
        let (r_type, pcrel) = match r.kind {
            RelocKind::AArch64Call26 | RelocKind::AArch64Jump26 => (ARM64_RELOC_BRANCH26, 1u32),
            RelocKind::AArch64AdrPrelPgHi21 => (ARM64_RELOC_PAGE21, 1),
            RelocKind::AArch64AddAbsLo12Nc => (ARM64_RELOC_PAGEOFF12, 0),
            other => panic!(
                "aarch64 Mach-O writer cannot emit relocation kind {other:?} \
                 (RQ-64-MACHO): only the four AArch64 kinds are expressible"
            ),
        };
        // relocation_info: r_address (section-relative), then the packed
        // word r_symbolnum:24 | r_pcrel:1 | r_length:2 | r_extern:1 | r_type:4.
        let symbolnum = u32::try_from(r.symbol).expect("symbol index fits 24 bits");
        assert!(symbolnum < (1 << 24), "Mach-O r_symbolnum is 24 bits");
        let r_length: u32 = 2; // 4 bytes
        let r_extern: u32 = 1;
        let packed =
            symbolnum | (pcrel << 24) | (r_length << 25) | (r_extern << 27) | (r_type << 28);
        push_i32(
            &mut relocs,
            i32::try_from(r.offset).expect("r_address fits i32"),
        );
        push_u32(&mut relocs, packed);
    }
    let nreloc = plan.relocs.len();
    let reloff = if nreloc > 0 { align8(after_seg) } else { 0 };
    let after_relocs = if nreloc > 0 {
        reloff + relocs.len()
    } else {
        after_seg
    };

    // --- symbols: nlist_64 in plan order (defined first, undefined last —
    //     the plan's order, which LC_DYSYMTAB's ranges require) + strtab. ---
    let mut strtab: Vec<u8> = vec![0]; // index 0 is the empty name
    let mut nlist: Vec<u8> = Vec::with_capacity(plan.symbols.len() * NLIST_SIZE);
    let mut ndefined = 0usize;
    let mut seen_undefined = false;
    for s in &plan.symbols {
        let n_strx = strtab.len() as u32;
        strtab.extend_from_slice(DARWIN_SYMBOL_PREFIX.as_bytes());
        strtab.extend_from_slice(s.name.as_bytes());
        strtab.push(0);
        let (n_type, n_sect, n_value) = match s.place {
            SymbolPlace::Text => (N_SECT | N_EXT, 1u8, text_addr + s.value),
            SymbolPlace::Data => {
                debug_assert!(have_data, "a .data symbol without .data bytes");
                (N_SECT | N_EXT, 2u8, data_addr + s.value)
            }
            SymbolPlace::Undefined => (N_UNDF | N_EXT, NO_SECT, 0),
        };
        if s.place == SymbolPlace::Undefined {
            seen_undefined = true;
        } else {
            assert!(
                !seen_undefined,
                "plan symbols must be defined-then-undefined (LC_DYSYMTAB partition)"
            );
            ndefined += 1;
        }
        push_u32(&mut nlist, n_strx);
        nlist.push(n_type);
        nlist.push(n_sect);
        push_u16(&mut nlist, 0); // n_desc
        push_u64(&mut nlist, n_value);
    }
    let nsyms = plan.symbols.len();
    let nundef = nsyms - ndefined;
    while !strtab.len().is_multiple_of(8) {
        strtab.push(0);
    }
    let symoff = align8(after_relocs);
    let stroff = symoff + nlist.len();

    // --- emit ---
    let mut out: Vec<u8> = Vec::with_capacity(stroff + strtab.len());
    // mach_header_64
    push_u32(&mut out, MH_MAGIC_64);
    push_u32(&mut out, CPU_TYPE_ARM64);
    push_u32(&mut out, CPU_SUBTYPE_ARM64_ALL);
    push_u32(&mut out, MH_OBJECT);
    push_u32(&mut out, 4); // ncmds
    push_u32(&mut out, sizeofcmds as u32);
    push_u32(&mut out, 0); // flags: no MH_SUBSECTIONS_VIA_SYMBOLS (see module doc)
    push_u32(&mut out, 0); // reserved
    debug_assert_eq!(out.len(), HEADER_SIZE);

    // LC_SEGMENT_64 (unnamed) + sections
    push_u32(&mut out, LC_SEGMENT_64);
    push_u32(&mut out, (SEGMENT_CMD_SIZE + nsects * SECTION_SIZE) as u32);
    push_name16(&mut out, "");
    push_u64(&mut out, 0); // vmaddr
    push_u64(&mut out, vmsize);
    push_u64(&mut out, seg_fileoff as u64);
    push_u64(&mut out, vmsize); // filesize
    push_i32(&mut out, VM_PROT_RWX); // maxprot
    push_i32(&mut out, VM_PROT_RWX); // initprot
    push_u32(&mut out, nsects as u32);
    push_u32(&mut out, 0); // flags
    let section = |out: &mut Vec<u8>,
                   sectname: &str,
                   segname: &str,
                   addr: u64,
                   size: u64,
                   offset: usize,
                   align_log2: u32,
                   reloff: usize,
                   nreloc: usize,
                   flags: u32| {
        push_name16(out, sectname);
        push_name16(out, segname);
        push_u64(out, addr);
        push_u64(out, size);
        push_u32(out, offset as u32);
        push_u32(out, align_log2);
        push_u32(out, reloff as u32);
        push_u32(out, nreloc as u32);
        push_u32(out, flags);
        push_u32(out, 0); // reserved1
        push_u32(out, 0); // reserved2
        push_u32(out, 0); // reserved3
    };
    section(
        &mut out,
        "__text",
        "__TEXT",
        text_addr,
        plan.text.len() as u64,
        text_off,
        2,
        reloff,
        nreloc,
        S_REGULAR | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS,
    );
    if have_data {
        section(
            &mut out,
            "__data",
            "__DATA",
            data_addr,
            plan.data.len() as u64,
            data_off,
            3,
            0,
            0,
            S_REGULAR,
        );
    }

    // LC_BUILD_VERSION
    push_u32(&mut out, LC_BUILD_VERSION);
    push_u32(&mut out, BUILD_VERSION_CMD_SIZE as u32);
    push_u32(&mut out, PLATFORM_MACOS);
    push_u32(&mut out, MINOS_MACOS_11_0);
    push_u32(&mut out, 0); // sdk: none recorded
    push_u32(&mut out, 0); // ntools

    // LC_SYMTAB
    push_u32(&mut out, LC_SYMTAB);
    push_u32(&mut out, SYMTAB_CMD_SIZE as u32);
    push_u32(&mut out, symoff as u32);
    push_u32(&mut out, nsyms as u32);
    push_u32(&mut out, stroff as u32);
    push_u32(&mut out, strtab.len() as u32);

    // LC_DYSYMTAB: locals [0,0), extdef [0, ndefined), undef [ndefined, nsyms);
    // no table of contents, modules, referenced or indirect symbols.
    push_u32(&mut out, LC_DYSYMTAB);
    push_u32(&mut out, DYSYMTAB_CMD_SIZE as u32);
    push_u32(&mut out, 0); // ilocalsym
    push_u32(&mut out, 0); // nlocalsym
    push_u32(&mut out, 0); // iextdefsym
    push_u32(&mut out, ndefined as u32);
    push_u32(&mut out, ndefined as u32); // iundefsym
    push_u32(&mut out, nundef as u32);
    for _ in 0..12 {
        push_u32(&mut out, 0); // tocoff..nlocrel
    }
    debug_assert_eq!(out.len(), HEADER_SIZE + sizeofcmds);

    // Section contents, at their congruent offsets.
    out.resize(text_off, 0);
    out.extend_from_slice(&plan.text);
    if have_data {
        out.resize(data_off, 0);
        out.extend_from_slice(&plan.data);
    }
    debug_assert_eq!(out.len(), after_seg);
    if nreloc > 0 {
        out.resize(reloff, 0);
        out.extend_from_slice(&relocs);
    }
    out.resize(symoff, 0);
    out.extend_from_slice(&nlist);
    debug_assert_eq!(out.len(), stroff);
    out.extend_from_slice(&strtab);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elf::{DataBlob, ElfFunction, build_relocatable_object_full};
    use synth_core::backend::CodeRelocation;

    fn u32_at(b: &[u8], off: usize) -> u32 {
        u32::from_le_bytes(b[off..off + 4].try_into().unwrap())
    }
    fn u64_at(b: &[u8], off: usize) -> u64 {
        u64::from_le_bytes(b[off..off + 8].try_into().unwrap())
    }
    fn name16(b: &[u8], off: usize) -> String {
        let raw = &b[off..off + 16];
        let end = raw.iter().position(|&c| c == 0).unwrap_or(16);
        String::from_utf8(raw[..end].to_vec()).unwrap()
    }

    /// (sectname, segname, addr, size, offset, align, reloff, nreloc, flags)
    type SectionRow = (String, String, u64, u64, usize, u32, usize, usize, u32);

    /// Walk the load commands: (segment sections, symtab cmd offset, dysymtab
    /// cmd offset, build-version cmd offset).
    fn load_commands(obj: &[u8]) -> (Vec<SectionRow>, usize, usize, usize) {
        let ncmds = u32_at(obj, 16) as usize;
        let mut off = HEADER_SIZE;
        let mut sections = Vec::new();
        let (mut symtab, mut dysymtab, mut bv) = (0, 0, 0);
        for _ in 0..ncmds {
            let cmd = u32_at(obj, off);
            let cmdsize = u32_at(obj, off + 4) as usize;
            match cmd {
                LC_SEGMENT_64 => {
                    let nsects = u32_at(obj, off + 64) as usize;
                    let mut so = off + SEGMENT_CMD_SIZE;
                    for _ in 0..nsects {
                        sections.push((
                            name16(obj, so),
                            name16(obj, so + 16),
                            u64_at(obj, so + 32),
                            u64_at(obj, so + 40),
                            u32_at(obj, so + 48) as usize,
                            u32_at(obj, so + 52),
                            u32_at(obj, so + 56) as usize,
                            u32_at(obj, so + 60) as usize,
                            u32_at(obj, so + 64),
                        ));
                        so += SECTION_SIZE;
                    }
                }
                LC_SYMTAB => symtab = off,
                LC_DYSYMTAB => dysymtab = off,
                LC_BUILD_VERSION => bv = off,
                _ => panic!("unexpected load command {cmd:#x}"),
            }
            off += cmdsize;
        }
        (sections, symtab, dysymtab, bv)
    }

    fn symbols(obj: &[u8]) -> Vec<(String, u8, u8, u64)> {
        let (_, st, _, _) = load_commands(obj);
        let symoff = u32_at(obj, st + 8) as usize;
        let nsyms = u32_at(obj, st + 12) as usize;
        let stroff = u32_at(obj, st + 16) as usize;
        let strsize = u32_at(obj, st + 20) as usize;
        let strtab = &obj[stroff..stroff + strsize];
        (0..nsyms)
            .map(|i| {
                let n = symoff + i * NLIST_SIZE;
                let strx = u32_at(obj, n) as usize;
                let end = strtab[strx..].iter().position(|&c| c == 0).unwrap();
                (
                    String::from_utf8(strtab[strx..strx + end].to_vec()).unwrap(),
                    obj[n + 4],
                    obj[n + 5],
                    u64_at(obj, n + 8),
                )
            })
            .collect()
    }

    fn fixture() -> (Vec<ElfFunction>, DataBlob, Vec<String>) {
        let funcs = vec![
            ElfFunction::code(
                vec!["func_1".into(), "run".into()],
                vec![0x00, 0x00, 0x00, 0x94, 0xC0, 0x03, 0x5F, 0xD6], // bl #0; ret
                vec![CodeRelocation {
                    offset: 0,
                    symbol: "func_2".into(),
                    kind: RelocKind::AArch64Call26,
                }],
            ),
            ElfFunction::code(
                vec!["func_2".into()],
                vec![
                    0x00, 0x00, 0x00, 0x90, // adrp x0, #0
                    0x00, 0x00, 0x00, 0x91, // add x0, x0, #0
                    0x00, 0x00, 0x00, 0x94, // bl #0 (import)
                    0xC0, 0x03, 0x5F, 0xD6, // ret
                ],
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
                    CodeRelocation {
                        offset: 8,
                        symbol: "host_add".into(),
                        kind: RelocKind::AArch64Call26,
                    },
                ],
            ),
            ElfFunction {
                symbols: vec!["__synth_func_table".into()],
                code: vec![1, 0, 0, 0, 0x00, 0x00, 0x00, 0x14], // [class 1][b #0]
                relocations: vec![CodeRelocation {
                    offset: 4,
                    symbol: "func_1".into(),
                    kind: RelocKind::AArch64Jump26,
                }],
                is_object: true,
            },
        ];
        let data = DataBlob {
            bytes: vec![41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
            symbols: vec![("__synth_globals".into(), 0)],
        };
        (funcs, data, vec!["host_add".into()])
    }

    #[test]
    fn header_segment_sections_and_build_version() {
        let (f, d, ext) = fixture();
        let obj = build_macho_object_full(&f, &d, &ext).unwrap();
        assert_eq!(u32_at(&obj, 0), MH_MAGIC_64);
        assert_eq!(u32_at(&obj, 4), CPU_TYPE_ARM64);
        assert_eq!(u32_at(&obj, 8), CPU_SUBTYPE_ARM64_ALL);
        assert_eq!(u32_at(&obj, 12), MH_OBJECT);
        assert_eq!(u32_at(&obj, 16), 4, "ncmds");
        assert_eq!(u32_at(&obj, 24), 0, "flags: no MH_SUBSECTIONS_VIA_SYMBOLS");
        let (secs, _, _, bv) = load_commands(&obj);
        assert_eq!(secs.len(), 2);
        let (n, seg, addr, size, off, align, _reloff, nreloc, flags) = &secs[0];
        assert_eq!((n.as_str(), seg.as_str()), ("__text", "__TEXT"));
        assert_eq!(*addr, 0);
        assert_eq!(*size, 32);
        assert_eq!(*align, 2);
        assert_eq!(*nreloc, 5);
        assert_eq!(*flags, S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS);
        assert_eq!(
            &obj[*off..*off + 32],
            &f[0]
                .code
                .iter()
                .chain(&f[1].code)
                .chain(&f[2].code)
                .copied()
                .collect::<Vec<_>>()[..]
        );
        let (n, seg, addr, size, off, align, _, nreloc, flags) = &secs[1];
        assert_eq!((n.as_str(), seg.as_str()), ("__data", "__DATA"));
        assert_eq!(*addr, 32, "data address follows text, 8-aligned");
        assert_eq!(*size, 16);
        assert_eq!(*align, 3);
        assert_eq!(*nreloc, 0);
        assert_eq!(*flags, S_REGULAR);
        assert_eq!(&obj[*off..*off + 16], &d.bytes[..]);
        // file offsets congruent with addresses within the segment
        assert_eq!(secs[1].4 - secs[0].4, 32);
        // LC_BUILD_VERSION: macOS, 11.0, no sdk, no tools
        assert_eq!(u32_at(&obj, bv + 8), PLATFORM_MACOS);
        assert_eq!(u32_at(&obj, bv + 12), MINOS_MACOS_11_0);
        assert_eq!(u32_at(&obj, bv + 16), 0);
        assert_eq!(u32_at(&obj, bv + 20), 0);
    }

    #[test]
    fn symbols_carry_the_darwin_prefix_and_partition_defined_then_undefined() {
        let (f, d, ext) = fixture();
        let obj = build_macho_object_full(&f, &d, &ext).unwrap();
        let syms = symbols(&obj);
        assert_eq!(
            syms,
            vec![
                ("_func_1".to_string(), N_SECT | N_EXT, 1, 0),
                ("_run".to_string(), N_SECT | N_EXT, 1, 0),
                ("_func_2".to_string(), N_SECT | N_EXT, 1, 8),
                ("___synth_func_table".to_string(), N_SECT | N_EXT, 1, 24),
                ("___synth_globals".to_string(), N_SECT | N_EXT, 2, 32),
                ("_host_add".to_string(), N_UNDF | N_EXT, NO_SECT, 0),
            ]
        );
        let (_, _, dy, _) = load_commands(&obj);
        let ranges: Vec<u32> = (0..6).map(|i| u32_at(&obj, dy + 8 + 4 * i)).collect();
        assert_eq!(
            ranges,
            vec![0, 0, 0, 5, 5, 1],
            "ilocal nlocal iextdef nextdef iundef nundef"
        );
    }

    #[test]
    fn relocations_map_kind_for_kind_all_extern_length_2() {
        let (f, d, ext) = fixture();
        let obj = build_macho_object_full(&f, &d, &ext).unwrap();
        let (secs, _, _, _) = load_commands(&obj);
        let (reloff, nreloc) = (secs[0].6, secs[0].7);
        let syms = symbols(&obj);
        let mut got = Vec::new();
        for i in 0..nreloc {
            let r = reloff + i * RELOC_SIZE;
            let addr = u32_at(&obj, r) as i32;
            let packed = u32_at(&obj, r + 4);
            let symnum = (packed & 0xFF_FFFF) as usize;
            let pcrel = (packed >> 24) & 1;
            let length = (packed >> 25) & 3;
            let extern_ = (packed >> 27) & 1;
            let ty = packed >> 28;
            assert_eq!(length, 2);
            assert_eq!(extern_, 1);
            got.push((addr, ty, pcrel, syms[symnum].0.clone()));
        }
        assert_eq!(
            got,
            vec![
                (0, ARM64_RELOC_BRANCH26, 1, "_func_2".to_string()),
                (8, ARM64_RELOC_PAGE21, 1, "___synth_globals".to_string()),
                (12, ARM64_RELOC_PAGEOFF12, 0, "___synth_globals".to_string()),
                (16, ARM64_RELOC_BRANCH26, 1, "_host_add".to_string()),
                (28, ARM64_RELOC_BRANCH26, 1, "_func_1".to_string()),
            ]
        );
    }

    #[test]
    fn text_and_data_are_byte_identical_to_the_elf_writer() {
        // The property the oracle checks from outside, at unit scale: both
        // containers are laid around ONE plan.
        let (f, d, ext) = fixture();
        let elf = build_relocatable_object_full(&f, &d, &ext).unwrap();
        let mo = build_macho_object_full(&f, &d, &ext).unwrap();
        let plan = plan_object(&f, &d, &ext).unwrap();
        let (secs, _, _, _) = load_commands(&mo);
        assert_eq!(
            &mo[secs[0].4..secs[0].4 + secs[0].3 as usize],
            &plan.text[..]
        );
        assert_eq!(
            &mo[secs[1].4..secs[1].4 + secs[1].3 as usize],
            &plan.data[..]
        );
        // ELF .text sits at ehdr+64 in this writer's layout.
        assert_eq!(&elf[64..64 + plan.text.len()], &plan.text[..]);
    }

    #[test]
    fn no_globals_means_a_single_text_section() {
        let f = vec![ElfFunction::code(
            vec!["func_0".into(), "f".into()],
            vec![0xE0, 0x00, 0x80, 0x52, 0xC0, 0x03, 0x5F, 0xD6],
            vec![],
        )];
        let obj = build_macho_object_full(&f, &DataBlob::default(), &[]).unwrap();
        let (secs, _, _, _) = load_commands(&obj);
        assert_eq!(secs.len(), 1);
        assert_eq!(secs[0].0, "__text");
        assert_eq!(secs[0].6, 0, "no relocations: reloff 0");
        assert_eq!(secs[0].7, 0);
        assert_eq!(
            symbols(&obj),
            vec![
                ("_func_0".to_string(), N_SECT | N_EXT, 1, 0),
                ("_f".to_string(), N_SECT | N_EXT, 1, 0),
            ]
        );
    }

    #[test]
    fn unplaced_symbol_is_the_same_1013_err_as_elf() {
        let f = vec![ElfFunction::code(
            vec!["func_1".into()],
            vec![0x00, 0x00, 0x00, 0x94],
            vec![CodeRelocation {
                offset: 0,
                symbol: "func_0".into(),
                kind: RelocKind::AArch64Call26,
            }],
        )];
        let e = build_macho_object_full(&f, &DataBlob::default(), &[]).unwrap_err();
        let msg = format!("{e}");
        assert!(
            msg.contains("targets symbol 'func_0', which this object does not place"),
            "{msg}"
        );
        let e2 = build_relocatable_object_full(&f, &DataBlob::default(), &[]).unwrap_err();
        assert_eq!(format!("{e2}"), msg, "one plan, one refusal");
    }
}
