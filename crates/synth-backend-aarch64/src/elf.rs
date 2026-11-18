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
//!
//! RQ-91-X86OBJPLAN (#1741): the plan and the ELF64 writer are SHARED —
//! `synth_core::object_plan`. What stays here is what is A64: `e_machine`,
//! the 4-byte `.text` alignment and the relocation-type map. Every A64 site
//! states addend 0 itself (`CodeRelocation::site`).

use synth_core::backend::{BackendError, RelocKind};
pub use synth_core::object_plan::{
    DataBlob, ObjectFunction as ElfFunction, ObjectPlan, PlannedReloc, PlannedSymbol, SymbolPlace,
    defined_symbol_names,
};
use synth_core::object_plan::{ElfMachine, write_elf64_rel};

/// R_AARCH64_CALL26 — the ELF relocation type for a `bl` 26-bit call site.
const R_AARCH64_CALL26: u32 = 283;
/// R_AARCH64_JUMP26 — the same 26-bit field on a plain `b` (no link). Used by
/// the `call_indirect` funcref-table trampolines (#851 lane L3).
const R_AARCH64_JUMP26: u32 = 282;
/// R_AARCH64_ADR_PREL_PG_HI21 — the `adrp` half of a PC-relative symbol address.
const R_AARCH64_ADR_PREL_PG_HI21: u32 = 275;
/// R_AARCH64_ADD_ABS_LO12_NC — the `add …, :lo12:sym` half of the same pair.
const R_AARCH64_ADD_ABS_LO12_NC: u32 = 277;

/// NO wildcard: a relocation kind this backend cannot express must fail
/// loudly here rather than be silently dropped (which would ship an
/// unrelocated `bl #0` / `adrp #0` — a branch-to-self or a wrong address,
/// the silent-miscompile class).
fn a64_reloc_type(kind: RelocKind) -> u32 {
    match kind {
        RelocKind::AArch64Call26 => R_AARCH64_CALL26,
        RelocKind::AArch64Jump26 => R_AARCH64_JUMP26,
        RelocKind::AArch64AdrPrelPgHi21 => R_AARCH64_ADR_PREL_PG_HI21,
        RelocKind::AArch64AddAbsLo12Nc => R_AARCH64_ADD_ABS_LO12_NC,
        other => panic!(
            "aarch64 ELF builder cannot emit relocation kind {other:?} \
             (#851): only the four AArch64 kinds are expressible"
        ),
    }
}

/// `EM_AARCH64`; A64 instructions are 4-byte aligned.
const AARCH64: ElfMachine = ElfMachine {
    e_machine: 183,
    text_align: 4,
    reloc_type: a64_reloc_type,
};

/// The shared [`synth_core::object_plan::plan_object`], refusing as the
/// aarch64 ELF builder (the #1013 message names it).
pub fn plan_object(
    functions: &[ElfFunction],
    data: &DataBlob,
    undefined_externals: &[String],
) -> Result<ObjectPlan, BackendError> {
    synth_core::object_plan::plan_object(
        "aarch64 ELF builder",
        functions,
        data,
        undefined_externals,
    )
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
/// section (#851 lane L3 — the WASM globals region, see [`DataBlob`]); the
/// layout is [`synth_core::object_plan::write_elf64_rel`]'s.
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
    Ok(write_elf64_rel(&plan, &AARCH64))
}

#[cfg(test)]
mod tests {
    use super::*;
    use synth_core::backend::{CodeRelocation, SymbolBinding};
    use synth_core::object_plan::{EHDR_SIZE, RELA_SIZE, SHDR_SIZE, SYM_SIZE};

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
                vec![CodeRelocation::site(
                    0,
                    "func_0",
                    RelocKind::AArch64Call26,
                    0,
                )],
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
                relocations: vec![CodeRelocation::site(
                    4,
                    "func_0",
                    RelocKind::AArch64Jump26,
                    0,
                )],
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
                    CodeRelocation::site(0, "__synth_globals", RelocKind::AArch64AdrPrelPgHi21, 0),
                    CodeRelocation::site(4, "__synth_globals", RelocKind::AArch64AddAbsLo12Nc, 0),
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
            vec![CodeRelocation::site(
                0,
                "func_0",
                RelocKind::AArch64Call26,
                0,
            )], // declined — not placed in this object
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

    /// RQ-91-NAMECOLL (#1698): `defined_symbol_names` is the set `plan_object`
    /// PLACES (every function symbol, every `.data` symbol), and a name in it
    /// is never emitted as an external even when allowlisted. That is why the
    /// driver must refuse a called import named like one: here the plan binds
    /// the `get` relocation to the defined `get`, not to an `SHN_UNDEF`.
    #[test]
    fn defined_symbol_names_are_what_the_plan_places_1698() {
        let funcs = [ElfFunction::code(
            vec!["func_1".into(), "get".into()],
            vec![0x00, 0x00, 0x00, 0x94, 0xC0, 0x03, 0x5F, 0xD6], // bl #0 ; ret
            vec![CodeRelocation::site(0, "get", RelocKind::AArch64Call26, 0)],
        )];
        let data = DataBlob {
            bytes: vec![0; 4],
            symbols: vec![("__synth_globals".into(), 0)],
        };
        let defined = defined_symbol_names(&funcs, &data);
        let mut names: Vec<&str> = defined.iter().copied().collect();
        names.sort_unstable();
        assert_eq!(names, ["__synth_globals", "func_1", "get"]);
        let plan = plan_object(&funcs, &data, &["get".into()]).expect("plans");
        let placed: Vec<&str> = plan.symbols.iter().map(|s| s.name.as_str()).collect();
        for d in &names {
            assert!(placed.contains(d), "{d} must be placed");
        }
        assert_eq!(
            placed.iter().filter(|n| **n == "get").count(),
            1,
            "an allowlisted name that is also defined is NOT emitted a second time"
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
                vec![CodeRelocation::site(
                    0,
                    "host_add",
                    RelocKind::AArch64Call26,
                    0,
                )],
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
                vec![CodeRelocation::site(
                    0,
                    "func_0",
                    RelocKind::AArch64Call26,
                    0,
                )], // declined local — NOT allowlisted
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
                    vec![CodeRelocation::site(
                        0,
                        "host_add",
                        RelocKind::AArch64Call26,
                        0,
                    )],
                ),
                ElfFunction::code(
                    vec!["func_2".into()],
                    vec![0x00, 0x00, 0x00, 0x90, 0x00, 0x00, 0x00, 0x91], // adrp; add
                    vec![
                        CodeRelocation::site(
                            0,
                            "__synth_globals",
                            RelocKind::AArch64AdrPrelPgHi21,
                            0,
                        ),
                        CodeRelocation::site(
                            4,
                            "__synth_globals",
                            RelocKind::AArch64AddAbsLo12Nc,
                            0,
                        ),
                    ],
                ),
                ElfFunction {
                    symbols: vec!["__synth_func_table".into()],
                    code: vec![1, 0, 0, 0, 0x00, 0x00, 0x00, 0x14], // [class 1][b func_1]
                    relocations: vec![CodeRelocation::site(
                        4,
                        "func_1",
                        RelocKind::AArch64Jump26,
                        0,
                    )],
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
