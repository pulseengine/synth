//! Minimal RISC-V ELF builder — emits ET_REL or ET_EXEC for RV32IMAC.
//!
//! Mirrors `synth-backend::elf_builder` (ARM) but targets EM_RISCV (0xF3)
//! and writes RISC-V-flavored e_flags. The skeleton only handles the
//! mechanics of producing a well-formed ELF; the instruction selection
//! and code-byte production happen upstream in `synth-synthesis::riscv`.
//!
//! What this skeleton does *now*:
//! - Construct a 32-bit little-endian ELF header
//! - Write `.text` containing concatenated function bytes
//! - Optionally emit a `.symtab` + `.strtab` with one symbol per function
//! - Resolve `Jal`/`Branch`/`Call` ops to byte offsets after layout
//!
//! What it leaves to follow-ups (B3):
//! - Vector tables / mtvec setup
//! - PMP init code linkage
//! - Linker script generation
//! - Multiple sections (.rodata, .bss, .data init copies)

use crate::encoder::{RiscVEncoder, RiscVEncodingError};
use crate::register::Reg;
use crate::riscv_op::RiscVOp;
use std::collections::HashMap;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ElfBuildError {
    #[error("encoding error: {0}")]
    Encoding(#[from] RiscVEncodingError),

    #[error("undefined label `{0}`")]
    UndefinedLabel(String),

    /// #882 hard gate: a label defined MORE than once in one function's
    /// stream. The resolution map is last-wins on insert, so a duplicate
    /// would silently rebind every reference to the later position — a
    /// wrong-offset branch, i.e. a silent miscompile. The selector's
    /// monotonic `fresh_label` counter makes duplicates unconstructible
    /// today; this emit-time check makes that a structural invariant
    /// (every referenced label resolves to EXACTLY ONE definition inside
    /// the current function) instead of a convention.
    #[error("duplicate label `{0}` (defined at byte {1} and byte {2})")]
    DuplicateLabel(String, u32, u32),

    #[error("function `{0}` is empty")]
    EmptyFunction(String),

    #[error("unsupported in skeleton: {0}")]
    Unsupported(&'static str),

    /// RQ-63-RVGLOBAL: a function relocates against the globals region
    /// (`__synth_globals`) but the driver placed NO region in this object.
    /// Emitting the symbol UNDEFINED would hand the linker a dangling
    /// reference to something no object defines — the #1102 class. Refuse.
    #[error(
        "function code relocates against `{0}` but this object ships no globals \
         region — the driver compiled a global access without placing the image \
         (RQ-63-RVGLOBAL; refusing to emit a dangling reference)"
    )]
    DanglingGlobalsReloc(String),
}

/// One compiled function — name + a sequence of RISC-V ops (with embedded
/// `Label { name }` markers to anchor branch targets).
#[derive(Debug, Clone)]
pub struct RiscVElfFunction {
    pub name: String,
    pub ops: Vec<RiscVOp>,
}

/// #871: one `R_RISCV_CALL_PLT` call-site relocation. `offset` points at the
/// `auipc` of an 8-byte `auipc ra, 0 ; jalr ra, 0(ra)` placeholder pair;
/// `symbol` is the target symbol name. From [`RiscVElfBuilder::
/// assemble_single_function`] the offset is FUNCTION-relative; the offsets
/// passed to [`RiscVElfBuilder::build_object`] are `.text`-relative.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RiscVCallReloc {
    pub offset: u32,
    pub symbol: String,
    /// Which `R_RISCV_*` type this record carries (RQ-63-RVGLOBAL widened
    /// the builder past call sites: the globals `la` pair emits an
    /// `R_RISCV_HI20` + `R_RISCV_LO12_I` against `__synth_globals`).
    pub kind: RiscVRelocKind,
}

/// The relocation types the RV32 object emits — each fixed at the site that
/// knows the instruction shape, never re-derived at the emitter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RiscVRelocKind {
    /// `R_RISCV_CALL_PLT` on an 8-byte `auipc`+`jalr` call placeholder (#871).
    CallPlt,
    /// `R_RISCV_HI20` on the `lui` of an absolute-address `la` pair
    /// (RQ-63-RVGLOBAL).
    Hi20,
    /// `R_RISCV_LO12_I` on the `addi` of an absolute-address `la` pair
    /// (RQ-63-RVGLOBAL).
    Lo12I,
}

impl RiscVRelocKind {
    /// The ELF `r_info` type field.
    pub fn r_type(self) -> u32 {
        match self {
            RiscVRelocKind::CallPlt => R_RISCV_CALL_PLT,
            RiscVRelocKind::Hi20 => R_RISCV_HI20,
            RiscVRelocKind::Lo12I => R_RISCV_LO12_I,
        }
    }

    /// The arch-neutral [`synth_core::backend::RelocKind`] this record
    /// carries out of the backend (a total mapping, kept beside `r_type` so
    /// the two enums' correspondence lives in ONE place).
    pub fn core_kind(self) -> synth_core::backend::RelocKind {
        match self {
            RiscVRelocKind::CallPlt => synth_core::backend::RelocKind::RiscvCallPlt,
            RiscVRelocKind::Hi20 => synth_core::backend::RelocKind::RiscvHi20,
            RiscVRelocKind::Lo12I => synth_core::backend::RelocKind::RiscvLo12I,
        }
    }
}

/// `R_RISCV_CALL_PLT` — the modern auipc+jalr call-pair relocation type
/// (`R_RISCV_CALL` = 18 is deprecated by the psABI).
pub const R_RISCV_CALL_PLT: u32 = 19;

/// `R_RISCV_HI20` — the `lui` half of an absolute symbol address
/// (`((S + A) + 0x800) >> 12`). RQ-63-RVGLOBAL.
pub const R_RISCV_HI20: u32 = 26;

/// `R_RISCV_LO12_I` — the I-type (`addi`/`lw`) low-12 half of an absolute
/// symbol address (`(S + A) & 0xFFF`, sign-extended). RQ-63-RVGLOBAL.
pub const R_RISCV_LO12_I: u32 = 27;

/// The 8-byte external-call placeholder the linker patches via
/// `R_RISCV_CALL_PLT`: `auipc ra, 0` (0x00000097) + `jalr ra, 0(ra)`
/// (0x000080E7) — the canonical un-relaxed `call` pseudo-instruction
/// expansion. Register fields are preserved by the relocation (the linker
/// only patches the immediates).
pub const CALL_PLACEHOLDER_BYTES: [u8; 8] = [0x97, 0x00, 0x00, 0x00, 0xE7, 0x80, 0x00, 0x00];

/// Output mode — forces the ELF file type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ElfMode {
    /// `ET_REL` — relocatable object, suitable for `ld` / linker.
    Relocatable,
    /// `ET_EXEC` — fully linked, statically positioned executable.
    Executable,
}

pub struct RiscVElfBuilder {
    pub xlen: u8,
    pub mode: ElfMode,
    /// Entry point virtual address (only used for `Executable` mode).
    pub entry_addr: u32,
    /// Base virtual address of `.text` (only used for `Executable` mode).
    pub text_base: u32,
}

impl RiscVElfBuilder {
    pub fn new_relocatable() -> Self {
        Self {
            xlen: 32,
            mode: ElfMode::Relocatable,
            entry_addr: 0,
            text_base: 0,
        }
    }

    pub fn new_executable(entry_addr: u32, text_base: u32) -> Self {
        Self {
            xlen: 32,
            mode: ElfMode::Executable,
            entry_addr,
            text_base,
        }
    }

    /// Build the full ELF blob. Functions are concatenated in order;
    /// each function is independently resolved (no cross-function branch
    /// labels — those will need a second pass once we add `Call`).
    pub fn build(&self, functions: &[RiscVElfFunction]) -> Result<Vec<u8>, ElfBuildError> {
        self.build_with_data(functions, &[])
    }

    /// Build the full ELF blob, shipping `wasm_data` (the #798 packed
    /// active-data-segment records — see
    /// `synth_core::static_data_addr::pack_segment_records`) as a `.wasm_data`
    /// PROGBITS section. The generated linker script places it in flash and
    /// the generated startup copies each record to
    /// `__linear_memory_base + off` at reset. An EMPTY `wasm_data` omits the
    /// section entirely, producing bytes identical to the pre-#798 layout —
    /// data-free modules (and every frozen fixture without segments) are
    /// untouched.
    pub fn build_with_data(
        &self,
        functions: &[RiscVElfFunction],
        wasm_data: &[u8],
    ) -> Result<Vec<u8>, ElfBuildError> {
        self.build_object(functions, wasm_data, &[])
    }

    /// #871: assemble ONE function to raw bytes plus its external-call
    /// relocations (function-relative offsets). This is the byte source the
    /// backend's `compile_function` path uses — identical bytes to what
    /// [`Self::build_object`] would place in `.text` for this function.
    pub fn assemble_single_function(
        &self,
        f: &RiscVElfFunction,
    ) -> Result<(Vec<u8>, Vec<RiscVCallReloc>), ElfBuildError> {
        let encoder = RiscVEncoder::new_rv32();
        self.assemble_function(&encoder, f)
    }

    /// Build the full ELF blob with data records AND `.text`-relative call
    /// relocations (#871). `extra_call_relocs` covers the CLI path, where the
    /// function bytes arrive pre-assembled (placeholder ops) and the call
    /// relocations were captured by `assemble_single_function` at
    /// per-function compile time. Relocation symbols that match a defined
    /// function name resolve against that symbol; every other symbol is added
    /// as an UNDEFINED global (`nm -u` shows `U <symbol>`) for the host
    /// linker to resolve — exactly the ARM `--relocatable` import contract.
    /// With no relocations at all the object is byte-identical to the
    /// pre-#871 layout (no `.rela.text` section, no undefined symbols).
    pub fn build_object(
        &self,
        functions: &[RiscVElfFunction],
        wasm_data: &[u8],
        extra_call_relocs: &[RiscVCallReloc],
    ) -> Result<Vec<u8>, ElfBuildError> {
        self.build_object_with_globals(functions, wasm_data, &[], extra_call_relocs)
    }

    /// RQ-63-RVGLOBAL (#242): [`Self::build_object`] plus the synth-emitted
    /// globals region. A NON-EMPTY `globals_image` ships as a `.data` PROGBITS
    /// section (SHF_ALLOC | SHF_WRITE, 4-aligned) with ONE global `STT_OBJECT`
    /// symbol, `__synth_globals` ([`crate::globals::GLOBALS_SYMBOL`]),
    /// spanning it; the `la` pairs the selector emits relocate against that
    /// symbol (`R_RISCV_HI20` + `R_RISCV_LO12_I`) and the host linker places
    /// the region wherever its script puts `.data` — RAM, copied from flash by
    /// the standard C-runtime startup (synth's own `riscv-runtime` startup
    /// does exactly that). An EMPTY image omits the section and the symbol,
    /// so a globals-free object is byte-identical to the pre-v0.63 layout.
    ///
    /// A relocation naming `__synth_globals` while the image is empty is
    /// REFUSED ([`ElfBuildError::DanglingGlobalsReloc`]) rather than emitted
    /// as an undefined symbol — a driver that compiled a global access
    /// without placing the region is a compiler bug, not a link-time surprise.
    pub fn build_object_with_globals(
        &self,
        functions: &[RiscVElfFunction],
        wasm_data: &[u8],
        globals_image: &[u8],
        extra_call_relocs: &[RiscVCallReloc],
    ) -> Result<Vec<u8>, ElfBuildError> {
        let encoder = RiscVEncoder::new_rv32();
        let globals_symbol = crate::globals::GLOBALS_SYMBOL;

        // 1. Resolve labels per-function, accumulate code bytes & symbols.
        let mut text: Vec<u8> = Vec::new();
        let mut symbols: Vec<(String, u32, u32)> = Vec::new(); // (name, st_value, st_size)
        let mut call_relocs: Vec<RiscVCallReloc> = Vec::new();

        for f in functions {
            if f.ops.is_empty() {
                return Err(ElfBuildError::EmptyFunction(f.name.clone()));
            }
            let function_offset = text.len() as u32;
            let (bytes, fn_relocs) = self.assemble_function(&encoder, f)?;
            let function_size = bytes.len() as u32;
            text.extend_from_slice(&bytes);
            symbols.push((f.name.clone(), function_offset, function_size));
            call_relocs.extend(fn_relocs.into_iter().map(|r| RiscVCallReloc {
                offset: function_offset + r.offset,
                symbol: r.symbol,
                kind: r.kind,
            }));
        }
        call_relocs.extend_from_slice(extra_call_relocs);

        let has_globals = !globals_image.is_empty();
        // RQ-63-RVGLOBAL: a globals reference with no region is a dangling
        // symbol — refuse up front, never emit it undefined.
        if !has_globals && call_relocs.iter().any(|r| r.symbol == globals_symbol) {
            return Err(ElfBuildError::DanglingGlobalsReloc(
                globals_symbol.to_string(),
            ));
        }
        if has_globals && self.mode == ElfMode::Executable {
            // The builder places `.text` at `text_base` but has no data
            // address contract — nothing in-tree builds an ET_EXEC with a
            // globals region; refuse rather than write a 0 st_value.
            return Err(ElfBuildError::Unsupported(
                "globals region (.data) in ET_EXEC mode — the RV32 object is always host-linked ET_REL",
            ));
        }

        // #871: resolve relocation symbols. Defined function names — and the
        // globals object symbol, when shipped — win; anything else becomes an
        // UNDEFINED global symbol (dedup'd, in first-use order so output is
        // deterministic).
        let n_funcs = symbols.len();
        let mut undefined: Vec<String> = Vec::new();
        for r in &call_relocs {
            let defined = symbols.iter().any(|(n, _, _)| n == &r.symbol)
                || (has_globals && r.symbol == globals_symbol);
            if !defined && !undefined.iter().any(|u| u == &r.symbol) {
                undefined.push(r.symbol.clone());
            }
        }
        // symtab index: [0] null, [1..=n_funcs] functions, [n_funcs+1] the
        // globals object (when shipped), then the undefined externals.
        let globals_sym_index = n_funcs as u32 + 1;
        let n_defined = n_funcs + usize::from(has_globals);
        let sym_index_of = |name: &str| -> u32 {
            if let Some(i) = symbols.iter().position(|(n, _, _)| n == name) {
                (i + 1) as u32
            } else if has_globals && name == globals_symbol {
                globals_sym_index
            } else {
                let u = undefined
                    .iter()
                    .position(|u| u == name)
                    .expect("every reloc symbol is defined or collected as undefined");
                (n_defined + 1 + u) as u32
            }
        };
        let has_relocs = !call_relocs.is_empty();

        // 2. Section ordering (— entries marked § exist only when their
        //    payload is non-empty; without them the layout is bit-identical
        //    to the pre-#798 / pre-v0.63 objects):
        //    [0]  null
        //    [1]  .text (PROGBITS, AX)
        //    [·]§ .wasm_data (PROGBITS, A) — packed segment records (#798)
        //    [·]§ .data (PROGBITS, WA) — the globals image (RQ-63-RVGLOBAL)
        //    [·]  .symtab (SYMTAB)
        //    [·]  .strtab (STRTAB) — symbol names
        //    [·]  .shstrtab (STRTAB) — section names
        //    [·]§ .rela.text (RELA) — appended LAST (#871)
        let has_wasm_data = !wasm_data.is_empty();
        let mut elf = Vec::new();
        let ehsize = 52usize;
        let shentsize = 40usize;
        let phentsize = 32usize;

        elf.resize(ehsize, 0);

        // .text
        let text_offset = elf.len();
        elf.extend_from_slice(&text);

        // Pad to 4-byte alignment for what follows (.wasm_data / .data / .symtab).
        while elf.len() % 4 != 0 {
            elf.push(0);
        }

        // .wasm_data — packed active-segment records (#798), 4-aligned.
        let wasm_data_offset = elf.len();
        if has_wasm_data {
            elf.extend_from_slice(wasm_data);
            // pack_segment_records pads each record to 4 bytes, but stay
            // robust to arbitrary blobs: re-align for the symbol table.
            while elf.len() % 4 != 0 {
                elf.push(0);
            }
        }

        // .data — the globals initializer image (RQ-63-RVGLOBAL), 4-aligned.
        let data_offset = elf.len();
        if has_globals {
            elf.extend_from_slice(globals_image);
            while elf.len() % 4 != 0 {
                elf.push(0);
            }
        }

        // .strtab — built first so we know offsets for .symtab.
        let mut strtab = vec![0u8]; // ELF requires a leading NUL.
        let mut name_offsets: Vec<u32> = Vec::with_capacity(symbols.len());
        for (name, _, _) in &symbols {
            name_offsets.push(strtab.len() as u32);
            strtab.extend_from_slice(name.as_bytes());
            strtab.push(0);
        }
        // RQ-63-RVGLOBAL: the globals object symbol name follows the functions.
        let globals_name_offset = strtab.len() as u32;
        if has_globals {
            strtab.extend_from_slice(globals_symbol.as_bytes());
            strtab.push(0);
        }
        // #871: undefined external symbol names follow the defined names.
        let mut undef_name_offsets: Vec<u32> = Vec::with_capacity(undefined.len());
        for name in &undefined {
            undef_name_offsets.push(strtab.len() as u32);
            strtab.extend_from_slice(name.as_bytes());
            strtab.push(0);
        }

        // Section indices — the optional payload sections shift everything
        // after them up by one each.
        let wasm_data_shift = if has_wasm_data { 1u32 } else { 0 };
        let data_shift = if has_globals { 1u32 } else { 0 };
        let data_index = 2 + wasm_data_shift; // valid only when has_globals
        let symtab_index = 2 + wasm_data_shift + data_shift;
        let strtab_index = symtab_index + 1;
        let shstrtab_index = symtab_index + 2;

        // .symtab — entry 0 is reserved (all zero).
        let symtab_offset = elf.len();
        elf.extend_from_slice(&[0u8; 16]); // null symbol
        for (i, (_, value, size)) in symbols.iter().enumerate() {
            let st_name = name_offsets[i];
            let st_value = if self.mode == ElfMode::Executable {
                self.text_base + *value
            } else {
                *value
            };
            let st_info = (1u8 << 4) | 2; // STB_GLOBAL << 4 | STT_FUNC
            let st_other = 0u8;
            let st_shndx: u16 = 1; // .text
            let mut entry = [0u8; 16];
            entry[0..4].copy_from_slice(&st_name.to_le_bytes());
            entry[4..8].copy_from_slice(&st_value.to_le_bytes());
            entry[8..12].copy_from_slice(&size.to_le_bytes());
            entry[12] = st_info;
            entry[13] = st_other;
            entry[14..16].copy_from_slice(&st_shndx.to_le_bytes());
            elf.extend_from_slice(&entry);
        }
        // RQ-63-RVGLOBAL: `__synth_globals` — STB_GLOBAL / STT_OBJECT in
        // `.data`, value 0 (section-relative), size = the whole image.
        if has_globals {
            let mut entry = [0u8; 16];
            entry[0..4].copy_from_slice(&globals_name_offset.to_le_bytes());
            entry[8..12].copy_from_slice(&(globals_image.len() as u32).to_le_bytes());
            entry[12] = (1u8 << 4) | 1; // STB_GLOBAL << 4 | STT_OBJECT
            entry[14..16].copy_from_slice(&(data_index as u16).to_le_bytes());
            elf.extend_from_slice(&entry);
        }
        // #871: undefined externals — STB_GLOBAL / STT_NOTYPE / SHN_UNDEF
        // (`nm` shows them as `U <name>`, exactly like the ARM object).
        for off in &undef_name_offsets {
            let mut entry = [0u8; 16];
            entry[0..4].copy_from_slice(&off.to_le_bytes());
            entry[12] = 1u8 << 4; // STB_GLOBAL << 4 | STT_NOTYPE
            // st_value/st_size stay 0, st_shndx stays 0 (SHN_UNDEF).
            elf.extend_from_slice(&entry);
        }
        let symtab_size = (n_defined + undefined.len() + 1) * 16;

        // .strtab
        let strtab_offset = elf.len();
        elf.extend_from_slice(&strtab);

        // .shstrtab — fixed contents
        let shstrtab_offset = elf.len();
        let shstrtab_data = build_shstrtab(has_wasm_data, has_globals, has_relocs);
        elf.extend_from_slice(&shstrtab_data.bytes);

        // #871: .rela.text — placed after .shstrtab, 4-aligned. ELF32 RELA
        // entries are 12 bytes: r_offset, r_info = (sym << 8) | type,
        // r_addend (always 0 — the target is the symbol itself; a globals
        // slot offset is a plain immediate on the following `lw`/`sw`).
        let mut rela_offset = 0usize;
        if has_relocs {
            while elf.len() % 4 != 0 {
                elf.push(0);
            }
            rela_offset = elf.len();
            for r in &call_relocs {
                let r_info = (sym_index_of(&r.symbol) << 8) | r.kind.r_type();
                elf.extend_from_slice(&r.offset.to_le_bytes());
                elf.extend_from_slice(&r_info.to_le_bytes());
                elf.extend_from_slice(&0i32.to_le_bytes());
            }
        }

        // Pad to 4-byte for the section header table.
        while elf.len() % 4 != 0 {
            elf.push(0);
        }

        let shoff = elf.len();

        // Section headers
        let text_size = text.len() as u32;
        let mut shdrs = vec![
            // [0] null
            ShEntry::null(),
            // [1] .text
            ShEntry {
                sh_name: shstrtab_data.text_off,
                sh_type: 1,    // SHT_PROGBITS
                sh_flags: 0x6, // SHF_ALLOC | SHF_EXECINSTR
                sh_addr: if self.mode == ElfMode::Executable {
                    self.text_base
                } else {
                    0
                },
                sh_offset: text_offset as u32,
                sh_size: text_size,
                sh_link: 0,
                sh_info: 0,
                sh_addralign: 4,
                sh_entsize: 0,
            },
        ];
        if has_wasm_data {
            // [2] .wasm_data — SHF_ALLOC only (a read-only flash image; the
            // startup copies it into linear-memory RAM, code never executes
            // or writes it in place).
            shdrs.push(ShEntry {
                sh_name: shstrtab_data.wasm_data_off,
                sh_type: 1,    // SHT_PROGBITS
                sh_flags: 0x2, // SHF_ALLOC
                sh_addr: 0,
                sh_offset: wasm_data_offset as u32,
                sh_size: wasm_data.len() as u32,
                sh_link: 0,
                sh_info: 0,
                sh_addralign: 4,
                sh_entsize: 0,
            });
        }
        if has_globals {
            // [2/3] .data — SHF_ALLOC | SHF_WRITE: `global.set` writes it in
            // place, so a linker script MUST give it a RAM run address (every
            // standard bare-metal script does, with a flash load address and
            // a startup copy). Word alignment is all the paired `lw`/`sw`
            // lowering requires.
            shdrs.push(ShEntry {
                sh_name: shstrtab_data.data_off,
                sh_type: 1,    // SHT_PROGBITS
                sh_flags: 0x3, // SHF_WRITE | SHF_ALLOC
                sh_addr: 0,
                sh_offset: data_offset as u32,
                sh_size: globals_image.len() as u32,
                sh_link: 0,
                sh_info: 0,
                sh_addralign: 4,
                sh_entsize: 0,
            });
        }
        shdrs.extend([
            // [·] .symtab
            ShEntry {
                sh_name: shstrtab_data.symtab_off,
                sh_type: 2, // SHT_SYMTAB
                sh_flags: 0,
                sh_addr: 0,
                sh_offset: symtab_offset as u32,
                sh_size: symtab_size as u32,
                sh_link: strtab_index,
                sh_info: 1, // index of first global symbol
                sh_addralign: 4,
                sh_entsize: 16,
            },
            // [·] .strtab
            ShEntry {
                sh_name: shstrtab_data.strtab_off,
                sh_type: 3, // SHT_STRTAB
                sh_flags: 0,
                sh_addr: 0,
                sh_offset: strtab_offset as u32,
                sh_size: strtab.len() as u32,
                sh_link: 0,
                sh_info: 0,
                sh_addralign: 1,
                sh_entsize: 0,
            },
            // [·] .shstrtab
            ShEntry {
                sh_name: shstrtab_data.shstrtab_off,
                sh_type: 3, // SHT_STRTAB
                sh_flags: 0,
                sh_addr: 0,
                sh_offset: shstrtab_offset as u32,
                sh_size: shstrtab_data.bytes.len() as u32,
                sh_link: 0,
                sh_info: 0,
                sh_addralign: 1,
                sh_entsize: 0,
            },
        ]);
        // #871: .rela.text appended as the LAST section so every existing
        // index (.text=1, shstrndx, symtab sh_link) is unchanged — reloc-free
        // objects stay byte-identical by construction.
        if has_relocs {
            shdrs.push(ShEntry {
                sh_name: shstrtab_data.rela_text_off,
                sh_type: 4,     // SHT_RELA
                sh_flags: 0x40, // SHF_INFO_LINK
                sh_addr: 0,
                sh_offset: rela_offset as u32,
                sh_size: (call_relocs.len() * 12) as u32,
                sh_link: symtab_index,
                sh_info: 1, // relocates .text
                sh_addralign: 4,
                sh_entsize: 12,
            });
        }

        for sh in &shdrs {
            sh.write_into(&mut elf);
        }

        // Now patch up the ELF header at offset 0.
        write_elf_header(
            &mut elf,
            self.xlen,
            self.mode,
            self.entry_addr,
            shoff as u32,
            shdrs.len() as u16,
            shentsize as u16,
            ehsize as u16,
            phentsize as u16,
            shstrtab_index as u16,
        );

        Ok(elf)
    }

    fn assemble_function(
        &self,
        encoder: &RiscVEncoder,
        f: &RiscVElfFunction,
    ) -> Result<(Vec<u8>, Vec<RiscVCallReloc>), ElfBuildError> {
        let mut relocs: Vec<RiscVCallReloc> = Vec::new();
        // Pass 1: compute byte offset of each label.
        let mut byte_offsets: Vec<u32> = Vec::with_capacity(f.ops.len() + 1);
        let mut labels: HashMap<String, u32> = HashMap::new();
        let mut cursor: u32 = 0;
        for op in &f.ops {
            byte_offsets.push(cursor);
            match op {
                RiscVOp::Label { name } => {
                    // #882 hard gate: exactly-one definition per label per
                    // function. `insert` is last-wins — a duplicate would
                    // silently rebind every reference to the later position
                    // (a wrong-offset branch). Hard-error instead.
                    if let Some(prev) = labels.insert(name.clone(), cursor) {
                        return Err(ElfBuildError::DuplicateLabel(name.clone(), prev, cursor));
                    }
                }
                RiscVOp::Call { .. } => cursor += 8, // auipc + jalr pair
                RiscVOp::La { .. } => cursor += 8,   // lui + addi pair (RQ-63-RVGLOBAL)
                _ => cursor += 4,
            }
        }
        byte_offsets.push(cursor);

        // Pass 2: emit bytes, resolving Jal/Branch/Call with the offsets we just collected.
        let mut bytes: Vec<u8> = Vec::with_capacity(cursor as usize);
        for (i, op) in f.ops.iter().enumerate() {
            let here = byte_offsets[i] as i32;
            match op {
                RiscVOp::Label { .. } => {}
                RiscVOp::Jal { rd, label } => {
                    let target = *labels
                        .get(label)
                        .ok_or_else(|| ElfBuildError::UndefinedLabel(label.clone()))?
                        as i32;
                    let inst = encoder.encode_jal(rd.num(), target - here)?;
                    bytes.extend_from_slice(&inst.to_le_bytes());
                }
                RiscVOp::Branch {
                    cond,
                    rs1,
                    rs2,
                    label,
                } => {
                    let target = *labels
                        .get(label)
                        .ok_or_else(|| ElfBuildError::UndefinedLabel(label.clone()))?
                        as i32;
                    let inst = encoder.encode_branch(*cond, rs1.num(), rs2.num(), target - here)?;
                    bytes.extend_from_slice(&inst.to_le_bytes());
                }
                RiscVOp::Call { label } => {
                    // A LABEL-local call resolves to a self-contained
                    // auipc t1 + jalr pair. An EXTERNAL call (#871 — an
                    // imported function, or another function in the object)
                    // emits the canonical 8-byte `auipc ra, 0 ; jalr ra,
                    // 0(ra)` placeholder plus an `R_RISCV_CALL_PLT`
                    // relocation for the linker to patch — mirroring the
                    // ARM `BL` + `R_ARM_THM_CALL` import contract.
                    if let Some(&target) = labels.get(label) {
                        let rel = target as i32 - here;
                        // auipc t1, rel[31:12] + carry
                        let hi = (rel + 0x800) >> 12;
                        let lo = rel - (hi << 12);
                        let auipc = RiscVOp::Auipc {
                            rd: Reg::T1,
                            imm20: (hi as u32) & 0xFFFFF,
                        };
                        bytes.extend_from_slice(&encoder.encode(&auipc)?.to_le_bytes());
                        let jalr = RiscVOp::Jalr {
                            rd: Reg::RA,
                            rs1: Reg::T1,
                            imm: lo,
                        };
                        bytes.extend_from_slice(&encoder.encode(&jalr)?.to_le_bytes());
                    } else {
                        relocs.push(RiscVCallReloc {
                            offset: bytes.len() as u32,
                            symbol: label.clone(),
                            kind: RiscVRelocKind::CallPlt,
                        });
                        bytes.extend_from_slice(&CALL_PLACEHOLDER_BYTES);
                    }
                }
                RiscVOp::La { rd, symbol } => {
                    // RQ-63-RVGLOBAL: the absolute-address pair. Both
                    // immediates are 0 in the object; the linker patches the
                    // `lui` via R_RISCV_HI20 (at +0) and the `addi` via
                    // R_RISCV_LO12_I (at +4). The register fields survive
                    // relocation (only the immediates are rewritten).
                    let here = bytes.len() as u32;
                    relocs.push(RiscVCallReloc {
                        offset: here,
                        symbol: symbol.clone(),
                        kind: RiscVRelocKind::Hi20,
                    });
                    relocs.push(RiscVCallReloc {
                        offset: here + 4,
                        symbol: symbol.clone(),
                        kind: RiscVRelocKind::Lo12I,
                    });
                    let lui = RiscVOp::Lui { rd: *rd, imm20: 0 };
                    bytes.extend_from_slice(&encoder.encode(&lui)?.to_le_bytes());
                    let addi = RiscVOp::Addi {
                        rd: *rd,
                        rs1: *rd,
                        imm: 0,
                    };
                    bytes.extend_from_slice(&encoder.encode(&addi)?.to_le_bytes());
                }
                _ => {
                    let inst = encoder.encode(op)?;
                    bytes.extend_from_slice(&inst.to_le_bytes());
                }
            }
            // Sanity: the byte cursor in pass-1 must match what we actually wrote.
            debug_assert_eq!(bytes.len() as u32, byte_offsets[i + 1]);
        }
        Ok((bytes, relocs))
    }
}

// ────────────────────────────────────────────────────────────────────
// ELF plumbing
// ────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy)]
struct ShEntry {
    sh_name: u32,
    sh_type: u32,
    sh_flags: u32,
    sh_addr: u32,
    sh_offset: u32,
    sh_size: u32,
    sh_link: u32,
    sh_info: u32,
    sh_addralign: u32,
    sh_entsize: u32,
}

impl ShEntry {
    fn null() -> Self {
        Self {
            sh_name: 0,
            sh_type: 0,
            sh_flags: 0,
            sh_addr: 0,
            sh_offset: 0,
            sh_size: 0,
            sh_link: 0,
            sh_info: 0,
            sh_addralign: 0,
            sh_entsize: 0,
        }
    }

    fn write_into(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.sh_name.to_le_bytes());
        out.extend_from_slice(&self.sh_type.to_le_bytes());
        out.extend_from_slice(&self.sh_flags.to_le_bytes());
        out.extend_from_slice(&self.sh_addr.to_le_bytes());
        out.extend_from_slice(&self.sh_offset.to_le_bytes());
        out.extend_from_slice(&self.sh_size.to_le_bytes());
        out.extend_from_slice(&self.sh_link.to_le_bytes());
        out.extend_from_slice(&self.sh_info.to_le_bytes());
        out.extend_from_slice(&self.sh_addralign.to_le_bytes());
        out.extend_from_slice(&self.sh_entsize.to_le_bytes());
    }
}

struct ShstrtabData {
    bytes: Vec<u8>,
    text_off: u32,
    wasm_data_off: u32,
    data_off: u32,
    symtab_off: u32,
    strtab_off: u32,
    shstrtab_off: u32,
    rela_text_off: u32,
}

fn build_shstrtab(with_wasm_data: bool, with_data: bool, with_relocs: bool) -> ShstrtabData {
    let mut bytes = vec![0u8];
    let text_off = bytes.len() as u32;
    bytes.extend_from_slice(b".text\0");
    // Only present when the object ships data (#798) — keeps data-free
    // objects bit-identical to the pre-#798 layout.
    let wasm_data_off = if with_wasm_data {
        let off = bytes.len() as u32;
        bytes.extend_from_slice(b".wasm_data\0");
        off
    } else {
        0
    };
    // Only present when the object ships a globals region (RQ-63-RVGLOBAL)
    // — keeps globals-free objects bit-identical to the pre-v0.63 layout.
    let data_off = if with_data {
        let off = bytes.len() as u32;
        bytes.extend_from_slice(b".data\0");
        off
    } else {
        0
    };
    let symtab_off = bytes.len() as u32;
    bytes.extend_from_slice(b".symtab\0");
    let strtab_off = bytes.len() as u32;
    bytes.extend_from_slice(b".strtab\0");
    let shstrtab_off = bytes.len() as u32;
    bytes.extend_from_slice(b".shstrtab\0");
    // Only present when the object carries call relocations (#871) — keeps
    // reloc-free objects bit-identical to the pre-#871 layout.
    let rela_text_off = if with_relocs {
        let off = bytes.len() as u32;
        bytes.extend_from_slice(b".rela.text\0");
        off
    } else {
        0
    };
    ShstrtabData {
        bytes,
        text_off,
        wasm_data_off,
        data_off,
        symtab_off,
        strtab_off,
        shstrtab_off,
        rela_text_off,
    }
}

#[allow(clippy::too_many_arguments)]
fn write_elf_header(
    out: &mut [u8],
    xlen: u8,
    mode: ElfMode,
    entry: u32,
    shoff: u32,
    shnum: u16,
    shentsize: u16,
    ehsize: u16,
    _phentsize: u16,
    shstrndx: u16,
) {
    // e_ident[0..4] — magic
    out[0..4].copy_from_slice(&[0x7F, b'E', b'L', b'F']);
    // EI_CLASS — 1 = 32-bit, 2 = 64-bit
    out[4] = if xlen == 32 { 1 } else { 2 };
    // EI_DATA — 1 = little endian
    out[5] = 1;
    // EI_VERSION
    out[6] = 1;
    // EI_OSABI = 0 (System V)
    out[7] = 0;
    // EI_ABIVERSION = 0
    out[8] = 0;
    // padding 9..15 already zero

    // e_type
    let e_type: u16 = match mode {
        ElfMode::Relocatable => 1, // ET_REL
        ElfMode::Executable => 2,  // ET_EXEC
    };
    out[16..18].copy_from_slice(&e_type.to_le_bytes());
    // e_machine = 0xF3 (EM_RISCV)
    let e_machine: u16 = 0xF3;
    out[18..20].copy_from_slice(&e_machine.to_le_bytes());
    // e_version = 1
    out[20..24].copy_from_slice(&1u32.to_le_bytes());
    // e_entry
    out[24..28].copy_from_slice(&entry.to_le_bytes());
    // e_phoff = 0 (no program headers in this skeleton)
    out[28..32].copy_from_slice(&0u32.to_le_bytes());
    // e_shoff
    out[32..36].copy_from_slice(&shoff.to_le_bytes());
    // e_flags — RVC + soft float ABI
    let e_flags: u32 = 0x1; // RVC
    out[36..40].copy_from_slice(&e_flags.to_le_bytes());
    // e_ehsize
    out[40..42].copy_from_slice(&ehsize.to_le_bytes());
    // e_phentsize, e_phnum
    out[42..44].copy_from_slice(&0u16.to_le_bytes());
    out[44..46].copy_from_slice(&0u16.to_le_bytes());
    // e_shentsize
    out[46..48].copy_from_slice(&shentsize.to_le_bytes());
    // e_shnum
    out[48..50].copy_from_slice(&shnum.to_le_bytes());
    // e_shstrndx
    out[50..52].copy_from_slice(&shstrndx.to_le_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::register::Reg;

    fn nop_op() -> RiscVOp {
        RiscVOp::Addi {
            rd: Reg::ZERO,
            rs1: Reg::ZERO,
            imm: 0,
        }
    }

    #[test]
    fn build_minimal_elf() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "add".into(),
            ops: vec![
                RiscVOp::Add {
                    rd: Reg::A0,
                    rs1: Reg::A0,
                    rs2: Reg::A1,
                },
                RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::RA,
                    imm: 0,
                }, // ret
            ],
        };
        let elf = builder.build(&[f]).unwrap();
        // Sanity-check the magic bytes and machine type.
        assert_eq!(&elf[0..4], &[0x7F, b'E', b'L', b'F']);
        assert_eq!(elf[4], 1, "EI_CLASS = 32-bit");
        assert_eq!(elf[5], 1, "EI_DATA = little endian");
        // EM_RISCV = 0xF3
        assert_eq!(u16::from_le_bytes([elf[18], elf[19]]), 0xF3);
        // ET_REL
        assert_eq!(u16::from_le_bytes([elf[16], elf[17]]), 1);
    }

    /// MIRROR PIN (#511 estimator↔encoder lesson): the selector's
    /// `emitted_byte_size` must agree with `assemble_function`'s pass-1 sizing
    /// (Label 0 B, Call 8 B, everything else 4 B) on a sequence exercising all
    /// three size classes. `select_inner`'s measured local-promotion decision
    /// (#472) compares functions by `emitted_byte_size`, so drift here would
    /// silently corrupt the no-grow guarantee.
    #[test]
    fn emitted_byte_size_matches_assembled_text() {
        let builder = RiscVElfBuilder::new_relocatable();
        let encoder = RiscVEncoder::new_rv32();
        let ops = vec![
            RiscVOp::Label { name: "f".into() },
            nop_op(),
            RiscVOp::Branch {
                cond: crate::riscv_op::Branch::Ne,
                rs1: Reg::A0,
                rs2: Reg::ZERO,
                label: "f".into(),
            },
            RiscVOp::Call { label: "f".into() },
            // RQ-63-RVGLOBAL: the 8-byte `la` pair — the fourth size class.
            RiscVOp::La {
                rd: Reg::T0,
                symbol: crate::globals::GLOBALS_SYMBOL.into(),
            },
            RiscVOp::Lw {
                rd: Reg::S8,
                rs1: Reg::SP,
                imm: 4,
            },
            RiscVOp::Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            },
        ];
        let f = RiscVElfFunction {
            name: "f".into(),
            ops: ops.clone(),
        };
        let (assembled, _relocs) = builder.assemble_function(&encoder, &f).unwrap();
        assert_eq!(
            assembled.len(),
            crate::selector::emitted_byte_size(&ops),
            "emitted_byte_size drifted from the ELF builder's sizing"
        );
    }

    #[test]
    fn jal_with_label_resolution() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "loop".into(),
            ops: vec![
                RiscVOp::Label { name: "top".into() },
                nop_op(),
                RiscVOp::Jal {
                    rd: Reg::ZERO,
                    label: "top".into(),
                },
            ],
        };
        let bytes = builder.build(&[f]).unwrap();
        // .text starts at 52 (ELF header). First instruction is the nop (4 bytes).
        // The JAL is at offset 52+4 = 56 and targets offset 52 → rel = -4
        // jal zero, -4 encodes to 0xFFDFF06F (rd=0, imm=-4)
        let jal = u32::from_le_bytes([bytes[56], bytes[57], bytes[58], bytes[59]]);
        assert_eq!(jal, 0xFFDFF06F);
    }

    #[test]
    fn empty_function_rejected() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "empty".into(),
            ops: vec![],
        };
        assert!(matches!(
            builder.build(&[f]),
            Err(ElfBuildError::EmptyFunction(_))
        ));
    }

    #[test]
    fn undefined_label_rejected() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "broken".into(),
            ops: vec![RiscVOp::Jal {
                rd: Reg::ZERO,
                label: "missing".into(),
            }],
        };
        assert!(matches!(
            builder.build(&[f]),
            Err(ElfBuildError::UndefinedLabel(_))
        ));
    }

    /// #882 hard gate: a label defined twice in one function is a HARD error.
    /// The map insert is last-wins, so a duplicate would silently rebind
    /// every reference to the later position — a wrong-offset branch, i.e. a
    /// silent miscompile. This makes "every referenced label resolves to
    /// exactly one definition inside the current function" structural.
    #[test]
    fn duplicate_label_rejected_882() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "f".into(),
            ops: vec![
                RiscVOp::Label { name: "L".into() },
                nop_op(),
                RiscVOp::Label { name: "L".into() },
                RiscVOp::Jal {
                    rd: Reg::ZERO,
                    label: "L".into(),
                },
            ],
        };
        match builder.build(&[f]) {
            Err(ElfBuildError::DuplicateLabel(name, first, second)) => {
                assert_eq!(name, "L");
                assert_eq!((first, second), (0, 4));
            }
            other => panic!("duplicate label must hard-error, got {other:?}"),
        }
    }

    /// #882: the same label name in TWO DIFFERENT functions is fine — label
    /// resolution is per-function (the map is rebuilt for each function), so
    /// a reference can never bind across function boundaries.
    #[test]
    fn same_label_name_across_functions_ok_882() {
        let builder = RiscVElfBuilder::new_relocatable();
        let mk = |name: &str| RiscVElfFunction {
            name: name.into(),
            ops: vec![
                RiscVOp::Label { name: "L".into() },
                nop_op(),
                RiscVOp::Jal {
                    rd: Reg::ZERO,
                    label: "L".into(),
                },
            ],
        };
        assert!(builder.build(&[mk("f"), mk("g")]).is_ok());
    }

    /// #798: `build` (no data) and `build_with_data(&[], …)` are BYTE-identical
    /// — the `.wasm_data` section, its shstrtab name, and the index shift only
    /// exist when there are records to ship. Frozen data-free objects are
    /// untouched by construction.
    #[test]
    fn empty_wasm_data_is_byte_identical_798() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "f".into(),
            ops: vec![
                nop_op(),
                RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::RA,
                    imm: 0,
                },
            ],
        };
        let plain = builder.build(std::slice::from_ref(&f)).unwrap();
        let with_empty = builder.build_with_data(&[f], &[]).unwrap();
        assert_eq!(plain, with_empty, "empty wasm_data must not perturb bytes");
        assert!(!plain.windows(10).any(|w| w == b".wasm_data"));
    }

    /// #798: a non-empty record blob ships as a `.wasm_data` PROGBITS section
    /// (SHF_ALLOC, 4-aligned) holding the blob verbatim, `.text` unchanged,
    /// and the trailing string/symbol sections still resolve (shstrndx shift).
    #[test]
    fn wasm_data_section_ships_records_verbatim_798() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "f".into(),
            ops: vec![
                nop_op(),
                RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::RA,
                    imm: 0,
                },
            ],
        };
        let records = synth_core::static_data_addr::pack_segment_records(&[
            synth_core::static_data_addr::DataSegment {
                linmem_off: 16,
                bytes: vec![1, 2, 3, 4],
            },
            synth_core::static_data_addr::DataSegment {
                linmem_off: 0x10000,
                bytes: vec![0xAA, 0xBB, 0xCC],
            },
        ]);
        let plain = builder.build(std::slice::from_ref(&f)).unwrap();
        let elf = builder.build_with_data(&[f], &records).unwrap();

        // Walk the section headers by hand (mirrors what a linker does).
        let shoff = u32::from_le_bytes(elf[32..36].try_into().unwrap()) as usize;
        let shnum = u16::from_le_bytes(elf[48..50].try_into().unwrap()) as usize;
        let shstrndx = u16::from_le_bytes(elf[50..52].try_into().unwrap()) as usize;
        assert_eq!(shnum, 6, "null/.text/.wasm_data/.symtab/.strtab/.shstrtab");
        assert_eq!(shstrndx, 5);
        let shdr = |i: usize| &elf[shoff + i * 40..shoff + (i + 1) * 40];
        let field =
            |h: &[u8], o: usize| u32::from_le_bytes(h[o..o + 4].try_into().unwrap()) as usize;
        let shstr = shdr(shstrndx);
        let (stroff, strsz) = (field(shstr, 16), field(shstr, 20));
        let names = &elf[stroff..stroff + strsz];
        let name_of = |h: &[u8]| {
            let n = field(h, 0);
            let end = names[n..].iter().position(|&b| b == 0).unwrap() + n;
            std::str::from_utf8(&names[n..end]).unwrap().to_string()
        };
        let wd = shdr(2);
        assert_eq!(name_of(wd), ".wasm_data");
        assert_eq!(field(wd, 4), 1, "SHT_PROGBITS");
        assert_eq!(field(wd, 8), 0x2, "SHF_ALLOC only");
        assert_eq!(field(wd, 32), 4, "sh_addralign");
        let (off, sz) = (field(wd, 16), field(wd, 20));
        assert_eq!(&elf[off..off + sz], &records[..], "records verbatim");
        assert_eq!(off % 4, 0, "records 4-aligned in the file");
        // .text bytes identical to the data-free build.
        let text = shdr(1);
        let plain_shoff = u32::from_le_bytes(plain[32..36].try_into().unwrap()) as usize;
        let plain_text = &plain[plain_shoff + 40..plain_shoff + 80];
        assert_eq!(
            &elf[field(text, 16)..field(text, 16) + field(text, 20)],
            &plain[field(plain_text, 16)..field(plain_text, 16) + field(plain_text, 20)],
            ".text must be unchanged by shipping data"
        );
        // symtab still links to the (shifted) strtab: symbol 1 is "f".
        let symtab = shdr(3);
        assert_eq!(name_of(symtab), ".symtab");
        assert_eq!(field(symtab, 24), 4, "sh_link -> .strtab at index 4");
    }

    /// #871: an external `Call` assembles to the canonical 8-byte
    /// `auipc ra, 0 ; jalr ra, 0(ra)` placeholder plus a function-relative
    /// `R_RISCV_CALL_PLT` reloc record — no more "external call without
    /// relocation table" error.
    #[test]
    fn external_call_emits_placeholder_and_reloc_871() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "caller".into(),
            ops: vec![
                nop_op(),
                RiscVOp::Call {
                    label: "mmio_read32".into(),
                },
                RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::RA,
                    imm: 0,
                },
            ],
        };
        let (bytes, relocs) = builder.assemble_single_function(&f).unwrap();
        assert_eq!(bytes.len(), 16, "nop + 8B call pair + ret");
        assert_eq!(&bytes[4..12], &CALL_PLACEHOLDER_BYTES);
        assert_eq!(
            relocs,
            vec![RiscVCallReloc {
                offset: 4,
                symbol: "mmio_read32".into(),
                kind: RiscVRelocKind::CallPlt,
            }]
        );
    }

    /// #871: `build_object` emits `.rela.text` (SHT_RELA, entsize 12, type 19
    /// entries) and an UNDEFINED global symbol per unresolved reloc target,
    /// while a defined function name resolves to its own symtab index. Walk
    /// the section headers by hand, like a linker would.
    #[test]
    fn build_object_emits_rela_text_and_undefined_symbols_871() {
        let builder = RiscVElfBuilder::new_relocatable();
        let callee = RiscVElfFunction {
            name: "callee".into(),
            ops: vec![
                nop_op(),
                RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::RA,
                    imm: 0,
                },
            ],
        };
        let caller = RiscVElfFunction {
            name: "caller".into(),
            ops: vec![
                RiscVOp::Call {
                    label: "mmio_read32".into(),
                },
                RiscVOp::Call {
                    label: "callee".into(),
                },
                RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::RA,
                    imm: 0,
                },
            ],
        };
        let elf = builder.build_object(&[callee, caller], &[], &[]).unwrap();

        let shoff = u32::from_le_bytes(elf[32..36].try_into().unwrap()) as usize;
        let shnum = u16::from_le_bytes(elf[48..50].try_into().unwrap()) as usize;
        assert_eq!(shnum, 6, "null/.text/.symtab/.strtab/.shstrtab/.rela.text");
        let shdr = |i: usize| &elf[shoff + i * 40..shoff + (i + 1) * 40];
        let field =
            |h: &[u8], o: usize| u32::from_le_bytes(h[o..o + 4].try_into().unwrap()) as usize;
        // The last section is .rela.text.
        let rela = shdr(5);
        assert_eq!(field(rela, 4), 4, "SHT_RELA");
        assert_eq!(field(rela, 24), 2, "sh_link -> .symtab");
        assert_eq!(field(rela, 28), 1, "sh_info -> .text");
        assert_eq!(field(rela, 36), 12, "sh_entsize");
        let (roff, rsz) = (field(rela, 16), field(rela, 20));
        assert_eq!(rsz, 24, "two RELA entries");
        // Entry 0: the import call at caller+0 (callee is 8 bytes, caller
        // starts at 8) → r_offset 8, type 19.
        let e0 = &elf[roff..roff + 12];
        let r_offset0 = u32::from_le_bytes(e0[0..4].try_into().unwrap());
        let r_info0 = u32::from_le_bytes(e0[4..8].try_into().unwrap());
        assert_eq!(r_offset0, 8);
        assert_eq!(r_info0 & 0xFF, R_RISCV_CALL_PLT);
        let import_sym = (r_info0 >> 8) as usize;
        // Entry 1: the local call to `callee` resolves to symbol index 1.
        let e1 = &elf[roff + 12..roff + 24];
        let r_offset1 = u32::from_le_bytes(e1[0..4].try_into().unwrap());
        let r_info1 = u32::from_le_bytes(e1[4..8].try_into().unwrap());
        assert_eq!(r_offset1, 16);
        assert_eq!(r_info1 & 0xFF, R_RISCV_CALL_PLT);
        assert_eq!((r_info1 >> 8) as usize, 1, "callee = first symtab entry");
        // The import symbol is UNDEFINED (st_shndx 0) and named mmio_read32.
        let symtab = shdr(2);
        let (soff, _ssz) = (field(symtab, 16), field(symtab, 20));
        let sym = &elf[soff + import_sym * 16..soff + import_sym * 16 + 16];
        let st_shndx = u16::from_le_bytes(sym[14..16].try_into().unwrap());
        assert_eq!(st_shndx, 0, "SHN_UNDEF");
        let strtab = shdr(3);
        let stroff = field(strtab, 16);
        let name_off = stroff + u32::from_le_bytes(sym[0..4].try_into().unwrap()) as usize;
        let end = elf[name_off..].iter().position(|&b| b == 0).unwrap() + name_off;
        assert_eq!(&elf[name_off..end], b"mmio_read32");
        // Placeholder bytes sit at both reloc sites in .text.
        let text = shdr(1);
        let toff = field(text, 16);
        assert_eq!(&elf[toff + 8..toff + 16], &CALL_PLACEHOLDER_BYTES);
        assert_eq!(&elf[toff + 16..toff + 24], &CALL_PLACEHOLDER_BYTES);
    }

    /// #871: an object with NO call relocations is byte-identical to the
    /// pre-#871 layout — no `.rela.text`, no undefined symbols, no shstrtab
    /// entry. (The frozen RV32 fixtures rely on this.)
    #[test]
    fn reloc_free_object_layout_unchanged_871() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "f".into(),
            ops: vec![
                nop_op(),
                RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::RA,
                    imm: 0,
                },
            ],
        };
        let elf = builder.build(std::slice::from_ref(&f)).unwrap();
        let shnum = u16::from_le_bytes(elf[48..50].try_into().unwrap());
        assert_eq!(shnum, 5, "no .rela.text section");
        assert!(!elf.windows(10).any(|w| w == b".rela.text"));
    }

    /// RQ-63-RVGLOBAL: a NON-EMPTY globals image ships as `.data` (PROGBITS,
    /// WA, 4-aligned) with a GLOBAL `STT_OBJECT` `__synth_globals` spanning
    /// it, and an `La` pair relocates against that symbol with an
    /// `R_RISCV_HI20` at +0 and an `R_RISCV_LO12_I` at +4 over the
    /// `lui rd, 0 ; addi rd, rd, 0` placeholder. Walked by hand, like a
    /// linker would (the #871 test's shape).
    #[test]
    fn globals_image_ships_as_data_with_object_symbol_and_relocs_1163() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "get".into(),
            ops: vec![
                RiscVOp::La {
                    rd: Reg::T0,
                    symbol: crate::globals::GLOBALS_SYMBOL.into(),
                },
                RiscVOp::Lw {
                    rd: Reg::A0,
                    rs1: Reg::T0,
                    imm: 4,
                },
                RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::RA,
                    imm: 0,
                },
            ],
        };
        let image = [7u8, 0, 0, 0, 0xC0, 0x1D, 0xFE, 0xFF];
        let elf = builder
            .build_object_with_globals(&[f], &[], &image, &[])
            .unwrap();

        let shoff = u32::from_le_bytes(elf[32..36].try_into().unwrap()) as usize;
        let shnum = u16::from_le_bytes(elf[48..50].try_into().unwrap()) as usize;
        let shstrndx = u16::from_le_bytes(elf[50..52].try_into().unwrap()) as usize;
        assert_eq!(
            shnum, 7,
            "null/.text/.data/.symtab/.strtab/.shstrtab/.rela.text"
        );
        assert_eq!(shstrndx, 5, ".shstrtab shifted by the .data section");
        let shdr = |i: usize| &elf[shoff + i * 40..shoff + (i + 1) * 40];
        let field =
            |h: &[u8], o: usize| u32::from_le_bytes(h[o..o + 4].try_into().unwrap()) as usize;
        let shstr_off = field(shdr(shstrndx), 16);
        let sec_name = |h: &[u8]| {
            let n = shstr_off + field(h, 0);
            let e = elf[n..].iter().position(|&b| b == 0).unwrap() + n;
            &elf[n..e]
        };
        // [2] .data — PROGBITS, SHF_WRITE | SHF_ALLOC, the image verbatim.
        let data = shdr(2);
        assert_eq!(sec_name(data), b".data");
        assert_eq!(field(data, 4), 1, "SHT_PROGBITS");
        assert_eq!(field(data, 8), 0x3, "SHF_WRITE | SHF_ALLOC");
        assert_eq!(field(data, 20), image.len(), "sh_size = image");
        assert_eq!(field(data, 32), 4, "word alignment");
        let doff = field(data, 16);
        assert_eq!(&elf[doff..doff + image.len()], &image);
        // .symtab [3]: [1] get (FUNC, .text), [2] __synth_globals (OBJECT, .data, size 8).
        let symtab = shdr(3);
        assert_eq!(sec_name(symtab), b".symtab");
        assert_eq!(field(symtab, 24), 4, "sh_link -> .strtab");
        let soff = field(symtab, 16);
        let sym = &elf[soff + 2 * 16..soff + 3 * 16];
        assert_eq!(sym[12], (1 << 4) | 1, "STB_GLOBAL | STT_OBJECT");
        assert_eq!(
            u16::from_le_bytes(sym[14..16].try_into().unwrap()),
            2,
            "st_shndx = .data"
        );
        assert_eq!(
            u32::from_le_bytes(sym[8..12].try_into().unwrap()),
            8,
            "st_size = image"
        );
        assert_eq!(
            u32::from_le_bytes(sym[4..8].try_into().unwrap()),
            0,
            "st_value = 0"
        );
        let stroff = field(shdr(4), 16);
        let name_off = stroff + u32::from_le_bytes(sym[0..4].try_into().unwrap()) as usize;
        let end = elf[name_off..].iter().position(|&b| b == 0).unwrap() + name_off;
        assert_eq!(
            &elf[name_off..end],
            crate::globals::GLOBALS_SYMBOL.as_bytes()
        );
        // .rela.text [6]: HI20 @0 and LO12_I @4, both against symbol 2.
        let rela = shdr(6);
        assert_eq!(sec_name(rela), b".rela.text");
        assert_eq!(field(rela, 4), 4, "SHT_RELA");
        assert_eq!(field(rela, 24), 3, "sh_link -> .symtab");
        assert_eq!(field(rela, 28), 1, "sh_info -> .text");
        let (roff, rsz) = (field(rela, 16), field(rela, 20));
        assert_eq!(rsz, 24, "two RELA entries");
        let entry = |i: usize| {
            let e = &elf[roff + i * 12..roff + (i + 1) * 12];
            (
                u32::from_le_bytes(e[0..4].try_into().unwrap()),
                u32::from_le_bytes(e[4..8].try_into().unwrap()),
                i32::from_le_bytes(e[8..12].try_into().unwrap()),
            )
        };
        assert_eq!(entry(0), (0, (2 << 8) | R_RISCV_HI20, 0));
        assert_eq!(entry(1), (4, (2 << 8) | R_RISCV_LO12_I, 0));
        // .text: `lui t0, 0` ; `addi t0, t0, 0` ; `lw a0, 4(t0)` ; `ret`.
        let toff = field(shdr(1), 16);
        let word =
            |i: usize| u32::from_le_bytes(elf[toff + i * 4..toff + i * 4 + 4].try_into().unwrap());
        assert_eq!(word(0), 0x0000_02B7, "lui t0, 0");
        assert_eq!(word(1), 0x0002_8293, "addi t0, t0, 0");
        assert_eq!(word(2), 0x0042_A503, "lw a0, 4(t0)");
        assert_eq!(field(shdr(1), 20), 16, ".text = 4 words");
    }

    /// RQ-63-RVGLOBAL: an EMPTY image is exactly `build_object` — no `.data`,
    /// no `__synth_globals`, no shstrtab entry. (The frozen RV32 fixtures rely
    /// on this: a module that touches no global is byte-identical.)
    #[test]
    fn empty_globals_image_is_byte_identical_1163() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "f".into(),
            ops: vec![
                nop_op(),
                RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::RA,
                    imm: 0,
                },
            ],
        };
        let plain = builder
            .build_object(std::slice::from_ref(&f), &[], &[])
            .unwrap();
        let with_empty = builder
            .build_object_with_globals(std::slice::from_ref(&f), &[], &[], &[])
            .unwrap();
        assert_eq!(
            plain, with_empty,
            "empty globals image must not perturb bytes"
        );
        assert!(!plain.windows(5).any(|w| w == b".data"));
        assert!(!plain.windows(15).any(|w| w == b"__synth_globals"));
    }

    /// RQ-63-RVGLOBAL: code relocating against `__synth_globals` with NO
    /// image is REFUSED — never emitted as an undefined symbol for the linker
    /// to trip over (the #1102 dangling-reference class).
    #[test]
    fn dangling_globals_reloc_is_refused_1163() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "get".into(),
            ops: vec![
                RiscVOp::La {
                    rd: Reg::T0,
                    symbol: crate::globals::GLOBALS_SYMBOL.into(),
                },
                RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::RA,
                    imm: 0,
                },
            ],
        };
        let err = builder.build_object(&[f], &[], &[]).unwrap_err();
        assert!(
            matches!(err, ElfBuildError::DanglingGlobalsReloc(ref s) if s == crate::globals::GLOBALS_SYMBOL),
            "expected DanglingGlobalsReloc, got {err:?}"
        );
    }

    #[test]
    fn executable_mode_writes_text_base_in_symbols() {
        let builder = RiscVElfBuilder::new_executable(0x80000000, 0x80000000);
        let f = RiscVElfFunction {
            name: "main".into(),
            ops: vec![
                nop_op(),
                RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::RA,
                    imm: 0,
                },
            ],
        };
        let elf = builder.build(&[f]).unwrap();
        assert_eq!(u16::from_le_bytes([elf[16], elf[17]]), 2, "ET_EXEC");
        assert_eq!(
            u32::from_le_bytes([elf[24], elf[25], elf[26], elf[27]]),
            0x80000000,
            "e_entry"
        );
    }
}
