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

    #[error("function `{0}` is empty")]
    EmptyFunction(String),

    #[error("unsupported in skeleton: {0}")]
    Unsupported(&'static str),
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
}

/// `R_RISCV_CALL_PLT` — the modern auipc+jalr call-pair relocation type
/// (`R_RISCV_CALL` = 18 is deprecated by the psABI).
pub const R_RISCV_CALL_PLT: u32 = 19;

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
        let encoder = RiscVEncoder::new_rv32();

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
            }));
        }
        call_relocs.extend_from_slice(extra_call_relocs);

        // #871: resolve relocation symbols. Defined function names win;
        // anything else becomes an UNDEFINED global symbol (dedup'd, in
        // first-use order so output is deterministic).
        let mut undefined: Vec<String> = Vec::new();
        for r in &call_relocs {
            if !symbols.iter().any(|(n, _, _)| n == &r.symbol)
                && !undefined.iter().any(|u| u == &r.symbol)
            {
                undefined.push(r.symbol.clone());
            }
        }
        let sym_index_of = |name: &str| -> u32 {
            // symtab index: [0] null, [1..] functions, then undefined.
            if let Some(i) = symbols.iter().position(|(n, _, _)| n == name) {
                (i + 1) as u32
            } else {
                let u = undefined
                    .iter()
                    .position(|u| u == name)
                    .expect("every reloc symbol is defined or collected as undefined");
                (symbols.len() + 1 + u) as u32
            }
        };
        let has_relocs = !call_relocs.is_empty();

        // 2. Section ordering (— entries marked § exist only when `wasm_data`
        //    is non-empty; without it the layout is bit-identical to pre-#798):
        //    [0]  null
        //    [1]  .text (PROGBITS, AX)
        //    [2]§ .wasm_data (PROGBITS, A) — packed segment records
        //    [·]  .symtab (SYMTAB)
        //    [·]  .strtab (STRTAB) — symbol names
        //    [·]  .shstrtab (STRTAB) — section names
        let has_wasm_data = !wasm_data.is_empty();
        let mut elf = Vec::new();
        let ehsize = 52usize;
        let shentsize = 40usize;
        let phentsize = 32usize;

        elf.resize(ehsize, 0);

        // .text
        let text_offset = elf.len();
        elf.extend_from_slice(&text);

        // Pad to 4-byte alignment for what follows (.wasm_data / .symtab).
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

        // .strtab — built first so we know offsets for .symtab.
        let mut strtab = vec![0u8]; // ELF requires a leading NUL.
        let mut name_offsets: Vec<u32> = Vec::with_capacity(symbols.len());
        for (name, _, _) in &symbols {
            name_offsets.push(strtab.len() as u32);
            strtab.extend_from_slice(name.as_bytes());
            strtab.push(0);
        }
        // #871: undefined external symbol names follow the function names.
        let mut undef_name_offsets: Vec<u32> = Vec::with_capacity(undefined.len());
        for name in &undefined {
            undef_name_offsets.push(strtab.len() as u32);
            strtab.extend_from_slice(name.as_bytes());
            strtab.push(0);
        }

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
        // #871: undefined externals — STB_GLOBAL / STT_NOTYPE / SHN_UNDEF
        // (`nm` shows them as `U <name>`, exactly like the ARM object).
        for off in &undef_name_offsets {
            let mut entry = [0u8; 16];
            entry[0..4].copy_from_slice(&off.to_le_bytes());
            entry[12] = 1u8 << 4; // STB_GLOBAL << 4 | STT_NOTYPE
            // st_value/st_size stay 0, st_shndx stays 0 (SHN_UNDEF).
            elf.extend_from_slice(&entry);
        }
        let symtab_size = (symbols.len() + undefined.len() + 1) * 16;

        // .strtab
        let strtab_offset = elf.len();
        elf.extend_from_slice(&strtab);

        // .shstrtab — fixed contents
        let shstrtab_offset = elf.len();
        let shstrtab_data = build_shstrtab(has_wasm_data, has_relocs);
        elf.extend_from_slice(&shstrtab_data.bytes);

        // #871: .rela.text — placed after .shstrtab, 4-aligned. ELF32 RELA
        // entries are 12 bytes: r_offset, r_info = (sym << 8) | type,
        // r_addend (always 0 — the call target is the symbol itself).
        let mut rela_offset = 0usize;
        if has_relocs {
            while elf.len() % 4 != 0 {
                elf.push(0);
            }
            rela_offset = elf.len();
            for r in &call_relocs {
                let r_info = (sym_index_of(&r.symbol) << 8) | R_RISCV_CALL_PLT;
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
        // .wasm_data (when present) sits between .text and .symtab, shifting
        // the string/symbol-table indices up by one.
        let wasm_data_shift = if has_wasm_data { 1u32 } else { 0 };
        let symtab_link = 3u32 + wasm_data_shift; // index of .strtab
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
        shdrs.extend([
            // [2/3] .symtab
            ShEntry {
                sh_name: shstrtab_data.symtab_off,
                sh_type: 2, // SHT_SYMTAB
                sh_flags: 0,
                sh_addr: 0,
                sh_offset: symtab_offset as u32,
                sh_size: symtab_size as u32,
                sh_link: symtab_link,
                sh_info: 1, // index of first global symbol
                sh_addralign: 4,
                sh_entsize: 16,
            },
            // [3/4] .strtab
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
            // [4/5] .shstrtab
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
                sh_link: 2 + wasm_data_shift, // .symtab
                sh_info: 1,                   // relocates .text
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
            (4 + wasm_data_shift) as u16, // shstrtab index
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
                    labels.insert(name.clone(), cursor);
                }
                RiscVOp::Call { .. } => cursor += 8, // auipc + jalr pair
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
                        });
                        bytes.extend_from_slice(&CALL_PLACEHOLDER_BYTES);
                    }
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
    symtab_off: u32,
    strtab_off: u32,
    shstrtab_off: u32,
    rela_text_off: u32,
}

fn build_shstrtab(with_wasm_data: bool, with_relocs: bool) -> ShstrtabData {
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
                symbol: "mmio_read32".into()
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
