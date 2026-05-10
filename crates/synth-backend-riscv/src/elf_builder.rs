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
//! - Emit a `.rela.text` section when `RiscVOp::Call` targets a non-local
//!   symbol — the placeholder `auipc t1, 0; jalr ra, 0(t1)` pair is left
//!   in `.text` and the linker patches it via `R_RISCV_CALL_PLT`.
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

/// RISC-V relocation types we know how to emit.
///
/// Only the small subset needed for cross-function calls is wired up so far.
/// The numeric values match the psABI assignments in `elf.h`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum RiscVRelocationType {
    /// `R_RISCV_CALL_PLT (19)` — `auipc + jalr` pair, optionally via the PLT.
    /// The linker fixes up both the high-20 (auipc imm) and the low-12 (jalr
    /// imm) so the pair jumps to `S + A` relative to the auipc's PC.
    /// This is what GAS emits for `call sym` and is the safe default for
    /// inter-function calls in a freestanding RV32 binary.
    CallPlt = 19,
}

/// A `.rela.text` entry — RELA format (with explicit addend).
///
/// RISC-V uses RELA (not REL) per the psABI. Each entry occupies 12 bytes
/// in ELF32: `r_offset` (4), `r_info` (4), `r_addend` (4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RiscVRelocation {
    /// Byte offset inside `.text` where the placeholder instruction pair lives.
    pub offset: u32,
    /// Name of the external symbol being called.
    pub symbol: String,
    /// Relocation kind (only `CallPlt` for now).
    pub kind: RiscVRelocationType,
    /// Explicit RELA addend. For `R_RISCV_CALL_PLT` this is 0.
    pub addend: i32,
}

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

/// Per-function relocation as seen by `build_precompiled` — the offset is
/// **relative to the start of the function's code**, not absolute inside
/// `.text`. The ELF builder rebases it when emitting `.rela.text`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrecompiledRelocation {
    pub offset: u32,
    pub symbol: String,
}

/// A function whose machine code has already been emitted (e.g. by an
/// earlier call to `Backend::compile_function`). Used by callers that
/// need to combine multiple `CompiledFunction`s into a single object
/// without re-running the selector.
#[derive(Debug, Clone)]
pub struct PrecompiledFunction {
    pub name: String,
    pub code: Vec<u8>,
    pub relocations: Vec<PrecompiledRelocation>,
}

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

    /// Build the full ELF blob. Functions are concatenated in order; cross-
    /// function `Call` ops are resolved either against the local label table
    /// (when the target is in the same function) or via a `R_RISCV_CALL_PLT`
    /// relocation in `.rela.text` (when the target is another function or an
    /// undefined extern symbol).
    pub fn build(&self, functions: &[RiscVElfFunction]) -> Result<Vec<u8>, ElfBuildError> {
        let encoder = RiscVEncoder::new_rv32();

        // 1. Resolve labels per-function, accumulate code bytes & symbols.
        //    A two-phase scheme: first we collect every function's start
        //    offset so cross-function `Call` ops can patch to a local
        //    symbol; ops that target an unknown name become relocations.
        let mut text: Vec<u8> = Vec::new();
        let mut symbols: Vec<(String, u32, u32)> = Vec::new(); // (name, st_value, st_size)
        let mut relocations: Vec<RiscVRelocation> = Vec::new();

        // Pre-pass: compute every function's start offset so cross-function
        // calls can resolve to a sibling's known position without a
        // relocation when both are defined in this module.
        let mut function_offsets: HashMap<String, u32> = HashMap::new();
        {
            let mut cursor: u32 = 0;
            for f in functions {
                function_offsets.insert(f.name.clone(), cursor);
                cursor += function_byte_size(&f.ops);
            }
        }

        for f in functions {
            if f.ops.is_empty() {
                return Err(ElfBuildError::EmptyFunction(f.name.clone()));
            }
            let function_offset = text.len() as u32;
            let (bytes, mut func_relocs) = self.assemble_function(
                &encoder,
                f,
                function_offset,
                &function_offsets,
            )?;
            let function_size = bytes.len() as u32;
            text.extend_from_slice(&bytes);
            relocations.append(&mut func_relocs);
            symbols.push((f.name.clone(), function_offset, function_size));
        }

        self.emit_elf(text, symbols, relocations)
    }

    /// Like `build`, but takes pre-encoded function bytes and relocations
    /// instead of `RiscVOp` sequences. Used by the CLI when it has already
    /// gone through `Backend::compile_function` and only needs to stitch
    /// the per-function blobs together.
    ///
    /// `aliases` is a list of `(alias_name, target_function_name)` pairs —
    /// extra symbol entries that point at the same offset/size as the
    /// named target. The CLI uses this to emit `synth_func_<idx>` aliases
    /// alongside the public export name (e.g. `add`), so a relocation
    /// generated by the selector against `synth_func_1` can be resolved
    /// against the `fib` export.
    pub fn build_precompiled(
        &self,
        functions: &[PrecompiledFunction],
        aliases: &[(String, String)],
    ) -> Result<Vec<u8>, ElfBuildError> {
        let mut text: Vec<u8> = Vec::new();
        let mut symbols: Vec<(String, u32, u32)> = Vec::new();
        let mut relocations: Vec<RiscVRelocation> = Vec::new();
        // (intentionally `let mut symbols` — we extend it below with aliases.)

        for f in functions {
            if f.code.is_empty() {
                return Err(ElfBuildError::EmptyFunction(f.name.clone()));
            }
            // 4-byte align each function (RISC-V instructions are 32-bit).
            while text.len() % 4 != 0 {
                text.push(0);
            }
            let function_offset = text.len() as u32;
            for r in &f.relocations {
                relocations.push(RiscVRelocation {
                    offset: function_offset + r.offset,
                    symbol: r.symbol.clone(),
                    kind: RiscVRelocationType::CallPlt,
                    addend: 0,
                });
            }
            text.extend_from_slice(&f.code);
            symbols.push((f.name.clone(), function_offset, f.code.len() as u32));
        }

        // Resolve aliases — each (alias, target) pair produces another
        // symbol entry pointing at the target's offset/size.
        let mut alias_symbols: Vec<(String, u32, u32)> = Vec::new();
        for (alias, target) in aliases {
            if let Some((_, value, size)) = symbols.iter().find(|(n, _, _)| n == target) {
                alias_symbols.push((alias.clone(), *value, *size));
            }
        }
        symbols.extend(alias_symbols);

        self.emit_elf(text, symbols, relocations)
    }

    /// Pack pre-collected text/symbols/relocations into a complete ELF.
    /// Shared between `build` (which derives them from `RiscVOp` sequences)
    /// and `build_precompiled` (which receives them directly).
    fn emit_elf(
        &self,
        text: Vec<u8>,
        symbols: Vec<(String, u32, u32)>,
        relocations: Vec<RiscVRelocation>,
    ) -> Result<Vec<u8>, ElfBuildError> {
        // Collect undefined-extern symbol names referenced by relocations
        // but not satisfied by any function defined in this module. Each
        // becomes a section-0 (SHN_UNDEF) entry in the symbol table.
        let defined: std::collections::HashSet<&str> =
            symbols.iter().map(|(n, _, _)| n.as_str()).collect();
        let mut undefined_names: Vec<String> = Vec::new();
        {
            let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
            for r in &relocations {
                if !defined.contains(r.symbol.as_str()) && seen.insert(r.symbol.clone()) {
                    undefined_names.push(r.symbol.clone());
                }
            }
        }

        // 2. Section ordering:
        //    [0]  null
        //    [1]  .text (PROGBITS, AX)
        //    [2]  .symtab (SYMTAB)
        //    [3]  .strtab (STRTAB) — symbol names
        //    [4]  .shstrtab (STRTAB) — section names
        //    [5]  .rela.text (RELA, optional — only present if any relocs)
        let mut elf = Vec::new();
        let ehsize = 52usize;
        let shentsize = 40usize;
        let phentsize = 32usize;
        let has_relocs = !relocations.is_empty();

        elf.resize(ehsize, 0);

        // .text
        let text_offset = elf.len();
        elf.extend_from_slice(&text);

        // Pad to 4-byte alignment for the symbol table.
        while elf.len() % 4 != 0 {
            elf.push(0);
        }

        // .strtab — built first so we know offsets for .symtab.
        let mut strtab = vec![0u8]; // ELF requires a leading NUL.
        let mut name_offsets: Vec<u32> = Vec::with_capacity(symbols.len());
        for (name, _, _) in &symbols {
            name_offsets.push(strtab.len() as u32);
            strtab.extend_from_slice(name.as_bytes());
            strtab.push(0);
        }
        let mut undef_name_offsets: Vec<u32> = Vec::with_capacity(undefined_names.len());
        for name in &undefined_names {
            undef_name_offsets.push(strtab.len() as u32);
            strtab.extend_from_slice(name.as_bytes());
            strtab.push(0);
        }

        // .symtab — entry 0 is reserved (all zero).
        // Layout: [null][defined func globals...][undefined extern globals...]
        // sh_info = 1 because every non-null entry is STB_GLOBAL (we have no
        // locals).
        let symtab_offset = elf.len();
        elf.extend_from_slice(&[0u8; 16]); // null symbol
        // Defined functions (STT_FUNC, STB_GLOBAL, st_shndx = .text = 1)
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
        // Undefined externs (STT_NOTYPE, STB_GLOBAL, st_shndx = SHN_UNDEF = 0)
        let first_undef_sym_index = 1 + symbols.len() as u32;
        for (i, _name) in undefined_names.iter().enumerate() {
            let st_name = undef_name_offsets[i];
            let st_info = 1u8 << 4; // STB_GLOBAL << 4 | STT_NOTYPE
            let mut entry = [0u8; 16];
            entry[0..4].copy_from_slice(&st_name.to_le_bytes());
            // st_value = 0, st_size = 0, st_shndx = 0
            entry[12] = st_info;
            elf.extend_from_slice(&entry);
        }
        let total_syms = 1 + symbols.len() + undefined_names.len();
        let symtab_size = total_syms * 16;

        // Map each relocation's symbol name to its index in .symtab.
        // Defined symbols occupy indices [1 .. 1 + symbols.len()];
        // undefined ones follow.
        let mut sym_index_by_name: HashMap<String, u32> = HashMap::new();
        for (i, (name, _, _)) in symbols.iter().enumerate() {
            sym_index_by_name.insert(name.clone(), 1 + i as u32);
        }
        for (i, name) in undefined_names.iter().enumerate() {
            sym_index_by_name.insert(name.clone(), first_undef_sym_index + i as u32);
        }

        // .strtab
        let strtab_offset = elf.len();
        elf.extend_from_slice(&strtab);

        // .shstrtab — varies depending on whether .rela.text is present.
        let shstrtab_offset = elf.len();
        let shstrtab_data = build_shstrtab(has_relocs);
        elf.extend_from_slice(&shstrtab_data.bytes);

        // Pad to 4-byte for the relocation table / section header table.
        while elf.len() % 4 != 0 {
            elf.push(0);
        }

        // .rela.text — RELA entries (12 bytes each on ELF32).
        let rela_offset = elf.len();
        if has_relocs {
            for r in &relocations {
                let sym_idx = sym_index_by_name
                    .get(&r.symbol)
                    .copied()
                    .expect("relocation references a symbol not in the table");
                let r_info: u32 = (sym_idx << 8) | (r.kind as u32 & 0xFF);
                elf.extend_from_slice(&r.offset.to_le_bytes());
                elf.extend_from_slice(&r_info.to_le_bytes());
                elf.extend_from_slice(&r.addend.to_le_bytes());
            }
            while elf.len() % 4 != 0 {
                elf.push(0);
            }
        }
        let rela_size = (relocations.len() * 12) as u32;

        let shoff = elf.len();

        // Section headers
        let text_size = text.len() as u32;
        let symtab_link = 3u32; // index of .strtab
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
            // [2] .symtab
            ShEntry {
                sh_name: shstrtab_data.symtab_off,
                sh_type: 2, // SHT_SYMTAB
                sh_flags: 0,
                sh_addr: 0,
                sh_offset: symtab_offset as u32,
                sh_size: symtab_size as u32,
                sh_link: symtab_link,
                sh_info: 1, // index of first global (we have no locals)
                sh_addralign: 4,
                sh_entsize: 16,
            },
            // [3] .strtab
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
            // [4] .shstrtab
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
        ];

        if has_relocs {
            shdrs.push(ShEntry {
                sh_name: shstrtab_data.rela_text_off,
                sh_type: 4, // SHT_RELA
                sh_flags: 0,
                sh_addr: 0,
                sh_offset: rela_offset as u32,
                sh_size: rela_size,
                sh_link: 2,  // index of .symtab
                sh_info: 1,  // index of the section the relocations apply to (.text)
                sh_addralign: 4,
                sh_entsize: 12, // ELF32 RELA entry size
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
            4u16, // shstrtab index
        );

        Ok(elf)
    }

    fn assemble_function(
        &self,
        encoder: &RiscVEncoder,
        f: &RiscVElfFunction,
        function_offset: u32,
        function_offsets: &HashMap<String, u32>,
    ) -> Result<(Vec<u8>, Vec<RiscVRelocation>), ElfBuildError> {
        // Pass 1: compute byte offset of each label inside this function.
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

        // Pass 2: emit bytes, resolving Jal/Branch/Call with the offsets we
        // just collected. Cross-function `Call`s either patch in a direct
        // PC-relative pair (when the target sits in the same module) or
        // become `R_RISCV_CALL_PLT` relocations to be fixed up by the linker.
        let mut bytes: Vec<u8> = Vec::with_capacity(cursor as usize);
        let mut relocations: Vec<RiscVRelocation> = Vec::new();
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
                    if let Some(&target_in_fn) = labels.get(label) {
                        // Intra-function call (rare — selectors typically emit
                        // these as Jal). Resolve to a concrete PC-relative pair.
                        let rel = target_in_fn as i32 - here;
                        emit_pcrel_call_pair(&mut bytes, encoder, rel)?;
                    } else if let Some(&sibling_offset) = function_offsets.get(label) {
                        // Cross-function call to another defined-here symbol.
                        // We could resolve this directly (sibling offset is
                        // known), but emitting a relocation matches GAS's
                        // behavior and keeps the ELF inspectable by `readelf`.
                        // The relocation's offset is the auipc PC inside .text.
                        let r_offset = function_offset + here as u32;
                        relocations.push(RiscVRelocation {
                            offset: r_offset,
                            symbol: label.clone(),
                            kind: RiscVRelocationType::CallPlt,
                            addend: 0,
                        });
                        // Still emit a sensible placeholder so the resulting
                        // ELF disassembles cleanly even before linking.
                        let rel = sibling_offset as i32 - r_offset as i32;
                        emit_pcrel_call_pair(&mut bytes, encoder, rel)?;
                    } else {
                        // Undefined external symbol — emit a placeholder pair
                        // with a `R_RISCV_CALL_PLT` relocation pointing at the
                        // auipc.
                        let r_offset = function_offset + here as u32;
                        relocations.push(RiscVRelocation {
                            offset: r_offset,
                            symbol: label.clone(),
                            kind: RiscVRelocationType::CallPlt,
                            addend: 0,
                        });
                        emit_placeholder_call_pair(&mut bytes, encoder)?;
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
        Ok((bytes, relocations))
    }
}

/// Predict the encoded size of a function's op list. Used by the pre-pass
/// in `build` so cross-function calls can compute sibling offsets.
fn function_byte_size(ops: &[RiscVOp]) -> u32 {
    let mut size: u32 = 0;
    for op in ops {
        match op {
            RiscVOp::Label { .. } => {}
            RiscVOp::Call { .. } => size += 8,
            _ => size += 4,
        }
    }
    size
}

/// Emit an `auipc t1, hi20; jalr ra, lo12(t1)` pair encoding a known PC-rel
/// target. The split between hi20 and lo12 uses the "+0x800 carry" trick
/// (lo12 is sign-extended by jalr).
fn emit_pcrel_call_pair(
    bytes: &mut Vec<u8>,
    encoder: &RiscVEncoder,
    rel: i32,
) -> Result<(), ElfBuildError> {
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
    Ok(())
}

/// Emit a placeholder `auipc t1, 0; jalr ra, 0(t1)` pair for an undefined
/// extern call. The linker patches both immediates via the accompanying
/// `R_RISCV_CALL_PLT` relocation.
fn emit_placeholder_call_pair(
    bytes: &mut Vec<u8>,
    encoder: &RiscVEncoder,
) -> Result<(), ElfBuildError> {
    let auipc = RiscVOp::Auipc {
        rd: Reg::T1,
        imm20: 0,
    };
    bytes.extend_from_slice(&encoder.encode(&auipc)?.to_le_bytes());
    let jalr = RiscVOp::Jalr {
        rd: Reg::RA,
        rs1: Reg::T1,
        imm: 0,
    };
    bytes.extend_from_slice(&encoder.encode(&jalr)?.to_le_bytes());
    Ok(())
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
    symtab_off: u32,
    strtab_off: u32,
    shstrtab_off: u32,
    /// Only meaningful when the caller asked for a `.rela.text` section
    /// (i.e. `include_rela = true`). Otherwise zero (never indexed).
    rela_text_off: u32,
}

fn build_shstrtab(include_rela: bool) -> ShstrtabData {
    let mut bytes = vec![0u8];
    let text_off = bytes.len() as u32;
    bytes.extend_from_slice(b".text\0");
    let symtab_off = bytes.len() as u32;
    bytes.extend_from_slice(b".symtab\0");
    let strtab_off = bytes.len() as u32;
    bytes.extend_from_slice(b".strtab\0");
    let shstrtab_off = bytes.len() as u32;
    bytes.extend_from_slice(b".shstrtab\0");
    let rela_text_off = if include_rela {
        let off = bytes.len() as u32;
        bytes.extend_from_slice(b".rela.text\0");
        off
    } else {
        0
    };
    ShstrtabData {
        bytes,
        text_off,
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

    fn ret_op() -> RiscVOp {
        RiscVOp::Jalr {
            rd: Reg::ZERO,
            rs1: Reg::RA,
            imm: 0,
        }
    }

    /// Verify that a `Call` between two defined functions in the same
    /// module emits a placeholder `auipc + jalr` pair *and* a `.rela.text`
    /// entry against the sibling symbol. The pair is positioned so the
    /// linker can patch it in place without needing to insert any extra
    /// bytes.
    #[test]
    fn cross_function_call_emits_relocation_and_placeholder() {
        let builder = RiscVElfBuilder::new_relocatable();
        // f1: just calls f2 and returns.
        let f1 = RiscVElfFunction {
            name: "synth_func_0".into(),
            ops: vec![
                RiscVOp::Call {
                    label: "synth_func_1".into(),
                },
                ret_op(),
            ],
        };
        let f2 = RiscVElfFunction {
            name: "synth_func_1".into(),
            ops: vec![nop_op(), ret_op()],
        };
        let elf = builder.build(&[f1, f2]).unwrap();

        // Section count: null + .text + .symtab + .strtab + .shstrtab + .rela.text = 6.
        let sh_num = u16::from_le_bytes([elf[48], elf[49]]);
        assert_eq!(sh_num, 6, "ELF should include .rela.text");

        // The shstrtab should contain ".rela.text".
        let has_rela = elf.windows(b".rela.text".len()).any(|w| w == b".rela.text");
        assert!(has_rela, "shstrtab should mention .rela.text");

        // .text starts at offset 52. The auipc/jalr placeholder pair lives
        // at bytes [52..60].
        let auipc_word = u32::from_le_bytes([elf[52], elf[53], elf[54], elf[55]]);
        let jalr_word = u32::from_le_bytes([elf[56], elf[57], elf[58], elf[59]]);
        // auipc opcode bits = 0b0010111 = 0x17
        assert_eq!(auipc_word & 0x7F, 0x17, "first inst should be auipc");
        // jalr opcode bits = 0b1100111 = 0x67
        assert_eq!(jalr_word & 0x7F, 0x67, "second inst should be jalr");
    }

    /// `Call` to an external (undefined) symbol must still produce a valid
    /// ELF — the symbol shows up in `.symtab` with `st_shndx = SHN_UNDEF`
    /// and a `.rela.text` entry references it.
    #[test]
    fn external_call_emits_undefined_symbol_and_relocation() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "synth_func_0".into(),
            ops: vec![
                RiscVOp::Call {
                    label: "__meld_dispatch_import".into(),
                },
                ret_op(),
            ],
        };
        let elf = builder.build(&[f]).unwrap();
        // The undefined symbol's name must appear in .strtab.
        assert!(
            elf.windows(b"__meld_dispatch_import".len())
                .any(|w| w == b"__meld_dispatch_import"),
            "ELF should contain the external symbol name"
        );
    }

    /// No `Call` ops anywhere ⇒ no `.rela.text` section. We preserve the
    /// original 5-section layout so existing tests and consumers don't
    /// notice extra sections.
    #[test]
    fn no_relocs_means_no_rela_text_section() {
        let builder = RiscVElfBuilder::new_relocatable();
        let f = RiscVElfFunction {
            name: "add".into(),
            ops: vec![
                RiscVOp::Add {
                    rd: Reg::A0,
                    rs1: Reg::A0,
                    rs2: Reg::A1,
                },
                ret_op(),
            ],
        };
        let elf = builder.build(&[f]).unwrap();
        let sh_num = u16::from_le_bytes([elf[48], elf[49]]);
        assert_eq!(sh_num, 5, "ELF without calls should not include .rela.text");
    }

    /// A two-function module where f1 calls f2: the relocation's
    /// `r_offset` should point at the auipc inside f1's section of .text.
    #[test]
    fn relocation_offset_points_at_call_site() {
        let builder = RiscVElfBuilder::new_relocatable();
        // f1: 2 instructions of padding before the call, then call f2, then ret.
        let f1 = RiscVElfFunction {
            name: "synth_func_0".into(),
            ops: vec![
                nop_op(),
                nop_op(),
                RiscVOp::Call {
                    label: "synth_func_1".into(),
                },
                ret_op(),
            ],
        };
        let f2 = RiscVElfFunction {
            name: "synth_func_1".into(),
            ops: vec![ret_op()],
        };
        let elf = builder.build(&[f1, f2]).unwrap();

        // The call is 2 instructions into f1, i.e. at byte offset 8.
        // Find the .rela.text section: its sh_offset tells us where the
        // first RELA entry lives. The first u32 of that entry is r_offset.
        let shoff = u32::from_le_bytes([elf[32], elf[33], elf[34], elf[35]]) as usize;
        let shentsize = 40usize;
        // .rela.text is the last section header.
        let sh_num = u16::from_le_bytes([elf[48], elf[49]]) as usize;
        let rela_shdr = shoff + (sh_num - 1) * shentsize;
        let rela_sh_offset = u32::from_le_bytes([
            elf[rela_shdr + 16],
            elf[rela_shdr + 17],
            elf[rela_shdr + 18],
            elf[rela_shdr + 19],
        ]) as usize;
        let r_offset = u32::from_le_bytes([
            elf[rela_sh_offset],
            elf[rela_sh_offset + 1],
            elf[rela_sh_offset + 2],
            elf[rela_sh_offset + 3],
        ]);
        assert_eq!(r_offset, 8, "relocation should point at the call site");
        // Verify the relocation type is R_RISCV_CALL_PLT (19).
        let r_info = u32::from_le_bytes([
            elf[rela_sh_offset + 4],
            elf[rela_sh_offset + 5],
            elf[rela_sh_offset + 6],
            elf[rela_sh_offset + 7],
        ]);
        assert_eq!(r_info & 0xFF, 19, "should be R_RISCV_CALL_PLT");
    }
}
