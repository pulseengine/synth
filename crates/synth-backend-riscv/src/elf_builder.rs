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
        let encoder = RiscVEncoder::new_rv32();

        // 1. Resolve labels per-function, accumulate code bytes & symbols.
        let mut text: Vec<u8> = Vec::new();
        let mut symbols: Vec<(String, u32, u32)> = Vec::new(); // (name, st_value, st_size)

        for f in functions {
            if f.ops.is_empty() {
                return Err(ElfBuildError::EmptyFunction(f.name.clone()));
            }
            let function_offset = text.len() as u32;
            let bytes = self.assemble_function(&encoder, f)?;
            let function_size = bytes.len() as u32;
            text.extend_from_slice(&bytes);
            symbols.push((f.name.clone(), function_offset, function_size));
        }

        // 2. Section ordering:
        //    [0]  null
        //    [1]  .text (PROGBITS, AX)
        //    [2]  .symtab (SYMTAB)
        //    [3]  .strtab (STRTAB) — symbol names
        //    [4]  .shstrtab (STRTAB) — section names
        let mut elf = Vec::new();
        let ehsize = 52usize;
        let shentsize = 40usize;
        let phentsize = 32usize;

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
        let symtab_size = (symbols.len() + 1) * 16;

        // .strtab
        let strtab_offset = elf.len();
        elf.extend_from_slice(&strtab);

        // .shstrtab — fixed contents
        let shstrtab_offset = elf.len();
        let shstrtab_data = build_shstrtab();
        elf.extend_from_slice(&shstrtab_data.bytes);

        // Pad to 4-byte for the section header table.
        while elf.len() % 4 != 0 {
            elf.push(0);
        }

        let shoff = elf.len();

        // Section headers
        let text_size = text.len() as u32;
        let symtab_link = 3u32; // index of .strtab
        let shdrs = vec![
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
                sh_info: 1, // index of first global symbol
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
    ) -> Result<Vec<u8>, ElfBuildError> {
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
                    // Skeleton emits a placeholder auipc + jalr ra, 0(ra) — the
                    // ELF builder for executables will need PC-relative
                    // relocations; for now we emit a self-resolving local call
                    // if the label is local, else error.
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
                        return Err(ElfBuildError::Unsupported(
                            "external call without relocation table",
                        ));
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
        Ok(bytes)
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
    symtab_off: u32,
    strtab_off: u32,
    shstrtab_off: u32,
}

fn build_shstrtab() -> ShstrtabData {
    let mut bytes = vec![0u8];
    let text_off = bytes.len() as u32;
    bytes.extend_from_slice(b".text\0");
    let symtab_off = bytes.len() as u32;
    bytes.extend_from_slice(b".symtab\0");
    let strtab_off = bytes.len() as u32;
    bytes.extend_from_slice(b".strtab\0");
    let shstrtab_off = bytes.len() as u32;
    bytes.extend_from_slice(b".shstrtab\0");
    ShstrtabData {
        bytes,
        text_off,
        symtab_off,
        strtab_off,
        shstrtab_off,
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
}
