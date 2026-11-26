//! Drive the `synth` binary and read what it emitted.
//!
//! Function bytes come from the ELF SYMBOL TABLE (`STT_FUNC` value and size
//! within `.text`), never from `synth disasm` text, which is host-dependent.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use object::read::elf::{ElfFile, FileHeader, Sym};
use object::{Object as _, ObjectSection as _, ObjectSymbol as _, SectionIndex, SymbolKind};

/// The machine an object was emitted for, from `e_machine`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Machine {
    Arm,
    RiscV32,
    /// AArch64 (A64), an ELF64 object.
    AArch64,
}

/// A function symbol, located within `.text`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuncSym {
    /// Byte offset of the first instruction within `.text`.
    pub offset: u64,
    /// `st_size`.
    pub size: u64,
    /// ARM only: the symbol value carried the Thumb bit.
    pub thumb: bool,
    pub global: bool,
}

/// A compiled object, parsed.
#[derive(Clone, Debug)]
pub struct CompiledObject {
    pub path: PathBuf,
    pub machine: Machine,
    /// The bytes of `.text`.
    pub text: Vec<u8>,
    /// Function symbols in `.text` by name. When a name is bound more than
    /// once, the GLOBAL binding wins.
    pub funcs: BTreeMap<String, FuncSym>,
    /// Offsets (within `.text`) that carry a relocation.
    pub text_relocs: Vec<u64>,
    /// The same relocations, resolved against the symbol table (see
    /// [`TextReloc`]). The hosted emulator links from these.
    pub relocs: Vec<TextReloc>,
    /// `e_type == ET_REL`: a host-linked object, not a self-contained image.
    pub relocatable: bool,
    /// The ELF header's `e_flags` (RQ-91-RV32ISA: the RV32 RVC bit).
    pub e_flags: u32,
}

/// One relocation in `.text`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TextReloc {
    /// Byte offset of the relocated instruction within `.text`.
    pub offset: u64,
    /// The ELF relocation type (`R_ARM_THM_CALL` = 10).
    pub r_type: u32,
    /// The relocation's explicit addend (RELA, as RV32 objects carry; 0 for
    /// a REL relocation, whose addend is in the instruction).
    pub addend: i64,
    /// The symbol's name; empty when the symbol has none.
    pub symbol: String,
    /// `Some(offset within .text)` when the symbol is DEFINED in `.text` (an
    /// internal call), with the Thumb bit stripped; `None` when it is
    /// undefined, i.e. the host linker must provide it.
    pub target: Option<u64>,
    /// The symbol is undefined (`SHN_UNDEF`): something the link supplies.
    /// The RV32 link step ([`crate::emulate::EmuEnv`]) requires it for a
    /// host stub, so a symbol in another section is not mistaken for one.
    pub undefined: bool,
}

/// `R_ARM_THM_CALL`: the only relocation the hosted emulator resolves.
pub const R_ARM_THM_CALL: u32 = 10;

/// Resolve a Thumb `BL` at `text[offset..offset + 4]` so it branches from
/// `place` (the instruction's address) to `dest`, as a static linker resolves
/// `R_ARM_THM_CALL` on a REL object: `S + A - P`, the addend `A` read from the
/// instruction itself.
///
/// Refuses bytes that are not a `BL` (T1) and a displacement outside its
/// +/-16 MiB range; `text` is left untouched on refusal.
pub fn patch_thm_call(text: &mut [u8], offset: u64, place: u64, dest: u64) -> Result<(), String> {
    let o = usize::try_from(offset).map_err(|_| "offset overflow".to_string())?;
    let bytes = text
        .get(o..o + 4)
        .ok_or_else(|| format!("relocation at {offset:#x} runs past .text"))?;
    let hw1 = u32::from(u16::from_le_bytes([bytes[0], bytes[1]]));
    let hw2 = u32::from(u16::from_le_bytes([bytes[2], bytes[3]]));
    if hw1 & 0xF800 != 0xF000 || hw2 & 0xD000 != 0xD000 {
        return Err(format!(
            "relocation at {offset:#x}: {hw1:04x} {hw2:04x} is not a Thumb BL"
        ));
    }
    // Decode the addend.
    let s = (hw1 >> 10) & 1;
    let j1 = (hw2 >> 13) & 1;
    let j2 = (hw2 >> 11) & 1;
    let i1 = 1 ^ (j1 ^ s);
    let i2 = 1 ^ (j2 ^ s);
    let raw = (s << 24) | (i1 << 23) | (i2 << 22) | ((hw1 & 0x3FF) << 12) | ((hw2 & 0x7FF) << 1);
    let addend = i64::from(((raw << 7) as i32) >> 7);
    // `S + A - P`, with `P` the instruction's address. The CPU then branches
    // to `P + 4 + encoded`, which the conventional addend of -4 turns into
    // `dest` exactly.
    let rel = dest as i64 + addend - place as i64;
    if rel & 1 != 0 || !(-(1 << 24)..(1 << 24)).contains(&rel) {
        return Err(format!(
            "relocation at {offset:#x}: displacement {rel:#x} does not fit a Thumb BL"
        ));
    }
    let v = rel as u32;
    let s = (v >> 24) & 1;
    let i1 = (v >> 23) & 1;
    let i2 = (v >> 22) & 1;
    let j1 = 1 ^ (i1 ^ s);
    let j2 = 1 ^ (i2 ^ s);
    let hw1 = 0xF000 | (s << 10) | ((v >> 12) & 0x3FF);
    let hw2 = 0xD000 | (j1 << 13) | (j2 << 11) | ((v >> 1) & 0x7FF);
    text[o..o + 2].copy_from_slice(&(hw1 as u16).to_le_bytes());
    text[o + 2..o + 4].copy_from_slice(&(hw2 as u16).to_le_bytes());
    Ok(())
}

impl CompiledObject {
    /// Parse an ELF object or executable emitted by synth: ELF32 for ARM and
    /// RV32, ELF64 for AArch64.
    pub fn parse(path: &Path) -> Result<Self, String> {
        let data = std::fs::read(path).map_err(|e| format!("read {}: {e}", path.display()))?;
        Self::parse_bytes(path, &data)
    }

    pub fn parse_bytes(path: &Path, data: &[u8]) -> Result<Self, String> {
        match object::FileKind::parse(data) {
            Ok(object::FileKind::Elf32) => {
                Self::parse_elf::<object::elf::FileHeader32<object::Endianness>>(path, data, false)
            }
            Ok(object::FileKind::Elf64) => {
                Self::parse_elf::<object::elf::FileHeader64<object::Endianness>>(path, data, true)
            }
            other => Err(format!("{}: not an ELF file: {other:?}", path.display())),
        }
    }

    /// `elf64` is the file's class. A machine is accepted only in the class
    /// synth emits it in (ARM and RV32 in ELF32, AArch64 in ELF64): an
    /// RV64 object, say, carries `EM_RISCV` too and must not be read as RV32.
    fn parse_elf<Elf: FileHeader<Endian = object::Endianness>>(
        path: &Path,
        data: &[u8],
        elf64: bool,
    ) -> Result<Self, String> {
        let file = ElfFile::<Elf>::parse(data)
            .map_err(|e| format!("{}: not an ELF file: {e}", path.display()))?;
        let endian = file.endian();
        let machine = match (file.elf_header().e_machine(endian), elf64) {
            (object::elf::EM_ARM, false) => Machine::Arm,
            (object::elf::EM_RISCV, false) => Machine::RiscV32,
            (object::elf::EM_AARCH64, true) => Machine::AArch64,
            (m, _) => {
                return Err(format!(
                    "{}: unsupported e_machine {m} in an ELF{} file",
                    path.display(),
                    if elf64 { 64 } else { 32 }
                ));
            }
        };
        let text_sec = file
            .section_by_name(".text")
            .ok_or_else(|| format!("{}: no .text section", path.display()))?;
        let text_idx: SectionIndex = text_sec.index();
        let text_addr = text_sec.address();
        let text = text_sec
            .data()
            .map_err(|e| format!("{}: .text: {e}", path.display()))?
            .to_vec();
        let mut funcs = BTreeMap::new();
        for sym in file.symbols() {
            if sym.kind() != SymbolKind::Text || sym.section_index() != Some(text_idx) {
                continue;
            }
            let Ok(name) = sym.name() else { continue };
            if name.is_empty() || name.starts_with('$') {
                continue;
            }
            // The RAW st_value, so the Thumb bit is ours to interpret.
            let raw: u64 = sym.elf_symbol().st_value(endian).into();
            let thumb = machine == Machine::Arm && raw & 1 == 1;
            let addr = if machine == Machine::Arm {
                raw & !1
            } else {
                raw
            };
            let fs = FuncSym {
                offset: addr - text_addr,
                size: sym.elf_symbol().st_size(endian).into(),
                thumb,
                global: sym.is_global(),
            };
            match funcs.get(name) {
                Some(FuncSym { global: true, .. }) if !fs.global => {}
                _ => {
                    funcs.insert(name.to_string(), fs);
                }
            }
        }
        let text_relocs = text_sec.relocations().map(|(off, _)| off).collect();
        let mut relocs = Vec::new();
        for (offset, rel) in text_sec.relocations() {
            let object::RelocationFlags::Elf { r_type } = rel.flags() else {
                return Err(format!("{}: non-ELF relocation flags", path.display()));
            };
            let object::RelocationTarget::Symbol(si) = rel.target() else {
                return Err(format!(
                    "{}: relocation at {offset:#x} names no symbol",
                    path.display()
                ));
            };
            let sym = file
                .symbol_by_index(si)
                .map_err(|e| format!("{}: relocation symbol: {e}", path.display()))?;
            let target = (sym.section_index() == Some(text_idx)).then(|| {
                let raw: u64 = sym.elf_symbol().st_value(endian).into();
                (if machine == Machine::Arm {
                    raw & !1
                } else {
                    raw
                }) - text_addr
            });
            relocs.push(TextReloc {
                offset,
                r_type: r_type.0,
                addend: rel.addend(),
                symbol: sym.name().unwrap_or("").to_string(),
                target,
                undefined: sym.is_undefined(),
            });
        }
        let relocatable = file.elf_header().e_type(endian) == object::elf::ET_REL;
        let e_flags = file.elf_header().e_flags(endian).0;
        Ok(Self {
            path: path.to_path_buf(),
            machine,
            text,
            funcs,
            text_relocs,
            relocs,
            relocatable,
            e_flags,
        })
    }

    pub fn func(&self, name: &str) -> Option<&FuncSym> {
        self.funcs.get(name)
    }

    /// The function's bytes, `[offset, offset + st_size)` of `.text`.
    pub fn function_bytes(&self, name: &str) -> Option<&[u8]> {
        let f = self.funcs.get(name)?;
        self.text
            .get(f.offset as usize..(f.offset + f.size) as usize)
    }

    /// Relocations that fall inside the function: a function with any cannot
    /// run without a link step.
    pub fn relocs_in(&self, name: &str) -> usize {
        self.funcs.get(name).map_or(0, |f| {
            self.text_relocs
                .iter()
                .filter(|&&r| r >= f.offset && r < f.offset + f.size)
                .count()
        })
    }
}

/// The synth binary: `$SYNTH` if set, otherwise `cargo build -p synth-cli`
/// in this workspace (once per process) and its `target/debug/synth`.
pub fn synth_binary() -> Result<PathBuf, String> {
    static BIN: OnceLock<Result<PathBuf, String>> = OnceLock::new();
    BIN.get_or_init(|| {
        if let Some(p) = std::env::var_os("SYNTH") {
            let p = PathBuf::from(p);
            return if p.is_file() {
                Ok(p)
            } else {
                Err(format!("SYNTH={} is not a file", p.display()))
            };
        }
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
        let st = Command::new(cargo)
            .current_dir(&root)
            .args(["build", "-q", "-p", "synth-cli"])
            .status()
            .map_err(|e| format!("cargo build -p synth-cli: {e}"))?;
        if !st.success() {
            return Err(format!("cargo build -p synth-cli: {st}"));
        }
        let target = std::env::var_os("CARGO_TARGET_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| root.join("target"));
        let bin = target.join("debug/synth");
        if bin.is_file() {
            Ok(bin)
        } else {
            Err(format!("built synth-cli but {} is missing", bin.display()))
        }
    })
    .clone()
}

/// The result of one `synth compile` run.
#[derive(Debug)]
pub struct CompileRun {
    pub status: std::process::ExitStatus,
    pub stderr: String,
    /// Present when the compile succeeded and produced a parseable object.
    pub object: Option<CompiledObject>,
}

/// `synth compile <input> <flags...> -o <out>`.
pub fn compile(input: &Path, flags: &[&str], out: &Path) -> Result<CompileRun, String> {
    let bin = synth_binary()?;
    let o = Command::new(&bin)
        .arg("compile")
        .arg(input)
        .args(flags)
        .arg("-o")
        .arg(out)
        .env("RUST_LOG", "error")
        .output()
        .map_err(|e| format!("{}: {e}", bin.display()))?;
    let stderr = String::from_utf8_lossy(&o.stderr).into_owned();
    let object = if o.status.success() {
        Some(CompiledObject::parse(out)?)
    } else {
        None
    };
    Ok(CompileRun {
        status: o.status,
        stderr,
        object,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bl(text: &[u8]) -> (u16, u16) {
        (
            u16::from_le_bytes([text[0], text[1]]),
            u16::from_le_bytes([text[2], text[3]]),
        )
    }

    /// The placeholder synth emits (`bl .` with the REL addend -4) resolved to
    /// known encodings: `bl +0x100` is `f000 f87e` at address 0 (branch target
    /// = 0 + 4 + 0xfc), a backward call needs the sign and J bits.
    #[test]
    fn thm_call_is_resolved_like_a_linker() {
        let placeholder = [0xff, 0xf7, 0xfe, 0xff]; // f7ff fffe
        let mut t = placeholder;
        patch_thm_call(&mut t, 0, 0x1_0000, 0x1_0100).unwrap();
        assert_eq!(bl(&t), (0xf000, 0xf87e));
        let mut t = placeholder;
        patch_thm_call(&mut t, 0, 0x1_0100, 0x1_0000).unwrap();
        assert_eq!(bl(&t), (0xf7ff, 0xff7e));
        // Far forward, past the 22-bit range the J bits extend.
        let mut t = placeholder;
        patch_thm_call(&mut t, 0, 0x1_0000, 0x50_0000).unwrap();
        assert_eq!(bl(&t), (0xf0ef, 0xf7fe));
        // Not a BL: refused, bytes untouched.
        let mut t = [0x70, 0x47, 0x00, 0xbf]; // bx lr; nop
        assert!(patch_thm_call(&mut t, 0, 0, 0x100).is_err());
        assert_eq!(t, [0x70, 0x47, 0x00, 0xbf]);
        // Out of range and misaligned: refused.
        let mut t = placeholder;
        assert!(patch_thm_call(&mut t, 0, 0, 0x200_0000).is_err());
        assert!(patch_thm_call(&mut t, 0, 0, 0x101).is_err());
        assert!(patch_thm_call(&mut t, 2, 0, 0x100).is_err());
        assert_eq!(t, placeholder);
    }
}
