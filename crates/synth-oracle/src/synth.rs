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
        Ok(Self {
            path: path.to_path_buf(),
            machine,
            text,
            funcs,
            text_relocs,
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
