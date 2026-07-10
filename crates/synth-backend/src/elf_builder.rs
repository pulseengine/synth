//! ELF (Executable and Linkable Format) Builder for ARM
//!
//! Generates ELF32 files for ARM Cortex-M targets

use synth_core::Result;

/// ELF file class
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ElfClass {
    /// 32-bit
    Elf32 = 1,
    /// 64-bit
    Elf64 = 2,
}

/// ELF data encoding
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ElfData {
    /// Little-endian
    LittleEndian = 1,
    /// Big-endian
    BigEndian = 2,
}

/// ELF file type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ElfType {
    /// Relocatable file
    Rel = 1,
    /// Executable file
    Exec = 2,
    /// Shared object file
    Dyn = 3,
}

/// ELF machine architecture
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ElfMachine {
    /// ARM
    Arm = 40,
    /// ARM64/AArch64
    AArch64 = 183,
}

/// Section type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SectionType {
    /// Null section
    Null = 0,
    /// Program data
    ProgBits = 1,
    /// Symbol table
    SymTab = 2,
    /// String table
    StrTab = 3,
    /// Relocation entries with addends
    Rela = 4,
    /// Symbol hash table
    Hash = 5,
    /// Dynamic linking information
    Dynamic = 6,
    /// Note
    Note = 7,
    /// No space (BSS)
    NoBits = 8,
    /// Relocation entries
    Rel = 9,
    /// ARM build attributes (`SHT_ARM_ATTRIBUTES`, #637) — the `.ARM.attributes`
    /// section every ARM toolchain consults to auto-select the Thumb/A32 decoder.
    ArmAttributes = 0x7000_0003,
}

/// Section flags
#[derive(Debug, Clone, Copy)]
pub struct SectionFlags(pub u32);

impl SectionFlags {
    /// Writable
    pub const WRITE: u32 = 0x1;
    /// Occupies memory during execution
    pub const ALLOC: u32 = 0x2;
    /// Executable
    pub const EXEC: u32 = 0x4;
    /// Mergeable
    pub const MERGE: u32 = 0x10;
    /// Contains null-terminated strings
    pub const STRINGS: u32 = 0x20;
}

/// ELF section
#[derive(Debug, Clone)]
pub struct Section {
    /// Section name (index into string table)
    pub name: String,
    /// Section type
    pub section_type: SectionType,
    /// Section flags
    pub flags: u32,
    /// Virtual address
    pub addr: u32,
    /// Section data
    pub data: Vec<u8>,
    /// Alignment
    pub align: u32,
    /// Explicit size (for NoBits sections like .bss where data is empty)
    pub explicit_size: Option<u32>,
}

impl Section {
    /// Create a new section
    pub fn new(name: &str, section_type: SectionType) -> Self {
        Self {
            name: name.to_string(),
            section_type,
            flags: 0,
            addr: 0,
            data: Vec::new(),
            align: 1,
            explicit_size: None,
        }
    }

    /// Set flags
    pub fn with_flags(mut self, flags: u32) -> Self {
        self.flags = flags;
        self
    }

    /// Set address
    pub fn with_addr(mut self, addr: u32) -> Self {
        self.addr = addr;
        self
    }

    /// Set alignment
    pub fn with_align(mut self, align: u32) -> Self {
        self.align = align;
        self
    }

    /// Add data
    pub fn with_data(mut self, data: Vec<u8>) -> Self {
        self.data = data;
        self
    }

    /// Set explicit size (for NoBits sections like .bss where data is empty)
    pub fn with_size(mut self, size: u32) -> Self {
        self.explicit_size = Some(size);
        self
    }

    /// Get the effective size of the section
    pub fn size(&self) -> u32 {
        self.explicit_size.unwrap_or(self.data.len() as u32)
    }
}

/// Symbol binding
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolBinding {
    /// Local symbol
    Local = 0,
    /// Global symbol
    Global = 1,
    /// Weak symbol
    Weak = 2,
}

/// Symbol type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolType {
    /// No type
    NoType = 0,
    /// Object (data)
    Object = 1,
    /// Function
    Func = 2,
    /// Section
    Section = 3,
    /// File name
    File = 4,
}

/// ELF symbol
#[derive(Debug, Clone)]
pub struct Symbol {
    /// Symbol name
    pub name: String,
    /// Value/address
    pub value: u32,
    /// Size
    pub size: u32,
    /// Binding
    pub binding: SymbolBinding,
    /// Type
    pub symbol_type: SymbolType,
    /// Section index
    pub section: u16,
}

impl Symbol {
    /// Create a new symbol
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            value: 0,
            size: 0,
            binding: SymbolBinding::Local,
            symbol_type: SymbolType::NoType,
            section: 0,
        }
    }

    /// Set value
    pub fn with_value(mut self, value: u32) -> Self {
        self.value = value;
        self
    }

    /// Set size
    pub fn with_size(mut self, size: u32) -> Self {
        self.size = size;
        self
    }

    /// Set binding
    pub fn with_binding(mut self, binding: SymbolBinding) -> Self {
        self.binding = binding;
        self
    }

    /// Set type
    pub fn with_type(mut self, symbol_type: SymbolType) -> Self {
        self.symbol_type = symbol_type;
        self
    }

    /// Set section
    pub fn with_section(mut self, section: u16) -> Self {
        self.section = section;
        self
    }
}

/// Program header type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProgramType {
    /// Null entry
    Null = 0,
    /// Loadable segment
    Load = 1,
    /// Dynamic linking info
    Dynamic = 2,
    /// Interpreter path
    Interp = 3,
    /// Note section
    Note = 4,
}

/// Program header flags
pub struct ProgramFlags;

impl ProgramFlags {
    /// Executable
    pub const EXEC: u32 = 0x1;
    /// Writable
    pub const WRITE: u32 = 0x2;
    /// Readable
    pub const READ: u32 = 0x4;
}

/// ELF program header (segment)
#[derive(Debug, Clone)]
pub struct ProgramHeader {
    /// Segment type
    pub p_type: ProgramType,
    /// Offset in file
    pub offset: u32,
    /// Virtual address
    pub vaddr: u32,
    /// Physical address
    pub paddr: u32,
    /// Size in file
    pub filesz: u32,
    /// Size in memory
    pub memsz: u32,
    /// Flags (R/W/X)
    pub flags: u32,
    /// Alignment
    pub align: u32,
}

impl ProgramHeader {
    /// Create a new LOAD segment
    pub fn load(vaddr: u32, offset: u32, size: u32, flags: u32) -> Self {
        Self {
            p_type: ProgramType::Load,
            offset,
            vaddr,
            paddr: vaddr, // Physical = virtual for simple cases
            filesz: size,
            memsz: size,
            flags,
            align: 4,
        }
    }

    /// Create a new LOAD segment for BSS-like regions (no file data, only memory)
    /// Used for .bss, linear memory, and other zero-initialized regions
    pub fn load_nobits(vaddr: u32, memsz: u32, flags: u32) -> Self {
        Self {
            p_type: ProgramType::Load,
            offset: 0, // No file offset for NoBits
            vaddr,
            paddr: vaddr, // Physical = virtual
            filesz: 0,    // No file data
            memsz,        // Memory size to allocate
            flags,
            align: 4,
        }
    }
}

/// ARM relocation type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArmRelocationType {
    /// R_ARM_THM_CALL (10) — Thumb BL/BLX instruction (Cortex-M). This is the
    /// correct relocation for a Thumb-2 `bl` call site; `Call`/R_ARM_CALL below
    /// is the ARM-mode form and is mis-resolved by `ld` for Thumb calls.
    ThmCall = 10,
    /// R_ARM_CALL (28) — BL/BLX instruction
    Call = 28,
    /// R_ARM_JUMP24 (29) — B/BL<cond> instruction
    Jump24 = 29,
    /// R_ARM_ABS32 (2) — Direct 32-bit reference
    Abs32 = 2,
    /// R_ARM_MOVW_ABS_NC (43) — MOVW instruction (low 16 bits)
    MovwAbsNc = 43,
    /// R_ARM_MOVT_ABS (44) — MOVT instruction (high 16 bits)
    MovtAbs = 44,
}

/// A built `.rel.<name>` section: its name offset in `.shstrtab`, the target
/// section index it relocates (`sh_info`), its file offset, and the encoded
/// REL entries. Internal to [`ElfBuilder::build`].
struct ExtraRelSection {
    name_offset: usize,
    target_idx: u32,
    offset: usize,
    data: Vec<u8>,
}

/// ELF relocation entry (REL format, no addend)
#[derive(Debug, Clone)]
pub struct Relocation {
    /// Offset within the section where the relocation applies
    pub offset: u32,
    /// Symbol index in the symbol table
    pub symbol_index: u32,
    /// Relocation type
    pub reloc_type: ArmRelocationType,
}

/// ARM EABI version 5 (soft-float)
pub const EF_ARM_EABI_VER5: u32 = 0x05000000;
/// ARM hard-float ABI flag
pub const EF_ARM_ABI_FLOAT_HARD: u32 = 0x00000400;
/// ARM soft-float ABI flag
pub const EF_ARM_ABI_FLOAT_SOFT: u32 = 0x00000200;

/// ARM EABI build-attribute tags and values (#637) — "Addenda to, and Errata
/// in, the ABI for the Arm Architecture" (build attributes). Only the tags the
/// synth ELF writer emits; consumers (objdump, gdb, `synth disasm`) use them to
/// auto-select the Thumb vs A32 decoder without a manual `--triple`.
pub mod aeabi {
    /// Tag_CPU_arch (uleb value)
    pub const TAG_CPU_ARCH: u32 = 6;
    /// Tag_CPU_arch_profile (uleb value: 'M', 'R', 'A')
    pub const TAG_CPU_ARCH_PROFILE: u32 = 7;
    /// Tag_ARM_ISA_use (0 = no A32, 1 = A32 permitted)
    pub const TAG_ARM_ISA_USE: u32 = 8;
    /// Tag_THUMB_ISA_use (0 = none, 1 = Thumb-1 (16-bit), 2 = Thumb-2)
    pub const TAG_THUMB_ISA_USE: u32 = 9;

    /// Tag_CPU_arch value: ARMv7 (Cortex-M3 / Cortex-R profile base)
    pub const CPU_ARCH_V7: u32 = 10;
    /// Tag_CPU_arch value: ARMv6-M (Cortex-M0)
    pub const CPU_ARCH_V6M: u32 = 11;
    /// Tag_CPU_arch value: ARMv7E-M (Cortex-M4/M7)
    pub const CPU_ARCH_V7EM: u32 = 13;
    /// Tag_CPU_arch value: ARMv8.1-M.mainline (Cortex-M55)
    pub const CPU_ARCH_V8_1M_MAIN: u32 = 21;

    /// Tag_CPU_arch_profile value: microcontroller
    pub const PROFILE_M: u32 = b'M' as u32;
    /// Tag_CPU_arch_profile value: real-time
    pub const PROFILE_R: u32 = b'R' as u32;
}

/// Encode a u32 as ULEB128 (build-attribute value encoding).
fn push_uleb128(out: &mut Vec<u8>, mut v: u32) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(byte);
            break;
        }
        out.push(byte | 0x80);
    }
}

/// Build the `.ARM.attributes` section (#637): format-version `'A'`, one
/// `"aeabi"` vendor subsection carrying a single `Tag_File` (1) subsubsection
/// with the given file-scope attributes. Tags with value 0 are omitted (0 is
/// the spec default). Standard toolchains (objdump, gdb, ld) read this to
/// auto-select the Thumb vs A32 decoder — synth objects become self-describing
/// instead of requiring a manual `--triple=thumbv7m`.
pub fn arm_attributes_section(
    cpu_arch: u32,
    cpu_arch_profile: u32,
    arm_isa_use: u32,
    thumb_isa_use: u32,
) -> Section {
    // File-scope attribute pairs (uleb tag, uleb value).
    let mut attrs = Vec::new();
    for (tag, value) in [
        (aeabi::TAG_CPU_ARCH, cpu_arch),
        (aeabi::TAG_CPU_ARCH_PROFILE, cpu_arch_profile),
        (aeabi::TAG_ARM_ISA_USE, arm_isa_use),
        (aeabi::TAG_THUMB_ISA_USE, thumb_isa_use),
    ] {
        if value != 0 {
            push_uleb128(&mut attrs, tag);
            push_uleb128(&mut attrs, value);
        }
    }

    // Tag_File (1) subsubsection: tag byte + u32 length (self-inclusive) + attrs.
    let file_len = (1 + 4 + attrs.len()) as u32;
    let mut file_sub = vec![1u8]; // Tag_File
    file_sub.extend_from_slice(&file_len.to_le_bytes());
    file_sub.extend_from_slice(&attrs);

    // "aeabi" vendor subsection: u32 length (self-inclusive) + NTBS name + data.
    let vendor_name = b"aeabi\0";
    let vendor_len = (4 + vendor_name.len() + file_sub.len()) as u32;
    let mut blob = vec![b'A']; // format version
    blob.extend_from_slice(&vendor_len.to_le_bytes());
    blob.extend_from_slice(vendor_name);
    blob.extend_from_slice(&file_sub);

    Section::new(".ARM.attributes", SectionType::ArmAttributes)
        .with_align(1)
        .with_data(blob)
}

/// ELF file builder
pub struct ElfBuilder {
    /// File class (32 or 64 bit)
    class: ElfClass,
    /// Data encoding
    data: ElfData,
    /// File type
    elf_type: ElfType,
    /// Machine architecture
    machine: ElfMachine,
    /// Entry point address
    entry: u32,
    /// ELF e_flags (EABI version + float ABI)
    e_flags: u32,
    /// Sections
    sections: Vec<Section>,
    /// Symbols
    symbols: Vec<Symbol>,
    /// Program headers (segments)
    program_headers: Vec<ProgramHeader>,
    /// Relocations for .text section
    relocations: Vec<Relocation>,
    /// Extra per-section relocation tables, keyed by the target section's name
    /// (e.g. `.debug_line`). Each produces a `.rel.<name>` section. Kept separate
    /// from `relocations` (the `.text` set) so the existing `.rel.text` byte
    /// layout is untouched: when this is empty the build is byte-identical to the
    /// pre-generalization output (VCR-DBG-001 PR C, #394).
    extra_relocations: Vec<(String, Vec<Relocation>)>,
    /// #598: whether the object's functions are Thumb-encoded. Bit 0 of an
    /// STT_FUNC `st_value` (and of `e_entry`) is the Thumb interworking bit —
    /// it must be SET for Thumb code (Cortex-M) and CLEAR for A32 code
    /// (cortex-r5 path). Defaults to `true` (every pre-#598 ARM object was
    /// treated as Thumb, so Thumb outputs stay bit-identical).
    thumb_funcs: bool,
}

impl ElfBuilder {
    /// Create a new ELF builder for ARM32
    pub fn new_arm32() -> Self {
        Self {
            class: ElfClass::Elf32,
            data: ElfData::LittleEndian,
            elf_type: ElfType::Exec,
            machine: ElfMachine::Arm,
            entry: 0,
            e_flags: EF_ARM_EABI_VER5,
            sections: Vec::new(),
            symbols: Vec::new(),
            program_headers: Vec::new(),
            relocations: Vec::new(),
            extra_relocations: Vec::new(),
            thumb_funcs: true,
        }
    }

    /// #598: mark the object's functions as A32-encoded (cortex-r5 path) —
    /// suppresses the Thumb interworking bit on STT_FUNC `st_value`s and on
    /// `e_entry`. Call BEFORE `with_entry`.
    pub fn with_thumb_funcs(mut self, thumb: bool) -> Self {
        self.thumb_funcs = thumb;
        self
    }

    /// Set entry point
    ///
    /// For ARM Thumb targets, bit 0 is automatically set to indicate Thumb mode.
    /// Cortex-M is Thumb-only, so function addresses in ELF must have bit 0 set.
    /// A32 objects (`with_thumb_funcs(false)`, #598) keep bit 0 clear.
    pub fn with_entry(mut self, entry: u32) -> Self {
        self.entry = if self.machine == ElfMachine::Arm && self.thumb_funcs {
            entry | 1 // Set Thumb bit for ARM Thumb targets
        } else {
            entry
        };
        self
    }

    /// Set ELF e_flags (e.g. to add hard-float ABI)
    pub fn set_flags(&mut self, flags: u32) {
        self.e_flags = flags;
    }

    /// Set file type
    pub fn with_type(mut self, elf_type: ElfType) -> Self {
        self.elf_type = elf_type;
        self
    }

    /// Add a section
    pub fn add_section(&mut self, section: Section) {
        self.sections.push(section);
    }

    /// Add a symbol
    pub fn add_symbol(&mut self, symbol: Symbol) {
        self.symbols.push(symbol);
    }

    /// Add a symbol and return its 1-based index in `.symtab` (index 0 is the
    /// reserved null symbol). Use when a later relocation must reference this
    /// symbol — e.g. the `.text` base symbol the DWARF `.rel.debug_*` records
    /// resolve against (VCR-DBG-001).
    pub fn add_symbol_indexed(&mut self, symbol: Symbol) -> u32 {
        let index = self.symbols.len() as u32 + 1;
        self.symbols.push(symbol);
        index
    }

    /// Add a program header (segment)
    pub fn add_program_header(&mut self, ph: ProgramHeader) {
        self.program_headers.push(ph);
    }

    /// Add a relocation entry for the .text section
    pub fn add_relocation(&mut self, reloc: Relocation) {
        self.relocations.push(reloc);
    }

    /// Add a relocation table targeting a non-`.text` section by name (e.g.
    /// `.debug_line`). Produces a separate `.rel.<name>` section whose `sh_info`
    /// points at the named section. The section must already have been added via
    /// [`add_section`]; if no matching section exists at build time the table is
    /// silently dropped. Used by VCR-DBG-001 to relocate the DWARF `.text`
    /// references so a host linker fixes them up alongside `.text`.
    pub fn add_section_relocations(&mut self, target_section: &str, relocs: Vec<Relocation>) {
        if relocs.is_empty() {
            return;
        }
        self.extra_relocations
            .push((target_section.to_string(), relocs));
    }

    /// Add an undefined external symbol (e.g., __meld_dispatch_import)
    /// Returns the symbol index (1-based, accounting for null symbol)
    pub fn add_undefined_symbol(&mut self, name: &str) -> u32 {
        let index = self.symbols.len() as u32 + 1; // +1 for null symbol
        self.symbols.push(Symbol {
            name: name.to_string(),
            value: 0,
            size: 0,
            binding: SymbolBinding::Global,
            symbol_type: SymbolType::Func,
            section: 0, // SHN_UNDEF
        });
        index
    }

    /// Build the ELF file to bytes
    pub fn build(&self) -> Result<Vec<u8>> {
        let mut output = Vec::new();

        // ELF header size (52 bytes for ELF32)
        let header_size = 52;
        // Program header size (32 bytes for ELF32)
        let ph_entry_size = 32;
        let ph_count = self.program_headers.len();
        let ph_table_size = ph_entry_size * ph_count;

        // Reserve space for ELF header + program headers
        output.resize(header_size + ph_table_size, 0);

        // Build string table for section names
        let (shstrtab_data, section_name_offsets, extra_rel_name_offsets) =
            self.build_section_string_table();

        // Build symbol string table
        let (strtab_data, symbol_name_offsets) = self.build_symbol_string_table();

        // #656: ELF requires every STB_LOCAL symbol to precede all non-local
        // symbols in `.symtab`, with the section's `sh_info` set to the index of
        // the first non-local symbol. Callers add symbols in whatever order is
        // convenient (and hold 1-based indices from `add_symbol_indexed` /
        // `add_undefined_symbol` for their relocations), so the LOCAL/GLOBAL
        // ordering is established here at build time: a stable locals-first
        // permutation, plus an old→new index map every relocation is rewritten
        // through. With zero local symbols (every pre-#656 object) the
        // permutation is the identity and `sh_info` stays 1 — byte-identical.
        let mut sym_order: Vec<usize> = (0..self.symbols.len()).collect();
        sym_order.sort_by_key(|&i| self.symbols[i].binding != SymbolBinding::Local);
        // old_to_new[old_1based] = new_1based; index 0 (the null symbol) maps to 0.
        let mut old_to_new = vec![0u32; self.symbols.len() + 1];
        for (new_pos, &old) in sym_order.iter().enumerate() {
            old_to_new[old + 1] = new_pos as u32 + 1;
        }
        let local_count = self
            .symbols
            .iter()
            .filter(|s| s.binding == SymbolBinding::Local)
            .count();
        // The null symbol (index 0) counts as local, so first-global = locals + 1.
        let symtab_sh_info = local_count as u32 + 1;
        let remap_relocs = |relocs: &[Relocation]| -> Vec<Relocation> {
            relocs
                .iter()
                .map(|r| Relocation {
                    offset: r.offset,
                    symbol_index: old_to_new[r.symbol_index as usize],
                    reloc_type: r.reloc_type,
                })
                .collect()
        };

        // Calculate section offsets (after ELF header + program headers)
        let mut current_offset = header_size + ph_table_size;

        // Section 1: .shstrtab (section name string table)
        let shstrtab_offset = current_offset;
        current_offset += shstrtab_data.len();

        // Section 2: .strtab (symbol name string table)
        let strtab_offset = current_offset;
        current_offset += strtab_data.len();

        // User sections
        let mut section_offsets = Vec::new();
        for section in &self.sections {
            section_offsets.push(current_offset);
            current_offset += section.data.len();
        }

        // Section 3: .symtab (symbol table), in locals-first order (#656)
        let symtab_offset = current_offset;
        let symtab_data = self.build_symbol_table(&symbol_name_offsets, &sym_order);
        current_offset += symtab_data.len();

        // Section 4+ (optional): .rel.text (relocations), symbol indices
        // rewritten through the locals-first permutation (#656)
        let rel_data = Self::encode_rel_entries(&remap_relocs(&self.relocations));
        let rel_offset = current_offset;
        current_offset += rel_data.len();

        // Extra per-section relocation tables (.rel.<name>), laid out after
        // .rel.text. Each entry resolves its target section index by name; a
        // table whose target section is absent is dropped. Empty when no
        // --debug-line ⇒ byte-identical to the pre-generalization layout.
        let mut extra_rel: Vec<ExtraRelSection> = Vec::new();
        for (i, (target, relocs)) in self.extra_relocations.iter().enumerate() {
            let Some(target_idx) = self.section_index_by_name(target) else {
                continue;
            };
            let data = Self::encode_rel_entries(&remap_relocs(relocs));
            let name_offset = extra_rel_name_offsets.get(i).copied().unwrap_or(0);
            extra_rel.push(ExtraRelSection {
                name_offset,
                target_idx,
                offset: current_offset,
                data,
            });
            current_offset += extra_rel.last().unwrap().data.len();
        }

        // Section header table comes at the end
        let sh_offset = current_offset;

        // Now write all the data
        output.extend_from_slice(&shstrtab_data);
        output.extend_from_slice(&strtab_data);

        for section in &self.sections {
            output.extend_from_slice(&section.data);
        }

        output.extend_from_slice(&symtab_data);
        output.extend_from_slice(&rel_data);
        for er in &extra_rel {
            output.extend_from_slice(&er.data);
        }

        // Write section headers
        let section_headers = self.build_section_headers_with_rel(
            &section_name_offsets,
            shstrtab_offset,
            &shstrtab_data,
            strtab_offset,
            &strtab_data,
            symtab_offset,
            &symtab_data,
            &section_offsets,
            rel_offset,
            &rel_data,
            &extra_rel,
            symtab_sh_info,
        );
        output.extend_from_slice(&section_headers);

        // Write program headers (right after ELF header)
        // Auto-correct p_offset for LOAD segments by matching vaddr to section addrs
        for (i, ph) in self.program_headers.iter().enumerate() {
            let ph_offset = header_size + i * ph_entry_size;
            let mut corrected_ph = ph.clone();
            if corrected_ph.filesz > 0 {
                // Find the section whose addr matches this segment's vaddr
                for (si, section) in self.sections.iter().enumerate() {
                    if section.addr == corrected_ph.vaddr && si < section_offsets.len() {
                        corrected_ph.offset = section_offsets[si] as u32;
                        break;
                    }
                }
            }
            self.write_program_header(
                &mut output[ph_offset..ph_offset + ph_entry_size],
                &corrected_ph,
            );
        }

        // Now write the actual ELF header at the beginning
        let has_rel = !self.relocations.is_empty();
        let num_sections = 4 + self.sections.len() + if has_rel { 1 } else { 0 } + extra_rel.len();
        let ph_offset = if ph_count > 0 { header_size as u32 } else { 0 };
        self.write_elf_header_with_phdrs(
            &mut output[0..header_size],
            ph_offset,
            ph_count as u16,
            sh_offset as u32,
            num_sections as u16,
        )?;

        Ok(output)
    }

    /// Write a single program header
    fn write_program_header(&self, output: &mut [u8], ph: &ProgramHeader) {
        let mut cursor = 0;

        // p_type (4 bytes)
        output[cursor..cursor + 4].copy_from_slice(&(ph.p_type as u32).to_le_bytes());
        cursor += 4;

        // p_offset (4 bytes)
        output[cursor..cursor + 4].copy_from_slice(&ph.offset.to_le_bytes());
        cursor += 4;

        // p_vaddr (4 bytes)
        output[cursor..cursor + 4].copy_from_slice(&ph.vaddr.to_le_bytes());
        cursor += 4;

        // p_paddr (4 bytes)
        output[cursor..cursor + 4].copy_from_slice(&ph.paddr.to_le_bytes());
        cursor += 4;

        // p_filesz (4 bytes)
        output[cursor..cursor + 4].copy_from_slice(&ph.filesz.to_le_bytes());
        cursor += 4;

        // p_memsz (4 bytes)
        output[cursor..cursor + 4].copy_from_slice(&ph.memsz.to_le_bytes());
        cursor += 4;

        // p_flags (4 bytes)
        output[cursor..cursor + 4].copy_from_slice(&ph.flags.to_le_bytes());
        cursor += 4;

        // p_align (4 bytes)
        output[cursor..cursor + 4].copy_from_slice(&ph.align.to_le_bytes());
    }

    /// Write ELF header with program header info
    fn write_elf_header_with_phdrs(
        &self,
        output: &mut [u8],
        ph_offset: u32,
        ph_count: u16,
        sh_offset: u32,
        sh_count: u16,
    ) -> Result<()> {
        let mut cursor = 0;

        // ELF magic number
        output[cursor..cursor + 4].copy_from_slice(&[0x7f, b'E', b'L', b'F']);
        cursor += 4;

        // Class (32-bit)
        output[cursor] = self.class as u8;
        cursor += 1;

        // Data (little-endian)
        output[cursor] = self.data as u8;
        cursor += 1;

        // Version
        output[cursor] = 1;
        cursor += 1;

        // OS/ABI
        output[cursor] = 0; // System V
        cursor += 1;

        // ABI version
        output[cursor] = 0;
        cursor += 1;

        // Padding (7 bytes)
        output[cursor..cursor + 7].copy_from_slice(&[0; 7]);
        cursor += 7;

        // Type (little-endian u16)
        let etype = self.elf_type as u16;
        output[cursor..cursor + 2].copy_from_slice(&etype.to_le_bytes());
        cursor += 2;

        // Machine (little-endian u16)
        let machine = self.machine as u16;
        output[cursor..cursor + 2].copy_from_slice(&machine.to_le_bytes());
        cursor += 2;

        // Version (little-endian u32)
        output[cursor..cursor + 4].copy_from_slice(&1u32.to_le_bytes());
        cursor += 4;

        // Entry point (little-endian u32)
        output[cursor..cursor + 4].copy_from_slice(&self.entry.to_le_bytes());
        cursor += 4;

        // Program header offset (little-endian u32)
        output[cursor..cursor + 4].copy_from_slice(&ph_offset.to_le_bytes());
        cursor += 4;

        // Section header offset (little-endian u32)
        output[cursor..cursor + 4].copy_from_slice(&sh_offset.to_le_bytes());
        cursor += 4;

        // Flags (little-endian u32) - ARM EABI version 5 + float ABI
        output[cursor..cursor + 4].copy_from_slice(&self.e_flags.to_le_bytes());
        cursor += 4;

        // ELF header size (little-endian u16)
        output[cursor..cursor + 2].copy_from_slice(&52u16.to_le_bytes());
        cursor += 2;

        // Program header entry size (little-endian u16)
        let ph_entry_size: u16 = if ph_count > 0 { 32 } else { 0 };
        output[cursor..cursor + 2].copy_from_slice(&ph_entry_size.to_le_bytes());
        cursor += 2;

        // Program header count (little-endian u16)
        output[cursor..cursor + 2].copy_from_slice(&ph_count.to_le_bytes());
        cursor += 2;

        // Section header entry size (little-endian u16)
        output[cursor..cursor + 2].copy_from_slice(&40u16.to_le_bytes());
        cursor += 2;

        // Section header count (little-endian u16)
        output[cursor..cursor + 2].copy_from_slice(&sh_count.to_le_bytes());
        cursor += 2;

        // Section header string table index (little-endian u16) - .shstrtab is section 1
        output[cursor..cursor + 2].copy_from_slice(&1u16.to_le_bytes());

        Ok(())
    }

    /// Build section name string table. Returns the bytes, the per-user-section
    /// name offsets, and the per-extra-relocation `.rel.<name>` name offsets
    /// (parallel to `self.extra_relocations`). The extra-rel names are appended
    /// AFTER `.rel.text`, so when `extra_relocations` is empty the table is
    /// byte-identical to the pre-generalization layout.
    fn build_section_string_table(&self) -> (Vec<u8>, Vec<usize>, Vec<usize>) {
        let mut strtab = vec![0]; // null string at offset 0
        let mut offsets = Vec::new();

        // Standard sections
        strtab.extend_from_slice(b".shstrtab\0");
        strtab.extend_from_slice(b".strtab\0");
        strtab.extend_from_slice(b".symtab\0");

        // User sections
        for section in &self.sections {
            let offset = strtab.len();
            offsets.push(offset);
            strtab.extend_from_slice(section.name.as_bytes());
            strtab.push(0);
        }

        // .rel.text (if relocations exist)
        if !self.relocations.is_empty() {
            strtab.extend_from_slice(b".rel.text\0");
        }

        // .rel.<name> for each extra per-section relocation table.
        let mut extra_rel_offsets = Vec::new();
        for (target, _) in &self.extra_relocations {
            let offset = strtab.len();
            extra_rel_offsets.push(offset);
            strtab.extend_from_slice(format!(".rel{target}\0").as_bytes());
        }

        (strtab, offsets, extra_rel_offsets)
    }

    /// Build symbol name string table
    fn build_symbol_string_table(&self) -> (Vec<u8>, Vec<usize>) {
        let mut strtab = vec![0]; // null string at offset 0
        let mut offsets = Vec::new();

        for symbol in &self.symbols {
            let offset = strtab.len();
            offsets.push(offset);
            strtab.extend_from_slice(symbol.name.as_bytes());
            strtab.push(0);
        }

        (strtab, offsets)
    }

    /// Encode a slice of relocations as ELF32 REL entries (8 bytes each). Shared
    /// by `.rel.text` and the per-section `.rel.<name>` tables.
    fn encode_rel_entries(relocs: &[Relocation]) -> Vec<u8> {
        let mut rel_data = Vec::new();
        for reloc in relocs {
            // r_offset (4 bytes)
            rel_data.extend_from_slice(&reloc.offset.to_le_bytes());
            // r_info (4 bytes) = (sym_index << 8) | type
            let r_info = (reloc.symbol_index << 8) | (reloc.reloc_type as u32);
            rel_data.extend_from_slice(&r_info.to_le_bytes());
        }
        rel_data
    }

    /// Resolve a target section name to its ELF section index. User sections
    /// begin at index 4 (null=0, shstrtab=1, strtab=2, symtab=3). Returns `None`
    /// if no user section has that name.
    fn section_index_by_name(&self, name: &str) -> Option<u32> {
        self.sections
            .iter()
            .position(|s| s.name == name)
            .map(|pos| 4 + pos as u32)
    }

    /// Build symbol table. `order` is the locals-first permutation of
    /// `self.symbols` computed in [`build`] (#656): entry `k` of the emitted
    /// table (after the null symbol) is `self.symbols[order[k]]`.
    fn build_symbol_table(&self, name_offsets: &[usize], order: &[usize]) -> Vec<u8> {
        let mut symtab = Vec::new();

        // First entry is always null symbol
        symtab.extend_from_slice(&[0u8; 16]); // 16 bytes per symbol in ELF32

        // User symbols, locals first (#656)
        for &i in order {
            let symbol = &self.symbols[i];
            let name_offset = if i < name_offsets.len() {
                name_offsets[i] as u32
            } else {
                0
            };

            // st_name (4 bytes)
            symtab.extend_from_slice(&name_offset.to_le_bytes());

            // st_value (4 bytes)
            // For ARM THUMB targets, STT_FUNC symbols must have bit 0 set (Thumb
            // interworking). #598: A32 objects (cortex-r5 path) must NOT set it —
            // bit 0 on an A32 function address is wrong metadata (harnesses had
            // to mask it; an interworking-aware consumer would mis-classify the
            // function as Thumb).
            let value = if self.machine == ElfMachine::Arm
                && self.thumb_funcs
                && symbol.symbol_type == SymbolType::Func
            {
                symbol.value | 1
            } else {
                symbol.value
            };
            symtab.extend_from_slice(&value.to_le_bytes());

            // st_size (4 bytes)
            symtab.extend_from_slice(&symbol.size.to_le_bytes());

            // st_info (1 byte) = (binding << 4) | (type & 0xf)
            let info = ((symbol.binding as u8) << 4) | (symbol.symbol_type as u8 & 0xf);
            symtab.push(info);

            // st_other (1 byte)
            symtab.push(0);

            // st_shndx (2 bytes)
            symtab.extend_from_slice(&symbol.section.to_le_bytes());
        }

        symtab
    }

    /// Build section headers (with optional .rel.text)
    #[allow(clippy::too_many_arguments)]
    fn build_section_headers_with_rel(
        &self,
        section_name_offsets: &[usize],
        shstrtab_offset: usize,
        shstrtab_data: &[u8],
        strtab_offset: usize,
        strtab_data: &[u8],
        symtab_offset: usize,
        symtab_data: &[u8],
        section_offsets: &[usize],
        rel_offset: usize,
        rel_data: &[u8],
        extra_rel: &[ExtraRelSection],
        // #656: `.symtab` sh_info = index of the first non-LOCAL symbol
        // (1 + number of local symbols; the null symbol counts as local).
        symtab_sh_info: u32,
    ) -> Vec<u8> {
        let mut headers = Vec::new();

        // Section header size is 40 bytes for ELF32

        // Section 0: null section
        headers.extend_from_slice(&[0u8; 40]);

        // Section 1: .shstrtab
        self.write_section_header(
            &mut headers,
            1,
            SectionType::StrTab as u32,
            0,
            0,
            shstrtab_offset as u32,
            shstrtab_data.len() as u32,
            0,
            0,
            1,
            0,
        );

        // Section 2: .strtab
        let strtab_name_offset = ".shstrtab\0".len();
        self.write_section_header(
            &mut headers,
            strtab_name_offset as u32,
            SectionType::StrTab as u32,
            0,
            0,
            strtab_offset as u32,
            strtab_data.len() as u32,
            0,
            0,
            1,
            0,
        );

        // Section 3: .symtab (links to .strtab which is section 2)
        let symtab_name_offset = ".shstrtab\0.strtab\0".len();
        self.write_section_header(
            &mut headers,
            symtab_name_offset as u32,
            SectionType::SymTab as u32,
            0,
            0,
            symtab_offset as u32,
            symtab_data.len() as u32,
            2,
            // #656: was hardcoded 1 (the #430 blocker) — with local symbols
            // present that under-reports, and `ld` then treats every local as
            // global-bindable. Now the real first-non-local index.
            symtab_sh_info,
            4,
            16,
        );

        // User sections
        for (i, section) in self.sections.iter().enumerate() {
            let name_offset = if i < section_name_offsets.len() {
                section_name_offsets[i] as u32
            } else {
                0
            };
            let offset = if i < section_offsets.len() {
                section_offsets[i] as u32
            } else {
                0
            };

            self.write_section_header(
                &mut headers,
                name_offset,
                section.section_type as u32,
                section.flags,
                section.addr,
                offset,
                section.size(),
                0,
                0,
                section.align,
                0,
            );
        }

        // .rel.text section (if relocations exist)
        if !rel_data.is_empty() {
            let rel_name_offset = self.rel_text_shstrtab_offset();
            // sh_link = symtab section index (3), sh_info = .text section index (4, first user section)
            let text_section_idx = 4u32; // null(0) + shstrtab(1) + strtab(2) + symtab(3) + .text(4)
            self.write_section_header(
                &mut headers,
                rel_name_offset as u32,
                SectionType::Rel as u32,
                0,
                0,
                rel_offset as u32,
                rel_data.len() as u32,
                3,                // sh_link = .symtab section index
                text_section_idx, // sh_info = section to which relocations apply
                4,
                8, // Each REL entry is 8 bytes
            );
        }

        // Extra .rel.<name> sections (e.g. .rel.debug_line). Same shape as
        // .rel.text but sh_info points at the named target section.
        for er in extra_rel {
            self.write_section_header(
                &mut headers,
                er.name_offset as u32,
                SectionType::Rel as u32,
                0,
                0,
                er.offset as u32,
                er.data.len() as u32,
                3,             // sh_link = .symtab section index
                er.target_idx, // sh_info = relocated section
                4,
                8, // Each REL entry is 8 bytes
            );
        }

        headers
    }

    /// Compute the shstrtab offset where .rel.text name begins
    fn rel_text_shstrtab_offset(&self) -> usize {
        // Layout: \0 .shstrtab\0 .strtab\0 .symtab\0 [user sections...] .rel.text\0
        let mut offset = 1 + ".shstrtab\0".len() + ".strtab\0".len() + ".symtab\0".len();
        for section in &self.sections {
            offset += section.name.len() + 1;
        }
        offset
    }

    /// Write a single section header
    #[allow(clippy::too_many_arguments)]
    fn write_section_header(
        &self,
        output: &mut Vec<u8>,
        name: u32,
        sh_type: u32,
        flags: u32,
        addr: u32,
        offset: u32,
        size: u32,
        link: u32,
        info: u32,
        align: u32,
        entsize: u32,
    ) {
        output.extend_from_slice(&name.to_le_bytes());
        output.extend_from_slice(&sh_type.to_le_bytes());
        output.extend_from_slice(&flags.to_le_bytes());
        output.extend_from_slice(&addr.to_le_bytes());
        output.extend_from_slice(&offset.to_le_bytes());
        output.extend_from_slice(&size.to_le_bytes());
        output.extend_from_slice(&link.to_le_bytes());
        output.extend_from_slice(&info.to_le_bytes());
        output.extend_from_slice(&align.to_le_bytes());
        output.extend_from_slice(&entsize.to_le_bytes());
    }

    /// Write ELF header (legacy method for tests)
    #[allow(dead_code)]
    fn write_elf_header(&self, output: &mut Vec<u8>) -> Result<()> {
        // ELF magic number
        output.extend_from_slice(&[0x7f, b'E', b'L', b'F']);

        // Class (32-bit)
        output.push(self.class as u8);

        // Data (little-endian)
        output.push(self.data as u8);

        // Version
        output.push(1);

        // OS/ABI
        output.push(0); // System V

        // ABI version
        output.push(0);

        // Padding
        output.extend_from_slice(&[0; 7]);

        // Type (little-endian u16)
        let etype = self.elf_type as u16;
        output.extend_from_slice(&etype.to_le_bytes());

        // Machine (little-endian u16)
        let machine = self.machine as u16;
        output.extend_from_slice(&machine.to_le_bytes());

        // Version (little-endian u32)
        output.extend_from_slice(&1u32.to_le_bytes());

        // Entry point (little-endian u32)
        output.extend_from_slice(&self.entry.to_le_bytes());

        // Program header offset (little-endian u32)
        output.extend_from_slice(&0u32.to_le_bytes());

        // Section header offset (little-endian u32)
        output.extend_from_slice(&0u32.to_le_bytes());

        // Flags (little-endian u32)
        output.extend_from_slice(&0u32.to_le_bytes());

        // ELF header size (little-endian u16)
        output.extend_from_slice(&52u16.to_le_bytes());

        // Program header entry size (little-endian u16)
        output.extend_from_slice(&0u16.to_le_bytes());

        // Program header count (little-endian u16)
        output.extend_from_slice(&0u16.to_le_bytes());

        // Section header entry size (little-endian u16)
        output.extend_from_slice(&40u16.to_le_bytes());

        // Section header count (little-endian u16)
        output.extend_from_slice(&0u16.to_le_bytes());

        // Section header string table index (little-endian u16)
        output.extend_from_slice(&0u16.to_le_bytes());

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_elf_builder_creation() {
        let builder = ElfBuilder::new_arm32();
        assert_eq!(builder.class, ElfClass::Elf32);
        assert_eq!(builder.data, ElfData::LittleEndian);
        assert_eq!(builder.machine, ElfMachine::Arm);
    }

    #[test]
    fn test_section_creation() {
        let section = Section::new(".text", SectionType::ProgBits)
            .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
            .with_addr(0x8000)
            .with_align(4);

        assert_eq!(section.name, ".text");
        assert_eq!(section.section_type, SectionType::ProgBits);
        assert_eq!(section.addr, 0x8000);
        assert_eq!(section.align, 4);
    }

    #[test]
    fn test_symbol_creation() {
        let symbol = Symbol::new("main")
            .with_value(0x8000)
            .with_size(128)
            .with_binding(SymbolBinding::Global)
            .with_type(SymbolType::Func)
            .with_section(1);

        assert_eq!(symbol.name, "main");
        assert_eq!(symbol.value, 0x8000);
        assert_eq!(symbol.size, 128);
        assert_eq!(symbol.binding, SymbolBinding::Global);
        assert_eq!(symbol.symbol_type, SymbolType::Func);
    }

    #[test]
    fn test_elf_header_generation() {
        let builder = ElfBuilder::new_arm32().with_entry(0x8000);
        let elf = builder.build().unwrap();

        // Check magic number
        assert_eq!(&elf[0..4], &[0x7f, b'E', b'L', b'F']);

        // Check class (32-bit)
        assert_eq!(elf[4], 1);

        // Check data (little-endian)
        assert_eq!(elf[5], 1);

        // Check version
        assert_eq!(elf[6], 1);
    }

    #[test]
    fn test_add_sections() {
        let mut builder = ElfBuilder::new_arm32();

        let text = Section::new(".text", SectionType::ProgBits)
            .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC);

        let data = Section::new(".data", SectionType::ProgBits)
            .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE);

        builder.add_section(text);
        builder.add_section(data);

        assert_eq!(builder.sections.len(), 2);
    }

    #[test]
    fn test_add_symbols() {
        let mut builder = ElfBuilder::new_arm32();

        let main_sym = Symbol::new("main")
            .with_binding(SymbolBinding::Global)
            .with_type(SymbolType::Func);

        let data_sym = Symbol::new("data")
            .with_binding(SymbolBinding::Local)
            .with_type(SymbolType::Object);

        builder.add_symbol(main_sym);
        builder.add_symbol(data_sym);

        assert_eq!(builder.symbols.len(), 2);
    }

    #[test]
    fn test_complete_elf_generation() {
        // Create a complete ELF file with sections and symbols
        let mut builder = ElfBuilder::new_arm32()
            .with_entry(0x8000)
            .with_type(ElfType::Exec);

        // Add .text section with some ARM code
        let text_code = vec![
            0x00, 0x48, 0x2d, 0xe9, // push {fp, lr}
            0x04, 0xb0, 0x8d, 0xe2, // add fp, sp, #4
            0x00, 0x00, 0xa0, 0xe3, // mov r0, #0
            0x00, 0x88, 0xbd, 0xe8, // pop {fp, pc}
        ];
        let text = Section::new(".text", SectionType::ProgBits)
            .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
            .with_addr(0x8000)
            .with_align(4)
            .with_data(text_code);

        builder.add_section(text);

        // Add .data section
        let data_content = vec![0x01, 0x02, 0x03, 0x04];
        let data = Section::new(".data", SectionType::ProgBits)
            .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE)
            .with_addr(0x8100)
            .with_align(4)
            .with_data(data_content);

        builder.add_section(data);

        // Add .bss section (no data)
        let bss = Section::new(".bss", SectionType::NoBits)
            .with_flags(SectionFlags::ALLOC | SectionFlags::WRITE)
            .with_addr(0x8200)
            .with_align(4);

        builder.add_section(bss);

        // Add symbols
        let main_sym = Symbol::new("main")
            .with_value(0x8000)
            .with_size(16)
            .with_binding(SymbolBinding::Global)
            .with_type(SymbolType::Func)
            .with_section(4); // .text is section 4 (0=null, 1=shstrtab, 2=strtab, 3=symtab, 4=.text)

        builder.add_symbol(main_sym);

        let data_var = Symbol::new("global_var")
            .with_value(0x8100)
            .with_size(4)
            .with_binding(SymbolBinding::Global)
            .with_type(SymbolType::Object)
            .with_section(5); // .data is section 5

        builder.add_symbol(data_var);

        // Build the ELF file
        let elf = builder.build().unwrap();

        // Validate ELF header
        assert_eq!(&elf[0..4], &[0x7f, b'E', b'L', b'F']);
        assert_eq!(elf[4], 1); // 32-bit
        assert_eq!(elf[5], 1); // little-endian
        assert_eq!(elf[6], 1); // version

        // Check that we have a reasonable file size
        assert!(elf.len() > 52); // At least header size
        assert!(elf.len() < 10000); // Reasonable upper bound

        // Validate entry point is set correctly (Thumb bit set for ARM)
        let entry_bytes = &elf[24..28];
        let entry = u32::from_le_bytes([
            entry_bytes[0],
            entry_bytes[1],
            entry_bytes[2],
            entry_bytes[3],
        ]);
        assert_eq!(entry, 0x8001); // 0x8000 | 1 (Thumb bit)

        // Validate section header offset is non-zero
        let sh_off_bytes = &elf[32..36];
        let sh_off = u32::from_le_bytes([
            sh_off_bytes[0],
            sh_off_bytes[1],
            sh_off_bytes[2],
            sh_off_bytes[3],
        ]);
        assert!(sh_off > 0);

        // Validate section count (null + shstrtab + strtab + symtab + .text + .data + .bss = 7)
        let sh_num_bytes = &elf[48..50];
        let sh_num = u16::from_le_bytes([sh_num_bytes[0], sh_num_bytes[1]]);
        assert_eq!(sh_num, 7);

        // Validate string table index points to .shstrtab (section 1)
        let shstrndx_bytes = &elf[50..52];
        let shstrndx = u16::from_le_bytes([shstrndx_bytes[0], shstrndx_bytes[1]]);
        assert_eq!(shstrndx, 1);
    }

    #[test]
    fn test_string_table_generation() {
        let mut builder = ElfBuilder::new_arm32();

        builder.add_section(Section::new(".text", SectionType::ProgBits));
        builder.add_section(Section::new(".data", SectionType::ProgBits));

        let (strtab, offsets, _extra_rel_offsets) = builder.build_section_string_table();

        // Should have null byte at start
        assert_eq!(strtab[0], 0);

        // Should contain .shstrtab, .strtab, .symtab, .text, .data
        let strtab_str = String::from_utf8_lossy(&strtab);
        assert!(strtab_str.contains(".shstrtab"));
        assert!(strtab_str.contains(".strtab"));
        assert!(strtab_str.contains(".symtab"));
        assert!(strtab_str.contains(".text"));
        assert!(strtab_str.contains(".data"));

        // Should have offsets for user sections
        assert_eq!(offsets.len(), 2);
    }

    #[test]
    fn test_relocation_support() {
        let mut builder = ElfBuilder::new_arm32()
            .with_entry(0x8000)
            .with_type(ElfType::Rel);

        // Add .text section with a BL placeholder
        let text_code = vec![0x00u8; 16]; // 4 instructions of placeholder
        let text = Section::new(".text", SectionType::ProgBits)
            .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
            .with_addr(0x8000)
            .with_align(4)
            .with_data(text_code);
        builder.add_section(text);

        // Add undefined external symbol
        let sym_idx = builder.add_undefined_symbol("__meld_dispatch_import");
        assert!(sym_idx > 0);

        // Add relocation for the BL at offset 4
        builder.add_relocation(Relocation {
            offset: 4,
            symbol_index: sym_idx,
            reloc_type: ArmRelocationType::Call,
        });

        let elf = builder.build().unwrap();

        // Verify ELF is valid
        assert_eq!(&elf[0..4], &[0x7f, b'E', b'L', b'F']);

        // Section count should include .rel.text
        // null(1) + shstrtab(1) + strtab(1) + symtab(1) + .text(1) + .rel.text(1) = 6
        let sh_num = u16::from_le_bytes([elf[48], elf[49]]);
        assert_eq!(sh_num, 6);

        // Verify the symbol table contains the undefined symbol
        // (section = 0 for SHN_UNDEF)
        let has_undef = elf
            .windows(b"__meld_dispatch_import".len())
            .any(|w| w == b"__meld_dispatch_import");
        assert!(
            has_undef,
            "ELF should contain __meld_dispatch_import symbol name"
        );
    }

    #[test]
    fn test_symbol_table_encoding() {
        let mut builder = ElfBuilder::new_arm32();

        let sym = Symbol::new("test_func")
            .with_value(0x1000)
            .with_size(64)
            .with_binding(SymbolBinding::Global)
            .with_type(SymbolType::Func)
            .with_section(1);

        builder.add_symbol(sym);

        let (_strtab, offsets) = builder.build_symbol_string_table();
        let symtab = builder.build_symbol_table(&offsets, &[0]);

        // Should have null symbol (16 bytes) + 1 symbol (16 bytes) = 32 bytes
        assert_eq!(symtab.len(), 32);

        // First symbol should be all zeros
        assert!(symtab[0..16].iter().all(|&b| b == 0));

        // Second symbol should have correct encoding
        // Check st_value (bytes 4-7 of second entry)
        // For ARM STT_FUNC symbols, bit 0 is set for Thumb interworking
        let value_bytes = &symtab[20..24];
        let value = u32::from_le_bytes([
            value_bytes[0],
            value_bytes[1],
            value_bytes[2],
            value_bytes[3],
        ]);
        assert_eq!(value, 0x1001); // 0x1000 | 1 (Thumb bit)

        // Check st_size (bytes 8-11 of second entry)
        let size_bytes = &symtab[24..28];
        let size = u32::from_le_bytes([size_bytes[0], size_bytes[1], size_bytes[2], size_bytes[3]]);
        assert_eq!(size, 64);

        // Check st_info (byte 12 of second entry)
        let info = symtab[28];
        let binding = info >> 4;
        let sym_type = info & 0xf;
        assert_eq!(binding, SymbolBinding::Global as u8);
        assert_eq!(sym_type, SymbolType::Func as u8);
    }

    /// #598: an A32 object (`with_thumb_funcs(false)`, cortex-r5 path) must
    /// NOT set the Thumb interworking bit on STT_FUNC symbols or `e_entry` —
    /// bit 0 on an A32 code address is wrong metadata (harnesses had to mask
    /// it). Non-func symbols never carried the bit; that stays true.
    #[test]
    fn test_a32_symbols_have_no_thumb_bit_598() {
        let mut builder = ElfBuilder::new_arm32().with_thumb_funcs(false);

        let func_sym = Symbol::new("a32_func")
            .with_value(0x1000)
            .with_size(64)
            .with_binding(SymbolBinding::Global)
            .with_type(SymbolType::Func)
            .with_section(1);
        builder.add_symbol(func_sym);

        let (_strtab, offsets) = builder.build_symbol_string_table();
        let symtab = builder.build_symbol_table(&offsets, &[0]);
        let value = u32::from_le_bytes(symtab[20..24].try_into().unwrap());
        assert_eq!(value, 0x1000, "A32 STT_FUNC st_value must keep bit 0 clear");

        // e_entry stays clear too (was `0 | 1` on the A32 relocatable path).
        let builder = ElfBuilder::new_arm32()
            .with_thumb_funcs(false)
            .with_entry(0x8000);
        assert_eq!(builder.entry, 0x8000, "A32 e_entry must keep bit 0 clear");

        // The default (Thumb) behavior is unchanged: bit 0 set on both.
        let builder = ElfBuilder::new_arm32().with_entry(0x8000);
        assert_eq!(builder.entry, 0x8001, "Thumb e_entry keeps the bit");
    }

    /// Minimal ELF32 section-header reader for the tests below:
    /// (sh_type, sh_offset, sh_size, sh_link, sh_info) per section.
    fn read_section_headers(elf: &[u8]) -> Vec<(u32, u32, u32, u32, u32)> {
        let e_shoff = u32::from_le_bytes(elf[32..36].try_into().unwrap()) as usize;
        let e_shnum = u16::from_le_bytes(elf[48..50].try_into().unwrap()) as usize;
        (0..e_shnum)
            .map(|i| {
                let base = e_shoff + i * 40;
                let f = |off: usize| {
                    u32::from_le_bytes(elf[base + off..base + off + 4].try_into().unwrap())
                };
                (f(4), f(16), f(20), f(24), f(28))
            })
            .collect()
    }

    /// Read symtab entries as (st_value, st_info, st_shndx).
    fn read_symtab(elf: &[u8]) -> (Vec<(u32, u8, u16)>, u32) {
        let headers = read_section_headers(elf);
        let &(_, off, size, _, sh_info) = headers
            .iter()
            .find(|h| h.0 == SectionType::SymTab as u32)
            .expect("symtab present");
        let syms = (0..size as usize / 16)
            .map(|i| {
                let base = off as usize + i * 16;
                (
                    u32::from_le_bytes(elf[base + 4..base + 8].try_into().unwrap()),
                    elf[base + 12],
                    u16::from_le_bytes(elf[base + 14..base + 16].try_into().unwrap()),
                )
            })
            .collect();
        (syms, sh_info)
    }

    /// #656: local symbols must be emitted BEFORE globals (stable within each
    /// class), `.symtab` `sh_info` must be the first-non-local index, and every
    /// relocation's symbol index must be rewritten through the permutation.
    #[test]
    fn test_locals_sorted_first_sh_info_and_reloc_reindex_656() {
        let mut builder = ElfBuilder::new_arm32()
            .with_entry(0)
            .with_type(ElfType::Rel);
        let text = Section::new(".text", SectionType::ProgBits)
            .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
            .with_align(4)
            .with_data(vec![0u8; 16]);
        builder.add_section(text);

        // Added out of ELF order: global export first, then a LOCAL internal
        // helper, then a global undefined external.
        builder.add_symbol(
            Symbol::new("exported")
                .with_value(0)
                .with_binding(SymbolBinding::Global)
                .with_type(SymbolType::Func)
                .with_section(4),
        ); // pre-build index 1
        builder.add_symbol(
            Symbol::new("func_2")
                .with_value(8)
                .with_binding(SymbolBinding::Local)
                .with_type(SymbolType::Func)
                .with_section(4),
        ); // pre-build index 2
        let undef_idx = builder.add_undefined_symbol("external"); // pre-build index 3
        assert_eq!(undef_idx, 3);

        // BL at offset 0 → the LOCAL func_2 (pre-build index 2);
        // BL at offset 4 → the undefined external (pre-build index 3).
        builder.add_relocation(Relocation {
            offset: 0,
            symbol_index: 2,
            reloc_type: ArmRelocationType::ThmCall,
        });
        builder.add_relocation(Relocation {
            offset: 4,
            symbol_index: undef_idx,
            reloc_type: ArmRelocationType::ThmCall,
        });

        let elf = builder.build().unwrap();
        let (syms, sh_info) = read_symtab(&elf);

        // Order: null, func_2 (LOCAL), exported (GLOBAL), external (GLOBAL undef).
        assert_eq!(syms.len(), 4);
        assert_eq!(syms[0], (0, 0, 0), "null symbol first");
        let bind = |info: u8| info >> 4;
        assert_eq!(bind(syms[1].1), SymbolBinding::Local as u8, "local first");
        assert_eq!(syms[1].0, 8 | 1, "func_2 st_value (thumb bit)");
        assert_eq!(bind(syms[2].1), SymbolBinding::Global as u8);
        assert_eq!(syms[2].0, 1, "exported st_value 0 | thumb bit");
        assert_eq!(bind(syms[3].1), SymbolBinding::Global as u8);
        assert_eq!(syms[3].2, 0, "external is SHN_UNDEF");
        assert_eq!(sh_info, 2, "sh_info = index of first non-local symbol");

        // Relocations rewritten: func_2 is now index 1, external index 3.
        let headers = read_section_headers(&elf);
        let &(_, rel_off, rel_size, _, rel_info) = headers
            .iter()
            .find(|h| h.0 == SectionType::Rel as u32)
            .expect(".rel.text present");
        assert_eq!(rel_info, 4, ".rel.text still targets .text");
        assert_eq!(rel_size, 16);
        let r_info = |i: usize| {
            u32::from_le_bytes(
                elf[rel_off as usize + i * 8 + 4..rel_off as usize + i * 8 + 8]
                    .try_into()
                    .unwrap(),
            )
        };
        assert_eq!(r_info(0) >> 8, 1, "BL func_2 reloc remapped to new index 1");
        assert_eq!(r_info(0) & 0xff, ArmRelocationType::ThmCall as u32);
        assert_eq!(r_info(1) >> 8, 3, "BL external reloc keeps index 3");
    }

    /// #656 freeze guard: with zero LOCAL symbols the permutation is the
    /// identity and `sh_info` stays 1 — the pre-#656 layout, byte-identical.
    #[test]
    fn test_all_global_symtab_unchanged_sh_info_1_656() {
        let mut builder = ElfBuilder::new_arm32()
            .with_entry(0)
            .with_type(ElfType::Rel);
        builder.add_section(
            Section::new(".text", SectionType::ProgBits)
                .with_flags(SectionFlags::ALLOC | SectionFlags::EXEC)
                .with_data(vec![0u8; 8]),
        );
        for (name, val) in [("a", 0u32), ("b", 4u32)] {
            builder.add_symbol(
                Symbol::new(name)
                    .with_value(val)
                    .with_binding(SymbolBinding::Global)
                    .with_type(SymbolType::Func)
                    .with_section(4),
            );
        }
        let elf = builder.build().unwrap();
        let (syms, sh_info) = read_symtab(&elf);
        assert_eq!(sh_info, 1, "no locals ⇒ sh_info stays 1 (pre-#656 layout)");
        assert_eq!(syms[1].0, 1, "a first (insertion order preserved)");
        assert_eq!(syms[2].0, 5, "b second");
    }

    /// #637: `.ARM.attributes` blob structure — format version 'A', "aeabi"
    /// vendor subsection, Tag_File subsubsection with the uleb tag pairs, and
    /// zero-valued tags omitted (spec default).
    #[test]
    fn test_arm_attributes_section_bytes_637() {
        // Cortex-M3: v7, profile M, no A32, Thumb-2.
        let sec = arm_attributes_section(aeabi::CPU_ARCH_V7, aeabi::PROFILE_M, 0, 2);
        assert_eq!(sec.name, ".ARM.attributes");
        assert_eq!(sec.section_type, SectionType::ArmAttributes);
        let d = &sec.data;
        assert_eq!(d[0], b'A', "format version");
        let vendor_len = u32::from_le_bytes(d[1..5].try_into().unwrap()) as usize;
        assert_eq!(vendor_len, d.len() - 1, "vendor subsection length");
        assert_eq!(&d[5..11], b"aeabi\0");
        assert_eq!(d[11], 1, "Tag_File");
        let file_len = u32::from_le_bytes(d[12..16].try_into().unwrap()) as usize;
        assert_eq!(file_len, d.len() - 11, "Tag_File length");
        // Attribute pairs (all values < 128 ⇒ one uleb byte each).
        let attrs = &d[16..];
        assert_eq!(
            attrs,
            &[
                6, 10, // Tag_CPU_arch = v7
                7, b'M', // Tag_CPU_arch_profile = M
                9, 2, // Tag_THUMB_ISA_use = Thumb-2 (Tag_ARM_ISA_use=0 omitted)
            ],
        );

        // Cortex-R5: v7, profile R, A32 permitted, Thumb-2 permitted.
        let sec = arm_attributes_section(aeabi::CPU_ARCH_V7, aeabi::PROFILE_R, 1, 2);
        assert_eq!(&sec.data[16..], &[6, 10, 7, b'R', 8, 1, 9, 2]);
    }
}
