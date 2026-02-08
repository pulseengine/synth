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
    /// Sections
    sections: Vec<Section>,
    /// Symbols
    symbols: Vec<Symbol>,
    /// Program headers (segments)
    program_headers: Vec<ProgramHeader>,
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
            sections: Vec::new(),
            symbols: Vec::new(),
            program_headers: Vec::new(),
        }
    }

    /// Set entry point
    pub fn with_entry(mut self, entry: u32) -> Self {
        self.entry = entry;
        self
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

    /// Add a program header (segment)
    pub fn add_program_header(&mut self, ph: ProgramHeader) {
        self.program_headers.push(ph);
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
        let (shstrtab_data, section_name_offsets) = self.build_section_string_table();

        // Build symbol string table
        let (strtab_data, symbol_name_offsets) = self.build_symbol_string_table();

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

        // Section 3: .symtab (symbol table)
        let symtab_offset = current_offset;
        let symtab_data = self.build_symbol_table(&symbol_name_offsets);
        current_offset += symtab_data.len();

        // Section header table comes at the end
        let sh_offset = current_offset;

        // Now write all the data
        output.extend_from_slice(&shstrtab_data);
        output.extend_from_slice(&strtab_data);

        for section in &self.sections {
            output.extend_from_slice(&section.data);
        }

        output.extend_from_slice(&symtab_data);

        // Write section headers
        let section_headers = self.build_section_headers(
            &section_name_offsets,
            shstrtab_offset,
            &shstrtab_data,
            strtab_offset,
            &strtab_data,
            symtab_offset,
            &symtab_data,
            &section_offsets,
        );
        output.extend_from_slice(&section_headers);

        // Write program headers (right after ELF header)
        for (i, ph) in self.program_headers.iter().enumerate() {
            let ph_offset = header_size + i * ph_entry_size;
            self.write_program_header(&mut output[ph_offset..ph_offset + ph_entry_size], ph);
        }

        // Now write the actual ELF header at the beginning
        let num_sections = 4 + self.sections.len(); // null + shstrtab + strtab + symtab + user sections
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

        // Flags (little-endian u32) - ARM EABI version 5
        output[cursor..cursor + 4].copy_from_slice(&0x05000000u32.to_le_bytes());
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

    /// Build section name string table
    fn build_section_string_table(&self) -> (Vec<u8>, Vec<usize>) {
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

        (strtab, offsets)
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

    /// Build symbol table
    fn build_symbol_table(&self, name_offsets: &[usize]) -> Vec<u8> {
        let mut symtab = Vec::new();

        // First entry is always null symbol
        symtab.extend_from_slice(&[0u8; 16]); // 16 bytes per symbol in ELF32

        // User symbols
        for (i, symbol) in self.symbols.iter().enumerate() {
            let name_offset = if i < name_offsets.len() {
                name_offsets[i] as u32
            } else {
                0
            };

            // st_name (4 bytes)
            symtab.extend_from_slice(&name_offset.to_le_bytes());

            // st_value (4 bytes)
            symtab.extend_from_slice(&symbol.value.to_le_bytes());

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

    /// Build section headers
    fn build_section_headers(
        &self,
        section_name_offsets: &[usize],
        shstrtab_offset: usize,
        shstrtab_data: &[u8],
        strtab_offset: usize,
        strtab_data: &[u8],
        symtab_offset: usize,
        symtab_data: &[u8],
        section_offsets: &[usize],
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
            1,
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

        headers
    }

    /// Write a single section header
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

        // Validate entry point is set correctly
        let entry_bytes = &elf[24..28];
        let entry = u32::from_le_bytes([
            entry_bytes[0],
            entry_bytes[1],
            entry_bytes[2],
            entry_bytes[3],
        ]);
        assert_eq!(entry, 0x8000);

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

        let (strtab, offsets) = builder.build_section_string_table();

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
        let symtab = builder.build_symbol_table(&offsets);

        // Should have null symbol (16 bytes) + 1 symbol (16 bytes) = 32 bytes
        assert_eq!(symtab.len(), 32);

        // First symbol should be all zeros
        assert!(symtab[0..16].iter().all(|&b| b == 0));

        // Second symbol should have correct encoding
        // Check st_value (bytes 4-7 of second entry)
        let value_bytes = &symtab[20..24];
        let value = u32::from_le_bytes([
            value_bytes[0],
            value_bytes[1],
            value_bytes[2],
            value_bytes[3],
        ]);
        assert_eq!(value, 0x1000);

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
}
