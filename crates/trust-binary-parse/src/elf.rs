// trust-binary-parse: ELF binary format parser
//
// Zero-copy: Elf32<'a> and Elf64<'a> borrow from the input byte slice. Section names,
// symbol names, and string table entries are all references into the
// original buffer.
//
// Reference: ELF specification (System V ABI), gABI
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::dwarf::DwarfInfo;
use crate::elf_relocation::{
    self, Elf64Dyn, Elf64Rel, Elf64Rela, ResolvedRelocation, SHT_DYNAMIC, SHT_REL, SHT_RELA,
};
use crate::error::{DwarfError, ParseError};
use crate::read::{Cursor, read_strtab_entry};

// --- ELF magic and identification constants ---

/// ELF magic bytes: 0x7f 'E' 'L' 'F'
const ELF_MAGIC: [u8; 4] = [0x7f, b'E', b'L', b'F'];

/// EI_CLASS values
const ELFCLASS32: u8 = 1;
const ELFCLASS64: u8 = 2;

/// EI_DATA values
const ELFDATA2LSB: u8 = 1;
const ELFDATA2MSB: u8 = 2;

/// Section header types (SHT_*)
const SHT_SYMTAB: u32 = 2;
#[cfg(test)]
const SHT_STRTAB: u32 = 3;
const SHT_DYNSYM: u32 = 11;

/// Size of an ELF64 file header in bytes.
const ELF64_EHDR_SIZE: usize = 64;
/// Size of an ELF64 section header entry.
const ELF64_SHDR_SIZE: usize = 64;
/// Size of an ELF64 program header entry.
const ELF64_PHDR_SIZE: usize = 56;
/// Size of an ELF64 symbol table entry.
const ELF64_SYM_SIZE: usize = 24;
/// Size of an ELF32 file header in bytes.
const ELF32_EHDR_SIZE: usize = 52;
/// Size of an ELF32 section header entry.
const ELF32_SHDR_SIZE: usize = 40;
/// Size of an ELF32 program header entry.
const ELF32_PHDR_SIZE: usize = 32;
/// Size of an ELF32 symbol table entry.
const ELF32_SYM_SIZE: usize = 16;

// --- Parsed structures ---

/// Parsed ELF64 file header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Elf64Header {
    /// Object file type (ET_EXEC, ET_DYN, etc.).
    pub e_type: u16,
    /// Architecture (EM_X86_64, EM_AARCH64, etc.).
    pub e_machine: u16,
    /// Object file version.
    pub e_version: u32,
    /// Entry point virtual address.
    pub e_entry: u64,
    /// Program header table file offset.
    pub e_phoff: u64,
    /// Section header table file offset.
    pub e_shoff: u64,
    /// Processor-specific flags.
    pub e_flags: u32,
    /// ELF header size.
    pub e_ehsize: u16,
    /// Program header table entry size.
    pub e_phentsize: u16,
    /// Program header table entry count.
    pub e_phnum: u16,
    /// Section header table entry size.
    pub e_shentsize: u16,
    /// Section header table entry count.
    pub e_shnum: u16,
    /// Section name string table section index.
    pub e_shstrndx: u16,
}

/// Parsed ELF64 section header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Elf64SectionHeader {
    /// Section name (index into section header string table).
    pub sh_name: u32,
    /// Section type (SHT_*).
    pub sh_type: u32,
    /// Section flags (SHF_*).
    pub sh_flags: u64,
    /// Virtual address in memory.
    pub sh_addr: u64,
    /// Offset in file.
    pub sh_offset: u64,
    /// Size in bytes.
    pub sh_size: u64,
    /// Link to another section.
    pub sh_link: u32,
    /// Additional section information.
    pub sh_info: u32,
    /// Address alignment.
    pub sh_addralign: u64,
    /// Entry size if section holds fixed-size entries.
    pub sh_entsize: u64,
}

/// Parsed ELF64 program header (segment).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Elf64ProgramHeader {
    /// Segment type (PT_LOAD, PT_DYNAMIC, etc.).
    pub p_type: u32,
    /// Segment flags (PF_R, PF_W, PF_X).
    pub p_flags: u32,
    /// Offset in file.
    pub p_offset: u64,
    /// Virtual address in memory.
    pub p_vaddr: u64,
    /// Physical address (usually same as vaddr).
    pub p_paddr: u64,
    /// Size in file.
    pub p_filesz: u64,
    /// Size in memory.
    pub p_memsz: u64,
    /// Alignment.
    pub p_align: u64,
}

/// Parsed ELF64 symbol table entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Elf64Symbol<'a> {
    /// Symbol name from the string table.
    pub name: &'a str,
    /// Symbol name index (into linked string table).
    pub st_name: u32,
    /// Symbol type and binding (use helpers below).
    pub st_info: u8,
    /// Symbol visibility.
    pub st_other: u8,
    /// Section index this symbol is defined in.
    pub st_shndx: u16,
    /// Symbol value (address).
    pub st_value: u64,
    /// Symbol size.
    pub st_size: u64,
}

impl Elf64Symbol<'_> {
    /// Symbol binding (STB_LOCAL, STB_GLOBAL, STB_WEAK).
    #[must_use]
    pub fn binding(&self) -> u8 {
        self.st_info >> 4
    }

    /// Symbol type (STT_NOTYPE, STT_OBJECT, STT_FUNC, etc.).
    #[must_use]
    pub fn sym_type(&self) -> u8 {
        self.st_info & 0xf
    }

    /// Symbol visibility (STV_DEFAULT, STV_HIDDEN, etc.).
    #[must_use]
    pub fn visibility(&self) -> u8 {
        self.st_other & 0x3
    }

    /// Whether this is a function symbol.
    #[must_use]
    pub fn is_function(&self) -> bool {
        self.sym_type() == 2 // STT_FUNC
    }

    /// Whether this is an object (data) symbol.
    #[must_use]
    pub fn is_object(&self) -> bool {
        self.sym_type() == 1 // STT_OBJECT
    }

    /// Whether this symbol is globally visible.
    #[must_use]
    pub fn is_global(&self) -> bool {
        self.binding() == 1 // STB_GLOBAL
    }

    /// Whether this symbol is local.
    #[must_use]
    pub fn is_local(&self) -> bool {
        self.binding() == 0 // STB_LOCAL
    }

    /// Whether this symbol is weak.
    #[must_use]
    pub fn is_weak(&self) -> bool {
        self.binding() == 2 // STB_WEAK
    }
}

/// Parsed ELF32 file header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Elf32Header {
    /// Object file type (ET_EXEC, ET_DYN, etc.).
    pub e_type: u16,
    /// Architecture (EM_386, EM_ARM, etc.).
    pub e_machine: u16,
    /// Object file version.
    pub e_version: u32,
    /// Entry point virtual address.
    pub e_entry: u32,
    /// Program header table file offset.
    pub e_phoff: u32,
    /// Section header table file offset.
    pub e_shoff: u32,
    /// Processor-specific flags.
    pub e_flags: u32,
    /// ELF header size.
    pub e_ehsize: u16,
    /// Program header table entry size.
    pub e_phentsize: u16,
    /// Program header table entry count.
    pub e_phnum: u16,
    /// Section header table entry size.
    pub e_shentsize: u16,
    /// Section header table entry count.
    pub e_shnum: u16,
    /// Section name string table section index.
    pub e_shstrndx: u16,
}

/// Parsed ELF32 section header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Elf32SectionHeader {
    /// Section name (index into section header string table).
    pub sh_name: u32,
    /// Section type (SHT_*).
    pub sh_type: u32,
    /// Section flags (SHF_*).
    pub sh_flags: u32,
    /// Virtual address in memory.
    pub sh_addr: u32,
    /// Offset in file.
    pub sh_offset: u32,
    /// Size in bytes.
    pub sh_size: u32,
    /// Link to another section.
    pub sh_link: u32,
    /// Additional section information.
    pub sh_info: u32,
    /// Address alignment.
    pub sh_addralign: u32,
    /// Entry size if section holds fixed-size entries.
    pub sh_entsize: u32,
}

/// Parsed ELF32 program header (segment).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Elf32ProgramHeader {
    /// Segment type (PT_LOAD, PT_DYNAMIC, etc.).
    pub p_type: u32,
    /// Offset in file.
    pub p_offset: u32,
    /// Virtual address in memory.
    pub p_vaddr: u32,
    /// Physical address (usually same as vaddr).
    pub p_paddr: u32,
    /// Size in file.
    pub p_filesz: u32,
    /// Size in memory.
    pub p_memsz: u32,
    /// Segment flags (PF_R, PF_W, PF_X).
    pub p_flags: u32,
    /// Alignment.
    pub p_align: u32,
}

/// Parsed ELF32 symbol table entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Elf32Symbol<'a> {
    /// Symbol name from the string table.
    pub name: &'a str,
    /// Symbol name index (into linked string table).
    pub st_name: u32,
    /// Symbol value (address).
    pub st_value: u32,
    /// Symbol size.
    pub st_size: u32,
    /// Symbol type and binding (use helpers below).
    pub st_info: u8,
    /// Symbol visibility.
    pub st_other: u8,
    /// Section index this symbol is defined in.
    pub st_shndx: u16,
}

impl Elf32Symbol<'_> {
    /// Symbol binding (STB_LOCAL, STB_GLOBAL, STB_WEAK).
    #[must_use]
    pub fn binding(&self) -> u8 {
        self.st_info >> 4
    }

    /// Symbol type (STT_NOTYPE, STT_OBJECT, STT_FUNC, etc.).
    #[must_use]
    pub fn sym_type(&self) -> u8 {
        self.st_info & 0xf
    }

    /// Symbol visibility (STV_DEFAULT, STV_HIDDEN, etc.).
    #[must_use]
    pub fn visibility(&self) -> u8 {
        self.st_other & 0x3
    }

    /// Whether this is a function symbol.
    #[must_use]
    pub fn is_function(&self) -> bool {
        self.sym_type() == 2 // STT_FUNC
    }

    /// Whether this is an object (data) symbol.
    #[must_use]
    pub fn is_object(&self) -> bool {
        self.sym_type() == 1 // STT_OBJECT
    }

    /// Whether this symbol is globally visible.
    #[must_use]
    pub fn is_global(&self) -> bool {
        self.binding() == 1 // STB_GLOBAL
    }

    /// Whether this symbol is local.
    #[must_use]
    pub fn is_local(&self) -> bool {
        self.binding() == 0 // STB_LOCAL
    }

    /// Whether this symbol is weak.
    #[must_use]
    pub fn is_weak(&self) -> bool {
        self.binding() == 2 // STB_WEAK
    }
}

/// A parsed ELF64 binary.
///
/// Borrows from the input byte slice for zero-copy access to section data,
/// symbol names, and string table entries.
#[derive(Debug)]
pub struct Elf64<'a> {
    /// The raw file data.
    data: &'a [u8],
    /// Whether bytes need swapping (big-endian ELF on LE host).
    swap: bool,
    /// Parsed ELF header.
    pub header: Elf64Header,
    /// Parsed section headers.
    pub sections: Vec<Elf64SectionHeader>,
    /// Parsed program headers (segments).
    pub segments: Vec<Elf64ProgramHeader>,
}

/// A parsed ELF32 binary.
///
/// Borrows from the input byte slice for zero-copy access to section data,
/// symbol names, and string table entries.
#[derive(Debug)]
pub struct Elf32<'a> {
    /// The raw file data.
    data: &'a [u8],
    /// Whether bytes need swapping (big-endian ELF on LE host).
    swap: bool,
    /// Parsed ELF header.
    pub header: Elf32Header,
    /// Parsed section headers.
    pub sections: Vec<Elf32SectionHeader>,
    /// Parsed program headers (segments).
    pub segments: Vec<Elf32ProgramHeader>,
}

impl<'a> Elf64<'a> {
    /// Parse an ELF64 binary from raw bytes.
    ///
    /// Validates the ELF magic, parses the file header, section headers,
    /// and program headers. Symbol tables are parsed on demand via
    /// [`Elf64::symbols`] and [`Elf64::dynamic_symbols`].
    pub fn parse(data: &'a [u8]) -> Result<Self, ParseError> {
        if data.len() < ELF64_EHDR_SIZE {
            return Err(ParseError::UnexpectedEof(0));
        }

        // Validate magic
        if data[0..4] != ELF_MAGIC {
            let magic = u32::from_be_bytes([data[0], data[1], data[2], data[3]]);
            return Err(ParseError::InvalidMagic(magic));
        }

        // Validate ELF64
        if data[4] != ELFCLASS64 {
            return Err(ParseError::UnsupportedFormat(format!(
                "ELF class {} (only ELF64 supported)",
                data[4]
            )));
        }

        // Determine endianness
        let swap = match data[5] {
            ELFDATA2LSB => false, // native LE on LE host
            ELFDATA2MSB => true,  // need swap on LE host
            other => {
                return Err(ParseError::UnsupportedFormat(format!("ELF data encoding {other}")));
            }
        };

        let mut cursor = Cursor::new(data, 16, swap); // skip e_ident[16]

        let header = Elf64Header {
            e_type: cursor.read_u16()?,
            e_machine: cursor.read_u16()?,
            e_version: cursor.read_u32()?,
            e_entry: cursor.read_u64()?,
            e_phoff: cursor.read_u64()?,
            e_shoff: cursor.read_u64()?,
            e_flags: cursor.read_u32()?,
            e_ehsize: cursor.read_u16()?,
            e_phentsize: cursor.read_u16()?,
            e_phnum: cursor.read_u16()?,
            e_shentsize: cursor.read_u16()?,
            e_shnum: cursor.read_u16()?,
            e_shstrndx: cursor.read_u16()?,
        };

        // Parse program headers
        let segments = parse_program_headers(data, &header, swap)?;

        // Parse section headers
        let sections = parse_section_headers(data, &header, swap)?;

        Ok(Self { data, swap, header, sections, segments })
    }

    /// Check if the data starts with the ELF magic bytes.
    #[must_use]
    pub fn is_elf(data: &[u8]) -> bool {
        data.len() >= 4 && data[0..4] == ELF_MAGIC
    }

    /// The raw file data.
    #[must_use]
    pub fn data(&self) -> &'a [u8] {
        self.data
    }

    /// Look up a section name from the section header string table.
    pub fn section_name(&self, sh: &Elf64SectionHeader) -> Result<&'a str, ParseError> {
        let shstrndx = self.header.e_shstrndx as usize;
        if shstrndx >= self.sections.len() {
            return Err(ParseError::SectionNotFound(".shstrtab (invalid e_shstrndx)".into()));
        }
        let strtab_sh = &self.sections[shstrndx];
        let strtab = self.section_data(strtab_sh)?;
        read_strtab_entry(strtab, sh.sh_name)
    }

    /// Get the raw data for a section.
    pub fn section_data(&self, sh: &Elf64SectionHeader) -> Result<&'a [u8], ParseError> {
        let end = sh.sh_offset.checked_add(sh.sh_size).ok_or(ParseError::DataOutOfBounds {
            offset: sh.sh_offset,
            end: u64::MAX,
            file_size: self.data.len(),
        })?;
        if end > self.data.len() as u64 {
            return Err(ParseError::DataOutOfBounds {
                offset: sh.sh_offset,
                end,
                file_size: self.data.len(),
            });
        }
        let start = usize::try_from(sh.sh_offset).map_err(|_| ParseError::DataOutOfBounds {
            offset: sh.sh_offset,
            end,
            file_size: self.data.len(),
        })?;
        let end = usize::try_from(end).map_err(|_| ParseError::DataOutOfBounds {
            offset: sh.sh_offset,
            end,
            file_size: self.data.len(),
        })?;
        Ok(&self.data[start..end])
    }

    /// Find a section by name.
    #[must_use]
    pub fn find_section(&self, name: &str) -> Option<&Elf64SectionHeader> {
        self.sections.iter().find(|sh| self.section_name(sh).map(|n| n == name).unwrap_or(false))
    }

    /// Parse symbols from the .symtab section.
    pub fn symbols(&self) -> Result<Vec<Elf64Symbol<'a>>, ParseError> {
        self.parse_symbol_table(SHT_SYMTAB)
    }

    /// Parse symbols from the .dynsym section.
    pub fn dynamic_symbols(&self) -> Result<Vec<Elf64Symbol<'a>>, ParseError> {
        self.parse_symbol_table(SHT_DYNSYM)
    }

    /// Parse a symbol table of the given type (SHT_SYMTAB or SHT_DYNSYM).
    fn parse_symbol_table(&self, sh_type: u32) -> Result<Vec<Elf64Symbol<'a>>, ParseError> {
        let symtab_sh = match self.sections.iter().find(|sh| sh.sh_type == sh_type) {
            Some(sh) => sh,
            None => return Ok(Vec::new()),
        };

        // sh_link points to the associated string table section
        let strtab_idx = symtab_sh.sh_link as usize;
        if strtab_idx >= self.sections.len() {
            return Err(ParseError::SectionNotFound(
                "symbol string table (invalid sh_link)".into(),
            ));
        }
        let strtab_sh = &self.sections[strtab_idx];
        let strtab = self.section_data(strtab_sh)?;

        let sym_data = self.section_data(symtab_sh)?;
        let entry_size =
            if symtab_sh.sh_entsize > 0 { symtab_sh.sh_entsize as usize } else { ELF64_SYM_SIZE };

        if entry_size < ELF64_SYM_SIZE {
            return Err(ParseError::InvalidHeader(format!(
                "symbol entry size {entry_size} < minimum {ELF64_SYM_SIZE}"
            )));
        }

        let count = sym_data.len().checked_div(entry_size).unwrap_or(0);

        let mut symbols = Vec::with_capacity(count);
        let mut cursor = Cursor::new(sym_data, 0, self.swap);

        for _ in 0..count {
            let start = cursor.offset();
            let st_name = cursor.read_u32()?;
            let st_info = cursor.read_u8()?;
            let st_other = cursor.read_u8()?;
            let st_shndx = cursor.read_u16()?;
            let st_value = cursor.read_u64()?;
            let st_size = cursor.read_u64()?;

            let name = read_strtab_entry(strtab, st_name)?;

            // Skip padding if entry_size > ELF64_SYM_SIZE
            let consumed = cursor.offset() - start;
            if consumed < entry_size {
                cursor.skip(entry_size - consumed)?;
            }

            symbols.push(Elf64Symbol {
                name,
                st_name,
                st_info,
                st_other,
                st_shndx,
                st_value,
                st_size,
            });
        }

        Ok(symbols)
    }

    /// Get the entry point address.
    #[must_use]
    pub fn entry_point(&self) -> u64 {
        self.header.e_entry
    }

    /// Get executable PT_LOAD segments (those with PF_X flag set).
    #[must_use]
    pub fn executable_segments(&self) -> Vec<&Elf64ProgramHeader> {
        // PT_LOAD = 1, PF_X = 0x1
        self.segments.iter().filter(|seg| seg.p_type == 1 && (seg.p_flags & 0x1) != 0).collect()
    }

    /// Find the first executable PT_LOAD segment (PF_X flag set).
    ///
    /// This is the primary code segment in most ELF binaries. Returns `None`
    /// if the binary has no executable segments.
    // Trust: convenience API for reverse compilation pipeline
    #[must_use]
    pub fn executable_segment(&self) -> Option<&Elf64ProgramHeader> {
        // PT_LOAD = 1, PF_X = 0x1
        self.segments.iter().find(|seg| seg.p_type == 1 && (seg.p_flags & 0x1) != 0)
    }

    /// Find the `.text` section header, if present.
    #[must_use]
    pub fn text_section(&self) -> Option<&Elf64SectionHeader> {
        self.find_section(".text")
    }

    /// Extract DWARF debug information from this ELF binary.
    ///
    /// Locates `.debug_info`, `.debug_abbrev`, `.debug_str`, and optionally
    /// `.debug_line` sections, then delegates to [`DwarfInfo::parse`].
    /// Returns `Ok(None)` if the required DWARF sections are not present.
    // Trust: convenience API for reverse compilation pipeline
    pub fn dwarf_info(&self) -> Result<Option<DwarfInfo<'a>>, DwarfError> {
        let debug_info = match self.find_section(".debug_info") {
            Some(sh) => self.section_data(sh).map_err(|_| DwarfError::InvalidUnit)?,
            None => return Ok(None),
        };
        let debug_abbrev = match self.find_section(".debug_abbrev") {
            Some(sh) => self.section_data(sh).map_err(|_| DwarfError::InvalidUnit)?,
            None => return Ok(None),
        };
        let debug_str = match self.find_section(".debug_str") {
            Some(sh) => self.section_data(sh).map_err(|_| DwarfError::InvalidUnit)?,
            None => &[],
        };
        let debug_line = self.find_section(".debug_line").and_then(|sh| self.section_data(sh).ok());

        DwarfInfo::parse(debug_info, debug_abbrev, debug_str, debug_line).map(Some)
    }

    // --- Relocation and dynamic section methods (Trust: #559) ---

    /// Parse all SHT_RELA relocation sections.
    ///
    /// Returns all Elf64_Rela entries across all .rela.* sections.
    pub fn relocations(&self) -> Result<Vec<Elf64Rela>, ParseError> {
        let mut all = Vec::new();
        for sh in &self.sections {
            if sh.sh_type == SHT_RELA {
                let data = self.section_data(sh)?;
                let entries = elf_relocation::parse_rela_entries(data, self.swap)?;
                all.extend(entries);
            }
        }
        Ok(all)
    }

    /// Parse all SHT_REL relocation sections.
    ///
    /// Returns all Elf64_Rel entries across all .rel.* sections.
    pub fn rel_entries(&self) -> Result<Vec<Elf64Rel>, ParseError> {
        let mut all = Vec::new();
        for sh in &self.sections {
            if sh.sh_type == SHT_REL {
                let data = self.section_data(sh)?;
                let entries = elf_relocation::parse_rel_entries(data, self.swap)?;
                all.extend(entries);
            }
        }
        Ok(all)
    }

    /// Parse the SHT_DYNAMIC section.
    ///
    /// Returns dynamic entries; empty if no .dynamic section exists.
    pub fn dynamic_entries(&self) -> Result<Vec<Elf64Dyn>, ParseError> {
        let sh = match self.sections.iter().find(|s| s.sh_type == SHT_DYNAMIC) {
            Some(s) => s,
            None => return Ok(Vec::new()),
        };
        let data = self.section_data(sh)?;
        elf_relocation::parse_dynamic_entries(data, self.swap)
    }

    /// Extract the names of needed shared libraries from the dynamic section.
    ///
    /// Reads DT_NEEDED entries and resolves them against the dynamic string table
    /// (the section at the address given by DT_STRTAB).
    pub fn needed_libraries(&self) -> Result<Vec<&'a str>, ParseError> {
        let dyn_entries = self.dynamic_entries()?;
        if dyn_entries.is_empty() {
            return Ok(Vec::new());
        }

        // Find DT_STRTAB address
        let strtab_addr = match dyn_entries.iter().find(|d| d.d_tag == elf_relocation::DT_STRTAB) {
            Some(d) => d.d_val,
            None => return Ok(Vec::new()),
        };

        // Find the section whose sh_addr matches DT_STRTAB
        let strtab_sh = match self.sections.iter().find(|s| s.sh_addr == strtab_addr) {
            Some(s) => s,
            None => return Ok(Vec::new()),
        };
        let strtab = self.section_data(strtab_sh)?;

        // Collect DT_NEEDED entries
        let mut libs = Vec::new();
        for entry in &dyn_entries {
            if entry.d_tag == elf_relocation::DT_NEEDED {
                let name = read_strtab_entry(strtab, entry.d_val as u32)?;
                libs.push(name);
            }
        }
        Ok(libs)
    }

    /// Parse PLT relocation entries from the .rela.plt section.
    ///
    /// Returns entries from specifically the .rela.plt section (not all SHT_RELA sections).
    pub fn plt_relocations(&self) -> Result<Vec<Elf64Rela>, ParseError> {
        let sh = match self.find_section(".rela.plt") {
            Some(s) => s.clone(),
            None => return Ok(Vec::new()),
        };
        let data = self.section_data(&sh)?;
        elf_relocation::parse_rela_entries(data, self.swap)
    }

    /// Resolve relocation entries against the dynamic symbol table.
    ///
    /// For each SHT_RELA entry, looks up the referenced symbol in the section
    /// linked via sh_link and returns a resolved relocation with the symbol name.
    pub fn resolve_relocations(&self) -> Result<Vec<ResolvedRelocation>, ParseError> {
        let mut resolved = Vec::new();

        for sh in &self.sections {
            if sh.sh_type != SHT_RELA {
                continue;
            }

            let data = self.section_data(sh)?;
            let entries = elf_relocation::parse_rela_entries(data, self.swap)?;

            // sh_link points to the associated symbol table
            let symtab_idx = sh.sh_link as usize;
            if symtab_idx >= self.sections.len() {
                continue;
            }
            let symtab_sh = &self.sections[symtab_idx];

            // The symbol table's sh_link points to its string table
            let strtab_idx = symtab_sh.sh_link as usize;
            if strtab_idx >= self.sections.len() {
                continue;
            }
            let strtab_sh = &self.sections[strtab_idx];
            let strtab = self.section_data(strtab_sh)?;
            let sym_data = self.section_data(symtab_sh)?;

            let sym_entsize = if symtab_sh.sh_entsize > 0 {
                symtab_sh.sh_entsize as usize
            } else {
                ELF64_SYM_SIZE
            };

            for rela in &entries {
                let sym_idx = rela.sym() as usize;
                let sym_off = sym_idx * sym_entsize;

                let sym_name = if sym_off + ELF64_SYM_SIZE <= sym_data.len() {
                    // Read st_name (first 4 bytes of symbol entry)
                    let mut cursor = Cursor::new(sym_data, sym_off, self.swap);
                    let st_name = cursor.read_u32()?;
                    read_strtab_entry(strtab, st_name).unwrap_or("").to_string()
                } else {
                    String::new()
                };

                resolved.push(ResolvedRelocation {
                    offset: rela.r_offset,
                    sym_name,
                    reloc_type: rela.reloc_type(),
                    addend: rela.r_addend,
                });
            }
        }

        Ok(resolved)
    }

    /// Get function symbols (STT_FUNC) with nonzero addresses and valid sections.
    ///
    /// Chains `.symtab` and `.dynsym`, filters for STT_FUNC, sorts by address,
    /// and deduplicates by `(name, st_value)`.
    // Trust: convenience API for reverse compilation pipeline
    pub fn function_symbols(&self) -> Result<Vec<Elf64Symbol<'a>>, ParseError> {
        let mut funcs: Vec<Elf64Symbol<'a>> = self
            .symbols()?
            .into_iter()
            .chain(self.dynamic_symbols()?)
            .filter(|s| s.is_function() && s.st_value != 0 && s.st_shndx != 0)
            .collect();

        // Sort by address for predictable ordering
        funcs.sort_by_key(|s| s.st_value);

        // Dedup by (name, address)
        funcs.dedup_by(|a, b| a.name == b.name && a.st_value == b.st_value);

        Ok(funcs)
    }
}

impl<'a> Elf32<'a> {
    /// Parse an ELF32 binary from raw bytes.
    ///
    /// Validates the ELF magic, parses the file header, section headers,
    /// and program headers. Symbol tables are parsed on demand via
    /// [`Elf32::symbols`] and [`Elf32::dynamic_symbols`].
    pub fn parse(data: &'a [u8]) -> Result<Self, ParseError> {
        if data.len() < ELF32_EHDR_SIZE {
            return Err(ParseError::UnexpectedEof(0));
        }

        // Validate magic
        if data[0..4] != ELF_MAGIC {
            let magic = u32::from_be_bytes([data[0], data[1], data[2], data[3]]);
            return Err(ParseError::InvalidMagic(magic));
        }

        // Validate ELF32
        if data[4] != ELFCLASS32 {
            return Err(ParseError::UnsupportedFormat(format!(
                "ELF class {} (only ELF32 supported)",
                data[4]
            )));
        }

        // Determine endianness
        let swap = match data[5] {
            ELFDATA2LSB => false, // native LE on LE host
            ELFDATA2MSB => true,  // need swap on LE host
            other => {
                return Err(ParseError::UnsupportedFormat(format!("ELF data encoding {other}")));
            }
        };

        let mut cursor = Cursor::new(data, 16, swap); // skip e_ident[16]

        let header = Elf32Header {
            e_type: cursor.read_u16()?,
            e_machine: cursor.read_u16()?,
            e_version: cursor.read_u32()?,
            e_entry: cursor.read_u32()?,
            e_phoff: cursor.read_u32()?,
            e_shoff: cursor.read_u32()?,
            e_flags: cursor.read_u32()?,
            e_ehsize: cursor.read_u16()?,
            e_phentsize: cursor.read_u16()?,
            e_phnum: cursor.read_u16()?,
            e_shentsize: cursor.read_u16()?,
            e_shnum: cursor.read_u16()?,
            e_shstrndx: cursor.read_u16()?,
        };

        // Parse program headers
        let segments = parse_elf32_program_headers(data, &header, swap)?;

        // Parse section headers
        let sections = parse_elf32_section_headers(data, &header, swap)?;

        Ok(Self { data, swap, header, sections, segments })
    }

    /// Check if the data starts with the ELF magic bytes.
    #[must_use]
    pub fn is_elf(data: &[u8]) -> bool {
        data.len() >= 4 && data[0..4] == ELF_MAGIC
    }

    /// The raw file data.
    #[must_use]
    pub fn data(&self) -> &'a [u8] {
        self.data
    }

    /// Look up a section name from the section header string table.
    pub fn section_name(&self, sh: &Elf32SectionHeader) -> Result<&'a str, ParseError> {
        let shstrndx = self.header.e_shstrndx as usize;
        if shstrndx >= self.sections.len() {
            return Err(ParseError::SectionNotFound(".shstrtab (invalid e_shstrndx)".into()));
        }
        let strtab_sh = &self.sections[shstrndx];
        let strtab = self.section_data(strtab_sh)?;
        read_strtab_entry(strtab, sh.sh_name)
    }

    /// Get the raw data for a section.
    pub fn section_data(&self, sh: &Elf32SectionHeader) -> Result<&'a [u8], ParseError> {
        let start = sh.sh_offset as usize;
        let size = sh.sh_size as usize;
        let end = start.checked_add(size).ok_or(ParseError::DataOutOfBounds {
            offset: u64::from(sh.sh_offset),
            end: u64::from(sh.sh_offset).saturating_add(u64::from(sh.sh_size)),
            file_size: self.data.len(),
        })?;
        if end > self.data.len() {
            return Err(ParseError::DataOutOfBounds {
                offset: u64::from(sh.sh_offset),
                end: end as u64,
                file_size: self.data.len(),
            });
        }
        Ok(&self.data[start..end])
    }

    /// Find a section by name.
    #[must_use]
    pub fn find_section(&self, name: &str) -> Option<&Elf32SectionHeader> {
        self.sections.iter().find(|sh| self.section_name(sh).map(|n| n == name).unwrap_or(false))
    }

    /// Parse symbols from the .symtab section.
    pub fn symbols(&self) -> Result<Vec<Elf32Symbol<'a>>, ParseError> {
        self.parse_symbol_table(SHT_SYMTAB)
    }

    /// Parse symbols from the .dynsym section.
    pub fn dynamic_symbols(&self) -> Result<Vec<Elf32Symbol<'a>>, ParseError> {
        self.parse_symbol_table(SHT_DYNSYM)
    }

    /// Parse a symbol table of the given type (SHT_SYMTAB or SHT_DYNSYM).
    fn parse_symbol_table(&self, sh_type: u32) -> Result<Vec<Elf32Symbol<'a>>, ParseError> {
        let symtab_sh = match self.sections.iter().find(|sh| sh.sh_type == sh_type) {
            Some(sh) => sh,
            None => return Ok(Vec::new()),
        };

        // sh_link points to the associated string table section
        let strtab_idx = symtab_sh.sh_link as usize;
        if strtab_idx >= self.sections.len() {
            return Err(ParseError::SectionNotFound(
                "symbol string table (invalid sh_link)".into(),
            ));
        }
        let strtab_sh = &self.sections[strtab_idx];
        let strtab = self.section_data(strtab_sh)?;

        let sym_data = self.section_data(symtab_sh)?;
        let entry_size =
            if symtab_sh.sh_entsize > 0 { symtab_sh.sh_entsize as usize } else { ELF32_SYM_SIZE };

        if entry_size < ELF32_SYM_SIZE {
            return Err(ParseError::InvalidHeader(format!(
                "symbol entry size {entry_size} < minimum {ELF32_SYM_SIZE}"
            )));
        }

        let count = sym_data.len().checked_div(entry_size).unwrap_or(0);

        let mut symbols = Vec::with_capacity(count);
        let mut cursor = Cursor::new(sym_data, 0, self.swap);

        for _ in 0..count {
            let start = cursor.offset();
            let st_name = cursor.read_u32()?;
            let st_value = cursor.read_u32()?;
            let st_size = cursor.read_u32()?;
            let st_info = cursor.read_u8()?;
            let st_other = cursor.read_u8()?;
            let st_shndx = cursor.read_u16()?;

            let name = read_strtab_entry(strtab, st_name)?;

            // Skip padding if entry_size > ELF32_SYM_SIZE
            let consumed = cursor.offset() - start;
            if consumed < entry_size {
                cursor.skip(entry_size - consumed)?;
            }

            symbols.push(Elf32Symbol {
                name,
                st_name,
                st_value,
                st_size,
                st_info,
                st_other,
                st_shndx,
            });
        }

        Ok(symbols)
    }

    /// Get the entry point address.
    #[must_use]
    pub fn entry_point(&self) -> u64 {
        u64::from(self.header.e_entry)
    }

    /// Get executable PT_LOAD segments (those with PF_X flag set).
    #[must_use]
    pub fn executable_segments(&self) -> Vec<&Elf32ProgramHeader> {
        // PT_LOAD = 1, PF_X = 0x1
        self.segments.iter().filter(|seg| seg.p_type == 1 && (seg.p_flags & 0x1) != 0).collect()
    }

    /// Find the first executable PT_LOAD segment (PF_X flag set).
    ///
    /// This is the primary code segment in most ELF binaries. Returns `None`
    /// if the binary has no executable segments.
    #[must_use]
    pub fn executable_segment(&self) -> Option<&Elf32ProgramHeader> {
        // PT_LOAD = 1, PF_X = 0x1
        self.segments.iter().find(|seg| seg.p_type == 1 && (seg.p_flags & 0x1) != 0)
    }

    /// Find the `.text` section header, if present.
    #[must_use]
    pub fn text_section(&self) -> Option<&Elf32SectionHeader> {
        self.find_section(".text")
    }

    /// Get function symbols (STT_FUNC) with nonzero addresses and valid sections.
    ///
    /// Chains `.symtab` and `.dynsym`, filters for STT_FUNC, sorts by address,
    /// and deduplicates by `(name, st_value)`.
    pub fn function_symbols(&self) -> Result<Vec<Elf32Symbol<'a>>, ParseError> {
        let mut funcs: Vec<Elf32Symbol<'a>> = self
            .symbols()?
            .into_iter()
            .chain(self.dynamic_symbols()?)
            .filter(|s| s.is_function() && s.st_value != 0 && s.st_shndx != 0)
            .collect();

        // Sort by address for predictable ordering
        funcs.sort_by_key(|s| s.st_value);

        // Dedup by (name, address)
        funcs.dedup_by(|a, b| a.name == b.name && a.st_value == b.st_value);

        Ok(funcs)
    }
}

/// Parse ELF32 program headers (segments) from the ELF data.
fn parse_elf32_program_headers(
    data: &[u8],
    header: &Elf32Header,
    swap: bool,
) -> Result<Vec<Elf32ProgramHeader>, ParseError> {
    let count = header.e_phnum as usize;
    if count == 0 || header.e_phoff == 0 {
        return Ok(Vec::new());
    }

    let entry_size = header.e_phentsize as usize;
    if entry_size < ELF32_PHDR_SIZE {
        return Err(ParseError::InvalidHeader(format!(
            "program header entry size {entry_size} < minimum {ELF32_PHDR_SIZE}"
        )));
    }

    let mut segments = Vec::with_capacity(count);
    let mut offset = header.e_phoff as usize;

    for _ in 0..count {
        let fixed_end =
            offset.checked_add(ELF32_PHDR_SIZE).ok_or(ParseError::UnexpectedEof(offset))?;
        if fixed_end > data.len() {
            return Err(ParseError::UnexpectedEof(offset));
        }
        let mut cursor = Cursor::new(data, offset, swap);

        let phdr = Elf32ProgramHeader {
            p_type: cursor.read_u32()?,
            p_offset: cursor.read_u32()?,
            p_vaddr: cursor.read_u32()?,
            p_paddr: cursor.read_u32()?,
            p_filesz: cursor.read_u32()?,
            p_memsz: cursor.read_u32()?,
            p_flags: cursor.read_u32()?,
            p_align: cursor.read_u32()?,
        };
        segments.push(phdr);
        offset = offset.checked_add(entry_size).ok_or(ParseError::UnexpectedEof(offset))?;
    }

    Ok(segments)
}

/// Parse ELF32 section headers from the ELF data.
fn parse_elf32_section_headers(
    data: &[u8],
    header: &Elf32Header,
    swap: bool,
) -> Result<Vec<Elf32SectionHeader>, ParseError> {
    let count = header.e_shnum as usize;
    if count == 0 || header.e_shoff == 0 {
        return Ok(Vec::new());
    }

    let entry_size = header.e_shentsize as usize;
    if entry_size < ELF32_SHDR_SIZE {
        return Err(ParseError::InvalidHeader(format!(
            "section header entry size {entry_size} < minimum {ELF32_SHDR_SIZE}"
        )));
    }

    let mut sections = Vec::with_capacity(count);
    let mut offset = header.e_shoff as usize;

    for _ in 0..count {
        let fixed_end =
            offset.checked_add(ELF32_SHDR_SIZE).ok_or(ParseError::UnexpectedEof(offset))?;
        if fixed_end > data.len() {
            return Err(ParseError::UnexpectedEof(offset));
        }
        let mut cursor = Cursor::new(data, offset, swap);

        let shdr = Elf32SectionHeader {
            sh_name: cursor.read_u32()?,
            sh_type: cursor.read_u32()?,
            sh_flags: cursor.read_u32()?,
            sh_addr: cursor.read_u32()?,
            sh_offset: cursor.read_u32()?,
            sh_size: cursor.read_u32()?,
            sh_link: cursor.read_u32()?,
            sh_info: cursor.read_u32()?,
            sh_addralign: cursor.read_u32()?,
            sh_entsize: cursor.read_u32()?,
        };
        sections.push(shdr);
        offset = offset.checked_add(entry_size).ok_or(ParseError::UnexpectedEof(offset))?;
    }

    Ok(sections)
}

/// Parse ELF64 program headers (segments) from the ELF data.
fn parse_program_headers(
    data: &[u8],
    header: &Elf64Header,
    swap: bool,
) -> Result<Vec<Elf64ProgramHeader>, ParseError> {
    let count = header.e_phnum as usize;
    if count == 0 || header.e_phoff == 0 {
        return Ok(Vec::new());
    }

    let entry_size = header.e_phentsize as usize;
    if entry_size < ELF64_PHDR_SIZE {
        return Err(ParseError::InvalidHeader(format!(
            "program header entry size {entry_size} < minimum {ELF64_PHDR_SIZE}"
        )));
    }

    let mut segments = Vec::with_capacity(count);
    let mut offset = usize::try_from(header.e_phoff).map_err(|_| ParseError::DataOutOfBounds {
        offset: header.e_phoff,
        end: header.e_phoff,
        file_size: data.len(),
    })?;

    for _ in 0..count {
        let fixed_end =
            offset.checked_add(ELF64_PHDR_SIZE).ok_or(ParseError::UnexpectedEof(offset))?;
        if fixed_end > data.len() {
            return Err(ParseError::UnexpectedEof(offset));
        }
        let mut cursor = Cursor::new(data, offset, swap);

        let phdr = Elf64ProgramHeader {
            p_type: cursor.read_u32()?,
            p_flags: cursor.read_u32()?,
            p_offset: cursor.read_u64()?,
            p_vaddr: cursor.read_u64()?,
            p_paddr: cursor.read_u64()?,
            p_filesz: cursor.read_u64()?,
            p_memsz: cursor.read_u64()?,
            p_align: cursor.read_u64()?,
        };
        segments.push(phdr);
        offset = offset.checked_add(entry_size).ok_or(ParseError::UnexpectedEof(offset))?;
    }

    Ok(segments)
}

/// Parse section headers from the ELF data.
fn parse_section_headers(
    data: &[u8],
    header: &Elf64Header,
    swap: bool,
) -> Result<Vec<Elf64SectionHeader>, ParseError> {
    let count = header.e_shnum as usize;
    if count == 0 || header.e_shoff == 0 {
        return Ok(Vec::new());
    }

    let entry_size = header.e_shentsize as usize;
    if entry_size < ELF64_SHDR_SIZE {
        return Err(ParseError::InvalidHeader(format!(
            "section header entry size {entry_size} < minimum {ELF64_SHDR_SIZE}"
        )));
    }

    let mut sections = Vec::with_capacity(count);
    let mut offset = usize::try_from(header.e_shoff).map_err(|_| ParseError::DataOutOfBounds {
        offset: header.e_shoff,
        end: header.e_shoff,
        file_size: data.len(),
    })?;

    for _ in 0..count {
        let fixed_end =
            offset.checked_add(ELF64_SHDR_SIZE).ok_or(ParseError::UnexpectedEof(offset))?;
        if fixed_end > data.len() {
            return Err(ParseError::UnexpectedEof(offset));
        }
        let mut cursor = Cursor::new(data, offset, swap);

        let shdr = Elf64SectionHeader {
            sh_name: cursor.read_u32()?,
            sh_type: cursor.read_u32()?,
            sh_flags: cursor.read_u64()?,
            sh_addr: cursor.read_u64()?,
            sh_offset: cursor.read_u64()?,
            sh_size: cursor.read_u64()?,
            sh_link: cursor.read_u32()?,
            sh_info: cursor.read_u32()?,
            sh_addralign: cursor.read_u64()?,
            sh_entsize: cursor.read_u64()?,
        };
        sections.push(shdr);
        offset = offset.checked_add(entry_size).ok_or(ParseError::UnexpectedEof(offset))?;
    }

    Ok(sections)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a minimal valid ELF64 binary in memory for testing.
    /// Contains: ELF header, 1 program header (PT_LOAD), 4 sections
    /// (NULL, .shstrtab, .symtab, .strtab), and 2 symbols.
    fn build_test_elf() -> Vec<u8> {
        let mut buf = Vec::new();

        // --- Section header string table (.shstrtab) contents ---
        // Index 0: ""  (null section name)
        // Index 1: ".shstrtab"
        // Index 11: ".symtab"
        // Index 19: ".strtab"
        let shstrtab = b"\0.shstrtab\0.symtab\0.strtab\0";
        // offsets: 0=>\0, 1=>.shstrtab\0, 11=>.symtab\0, 19=>.strtab\0

        // --- Symbol string table (.strtab) contents ---
        let strtab = b"\0_start\0main\0";
        // offsets: 0=>\0, 1=>_start, 8=>main

        // --- Symbol table (.symtab) entries ---
        // Symbol 0: null symbol (required by ELF spec)
        // Symbol 1: _start (STB_GLOBAL | STT_FUNC, section 1)
        // Symbol 2: main (STB_GLOBAL | STT_FUNC, section 1)

        // Layout:
        // 0x000: ELF header (64 bytes)
        // 0x040: Program header (56 bytes)
        // 0x078: shstrtab data (27 bytes), padded to 0x098
        // 0x098: strtab data (14 bytes), padded to 0x0A8
        // 0x0A8: symtab data (3 * 24 = 72 bytes) => ends at 0x0F0
        // 0x0F0: Section headers (4 * 64 = 256 bytes) => ends at 0x1F0

        let phdr_off: u64 = 0x40;
        let shstrtab_off: u64 = 0x78;
        let strtab_off: u64 = 0x98;
        let symtab_off: u64 = 0xA8;
        let shdr_off: u64 = 0xF0;

        // --- ELF Header (64 bytes) ---
        buf.extend_from_slice(&ELF_MAGIC); // e_ident[0..4]: magic
        buf.push(ELFCLASS64); // e_ident[4]: class
        buf.push(ELFDATA2LSB); // e_ident[5]: data
        buf.push(1); // e_ident[6]: version (EV_CURRENT)
        buf.push(0); // e_ident[7]: OS/ABI
        buf.extend_from_slice(&[0u8; 8]); // e_ident[8..16]: padding
        buf.extend_from_slice(&2u16.to_le_bytes()); // e_type: ET_EXEC
        buf.extend_from_slice(&0x3Eu16.to_le_bytes()); // e_machine: EM_X86_64
        buf.extend_from_slice(&1u32.to_le_bytes()); // e_version
        buf.extend_from_slice(&0x400000u64.to_le_bytes()); // e_entry
        buf.extend_from_slice(&phdr_off.to_le_bytes()); // e_phoff
        buf.extend_from_slice(&shdr_off.to_le_bytes()); // e_shoff
        buf.extend_from_slice(&0u32.to_le_bytes()); // e_flags
        buf.extend_from_slice(&64u16.to_le_bytes()); // e_ehsize
        buf.extend_from_slice(&56u16.to_le_bytes()); // e_phentsize
        buf.extend_from_slice(&1u16.to_le_bytes()); // e_phnum
        buf.extend_from_slice(&64u16.to_le_bytes()); // e_shentsize
        buf.extend_from_slice(&4u16.to_le_bytes()); // e_shnum
        buf.extend_from_slice(&1u16.to_le_bytes()); // e_shstrndx (section 1)
        assert_eq!(buf.len(), 64);

        // --- Program Header (56 bytes at 0x40) ---
        buf.extend_from_slice(&1u32.to_le_bytes()); // p_type: PT_LOAD
        buf.extend_from_slice(&5u32.to_le_bytes()); // p_flags: PF_R | PF_X
        buf.extend_from_slice(&0u64.to_le_bytes()); // p_offset
        buf.extend_from_slice(&0x400000u64.to_le_bytes()); // p_vaddr
        buf.extend_from_slice(&0x400000u64.to_le_bytes()); // p_paddr
        buf.extend_from_slice(&0x200u64.to_le_bytes()); // p_filesz
        buf.extend_from_slice(&0x200u64.to_le_bytes()); // p_memsz
        buf.extend_from_slice(&0x1000u64.to_le_bytes()); // p_align
        assert_eq!(buf.len(), 0x78);

        // --- .shstrtab data at 0x78 (27 bytes, pad to 0x98 = 32 bytes) ---
        buf.extend_from_slice(shstrtab);
        while buf.len() < 0x98 {
            buf.push(0);
        }

        // --- .strtab data at 0x98 (14 bytes, pad to 0xA8 = 16 bytes) ---
        buf.extend_from_slice(strtab);
        while buf.len() < 0xA8 {
            buf.push(0);
        }

        // --- .symtab data at 0xA8 (3 entries * 24 bytes = 72 bytes) ---
        // Symbol 0: null
        buf.extend_from_slice(&0u32.to_le_bytes()); // st_name
        buf.push(0); // st_info
        buf.push(0); // st_other
        buf.extend_from_slice(&0u16.to_le_bytes()); // st_shndx
        buf.extend_from_slice(&0u64.to_le_bytes()); // st_value
        buf.extend_from_slice(&0u64.to_le_bytes()); // st_size

        // Symbol 1: _start (global func, section 1, addr 0x400000)
        buf.extend_from_slice(&1u32.to_le_bytes()); // st_name => "_start"
        buf.push((1 << 4) | 2); // st_info: STB_GLOBAL | STT_FUNC
        buf.push(0); // st_other: STV_DEFAULT
        buf.extend_from_slice(&1u16.to_le_bytes()); // st_shndx
        buf.extend_from_slice(&0x400000u64.to_le_bytes()); // st_value
        buf.extend_from_slice(&16u64.to_le_bytes()); // st_size

        // Symbol 2: main (global func, section 1, addr 0x400010)
        buf.extend_from_slice(&8u32.to_le_bytes()); // st_name => "main"
        buf.push((1 << 4) | 2); // st_info: STB_GLOBAL | STT_FUNC
        buf.push(0); // st_other
        buf.extend_from_slice(&1u16.to_le_bytes()); // st_shndx
        buf.extend_from_slice(&0x400010u64.to_le_bytes()); // st_value
        buf.extend_from_slice(&32u64.to_le_bytes()); // st_size

        assert_eq!(buf.len(), 0xF0);

        // --- Section Headers at 0xF0 (4 entries * 64 bytes = 256 bytes) ---

        // Section 0: NULL
        write_shdr(&mut buf, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);

        // Section 1: .shstrtab (sh_name=1, SHT_STRTAB)
        write_shdr(
            &mut buf,
            1,                     // sh_name
            SHT_STRTAB,            // sh_type
            0,                     // sh_flags
            0,                     // sh_addr
            shstrtab_off,          // sh_offset
            shstrtab.len() as u64, // sh_size
            0,                     // sh_link
            0,                     // sh_info
            1,                     // sh_addralign
            0,                     // sh_entsize
        );

        // Section 2: .symtab (sh_name=11, SHT_SYMTAB, sh_link=3 => .strtab)
        write_shdr(
            &mut buf,
            11,                          // sh_name
            SHT_SYMTAB,                  // sh_type
            0,                           // sh_flags
            0,                           // sh_addr
            symtab_off,                  // sh_offset
            (3 * ELF64_SYM_SIZE) as u64, // sh_size (3 symbols)
            3,                           // sh_link => .strtab section
            1,                           // sh_info (first non-local symbol index)
            8,                           // sh_addralign
            ELF64_SYM_SIZE as u64,       // sh_entsize
        );

        // Section 3: .strtab (sh_name=19, SHT_STRTAB)
        write_shdr(
            &mut buf,
            19,                  // sh_name
            SHT_STRTAB,          // sh_type
            0,                   // sh_flags
            0,                   // sh_addr
            strtab_off,          // sh_offset
            strtab.len() as u64, // sh_size
            0,                   // sh_link
            0,                   // sh_info
            1,                   // sh_addralign
            0,                   // sh_entsize
        );

        assert_eq!(buf.len(), 0x1F0);
        buf
    }

    /// Helper to write a 64-byte section header entry.
    #[allow(clippy::too_many_arguments)]
    fn write_shdr(
        buf: &mut Vec<u8>,
        sh_name: u32,
        sh_type: u32,
        sh_flags: u64,
        sh_addr: u64,
        sh_offset: u64,
        sh_size: u64,
        sh_link: u32,
        sh_info: u32,
        sh_addralign: u64,
        sh_entsize: u64,
    ) {
        buf.extend_from_slice(&sh_name.to_le_bytes());
        buf.extend_from_slice(&sh_type.to_le_bytes());
        buf.extend_from_slice(&sh_flags.to_le_bytes());
        buf.extend_from_slice(&sh_addr.to_le_bytes());
        buf.extend_from_slice(&sh_offset.to_le_bytes());
        buf.extend_from_slice(&sh_size.to_le_bytes());
        buf.extend_from_slice(&sh_link.to_le_bytes());
        buf.extend_from_slice(&sh_info.to_le_bytes());
        buf.extend_from_slice(&sh_addralign.to_le_bytes());
        buf.extend_from_slice(&sh_entsize.to_le_bytes());
    }

    #[test]
    fn test_elf64_parse_header() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse test ELF");

        assert_eq!(elf.header.e_type, 2); // ET_EXEC
        assert_eq!(elf.header.e_machine, 0x3E); // EM_X86_64
        assert_eq!(elf.header.e_entry, 0x400000);
        assert_eq!(elf.header.e_phnum, 1);
        assert_eq!(elf.header.e_shnum, 4);
        assert_eq!(elf.header.e_shstrndx, 1);
    }

    #[test]
    fn test_elf64_parse_segments() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse test ELF");

        assert_eq!(elf.segments.len(), 1);
        let seg = &elf.segments[0];
        assert_eq!(seg.p_type, 1); // PT_LOAD
        assert_eq!(seg.p_flags, 5); // PF_R | PF_X
        assert_eq!(seg.p_vaddr, 0x400000);
        assert_eq!(seg.p_align, 0x1000);
    }

    #[test]
    fn test_elf64_parse_sections() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse test ELF");

        assert_eq!(elf.sections.len(), 4);

        // Section 0 is NULL
        assert_eq!(elf.sections[0].sh_type, 0);

        // Find .shstrtab by name
        let shstrtab = elf.find_section(".shstrtab");
        assert!(shstrtab.is_some());
        assert_eq!(shstrtab.unwrap().sh_type, SHT_STRTAB);

        // Find .symtab by name
        let symtab = elf.find_section(".symtab");
        assert!(symtab.is_some());
        assert_eq!(symtab.unwrap().sh_type, SHT_SYMTAB);

        // Find .strtab by name
        let strtab = elf.find_section(".strtab");
        assert!(strtab.is_some());
        assert_eq!(strtab.unwrap().sh_type, SHT_STRTAB);
    }

    #[test]
    fn test_elf64_section_names() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse test ELF");

        let names: Vec<&str> =
            elf.sections.iter().map(|sh| elf.section_name(sh).unwrap_or("")).collect();
        assert_eq!(names, vec!["", ".shstrtab", ".symtab", ".strtab"]);
    }

    #[test]
    fn test_elf64_parse_symbols() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse test ELF");

        let symbols = elf.symbols().expect("should parse symbols");
        assert_eq!(symbols.len(), 3);

        // Symbol 0: null
        assert_eq!(symbols[0].name, "");
        assert!(symbols[0].is_local());

        // Symbol 1: _start
        assert_eq!(symbols[1].name, "_start");
        assert!(symbols[1].is_global());
        assert!(symbols[1].is_function());
        assert_eq!(symbols[1].st_value, 0x400000);
        assert_eq!(symbols[1].st_size, 16);

        // Symbol 2: main
        assert_eq!(symbols[2].name, "main");
        assert!(symbols[2].is_global());
        assert!(symbols[2].is_function());
        assert_eq!(symbols[2].st_value, 0x400010);
        assert_eq!(symbols[2].st_size, 32);
    }

    #[test]
    fn test_elf64_dynamic_symbols_empty() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse test ELF");

        // No .dynsym in our test binary
        let dynsyms = elf.dynamic_symbols().expect("should return empty vec");
        assert!(dynsyms.is_empty());
    }

    #[test]
    fn test_elf64_is_elf() {
        assert!(Elf64::is_elf(&[0x7f, b'E', b'L', b'F', 0, 0]));
        assert!(!Elf64::is_elf(&[0xCF, 0xFA, 0xED, 0xFE])); // Mach-O
        assert!(!Elf64::is_elf(&[0, 0, 0])); // too short
    }

    #[test]
    fn test_elf64_invalid_magic_returns_error() {
        let mut data = build_test_elf();
        data[0] = 0x00; // corrupt magic
        let err = Elf64::parse(&data).unwrap_err();
        assert!(matches!(err, ParseError::InvalidMagic(_)));
    }

    #[test]
    fn test_elf64_truncated_returns_error() {
        let err = Elf64::parse(&[0x7f, b'E', b'L', b'F']).unwrap_err();
        assert!(matches!(err, ParseError::UnexpectedEof(_)));
    }

    #[test]
    fn test_elf64_entry_point() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse test ELF");
        assert_eq!(elf.entry_point(), 0x400000);
    }

    #[test]
    fn test_elf64_section_data() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse test ELF");

        let strtab = elf.find_section(".strtab").expect("should find .strtab");
        let strtab_data = elf.section_data(strtab).expect("should get section data");
        // strtab contains "\0_start\0main\0"
        assert_eq!(strtab_data[0], 0);
        assert_eq!(&strtab_data[1..7], b"_start");
        assert_eq!(strtab_data[7], 0);
        assert_eq!(&strtab_data[8..12], b"main");
    }

    #[test]
    fn test_elf64_symbol_helpers() {
        let sym = Elf64Symbol {
            name: "test",
            st_name: 0,
            st_info: (2 << 4) | 1, // STB_WEAK | STT_OBJECT
            st_other: 0,
            st_shndx: 1,
            st_value: 0,
            st_size: 0,
        };
        assert!(sym.is_weak());
        assert!(sym.is_object());
        assert!(!sym.is_function());
        assert!(!sym.is_global());
        assert!(!sym.is_local());
        assert_eq!(sym.visibility(), 0); // STV_DEFAULT
    }

    #[test]
    fn test_elf64_executable_segments() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse test ELF");

        let exec_segs = elf.executable_segments();
        assert_eq!(exec_segs.len(), 1);
        assert_eq!(exec_segs[0].p_vaddr, 0x400000);
        assert_eq!(exec_segs[0].p_flags & 0x1, 1); // PF_X set
    }

    #[test]
    fn test_elf64_function_symbols() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse test ELF");

        let funcs = elf.function_symbols().expect("should get function symbols");
        assert_eq!(funcs.len(), 2);
        // Sorted by st_value: _start (0x400000) < main (0x400010)
        assert_eq!(funcs[0].name, "_start");
        assert_eq!(funcs[0].st_value, 0x400000);
        assert_eq!(funcs[1].name, "main");
        assert_eq!(funcs[1].st_value, 0x400010);
    }

    #[test]
    fn test_elf64_executable_segment_singular() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse test ELF");

        let seg = elf.executable_segment().expect("should find executable segment");
        assert_eq!(seg.p_type, 1); // PT_LOAD
        assert_eq!(seg.p_vaddr, 0x400000);
        assert_ne!(seg.p_flags & 0x1, 0); // PF_X set
    }

    #[test]
    fn test_elf64_dwarf_info_returns_none_without_debug_sections() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse test ELF");

        // Our test ELF has no .debug_info section, so dwarf_info() returns None
        let dwarf = elf.dwarf_info().expect("should not error");
        assert!(dwarf.is_none());
    }

    // --- Relocation & dynamic integration tests ---

    use crate::elf_relocation;

    /// Build a test ELF with .dynstr, .dynsym, .rela.plt, .dynamic sections.
    ///
    /// Layout:
    /// 0x000: ELF header (64 bytes)
    /// 0x040: Program header (56 bytes)
    /// 0x078: .shstrtab data (padded to 0x0C0)
    /// 0x0C0: .dynstr data (padded to 0x0F0)
    /// 0x0F0: .dynsym data (2 entries = 48 bytes, padded to 0x120)
    /// 0x120: .rela.plt data (1 entry = 24 bytes, padded to 0x138)
    /// 0x138: .dynamic data (5 entries = 80 bytes, ends at 0x188)
    /// 0x188: Section headers (7 * 64 = 448 bytes, ends at 0x348)
    fn build_test_elf_with_relocs() -> Vec<u8> {
        let mut buf = Vec::new();

        // --- Section header string table ---
        // Index 0: ""
        // Index 1: ".shstrtab"
        // Index 11: ".dynstr"
        // Index 19: ".dynsym"
        // Index 27: ".rela.plt"
        // Index 37: ".dynamic"
        let shstrtab = b"\0.shstrtab\0.dynstr\0.dynsym\0.rela.plt\0.dynamic\0";
        // offsets: 0, 1, 11, 19, 27, 37

        // --- Dynamic string table (.dynstr) ---
        // Index 0: ""
        // Index 1: "printf"
        // Index 8: "libm.so.6"
        // Index 18: "libc.so.6"
        let dynstr = b"\0printf\0libm.so.6\0libc.so.6\0";

        // Virtual address for .dynstr section (used in DT_STRTAB)
        let dynstr_vaddr: u64 = 0x400200;

        let phdr_off: u64 = 0x40;
        let shstrtab_off: u64 = 0x78;
        let dynstr_off: u64 = 0xC0;
        let dynsym_off: u64 = 0xF0;
        let rela_plt_off: u64 = 0x120;
        let dynamic_off: u64 = 0x138;
        let shdr_off: u64 = 0x188;

        // --- ELF Header (64 bytes) ---
        buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']); // magic
        buf.push(2); // ELFCLASS64
        buf.push(1); // ELFDATA2LSB
        buf.push(1); // EV_CURRENT
        buf.push(0); // OS/ABI
        buf.extend_from_slice(&[0u8; 8]); // padding
        buf.extend_from_slice(&3u16.to_le_bytes()); // e_type: ET_DYN
        buf.extend_from_slice(&0xB7u16.to_le_bytes()); // e_machine: EM_AARCH64
        buf.extend_from_slice(&1u32.to_le_bytes()); // e_version
        buf.extend_from_slice(&0x400000u64.to_le_bytes()); // e_entry
        buf.extend_from_slice(&phdr_off.to_le_bytes()); // e_phoff
        buf.extend_from_slice(&shdr_off.to_le_bytes()); // e_shoff
        buf.extend_from_slice(&0u32.to_le_bytes()); // e_flags
        buf.extend_from_slice(&64u16.to_le_bytes()); // e_ehsize
        buf.extend_from_slice(&56u16.to_le_bytes()); // e_phentsize
        buf.extend_from_slice(&1u16.to_le_bytes()); // e_phnum
        buf.extend_from_slice(&64u16.to_le_bytes()); // e_shentsize
        buf.extend_from_slice(&7u16.to_le_bytes()); // e_shnum (7 sections)
        buf.extend_from_slice(&1u16.to_le_bytes()); // e_shstrndx (section 1)
        assert_eq!(buf.len(), 64);

        // --- Program Header (56 bytes at 0x40) ---
        buf.extend_from_slice(&1u32.to_le_bytes()); // PT_LOAD
        buf.extend_from_slice(&5u32.to_le_bytes()); // PF_R | PF_X
        buf.extend_from_slice(&0u64.to_le_bytes()); // p_offset
        buf.extend_from_slice(&0x400000u64.to_le_bytes()); // p_vaddr
        buf.extend_from_slice(&0x400000u64.to_le_bytes()); // p_paddr
        buf.extend_from_slice(&0x400u64.to_le_bytes()); // p_filesz
        buf.extend_from_slice(&0x400u64.to_le_bytes()); // p_memsz
        buf.extend_from_slice(&0x1000u64.to_le_bytes()); // p_align
        assert_eq!(buf.len(), 0x78);

        // --- .shstrtab data at 0x78, pad to 0xC0 ---
        buf.extend_from_slice(shstrtab);
        while buf.len() < 0xC0 {
            buf.push(0);
        }

        // --- .dynstr data at 0xC0, pad to 0xF0 ---
        buf.extend_from_slice(dynstr);
        while buf.len() < 0xF0 {
            buf.push(0);
        }

        // --- .dynsym data at 0xF0 (2 entries * 24 bytes = 48, pad to 0x120) ---
        // Symbol 0: null
        buf.extend_from_slice(&0u32.to_le_bytes()); // st_name
        buf.push(0); // st_info
        buf.push(0); // st_other
        buf.extend_from_slice(&0u16.to_le_bytes()); // st_shndx
        buf.extend_from_slice(&0u64.to_le_bytes()); // st_value
        buf.extend_from_slice(&0u64.to_le_bytes()); // st_size

        // Symbol 1: printf (global func, undefined)
        buf.extend_from_slice(&1u32.to_le_bytes()); // st_name => "printf"
        buf.push((1 << 4) | 2); // STB_GLOBAL | STT_FUNC
        buf.push(0); // st_other
        buf.extend_from_slice(&0u16.to_le_bytes()); // st_shndx (SHN_UNDEF)
        buf.extend_from_slice(&0u64.to_le_bytes()); // st_value
        buf.extend_from_slice(&0u64.to_le_bytes()); // st_size

        while buf.len() < 0x120 {
            buf.push(0);
        }

        // --- .rela.plt data at 0x120 (1 entry = 24 bytes, pad to 0x138) ---
        // Relocation: offset=0x601000, sym=1 (printf), type=R_AARCH64_JUMP_SLOT(1026), addend=0
        buf.extend_from_slice(&0x601000u64.to_le_bytes()); // r_offset
        let rela_info: u64 = (1u64 << 32) | elf_relocation::R_AARCH64_JUMP_SLOT as u64;
        buf.extend_from_slice(&rela_info.to_le_bytes()); // r_info
        buf.extend_from_slice(&0i64.to_le_bytes()); // r_addend

        while buf.len() < 0x138 {
            buf.push(0);
        }

        // --- .dynamic data at 0x138 (5 entries * 16 bytes = 80 bytes, ends at 0x188) ---
        // DT_NEEDED: libm.so.6 (dynstr offset 8)
        buf.extend_from_slice(&(elf_relocation::DT_NEEDED).to_le_bytes());
        buf.extend_from_slice(&8u64.to_le_bytes());
        // DT_NEEDED: libc.so.6 (dynstr offset 18)
        buf.extend_from_slice(&(elf_relocation::DT_NEEDED).to_le_bytes());
        buf.extend_from_slice(&18u64.to_le_bytes());
        // DT_STRTAB: address of .dynstr
        buf.extend_from_slice(&(elf_relocation::DT_STRTAB).to_le_bytes());
        buf.extend_from_slice(&dynstr_vaddr.to_le_bytes());
        // DT_JMPREL: address of .rela.plt (we use file offset for test simplicity)
        buf.extend_from_slice(&(elf_relocation::DT_JMPREL).to_le_bytes());
        buf.extend_from_slice(&rela_plt_off.to_le_bytes());
        // DT_NULL: terminator
        buf.extend_from_slice(&(elf_relocation::DT_NULL).to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());

        assert_eq!(buf.len(), 0x188);

        // --- Section Headers at 0x188 (7 * 64 = 448 bytes) ---

        // Section 0: NULL
        write_shdr(&mut buf, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);

        // Section 1: .shstrtab
        write_shdr(&mut buf, 1, SHT_STRTAB, 0, 0, shstrtab_off, shstrtab.len() as u64, 0, 0, 1, 0);

        // Section 2: .dynstr (sh_addr = dynstr_vaddr so needed_libraries can find it)
        write_shdr(
            &mut buf,
            11, // sh_name => ".dynstr"
            SHT_STRTAB,
            0,
            dynstr_vaddr,
            dynstr_off,
            dynstr.len() as u64,
            0,
            0,
            1,
            0,
        );

        // Section 3: .dynsym (sh_link=2 => .dynstr)
        write_shdr(
            &mut buf,
            19, // sh_name => ".dynsym"
            SHT_DYNSYM,
            0,
            0,
            dynsym_off,
            (2 * ELF64_SYM_SIZE) as u64,
            2, // sh_link => .dynstr section
            1, // sh_info
            8,
            ELF64_SYM_SIZE as u64,
        );

        // Section 4: .rela.plt (SHT_RELA, sh_link=3 => .dynsym)
        write_shdr(
            &mut buf,
            27, // sh_name => ".rela.plt"
            SHT_RELA,
            0,
            0,
            rela_plt_off,
            24, // 1 rela entry
            3,  // sh_link => .dynsym
            0,
            8,
            24, // Elf64_Rela size
        );

        // Section 5: .dynamic (SHT_DYNAMIC, sh_link=2 => .dynstr)
        write_shdr(
            &mut buf,
            37, // sh_name => ".dynamic"
            SHT_DYNAMIC,
            0,
            0,
            dynamic_off,
            80, // 5 entries * 16 bytes
            2,  // sh_link => .dynstr
            0,
            8,
            16, // Elf64_Dyn size
        );

        // Section 6: padding NULL (to match e_shnum=7)
        write_shdr(&mut buf, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);

        buf
    }

    #[test]
    fn test_elf64_relocations() {
        let data = build_test_elf_with_relocs();
        let elf = Elf64::parse(&data).expect("should parse");

        let relocs = elf.relocations().expect("should parse relocations");
        assert_eq!(relocs.len(), 1);
        assert_eq!(relocs[0].r_offset, 0x601000);
        assert_eq!(relocs[0].sym(), 1);
        assert_eq!(relocs[0].reloc_type(), elf_relocation::R_AARCH64_JUMP_SLOT);
        assert_eq!(relocs[0].r_addend, 0);
    }

    #[test]
    fn test_elf64_rel_entries_empty() {
        // The test ELF has only SHT_RELA, no SHT_REL
        let data = build_test_elf_with_relocs();
        let elf = Elf64::parse(&data).expect("should parse");

        let rels = elf.rel_entries().expect("should return empty");
        assert!(rels.is_empty());
    }

    #[test]
    fn test_elf64_dynamic_entries() {
        let data = build_test_elf_with_relocs();
        let elf = Elf64::parse(&data).expect("should parse");

        let dyn_entries = elf.dynamic_entries().expect("should parse dynamic");
        assert_eq!(dyn_entries.len(), 5);
        assert_eq!(dyn_entries[0].d_tag, elf_relocation::DT_NEEDED);
        assert_eq!(dyn_entries[0].d_val, 8);
        assert_eq!(dyn_entries[1].d_tag, elf_relocation::DT_NEEDED);
        assert_eq!(dyn_entries[1].d_val, 18);
        assert_eq!(dyn_entries[2].d_tag, elf_relocation::DT_STRTAB);
        assert_eq!(dyn_entries[4].d_tag, elf_relocation::DT_NULL);
    }

    #[test]
    fn test_elf64_needed_libraries() {
        let data = build_test_elf_with_relocs();
        let elf = Elf64::parse(&data).expect("should parse");

        let libs = elf.needed_libraries().expect("should get needed libs");
        assert_eq!(libs.len(), 2);
        assert_eq!(libs[0], "libm.so.6");
        assert_eq!(libs[1], "libc.so.6");
    }

    #[test]
    fn test_elf64_plt_relocations() {
        let data = build_test_elf_with_relocs();
        let elf = Elf64::parse(&data).expect("should parse");

        let plt_relocs = elf.plt_relocations().expect("should parse plt relocs");
        assert_eq!(plt_relocs.len(), 1);
        assert_eq!(plt_relocs[0].r_offset, 0x601000);
        assert_eq!(plt_relocs[0].sym(), 1);
        assert_eq!(plt_relocs[0].reloc_type(), elf_relocation::R_AARCH64_JUMP_SLOT);
    }

    #[test]
    fn test_elf64_resolve_relocations() {
        let data = build_test_elf_with_relocs();
        let elf = Elf64::parse(&data).expect("should parse");

        let resolved = elf.resolve_relocations().expect("should resolve");
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].offset, 0x601000);
        assert_eq!(resolved[0].sym_name, "printf");
        assert_eq!(resolved[0].reloc_type, elf_relocation::R_AARCH64_JUMP_SLOT);
        assert_eq!(resolved[0].addend, 0);
    }

    #[test]
    fn test_elf64_no_relocs_returns_empty() {
        // Original test ELF has no relocation sections
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse");

        assert!(elf.relocations().unwrap().is_empty());
        assert!(elf.rel_entries().unwrap().is_empty());
        assert!(elf.dynamic_entries().unwrap().is_empty());
        assert!(elf.needed_libraries().unwrap().is_empty());
        assert!(elf.plt_relocations().unwrap().is_empty());
        assert!(elf.resolve_relocations().unwrap().is_empty());
    }

    // --- Edge case tests for improved coverage ---

    #[test]
    fn test_elf64_elf32_rejected() {
        let mut data = build_test_elf();
        data[4] = 1; // ELFCLASS32 instead of ELFCLASS64
        let err = Elf64::parse(&data).unwrap_err();
        match err {
            ParseError::UnsupportedFormat(msg) => {
                assert!(msg.contains("class 1"), "should mention class 1: {msg}");
            }
            other => panic!("expected UnsupportedFormat, got: {other}"),
        }
    }

    #[test]
    fn test_elf64_unknown_data_encoding_rejected() {
        let mut data = build_test_elf();
        data[5] = 3; // Invalid EI_DATA
        let err = Elf64::parse(&data).unwrap_err();
        assert!(matches!(err, ParseError::UnsupportedFormat(_)));
    }

    #[test]
    fn test_elf64_empty_input_rejected() {
        let err = Elf64::parse(&[]).unwrap_err();
        assert!(matches!(err, ParseError::UnexpectedEof(0)));
    }

    #[test]
    fn test_elf64_exactly_4_bytes_rejected() {
        let err = Elf64::parse(&[0x7f, b'E', b'L', b'F']).unwrap_err();
        assert!(matches!(err, ParseError::UnexpectedEof(_)));
    }

    #[test]
    fn test_elf64_symbol_type_combinations() {
        // STT_NOTYPE with STB_LOCAL
        let sym = Elf64Symbol {
            name: "notype",
            st_name: 0,
            st_info: 0, // STB_LOCAL | STT_NOTYPE
            st_other: 0,
            st_shndx: 0,
            st_value: 0,
            st_size: 0,
        };
        assert!(sym.is_local());
        assert!(!sym.is_global());
        assert!(!sym.is_weak());
        assert!(!sym.is_function());
        assert!(!sym.is_object());
        assert_eq!(sym.sym_type(), 0);
        assert_eq!(sym.binding(), 0);

        // STT_FUNC with STB_GLOBAL
        let sym = Elf64Symbol {
            name: "func",
            st_name: 0,
            st_info: (1 << 4) | 2, // STB_GLOBAL | STT_FUNC
            st_other: 0,
            st_shndx: 1,
            st_value: 0x1000,
            st_size: 64,
        };
        assert!(sym.is_global());
        assert!(sym.is_function());
        assert!(!sym.is_object());
        assert!(!sym.is_local());
        assert!(!sym.is_weak());

        // STT_OBJECT with STB_WEAK
        let sym = Elf64Symbol {
            name: "weak_obj",
            st_name: 0,
            st_info: (2 << 4) | 1, // STB_WEAK | STT_OBJECT
            st_other: 0,
            st_shndx: 1,
            st_value: 0x2000,
            st_size: 8,
        };
        assert!(sym.is_weak());
        assert!(sym.is_object());
        assert!(!sym.is_function());
        assert!(!sym.is_global());
    }

    #[test]
    fn test_elf64_symbol_visibility_values() {
        // STV_DEFAULT = 0
        let sym = Elf64Symbol {
            name: "default",
            st_name: 0,
            st_info: (1 << 4) | 2,
            st_other: 0,
            st_shndx: 1,
            st_value: 0,
            st_size: 0,
        };
        assert_eq!(sym.visibility(), 0);

        // STV_HIDDEN = 2
        let sym = Elf64Symbol {
            name: "hidden",
            st_name: 0,
            st_info: (1 << 4) | 2,
            st_other: 2,
            st_shndx: 1,
            st_value: 0,
            st_size: 0,
        };
        assert_eq!(sym.visibility(), 2);

        // STV_PROTECTED = 3
        let sym = Elf64Symbol {
            name: "protected",
            st_name: 0,
            st_info: (1 << 4) | 2,
            st_other: 3,
            st_shndx: 1,
            st_value: 0,
            st_size: 0,
        };
        assert_eq!(sym.visibility(), 3);
    }

    #[test]
    fn test_elf64_text_section_not_found() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse");
        // Test ELF has no .text section
        assert!(elf.text_section().is_none());
    }

    #[test]
    fn test_elf64_find_section_not_found() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse");
        assert!(elf.find_section(".nonexistent").is_none());
    }

    #[test]
    fn test_elf64_header_fields_complete() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse");

        assert_eq!(elf.header.e_version, 1);
        assert_eq!(elf.header.e_flags, 0);
        assert_eq!(elf.header.e_ehsize, 64);
        assert_eq!(elf.header.e_phentsize, 56);
        assert_eq!(elf.header.e_shentsize, 64);
    }

    #[test]
    fn test_elf64_data_accessor() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse");
        assert_eq!(elf.data().len(), data.len());
        assert_eq!(elf.data()[0..4], [0x7f, b'E', b'L', b'F']);
    }

    #[test]
    fn test_elf64_program_header_fields() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse");
        let seg = &elf.segments[0];

        assert_eq!(seg.p_offset, 0);
        assert_eq!(seg.p_paddr, 0x400000);
        assert_eq!(seg.p_filesz, 0x200);
        assert_eq!(seg.p_memsz, 0x200);
    }

    #[test]
    fn test_elf64_section_header_fields() {
        let data = build_test_elf();
        let elf = Elf64::parse(&data).expect("should parse");

        // .symtab section
        let symtab = elf.find_section(".symtab").expect("should find .symtab");
        assert_eq!(symtab.sh_type, SHT_SYMTAB);
        assert_eq!(symtab.sh_link, 3); // points to .strtab
        assert_eq!(symtab.sh_entsize, ELF64_SYM_SIZE as u64);
        assert_eq!(symtab.sh_addralign, 8);
    }

    #[test]
    fn test_elf64_executable_segment_none_when_no_exec() {
        let mut data = build_test_elf();
        // Patch p_flags to remove PF_X (change 5 -> 4, read-only)
        // p_flags is at offset 0x40 + 4 = 0x44
        data[0x44] = 4;
        data[0x45] = 0;
        data[0x46] = 0;
        data[0x47] = 0;
        let elf = Elf64::parse(&data).expect("should parse");
        assert!(elf.executable_segment().is_none());
        assert!(elf.executable_segments().is_empty());
    }

    #[test]
    fn test_elf64_reloc_elf_dynamic_entry_fields() {
        let data = build_test_elf_with_relocs();
        let elf = Elf64::parse(&data).expect("should parse");

        assert_eq!(elf.header.e_type, 3); // ET_DYN
        assert_eq!(elf.header.e_machine, 0xB7); // EM_AARCH64

        let dyn_entries = elf.dynamic_entries().unwrap();
        // Check DT_STRTAB
        let strtab_entry = dyn_entries.iter().find(|e| e.d_tag == elf_relocation::DT_STRTAB);
        assert!(strtab_entry.is_some());
    }
}
