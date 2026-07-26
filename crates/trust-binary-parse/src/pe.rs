// trust-binary-parse: PE/COFF binary format parser
//
// Zero-copy: Pe<'a> borrows from the input byte slice. Section names,
// import/export names, and symbol names are all references into the
// original buffer.
//
// Reference: Microsoft PE/COFF specification (PE Format, rev 11.0+)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::error::ParseError;
use crate::read::{Cursor, read_fixed_name, read_strtab_entry};

// --- PE/COFF constants ---

/// DOS MZ magic: 0x5A4D ('MZ')
const DOS_MAGIC: u16 = 0x5A4D;

/// PE signature: 'PE\0\0' = 0x00004550
const PE_SIGNATURE: u32 = 0x0000_4550;

/// Optional header magic for PE32 (32-bit)
const PE32_MAGIC: u16 = 0x10B;
/// Optional header magic for PE32+ (64-bit)
const PE32PLUS_MAGIC: u16 = 0x20B;

/// Size of the DOS header (64 bytes)
const DOS_HEADER_SIZE: usize = 64;
/// Size of the COFF file header (20 bytes)
const COFF_HEADER_SIZE: usize = 20;
/// Size of a PE section header entry (40 bytes)
const SECTION_HEADER_SIZE: usize = 40;
/// Size of a COFF symbol table entry (18 bytes)
const COFF_SYMBOL_SIZE: usize = 18;

/// Import directory entry size (20 bytes)
const IMPORT_DIR_ENTRY_SIZE: usize = 20;
/// Export directory table size (40 bytes)
const EXPORT_DIR_TABLE_SIZE: usize = 40;

/// Data directory indices
const IMAGE_DIRECTORY_ENTRY_EXPORT: usize = 0;
const IMAGE_DIRECTORY_ENTRY_IMPORT: usize = 1;

// --- Machine type constants ---

/// Machine type: x86
pub const IMAGE_FILE_MACHINE_I386: u16 = 0x14C;
/// Machine type: x86-64 / AMD64
pub const IMAGE_FILE_MACHINE_AMD64: u16 = 0x8664;
/// Machine type: ARM
pub const IMAGE_FILE_MACHINE_ARM: u16 = 0x1C0;
/// Machine type: ARM64 / AArch64
pub const IMAGE_FILE_MACHINE_ARM64: u16 = 0xAA64;

// --- COFF symbol storage classes ---

/// External (public) symbol
const IMAGE_SYM_CLASS_EXTERNAL: u8 = 2;
/// Static (file-scope) symbol
const IMAGE_SYM_CLASS_STATIC: u8 = 3;
/// Function symbol
const IMAGE_SYM_CLASS_FUNCTION: u8 = 101;

// --- Parsed structures ---

/// DOS header — only the fields we need.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DosHeader {
    /// Magic number (must be 0x5A4D 'MZ')
    pub(crate) e_magic: u16,
    /// File offset to the PE signature
    pub(crate) e_lfanew: u32,
}

/// COFF file header (20 bytes after PE signature).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoffHeader {
    /// Target machine type (IMAGE_FILE_MACHINE_*)
    pub(crate) machine: u16,
    /// Number of sections
    pub(crate) number_of_sections: u16,
    /// Time/date stamp (seconds since 1970-01-01)
    pub(crate) time_date_stamp: u32,
    /// File offset of COFF symbol table (0 if none)
    pub(crate) pointer_to_symbol_table: u32,
    /// Number of entries in the symbol table
    pub(crate) number_of_symbols: u32,
    /// Size of the optional header (0 for object files)
    pub(crate) size_of_optional_header: u16,
    /// Characteristics flags
    pub(crate) characteristics: u16,
}

/// PE format variant (PE32 vs PE32+).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum PeFormat {
    /// PE32 — 32-bit executable
    Pe32,
    /// PE32+ — 64-bit executable
    Pe32Plus,
}

/// PE optional header (PE32 or PE32+).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptionalHeader {
    /// PE32 or PE32+
    pub(crate) format: PeFormat,
    /// Linker major version
    pub(crate) major_linker_version: u8,
    /// Linker minor version
    pub(crate) minor_linker_version: u8,
    /// Size of the code (.text) section
    pub(crate) size_of_code: u32,
    /// Size of initialized data
    pub(crate) size_of_initialized_data: u32,
    /// Size of uninitialized data (BSS)
    pub(crate) size_of_uninitialized_data: u32,
    /// RVA of entry point
    pub(crate) address_of_entry_point: u32,
    /// RVA of beginning of code section
    pub(crate) base_of_code: u32,
    /// Preferred base address of the image
    pub(crate) image_base: u64,
    /// Section alignment in memory (power of 2)
    pub(crate) section_alignment: u32,
    /// File alignment on disk (power of 2)
    pub(crate) file_alignment: u32,
    /// Major OS version
    pub(crate) major_os_version: u16,
    /// Minor OS version
    pub(crate) minor_os_version: u16,
    /// Major image version
    pub(crate) major_image_version: u16,
    /// Minor image version
    pub(crate) minor_image_version: u16,
    /// Major subsystem version
    pub(crate) major_subsystem_version: u16,
    /// Minor subsystem version
    pub(crate) minor_subsystem_version: u16,
    /// Size of the image in memory
    pub(crate) size_of_image: u32,
    /// Size of all headers rounded up to file_alignment
    pub(crate) size_of_headers: u32,
    /// Image checksum
    pub(crate) checksum: u32,
    /// Subsystem (console, GUI, etc.)
    pub(crate) subsystem: u16,
    /// DLL characteristics
    pub(crate) dll_characteristics: u16,
    /// Number of data directory entries
    pub(crate) number_of_rva_and_sizes: u32,
    /// Data directories (RVA, Size pairs)
    pub(crate) data_directories: Vec<DataDirectory>,
}

/// A data directory entry (RVA + size).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DataDirectory {
    /// Relative virtual address
    pub(crate) virtual_address: u32,
    /// Size in bytes
    pub(crate) size: u32,
}

/// A PE section header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeSectionHeader {
    /// Section name (up to 8 ASCII characters)
    pub(crate) name: String,
    /// Virtual size (actual size in memory)
    pub(crate) virtual_size: u32,
    /// RVA when loaded into memory
    pub(crate) virtual_address: u32,
    /// Size of raw data on disk
    pub(crate) size_of_raw_data: u32,
    /// File offset to raw data
    pub(crate) pointer_to_raw_data: u32,
    /// File offset to relocations
    pub(crate) pointer_to_relocations: u32,
    /// File offset to line numbers
    pub(crate) pointer_to_line_numbers: u32,
    /// Number of relocations
    pub(crate) number_of_relocations: u16,
    /// Number of line numbers
    pub(crate) number_of_line_numbers: u16,
    /// Section characteristics/flags
    pub(crate) characteristics: u32,
}

/// An imported DLL and its functions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportEntry<'a> {
    /// DLL name (e.g., "KERNEL32.dll")
    pub(crate) dll_name: &'a str,
    /// Imported functions
    pub(crate) functions: Vec<ImportFunction<'a>>,
}

/// A single imported function.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ImportFunction<'a> {
    /// Import by name (hint, name)
    ByName { hint: u16, name: &'a str },
    /// Import by ordinal number
    ByOrdinal(u16),
}

/// An exported function from the PE.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportEntry<'a> {
    /// Ordinal number
    pub(crate) ordinal: u16,
    /// Function name (if named; ordinal-only exports have no name)
    pub(crate) name: Option<&'a str>,
    /// RVA of the function
    pub(crate) rva: u32,
    /// Whether this is a forwarder (string RVA pointing to "DLL.Function")
    pub(crate) is_forwarder: bool,
}

/// A COFF symbol table entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoffSymbol<'a> {
    /// Symbol name
    pub(crate) name: &'a str,
    /// Symbol value (typically address or offset)
    pub(crate) value: u32,
    /// Section number (1-based, 0=external, -1=absolute, -2=debug)
    pub(crate) section_number: i16,
    /// Symbol type
    pub(crate) sym_type: u16,
    /// Storage class (IMAGE_SYM_CLASS_*)
    pub(crate) storage_class: u8,
    /// Number of auxiliary symbol records that follow
    pub(crate) number_of_aux_symbols: u8,
}

impl CoffSymbol<'_> {
    /// Whether this is an external (public) symbol.
    #[must_use]
    pub fn is_external(&self) -> bool {
        self.storage_class == IMAGE_SYM_CLASS_EXTERNAL
    }

    /// Whether this is a static (file-scope) symbol.
    #[must_use]
    pub fn is_static(&self) -> bool {
        self.storage_class == IMAGE_SYM_CLASS_STATIC
    }

    /// Whether this is a function symbol.
    #[must_use]
    pub fn is_function(&self) -> bool {
        self.storage_class == IMAGE_SYM_CLASS_FUNCTION || (self.sym_type & 0xF0) == 0x20 // derived type == function
    }
}

/// A parsed PE/COFF binary.
///
/// Borrows from the input byte slice for zero-copy access to section data,
/// import/export names, and symbol names.
#[derive(Debug)]
pub struct Pe<'a> {
    /// The raw file data.
    data: &'a [u8],
    /// DOS header.
    #[cfg(test)]
    pub(crate) dos_header: DosHeader,
    /// COFF file header.
    pub(crate) coff_header: CoffHeader,
    /// Optional header (present in executables/DLLs, absent in object files).
    pub(crate) optional_header: Option<OptionalHeader>,
    /// Section headers.
    pub(crate) sections: Vec<PeSectionHeader>,
}

impl<'a> Pe<'a> {
    /// Parse a PE/COFF binary from raw bytes.
    ///
    /// Validates the DOS magic, PE signature, and parses COFF header,
    /// optional header, and section headers. Import/export tables and
    /// symbols are parsed on demand.
    pub fn parse(data: &'a [u8]) -> Result<Self, ParseError> {
        // --- DOS Header ---
        if data.len() < DOS_HEADER_SIZE {
            return Err(ParseError::UnexpectedEof(0));
        }

        let mut cursor = Cursor::new(data, 0, false); // PE is always little-endian
        let e_magic = cursor.read_u16()?;
        if e_magic != DOS_MAGIC {
            return Err(ParseError::InvalidDosMagic(e_magic));
        }

        // e_lfanew is at offset 0x3C in the DOS header
        cursor.set_offset(0x3C);
        let e_lfanew = cursor.read_u32()?;
        #[cfg(test)]
        let dos_header = DosHeader { e_magic, e_lfanew };

        // --- PE Signature ---
        let pe_sig_offset = e_lfanew as usize;
        if pe_sig_offset + 4 > data.len() {
            return Err(ParseError::UnexpectedEof(pe_sig_offset));
        }
        cursor.set_offset(pe_sig_offset);
        let pe_sig = cursor.read_u32()?;
        if pe_sig != PE_SIGNATURE {
            return Err(ParseError::InvalidPeSignature(pe_sig));
        }

        // --- COFF Header (20 bytes immediately after PE signature) ---
        let coff_offset = pe_sig_offset + 4;
        if coff_offset + COFF_HEADER_SIZE > data.len() {
            return Err(ParseError::UnexpectedEof(coff_offset));
        }
        cursor.set_offset(coff_offset);
        let coff_header = CoffHeader {
            machine: cursor.read_u16()?,
            number_of_sections: cursor.read_u16()?,
            time_date_stamp: cursor.read_u32()?,
            pointer_to_symbol_table: cursor.read_u32()?,
            number_of_symbols: cursor.read_u32()?,
            size_of_optional_header: cursor.read_u16()?,
            characteristics: cursor.read_u16()?,
        };

        // --- Optional Header ---
        let opt_hdr_offset = coff_offset + COFF_HEADER_SIZE;
        let optional_header = if coff_header.size_of_optional_header > 0 {
            Some(parse_optional_header(
                data,
                opt_hdr_offset,
                coff_header.size_of_optional_header as usize,
            )?)
        } else {
            None
        };

        // --- Section Headers ---
        let sections_offset = opt_hdr_offset + coff_header.size_of_optional_header as usize;
        let sections =
            parse_section_headers(data, sections_offset, coff_header.number_of_sections as usize)?;

        Ok(Self {
            data,
            #[cfg(test)]
            dos_header,
            coff_header,
            optional_header,
            sections,
        })
    }

    /// Check if the data starts with the DOS 'MZ' magic.
    #[must_use]
    pub fn is_pe(data: &[u8]) -> bool {
        data.len() >= 2 && data[0] == b'M' && data[1] == b'Z'
    }

    /// The raw file data.
    #[must_use]
    pub fn data(&self) -> &'a [u8] {
        self.data
    }

    /// Get the entry point RVA (0 if no optional header).
    #[must_use]
    pub fn entry_point(&self) -> u32 {
        self.optional_header.as_ref().map_or(0, |oh| oh.address_of_entry_point)
    }

    /// Get the image base address (0 if no optional header).
    #[must_use]
    pub fn image_base(&self) -> u64 {
        self.optional_header.as_ref().map_or(0, |oh| oh.image_base)
    }

    /// Find a section by name (e.g., ".text", ".data").
    #[must_use]
    pub fn find_section(&self, name: &str) -> Option<&PeSectionHeader> {
        self.sections.iter().find(|s| s.name == name)
    }

    /// Get the raw data for a section.
    pub fn section_data(&self, sh: &PeSectionHeader) -> Result<&'a [u8], ParseError> {
        let start =
            usize::try_from(sh.pointer_to_raw_data).map_err(|_| ParseError::DataOutOfBounds {
                offset: u64::from(sh.pointer_to_raw_data),
                end: u64::from(sh.pointer_to_raw_data)
                    .saturating_add(u64::from(sh.size_of_raw_data)),
                file_size: self.data.len(),
            })?;
        let size =
            usize::try_from(sh.size_of_raw_data).map_err(|_| ParseError::DataOutOfBounds {
                offset: u64::from(sh.pointer_to_raw_data),
                end: u64::from(sh.pointer_to_raw_data)
                    .saturating_add(u64::from(sh.size_of_raw_data)),
                file_size: self.data.len(),
            })?;
        let end = start.checked_add(size).ok_or(ParseError::DataOutOfBounds {
            offset: u64::from(sh.pointer_to_raw_data),
            end: u64::from(sh.pointer_to_raw_data).saturating_add(u64::from(sh.size_of_raw_data)),
            file_size: self.data.len(),
        })?;
        if end > self.data.len() {
            return Err(ParseError::DataOutOfBounds {
                offset: u64::from(sh.pointer_to_raw_data),
                end: u64::from(sh.pointer_to_raw_data)
                    .saturating_add(u64::from(sh.size_of_raw_data)),
                file_size: self.data.len(),
            });
        }
        Ok(&self.data[start..end])
    }

    /// Resolve a Relative Virtual Address (RVA) to a file offset.
    ///
    /// Searches section headers to find which section contains the RVA,
    /// then computes: file_offset = rva - section.virtual_address + section.pointer_to_raw_data
    pub fn rva_to_offset(&self, rva: u32) -> Result<usize, ParseError> {
        let section = self.section_containing_rva(rva)?;
        let offset = self.checked_section_file_offset(section, rva)?;
        let raw_end = u64::from(section.pointer_to_raw_data)
            .checked_add(u64::from(section.size_of_raw_data))
            .ok_or(ParseError::DataOutOfBounds {
                offset: u64::from(section.pointer_to_raw_data),
                end: u64::MAX,
                file_size: self.data.len(),
            })?;
        if offset >= raw_end || offset >= self.data.len() as u64 {
            return Err(ParseError::DataOutOfBounds {
                offset,
                end: offset.saturating_add(1),
                file_size: self.data.len(),
            });
        }
        usize::try_from(offset).map_err(|_| ParseError::DataOutOfBounds {
            offset,
            end: offset.saturating_add(1),
            file_size: self.data.len(),
        })
    }

    fn section_containing_rva(&self, rva: u32) -> Result<&PeSectionHeader, ParseError> {
        for section in &self.sections {
            let va = section.virtual_address;
            let mapped_size = section.virtual_size.max(section.size_of_raw_data);
            let Some(end) = va.checked_add(mapped_size) else {
                continue;
            };
            if rva >= va && rva < end {
                return Ok(section);
            }
        }
        Err(ParseError::InvalidRva { rva })
    }

    fn checked_section_file_offset(
        &self,
        section: &PeSectionHeader,
        rva: u32,
    ) -> Result<u64, ParseError> {
        let delta = u64::from(rva - section.virtual_address);
        u64::from(section.pointer_to_raw_data).checked_add(delta).ok_or_else(|| {
            ParseError::DataOutOfBounds {
                offset: u64::from(section.pointer_to_raw_data),
                end: u64::MAX,
                file_size: self.data.len(),
            }
        })
    }

    fn file_range(&self, offset: usize, size: usize) -> Result<std::ops::Range<usize>, ParseError> {
        let end = offset.checked_add(size).ok_or(ParseError::DataOutOfBounds {
            offset: offset as u64,
            end: u64::MAX,
            file_size: self.data.len(),
        })?;
        if end > self.data.len() {
            return Err(ParseError::DataOutOfBounds {
                offset: offset as u64,
                end: end as u64,
                file_size: self.data.len(),
            });
        }
        Ok(offset..end)
    }

    fn rva_range_to_offsets(
        &self,
        rva: u32,
        size: u32,
    ) -> Result<std::ops::Range<usize>, ParseError> {
        let section = self.section_containing_rva(rva)?;
        let end_rva = rva.checked_add(size).ok_or(ParseError::InvalidRva { rva })?;
        let section_mapped_end = section
            .virtual_address
            .checked_add(section.virtual_size.max(section.size_of_raw_data))
            .ok_or(ParseError::InvalidRva { rva })?;
        if end_rva > section_mapped_end {
            return Err(ParseError::InvalidRva { rva: end_rva });
        }

        let start_delta = rva - section.virtual_address;
        let start = section
            .pointer_to_raw_data
            .checked_add(start_delta)
            .ok_or(ParseError::InvalidRva { rva })? as usize;
        let raw_end = (section.pointer_to_raw_data as usize)
            .checked_add(section.size_of_raw_data as usize)
            .ok_or(ParseError::DataOutOfBounds {
                offset: section.pointer_to_raw_data as u64,
                end: u64::MAX,
                file_size: self.data.len(),
            })?;
        let range = self.file_range(start, size as usize)?;
        if range.end > raw_end {
            return Err(ParseError::DataOutOfBounds {
                offset: range.start as u64,
                end: range.end as u64,
                file_size: self.data.len(),
            });
        }
        Ok(range)
    }

    fn rva_to_offset_with_section_end(&self, rva: u32) -> Result<(usize, usize), ParseError> {
        let section = self.section_containing_rva(rva)?;
        let delta = rva - section.virtual_address;
        let offset =
            section.pointer_to_raw_data.checked_add(delta).ok_or(ParseError::InvalidRva { rva })?
                as usize;
        let raw_end = (section.pointer_to_raw_data as usize)
            .checked_add(section.size_of_raw_data as usize)
            .ok_or(ParseError::DataOutOfBounds {
                offset: section.pointer_to_raw_data as u64,
                end: u64::MAX,
                file_size: self.data.len(),
            })?;
        let raw_end = raw_end.min(self.data.len());
        if offset >= raw_end {
            return Err(ParseError::DataOutOfBounds {
                offset: offset as u64,
                end: raw_end as u64,
                file_size: self.data.len(),
            });
        }
        Ok((offset, raw_end))
    }

    /// Read a nul-terminated ASCII string at an RVA.
    fn read_string_at_rva(&self, rva: u32) -> Result<&'a str, ParseError> {
        let (offset, section_end) = self.rva_to_offset_with_section_end(rva)?;
        self.read_nul_string_bounded(offset, section_end).map_err(|err| match err {
            ParseError::InvalidUtf8 { .. } => ParseError::InvalidUtf8 { index: rva },
            other => other,
        })
    }

    /// Parse the import table.
    ///
    /// Returns a list of imported DLLs with their function imports.
    /// Requires the optional header to be present (for data directories).
    pub fn imports(&self) -> Result<Vec<ImportEntry<'a>>, ParseError> {
        let oh = match &self.optional_header {
            Some(oh) => oh,
            None => return Ok(Vec::new()),
        };

        if IMAGE_DIRECTORY_ENTRY_IMPORT >= oh.data_directories.len() {
            return Ok(Vec::new());
        }
        let import_dir = &oh.data_directories[IMAGE_DIRECTORY_ENTRY_IMPORT];
        if import_dir.virtual_address == 0 || import_dir.size == 0 {
            return Ok(Vec::new());
        }

        let import_range =
            self.rva_range_to_offsets(import_dir.virtual_address, import_dir.size)?;
        let is_pe32plus = oh.format == PeFormat::Pe32Plus;

        let mut entries = Vec::new();
        let mut descriptor_offset = import_range.start;
        let mut found_terminator = false;

        while descriptor_offset < import_range.end {
            let Some(descriptor_end) = descriptor_offset.checked_add(IMPORT_DIR_ENTRY_SIZE) else {
                return Err(ParseError::InvalidImportEntry { offset: descriptor_offset });
            };
            if descriptor_end > import_range.end {
                return Err(ParseError::InvalidImportEntry { offset: descriptor_offset });
            }

            let mut cursor = Cursor::new(self.data, descriptor_offset, false);
            let original_first_thunk = cursor.read_u32()?; // OriginalFirstThunk (ILT RVA)
            let time_date_stamp = cursor.read_u32()?;
            let forwarder_chain = cursor.read_u32()?;
            let name_rva = cursor.read_u32()?;
            let first_thunk = cursor.read_u32()?; // FirstThunk (IAT RVA)

            // Null entry terminates the import directory
            if original_first_thunk == 0
                && time_date_stamp == 0
                && forwarder_chain == 0
                && name_rva == 0
                && first_thunk == 0
            {
                found_terminator = true;
                break;
            }
            if name_rva == 0 {
                return Err(ParseError::InvalidImportEntry { offset: descriptor_offset });
            }

            let dll_name = self.read_string_at_rva(name_rva)?;
            let lookup_table_rva =
                if original_first_thunk != 0 { original_first_thunk } else { first_thunk };
            if lookup_table_rva == 0 {
                return Err(ParseError::InvalidImportEntry { offset: descriptor_offset });
            }
            let functions = self.parse_import_lookup_table(lookup_table_rva, is_pe32plus)?;

            entries.push(ImportEntry { dll_name, functions });
            descriptor_offset = descriptor_end;
        }

        if !found_terminator {
            return Err(ParseError::InvalidImportEntry { offset: import_range.end });
        }

        Ok(entries)
    }

    /// Parse an Import Lookup Table (ILT) starting at the given RVA.
    fn parse_import_lookup_table(
        &self,
        ilt_rva: u32,
        is_pe32plus: bool,
    ) -> Result<Vec<ImportFunction<'a>>, ParseError> {
        if ilt_rva == 0 {
            return Ok(Vec::new());
        }

        let (ilt_offset, ilt_end) = self.rva_to_offset_with_section_end(ilt_rva)?;
        let entry_size = if is_pe32plus { 8 } else { 4 };
        let mut entry_offset = ilt_offset;
        let mut functions = Vec::new();

        loop {
            let Some(entry_end) = entry_offset.checked_add(entry_size) else {
                return Err(ParseError::InvalidImportEntry { offset: entry_offset });
            };
            if entry_end > ilt_end {
                return Err(ParseError::InvalidImportEntry { offset: entry_offset });
            }

            if is_pe32plus {
                let mut cursor = Cursor::new(self.data, entry_offset, false);
                let entry = cursor.read_u64()?;
                if entry == 0 {
                    break;
                }
                // Bit 63 set = import by ordinal
                if entry & (1u64 << 63) != 0 {
                    functions.push(ImportFunction::ByOrdinal((entry & 0xFFFF) as u16));
                } else {
                    if entry & !0x7FFF_FFFF != 0 {
                        return Err(ParseError::InvalidImportEntry { offset: entry_offset });
                    }
                    let hint_name_rva = entry as u32;
                    let (hint, name) = self.read_hint_name(hint_name_rva, entry_offset)?;
                    functions.push(ImportFunction::ByName { hint, name });
                }
            } else {
                let mut cursor = Cursor::new(self.data, entry_offset, false);
                let entry = cursor.read_u32()?;
                if entry == 0 {
                    break;
                }
                // Bit 31 set = import by ordinal
                if entry & (1u32 << 31) != 0 {
                    functions.push(ImportFunction::ByOrdinal((entry & 0xFFFF) as u16));
                } else {
                    let hint_name_rva = entry & 0x7FFF_FFFF;
                    let (hint, name) = self.read_hint_name(hint_name_rva, entry_offset)?;
                    functions.push(ImportFunction::ByName { hint, name });
                }
            }
            entry_offset = entry_end;
        }

        Ok(functions)
    }

    fn read_hint_name(
        &self,
        hint_name_rva: u32,
        entry_offset: usize,
    ) -> Result<(u16, &'a str), ParseError> {
        let hint_range = self
            .rva_range_to_offsets(hint_name_rva, 2)
            .map_err(|_| ParseError::InvalidImportEntry { offset: entry_offset })?;
        let hint =
            u16::from_le_bytes([self.data[hint_range.start], self.data[hint_range.start + 1]]);
        let name_rva = hint_name_rva
            .checked_add(2)
            .ok_or(ParseError::InvalidImportEntry { offset: entry_offset })?;
        let name = self
            .read_string_at_rva(name_rva)
            .map_err(|_| ParseError::InvalidImportEntry { offset: entry_offset })?;
        Ok((hint, name))
    }

    /// Read a nul-terminated string at a file offset without crossing the bound.
    fn read_nul_string_bounded(
        &self,
        offset: usize,
        bound_end: usize,
    ) -> Result<&'a str, ParseError> {
        if offset >= bound_end || offset >= self.data.len() {
            return Err(ParseError::UnexpectedEof(offset));
        }
        let end_bound = bound_end.min(self.data.len());
        let remaining = &self.data[offset..end_bound];
        let end =
            remaining.iter().position(|&b| b == 0).ok_or(ParseError::UnexpectedEof(end_bound))?;
        std::str::from_utf8(&remaining[..end])
            .map_err(|_| ParseError::InvalidUtf8 { index: offset as u32 })
    }

    /// Parse the export table.
    ///
    /// Returns a list of exported functions with their ordinals, names,
    /// and RVAs.
    pub fn exports(&self) -> Result<Vec<ExportEntry<'a>>, ParseError> {
        let oh = match &self.optional_header {
            Some(oh) => oh,
            None => return Ok(Vec::new()),
        };

        let Some(export_dir) = oh.data_directories.get(IMAGE_DIRECTORY_ENTRY_EXPORT) else {
            return Ok(Vec::new());
        };
        if export_dir.virtual_address == 0 || export_dir.size == 0 {
            return Ok(Vec::new());
        }

        if export_dir.size < EXPORT_DIR_TABLE_SIZE as u32 {
            return Err(ParseError::InvalidExportTable {
                reason: "export directory is shorter than 40 bytes".into(),
            });
        }
        let export_range =
            self.rva_range_to_offsets(export_dir.virtual_address, export_dir.size)?;
        let export_offset = export_range.start;
        let export_end_rva =
            export_dir.virtual_address.checked_add(export_dir.size).ok_or_else(|| {
                ParseError::InvalidExportTable {
                    reason: "export directory RVA range overflows".into(),
                }
            })?;

        // Parse export directory table (40 bytes)
        let mut cursor = Cursor::new(self.data, export_offset, false);
        let _characteristics = cursor.read_u32()?;
        let _time_date_stamp = cursor.read_u32()?;
        let _major_version = cursor.read_u16()?;
        let _minor_version = cursor.read_u16()?;
        let _name_rva = cursor.read_u32()?;
        let ordinal_base = cursor.read_u32()?;
        let number_of_functions = cursor.read_u32()?;
        let number_of_names = cursor.read_u32()?;
        let address_of_functions = cursor.read_u32()?;
        let address_of_names = cursor.read_u32()?;
        let address_of_name_ordinals = cursor.read_u32()?;

        if number_of_names > number_of_functions {
            return Err(ParseError::InvalidExportTable {
                reason: format!(
                    "name count {number_of_names} exceeds function count {number_of_functions}"
                ),
            });
        }

        // Read Export Address Table (EAT)
        let eat_size = (number_of_functions as usize).checked_mul(4).ok_or_else(|| {
            ParseError::InvalidExportTable { reason: "export address table size overflows".into() }
        })?;
        let eat_size = u32::try_from(eat_size).map_err(|_| ParseError::InvalidExportTable {
            reason: "export address table size exceeds PE RVA range".into(),
        })?;
        let eat_range = self.rva_range_to_offsets(address_of_functions, eat_size)?;
        let eat_offset = eat_range.start;
        let mut eat_cursor = Cursor::new(self.data, eat_offset, false);
        let mut function_rvas = Vec::with_capacity(number_of_functions as usize);
        for _ in 0..number_of_functions {
            function_rvas.push(eat_cursor.read_u32()?);
        }

        // Read name pointer table and ordinal table
        let mut name_map: Vec<(u16, &'a str)> = Vec::with_capacity(number_of_names as usize);
        if number_of_names > 0 && address_of_names != 0 {
            let names_size = (number_of_names as usize).checked_mul(4).ok_or_else(|| {
                ParseError::InvalidExportTable { reason: "export name table size overflows".into() }
            })?;
            let names_size =
                u32::try_from(names_size).map_err(|_| ParseError::InvalidExportTable {
                    reason: "export name table size exceeds PE RVA range".into(),
                })?;
            let ordinals_size = (number_of_names as usize).checked_mul(2).ok_or_else(|| {
                ParseError::InvalidExportTable {
                    reason: "export ordinal table size overflows".into(),
                }
            })?;
            let ordinals_size =
                u32::try_from(ordinals_size).map_err(|_| ParseError::InvalidExportTable {
                    reason: "export ordinal table size exceeds PE RVA range".into(),
                })?;
            let names_offset = self.rva_range_to_offsets(address_of_names, names_size)?.start;
            let ordinals_offset =
                self.rva_range_to_offsets(address_of_name_ordinals, ordinals_size)?.start;
            let mut names_cursor = Cursor::new(self.data, names_offset, false);
            let mut ords_cursor = Cursor::new(self.data, ordinals_offset, false);

            for _ in 0..number_of_names {
                let name_rva = names_cursor.read_u32()?;
                let ordinal_index = ords_cursor.read_u16()?;
                if ordinal_index as u32 >= number_of_functions {
                    return Err(ParseError::InvalidExportTable {
                        reason: format!(
                            "export name ordinal index {ordinal_index} out of range for {number_of_functions} functions"
                        ),
                    });
                }
                let name = self.read_string_at_rva(name_rva)?;
                name_map.push((ordinal_index, name));
            }
        }

        // Build export entries
        let mut entries = Vec::with_capacity(number_of_functions as usize);
        for (i, &rva) in function_rvas.iter().enumerate() {
            if rva == 0 {
                continue; // unused ordinal slot
            }
            let ordinal_u32 = ordinal_base.checked_add(i as u32).ok_or_else(|| {
                ParseError::InvalidExportTable { reason: "export ordinal overflows u32".into() }
            })?;
            let ordinal =
                u16::try_from(ordinal_u32).map_err(|_| ParseError::InvalidExportTable {
                    reason: format!("export ordinal {ordinal_u32} exceeds u16 range"),
                })?;
            let name = name_map.iter().find(|(idx, _)| *idx == i as u16).map(|(_, n)| *n);
            // Forwarder: RVA points within the export directory itself
            let is_forwarder = rva >= export_dir.virtual_address && rva < export_end_rva;
            entries.push(ExportEntry { ordinal, name, rva, is_forwarder });
        }

        Ok(entries)
    }

    /// Parse the COFF symbol table (if present).
    ///
    /// COFF symbol tables are typically only present in object files
    /// and some older PE executables (not stripped).
    pub fn symbols(&self) -> Result<Vec<CoffSymbol<'a>>, ParseError> {
        let sym_offset = self.coff_header.pointer_to_symbol_table as usize;
        let sym_count = self.coff_header.number_of_symbols as usize;

        if sym_offset == 0 || sym_count == 0 {
            return Ok(Vec::new());
        }

        let sym_table_size = sym_count * COFF_SYMBOL_SIZE;
        if sym_offset + sym_table_size > self.data.len() {
            return Err(ParseError::InvalidSymbolTable {
                offset: sym_offset as u32,
                count: sym_count as u32,
            });
        }

        // String table starts immediately after the symbol table
        let strtab_offset = sym_offset + sym_table_size;

        let mut symbols = Vec::new();
        let mut cursor = Cursor::new(self.data, sym_offset, false);
        let mut i = 0;
        while i < sym_count {
            let name_bytes = cursor.read_bytes(8)?;
            let value = cursor.read_u32()?;
            let section_number = cursor.read_u16()? as i16;
            let sym_type = cursor.read_u16()?;
            let storage_class = cursor.read_u8()?;
            let number_of_aux_symbols = cursor.read_u8()?;

            // Decode symbol name: if first 4 bytes are zero, bytes 4-7
            // are an offset into the string table
            let name = if name_bytes[0..4] == [0, 0, 0, 0] {
                let str_offset = u32::from_le_bytes([
                    name_bytes[4],
                    name_bytes[5],
                    name_bytes[6],
                    name_bytes[7],
                ]);
                self.read_coff_string(strtab_offset, str_offset)?
            } else {
                read_fixed_name(name_bytes)
            };

            symbols.push(CoffSymbol {
                name,
                value,
                section_number,
                sym_type,
                storage_class,
                number_of_aux_symbols,
            });

            // Skip auxiliary symbol records
            let aux_count = number_of_aux_symbols as usize;
            if aux_count > 0 {
                cursor.skip(aux_count * COFF_SYMBOL_SIZE)?;
            }
            i += 1 + aux_count;
        }

        Ok(symbols)
    }

    /// Read a string from the COFF string table.
    fn read_coff_string(&self, strtab_base: usize, offset: u32) -> Result<&'a str, ParseError> {
        let abs_offset = strtab_base + offset as usize;
        // The first 4 bytes of the string table are its size; strings
        // start at offset 4, but callers pass the raw offset including
        // the size field, so we just use abs_offset directly.
        if abs_offset >= self.data.len() {
            return Err(ParseError::StringIndexOutOfBounds {
                index: offset,
                size: (self.data.len() - strtab_base) as u32,
            });
        }
        read_strtab_entry(&self.data[strtab_base..], offset)
    }
}

/// Parse the PE optional header.
fn parse_optional_header(
    data: &[u8],
    offset: usize,
    size: usize,
) -> Result<OptionalHeader, ParseError> {
    if offset + size > data.len() {
        return Err(ParseError::UnexpectedEof(offset));
    }

    let mut cursor = Cursor::new(data, offset, false);
    let magic = cursor.read_u16()?;

    let format = match magic {
        PE32_MAGIC => PeFormat::Pe32,
        PE32PLUS_MAGIC => PeFormat::Pe32Plus,
        other => return Err(ParseError::UnsupportedPeMagic(other)),
    };

    let major_linker_version = cursor.read_u8()?;
    let minor_linker_version = cursor.read_u8()?;
    let size_of_code = cursor.read_u32()?;
    let size_of_initialized_data = cursor.read_u32()?;
    let size_of_uninitialized_data = cursor.read_u32()?;
    let address_of_entry_point = cursor.read_u32()?;
    let base_of_code = cursor.read_u32()?;

    let image_base = match format {
        PeFormat::Pe32 => {
            let _base_of_data = cursor.read_u32()?; // PE32 only
            cursor.read_u32()? as u64
        }
        PeFormat::Pe32Plus => cursor.read_u64()?,
    };

    let section_alignment = cursor.read_u32()?;
    let file_alignment = cursor.read_u32()?;
    let major_os_version = cursor.read_u16()?;
    let minor_os_version = cursor.read_u16()?;
    let major_image_version = cursor.read_u16()?;
    let minor_image_version = cursor.read_u16()?;
    let major_subsystem_version = cursor.read_u16()?;
    let minor_subsystem_version = cursor.read_u16()?;
    let _win32_version_value = cursor.read_u32()?;
    let size_of_image = cursor.read_u32()?;
    let size_of_headers = cursor.read_u32()?;
    let checksum = cursor.read_u32()?;
    let subsystem = cursor.read_u16()?;
    let dll_characteristics = cursor.read_u16()?;

    // Stack/heap sizes differ between PE32 and PE32+
    match format {
        PeFormat::Pe32 => {
            let _stack_reserve = cursor.read_u32()?;
            let _stack_commit = cursor.read_u32()?;
            let _heap_reserve = cursor.read_u32()?;
            let _heap_commit = cursor.read_u32()?;
        }
        PeFormat::Pe32Plus => {
            let _stack_reserve = cursor.read_u64()?;
            let _stack_commit = cursor.read_u64()?;
            let _heap_reserve = cursor.read_u64()?;
            let _heap_commit = cursor.read_u64()?;
        }
    }

    let _loader_flags = cursor.read_u32()?;
    let number_of_rva_and_sizes = cursor.read_u32()?;

    // Data directories
    let dir_count = number_of_rva_and_sizes.min(16) as usize;
    let mut data_directories = Vec::with_capacity(dir_count);
    for _ in 0..dir_count {
        let virtual_address = cursor.read_u32()?;
        let dir_size = cursor.read_u32()?;
        data_directories.push(DataDirectory { virtual_address, size: dir_size });
    }

    Ok(OptionalHeader {
        format,
        major_linker_version,
        minor_linker_version,
        size_of_code,
        size_of_initialized_data,
        size_of_uninitialized_data,
        address_of_entry_point,
        base_of_code,
        image_base,
        section_alignment,
        file_alignment,
        major_os_version,
        minor_os_version,
        major_image_version,
        minor_image_version,
        major_subsystem_version,
        minor_subsystem_version,
        size_of_image,
        size_of_headers,
        checksum,
        subsystem,
        dll_characteristics,
        number_of_rva_and_sizes,
        data_directories,
    })
}

/// Parse section headers from the PE file.
fn parse_section_headers(
    data: &[u8],
    offset: usize,
    count: usize,
) -> Result<Vec<PeSectionHeader>, ParseError> {
    let mut sections = Vec::with_capacity(count);
    let mut cursor = Cursor::new(data, offset, false);

    for _ in 0..count {
        if cursor.offset() + SECTION_HEADER_SIZE > data.len() {
            return Err(ParseError::UnexpectedEof(cursor.offset()));
        }

        let name_bytes = cursor.read_bytes(8)?;
        let name = read_fixed_name(name_bytes).to_owned();
        let virtual_size = cursor.read_u32()?;
        let virtual_address = cursor.read_u32()?;
        let size_of_raw_data = cursor.read_u32()?;
        let pointer_to_raw_data = cursor.read_u32()?;
        let pointer_to_relocations = cursor.read_u32()?;
        let pointer_to_line_numbers = cursor.read_u32()?;
        let number_of_relocations = cursor.read_u16()?;
        let number_of_line_numbers = cursor.read_u16()?;
        let characteristics = cursor.read_u32()?;

        sections.push(PeSectionHeader {
            name,
            virtual_size,
            virtual_address,
            size_of_raw_data,
            pointer_to_raw_data,
            pointer_to_relocations,
            pointer_to_line_numbers,
            number_of_relocations,
            number_of_line_numbers,
            characteristics,
        });
    }

    Ok(sections)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a minimal valid PE32+ binary in memory for testing.
    ///
    /// Layout:
    /// 0x000: DOS header (64 bytes)
    /// 0x040: DOS stub (skip)
    /// 0x080: PE signature (4 bytes)
    /// 0x084: COFF header (20 bytes)
    /// 0x098: Optional header PE32+ (112 + 16*8 = 240 bytes)
    /// 0x188: Section headers (3 * 40 = 120 bytes)
    /// 0x200: .text section data (512 bytes)
    /// 0x400: .rdata section data (512 bytes) — contains import/export tables
    /// 0x600: .data section data (512 bytes)
    fn build_test_pe() -> Vec<u8> {
        let mut buf = vec![0u8; 0x800]; // 2048 bytes total

        let pe_offset: u32 = 0x80;
        let opt_hdr_size: u16 = 240; // PE32+ optional header
        let text_rva: u32 = 0x1000;
        let rdata_rva: u32 = 0x2000;
        let data_rva: u32 = 0x3000;
        let text_file_off: u32 = 0x200;
        let rdata_file_off: u32 = 0x400;
        let data_file_off: u32 = 0x600;

        // --- DOS Header ---
        // e_magic = 'MZ'
        buf[0] = b'M';
        buf[1] = b'Z';
        // e_lfanew at offset 0x3C
        buf[0x3C..0x40].copy_from_slice(&pe_offset.to_le_bytes());

        // --- PE Signature at 0x80 ---
        buf[0x80..0x84].copy_from_slice(&PE_SIGNATURE.to_le_bytes());

        // --- COFF Header at 0x84 (20 bytes) ---
        let coff_off = 0x84usize;
        // Machine = AMD64
        buf[coff_off..coff_off + 2].copy_from_slice(&IMAGE_FILE_MACHINE_AMD64.to_le_bytes());
        // NumberOfSections = 3
        buf[coff_off + 2..coff_off + 4].copy_from_slice(&3u16.to_le_bytes());
        // TimeDateStamp
        buf[coff_off + 4..coff_off + 8].copy_from_slice(&0x6000_0000u32.to_le_bytes());
        // PointerToSymbolTable = 0 (no symbols in this test)
        // NumberOfSymbols = 0
        // SizeOfOptionalHeader
        buf[coff_off + 16..coff_off + 18].copy_from_slice(&opt_hdr_size.to_le_bytes());
        // Characteristics: IMAGE_FILE_EXECUTABLE_IMAGE | IMAGE_FILE_LARGE_ADDRESS_AWARE
        buf[coff_off + 18..coff_off + 20].copy_from_slice(&0x0022u16.to_le_bytes());

        // --- Optional Header PE32+ at 0x98 ---
        let opt_off = 0x98usize;
        // Magic = PE32+
        buf[opt_off..opt_off + 2].copy_from_slice(&PE32PLUS_MAGIC.to_le_bytes());
        // MajorLinkerVersion, MinorLinkerVersion
        buf[opt_off + 2] = 14;
        buf[opt_off + 3] = 0;
        // SizeOfCode
        buf[opt_off + 4..opt_off + 8].copy_from_slice(&0x200u32.to_le_bytes());
        // SizeOfInitializedData
        buf[opt_off + 8..opt_off + 12].copy_from_slice(&0x400u32.to_le_bytes());
        // SizeOfUninitializedData = 0
        // AddressOfEntryPoint
        buf[opt_off + 16..opt_off + 20].copy_from_slice(&text_rva.to_le_bytes());
        // BaseOfCode
        buf[opt_off + 20..opt_off + 24].copy_from_slice(&text_rva.to_le_bytes());
        // ImageBase (u64 for PE32+)
        buf[opt_off + 24..opt_off + 32].copy_from_slice(&0x0000_0001_4000_0000u64.to_le_bytes());
        // SectionAlignment
        buf[opt_off + 32..opt_off + 36].copy_from_slice(&0x1000u32.to_le_bytes());
        // FileAlignment
        buf[opt_off + 36..opt_off + 40].copy_from_slice(&0x200u32.to_le_bytes());
        // MajorOperatingSystemVersion
        buf[opt_off + 40..opt_off + 42].copy_from_slice(&6u16.to_le_bytes());
        // MinorOperatingSystemVersion
        buf[opt_off + 42..opt_off + 44].copy_from_slice(&0u16.to_le_bytes());
        // MajorImageVersion = 0, MinorImageVersion = 0
        // MajorSubsystemVersion
        buf[opt_off + 48..opt_off + 50].copy_from_slice(&6u16.to_le_bytes());
        // MinorSubsystemVersion = 0
        // Win32VersionValue = 0
        // SizeOfImage
        buf[opt_off + 56..opt_off + 60].copy_from_slice(&0x4000u32.to_le_bytes());
        // SizeOfHeaders
        buf[opt_off + 60..opt_off + 64].copy_from_slice(&0x200u32.to_le_bytes());
        // CheckSum = 0
        // Subsystem = IMAGE_SUBSYSTEM_WINDOWS_CUI (3)
        buf[opt_off + 68..opt_off + 70].copy_from_slice(&3u16.to_le_bytes());
        // DllCharacteristics = 0x8160 (DYNAMIC_BASE | NX_COMPAT | TERMINAL_SERVER_AWARE | HIGH_ENTROPY_VA)
        buf[opt_off + 70..opt_off + 72].copy_from_slice(&0x8160u16.to_le_bytes());
        // Stack/Heap sizes (PE32+ = u64 each, 4 fields = 32 bytes)
        // SizeOfStackReserve
        buf[opt_off + 72..opt_off + 80].copy_from_slice(&0x100000u64.to_le_bytes());
        // SizeOfStackCommit
        buf[opt_off + 80..opt_off + 88].copy_from_slice(&0x1000u64.to_le_bytes());
        // SizeOfHeapReserve
        buf[opt_off + 88..opt_off + 96].copy_from_slice(&0x100000u64.to_le_bytes());
        // SizeOfHeapCommit
        buf[opt_off + 96..opt_off + 104].copy_from_slice(&0x1000u64.to_le_bytes());
        // LoaderFlags = 0
        // NumberOfRvaAndSizes = 16
        buf[opt_off + 108..opt_off + 112].copy_from_slice(&16u32.to_le_bytes());

        // Data directories start at opt_off + 112 (16 entries * 8 bytes = 128 bytes)
        let dd_off = opt_off + 112;
        // [0] Export: RVA = rdata_rva, Size = 0x50
        buf[dd_off..dd_off + 4].copy_from_slice(&rdata_rva.to_le_bytes());
        buf[dd_off + 4..dd_off + 8].copy_from_slice(&0x50u32.to_le_bytes());
        // [1] Import: RVA = rdata_rva + 0x60, Size = 0x3C (3 entries * 20 bytes, including null terminator)
        let import_rva = rdata_rva + 0x60;
        buf[dd_off + 8..dd_off + 12].copy_from_slice(&import_rva.to_le_bytes());
        buf[dd_off + 12..dd_off + 16].copy_from_slice(&0x3Cu32.to_le_bytes());
        // [2..15] = zeros (already zeroed)

        // --- Section Headers at 0x188 (3 sections * 40 bytes = 120 bytes) ---
        let sh_off = 0x188usize;

        // .text section
        write_section_header(
            &mut buf,
            sh_off,
            b".text\0\0\0",
            0x200, // virtual_size
            text_rva,
            0x200, // size_of_raw_data
            text_file_off,
            0x6000_0020, // CODE | EXECUTE | READ
        );

        // .rdata section
        write_section_header(
            &mut buf,
            sh_off + 40,
            b".rdata\0\0",
            0x200,
            rdata_rva,
            0x200,
            rdata_file_off,
            0x4000_0040, // INITIALIZED_DATA | READ
        );

        // .data section
        write_section_header(
            &mut buf,
            sh_off + 80,
            b".data\0\0\0",
            0x100,
            data_rva,
            0x200,
            data_file_off,
            0xC000_0040, // INITIALIZED_DATA | READ | WRITE
        );

        // --- Export table in .rdata at rdata_file_off ---
        // Export directory table (40 bytes)
        let exp_off = rdata_file_off as usize;
        // Characteristics = 0
        // TimeDateStamp = 0
        // MajorVersion = 0, MinorVersion = 0
        // Name RVA (DLL name) — we'll put it at rdata_rva + 0x28
        let dll_name_rva = rdata_rva + 0x28;
        buf[exp_off + 12..exp_off + 16].copy_from_slice(&dll_name_rva.to_le_bytes());
        // OrdinalBase = 1
        buf[exp_off + 16..exp_off + 20].copy_from_slice(&1u32.to_le_bytes());
        // NumberOfFunctions = 2
        buf[exp_off + 20..exp_off + 24].copy_from_slice(&2u32.to_le_bytes());
        // NumberOfNames = 2
        buf[exp_off + 24..exp_off + 28].copy_from_slice(&2u32.to_le_bytes());
        // AddressOfFunctions = rdata_rva + 0x38
        let eat_rva = rdata_rva + 0x38;
        buf[exp_off + 28..exp_off + 32].copy_from_slice(&eat_rva.to_le_bytes());
        // AddressOfNames = rdata_rva + 0x40
        let names_rva = rdata_rva + 0x40;
        buf[exp_off + 32..exp_off + 36].copy_from_slice(&names_rva.to_le_bytes());
        // AddressOfNameOrdinals = rdata_rva + 0x48
        let ords_rva = rdata_rva + 0x48;
        buf[exp_off + 36..exp_off + 40].copy_from_slice(&ords_rva.to_le_bytes());

        // DLL name at rdata_file_off + 0x28
        let dll_name = b"test.dll\0";
        buf[exp_off + 0x28..exp_off + 0x28 + dll_name.len()].copy_from_slice(dll_name);

        // EAT at rdata_file_off + 0x38: [rva_func1, rva_func2]
        buf[exp_off + 0x38..exp_off + 0x3C].copy_from_slice(&(text_rva).to_le_bytes()); // func1 at .text start
        buf[exp_off + 0x3C..exp_off + 0x40].copy_from_slice(&(text_rva + 0x10).to_le_bytes()); // func2

        // Name pointers at rdata_file_off + 0x40: [name1_rva, name2_rva]
        // name1 at rdata_rva + 0x4C, name2 at rdata_rva + 0x52
        let name1_rva = rdata_rva + 0x4C;
        let name2_rva = rdata_rva + 0x56;
        buf[exp_off + 0x40..exp_off + 0x44].copy_from_slice(&name1_rva.to_le_bytes());
        buf[exp_off + 0x44..exp_off + 0x48].copy_from_slice(&name2_rva.to_le_bytes());

        // Ordinal table at rdata_file_off + 0x48: [0, 1]
        buf[exp_off + 0x48..exp_off + 0x4A].copy_from_slice(&0u16.to_le_bytes());
        buf[exp_off + 0x4A..exp_off + 0x4C].copy_from_slice(&1u16.to_le_bytes());

        // Function names
        let name1 = b"AddFunc\0";
        let name2 = b"SubFunc\0";
        buf[exp_off + 0x4C..exp_off + 0x4C + name1.len()].copy_from_slice(name1);
        buf[exp_off + 0x56..exp_off + 0x56 + name2.len()].copy_from_slice(name2);

        // --- Import table in .rdata at rdata_file_off + 0x60 ---
        let imp_off = rdata_file_off as usize + 0x60;

        // Import directory entry 1: KERNEL32.dll
        // OriginalFirstThunk (ILT) RVA = rdata_rva + 0xA0
        let ilt_rva = rdata_rva + 0xA0;
        buf[imp_off..imp_off + 4].copy_from_slice(&ilt_rva.to_le_bytes());
        // TimeDateStamp = 0
        // ForwarderChain = 0
        // Name RVA = rdata_rva + 0xC0
        let k32_name_rva = rdata_rva + 0xC0;
        buf[imp_off + 12..imp_off + 16].copy_from_slice(&k32_name_rva.to_le_bytes());
        // FirstThunk (IAT) RVA = same as ILT for simplicity
        buf[imp_off + 16..imp_off + 20].copy_from_slice(&ilt_rva.to_le_bytes());

        // Import directory entry 2: null terminator (all zeros)
        // Already zeroed

        // ILT at rdata_file_off + 0xA0 (PE32+ = 8 bytes per entry)
        let ilt_off = rdata_file_off as usize + 0xA0;
        // Entry 1: import by name, Hint/Name RVA = rdata_rva + 0xD0
        let hn_rva1 = rdata_rva + 0xD0;
        buf[ilt_off..ilt_off + 8].copy_from_slice(&(hn_rva1 as u64).to_le_bytes());
        // Entry 2: import by ordinal, ordinal 42 (bit 63 set)
        let ord_entry: u64 = (1u64 << 63) | 42;
        buf[ilt_off + 8..ilt_off + 16].copy_from_slice(&ord_entry.to_le_bytes());
        // Entry 3: null terminator (8 zero bytes, already zeroed)

        // DLL name "KERNEL32.dll\0" at rdata_file_off + 0xC0
        let k32_name = b"KERNEL32.dll\0";
        buf[rdata_file_off as usize + 0xC0..rdata_file_off as usize + 0xC0 + k32_name.len()]
            .copy_from_slice(k32_name);

        // Hint/Name entry at rdata_file_off + 0xD0: hint(u16) + name(nul-terminated)
        let hn_off = rdata_file_off as usize + 0xD0;
        buf[hn_off..hn_off + 2].copy_from_slice(&0x01F4u16.to_le_bytes()); // hint = 500
        let func_name = b"ExitProcess\0";
        buf[hn_off + 2..hn_off + 2 + func_name.len()].copy_from_slice(func_name);

        buf
    }

    const TEST_DATA_DIRECTORY_OFF: usize = 0x98 + 112;
    const TEST_EXPORT_DIRECTORY_SIZE_OFF: usize = TEST_DATA_DIRECTORY_OFF + 4;
    const TEST_IMPORT_DIRECTORY_SIZE_OFF: usize = TEST_DATA_DIRECTORY_OFF + 12;
    const TEST_RDATA_FILE_OFF: usize = 0x400;
    const TEST_RDATA_RVA: u32 = 0x2000;
    const TEST_EXPORT_DIRECTORY_OFF: usize = TEST_RDATA_FILE_OFF;
    const TEST_EXPORT_NUMBER_OF_FUNCTIONS_OFF: usize = TEST_EXPORT_DIRECTORY_OFF + 20;
    const TEST_EXPORT_NUMBER_OF_NAMES_OFF: usize = TEST_EXPORT_DIRECTORY_OFF + 24;
    const TEST_EXPORT_ORDINAL_TABLE_OFF: usize = TEST_RDATA_FILE_OFF + 0x48;
    const TEST_EXPORT_NAME1_OFF: usize = TEST_RDATA_FILE_OFF + 0x4C;
    const TEST_IMPORT_DESCRIPTOR_OFF: usize = TEST_RDATA_FILE_OFF + 0x60;
    const TEST_IMPORT_DLL_NAME_OFF: usize = TEST_RDATA_FILE_OFF + 0xC0;

    fn write_u32_at(buf: &mut [u8], offset: usize, value: u32) {
        buf[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
    }

    /// Helper to write a 40-byte PE section header at the given offset.
    #[allow(clippy::too_many_arguments)]
    fn write_section_header(
        buf: &mut [u8],
        offset: usize,
        name: &[u8; 8],
        virtual_size: u32,
        virtual_address: u32,
        size_of_raw_data: u32,
        pointer_to_raw_data: u32,
        characteristics: u32,
    ) {
        buf[offset..offset + 8].copy_from_slice(name);
        buf[offset + 8..offset + 12].copy_from_slice(&virtual_size.to_le_bytes());
        buf[offset + 12..offset + 16].copy_from_slice(&virtual_address.to_le_bytes());
        buf[offset + 16..offset + 20].copy_from_slice(&size_of_raw_data.to_le_bytes());
        buf[offset + 20..offset + 24].copy_from_slice(&pointer_to_raw_data.to_le_bytes());
        // pointer_to_relocations = 0 (offset + 24..28)
        // pointer_to_line_numbers = 0 (offset + 28..32)
        // number_of_relocations = 0 (offset + 32..34)
        // number_of_line_numbers = 0 (offset + 34..36)
        buf[offset + 36..offset + 40].copy_from_slice(&characteristics.to_le_bytes());
    }

    #[test]
    fn test_pe_parse_dos_header() {
        let data = build_test_pe();
        let pe = Pe::parse(&data).expect("should parse test PE");
        assert_eq!(pe.dos_header.e_magic, DOS_MAGIC);
        assert_eq!(pe.dos_header.e_lfanew, 0x80);
    }

    #[test]
    fn test_pe_parse_coff_header() {
        let data = build_test_pe();
        let pe = Pe::parse(&data).expect("should parse test PE");
        assert_eq!(pe.coff_header.machine, IMAGE_FILE_MACHINE_AMD64);
        assert_eq!(pe.coff_header.number_of_sections, 3);
        assert_eq!(pe.coff_header.time_date_stamp, 0x6000_0000);
        assert_eq!(pe.coff_header.characteristics, 0x0022);
    }

    #[test]
    fn test_pe_parse_optional_header() {
        let data = build_test_pe();
        let pe = Pe::parse(&data).expect("should parse test PE");
        let oh = pe.optional_header.as_ref().expect("should have optional header");
        assert_eq!(oh.format, PeFormat::Pe32Plus);
        assert_eq!(oh.address_of_entry_point, 0x1000);
        assert_eq!(oh.image_base, 0x0000_0001_4000_0000);
        assert_eq!(oh.section_alignment, 0x1000);
        assert_eq!(oh.file_alignment, 0x200);
        assert_eq!(oh.subsystem, 3); // WINDOWS_CUI
        assert_eq!(oh.number_of_rva_and_sizes, 16);
        assert_eq!(oh.data_directories.len(), 16);
    }

    #[test]
    fn test_pe_parse_sections() {
        let data = build_test_pe();
        let pe = Pe::parse(&data).expect("should parse test PE");
        assert_eq!(pe.sections.len(), 3);

        assert_eq!(pe.sections[0].name, ".text");
        assert_eq!(pe.sections[0].virtual_address, 0x1000);
        assert_eq!(pe.sections[0].size_of_raw_data, 0x200);

        assert_eq!(pe.sections[1].name, ".rdata");
        assert_eq!(pe.sections[1].virtual_address, 0x2000);

        assert_eq!(pe.sections[2].name, ".data");
        assert_eq!(pe.sections[2].virtual_address, 0x3000);
    }

    #[test]
    fn test_pe_find_section() {
        let data = build_test_pe();
        let pe = Pe::parse(&data).expect("should parse test PE");

        let text = pe.find_section(".text");
        assert!(text.is_some());
        assert_eq!(text.unwrap().virtual_address, 0x1000);

        let missing = pe.find_section(".bss");
        assert!(missing.is_none());
    }

    #[test]
    fn test_pe_entry_point_and_image_base() {
        let data = build_test_pe();
        let pe = Pe::parse(&data).expect("should parse test PE");
        assert_eq!(pe.entry_point(), 0x1000);
        assert_eq!(pe.image_base(), 0x0000_0001_4000_0000);
    }

    #[test]
    fn test_pe_section_data() {
        let data = build_test_pe();
        let pe = Pe::parse(&data).expect("should parse test PE");
        let text = pe.find_section(".text").expect("should find .text");
        let text_data = pe.section_data(text).expect("should get .text data");
        assert_eq!(text_data.len(), 0x200);
    }

    #[test]
    fn test_pe_section_data_rejects_out_of_bounds_raw_data() {
        let data = build_test_pe();
        let pe = Pe::parse(&data).expect("should parse test PE");
        let mut text = pe.find_section(".text").expect("should find .text").clone();
        text.pointer_to_raw_data = 0x700;
        text.size_of_raw_data = 0x200;

        let err = pe.section_data(&text).expect_err("section data should be out of bounds");
        assert!(matches!(
            err,
            ParseError::DataOutOfBounds { offset: 0x700, end: 0x900, file_size: 0x800 }
        ));
    }

    #[test]
    fn test_pe_rva_to_offset() {
        let data = build_test_pe();
        let pe = Pe::parse(&data).expect("should parse test PE");

        // .text: RVA 0x1000, file offset 0x200
        assert_eq!(pe.rva_to_offset(0x1000).unwrap(), 0x200);
        assert_eq!(pe.rva_to_offset(0x1010).unwrap(), 0x210);

        // .rdata: RVA 0x2000, file offset 0x400
        assert_eq!(pe.rva_to_offset(0x2000).unwrap(), 0x400);

        // Invalid RVA
        assert!(pe.rva_to_offset(0x9000).is_err());
    }

    #[test]
    fn test_pe_rva_to_offset_rejects_overflowing_section_range() {
        let data = build_test_pe();
        let mut pe = Pe::parse(&data).expect("should parse test PE");
        let text = pe.sections.iter_mut().find(|s| s.name == ".text").unwrap();
        text.virtual_address = u32::MAX - 0x10;
        text.virtual_size = 0x20;

        let err = pe.rva_to_offset(u32::MAX).expect_err("overflowing section range is invalid");
        assert!(matches!(err, ParseError::InvalidRva { rva: u32::MAX }));
    }

    #[test]
    fn test_pe_rva_to_offset_rejects_overflowing_file_offset() {
        let data = build_test_pe();
        let mut pe = Pe::parse(&data).expect("should parse test PE");
        let text = pe.sections.iter_mut().find(|s| s.name == ".text").unwrap();
        text.pointer_to_raw_data = u32::MAX - 0x10;

        let err = pe.rva_to_offset(0x1020).expect_err("file offset should overflow");
        assert!(matches!(err, ParseError::DataOutOfBounds { .. }));
    }

    #[test]
    fn test_pe_rva_to_offset_rejects_out_of_bounds_file_offset() {
        let data = build_test_pe();
        let mut pe = Pe::parse(&data).expect("should parse test PE");
        let text = pe.sections.iter_mut().find(|s| s.name == ".text").unwrap();
        text.pointer_to_raw_data = 0x900;

        let err = pe.rva_to_offset(0x1000).expect_err("file offset should be out of bounds");
        assert!(matches!(
            err,
            ParseError::DataOutOfBounds { offset: 0x900, end: 0x901, file_size: 0x800 }
        ));
    }

    #[test]
    fn test_pe_exports() {
        let data = build_test_pe();
        let pe = Pe::parse(&data).expect("should parse test PE");
        let exports = pe.exports().expect("should parse exports");
        assert_eq!(exports.len(), 2);

        assert_eq!(exports[0].ordinal, 1);
        assert_eq!(exports[0].name, Some("AddFunc"));
        assert_eq!(exports[0].rva, 0x1000);
        assert!(!exports[0].is_forwarder);

        assert_eq!(exports[1].ordinal, 2);
        assert_eq!(exports[1].name, Some("SubFunc"));
        assert_eq!(exports[1].rva, 0x1010);
        assert!(!exports[1].is_forwarder);
    }

    #[test]
    fn test_pe_imports() {
        let data = build_test_pe();
        let pe = Pe::parse(&data).expect("should parse test PE");
        let imports = pe.imports().expect("should parse imports");
        assert_eq!(imports.len(), 1);
        assert_eq!(imports[0].dll_name, "KERNEL32.dll");
        assert_eq!(imports[0].functions.len(), 2);

        match &imports[0].functions[0] {
            ImportFunction::ByName { hint, name } => {
                assert_eq!(*hint, 500);
                assert_eq!(*name, "ExitProcess");
            }
            other => panic!("expected ByName, got {:?}", other),
        }

        match &imports[0].functions[1] {
            ImportFunction::ByOrdinal(ord) => assert_eq!(*ord, 42),
            other => panic!("expected ByOrdinal, got {:?}", other),
        }
    }

    #[test]
    fn test_pe_import_directory_truncated_fails_closed() {
        let mut data = build_test_pe();
        write_u32_at(&mut data, TEST_IMPORT_DIRECTORY_SIZE_OFF, 19);

        let pe = Pe::parse(&data).expect("should parse test PE");
        let err = pe.imports().unwrap_err();
        assert!(matches!(err, ParseError::InvalidImportEntry { .. }));
    }

    #[test]
    fn test_pe_import_directory_without_null_descriptor_fails_closed() {
        let mut data = build_test_pe();
        write_u32_at(&mut data, TEST_IMPORT_DIRECTORY_SIZE_OFF, IMPORT_DIR_ENTRY_SIZE as u32);

        let pe = Pe::parse(&data).expect("should parse test PE");
        let err = pe.imports().unwrap_err();
        assert!(matches!(err, ParseError::InvalidImportEntry { .. }));
    }

    #[test]
    fn test_pe_import_dll_name_without_nul_fails_closed() {
        let mut data = build_test_pe();
        data[TEST_IMPORT_DLL_NAME_OFF..TEST_RDATA_FILE_OFF + 0x200].fill(b'A');

        let pe = Pe::parse(&data).expect("should parse test PE");
        let err = pe.imports().unwrap_err();
        assert!(matches!(err, ParseError::UnexpectedEof(_)));
    }

    #[test]
    fn test_pe_import_lookup_table_without_null_entry_fails_closed() {
        let mut data = build_test_pe();
        let ilt_rva = TEST_RDATA_RVA + 0x100;
        let ilt_off = TEST_RDATA_FILE_OFF + 0x100;
        write_u32_at(&mut data, TEST_IMPORT_DESCRIPTOR_OFF, ilt_rva);
        write_u32_at(&mut data, TEST_IMPORT_DESCRIPTOR_OFF + 16, ilt_rva);

        let ordinal_entry = (1u64 << 63) | 7;
        for chunk in data[ilt_off..TEST_RDATA_FILE_OFF + 0x200].chunks_exact_mut(8) {
            chunk.copy_from_slice(&ordinal_entry.to_le_bytes());
        }

        let pe = Pe::parse(&data).expect("should parse test PE");
        let err = pe.imports().unwrap_err();
        assert!(matches!(err, ParseError::InvalidImportEntry { .. }));
    }

    #[test]
    fn test_pe_export_directory_truncated_fails_closed() {
        let mut data = build_test_pe();
        write_u32_at(&mut data, TEST_EXPORT_DIRECTORY_SIZE_OFF, 39);

        let pe = Pe::parse(&data).expect("should parse test PE");
        let err = pe.exports().unwrap_err();
        assert!(matches!(err, ParseError::InvalidExportTable { .. }));
    }

    #[test]
    fn test_pe_export_address_table_out_of_bounds_fails_closed() {
        let mut data = build_test_pe();
        write_u32_at(&mut data, TEST_EXPORT_NUMBER_OF_FUNCTIONS_OFF, 128);
        write_u32_at(&mut data, TEST_EXPORT_NUMBER_OF_NAMES_OFF, 0);

        let pe = Pe::parse(&data).expect("should parse test PE");
        let err = pe.exports().unwrap_err();
        assert!(matches!(err, ParseError::DataOutOfBounds { .. } | ParseError::InvalidRva { .. }));
    }

    #[test]
    fn test_pe_export_address_table_size_overflow_fails_closed() {
        let mut data = build_test_pe();
        write_u32_at(&mut data, TEST_EXPORT_NUMBER_OF_FUNCTIONS_OFF, 0x4000_0000);
        write_u32_at(&mut data, TEST_EXPORT_NUMBER_OF_NAMES_OFF, 0);

        let pe = Pe::parse(&data).expect("should parse test PE");
        let err = pe.exports().unwrap_err();
        assert!(matches!(err, ParseError::InvalidExportTable { .. }));
    }

    #[test]
    fn test_pe_export_name_ordinal_out_of_bounds_fails_closed() {
        let mut data = build_test_pe();
        data[TEST_EXPORT_ORDINAL_TABLE_OFF..TEST_EXPORT_ORDINAL_TABLE_OFF + 2]
            .copy_from_slice(&5u16.to_le_bytes());

        let pe = Pe::parse(&data).expect("should parse test PE");
        let err = pe.exports().unwrap_err();
        assert!(matches!(err, ParseError::InvalidExportTable { .. }));
    }

    #[test]
    fn test_pe_export_name_without_nul_fails_closed() {
        let mut data = build_test_pe();
        data[TEST_EXPORT_NAME1_OFF..TEST_RDATA_FILE_OFF + 0x200].fill(b'B');

        let pe = Pe::parse(&data).expect("should parse test PE");
        let err = pe.exports().unwrap_err();
        assert!(matches!(err, ParseError::UnexpectedEof(_)));
    }

    #[test]
    fn test_pe_is_pe() {
        assert!(Pe::is_pe(&[b'M', b'Z', 0, 0]));
        assert!(!Pe::is_pe(&[0x7f, b'E', b'L', b'F'])); // ELF
        assert!(!Pe::is_pe(&[0, 0])); // too short
        assert!(!Pe::is_pe(b"PK")); // ZIP
    }

    #[test]
    fn test_pe_invalid_dos_magic() {
        let mut data = build_test_pe();
        data[0] = 0x00; // corrupt MZ magic
        let err = Pe::parse(&data).unwrap_err();
        assert!(matches!(err, ParseError::InvalidDosMagic(_)));
    }

    #[test]
    fn test_pe_invalid_pe_signature() {
        let mut data = build_test_pe();
        // Corrupt PE signature at offset 0x80
        data[0x80] = 0xFF;
        let err = Pe::parse(&data).unwrap_err();
        assert!(matches!(err, ParseError::InvalidPeSignature(_)));
    }

    #[test]
    fn test_pe_truncated_returns_error() {
        let err = Pe::parse(b"MZ").unwrap_err();
        assert!(matches!(err, ParseError::UnexpectedEof(_)));
    }

    #[test]
    fn test_pe_no_optional_header() {
        // Build a minimal COFF object (no optional header)
        let mut buf = vec![0u8; 256];

        // DOS header
        buf[0] = b'M';
        buf[1] = b'Z';
        let pe_off: u32 = 0x40;
        buf[0x3C..0x40].copy_from_slice(&pe_off.to_le_bytes());

        // PE sig
        buf[0x40..0x44].copy_from_slice(&PE_SIGNATURE.to_le_bytes());

        // COFF header
        let coff = 0x44usize;
        buf[coff..coff + 2].copy_from_slice(&IMAGE_FILE_MACHINE_AMD64.to_le_bytes());
        // NumberOfSections = 0
        // SizeOfOptionalHeader = 0

        let pe = Pe::parse(&buf).expect("should parse minimal PE/COFF");
        assert!(pe.optional_header.is_none());
        assert!(pe.sections.is_empty());
        assert_eq!(pe.entry_point(), 0);
        assert_eq!(pe.image_base(), 0);
        // imports/exports should return empty
        assert!(pe.imports().unwrap().is_empty());
        assert!(pe.exports().unwrap().is_empty());
    }

    #[test]
    fn test_pe_coff_symbols() {
        // Build a PE with a COFF symbol table
        let mut buf = vec![0u8; 512];

        // DOS header
        buf[0] = b'M';
        buf[1] = b'Z';
        let pe_off: u32 = 0x40;
        buf[0x3C..0x40].copy_from_slice(&pe_off.to_le_bytes());

        // PE sig
        buf[0x40..0x44].copy_from_slice(&PE_SIGNATURE.to_le_bytes());

        // COFF header at 0x44
        let coff = 0x44usize;
        buf[coff..coff + 2].copy_from_slice(&IMAGE_FILE_MACHINE_I386.to_le_bytes());
        // NumberOfSections = 0
        // PointerToSymbolTable = 0x80
        let sym_off: u32 = 0x80;
        buf[coff + 8..coff + 12].copy_from_slice(&sym_off.to_le_bytes());
        // NumberOfSymbols = 2
        buf[coff + 12..coff + 16].copy_from_slice(&2u32.to_le_bytes());
        // SizeOfOptionalHeader = 0

        // Symbol table at 0x80 (2 entries * 18 bytes = 36 bytes)
        let sym = sym_off as usize;

        // Symbol 0: short name "_main" (fits in 8 bytes)
        let name0 = b"_main\0\0\0";
        buf[sym..sym + 8].copy_from_slice(name0);
        buf[sym + 8..sym + 12].copy_from_slice(&0x1000u32.to_le_bytes()); // value
        buf[sym + 12..sym + 14].copy_from_slice(&1u16.to_le_bytes()); // section 1
        buf[sym + 14..sym + 16].copy_from_slice(&0x20u16.to_le_bytes()); // type = function
        buf[sym + 16] = IMAGE_SYM_CLASS_EXTERNAL; // storage class
        buf[sym + 17] = 0; // aux symbols

        // Symbol 1: long name via string table (first 4 bytes = 0, next 4 = offset)
        buf[sym + 18..sym + 22].copy_from_slice(&[0, 0, 0, 0]); // zeroes
        buf[sym + 22..sym + 26].copy_from_slice(&4u32.to_le_bytes()); // string offset = 4
        buf[sym + 26..sym + 30].copy_from_slice(&0x2000u32.to_le_bytes()); // value
        buf[sym + 30..sym + 32].copy_from_slice(&1u16.to_le_bytes()); // section 1
        buf[sym + 32..sym + 34].copy_from_slice(&0x00u16.to_le_bytes()); // type = null
        buf[sym + 34] = IMAGE_SYM_CLASS_STATIC; // storage class
        buf[sym + 35] = 0; // aux symbols

        // String table starts at sym + 36 (= sym_off + 2 * 18)
        let strtab = sym + 36;
        // First 4 bytes = size of string table (including size field)
        let long_name = b"_very_long_symbol_name\0";
        let strtab_size = (4 + long_name.len()) as u32;
        buf[strtab..strtab + 4].copy_from_slice(&strtab_size.to_le_bytes());
        buf[strtab + 4..strtab + 4 + long_name.len()].copy_from_slice(long_name);

        let pe = Pe::parse(&buf).expect("should parse PE with symbols");
        let symbols = pe.symbols().expect("should parse symbols");
        assert_eq!(symbols.len(), 2);

        assert_eq!(symbols[0].name, "_main");
        assert_eq!(symbols[0].value, 0x1000);
        assert!(symbols[0].is_external());
        assert!(symbols[0].is_function());

        assert_eq!(symbols[1].name, "_very_long_symbol_name");
        assert_eq!(symbols[1].value, 0x2000);
        assert!(symbols[1].is_static());
        assert!(!symbols[1].is_function());
    }

    #[test]
    fn test_pe_data_directory_entries() {
        let data = build_test_pe();
        let pe = Pe::parse(&data).expect("should parse test PE");
        let oh = pe.optional_header.as_ref().unwrap();

        // Export directory
        assert_ne!(oh.data_directories[0].virtual_address, 0);
        assert_ne!(oh.data_directories[0].size, 0);

        // Import directory
        assert_ne!(oh.data_directories[1].virtual_address, 0);
        assert_ne!(oh.data_directories[1].size, 0);

        // Others should be zero
        for i in 2..16 {
            assert_eq!(oh.data_directories[i].virtual_address, 0);
            assert_eq!(oh.data_directories[i].size, 0);
        }
    }

    #[test]
    fn test_pe_section_characteristics() {
        let data = build_test_pe();
        let pe = Pe::parse(&data).expect("should parse test PE");

        // .text: CODE | EXECUTE | READ
        assert_eq!(pe.sections[0].characteristics, 0x6000_0020);
        // .rdata: INITIALIZED_DATA | READ
        assert_eq!(pe.sections[1].characteristics, 0x4000_0040);
        // .data: INITIALIZED_DATA | READ | WRITE
        assert_eq!(pe.sections[2].characteristics, 0xC000_0040);
    }

    /// Build a minimal valid PE32 (32-bit) binary for testing.
    ///
    /// Layout:
    /// 0x000: DOS header (64 bytes)
    /// 0x080: PE signature (4 bytes)
    /// 0x084: COFF header (20 bytes)
    /// 0x098: Optional header PE32 (224 bytes: 96 standard + 128 data dirs)
    /// 0x178: Section headers (1 * 40 = 40 bytes)
    /// 0x200: .text section data (512 bytes)
    fn build_test_pe32() -> Vec<u8> {
        let mut buf = vec![0u8; 0x400]; // 1024 bytes

        let pe_offset: u32 = 0x80;
        let opt_hdr_size: u16 = 224; // PE32 optional header
        let text_rva: u32 = 0x1000;
        let text_file_off: u32 = 0x200;

        // --- DOS Header ---
        buf[0] = b'M';
        buf[1] = b'Z';
        buf[0x3C..0x40].copy_from_slice(&pe_offset.to_le_bytes());

        // --- PE Signature ---
        buf[0x80..0x84].copy_from_slice(&PE_SIGNATURE.to_le_bytes());

        // --- COFF Header at 0x84 ---
        let coff_off = 0x84usize;
        buf[coff_off..coff_off + 2].copy_from_slice(&IMAGE_FILE_MACHINE_I386.to_le_bytes());
        buf[coff_off + 2..coff_off + 4].copy_from_slice(&1u16.to_le_bytes()); // 1 section
        buf[coff_off + 4..coff_off + 8].copy_from_slice(&0x5F00_0000u32.to_le_bytes());
        buf[coff_off + 16..coff_off + 18].copy_from_slice(&opt_hdr_size.to_le_bytes());
        buf[coff_off + 18..coff_off + 20].copy_from_slice(&0x0102u16.to_le_bytes()); // EXECUTABLE | 32BIT

        // --- Optional Header PE32 at 0x98 ---
        let opt_off = 0x98usize;
        buf[opt_off..opt_off + 2].copy_from_slice(&PE32_MAGIC.to_le_bytes());
        buf[opt_off + 2] = 10; // major linker version
        buf[opt_off + 3] = 0;
        // SizeOfCode
        buf[opt_off + 4..opt_off + 8].copy_from_slice(&0x200u32.to_le_bytes());
        // AddressOfEntryPoint
        buf[opt_off + 16..opt_off + 20].copy_from_slice(&text_rva.to_le_bytes());
        // BaseOfCode
        buf[opt_off + 20..opt_off + 24].copy_from_slice(&text_rva.to_le_bytes());
        // BaseOfData (PE32 only, at offset 24)
        buf[opt_off + 24..opt_off + 28].copy_from_slice(&0x2000u32.to_le_bytes());
        // ImageBase (u32 for PE32)
        buf[opt_off + 28..opt_off + 32].copy_from_slice(&0x0040_0000u32.to_le_bytes());
        // SectionAlignment
        buf[opt_off + 32..opt_off + 36].copy_from_slice(&0x1000u32.to_le_bytes());
        // FileAlignment
        buf[opt_off + 36..opt_off + 40].copy_from_slice(&0x200u32.to_le_bytes());
        // MajorOperatingSystemVersion
        buf[opt_off + 40..opt_off + 42].copy_from_slice(&6u16.to_le_bytes());
        // MajorSubsystemVersion
        buf[opt_off + 48..opt_off + 50].copy_from_slice(&6u16.to_le_bytes());
        // SizeOfImage
        buf[opt_off + 56..opt_off + 60].copy_from_slice(&0x2000u32.to_le_bytes());
        // SizeOfHeaders
        buf[opt_off + 60..opt_off + 64].copy_from_slice(&0x200u32.to_le_bytes());
        // Subsystem = WINDOWS_GUI (2)
        buf[opt_off + 68..opt_off + 70].copy_from_slice(&2u16.to_le_bytes());
        // Stack/heap sizes (PE32 = u32 each, 4 fields = 16 bytes, offset 72..88)
        buf[opt_off + 72..opt_off + 76].copy_from_slice(&0x100000u32.to_le_bytes());
        buf[opt_off + 76..opt_off + 80].copy_from_slice(&0x1000u32.to_le_bytes());
        buf[opt_off + 80..opt_off + 84].copy_from_slice(&0x100000u32.to_le_bytes());
        buf[opt_off + 84..opt_off + 88].copy_from_slice(&0x1000u32.to_le_bytes());
        // LoaderFlags = 0 (88..92)
        // NumberOfRvaAndSizes = 16 (92..96)
        buf[opt_off + 92..opt_off + 96].copy_from_slice(&16u32.to_le_bytes());
        // Data directories (16 * 8 = 128 bytes at offset 96..224) — all zeros

        // --- Section header at 0x178 ---
        let sh_off = 0x178usize;
        write_section_header(
            &mut buf,
            sh_off,
            b".text\0\0\0",
            0x200,
            text_rva,
            0x200,
            text_file_off,
            0x6000_0020, // CODE | EXECUTE | READ
        );

        buf
    }

    #[test]
    fn test_pe32_parse_header_and_sections() {
        let data = build_test_pe32();
        let pe = Pe::parse(&data).expect("should parse PE32 binary");

        assert_eq!(pe.dos_header.e_magic, DOS_MAGIC);
        assert_eq!(pe.coff_header.machine, IMAGE_FILE_MACHINE_I386);
        assert_eq!(pe.coff_header.number_of_sections, 1);

        let oh = pe.optional_header.as_ref().expect("should have optional header");
        assert_eq!(oh.format, PeFormat::Pe32);
        assert_eq!(oh.address_of_entry_point, 0x1000);
        assert_eq!(oh.image_base, 0x0040_0000);
        assert_eq!(oh.section_alignment, 0x1000);
        assert_eq!(oh.file_alignment, 0x200);
        assert_eq!(oh.subsystem, 2); // WINDOWS_GUI
        assert_eq!(oh.number_of_rva_and_sizes, 16);

        assert_eq!(pe.sections.len(), 1);
        assert_eq!(pe.sections[0].name, ".text");
        assert_eq!(pe.sections[0].virtual_address, 0x1000);
        assert_eq!(pe.sections[0].characteristics, 0x6000_0020);

        // No imports/exports in this minimal PE32
        assert!(pe.imports().unwrap().is_empty());
        assert!(pe.exports().unwrap().is_empty());
    }

    #[test]
    fn test_coff_symbol_helpers() {
        let sym = CoffSymbol {
            name: "test",
            value: 0,
            section_number: 1,
            sym_type: 0x20, // function derived type
            storage_class: IMAGE_SYM_CLASS_EXTERNAL,
            number_of_aux_symbols: 0,
        };
        assert!(sym.is_external());
        assert!(sym.is_function());
        assert!(!sym.is_static());

        let static_sym = CoffSymbol {
            name: "static_var",
            value: 0,
            section_number: 2,
            sym_type: 0,
            storage_class: IMAGE_SYM_CLASS_STATIC,
            number_of_aux_symbols: 0,
        };
        assert!(static_sym.is_static());
        assert!(!static_sym.is_external());
        assert!(!static_sym.is_function());
    }
}
