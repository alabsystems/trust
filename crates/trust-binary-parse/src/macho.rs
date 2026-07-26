// trust-binary-parse: top-level MachO parser
//
// Zero-copy: MachO<'a> borrows from the input byte slice. Section data,
// symbol names, and string table entries are all references into the
// original buffer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::constants::*;
use crate::error::ParseError;
use crate::header::{FatArch, MachHeader64, parse_fat_header, parse_header};
use crate::load_command::{
    LoadCommand, Section64, SegmentCommand64, SymtabCommand, parse_load_commands,
};
use crate::relocation::{Relocation, parse_relocations};
use crate::symbol::{Symbol, parse_symbols};

/// A parsed Mach-O 64-bit binary.
///
/// Borrows from the input byte slice for zero-copy access to section data,
/// symbol names, and string table entries.
#[derive(Debug)]
pub struct MachO<'a> {
    /// The raw file data.
    data: &'a [u8],
    /// The Mach-O header.
    pub(crate) header: MachHeader64,
    /// Whether bytes need swapping (big-endian file on LE host).
    pub(crate) swap: bool,
    /// Parsed load commands.
    pub(crate) load_commands: Vec<LoadCommand<'a>>,
}

impl<'a> MachO<'a> {
    /// Parse a Mach-O 64-bit binary from raw bytes.
    ///
    /// The input must start with `MH_MAGIC_64` or `MH_CIGAM_64`.
    /// For fat/universal binaries, use [`MachO::from_fat_slice`] first to
    /// locate the desired architecture slice.
    pub fn parse(data: &'a [u8]) -> Result<Self, ParseError> {
        let (header, swap) = parse_header(data)?;
        let load_commands = parse_load_commands(data, header.ncmds, swap)?;

        Ok(Self { data, header, swap, load_commands })
    }

    /// Check if the data starts with a fat binary header.
    #[must_use]
    pub fn is_fat(data: &[u8]) -> bool {
        if data.len() < 4 {
            return false;
        }
        let magic = u32::from_be_bytes([data[0], data[1], data[2], data[3]]);
        magic == FAT_MAGIC || magic == FAT_MAGIC_64
    }

    /// Parse the fat header to get architecture slices.
    pub fn parse_fat_arches(data: &[u8]) -> Result<Vec<FatArch>, ParseError> {
        parse_fat_header(data)
    }

    /// Parse a specific slice from a fat binary.
    ///
    /// The `arch` descriptor is obtained from [`MachO::parse_fat_arches`].
    pub fn from_fat_slice(data: &'a [u8], arch: &FatArch) -> Result<Self, ParseError> {
        let end = arch.offset.checked_add(arch.size).ok_or(ParseError::DataOutOfBounds {
            offset: arch.offset,
            end: u64::MAX,
            file_size: data.len(),
        })?;
        if end > data.len() as u64 {
            return Err(ParseError::DataOutOfBounds {
                offset: arch.offset,
                end,
                file_size: data.len(),
            });
        }
        let start = usize::try_from(arch.offset).map_err(|_| ParseError::DataOutOfBounds {
            offset: arch.offset,
            end,
            file_size: data.len(),
        })?;
        let end = usize::try_from(end).map_err(|_| ParseError::DataOutOfBounds {
            offset: arch.offset,
            end,
            file_size: data.len(),
        })?;
        Self::parse(&data[start..end])
    }

    /// The raw file data.
    #[must_use]
    pub fn data(&self) -> &'a [u8] {
        self.data
    }

    /// Mach-O CPU type from the file header.
    #[must_use]
    pub fn cputype(&self) -> i32 {
        self.header.cputype
    }

    /// Iterate over all segments.
    pub fn segments(&self) -> impl Iterator<Item = &SegmentCommand64<'a>> {
        self.load_commands.iter().filter_map(|lc| match lc {
            LoadCommand::Segment64(seg) => Some(seg),
            _ => None,
        })
    }

    /// Iterate over all sections across all segments.
    pub fn sections(&self) -> impl Iterator<Item = (&SegmentCommand64<'a>, &Section64<'a>)> {
        self.segments().flat_map(|seg| seg.sections.iter().map(move |sect| (seg, sect)))
    }

    /// Find a section by segment name and section name.
    #[must_use]
    pub fn find_section(&self, segname: &str, sectname: &str) -> Option<&Section64<'a>> {
        self.sections()
            .find(|(seg, sect)| seg.segname == segname && sect.sectname == sectname)
            .map(|(_, sect)| sect)
    }

    /// Find a segment by name.
    #[must_use]
    pub fn find_segment(&self, name: &str) -> Option<&SegmentCommand64<'a>> {
        self.segments().find(|seg| seg.segname == name)
    }

    /// Get the symtab command, if present.
    #[must_use]
    pub fn symtab_command(&self) -> Option<&SymtabCommand> {
        self.load_commands.iter().find_map(|lc| match lc {
            LoadCommand::Symtab(st) => Some(st),
            _ => None,
        })
    }

    /// Parse and return all symbols.
    ///
    /// Requires LC_SYMTAB to be present; returns an empty vec if not.
    pub fn symbols(&self) -> Result<Vec<Symbol<'a>>, ParseError> {
        match self.symtab_command() {
            Some(st) => {
                parse_symbols(self.data, st.symoff, st.nsyms, st.stroff, st.strsize, self.swap)
            }
            None => Ok(Vec::new()),
        }
    }

    /// Parse relocations for a specific section.
    pub fn section_relocations(
        &self,
        section: &Section64<'_>,
    ) -> Result<Vec<Relocation>, ParseError> {
        parse_relocations(self.data, section.reloff, section.nreloc, self.swap)
    }

    /// Get the entry point offset (from LC_MAIN), if present.
    #[must_use]
    pub fn entry_point(&self) -> Option<u64> {
        self.load_commands.iter().find_map(|lc| match lc {
            LoadCommand::EntryPoint(ep) => Some(ep.entryoff),
            _ => None,
        })
    }

    /// Get the UUID, if present.
    #[must_use]
    pub fn uuid(&self) -> Option<[u8; 16]> {
        self.load_commands.iter().find_map(|lc| match lc {
            LoadCommand::Uuid(uuid) => Some(*uuid),
            _ => None,
        })
    }

    /// Get all loaded dylib names.
    pub fn dylibs(&self) -> Vec<&str> {
        self.load_commands
            .iter()
            .filter_map(|lc| match lc {
                LoadCommand::Dylib(d) if d.cmd == LC_LOAD_DYLIB => Some(d.name.as_str()),
                _ => None,
            })
            .collect()
    }

    /// Get the __TEXT,__text section (main executable code).
    #[must_use]
    pub fn text_section(&self) -> Option<&Section64<'a>> {
        self.find_section("__TEXT", "__text")
    }

    /// Total number of load commands.
    #[must_use]
    pub fn num_load_commands(&self) -> usize {
        self.load_commands.len()
    }

    /// Whether this binary targets AArch64.
    #[must_use]
    pub fn is_aarch64(&self) -> bool {
        self.header.cputype == CPU_TYPE_ARM64
    }

    /// Whether this binary targets x86_64.
    #[must_use]
    pub fn is_x86_64(&self) -> bool {
        self.header.cputype == CPU_TYPE_X86_64
    }

    /// Get the build version, if present.
    #[must_use]
    pub fn build_version(&self) -> Option<&crate::load_command::BuildVersionCommand> {
        self.load_commands.iter().find_map(|lc| match lc {
            LoadCommand::BuildVersion(bv) => Some(bv),
            _ => None,
        })
    }

    /// Get the dysymtab command, if present.
    #[must_use]
    pub fn dysymtab_command(&self) -> Option<&crate::load_command::DysymtabCommand> {
        self.load_commands.iter().find_map(|lc| match lc {
            LoadCommand::Dysymtab(ds) => Some(ds),
            _ => None,
        })
    }

    /// Parse a fat/universal binary, automatically selecting the AArch64 slice.
    ///
    /// If the data is a fat binary, selects the ARM64 slice. If it is already
    /// a thin Mach-O 64-bit binary, parses it directly.
    pub fn parse_prefer_aarch64(data: &'a [u8]) -> Result<Self, ParseError> {
        if Self::is_fat(data) {
            let arches = Self::parse_fat_arches(data)?;
            // Prefer ARM64, fall back to first available slice.
            let arch = arches
                .iter()
                .find(|a| a.cputype == CPU_TYPE_ARM64)
                .or_else(|| arches.first())
                .ok_or_else(|| {
                    ParseError::UnsupportedFormat(
                        "fat binary contains no architecture slices".into(),
                    )
                })?;
            Self::from_fat_slice(data, arch)
        } else {
            Self::parse(data)
        }
    }

    /// Find the AArch64 slice descriptor in a fat binary's architecture list.
    ///
    /// Returns `None` if no ARM64 slice is present.
    #[must_use]
    pub fn find_aarch64_slice(arches: &[FatArch]) -> Option<&FatArch> {
        arches.iter().find(|a| a.cputype == CPU_TYPE_ARM64)
    }
}

impl Section64<'_> {
    /// Memory address of this section.
    #[must_use]
    pub fn addr(&self) -> u64 {
        self.addr
    }

    /// Size of this section in bytes.
    #[must_use]
    pub fn size(&self) -> u64 {
        self.size
    }

    /// File offset of this section.
    #[must_use]
    pub fn offset(&self) -> u32 {
        self.offset
    }
}

impl<'a> Symbol<'a> {
    /// Symbol name from the string table.
    #[must_use]
    pub fn name(&self) -> &'a str {
        self.name
    }

    /// Section number (1-based) or NO_SECT (0).
    #[must_use]
    pub fn section_index(&self) -> u8 {
        self.n_sect
    }

    /// Symbol value (address for defined symbols).
    #[must_use]
    pub fn value(&self) -> u64 {
        self.n_value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a synthetic minimal Mach-O binary with header, load commands, symtab, and strtab.
    fn build_synthetic_macho() -> Vec<u8> {
        let mut buf = Vec::new();

        // -- Mach-O header (32 bytes) --
        buf.extend_from_slice(&MH_MAGIC_64.to_le_bytes()); // magic
        buf.extend_from_slice(&(CPU_TYPE_ARM64 as u32).to_le_bytes()); // cputype
        buf.extend_from_slice(&(CPU_SUBTYPE_ARM64_ALL as u32).to_le_bytes()); // cpusubtype
        buf.extend_from_slice(&MH_EXECUTE.to_le_bytes()); // filetype
        buf.extend_from_slice(&5u32.to_le_bytes()); // ncmds (segment + symtab + uuid + main + build_version)

        // We'll fill sizeofcmds after computing
        let sizeofcmds_offset = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes()); // placeholder
        buf.extend_from_slice(&0u32.to_le_bytes()); // flags
        buf.extend_from_slice(&0u32.to_le_bytes()); // reserved

        let cmds_start = buf.len();

        // -- LC_SEGMENT_64: __TEXT with one section __text --
        let segment_start = buf.len();
        buf.extend_from_slice(&LC_SEGMENT_64.to_le_bytes()); // cmd
        let seg_cmdsize_offset = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes()); // cmdsize placeholder

        // segname: "__TEXT" padded to 16 bytes
        let mut segname = [0u8; 16];
        segname[..6].copy_from_slice(b"__TEXT");
        buf.extend_from_slice(&segname);

        buf.extend_from_slice(&0x100000000u64.to_le_bytes()); // vmaddr
        buf.extend_from_slice(&0x4000u64.to_le_bytes()); // vmsize
        buf.extend_from_slice(&0u64.to_le_bytes()); // fileoff
        buf.extend_from_slice(&0x4000u64.to_le_bytes()); // filesize
        buf.extend_from_slice(&7i32.to_le_bytes()); // maxprot (rwx)
        buf.extend_from_slice(&5i32.to_le_bytes()); // initprot (r-x)
        buf.extend_from_slice(&1u32.to_le_bytes()); // nsects
        buf.extend_from_slice(&0u32.to_le_bytes()); // flags

        // Section: __text in __TEXT
        let mut sectname = [0u8; 16];
        sectname[..6].copy_from_slice(b"__text");
        buf.extend_from_slice(&sectname);

        let mut sect_segname = [0u8; 16];
        sect_segname[..6].copy_from_slice(b"__TEXT");
        buf.extend_from_slice(&sect_segname);

        buf.extend_from_slice(&0x100001000u64.to_le_bytes()); // addr
        buf.extend_from_slice(&4u64.to_le_bytes()); // size = 4 bytes
        // Section data offset will point to end of buffer (we'll append data later)
        let sect_offset_pos = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes()); // offset placeholder
        buf.extend_from_slice(&2u32.to_le_bytes()); // align (2^2 = 4)
        buf.extend_from_slice(&0u32.to_le_bytes()); // reloff
        buf.extend_from_slice(&0u32.to_le_bytes()); // nreloc
        buf.extend_from_slice(&(S_ATTR_PURE_INSTRUCTIONS | S_REGULAR).to_le_bytes()); // flags
        buf.extend_from_slice(&0u32.to_le_bytes()); // reserved1
        buf.extend_from_slice(&0u32.to_le_bytes()); // reserved2
        buf.extend_from_slice(&0u32.to_le_bytes()); // reserved3

        let segment_end = buf.len();
        let seg_cmdsize = (segment_end - segment_start) as u32;
        buf[seg_cmdsize_offset..seg_cmdsize_offset + 4].copy_from_slice(&seg_cmdsize.to_le_bytes());

        // -- LC_SYMTAB --
        buf.extend_from_slice(&LC_SYMTAB.to_le_bytes()); // cmd
        buf.extend_from_slice(&24u32.to_le_bytes()); // cmdsize
        // symoff/nsyms/stroff/strsize placeholders
        let symoff_pos = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes()); // symoff
        buf.extend_from_slice(&1u32.to_le_bytes()); // nsyms = 1
        let stroff_pos = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes()); // stroff
        buf.extend_from_slice(&7u32.to_le_bytes()); // strsize = 7 ("\0_main\0")

        // -- LC_UUID --
        buf.extend_from_slice(&LC_UUID.to_le_bytes()); // cmd
        buf.extend_from_slice(&24u32.to_le_bytes()); // cmdsize
        let uuid_bytes: [u8; 16] = [
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E,
            0x0F, 0x10,
        ];
        buf.extend_from_slice(&uuid_bytes);

        // -- LC_MAIN --
        buf.extend_from_slice(&LC_MAIN.to_le_bytes()); // cmd
        buf.extend_from_slice(&24u32.to_le_bytes()); // cmdsize
        buf.extend_from_slice(&0x1000u64.to_le_bytes()); // entryoff
        buf.extend_from_slice(&0u64.to_le_bytes()); // stacksize

        // -- LC_BUILD_VERSION --
        let bv_start = buf.len();
        buf.extend_from_slice(&LC_BUILD_VERSION.to_le_bytes()); // cmd
        let bv_cmdsize_offset = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes()); // cmdsize placeholder
        buf.extend_from_slice(&1u32.to_le_bytes()); // platform (MACOS=1)
        buf.extend_from_slice(&0x000E0000u32.to_le_bytes()); // minos (14.0)
        buf.extend_from_slice(&0x000E0000u32.to_le_bytes()); // sdk (14.0)
        buf.extend_from_slice(&1u32.to_le_bytes()); // ntools
        buf.extend_from_slice(&3u32.to_le_bytes()); // tool (LD=3)
        buf.extend_from_slice(&0x03E80000u32.to_le_bytes()); // version
        let bv_end = buf.len();
        let bv_cmdsize = (bv_end - bv_start) as u32;
        buf[bv_cmdsize_offset..bv_cmdsize_offset + 4].copy_from_slice(&bv_cmdsize.to_le_bytes());

        let cmds_end = buf.len();
        let sizeofcmds = (cmds_end - cmds_start) as u32;
        buf[sizeofcmds_offset..sizeofcmds_offset + 4].copy_from_slice(&sizeofcmds.to_le_bytes());

        // -- Section data: 4 bytes of ARM64 "ret" instruction --
        let text_data_offset = buf.len();
        buf.extend_from_slice(&[0xC0, 0x03, 0x5F, 0xD6]); // RET

        // Patch section offset
        buf[sect_offset_pos..sect_offset_pos + 4]
            .copy_from_slice(&(text_data_offset as u32).to_le_bytes());

        // -- String table --
        let strtab_offset = buf.len();
        buf.extend_from_slice(b"\0_main\0");

        // Patch stroff
        buf[stroff_pos..stroff_pos + 4].copy_from_slice(&(strtab_offset as u32).to_le_bytes());

        // -- Symbol table: one nlist_64 entry for _main --
        let symtab_offset = buf.len();
        buf.extend_from_slice(&1u32.to_le_bytes()); // n_strx = 1 ("_main")
        buf.push(N_SECT | N_EXT); // n_type
        buf.push(1); // n_sect = 1 (first section)
        buf.extend_from_slice(&0u16.to_le_bytes()); // n_desc
        buf.extend_from_slice(&0x100001000u64.to_le_bytes()); // n_value

        // Patch symoff
        buf[symoff_pos..symoff_pos + 4].copy_from_slice(&(symtab_offset as u32).to_le_bytes());

        buf
    }

    #[test]
    fn test_parse_synthetic_macho_header() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse synthetic Mach-O");

        assert_eq!(macho.header.magic, MH_MAGIC_64);
        assert_eq!(macho.header.cputype, CPU_TYPE_ARM64);
        assert_eq!(macho.header.filetype, MH_EXECUTE);
        assert_eq!(macho.header.ncmds, 5);
        assert!(macho.is_aarch64());
        assert!(!macho.is_x86_64());
        assert_eq!(macho.header.filetype_name(), "MH_EXECUTE");
        assert_eq!(macho.header.cputype_name(), "ARM64");
    }

    #[test]
    fn test_parse_synthetic_macho_segments_and_sections() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");

        let seg = macho.find_segment("__TEXT").expect("should find __TEXT");
        assert_eq!(seg.segname, "__TEXT");
        assert_eq!(seg.nsects, 1);

        let sect = macho.text_section().expect("should find __text");
        assert_eq!(sect.sectname, "__text");
        assert_eq!(sect.segname, "__TEXT");
        assert_eq!(sect.size, 4);
        assert!(sect.is_executable());
        // ARM64 RET instruction
        assert_eq!(sect.data, &[0xC0, 0x03, 0x5F, 0xD6]);
    }

    #[test]
    fn test_parse_synthetic_macho_uuid() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");

        let uuid = macho.uuid().expect("should have UUID");
        assert_eq!(
            uuid,
            [
                0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E,
                0x0F, 0x10
            ]
        );
    }

    #[test]
    fn test_parse_synthetic_macho_entry_point() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");

        let ep = macho.entry_point().expect("should have entry point");
        assert_eq!(ep, 0x1000);
    }

    #[test]
    fn test_parse_synthetic_macho_build_version() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");

        let bv = macho.build_version().expect("should have build version");
        assert_eq!(bv.platform, 1); // MACOS
        assert_eq!(bv.minos, 0x000E0000);
        assert_eq!(bv.tools.len(), 1);
        assert_eq!(bv.tools[0].tool, 3); // LD
    }

    #[test]
    fn test_parse_synthetic_macho_symbols() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");

        let syms = macho.symbols().expect("should parse symbols");
        assert_eq!(syms.len(), 1);
        assert_eq!(syms[0].name, "_main");
        assert!(syms[0].is_external());
        assert!(syms[0].is_defined_in_section());
        assert_eq!(syms[0].n_value, 0x100001000);
    }

    #[test]
    fn test_parse_synthetic_macho_load_command_count() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");

        assert_eq!(macho.num_load_commands(), 5);
        assert!(macho.symtab_command().is_some());
    }

    #[test]
    fn test_fat_binary_detection() {
        // Not a fat binary
        let thin = build_synthetic_macho();
        assert!(!MachO::is_fat(&thin));

        // FAT_MAGIC header (big-endian 0xCAFEBABE)
        let fat_header = [0xCA, 0xFE, 0xBA, 0xBE];
        assert!(MachO::is_fat(&fat_header));

        // FAT_MAGIC_64 header (big-endian 0xCAFEBABF)
        let fat64_header = [0xCA, 0xFE, 0xBA, 0xBF];
        assert!(MachO::is_fat(&fat64_header));

        // Too small
        assert!(!MachO::is_fat(&[0xCA]));
    }

    #[test]
    fn test_find_section_not_found() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");

        assert!(macho.find_section("__DATA", "__bss").is_none());
        assert!(macho.find_segment("__DATA").is_none());
    }

    #[test]
    fn test_find_aarch64_slice_empty() {
        let arches: Vec<FatArch> = vec![];
        assert!(MachO::find_aarch64_slice(&arches).is_none());
    }

    #[test]
    fn test_find_aarch64_slice_present() {
        let arches = vec![
            FatArch {
                cputype: CPU_TYPE_X86_64,
                cpusubtype: CPU_SUBTYPE_X86_64_ALL,
                offset: 0x1000,
                size: 0x5000,
                align: 14,
            },
            FatArch {
                cputype: CPU_TYPE_ARM64,
                cpusubtype: CPU_SUBTYPE_ARM64_ALL,
                offset: 0x8000,
                size: 0x6000,
                align: 14,
            },
        ];
        let found = MachO::find_aarch64_slice(&arches).expect("should find ARM64");
        assert_eq!(found.cputype, CPU_TYPE_ARM64);
        assert_eq!(found.offset, 0x8000);
    }

    #[test]
    fn test_parse_prefer_aarch64_thin() {
        let data = build_synthetic_macho();
        let macho = MachO::parse_prefer_aarch64(&data).expect("should parse thin binary");
        assert!(macho.is_aarch64());
    }

    #[test]
    fn test_section_type() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");
        let sect = macho.text_section().expect("should find __text");
        assert_eq!(sect.section_type(), S_REGULAR);
    }

    #[test]
    fn test_invalid_magic_rejected() {
        let data = [0x00; 32];
        let err = MachO::parse(&data).unwrap_err();
        assert!(matches!(err, ParseError::InvalidMagic(_)));
    }

    #[test]
    fn test_parse_real_binary() {
        // Parse the Rust test binary itself as a real-world smoke test on
        // Mach-O hosts. On ELF/PE hosts, prove that the Mach-O parser rejects
        // the host executable instead of accidentally treating it as valid.
        let exe = std::env::current_exe().expect("should get current exe path");
        let data = std::fs::read(&exe).expect("should read current binary");

        if !cfg!(target_vendor = "apple") {
            let err = MachO::parse_prefer_aarch64(&data).unwrap_err();
            assert!(matches!(err, ParseError::InvalidMagic(_)));
            return;
        }

        // The test binary might be fat or thin — handle both.
        let macho = MachO::parse_prefer_aarch64(&data).expect("should parse real binary");

        // Basic sanity checks.
        assert_eq!(macho.header.magic, MH_MAGIC_64);
        assert!(macho.num_load_commands() > 0);
        assert!(macho.find_segment("__TEXT").is_some());
        assert!(macho.text_section().is_some());

        // Should have symbols.
        let syms = macho.symbols().expect("should parse symbols");
        assert!(!syms.is_empty(), "real binary should have symbols");

        // Should have a UUID.
        assert!(macho.uuid().is_some(), "real binary should have UUID");
    }

    // --- Edge case tests for improved coverage ---

    #[test]
    fn test_macho_truncated_input_rejected() {
        // Only 4 bytes is valid magic but not enough for full header (32 bytes)
        let err = MachO::parse(&[0xCF, 0xFA, 0xED, 0xFE]).unwrap_err();
        // parse_header reads magic then tries to read more fields -> BufferTooSmall
        assert!(
            matches!(err, ParseError::BufferTooSmall { .. } | ParseError::UnexpectedEof(_)),
            "expected BufferTooSmall or UnexpectedEof, got: {err}"
        );
    }

    #[test]
    fn test_macho_empty_input_rejected() {
        let err = MachO::parse(&[]).unwrap_err();
        assert!(
            matches!(err, ParseError::BufferTooSmall { .. }),
            "expected BufferTooSmall, got: {err}"
        );
    }

    #[test]
    fn test_macho_data_accessor() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");
        assert_eq!(macho.data().len(), data.len());
    }

    #[test]
    fn test_macho_sections_iterator() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");

        let all_sections: Vec<_> = macho.sections().collect();
        assert_eq!(all_sections.len(), 1);
        let (seg, sect) = &all_sections[0];
        assert_eq!(seg.segname, "__TEXT");
        assert_eq!(sect.sectname, "__text");
    }

    #[test]
    fn test_macho_segments_iterator() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");

        let all_segments: Vec<_> = macho.segments().collect();
        assert_eq!(all_segments.len(), 1);
        assert_eq!(all_segments[0].segname, "__TEXT");
    }

    #[test]
    fn test_macho_dylibs_empty() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");
        assert!(macho.dylibs().is_empty());
    }

    #[test]
    fn test_macho_section_relocations_empty() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");
        let sect = macho.text_section().expect("should find __text");
        let relocs = macho.section_relocations(sect).expect("should parse relocs");
        assert!(relocs.is_empty());
    }

    #[test]
    fn test_macho_dysymtab_not_present() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");
        assert!(macho.dysymtab_command().is_none());
    }

    #[test]
    fn test_macho_is_fat_too_small() {
        assert!(!MachO::is_fat(&[]));
        assert!(!MachO::is_fat(&[0xCA]));
        assert!(!MachO::is_fat(&[0xCA, 0xFE]));
        assert!(!MachO::is_fat(&[0xCA, 0xFE, 0xBA]));
    }

    #[test]
    fn test_macho_from_fat_slice_out_of_bounds() {
        let data = build_synthetic_macho();
        let arch = FatArch {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            offset: data.len() as u64 + 100, // past end of data
            size: 100,
            align: 14,
        };
        let err = MachO::from_fat_slice(&data, &arch).unwrap_err();
        assert!(matches!(err, ParseError::DataOutOfBounds { .. }));
    }

    #[test]
    fn test_macho_find_aarch64_slice_not_present() {
        let arches = vec![FatArch {
            cputype: CPU_TYPE_X86_64,
            cpusubtype: CPU_SUBTYPE_X86_64_ALL,
            offset: 0x1000,
            size: 0x5000,
            align: 14,
        }];
        assert!(MachO::find_aarch64_slice(&arches).is_none());
    }

    #[test]
    fn test_macho_header_filetype_and_cputype_names() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");
        assert_eq!(macho.header.filetype_name(), "MH_EXECUTE");
        assert_eq!(macho.header.cputype_name(), "ARM64");
    }

    #[test]
    fn test_macho_swap_is_false_for_le() {
        let data = build_synthetic_macho();
        let macho = MachO::parse(&data).expect("should parse");
        assert!(!macho.swap, "LE binary on LE host should not swap");
    }
}
