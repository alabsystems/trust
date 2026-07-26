// trust-binary-parse: Mach-O load command parsing
//
// Reference: mach-o/loader.h — load_command, segment_command_64, etc.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::constants::*;
use crate::error::ParseError;
use crate::read::{Cursor, read_fixed_name};

/// A parsed Mach-O load command.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum LoadCommand<'a> {
    /// LC_SEGMENT_64: maps a segment of the file into memory.
    Segment64(SegmentCommand64<'a>),
    /// LC_SYMTAB: symbol table and string table offsets.
    Symtab(SymtabCommand),
    /// LC_DYSYMTAB: dynamic symbol table info.
    Dysymtab(DysymtabCommand),
    /// LC_LOAD_DYLIB, LC_ID_DYLIB, LC_REEXPORT_DYLIB, etc.
    Dylib(DylibCommand),
    /// LC_UUID: 128-bit UUID.
    Uuid([u8; 16]),
    /// LC_MAIN: entry point for main executables.
    EntryPoint(EntryPointCommand),
    /// LC_BUILD_VERSION: platform and tool versions.
    BuildVersion(BuildVersionCommand),
    /// LC_CODE_SIGNATURE, LC_FUNCTION_STARTS, LC_DATA_IN_CODE, etc.
    LinkeditData(LinkeditDataCommand),
    /// LC_SOURCE_VERSION: source version A.B.C.D.E packed.
    SourceVersion(u64),
    /// LC_RPATH: runtime search path.
    Rpath(String),
    /// LC_DYLD_INFO / LC_DYLD_INFO_ONLY.
    DyldInfo(DyldInfoCommand),
    /// LC_DYLD_CHAINED_FIXUPS.
    DyldChainedFixups(LinkeditDataCommand),
    /// LC_DYLD_EXPORTS_TRIE.
    DyldExportsTrie(LinkeditDataCommand),
    /// LC_LOAD_DYLINKER / LC_ID_DYLINKER.
    Dylinker(String),
    /// LC_ENCRYPTION_INFO_64.
    EncryptionInfo64(EncryptionInfoCommand),
    /// Unknown or unhandled load command.
    Unknown { cmd: u32, data: &'a [u8] },
}

/// LC_SEGMENT_64 command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SegmentCommand64<'a> {
    /// Segment name (up to 16 chars).
    pub(crate) segname: String,
    /// Memory address of this segment.
    pub(crate) vmaddr: u64,
    /// Memory size of this segment.
    pub(crate) vmsize: u64,
    /// File offset of this segment.
    pub(crate) fileoff: u64,
    /// Number of bytes from the file for this segment.
    pub(crate) filesize: u64,
    /// Maximum VM protection.
    pub(crate) maxprot: i32,
    /// Initial VM protection.
    pub(crate) initprot: i32,
    /// Number of sections.
    pub(crate) nsects: u32,
    /// Flags.
    pub(crate) flags: u32,
    /// Sections in this segment.
    pub(crate) sections: Vec<Section64<'a>>,
}

/// A section within a segment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Section64<'a> {
    /// Section name.
    pub(crate) sectname: String,
    /// Segment name this section belongs to.
    pub(crate) segname: String,
    /// Memory address.
    pub(crate) addr: u64,
    /// Size in bytes.
    pub(crate) size: u64,
    /// File offset.
    pub(crate) offset: u32,
    /// Alignment (power of 2).
    pub(crate) align: u32,
    /// File offset of relocations.
    pub(crate) reloff: u32,
    /// Number of relocations.
    pub(crate) nreloc: u32,
    /// Flags (type + attributes).
    pub(crate) flags: u32,
    /// Reserved fields.
    pub(crate) reserved1: u32,
    pub(crate) reserved2: u32,
    pub(crate) reserved3: u32,
    /// Zero-copy reference to the section's raw data in the file.
    pub(crate) data: &'a [u8],
}

impl Section64<'_> {
    /// Section type (low 8 bits of flags).
    #[must_use]
    pub fn section_type(&self) -> u32 {
        self.flags & SECTION_TYPE_MASK
    }

    /// Whether this section contains executable instructions.
    #[must_use]
    pub fn is_executable(&self) -> bool {
        (self.flags & S_ATTR_PURE_INSTRUCTIONS) != 0 || (self.flags & S_ATTR_SOME_INSTRUCTIONS) != 0
    }
}

/// LC_SYMTAB command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymtabCommand {
    /// File offset of the symbol table.
    pub(crate) symoff: u32,
    /// Number of symbol table entries.
    pub(crate) nsyms: u32,
    /// File offset of the string table.
    pub(crate) stroff: u32,
    /// Size of the string table in bytes.
    pub(crate) strsize: u32,
}

/// LC_DYSYMTAB command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DysymtabCommand {
    pub(crate) ilocalsym: u32,
    pub(crate) nlocalsym: u32,
    pub(crate) iextdefsym: u32,
    pub(crate) nextdefsym: u32,
    pub(crate) iundefsym: u32,
    pub(crate) nundefsym: u32,
    pub(crate) tocoff: u32,
    pub(crate) ntoc: u32,
    pub(crate) modtaboff: u32,
    pub(crate) nmodtab: u32,
    pub(crate) extrefsymoff: u32,
    pub(crate) nextrefsyms: u32,
    pub(crate) indirectsymoff: u32,
    pub(crate) nindirectsyms: u32,
    pub(crate) extreloff: u32,
    pub(crate) nextrel: u32,
    pub(crate) locreloff: u32,
    pub(crate) nlocrel: u32,
}

/// LC_LOAD_DYLIB / LC_ID_DYLIB / LC_REEXPORT_DYLIB.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DylibCommand {
    /// The load command type (LC_LOAD_DYLIB, etc.).
    pub(crate) cmd: u32,
    /// Dylib name (path).
    pub(crate) name: String,
    /// Compatibility version.
    pub(crate) compatibility_version: u32,
    /// Current version.
    pub(crate) current_version: u32,
    /// Timestamp.
    pub(crate) timestamp: u32,
}

/// LC_MAIN: entry point command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EntryPointCommand {
    /// File offset of main() entry point.
    pub(crate) entryoff: u64,
    /// Initial stack size (0 = default).
    pub(crate) stacksize: u64,
}

/// LC_BUILD_VERSION.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildVersionCommand {
    /// Platform identifier.
    pub(crate) platform: u32,
    /// Minimum OS version (X.Y.Z packed).
    pub(crate) minos: u32,
    /// SDK version.
    pub(crate) sdk: u32,
    /// Build tool versions.
    pub(crate) tools: Vec<BuildToolVersion>,
}

/// A build tool version entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BuildToolVersion {
    pub(crate) tool: u32,
    pub(crate) version: u32,
}

/// LC_CODE_SIGNATURE, LC_FUNCTION_STARTS, LC_DATA_IN_CODE, etc.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LinkeditDataCommand {
    pub(crate) cmd: u32,
    pub(crate) dataoff: u32,
    pub(crate) datasize: u32,
}

/// LC_DYLD_INFO / LC_DYLD_INFO_ONLY.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DyldInfoCommand {
    pub(crate) rebase_off: u32,
    pub(crate) rebase_size: u32,
    pub(crate) bind_off: u32,
    pub(crate) bind_size: u32,
    pub(crate) weak_bind_off: u32,
    pub(crate) weak_bind_size: u32,
    pub(crate) lazy_bind_off: u32,
    pub(crate) lazy_bind_size: u32,
    pub(crate) export_off: u32,
    pub(crate) export_size: u32,
}

/// LC_ENCRYPTION_INFO_64.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EncryptionInfoCommand {
    pub(crate) cryptoff: u32,
    pub(crate) cryptsize: u32,
    pub(crate) cryptid: u32,
    pub(crate) pad: u32,
}

/// Parse all load commands from the data following the Mach-O header.
pub fn parse_load_commands<'a>(
    file_data: &'a [u8],
    ncmds: u32,
    swap: bool,
) -> Result<Vec<LoadCommand<'a>>, ParseError> {
    let mut cursor = Cursor::new(file_data, MACH_HEADER_64_SIZE, swap);
    let mut commands = Vec::with_capacity(ncmds as usize);

    for _ in 0..ncmds {
        let cmd_start = cursor.offset();
        let cmd = cursor.read_u32()?;
        let cmdsize = cursor.read_u32()?;

        if cmdsize < LOAD_COMMAND_SIZE as u32 {
            return Err(ParseError::InvalidLoadCommandSize { cmd, size: cmdsize });
        }

        let cmd_end =
            cmd_start.checked_add(cmdsize as usize).ok_or(ParseError::DataOutOfBounds {
                offset: cmd_start as u64,
                end: u64::MAX,
                file_size: file_data.len(),
            })?;
        if cmd_end > file_data.len() {
            return Err(ParseError::DataOutOfBounds {
                offset: cmd_start as u64,
                end: cmd_end as u64,
                file_size: file_data.len(),
            });
        }

        let cmd_data = &file_data[cmd_start..cmd_end];
        let parsed = parse_single_command(file_data, cmd, cmdsize, cmd_data, swap)?;
        commands.push(parsed);

        // Advance cursor to next command.
        cursor.set_offset(cmd_end);
    }

    Ok(commands)
}

/// Parse a single load command from its raw data.
fn parse_single_command<'a>(
    file_data: &'a [u8],
    cmd: u32,
    cmdsize: u32,
    cmd_data: &'a [u8],
    swap: bool,
) -> Result<LoadCommand<'a>, ParseError> {
    match cmd {
        LC_SEGMENT_64 => parse_segment_64(file_data, cmd_data, swap),
        LC_SYMTAB => parse_symtab(cmd_data, swap),
        LC_DYSYMTAB => parse_dysymtab(cmd_data, swap),
        LC_LOAD_DYLIB | LC_ID_DYLIB | LC_REEXPORT_DYLIB | LC_LAZY_LOAD_DYLIB => {
            parse_dylib(cmd, cmd_data, cmdsize, swap)
        }
        LC_UUID => parse_uuid(cmd_data),
        LC_MAIN => parse_entry_point(cmd_data, swap),
        LC_BUILD_VERSION => parse_build_version(cmd_data, swap),
        LC_CODE_SIGNATURE
        | LC_FUNCTION_STARTS
        | LC_DATA_IN_CODE
        | LC_SEGMENT_SPLIT_INFO
        | LC_LINKER_OPTIMIZATION_HINT
        | LC_DYLIB_CODE_SIGN_DRS => parse_linkedit_data(cmd, cmd_data, swap),
        LC_SOURCE_VERSION => parse_source_version(cmd_data, swap),
        LC_RPATH => parse_rpath(cmd_data, cmdsize, swap),
        LC_DYLD_INFO | LC_DYLD_INFO_ONLY => parse_dyld_info(cmd_data, swap),
        LC_DYLD_CHAINED_FIXUPS => {
            let lc = parse_linkedit_data_inner(cmd, cmd_data, swap)?;
            Ok(LoadCommand::DyldChainedFixups(lc))
        }
        LC_DYLD_EXPORTS_TRIE => {
            let lc = parse_linkedit_data_inner(cmd, cmd_data, swap)?;
            Ok(LoadCommand::DyldExportsTrie(lc))
        }
        LC_LOAD_DYLINKER | LC_ID_DYLINKER => parse_dylinker(cmd_data, cmdsize, swap),
        LC_ENCRYPTION_INFO_64 => parse_encryption_info(cmd_data, swap),
        _ => Ok(LoadCommand::Unknown { cmd, data: cmd_data }),
    }
}

fn parse_segment_64<'a>(
    file_data: &'a [u8],
    cmd_data: &'a [u8],
    swap: bool,
) -> Result<LoadCommand<'a>, ParseError> {
    let mut c = Cursor::new(cmd_data, 8, swap); // skip cmd + cmdsize
    let name_bytes = c.read_bytes(SEG_NAME_LEN)?;
    let segname = read_fixed_name(name_bytes).to_owned();
    let vmaddr = c.read_u64()?;
    let vmsize = c.read_u64()?;
    let fileoff = c.read_u64()?;
    let filesize = c.read_u64()?;
    let maxprot = c.read_i32()?;
    let initprot = c.read_i32()?;
    let nsects = c.read_u32()?;
    let flags = c.read_u32()?;

    let mut sections = Vec::with_capacity(nsects as usize);
    for _ in 0..nsects {
        let sect_name_bytes = c.read_bytes(SECT_NAME_LEN)?;
        let sect_seg_bytes = c.read_bytes(SEG_NAME_LEN)?;
        let addr = c.read_u64()?;
        let size = c.read_u64()?;
        let offset = c.read_u32()?;
        let align = c.read_u32()?;
        let reloff = c.read_u32()?;
        let nreloc = c.read_u32()?;
        let sect_flags = c.read_u32()?;
        let reserved1 = c.read_u32()?;
        let reserved2 = c.read_u32()?;
        let reserved3 = c.read_u32()?;

        // Zero-copy: reference the section data directly from the file.
        let sect_type = sect_flags & SECTION_TYPE_MASK;
        let data = if sect_type == S_ZEROFILL || size == 0 {
            &[] as &[u8]
        } else {
            let end = u64::from(offset).checked_add(size).ok_or(ParseError::DataOutOfBounds {
                offset: u64::from(offset),
                end: u64::MAX,
                file_size: file_data.len(),
            })?;
            if end > file_data.len() as u64 {
                return Err(ParseError::DataOutOfBounds {
                    offset: u64::from(offset),
                    end,
                    file_size: file_data.len(),
                });
            }
            let start = offset as usize;
            let end = usize::try_from(end).map_err(|_| ParseError::DataOutOfBounds {
                offset: u64::from(offset),
                end,
                file_size: file_data.len(),
            })?;
            &file_data[start..end]
        };

        sections.push(Section64 {
            sectname: read_fixed_name(sect_name_bytes).to_owned(),
            segname: read_fixed_name(sect_seg_bytes).to_owned(),
            addr,
            size,
            offset,
            align,
            reloff,
            nreloc,
            flags: sect_flags,
            reserved1,
            reserved2,
            reserved3,
            data,
        });
    }

    Ok(LoadCommand::Segment64(SegmentCommand64 {
        segname,
        vmaddr,
        vmsize,
        fileoff,
        filesize,
        maxprot,
        initprot,
        nsects,
        flags,
        sections,
    }))
}

fn parse_symtab(cmd_data: &[u8], swap: bool) -> Result<LoadCommand<'_>, ParseError> {
    let mut c = Cursor::new(cmd_data, 8, swap);
    Ok(LoadCommand::Symtab(SymtabCommand {
        symoff: c.read_u32()?,
        nsyms: c.read_u32()?,
        stroff: c.read_u32()?,
        strsize: c.read_u32()?,
    }))
}

fn parse_dysymtab(cmd_data: &[u8], swap: bool) -> Result<LoadCommand<'_>, ParseError> {
    let mut c = Cursor::new(cmd_data, 8, swap);
    Ok(LoadCommand::Dysymtab(DysymtabCommand {
        ilocalsym: c.read_u32()?,
        nlocalsym: c.read_u32()?,
        iextdefsym: c.read_u32()?,
        nextdefsym: c.read_u32()?,
        iundefsym: c.read_u32()?,
        nundefsym: c.read_u32()?,
        tocoff: c.read_u32()?,
        ntoc: c.read_u32()?,
        modtaboff: c.read_u32()?,
        nmodtab: c.read_u32()?,
        extrefsymoff: c.read_u32()?,
        nextrefsyms: c.read_u32()?,
        indirectsymoff: c.read_u32()?,
        nindirectsyms: c.read_u32()?,
        extreloff: c.read_u32()?,
        nextrel: c.read_u32()?,
        locreloff: c.read_u32()?,
        nlocrel: c.read_u32()?,
    }))
}

fn parse_dylib(
    cmd: u32,
    cmd_data: &[u8],
    cmdsize: u32,
    swap: bool,
) -> Result<LoadCommand<'_>, ParseError> {
    let mut c = Cursor::new(cmd_data, 8, swap);
    let name_offset = c.read_u32()?;
    let timestamp = c.read_u32()?;
    let current_version = c.read_u32()?;
    let compatibility_version = c.read_u32()?;

    let name = if (name_offset as usize) < cmd_data.len() {
        let name_bytes = &cmd_data[name_offset as usize..];
        let end = name_bytes.iter().position(|&b| b == 0).unwrap_or(name_bytes.len());
        String::from_utf8_lossy(&name_bytes[..end]).into_owned()
    } else {
        return Err(ParseError::StringOffsetOutOfBounds { offset: name_offset, cmd_size: cmdsize });
    };

    Ok(LoadCommand::Dylib(DylibCommand {
        cmd,
        name,
        compatibility_version,
        current_version,
        timestamp,
    }))
}

fn parse_uuid(cmd_data: &[u8]) -> Result<LoadCommand<'_>, ParseError> {
    if cmd_data.len() < UUID_COMMAND_SIZE {
        return Err(ParseError::BufferTooSmall {
            offset: 0,
            need: UUID_COMMAND_SIZE,
            have: cmd_data.len(),
        });
    }
    let mut uuid = [0u8; 16];
    uuid.copy_from_slice(&cmd_data[8..24]);
    Ok(LoadCommand::Uuid(uuid))
}

fn parse_entry_point(cmd_data: &[u8], swap: bool) -> Result<LoadCommand<'_>, ParseError> {
    let mut c = Cursor::new(cmd_data, 8, swap);
    Ok(LoadCommand::EntryPoint(EntryPointCommand {
        entryoff: c.read_u64()?,
        stacksize: c.read_u64()?,
    }))
}

fn parse_build_version(cmd_data: &[u8], swap: bool) -> Result<LoadCommand<'_>, ParseError> {
    let mut c = Cursor::new(cmd_data, 8, swap);
    let platform = c.read_u32()?;
    let minos = c.read_u32()?;
    let sdk = c.read_u32()?;
    let ntools = c.read_u32()?;

    let mut tools = Vec::with_capacity(ntools as usize);
    for _ in 0..ntools {
        tools.push(BuildToolVersion { tool: c.read_u32()?, version: c.read_u32()? });
    }

    Ok(LoadCommand::BuildVersion(BuildVersionCommand { platform, minos, sdk, tools }))
}

fn parse_linkedit_data_inner(
    cmd: u32,
    cmd_data: &[u8],
    swap: bool,
) -> Result<LinkeditDataCommand, ParseError> {
    let mut c = Cursor::new(cmd_data, 8, swap);
    Ok(LinkeditDataCommand { cmd, dataoff: c.read_u32()?, datasize: c.read_u32()? })
}

fn parse_linkedit_data(
    cmd: u32,
    cmd_data: &[u8],
    swap: bool,
) -> Result<LoadCommand<'_>, ParseError> {
    Ok(LoadCommand::LinkeditData(parse_linkedit_data_inner(cmd, cmd_data, swap)?))
}

fn parse_source_version(cmd_data: &[u8], swap: bool) -> Result<LoadCommand<'_>, ParseError> {
    let mut c = Cursor::new(cmd_data, 8, swap);
    Ok(LoadCommand::SourceVersion(c.read_u64()?))
}

fn parse_rpath(cmd_data: &[u8], cmdsize: u32, swap: bool) -> Result<LoadCommand<'_>, ParseError> {
    let mut c = Cursor::new(cmd_data, 8, swap);
    let path_offset = c.read_u32()?;
    if (path_offset as usize) >= cmd_data.len() {
        return Err(ParseError::StringOffsetOutOfBounds { offset: path_offset, cmd_size: cmdsize });
    }
    let path_bytes = &cmd_data[path_offset as usize..];
    let end = path_bytes.iter().position(|&b| b == 0).unwrap_or(path_bytes.len());
    Ok(LoadCommand::Rpath(String::from_utf8_lossy(&path_bytes[..end]).into_owned()))
}

fn parse_dyld_info(cmd_data: &[u8], swap: bool) -> Result<LoadCommand<'_>, ParseError> {
    let mut c = Cursor::new(cmd_data, 8, swap);
    Ok(LoadCommand::DyldInfo(DyldInfoCommand {
        rebase_off: c.read_u32()?,
        rebase_size: c.read_u32()?,
        bind_off: c.read_u32()?,
        bind_size: c.read_u32()?,
        weak_bind_off: c.read_u32()?,
        weak_bind_size: c.read_u32()?,
        lazy_bind_off: c.read_u32()?,
        lazy_bind_size: c.read_u32()?,
        export_off: c.read_u32()?,
        export_size: c.read_u32()?,
    }))
}

fn parse_dylinker(
    cmd_data: &[u8],
    cmdsize: u32,
    swap: bool,
) -> Result<LoadCommand<'_>, ParseError> {
    let mut c = Cursor::new(cmd_data, 8, swap);
    let name_offset = c.read_u32()?;
    if (name_offset as usize) >= cmd_data.len() {
        return Err(ParseError::StringOffsetOutOfBounds { offset: name_offset, cmd_size: cmdsize });
    }
    let name_bytes = &cmd_data[name_offset as usize..];
    let end = name_bytes.iter().position(|&b| b == 0).unwrap_or(name_bytes.len());
    Ok(LoadCommand::Dylinker(String::from_utf8_lossy(&name_bytes[..end]).into_owned()))
}

fn parse_encryption_info(cmd_data: &[u8], swap: bool) -> Result<LoadCommand<'_>, ParseError> {
    let mut c = Cursor::new(cmd_data, 8, swap);
    Ok(LoadCommand::EncryptionInfo64(EncryptionInfoCommand {
        cryptoff: c.read_u32()?,
        cryptsize: c.read_u32()?,
        cryptid: c.read_u32()?,
        pad: c.read_u32()?,
    }))
}

/// Human-readable name for a load command type.
#[must_use]
#[cfg(test)]
pub fn load_command_name(cmd: u32) -> &'static str {
    match cmd {
        LC_SEGMENT_64 => "LC_SEGMENT_64",
        LC_SYMTAB => "LC_SYMTAB",
        LC_DYSYMTAB => "LC_DYSYMTAB",
        LC_LOAD_DYLIB => "LC_LOAD_DYLIB",
        LC_ID_DYLIB => "LC_ID_DYLIB",
        LC_LOAD_DYLINKER => "LC_LOAD_DYLINKER",
        LC_ID_DYLINKER => "LC_ID_DYLINKER",
        LC_UUID => "LC_UUID",
        LC_RPATH => "LC_RPATH",
        LC_CODE_SIGNATURE => "LC_CODE_SIGNATURE",
        LC_FUNCTION_STARTS => "LC_FUNCTION_STARTS",
        LC_DATA_IN_CODE => "LC_DATA_IN_CODE",
        LC_REEXPORT_DYLIB => "LC_REEXPORT_DYLIB",
        LC_LAZY_LOAD_DYLIB => "LC_LAZY_LOAD_DYLIB",
        LC_DYLD_INFO => "LC_DYLD_INFO",
        LC_DYLD_INFO_ONLY => "LC_DYLD_INFO_ONLY",
        LC_MAIN => "LC_MAIN",
        LC_SOURCE_VERSION => "LC_SOURCE_VERSION",
        LC_BUILD_VERSION => "LC_BUILD_VERSION",
        LC_DYLD_CHAINED_FIXUPS => "LC_DYLD_CHAINED_FIXUPS",
        LC_DYLD_EXPORTS_TRIE => "LC_DYLD_EXPORTS_TRIE",
        LC_ENCRYPTION_INFO_64 => "LC_ENCRYPTION_INFO_64",
        LC_SEGMENT_SPLIT_INFO => "LC_SEGMENT_SPLIT_INFO",
        LC_LINKER_OPTIMIZATION_HINT => "LC_LINKER_OPTIMIZATION_HINT",
        LC_FILESET_ENTRY => "LC_FILESET_ENTRY",
        _ => "UNKNOWN",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_load_command_name_known_types() {
        assert_eq!(load_command_name(LC_SEGMENT_64), "LC_SEGMENT_64");
        assert_eq!(load_command_name(LC_SYMTAB), "LC_SYMTAB");
        assert_eq!(load_command_name(LC_DYSYMTAB), "LC_DYSYMTAB");
        assert_eq!(load_command_name(LC_LOAD_DYLIB), "LC_LOAD_DYLIB");
        assert_eq!(load_command_name(LC_ID_DYLIB), "LC_ID_DYLIB");
        assert_eq!(load_command_name(LC_LOAD_DYLINKER), "LC_LOAD_DYLINKER");
        assert_eq!(load_command_name(LC_ID_DYLINKER), "LC_ID_DYLINKER");
        assert_eq!(load_command_name(LC_UUID), "LC_UUID");
        assert_eq!(load_command_name(LC_RPATH), "LC_RPATH");
        assert_eq!(load_command_name(LC_CODE_SIGNATURE), "LC_CODE_SIGNATURE");
        assert_eq!(load_command_name(LC_FUNCTION_STARTS), "LC_FUNCTION_STARTS");
        assert_eq!(load_command_name(LC_DATA_IN_CODE), "LC_DATA_IN_CODE");
        assert_eq!(load_command_name(LC_MAIN), "LC_MAIN");
        assert_eq!(load_command_name(LC_SOURCE_VERSION), "LC_SOURCE_VERSION");
        assert_eq!(load_command_name(LC_BUILD_VERSION), "LC_BUILD_VERSION");
        assert_eq!(load_command_name(LC_ENCRYPTION_INFO_64), "LC_ENCRYPTION_INFO_64");
    }

    #[test]
    fn test_load_command_name_unknown_returns_unknown() {
        assert_eq!(load_command_name(0xFFFF_FFFF), "UNKNOWN");
        assert_eq!(load_command_name(0), "UNKNOWN");
    }

    #[test]
    fn test_section64_section_type_masking() {
        let sect = Section64 {
            sectname: "__text".to_string(),
            segname: "__TEXT".to_string(),
            addr: 0,
            size: 0,
            offset: 0,
            align: 0,
            reloff: 0,
            nreloc: 0,
            flags: S_ATTR_PURE_INSTRUCTIONS | S_REGULAR,
            reserved1: 0,
            reserved2: 0,
            reserved3: 0,
            data: &[],
        };
        assert_eq!(sect.section_type(), S_REGULAR);
    }

    #[test]
    fn test_section64_section_type_cstring_literals() {
        let sect = Section64 {
            sectname: "__cstring".to_string(),
            segname: "__TEXT".to_string(),
            addr: 0,
            size: 0,
            offset: 0,
            align: 0,
            reloff: 0,
            nreloc: 0,
            flags: S_CSTRING_LITERALS,
            reserved1: 0,
            reserved2: 0,
            reserved3: 0,
            data: &[],
        };
        assert_eq!(sect.section_type(), S_CSTRING_LITERALS);
    }

    #[test]
    fn test_section64_is_executable_pure_instructions() {
        let sect = Section64 {
            sectname: "__text".to_string(),
            segname: "__TEXT".to_string(),
            addr: 0,
            size: 0,
            offset: 0,
            align: 0,
            reloff: 0,
            nreloc: 0,
            flags: S_ATTR_PURE_INSTRUCTIONS,
            reserved1: 0,
            reserved2: 0,
            reserved3: 0,
            data: &[],
        };
        assert!(sect.is_executable());
    }

    #[test]
    fn test_section64_is_executable_some_instructions() {
        let sect = Section64 {
            sectname: "__stub".to_string(),
            segname: "__TEXT".to_string(),
            addr: 0,
            size: 0,
            offset: 0,
            align: 0,
            reloff: 0,
            nreloc: 0,
            flags: S_ATTR_SOME_INSTRUCTIONS,
            reserved1: 0,
            reserved2: 0,
            reserved3: 0,
            data: &[],
        };
        assert!(sect.is_executable());
    }

    #[test]
    fn test_section64_not_executable() {
        let sect = Section64 {
            sectname: "__data".to_string(),
            segname: "__DATA".to_string(),
            addr: 0,
            size: 0,
            offset: 0,
            align: 0,
            reloff: 0,
            nreloc: 0,
            flags: S_REGULAR,
            reserved1: 0,
            reserved2: 0,
            reserved3: 0,
            data: &[],
        };
        assert!(!sect.is_executable());
    }

    #[test]
    fn test_parse_uuid_too_small_returns_error() {
        let data = [0u8; 16]; // needs 24 bytes (8 header + 16 uuid)
        let err = parse_uuid(&data).unwrap_err();
        assert!(matches!(err, ParseError::BufferTooSmall { .. }));
    }

    #[test]
    fn test_parse_uuid_valid() {
        let mut data = vec![0u8; 8]; // cmd + cmdsize
        let uuid_bytes = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        data.extend_from_slice(&uuid_bytes);
        match parse_uuid(&data).unwrap() {
            LoadCommand::Uuid(uuid) => assert_eq!(uuid, uuid_bytes),
            other => panic!("expected Uuid, got {:?}", other),
        }
    }

    #[test]
    fn test_entry_point_command_eq() {
        let cmd1 = EntryPointCommand { entryoff: 0x1000, stacksize: 0 };
        let cmd2 = EntryPointCommand { entryoff: 0x1000, stacksize: 0 };
        assert_eq!(cmd1, cmd2);
    }

    #[test]
    fn test_symtab_command_eq() {
        let cmd = SymtabCommand { symoff: 100, nsyms: 10, stroff: 200, strsize: 50 };
        let clone = cmd;
        assert_eq!(cmd, clone);
    }

    #[test]
    fn test_linkedit_data_command_eq() {
        let cmd = LinkeditDataCommand { cmd: LC_CODE_SIGNATURE, dataoff: 0x100, datasize: 0x50 };
        assert_eq!(cmd.cmd, LC_CODE_SIGNATURE);
        assert_eq!(cmd.dataoff, 0x100);
    }

    #[test]
    fn test_build_version_debug() {
        let cmd = BuildVersionCommand {
            platform: 1,
            minos: 0x000E0000, // macOS 14.0
            sdk: 0x000E0000,
            tools: vec![BuildToolVersion { tool: 3, version: 0x03FC0005 }],
        };
        let _ = format!("{:?}", cmd);
    }

    #[test]
    fn test_dyld_info_command_eq() {
        let cmd = DyldInfoCommand {
            rebase_off: 0,
            rebase_size: 0,
            bind_off: 0,
            bind_size: 0,
            weak_bind_off: 0,
            weak_bind_size: 0,
            lazy_bind_off: 0,
            lazy_bind_size: 0,
            export_off: 0,
            export_size: 0,
        };
        let clone = cmd;
        assert_eq!(cmd, clone);
    }

    #[test]
    fn test_encryption_info_command_eq() {
        let cmd = EncryptionInfoCommand { cryptoff: 0, cryptsize: 0, cryptid: 0, pad: 0 };
        let clone = cmd;
        assert_eq!(cmd, clone);
    }
}
