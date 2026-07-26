// trust-binary-parse: Mach-O header parsing
//
// Reference: mach-o/loader.h — struct mach_header_64
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::constants::*;
use crate::error::ParseError;
use crate::read::Cursor;

/// Parsed Mach-O 64-bit header.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MachHeader64 {
    /// Magic number (MH_MAGIC_64 or MH_CIGAM_64).
    pub(crate) magic: u32,
    /// CPU type (e.g., `CPU_TYPE_ARM64`).
    pub(crate) cputype: i32,
    /// CPU subtype.
    pub(crate) cpusubtype: i32,
    /// File type (e.g., `MH_EXECUTE`, `MH_DYLIB`).
    pub(crate) filetype: u32,
    /// Number of load commands.
    pub(crate) ncmds: u32,
    /// Total size of all load commands.
    pub(crate) sizeofcmds: u32,
    /// Flags.
    pub(crate) flags: u32,
    /// Reserved (must be zero).
    pub(crate) reserved: u32,
}

impl MachHeader64 {
    /// Whether this binary needs byte-swapping (big-endian on a LE host).
    #[cfg(test)]
    pub fn is_swapped(&self) -> bool {
        self.magic == MH_CIGAM_64
    }

    /// Human-readable file type name.
    #[must_use]
    #[cfg(test)]
    pub fn filetype_name(&self) -> &'static str {
        match self.filetype {
            MH_OBJECT => "MH_OBJECT",
            MH_EXECUTE => "MH_EXECUTE",
            MH_DYLIB => "MH_DYLIB",
            MH_DYLINKER => "MH_DYLINKER",
            MH_BUNDLE => "MH_BUNDLE",
            MH_DSYM => "MH_DSYM",
            MH_KEXT_BUNDLE => "MH_KEXT_BUNDLE",
            MH_CORE => "MH_CORE",
            MH_FILESET => "MH_FILESET",
            _ => "UNKNOWN",
        }
    }

    /// Human-readable CPU type name.
    #[must_use]
    #[cfg(test)]
    pub fn cputype_name(&self) -> &'static str {
        match self.cputype {
            CPU_TYPE_ARM64 => "ARM64",
            CPU_TYPE_X86_64 => "X86_64",
            _ => "UNKNOWN",
        }
    }
}

/// Parse a Mach-O 64-bit header from raw bytes.
///
/// Returns the header and whether byte-swapping is needed.
pub fn parse_header(data: &[u8]) -> Result<(MachHeader64, bool), ParseError> {
    if data.len() < 4 {
        return Err(ParseError::BufferTooSmall { offset: 0, need: 4, have: data.len() });
    }

    let magic = u32::from_le_bytes([data[0], data[1], data[2], data[3]]);
    let swap = match magic {
        MH_MAGIC_64 => false,
        MH_CIGAM_64 => true,
        _ => return Err(ParseError::InvalidMagic(magic)),
    };

    let mut cursor = Cursor::new(data, 0, swap);

    let header = MachHeader64 {
        magic: cursor.read_u32()?,
        cputype: cursor.read_i32()?,
        cpusubtype: cursor.read_i32()?,
        filetype: cursor.read_u32()?,
        ncmds: cursor.read_u32()?,
        sizeofcmds: cursor.read_u32()?,
        flags: cursor.read_u32()?,
        reserved: cursor.read_u32()?,
    };

    Ok((header, swap))
}

/// Fat binary header entry for a single architecture slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FatArch {
    /// CPU type.
    pub(crate) cputype: i32,
    /// CPU subtype.
    pub(crate) cpusubtype: i32,
    /// File offset to the architecture slice.
    pub(crate) offset: u64,
    /// Size of the architecture slice.
    pub(crate) size: u64,
    /// Alignment (power of 2).
    pub(crate) align: u32,
}

/// Parse a fat/universal binary header, returning the slice descriptors.
pub fn parse_fat_header(data: &[u8]) -> Result<Vec<FatArch>, ParseError> {
    if data.len() < 4 {
        return Err(ParseError::BufferTooSmall { offset: 0, need: 4, have: data.len() });
    }

    let magic = u32::from_be_bytes([data[0], data[1], data[2], data[3]]);
    let is_64 = match magic {
        FAT_MAGIC => false,
        FAT_MAGIC_64 => true,
        _ => return Err(ParseError::InvalidMagic(magic)),
    };

    // Fat headers are always big-endian.
    let mut cursor = Cursor::new(data, 0, true);
    cursor.skip(4)?; // skip magic
    let nfat_arch = cursor.read_u32()?;

    let mut arches = Vec::with_capacity(nfat_arch as usize);
    for _ in 0..nfat_arch {
        let cputype = cursor.read_i32()?;
        let cpusubtype = cursor.read_i32()?;
        let (offset, size) = if is_64 {
            (cursor.read_u64()?, cursor.read_u64()?)
        } else {
            (cursor.read_u32()? as u64, cursor.read_u32()? as u64)
        };
        let align = cursor.read_u32()?;
        if is_64 {
            cursor.skip(4)?; // reserved
        }
        arches.push(FatArch { cputype, cpusubtype, offset, size, align });
    }

    Ok(arches)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_header_too_small() {
        let data = [0xCF, 0xFA];
        let err = parse_header(&data).unwrap_err();
        assert!(matches!(err, ParseError::BufferTooSmall { .. }));
    }

    #[test]
    fn test_parse_header_invalid_magic() {
        let data = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let err = parse_header(&data).unwrap_err();
        assert!(matches!(err, ParseError::InvalidMagic(0)));
    }

    #[test]
    fn test_parse_header_valid_le() {
        // Construct a minimal valid 64-bit LE header.
        let mut data = [0u8; 32];
        // MH_MAGIC_64 = 0xFEEDFACF in LE
        data[0..4].copy_from_slice(&MH_MAGIC_64.to_le_bytes());
        // cputype = ARM64
        data[4..8].copy_from_slice(&(CPU_TYPE_ARM64 as u32).to_le_bytes());
        // cpusubtype = ALL
        data[8..12].copy_from_slice(&0u32.to_le_bytes());
        // filetype = MH_EXECUTE
        data[12..16].copy_from_slice(&MH_EXECUTE.to_le_bytes());
        // ncmds = 5
        data[16..20].copy_from_slice(&5u32.to_le_bytes());
        // sizeofcmds = 100
        data[20..24].copy_from_slice(&100u32.to_le_bytes());
        // flags = 0
        data[24..28].copy_from_slice(&0u32.to_le_bytes());
        // reserved = 0
        data[28..32].copy_from_slice(&0u32.to_le_bytes());

        let (hdr, swap) = parse_header(&data).expect("should parse valid header");
        assert!(!swap);
        assert_eq!(hdr.magic, MH_MAGIC_64);
        assert_eq!(hdr.cputype, CPU_TYPE_ARM64);
        assert_eq!(hdr.filetype, MH_EXECUTE);
        assert_eq!(hdr.ncmds, 5);
        assert_eq!(hdr.sizeofcmds, 100);
        assert_eq!(hdr.filetype_name(), "MH_EXECUTE");
        assert_eq!(hdr.cputype_name(), "ARM64");
    }

    #[test]
    fn test_filetype_name_all_known_types() {
        let cases = [
            (MH_OBJECT, "MH_OBJECT"),
            (MH_EXECUTE, "MH_EXECUTE"),
            (MH_DYLIB, "MH_DYLIB"),
            (MH_DYLINKER, "MH_DYLINKER"),
            (MH_BUNDLE, "MH_BUNDLE"),
            (MH_DSYM, "MH_DSYM"),
            (MH_KEXT_BUNDLE, "MH_KEXT_BUNDLE"),
            (MH_CORE, "MH_CORE"),
            (MH_FILESET, "MH_FILESET"),
            (0xFF, "UNKNOWN"),
        ];
        for (filetype, expected) in cases {
            let hdr = MachHeader64 {
                magic: MH_MAGIC_64,
                cputype: CPU_TYPE_ARM64,
                cpusubtype: 0,
                filetype,
                ncmds: 0,
                sizeofcmds: 0,
                flags: 0,
                reserved: 0,
            };
            assert_eq!(hdr.filetype_name(), expected, "filetype={filetype:#x}");
        }
    }

    #[test]
    fn test_cputype_name_all_known() {
        let x86 = MachHeader64 {
            magic: MH_MAGIC_64,
            cputype: CPU_TYPE_X86_64,
            cpusubtype: 0,
            filetype: MH_EXECUTE,
            ncmds: 0,
            sizeofcmds: 0,
            flags: 0,
            reserved: 0,
        };
        assert_eq!(x86.cputype_name(), "X86_64");

        let unknown = MachHeader64 {
            magic: MH_MAGIC_64,
            cputype: 0x0100_0099,
            cpusubtype: 0,
            filetype: MH_EXECUTE,
            ncmds: 0,
            sizeofcmds: 0,
            flags: 0,
            reserved: 0,
        };
        assert_eq!(unknown.cputype_name(), "UNKNOWN");
    }

    #[test]
    fn test_is_swapped_returns_true_for_cigam() {
        let hdr = MachHeader64 {
            magic: MH_CIGAM_64,
            cputype: CPU_TYPE_ARM64,
            cpusubtype: 0,
            filetype: MH_EXECUTE,
            ncmds: 0,
            sizeofcmds: 0,
            flags: 0,
            reserved: 0,
        };
        assert!(hdr.is_swapped());
    }

    #[test]
    fn test_is_swapped_returns_false_for_magic() {
        let hdr = MachHeader64 {
            magic: MH_MAGIC_64,
            cputype: CPU_TYPE_ARM64,
            cpusubtype: 0,
            filetype: MH_EXECUTE,
            ncmds: 0,
            sizeofcmds: 0,
            flags: 0,
            reserved: 0,
        };
        assert!(!hdr.is_swapped());
    }

    #[test]
    fn test_parse_fat_header_invalid_magic() {
        let data = [0x00; 8];
        let err = parse_fat_header(&data).unwrap_err();
        assert!(matches!(err, ParseError::InvalidMagic(_)));
    }

    #[test]
    fn test_parse_fat_header_too_small() {
        let data = [0xCA];
        let err = parse_fat_header(&data).unwrap_err();
        assert!(matches!(err, ParseError::BufferTooSmall { .. }));
    }

    #[test]
    fn test_parse_fat_header_valid_32bit() {
        let mut data = Vec::new();
        data.extend(FAT_MAGIC.to_be_bytes()); // magic (big-endian)
        data.extend(1u32.to_be_bytes()); // nfat_arch = 1
        // fat_arch entry (20 bytes, big-endian)
        data.extend((CPU_TYPE_ARM64 as u32).to_be_bytes()); // cputype
        data.extend(0u32.to_be_bytes()); // cpusubtype
        data.extend(0x1000u32.to_be_bytes()); // offset
        data.extend(0x2000u32.to_be_bytes()); // size
        data.extend(14u32.to_be_bytes()); // align

        let arches = parse_fat_header(&data).unwrap();
        assert_eq!(arches.len(), 1);
        assert_eq!(arches[0].cputype, CPU_TYPE_ARM64);
        assert_eq!(arches[0].offset, 0x1000);
        assert_eq!(arches[0].size, 0x2000);
        assert_eq!(arches[0].align, 14);
    }

    #[test]
    fn test_mach_header_64_eq_and_debug() {
        let hdr = MachHeader64 {
            magic: MH_MAGIC_64,
            cputype: CPU_TYPE_ARM64,
            cpusubtype: 0,
            filetype: MH_EXECUTE,
            ncmds: 0,
            sizeofcmds: 0,
            flags: 0,
            reserved: 0,
        };
        let hdr2 = hdr;
        assert_eq!(hdr, hdr2);
        let _ = format!("{:?}", hdr);
    }

    #[test]
    fn test_fat_arch_eq_and_debug() {
        let arch = FatArch { cputype: CPU_TYPE_ARM64, cpusubtype: 0, offset: 0, size: 0, align: 0 };
        let arch2 = arch;
        assert_eq!(arch, arch2);
        let _ = format!("{:?}", arch);
    }
}
