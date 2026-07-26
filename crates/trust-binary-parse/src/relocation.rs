// trust-binary-parse: Mach-O relocation parsing
//
// Reference: mach-o/reloc.h — struct relocation_info
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::constants::*;
use crate::error::ParseError;
use crate::read::Cursor;

/// A parsed relocation entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Relocation {
    /// Offset in the section to relocate.
    pub(crate) address: u32,
    /// Symbol index (if r_extern) or section number.
    pub(crate) symbol_or_section: u32,
    /// Whether this references an external symbol (vs. a section).
    pub(crate) is_extern: bool,
    /// Relocation type (architecture-specific).
    pub(crate) reloc_type: u8,
    /// Size of the relocation: 0=byte, 1=word, 2=long, 3=quad.
    pub(crate) length: u8,
    /// Whether the relocation is PC-relative.
    pub(crate) is_pcrel: bool,
}

/// Parse relocations for a section.
pub fn parse_relocations(
    file_data: &[u8],
    reloff: u32,
    nreloc: u32,
    swap: bool,
) -> Result<Vec<Relocation>, ParseError> {
    if nreloc == 0 {
        return Ok(Vec::new());
    }

    let start = reloff as usize;
    let end = start + (nreloc as usize) * RELOC_SIZE;
    if end > file_data.len() {
        return Err(ParseError::DataOutOfBounds {
            offset: reloff as u64,
            end: end as u64,
            file_size: file_data.len(),
        });
    }

    let mut relocs = Vec::with_capacity(nreloc as usize);
    let mut cursor = Cursor::new(file_data, start, swap);

    for _ in 0..nreloc {
        let r_address = cursor.read_u32()?;
        let r_info = cursor.read_u32()?;

        // relocation_info layout (little-endian):
        //   r_address: 32 bits
        //   r_symbolnum: 24 bits (low)
        //   r_pcrel: 1 bit
        //   r_length: 2 bits
        //   r_extern: 1 bit
        //   r_type: 4 bits (high)
        let symbol_or_section = r_info & 0x00FF_FFFF;
        let is_pcrel = (r_info >> 24) & 1 != 0;
        let length = ((r_info >> 25) & 3) as u8;
        let is_extern = (r_info >> 27) & 1 != 0;
        let reloc_type = ((r_info >> 28) & 0xF) as u8;

        relocs.push(Relocation {
            address: r_address,
            symbol_or_section,
            is_extern,
            reloc_type,
            length,
            is_pcrel,
        });
    }

    Ok(relocs)
}

/// Human-readable name for an AArch64 relocation type.
#[must_use]
#[cfg(test)]
pub fn arm64_reloc_name(reloc_type: u8) -> &'static str {
    match reloc_type {
        ARM64_RELOC_UNSIGNED => "ARM64_RELOC_UNSIGNED",
        ARM64_RELOC_SUBTRACTOR => "ARM64_RELOC_SUBTRACTOR",
        ARM64_RELOC_BRANCH26 => "ARM64_RELOC_BRANCH26",
        ARM64_RELOC_PAGE21 => "ARM64_RELOC_PAGE21",
        ARM64_RELOC_PAGEOFF12 => "ARM64_RELOC_PAGEOFF12",
        ARM64_RELOC_GOT_LOAD_PAGE21 => "ARM64_RELOC_GOT_LOAD_PAGE21",
        ARM64_RELOC_GOT_LOAD_PAGEOFF12 => "ARM64_RELOC_GOT_LOAD_PAGEOFF12",
        ARM64_RELOC_POINTER_TO_GOT => "ARM64_RELOC_POINTER_TO_GOT",
        ARM64_RELOC_TLVP_LOAD_PAGE21 => "ARM64_RELOC_TLVP_LOAD_PAGE21",
        ARM64_RELOC_TLVP_LOAD_PAGEOFF12 => "ARM64_RELOC_TLVP_LOAD_PAGEOFF12",
        ARM64_RELOC_ADDEND => "ARM64_RELOC_ADDEND",
        _ => "UNKNOWN",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arm64_reloc_names() {
        assert_eq!(arm64_reloc_name(ARM64_RELOC_BRANCH26), "ARM64_RELOC_BRANCH26");
        assert_eq!(arm64_reloc_name(ARM64_RELOC_PAGE21), "ARM64_RELOC_PAGE21");
        assert_eq!(arm64_reloc_name(255), "UNKNOWN");
    }

    #[test]
    fn test_arm64_reloc_names_all_known_types() {
        assert_eq!(arm64_reloc_name(ARM64_RELOC_UNSIGNED), "ARM64_RELOC_UNSIGNED");
        assert_eq!(arm64_reloc_name(ARM64_RELOC_SUBTRACTOR), "ARM64_RELOC_SUBTRACTOR");
        assert_eq!(arm64_reloc_name(ARM64_RELOC_PAGEOFF12), "ARM64_RELOC_PAGEOFF12");
        assert_eq!(arm64_reloc_name(ARM64_RELOC_GOT_LOAD_PAGE21), "ARM64_RELOC_GOT_LOAD_PAGE21");
        assert_eq!(
            arm64_reloc_name(ARM64_RELOC_GOT_LOAD_PAGEOFF12),
            "ARM64_RELOC_GOT_LOAD_PAGEOFF12"
        );
        assert_eq!(arm64_reloc_name(ARM64_RELOC_POINTER_TO_GOT), "ARM64_RELOC_POINTER_TO_GOT");
        assert_eq!(arm64_reloc_name(ARM64_RELOC_TLVP_LOAD_PAGE21), "ARM64_RELOC_TLVP_LOAD_PAGE21");
        assert_eq!(
            arm64_reloc_name(ARM64_RELOC_TLVP_LOAD_PAGEOFF12),
            "ARM64_RELOC_TLVP_LOAD_PAGEOFF12"
        );
        assert_eq!(arm64_reloc_name(ARM64_RELOC_ADDEND), "ARM64_RELOC_ADDEND");
    }

    #[test]
    fn test_parse_relocations_zero_nreloc_returns_empty() {
        let data = [0u8; 32];
        let result = parse_relocations(&data, 0, 0, false).unwrap();
        assert!(result.is_empty());
    }

    #[test]
    fn test_parse_relocations_out_of_bounds_returns_error() {
        let data = [0u8; 4]; // too small for one relocation entry (8 bytes)
        let err = parse_relocations(&data, 0, 1, false).unwrap_err();
        assert!(matches!(err, ParseError::DataOutOfBounds { .. }));
    }

    #[test]
    fn test_parse_relocations_bitfield_extraction() {
        // Build a relocation entry with known bits:
        // r_address = 0x100
        // r_info: symbolnum=5, pcrel=1, length=2, extern=1, type=3
        // r_info = 5 | (1<<24) | (2<<25) | (1<<27) | (3<<28)
        //        = 0x0000_0005 | 0x0100_0000 | 0x0400_0000 | 0x0800_0000 | 0x3000_0000
        //        = 0x3D00_0005
        let mut data = Vec::new();
        data.extend(0x100u32.to_le_bytes()); // r_address
        data.extend(0x3D00_0005u32.to_le_bytes()); // r_info

        let relocs = parse_relocations(&data, 0, 1, false).unwrap();
        assert_eq!(relocs.len(), 1);
        let r = &relocs[0];
        assert_eq!(r.address, 0x100);
        assert_eq!(r.symbol_or_section, 5);
        assert!(r.is_pcrel);
        assert_eq!(r.length, 2);
        assert!(r.is_extern);
        assert_eq!(r.reloc_type, 3);
    }

    #[test]
    fn test_parse_relocations_multiple_entries() {
        let mut data = Vec::new();
        // Entry 1: address=0, info=0 (all zeros)
        data.extend(0u32.to_le_bytes());
        data.extend(0u32.to_le_bytes());
        // Entry 2: address=0x200, info with pcrel=0, extern=0, type=0
        data.extend(0x200u32.to_le_bytes());
        data.extend(0x00FF_FFFFu32.to_le_bytes()); // symbolnum = max 24-bit

        let relocs = parse_relocations(&data, 0, 2, false).unwrap();
        assert_eq!(relocs.len(), 2);
        assert_eq!(relocs[0].address, 0);
        assert_eq!(relocs[1].address, 0x200);
        assert_eq!(relocs[1].symbol_or_section, 0x00FF_FFFF);
        assert!(!relocs[1].is_pcrel);
        assert!(!relocs[1].is_extern);
    }

    #[test]
    fn test_relocation_debug_clone_copy_eq() {
        let r = Relocation {
            address: 0x100,
            symbol_or_section: 1,
            is_extern: true,
            reloc_type: 2,
            length: 3,
            is_pcrel: false,
        };
        let r2 = r;
        assert_eq!(r, r2);
        let _ = format!("{:?}", r);
    }
}
