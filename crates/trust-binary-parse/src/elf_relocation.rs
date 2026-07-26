// trust-binary-parse: ELF64 relocation and dynamic section parsing
//
// Parses SHT_RELA, SHT_REL, and SHT_DYNAMIC sections from ELF64 binaries.
// Includes relocation type constants for x86_64 and AArch64.
//
// Reference: ELF specification (System V ABI), gABI
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::error::ParseError;
use crate::read::Cursor;

// --- ELF section header types for relocation/dynamic ---

/// Section contains relocation entries with explicit addends (Elf64_Rela).
pub const SHT_RELA: u32 = 4;
/// Section contains relocation entries without explicit addends (Elf64_Rel).
pub const SHT_REL: u32 = 9;
/// Section contains dynamic linking information.
pub const SHT_DYNAMIC: u32 = 6;

// --- Entry sizes ---

/// Size of an Elf64_Rel entry (r_offset + r_info).
const ELF64_REL_SIZE: usize = 16;
/// Size of an Elf64_Rela entry (r_offset + r_info + r_addend).
const ELF64_RELA_SIZE: usize = 24;
/// Size of an Elf64_Dyn entry (d_tag + d_val).
const ELF64_DYN_SIZE: usize = 16;

// --- x86_64 relocation types ---

/// No relocation.
#[cfg(test)]
pub const R_X86_64_NONE: u32 = 0;
/// Direct 64-bit.
#[cfg(test)]
pub const R_X86_64_64: u32 = 1;
/// PC-relative 32-bit.
#[cfg(test)]
pub const R_X86_64_PC32: u32 = 2;
/// 32-bit GOT entry.
#[cfg(test)]
pub const R_X86_64_GOT32: u32 = 3;
/// 32-bit PLT address.
#[cfg(test)]
pub const R_X86_64_PLT32: u32 = 4;
/// Copy symbol at runtime.
#[cfg(test)]
pub const R_X86_64_COPY: u32 = 5;
/// Create GOT entry.
#[cfg(test)]
pub const R_X86_64_GLOB_DAT: u32 = 6;
/// Create PLT entry (jump slot).
#[cfg(test)]
pub const R_X86_64_JUMP_SLOT: u32 = 7;
/// Adjust by program base.
#[cfg(test)]
pub const R_X86_64_RELATIVE: u32 = 8;
/// 32-bit PC-relative offset to GOT.
#[cfg(test)]
pub const R_X86_64_GOTPCREL: u32 = 9;
/// Direct 32-bit zero-extended.
#[cfg(test)]
pub const R_X86_64_32: u32 = 10;
/// Direct 32-bit sign-extended.
#[cfg(test)]
pub const R_X86_64_32S: u32 = 11;

// --- AArch64 relocation types ---

/// No relocation.
#[cfg(test)]
pub const R_AARCH64_NONE: u32 = 0;
/// Direct 64-bit.
#[cfg(test)]
pub const R_AARCH64_ABS64: u32 = 257;
/// Direct 32-bit.
#[cfg(test)]
pub const R_AARCH64_ABS32: u32 = 258;
/// PC-relative 32-bit.
#[cfg(test)]
pub const R_AARCH64_PREL32: u32 = 261;
/// Page-relative ADRP (bits [32:12] of offset).
#[cfg(test)]
pub const R_AARCH64_ADR_PREL_PG_HI21: u32 = 275;
/// ADD immediate (bits [11:0] of offset).
#[cfg(test)]
pub const R_AARCH64_ADD_ABS_LO12_NC: u32 = 277;
/// B/BL 26-bit jump.
#[cfg(test)]
pub const R_AARCH64_JUMP26: u32 = 282;
/// BL 26-bit call.
#[cfg(test)]
pub const R_AARCH64_CALL26: u32 = 283;
/// LDR/STR 64-bit (bits [11:3] of offset).
#[cfg(test)]
pub const R_AARCH64_LDST64_ABS_LO12_NC: u32 = 286;
/// Create GOT entry.
#[cfg(test)]
pub const R_AARCH64_GLOB_DAT: u32 = 1025;
/// Create PLT entry (jump slot).
#[cfg(test)]
pub const R_AARCH64_JUMP_SLOT: u32 = 1026;
/// Adjust by program base.
#[cfg(test)]
pub const R_AARCH64_RELATIVE: u32 = 1027;

// --- Dynamic section tag constants ---

/// Marks end of dynamic section.
pub const DT_NULL: i64 = 0;
/// Name of needed library (string table offset).
pub const DT_NEEDED: i64 = 1;
/// Size in bytes of PLT relocation entries.
/// Address of string table.
pub const DT_STRTAB: i64 = 5;
/// Address of termination function.
#[cfg(test)]
pub const DT_FINI: i64 = 13;
/// Address of PLT relocation entries.
#[cfg(test)]
pub const DT_JMPREL: i64 = 23;

// --- Parsed structures ---

/// Extract the symbol table index from an ELF64 relocation r_info field.
#[must_use]
pub fn elf64_r_sym(info: u64) -> u32 {
    (info >> 32) as u32
}

/// Extract the relocation type from an ELF64 relocation r_info field.
#[must_use]
pub fn elf64_r_type(info: u64) -> u32 {
    (info & 0xffff_ffff) as u32
}

/// Parsed ELF64 relocation entry without explicit addend (Elf64_Rel).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Elf64Rel {
    /// Offset where the relocation applies.
    pub(crate) r_offset: u64,
    /// Relocation type and symbol index packed together.
    pub(crate) r_info: u64,
}

impl Elf64Rel {
    /// Symbol table index this relocation refers to.
    #[must_use]
    pub fn sym(&self) -> u32 {
        elf64_r_sym(self.r_info)
    }

    /// Architecture-specific relocation type.
    #[must_use]
    pub fn reloc_type(&self) -> u32 {
        elf64_r_type(self.r_info)
    }
}

/// Parsed ELF64 relocation entry with explicit addend (Elf64_Rela).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Elf64Rela {
    /// Offset where the relocation applies.
    pub(crate) r_offset: u64,
    /// Relocation type and symbol index packed together.
    pub(crate) r_info: u64,
    /// Explicit addend for the relocation computation.
    pub(crate) r_addend: i64,
}

impl Elf64Rela {
    /// Symbol table index this relocation refers to.
    #[must_use]
    pub fn sym(&self) -> u32 {
        elf64_r_sym(self.r_info)
    }

    /// Architecture-specific relocation type.
    #[must_use]
    pub fn reloc_type(&self) -> u32 {
        elf64_r_type(self.r_info)
    }
}

/// Parsed ELF64 dynamic section entry (Elf64_Dyn).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Elf64Dyn {
    /// Dynamic entry tag (DT_NEEDED, DT_STRTAB, etc.).
    pub(crate) d_tag: i64,
    /// Tag-dependent value (address or offset).
    pub(crate) d_val: u64,
}

/// A relocation entry resolved against the symbol table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedRelocation {
    /// Virtual address where the relocation applies.
    pub(crate) offset: u64,
    /// Name of the symbol this relocation references.
    pub(crate) sym_name: String,
    /// Architecture-specific relocation type.
    pub(crate) reloc_type: u32,
    /// Explicit addend.
    pub(crate) addend: i64,
}

// --- Parsing functions ---

/// Parse Elf64_Rela entries from a section's raw data.
pub fn parse_rela_entries(data: &[u8], swap: bool) -> Result<Vec<Elf64Rela>, ParseError> {
    if data.is_empty() {
        return Ok(Vec::new());
    }
    let count = data.len() / ELF64_RELA_SIZE;
    let mut entries = Vec::with_capacity(count);
    let mut cursor = Cursor::new(data, 0, swap);

    for _ in 0..count {
        let r_offset = cursor.read_u64()?;
        let r_info = cursor.read_u64()?;
        let r_addend = cursor.read_i64()?;
        entries.push(Elf64Rela { r_offset, r_info, r_addend });
    }

    Ok(entries)
}

/// Parse Elf64_Rel entries from a section's raw data.
pub fn parse_rel_entries(data: &[u8], swap: bool) -> Result<Vec<Elf64Rel>, ParseError> {
    if data.is_empty() {
        return Ok(Vec::new());
    }
    let count = data.len() / ELF64_REL_SIZE;
    let mut entries = Vec::with_capacity(count);
    let mut cursor = Cursor::new(data, 0, swap);

    for _ in 0..count {
        let r_offset = cursor.read_u64()?;
        let r_info = cursor.read_u64()?;
        entries.push(Elf64Rel { r_offset, r_info });
    }

    Ok(entries)
}

/// Parse Elf64_Dyn entries from a section's raw data.
///
/// Parsing stops at DT_NULL or end of data.
pub fn parse_dynamic_entries(data: &[u8], swap: bool) -> Result<Vec<Elf64Dyn>, ParseError> {
    if data.is_empty() {
        return Ok(Vec::new());
    }
    let max_count = data.len() / ELF64_DYN_SIZE;
    let mut entries = Vec::with_capacity(max_count);
    let mut cursor = Cursor::new(data, 0, swap);

    for _ in 0..max_count {
        let d_tag = cursor.read_i64()?;
        let d_val = cursor.read_u64()?;
        entries.push(Elf64Dyn { d_tag, d_val });
        if d_tag == DT_NULL {
            break;
        }
    }

    Ok(entries)
}

/// Human-readable name for an x86_64 ELF relocation type.
#[must_use]
#[cfg(test)]
pub fn x86_64_reloc_name(r_type: u32) -> &'static str {
    match r_type {
        R_X86_64_NONE => "R_X86_64_NONE",
        R_X86_64_64 => "R_X86_64_64",
        R_X86_64_PC32 => "R_X86_64_PC32",
        R_X86_64_GOT32 => "R_X86_64_GOT32",
        R_X86_64_PLT32 => "R_X86_64_PLT32",
        R_X86_64_COPY => "R_X86_64_COPY",
        R_X86_64_GLOB_DAT => "R_X86_64_GLOB_DAT",
        R_X86_64_JUMP_SLOT => "R_X86_64_JUMP_SLOT",
        R_X86_64_RELATIVE => "R_X86_64_RELATIVE",
        R_X86_64_GOTPCREL => "R_X86_64_GOTPCREL",
        R_X86_64_32 => "R_X86_64_32",
        R_X86_64_32S => "R_X86_64_32S",
        _ => "UNKNOWN",
    }
}

/// Human-readable name for an AArch64 ELF relocation type.
#[must_use]
#[cfg(test)]
pub fn aarch64_reloc_name(r_type: u32) -> &'static str {
    match r_type {
        R_AARCH64_NONE => "R_AARCH64_NONE",
        R_AARCH64_ABS64 => "R_AARCH64_ABS64",
        R_AARCH64_ABS32 => "R_AARCH64_ABS32",
        R_AARCH64_PREL32 => "R_AARCH64_PREL32",
        R_AARCH64_ADR_PREL_PG_HI21 => "R_AARCH64_ADR_PREL_PG_HI21",
        R_AARCH64_ADD_ABS_LO12_NC => "R_AARCH64_ADD_ABS_LO12_NC",
        R_AARCH64_JUMP26 => "R_AARCH64_JUMP26",
        R_AARCH64_CALL26 => "R_AARCH64_CALL26",
        R_AARCH64_LDST64_ABS_LO12_NC => "R_AARCH64_LDST64_ABS_LO12_NC",
        R_AARCH64_GLOB_DAT => "R_AARCH64_GLOB_DAT",
        R_AARCH64_JUMP_SLOT => "R_AARCH64_JUMP_SLOT",
        R_AARCH64_RELATIVE => "R_AARCH64_RELATIVE",
        _ => "UNKNOWN",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_elf64_r_sym_and_type() {
        // Symbol index 5, type 7 (R_X86_64_JUMP_SLOT)
        let info: u64 = (5u64 << 32) | 7;
        assert_eq!(elf64_r_sym(info), 5);
        assert_eq!(elf64_r_type(info), 7);

        // Large symbol index
        let info2: u64 = (0xFFFF_FFFFu64 << 32) | 0x0000_0403;
        assert_eq!(elf64_r_sym(info2), 0xFFFF_FFFF);
        assert_eq!(elf64_r_type(info2), 0x0403);
    }

    #[test]
    fn test_elf64_rel_methods() {
        let rel = Elf64Rel { r_offset: 0x1000, r_info: (3u64 << 32) | R_X86_64_GLOB_DAT as u64 };
        assert_eq!(rel.sym(), 3);
        assert_eq!(rel.reloc_type(), R_X86_64_GLOB_DAT);
    }

    #[test]
    fn test_elf64_rela_methods() {
        let rela = Elf64Rela {
            r_offset: 0x2000,
            r_info: (7u64 << 32) | R_AARCH64_JUMP_SLOT as u64,
            r_addend: -4,
        };
        assert_eq!(rela.sym(), 7);
        assert_eq!(rela.reloc_type(), R_AARCH64_JUMP_SLOT);
        assert_eq!(rela.r_addend, -4);
    }

    #[test]
    fn test_x86_64_reloc_names() {
        assert_eq!(x86_64_reloc_name(R_X86_64_NONE), "R_X86_64_NONE");
        assert_eq!(x86_64_reloc_name(R_X86_64_JUMP_SLOT), "R_X86_64_JUMP_SLOT");
        assert_eq!(x86_64_reloc_name(R_X86_64_PLT32), "R_X86_64_PLT32");
        assert_eq!(x86_64_reloc_name(R_X86_64_RELATIVE), "R_X86_64_RELATIVE");
        assert_eq!(x86_64_reloc_name(9999), "UNKNOWN");
    }

    #[test]
    fn test_aarch64_reloc_names() {
        assert_eq!(aarch64_reloc_name(R_AARCH64_NONE), "R_AARCH64_NONE");
        assert_eq!(aarch64_reloc_name(R_AARCH64_JUMP_SLOT), "R_AARCH64_JUMP_SLOT");
        assert_eq!(aarch64_reloc_name(R_AARCH64_CALL26), "R_AARCH64_CALL26");
        assert_eq!(aarch64_reloc_name(R_AARCH64_ABS64), "R_AARCH64_ABS64");
        assert_eq!(aarch64_reloc_name(9999), "UNKNOWN");
    }

    #[test]
    fn test_parse_rela_entries() {
        // Build 2 Rela entries as raw bytes (little-endian)
        let mut data = Vec::new();
        // Entry 0: offset=0x1000, info=(sym=1, type=7), addend=0
        data.extend_from_slice(&0x1000u64.to_le_bytes()); // r_offset
        data.extend_from_slice(&((1u64 << 32) | 7).to_le_bytes()); // r_info
        data.extend_from_slice(&0i64.to_le_bytes()); // r_addend
        // Entry 1: offset=0x2000, info=(sym=3, type=1026), addend=-8
        data.extend_from_slice(&0x2000u64.to_le_bytes());
        data.extend_from_slice(&((3u64 << 32) | 1026).to_le_bytes());
        data.extend_from_slice(&(-8i64).to_le_bytes());

        let entries = parse_rela_entries(&data, false).expect("should parse rela");
        assert_eq!(entries.len(), 2);

        assert_eq!(entries[0].r_offset, 0x1000);
        assert_eq!(entries[0].sym(), 1);
        assert_eq!(entries[0].reloc_type(), R_X86_64_JUMP_SLOT);
        assert_eq!(entries[0].r_addend, 0);

        assert_eq!(entries[1].r_offset, 0x2000);
        assert_eq!(entries[1].sym(), 3);
        assert_eq!(entries[1].reloc_type(), R_AARCH64_JUMP_SLOT);
        assert_eq!(entries[1].r_addend, -8);
    }

    #[test]
    fn test_parse_rel_entries() {
        let mut data = Vec::new();
        // Entry 0: offset=0x3000, info=(sym=2, type=6)
        data.extend_from_slice(&0x3000u64.to_le_bytes());
        data.extend_from_slice(&((2u64 << 32) | 6).to_le_bytes());
        // Entry 1: offset=0x4000, info=(sym=5, type=1)
        data.extend_from_slice(&0x4000u64.to_le_bytes());
        data.extend_from_slice(&((5u64 << 32) | 1).to_le_bytes());

        let entries = parse_rel_entries(&data, false).expect("should parse rel");
        assert_eq!(entries.len(), 2);

        assert_eq!(entries[0].r_offset, 0x3000);
        assert_eq!(entries[0].sym(), 2);
        assert_eq!(entries[0].reloc_type(), R_X86_64_GLOB_DAT);

        assert_eq!(entries[1].r_offset, 0x4000);
        assert_eq!(entries[1].sym(), 5);
        assert_eq!(entries[1].reloc_type(), R_X86_64_64);
    }

    #[test]
    fn test_parse_dynamic_entries() {
        let mut data = Vec::new();
        // DT_NEEDED with d_val=0x10
        data.extend_from_slice(&DT_NEEDED.to_le_bytes());
        data.extend_from_slice(&0x10u64.to_le_bytes());
        // DT_STRTAB with d_val=0x400200
        data.extend_from_slice(&DT_STRTAB.to_le_bytes());
        data.extend_from_slice(&0x400200u64.to_le_bytes());
        // DT_NULL terminates
        data.extend_from_slice(&DT_NULL.to_le_bytes());
        data.extend_from_slice(&0u64.to_le_bytes());

        let entries = parse_dynamic_entries(&data, false).expect("should parse dynamic");
        assert_eq!(entries.len(), 3);

        assert_eq!(entries[0].d_tag, DT_NEEDED);
        assert_eq!(entries[0].d_val, 0x10);

        assert_eq!(entries[1].d_tag, DT_STRTAB);
        assert_eq!(entries[1].d_val, 0x400200);

        assert_eq!(entries[2].d_tag, DT_NULL);
        assert_eq!(entries[2].d_val, 0);
    }

    #[test]
    fn test_parse_empty_entries() {
        let empty: &[u8] = &[];
        assert!(parse_rela_entries(empty, false).unwrap().is_empty());
        assert!(parse_rel_entries(empty, false).unwrap().is_empty());
        assert!(parse_dynamic_entries(empty, false).unwrap().is_empty());
    }

    #[test]
    fn test_dynamic_stops_at_dt_null() {
        let mut data = Vec::new();
        // DT_NEEDED
        data.extend_from_slice(&DT_NEEDED.to_le_bytes());
        data.extend_from_slice(&1u64.to_le_bytes());
        // DT_NULL
        data.extend_from_slice(&DT_NULL.to_le_bytes());
        data.extend_from_slice(&0u64.to_le_bytes());
        // Extra entry after DT_NULL (should not be parsed)
        data.extend_from_slice(&DT_FINI.to_le_bytes());
        data.extend_from_slice(&0xDEADu64.to_le_bytes());

        let entries = parse_dynamic_entries(&data, false).expect("should parse");
        assert_eq!(entries.len(), 2); // DT_NEEDED + DT_NULL only
    }
}
