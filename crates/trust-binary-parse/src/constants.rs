// trust-binary-parse: Mach-O constants
//
// Reference: Apple's mach-o/loader.h, mach-o/nlist.h, mach-o/reloc.h
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// -- Magic numbers --

/// 64-bit Mach-O magic (little-endian, native on AArch64/x86_64).
pub const MH_MAGIC_64: u32 = 0xFEED_FACF;
/// 64-bit Mach-O magic (big-endian, needs byte-swap).
pub const MH_CIGAM_64: u32 = 0xCFFA_EDFE;
/// Fat/universal binary magic.
pub const FAT_MAGIC: u32 = 0xCAFE_BABE;
/// Fat/universal binary magic (64-bit offsets).
pub const FAT_MAGIC_64: u32 = 0xCAFE_BABF;

// -- File types --

#[cfg(test)]
pub const MH_OBJECT: u32 = 0x1;
#[cfg(test)]
pub const MH_EXECUTE: u32 = 0x2;
#[cfg(test)]
pub const MH_FVMLIB: u32 = 0x3;
#[cfg(test)]
pub const MH_CORE: u32 = 0x4;
#[cfg(test)]
pub const MH_PRELOAD: u32 = 0x5;
#[cfg(test)]
pub const MH_DYLIB: u32 = 0x6;
#[cfg(test)]
pub const MH_DYLINKER: u32 = 0x7;
#[cfg(test)]
pub const MH_BUNDLE: u32 = 0x8;
#[cfg(test)]
pub const MH_DYLIB_STUB: u32 = 0x9;
#[cfg(test)]
pub const MH_DSYM: u32 = 0xA;
#[cfg(test)]
pub const MH_KEXT_BUNDLE: u32 = 0xB;
#[cfg(test)]
pub const MH_FILESET: u32 = 0xC;

// -- CPU types --

pub const CPU_TYPE_X86_64: i32 = 0x0100_0007;
pub const CPU_TYPE_ARM64: i32 = 0x0100_000C;

// CPU subtypes
#[cfg(test)]
pub const CPU_SUBTYPE_ARM64_ALL: i32 = 0;
#[cfg(test)]
pub const CPU_SUBTYPE_X86_64_ALL: i32 = 3;

// -- Load command types --

pub const LC_REQ_DYLD: u32 = 0x8000_0000;

pub const LC_SEGMENT_64: u32 = 0x19;
pub const LC_SYMTAB: u32 = 0x02;
pub const LC_DYSYMTAB: u32 = 0x0B;
pub const LC_LOAD_DYLIB: u32 = 0x0C;
pub const LC_ID_DYLIB: u32 = 0x0D;
pub const LC_LOAD_DYLINKER: u32 = 0x0E;
pub const LC_ID_DYLINKER: u32 = 0x0F;
pub const LC_UUID: u32 = 0x1B;
pub const LC_RPATH: u32 = 0x1C | LC_REQ_DYLD;
pub const LC_CODE_SIGNATURE: u32 = 0x1D;
pub const LC_SEGMENT_SPLIT_INFO: u32 = 0x1E;
pub const LC_REEXPORT_DYLIB: u32 = 0x1F | LC_REQ_DYLD;
pub const LC_LAZY_LOAD_DYLIB: u32 = 0x20;
pub const LC_ENCRYPTION_INFO_64: u32 = 0x2C;
pub const LC_DYLD_INFO: u32 = 0x22;
pub const LC_DYLD_INFO_ONLY: u32 = 0x22 | LC_REQ_DYLD;
pub const LC_FUNCTION_STARTS: u32 = 0x26;
pub const LC_MAIN: u32 = 0x28 | LC_REQ_DYLD;
pub const LC_DATA_IN_CODE: u32 = 0x29;
pub const LC_SOURCE_VERSION: u32 = 0x2A;
pub const LC_DYLIB_CODE_SIGN_DRS: u32 = 0x2B;
pub const LC_LINKER_OPTIMIZATION_HINT: u32 = 0x2E;
pub const LC_BUILD_VERSION: u32 = 0x32;
pub const LC_DYLD_EXPORTS_TRIE: u32 = 0x33 | LC_REQ_DYLD;
pub const LC_DYLD_CHAINED_FIXUPS: u32 = 0x34 | LC_REQ_DYLD;
#[cfg(test)]
pub const LC_FILESET_ENTRY: u32 = 0x35 | LC_REQ_DYLD;

// -- Segment / Section flags --

/// Maximum segment name length (including nul).
pub const SEG_NAME_LEN: usize = 16;
/// Maximum section name length (including nul).
pub const SECT_NAME_LEN: usize = 16;

// Section types (low 8 bits of flags).
#[cfg(test)]
pub const S_REGULAR: u32 = 0x0;
pub const S_ZEROFILL: u32 = 0x1;
#[cfg(test)]
pub const S_CSTRING_LITERALS: u32 = 0x2;

pub const SECTION_TYPE_MASK: u32 = 0x0000_00FF;
#[cfg(test)]
pub const SECTION_ATTRIBUTES_MASK: u32 = 0xFFFF_FF00;
pub const S_ATTR_PURE_INSTRUCTIONS: u32 = 0x8000_0000;
pub const S_ATTR_SOME_INSTRUCTIONS: u32 = 0x0000_0400;

// -- Symbol table (nlist_64) --

// N_TYPE mask
pub const N_STAB: u8 = 0xE0;
pub const N_PEXT: u8 = 0x10;
pub const N_TYPE_MASK: u8 = 0x0E;
pub const N_EXT: u8 = 0x01;

// N_TYPE values (after masking with N_TYPE_MASK)
pub const N_UNDF: u8 = 0x00;
pub const N_ABS: u8 = 0x02;
pub const N_SECT: u8 = 0x0E;
pub const N_INDR: u8 = 0x0A;

// -- Relocation --

/// Size of a relocation_info struct.
pub const RELOC_SIZE: usize = 8;

// AArch64 relocation types
#[cfg(test)]
pub const ARM64_RELOC_UNSIGNED: u8 = 0;
#[cfg(test)]
pub const ARM64_RELOC_SUBTRACTOR: u8 = 1;
#[cfg(test)]
pub const ARM64_RELOC_BRANCH26: u8 = 2;
#[cfg(test)]
pub const ARM64_RELOC_PAGE21: u8 = 3;
#[cfg(test)]
pub const ARM64_RELOC_PAGEOFF12: u8 = 4;
#[cfg(test)]
pub const ARM64_RELOC_GOT_LOAD_PAGE21: u8 = 5;
#[cfg(test)]
pub const ARM64_RELOC_GOT_LOAD_PAGEOFF12: u8 = 6;
#[cfg(test)]
pub const ARM64_RELOC_POINTER_TO_GOT: u8 = 7;
#[cfg(test)]
pub const ARM64_RELOC_TLVP_LOAD_PAGE21: u8 = 8;
#[cfg(test)]
pub const ARM64_RELOC_TLVP_LOAD_PAGEOFF12: u8 = 9;
#[cfg(test)]
pub const ARM64_RELOC_ADDEND: u8 = 10;

// -- Struct sizes --

pub const MACH_HEADER_64_SIZE: usize = 32;
pub const LOAD_COMMAND_SIZE: usize = 8;
#[cfg(test)]
pub const SEGMENT_COMMAND_64_SIZE: usize = 72;
#[cfg(test)]
pub const SECTION_64_SIZE: usize = 80;
pub const NLIST_64_SIZE: usize = 16;
#[cfg(test)]
pub const SYMTAB_COMMAND_SIZE: usize = 24;
#[cfg(test)]
pub const DYSYMTAB_COMMAND_SIZE: usize = 80;
pub const UUID_COMMAND_SIZE: usize = 24;
#[cfg(test)]
pub const ENTRY_POINT_COMMAND_SIZE: usize = 24;
#[cfg(test)]
pub const BUILD_VERSION_COMMAND_SIZE: usize = 24;
#[cfg(test)]
pub const BUILD_TOOL_VERSION_SIZE: usize = 8;
#[cfg(test)]
pub const LINKEDIT_DATA_COMMAND_SIZE: usize = 16;
#[cfg(test)]
pub const SOURCE_VERSION_COMMAND_SIZE: usize = 16;
#[cfg(test)]
pub const FAT_HEADER_SIZE: usize = 8;
#[cfg(test)]
pub const FAT_ARCH_SIZE: usize = 20;
#[cfg(test)]
pub const FAT_ARCH_64_SIZE: usize = 32;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_macho_magic_values_are_distinct() {
        let magics = [MH_MAGIC_64, MH_CIGAM_64, FAT_MAGIC, FAT_MAGIC_64];
        for (i, a) in magics.iter().enumerate() {
            for (j, b) in magics.iter().enumerate() {
                if i != j {
                    assert_ne!(a, b, "magic values at indices {i} and {j} must differ");
                }
            }
        }
    }

    #[test]
    fn test_macho_magic_byte_swap_relationship() {
        // MH_MAGIC_64 and MH_CIGAM_64 should be byte-swapped versions of each other
        assert_eq!(MH_MAGIC_64.swap_bytes(), MH_CIGAM_64);
        assert_eq!(MH_CIGAM_64.swap_bytes(), MH_MAGIC_64);
    }

    #[test]
    fn test_file_types_are_sequential() {
        assert_eq!(MH_OBJECT, 1);
        assert_eq!(MH_EXECUTE, 2);
        assert_eq!(MH_FVMLIB, 3);
        assert_eq!(MH_CORE, 4);
        assert_eq!(MH_PRELOAD, 5);
        assert_eq!(MH_DYLIB, 6);
        assert_eq!(MH_DYLINKER, 7);
        assert_eq!(MH_BUNDLE, 8);
        assert_eq!(MH_DYLIB_STUB, 9);
        assert_eq!(MH_DSYM, 0xA);
        assert_eq!(MH_KEXT_BUNDLE, 0xB);
        assert_eq!(MH_FILESET, 0xC);
    }

    #[test]
    fn test_cpu_types_have_64bit_flag() {
        // CPU_TYPE_ARM64 and CPU_TYPE_X86_64 should have bit 24 set (ABI64 flag)
        let abi64_flag: i32 = 0x0100_0000;
        assert_ne!(CPU_TYPE_X86_64 & abi64_flag, 0);
        assert_ne!(CPU_TYPE_ARM64 & abi64_flag, 0);
    }

    #[test]
    fn test_n_type_mask_values() {
        // N_TYPE_MASK should isolate bits 1-3
        assert_eq!(N_TYPE_MASK, 0x0E);
        // N_EXT should be bit 0
        assert_eq!(N_EXT, 0x01);
        // N_STAB should cover upper 3 bits
        assert_eq!(N_STAB, 0xE0);
        // Masks should not overlap with each other
        assert_eq!(N_TYPE_MASK & N_EXT, 0);
        assert_eq!(N_TYPE_MASK & N_STAB, 0);
    }

    #[test]
    fn test_section_type_and_attributes_masks_disjoint() {
        assert_eq!(SECTION_TYPE_MASK & SECTION_ATTRIBUTES_MASK, 0);
        assert_eq!(SECTION_TYPE_MASK | SECTION_ATTRIBUTES_MASK, 0xFFFF_FFFF);
    }

    #[test]
    fn test_struct_sizes_are_reasonable() {
        assert_eq!(MACH_HEADER_64_SIZE, 32);
        assert_eq!(LOAD_COMMAND_SIZE, 8);
        assert_eq!(SEGMENT_COMMAND_64_SIZE, 72);
        assert_eq!(SECTION_64_SIZE, 80);
        assert_eq!(NLIST_64_SIZE, 16);
        // All struct sizes should be multiples of 4 (natural alignment)
        let sizes = [
            MACH_HEADER_64_SIZE,
            LOAD_COMMAND_SIZE,
            SEGMENT_COMMAND_64_SIZE,
            SECTION_64_SIZE,
            NLIST_64_SIZE,
            SYMTAB_COMMAND_SIZE,
            DYSYMTAB_COMMAND_SIZE,
            UUID_COMMAND_SIZE,
            ENTRY_POINT_COMMAND_SIZE,
            BUILD_VERSION_COMMAND_SIZE,
            BUILD_TOOL_VERSION_SIZE,
            LINKEDIT_DATA_COMMAND_SIZE,
            SOURCE_VERSION_COMMAND_SIZE,
            FAT_HEADER_SIZE,
            FAT_ARCH_SIZE,
            FAT_ARCH_64_SIZE,
        ];
        for size in sizes {
            assert_eq!(size % 4, 0, "struct size {size} should be 4-byte aligned");
        }
    }

    #[test]
    fn test_lc_req_dyld_flag() {
        // LC_REQ_DYLD is the high bit
        assert_eq!(LC_REQ_DYLD, 0x8000_0000);
        // Commands with LC_REQ_DYLD should have that bit set
        assert_ne!(LC_RPATH & LC_REQ_DYLD, 0);
        assert_ne!(LC_DYLD_INFO_ONLY & LC_REQ_DYLD, 0);
        assert_ne!(LC_MAIN & LC_REQ_DYLD, 0);
        assert_ne!(LC_DYLD_EXPORTS_TRIE & LC_REQ_DYLD, 0);
        assert_ne!(LC_DYLD_CHAINED_FIXUPS & LC_REQ_DYLD, 0);
        // Commands without LC_REQ_DYLD should not have that bit
        assert_eq!(LC_SEGMENT_64 & LC_REQ_DYLD, 0);
        assert_eq!(LC_SYMTAB & LC_REQ_DYLD, 0);
        assert_eq!(LC_UUID & LC_REQ_DYLD, 0);
    }

    #[test]
    fn test_relocation_types_are_sequential() {
        assert_eq!(ARM64_RELOC_UNSIGNED, 0);
        assert_eq!(ARM64_RELOC_SUBTRACTOR, 1);
        assert_eq!(ARM64_RELOC_BRANCH26, 2);
        assert_eq!(ARM64_RELOC_PAGE21, 3);
        assert_eq!(ARM64_RELOC_PAGEOFF12, 4);
        assert_eq!(ARM64_RELOC_GOT_LOAD_PAGE21, 5);
        assert_eq!(ARM64_RELOC_GOT_LOAD_PAGEOFF12, 6);
        assert_eq!(ARM64_RELOC_POINTER_TO_GOT, 7);
        assert_eq!(ARM64_RELOC_TLVP_LOAD_PAGE21, 8);
        assert_eq!(ARM64_RELOC_TLVP_LOAD_PAGEOFF12, 9);
        assert_eq!(ARM64_RELOC_ADDEND, 10);
    }

    #[test]
    fn test_name_length_constants() {
        assert_eq!(SEG_NAME_LEN, 16);
        assert_eq!(SECT_NAME_LEN, 16);
    }
}
