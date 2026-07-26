// trust-binary-parse: Binary format auto-detection via magic bytes
//
// Inspects the first few bytes of a binary to determine its format.
// Supports ELF, Mach-O (thin and fat/universal), and PE/COFF.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Detected binary format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum BinaryFormat {
    /// ELF binary (Linux, BSD, etc.)
    Elf,
    /// Mach-O binary (macOS, iOS)
    MachO,
    /// Fat/universal Mach-O binary containing multiple architectures
    FatMachO,
    /// PE/COFF binary (Windows)
    Pe,
}

impl BinaryFormat {
    /// Human-readable name for the format.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Elf => "ELF",
            Self::MachO => "Mach-O",
            Self::FatMachO => "Fat Mach-O",
            Self::Pe => "PE/COFF",
        }
    }
}

/// Detect the binary format from raw bytes by inspecting magic bytes.
///
/// Returns `None` if the format is unrecognized or the input is too short.
///
/// Magic byte signatures:
/// - ELF: `7F 45 4C 46` (`\x7FELF`)
/// - Mach-O 64 LE: `CF FA ED FE` (MH_MAGIC_64 little-endian)
/// - Mach-O 64 BE: `FE ED FA CF` (MH_MAGIC_64 big-endian)
/// - Fat Mach-O: `CA FE BA BE` or `CA FE BA BF`
/// - PE: `4D 5A` (`MZ`)
#[must_use]
pub fn detect_format(data: &[u8]) -> Option<BinaryFormat> {
    if data.len() < 4 {
        return None;
    }

    let magic4 = [data[0], data[1], data[2], data[3]];

    // ELF: 0x7F 'E' 'L' 'F'
    if magic4 == [0x7F, b'E', b'L', b'F'] {
        return Some(BinaryFormat::Elf);
    }

    // Mach-O 64-bit little-endian (native on AArch64/x86_64)
    // MH_MAGIC_64 = 0xFEEDFACF, stored LE = CF FA ED FE
    if magic4 == [0xCF, 0xFA, 0xED, 0xFE] {
        return Some(BinaryFormat::MachO);
    }

    // Mach-O 64-bit big-endian (needs swap)
    // MH_CIGAM_64 = 0xCFFAEDFE, stored BE = FE ED FA CF
    if magic4 == [0xFE, 0xED, 0xFA, 0xCF] {
        return Some(BinaryFormat::MachO);
    }

    // Fat/universal Mach-O
    // FAT_MAGIC = 0xCAFEBABE (big-endian)
    if magic4 == [0xCA, 0xFE, 0xBA, 0xBE] {
        return Some(BinaryFormat::FatMachO);
    }
    // FAT_MAGIC_64 = 0xCAFEBABF (big-endian, 64-bit offsets)
    if magic4 == [0xCA, 0xFE, 0xBA, 0xBF] {
        return Some(BinaryFormat::FatMachO);
    }

    // PE/COFF: DOS 'MZ' magic
    if data[0] == b'M' && data[1] == b'Z' {
        return Some(BinaryFormat::Pe);
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::fx::FxHashSet;

    #[test]
    fn test_detect_elf() {
        let data = [0x7F, b'E', b'L', b'F', 0x02, 0x01, 0x01, 0x00];
        assert_eq!(detect_format(&data), Some(BinaryFormat::Elf));
    }

    #[test]
    fn test_detect_macho_le() {
        // MH_MAGIC_64 little-endian
        let data = [0xCF, 0xFA, 0xED, 0xFE, 0x0C, 0x00, 0x00, 0x01];
        assert_eq!(detect_format(&data), Some(BinaryFormat::MachO));
    }

    #[test]
    fn test_detect_macho_be() {
        // MH_CIGAM_64 big-endian
        let data = [0xFE, 0xED, 0xFA, 0xCF, 0x00, 0x00, 0x00, 0x00];
        assert_eq!(detect_format(&data), Some(BinaryFormat::MachO));
    }

    #[test]
    fn test_detect_fat_macho() {
        let data = [0xCA, 0xFE, 0xBA, 0xBE, 0x00, 0x00, 0x00, 0x02];
        assert_eq!(detect_format(&data), Some(BinaryFormat::FatMachO));
    }

    #[test]
    fn test_detect_fat_macho_64() {
        let data = [0xCA, 0xFE, 0xBA, 0xBF, 0x00, 0x00, 0x00, 0x02];
        assert_eq!(detect_format(&data), Some(BinaryFormat::FatMachO));
    }

    #[test]
    fn test_detect_pe() {
        let data = [b'M', b'Z', 0x90, 0x00, 0x03, 0x00, 0x00, 0x00];
        assert_eq!(detect_format(&data), Some(BinaryFormat::Pe));
    }

    #[test]
    fn test_detect_unknown() {
        let data = [0x00, 0x00, 0x00, 0x00];
        assert_eq!(detect_format(&data), None);
    }

    #[test]
    fn test_detect_too_short() {
        assert_eq!(detect_format(&[0x7F, b'E', b'L']), None);
        assert_eq!(detect_format(&[]), None);
    }

    #[test]
    fn test_format_name() {
        assert_eq!(BinaryFormat::Elf.name(), "ELF");
        assert_eq!(BinaryFormat::MachO.name(), "Mach-O");
        assert_eq!(BinaryFormat::FatMachO.name(), "Fat Mach-O");
        assert_eq!(BinaryFormat::Pe.name(), "PE/COFF");
    }

    // --- Edge case tests for improved coverage ---

    #[test]
    fn test_detect_exactly_4_bytes_elf() {
        let data = [0x7F, b'E', b'L', b'F'];
        assert_eq!(detect_format(&data), Some(BinaryFormat::Elf));
    }

    #[test]
    fn test_detect_exactly_4_bytes_macho() {
        let data = [0xCF, 0xFA, 0xED, 0xFE];
        assert_eq!(detect_format(&data), Some(BinaryFormat::MachO));
    }

    #[test]
    fn test_detect_single_byte_returns_none() {
        assert_eq!(detect_format(&[0x7F]), None);
    }

    #[test]
    fn test_detect_two_bytes_mz_too_short() {
        // 'MZ' needs at least 4 bytes for the general check
        // but the PE check only looks at data[0] and data[1]
        // and we need data.len() >= 4
        assert_eq!(detect_format(&[b'M', b'Z', 0x90]), None);
    }

    #[test]
    fn test_detect_pe_minimal_4_bytes() {
        let data = [b'M', b'Z', 0x00, 0x00];
        assert_eq!(detect_format(&data), Some(BinaryFormat::Pe));
    }

    #[test]
    fn test_detect_nearly_matching_magic_returns_none() {
        // Off by one from ELF magic
        assert_eq!(detect_format(&[0x7F, b'E', b'L', b'G']), None);
        // Off by one from Mach-O LE
        assert_eq!(detect_format(&[0xCF, 0xFA, 0xED, 0xFF]), None);
        // Off by one from fat magic
        assert_eq!(detect_format(&[0xCA, 0xFE, 0xBA, 0xBD]), None);
    }

    #[test]
    fn test_detect_all_zeros_returns_none() {
        assert_eq!(detect_format(&[0, 0, 0, 0]), None);
    }

    #[test]
    fn test_detect_all_ff_returns_none() {
        assert_eq!(detect_format(&[0xFF, 0xFF, 0xFF, 0xFF]), None);
    }

    #[test]
    fn test_format_clone_copy_eq_hash() {
        let fmt = BinaryFormat::Elf;
        let cloned = fmt;
        assert_eq!(fmt, cloned);

        // Verify all variants are distinct
        assert_ne!(BinaryFormat::Elf, BinaryFormat::MachO);
        assert_ne!(BinaryFormat::MachO, BinaryFormat::FatMachO);
        assert_ne!(BinaryFormat::FatMachO, BinaryFormat::Pe);

        // Verify Hash works (compiles)
        let mut set = FxHashSet::default();
        set.insert(BinaryFormat::Elf);
        set.insert(BinaryFormat::MachO);
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_format_debug() {
        assert_eq!(format!("{:?}", BinaryFormat::Elf), "Elf");
        assert_eq!(format!("{:?}", BinaryFormat::MachO), "MachO");
        assert_eq!(format!("{:?}", BinaryFormat::FatMachO), "FatMachO");
        assert_eq!(format!("{:?}", BinaryFormat::Pe), "Pe");
    }
}
