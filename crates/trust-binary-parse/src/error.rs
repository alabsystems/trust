// trust-binary-parse: error types for all binary parsing
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use thiserror::Error;

/// Errors from DWARF debug info parsing
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum DwarfError {
    #[error("unexpected end of data at offset {offset}")]
    UnexpectedEof { offset: usize },
    #[error("invalid DWARF version {version}")]
    InvalidVersion { version: u16 },
    #[error("unsupported address size {size}")]
    UnsupportedAddressSize { size: u8 },
    #[error("invalid abbreviation code {code}")]
    InvalidAbbrevCode { code: u64 },
    #[error("unsupported form {form}")]
    UnsupportedForm { form: u16 },
    #[error("invalid unit type {unit_type}")]
    InvalidUnitType { unit_type: u8 },
    #[error("invalid unit")]
    InvalidUnit,
    #[error("missing required attribute {name}")]
    MissingAttribute { name: &'static str },
    #[error("invalid LEB128 encoding")]
    InvalidLeb128,
    #[error("invalid line number program")]
    InvalidLineProgram,
    #[error("unsupported DWARF version {0}")]
    UnsupportedDwarfVersion(u16),
    #[error("invalid abbreviation")]
    InvalidAbbreviation,
    #[error("invalid form")]
    InvalidForm,
    #[error("type resolution failed at DIE offset {0}")]
    TypeResolutionFailed(usize),
    #[error("unknown tag 0x{0:04x}")]
    UnknownTag(u64),
}

/// Errors from binary format parsing (ELF, Mach-O, PE)
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ParseError {
    #[error("invalid magic number: 0x{0:08x}")]
    InvalidMagic(u32),
    #[error("unexpected end of data at offset {0}")]
    UnexpectedEof(usize),
    #[error("unsupported format: {0}")]
    UnsupportedFormat(String),
    #[error("invalid header field: {0}")]
    InvalidHeader(String),
    #[error("section not found: {0}")]
    SectionNotFound(String),
    #[error("buffer too small at offset {offset}: need {need}, have {have}")]
    BufferTooSmall { offset: usize, need: usize, have: usize },
    #[error("string index out of bounds: index {index}, table size {size}")]
    StringIndexOutOfBounds { index: u32, size: u32 },
    #[error("invalid UTF-8 at string index {index}")]
    InvalidUtf8 { index: u32 },
    #[error("data out of bounds: offset {offset}, end {end}, file size {file_size}")]
    DataOutOfBounds { offset: u64, end: u64, file_size: usize },
    #[error("invalid symbol table at offset {offset}, count {count}")]
    InvalidSymbolTable { offset: u32, count: u32 },
    #[error("invalid load command size: cmd 0x{cmd:x}, size {size}")]
    InvalidLoadCommandSize { cmd: u32, size: u32 },
    #[error("string offset out of bounds: offset {offset}, cmd size {cmd_size}")]
    StringOffsetOutOfBounds { offset: u32, cmd_size: u32 },

    // PE/COFF-specific errors
    #[error("invalid DOS magic: expected 0x5A4D ('MZ'), got 0x{0:04X}")]
    InvalidDosMagic(u16),
    #[error("invalid PE signature: expected 0x00004550 ('PE\\0\\0'), got 0x{0:08X}")]
    InvalidPeSignature(u32),
    #[error("unsupported PE optional header magic: 0x{0:04X}")]
    UnsupportedPeMagic(u16),
    #[error("PE data directory index {index} out of range (count: {count})")]
    DataDirectoryOutOfRange { index: u32, count: u32 },
    #[error("PE RVA 0x{rva:08X} could not be resolved to a file offset")]
    InvalidRva { rva: u32 },
    #[error("PE import table entry invalid at offset {offset}")]
    InvalidImportEntry { offset: usize },
    #[error("PE export table invalid: {reason}")]
    InvalidExportTable { reason: String },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dwarf_error_display_all_variants() {
        assert_eq!(
            DwarfError::UnexpectedEof { offset: 42 }.to_string(),
            "unexpected end of data at offset 42"
        );
        assert_eq!(
            DwarfError::InvalidVersion { version: 99 }.to_string(),
            "invalid DWARF version 99"
        );
        assert_eq!(
            DwarfError::UnsupportedAddressSize { size: 3 }.to_string(),
            "unsupported address size 3"
        );
        assert_eq!(
            DwarfError::InvalidAbbrevCode { code: 255 }.to_string(),
            "invalid abbreviation code 255"
        );
        assert_eq!(DwarfError::UnsupportedForm { form: 0x30 }.to_string(), "unsupported form 48");
        assert_eq!(DwarfError::InvalidUnitType { unit_type: 7 }.to_string(), "invalid unit type 7");
        assert_eq!(DwarfError::InvalidUnit.to_string(), "invalid unit");
        assert_eq!(
            DwarfError::MissingAttribute { name: "DW_AT_name" }.to_string(),
            "missing required attribute DW_AT_name"
        );
        assert_eq!(DwarfError::InvalidLeb128.to_string(), "invalid LEB128 encoding");
        assert_eq!(DwarfError::InvalidLineProgram.to_string(), "invalid line number program");
        assert_eq!(
            DwarfError::UnsupportedDwarfVersion(6).to_string(),
            "unsupported DWARF version 6"
        );
        assert_eq!(DwarfError::InvalidAbbreviation.to_string(), "invalid abbreviation");
        assert_eq!(DwarfError::InvalidForm.to_string(), "invalid form");
        assert_eq!(
            DwarfError::TypeResolutionFailed(0x100).to_string(),
            "type resolution failed at DIE offset 256"
        );
        assert_eq!(DwarfError::UnknownTag(0xABCD).to_string(), "unknown tag 0xabcd");
    }

    #[test]
    fn test_parse_error_display_all_variants() {
        assert_eq!(
            ParseError::InvalidMagic(0xDEADBEEF).to_string(),
            "invalid magic number: 0xdeadbeef"
        );
        assert_eq!(
            ParseError::UnexpectedEof(100).to_string(),
            "unexpected end of data at offset 100"
        );
        assert_eq!(
            ParseError::UnsupportedFormat("COFF".into()).to_string(),
            "unsupported format: COFF"
        );
        assert_eq!(
            ParseError::InvalidHeader("bad".into()).to_string(),
            "invalid header field: bad"
        );
        assert_eq!(
            ParseError::SectionNotFound(".text".into()).to_string(),
            "section not found: .text"
        );
        assert_eq!(
            ParseError::BufferTooSmall { offset: 10, need: 8, have: 12 }.to_string(),
            "buffer too small at offset 10: need 8, have 12"
        );
        assert_eq!(
            ParseError::StringIndexOutOfBounds { index: 50, size: 30 }.to_string(),
            "string index out of bounds: index 50, table size 30"
        );
        assert_eq!(
            ParseError::InvalidUtf8 { index: 5 }.to_string(),
            "invalid UTF-8 at string index 5"
        );
        assert_eq!(
            ParseError::DataOutOfBounds { offset: 0x100, end: 0x200, file_size: 0x150 }.to_string(),
            "data out of bounds: offset 256, end 512, file size 336"
        );
        assert_eq!(
            ParseError::InvalidSymbolTable { offset: 0x400, count: 10 }.to_string(),
            "invalid symbol table at offset 1024, count 10"
        );
        assert_eq!(
            ParseError::InvalidLoadCommandSize { cmd: 0x19, size: 4 }.to_string(),
            "invalid load command size: cmd 0x19, size 4"
        );
        assert_eq!(
            ParseError::StringOffsetOutOfBounds { offset: 100, cmd_size: 50 }.to_string(),
            "string offset out of bounds: offset 100, cmd size 50"
        );
    }

    #[test]
    fn test_parse_error_display_pe_variants() {
        assert_eq!(
            ParseError::InvalidDosMagic(0x1234).to_string(),
            "invalid DOS magic: expected 0x5A4D ('MZ'), got 0x1234"
        );
        assert_eq!(
            ParseError::InvalidPeSignature(0xDEAD).to_string(),
            "invalid PE signature: expected 0x00004550 ('PE\\0\\0'), got 0x0000DEAD"
        );
        assert_eq!(
            ParseError::UnsupportedPeMagic(0x10B).to_string(),
            "unsupported PE optional header magic: 0x010B"
        );
        assert_eq!(
            ParseError::DataDirectoryOutOfRange { index: 20, count: 16 }.to_string(),
            "PE data directory index 20 out of range (count: 16)"
        );
        assert_eq!(
            ParseError::InvalidRva { rva: 0xDEAD }.to_string(),
            "PE RVA 0x0000DEAD could not be resolved to a file offset"
        );
        assert_eq!(
            ParseError::InvalidImportEntry { offset: 0x500 }.to_string(),
            "PE import table entry invalid at offset 1280"
        );
        assert_eq!(
            ParseError::InvalidExportTable { reason: "no name".into() }.to_string(),
            "PE export table invalid: no name"
        );
    }

    #[test]
    fn test_errors_implement_debug() {
        let _ = format!("{:?}", DwarfError::InvalidUnit);
        let _ = format!("{:?}", ParseError::InvalidMagic(0));
    }

    #[test]
    fn test_errors_implement_std_error() {
        fn assert_error<E: std::error::Error>(_: &E) {}
        assert_error(&DwarfError::InvalidUnit);
        assert_error(&ParseError::InvalidMagic(0));
    }
}
