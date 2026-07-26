// trust-binary-parse: DWARF string tables
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::error::DwarfError;

/// A borrowed view over `.debug_str`.
#[derive(Debug, Clone, Copy)]
pub struct StringTable<'a> {
    data: &'a [u8],
}

impl<'a> StringTable<'a> {
    /// Construct a string table wrapper from raw section bytes.
    #[must_use]
    pub fn new(data: &'a [u8]) -> Self {
        Self { data }
    }

    /// Look up a null-terminated UTF-8 string at `offset`.
    pub fn get_string(&self, offset: usize) -> Result<&'a str, DwarfError> {
        let bytes = self.data.get(offset..).ok_or(DwarfError::UnexpectedEof { offset })?;
        let end =
            bytes.iter().position(|byte| *byte == 0).ok_or(DwarfError::UnexpectedEof { offset })?;
        std::str::from_utf8(&bytes[..end]).map_err(|_| DwarfError::InvalidUnit)
    }
}

#[cfg(test)]
mod tests {
    use super::StringTable;

    #[test]
    fn test_string_table_valid_offset_returns_expected_string() {
        let table = StringTable::new(b"hello\0world\0");
        assert_eq!(table.get_string(0).unwrap(), "hello");
        assert_eq!(table.get_string(6).unwrap(), "world");
    }

    #[test]
    fn test_string_table_out_of_bounds_offset_returns_error() {
        let table = StringTable::new(b"hello\0");
        assert!(table.get_string(10).is_err());
    }

    // --- Edge case tests for improved coverage ---

    #[test]
    fn test_string_table_empty_string_at_offset_zero() {
        let table = StringTable::new(b"\0hello\0");
        assert_eq!(table.get_string(0).unwrap(), "");
    }

    #[test]
    fn test_string_table_empty_data() {
        let table = StringTable::new(b"");
        assert!(table.get_string(0).is_err());
    }

    #[test]
    fn test_string_table_no_null_terminator_returns_error() {
        let table = StringTable::new(b"hello");
        assert!(table.get_string(0).is_err());
    }

    #[test]
    fn test_string_table_consecutive_strings() {
        let table = StringTable::new(b"aaa\0bbb\0ccc\0");
        assert_eq!(table.get_string(0).unwrap(), "aaa");
        assert_eq!(table.get_string(4).unwrap(), "bbb");
        assert_eq!(table.get_string(8).unwrap(), "ccc");
    }

    #[test]
    fn test_string_table_exact_boundary_offset() {
        let data = b"hello\0";
        let table = StringTable::new(data);
        // Offset 5 is the null byte, so string at 5 is empty
        // Actually offset 5 is past the null of "hello", next is out of bounds (len=6)
        assert_eq!(table.get_string(5).unwrap(), "");
    }
}
