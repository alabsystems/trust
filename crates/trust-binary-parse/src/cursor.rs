// trust-binary-parse: Byte cursor for DWARF sections
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::error::DwarfError;
use crate::leb128::{read_sleb128, read_uleb128};

/// A lightweight byte cursor for little-endian DWARF sections.
pub struct Cursor<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    /// Construct a new cursor at position 0.
    #[must_use]
    pub fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0 }
    }

    /// Read a single byte.
    pub fn read_u8(&mut self) -> Result<u8, DwarfError> {
        let byte =
            *self.data.get(self.pos).ok_or(DwarfError::UnexpectedEof { offset: self.pos })?;
        self.pos += 1;
        Ok(byte)
    }

    /// Read a little-endian 16-bit integer.
    pub fn read_u16_le(&mut self) -> Result<u16, DwarfError> {
        let bytes = self.read_bytes(2)?;
        Ok(u16::from_le_bytes([bytes[0], bytes[1]]))
    }

    /// Read a little-endian 32-bit integer.
    pub fn read_u32_le(&mut self) -> Result<u32, DwarfError> {
        let bytes = self.read_bytes(4)?;
        Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    /// Read a little-endian 64-bit integer.
    pub fn read_u64_le(&mut self) -> Result<u64, DwarfError> {
        let bytes = self.read_bytes(8)?;
        Ok(u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    }

    /// Read an unsigned LEB128 value.
    pub fn read_uleb128(&mut self) -> Result<u64, DwarfError> {
        read_uleb128(self.data, &mut self.pos)
    }

    /// Read a signed LEB128 value.
    pub fn read_sleb128(&mut self) -> Result<i64, DwarfError> {
        read_sleb128(self.data, &mut self.pos)
    }

    /// Read a fixed number of raw bytes.
    pub fn read_bytes(&mut self, n: usize) -> Result<&'a [u8], DwarfError> {
        let end = self.pos.checked_add(n).ok_or(DwarfError::UnexpectedEof { offset: self.pos })?;
        let bytes =
            self.data.get(self.pos..end).ok_or(DwarfError::UnexpectedEof { offset: self.pos })?;
        self.pos = end;
        Ok(bytes)
    }

    /// Read a null-terminated UTF-8 string.
    pub fn read_null_terminated_string(&mut self) -> Result<&'a str, DwarfError> {
        let start = self.pos;
        let relative_end = self.data[start..]
            .iter()
            .position(|byte| *byte == 0)
            .ok_or(DwarfError::UnexpectedEof { offset: start })?;
        let end = start + relative_end;
        let string =
            std::str::from_utf8(&self.data[start..end]).map_err(|_| DwarfError::InvalidUnit)?;
        self.pos = end + 1;
        Ok(string)
    }

    /// Return the current byte position.
    #[must_use]
    pub fn position(&self) -> usize {
        self.pos
    }

    /// Set the current byte position.
    pub fn set_position(&mut self, pos: usize) -> Result<(), DwarfError> {
        if pos > self.data.len() {
            return Err(DwarfError::UnexpectedEof { offset: pos });
        }
        self.pos = pos;
        Ok(())
    }

    /// Return the number of unread bytes remaining.
    #[must_use]
    pub fn remaining(&self) -> usize {
        self.data.len().saturating_sub(self.pos)
    }

    /// Return true if all bytes were consumed.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.remaining() == 0
    }

    pub fn read_uint(&mut self, width: usize) -> Result<u64, DwarfError> {
        match width {
            1 => Ok(u64::from(self.read_u8()?)),
            2 => Ok(u64::from(self.read_u16_le()?)),
            4 => Ok(u64::from(self.read_u32_le()?)),
            8 => self.read_u64_le(),
            _ => Err(DwarfError::InvalidUnit),
        }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

#[cfg(test)]
mod tests {
    use super::Cursor;

    #[test]
    fn test_cursor_reads_scalars_and_bytes_expected() {
        let bytes = [
            0x12, 0x34, 0x12, 0x78, 0x56, 0x34, 0x12, 0xef, 0xcd, 0xab, 0x90, 0x78, 0x56, 0x34,
            0x12, 0xe5, 0x8e, 0x26, 0x9b, 0xf1, 0x59, b'h', b'i', 0,
        ];
        let mut cursor = Cursor::new(&bytes);

        assert_eq!(cursor.read_u8().unwrap(), 0x12);
        assert_eq!(cursor.read_u16_le().unwrap(), 0x1234);
        assert_eq!(cursor.read_u32_le().unwrap(), 0x1234_5678);
        assert_eq!(cursor.read_u64_le().unwrap(), 0x1234_5678_90ab_cdef);
        assert_eq!(cursor.read_uleb128().unwrap(), 624_485);
        assert_eq!(cursor.read_sleb128().unwrap(), -624_485);
        assert_eq!(cursor.read_null_terminated_string().unwrap(), "hi");
        assert!(cursor.is_empty());
    }

    #[test]
    fn test_cursor_read_bytes_position_and_remaining_expected() {
        let mut cursor = Cursor::new(&[1, 2, 3, 4, 5]);

        assert_eq!(cursor.read_bytes(2).unwrap(), &[1, 2]);
        assert_eq!(cursor.position(), 2);
        assert_eq!(cursor.remaining(), 3);

        cursor.set_position(4).unwrap();
        assert_eq!(cursor.read_u8().unwrap(), 5);
        assert!(cursor.is_empty());
    }

    #[test]
    fn test_cursor_set_position_out_of_bounds_returns_error() {
        let mut cursor = Cursor::new(&[1, 2, 3]);
        assert!(cursor.set_position(4).is_err());
    }

    #[test]
    fn test_cursor_read_u8_empty_returns_error() {
        let mut cursor = Cursor::new(&[]);
        assert!(cursor.read_u8().is_err());
    }

    #[test]
    fn test_cursor_read_u16_le_insufficient_bytes_returns_error() {
        let mut cursor = Cursor::new(&[0x01]);
        assert!(cursor.read_u16_le().is_err());
    }

    #[test]
    fn test_cursor_read_u32_le_insufficient_bytes_returns_error() {
        let mut cursor = Cursor::new(&[0x01, 0x02, 0x03]);
        assert!(cursor.read_u32_le().is_err());
    }

    #[test]
    fn test_cursor_read_u64_le_insufficient_bytes_returns_error() {
        let mut cursor = Cursor::new(&[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]);
        assert!(cursor.read_u64_le().is_err());
    }

    #[test]
    fn test_cursor_read_null_terminated_string_no_null_returns_error() {
        let mut cursor = Cursor::new(b"no null terminator");
        assert!(cursor.read_null_terminated_string().is_err());
    }

    #[test]
    fn test_cursor_read_null_terminated_string_invalid_utf8_returns_error() {
        let mut cursor = Cursor::new(&[0xFF, 0xFE, 0x00]);
        assert!(cursor.read_null_terminated_string().is_err());
    }

    #[test]
    fn test_cursor_read_null_terminated_string_empty_string() {
        let mut cursor = Cursor::new(&[0x00, b'a', 0x00]);
        assert_eq!(cursor.read_null_terminated_string().unwrap(), "");
        assert_eq!(cursor.position(), 1);
    }

    #[test]
    fn test_cursor_read_bytes_zero_succeeds() {
        let mut cursor = Cursor::new(&[1, 2, 3]);
        let bytes = cursor.read_bytes(0).unwrap();
        assert!(bytes.is_empty());
        assert_eq!(cursor.position(), 0);
    }

    #[test]
    fn test_cursor_read_bytes_overflow_returns_error() {
        let mut cursor = Cursor::new(&[1, 2, 3]);
        assert!(cursor.read_bytes(usize::MAX).is_err());
    }

    #[test]
    fn test_cursor_read_uint_supported_widths() {
        // Little-endian encoding: least significant byte first
        let data = [
            0x42, // 1-byte: 0x42
            0x34, 0x12, // 2-byte LE: 0x1234
            0x78, 0x56, 0x34, 0x12, // 4-byte LE: 0x1234_5678
            0xEF, 0xCD, 0xAB, 0x90, 0x78, 0x56, 0x34,
            0x12, // 8-byte LE: 0x1234_5678_90AB_CDEF
        ];
        let mut cursor = Cursor::new(&data);
        assert_eq!(cursor.read_uint(1).unwrap(), 0x42);
        assert_eq!(cursor.read_uint(2).unwrap(), 0x1234);
        assert_eq!(cursor.read_uint(4).unwrap(), 0x1234_5678);
        assert_eq!(cursor.read_uint(8).unwrap(), 0x1234_5678_90AB_CDEF);
    }

    #[test]
    fn test_cursor_read_uint_unsupported_widths_return_error() {
        let mut cursor = Cursor::new(&[0; 16]);
        assert!(cursor.read_uint(0).is_err());
        assert!(cursor.read_uint(3).is_err());
        assert!(cursor.read_uint(5).is_err());
        assert!(cursor.read_uint(6).is_err());
        assert!(cursor.read_uint(7).is_err());
    }

    #[test]
    fn test_cursor_new_starts_at_zero() {
        let cursor = Cursor::new(&[1, 2, 3]);
        assert_eq!(cursor.position(), 0);
        assert_eq!(cursor.remaining(), 3);
        assert!(!cursor.is_empty());
    }

    #[test]
    fn test_cursor_len_returns_data_length() {
        let cursor = Cursor::new(&[1, 2, 3, 4, 5]);
        assert_eq!(cursor.len(), 5);
    }

    #[test]
    fn test_cursor_set_position_to_end_is_valid() {
        let mut cursor = Cursor::new(&[1, 2, 3]);
        cursor.set_position(3).unwrap();
        assert!(cursor.is_empty());
        assert_eq!(cursor.remaining(), 0);
    }

    #[test]
    fn test_cursor_remaining_decreases_after_reads() {
        let mut cursor = Cursor::new(&[1, 2, 3, 4]);
        assert_eq!(cursor.remaining(), 4);
        cursor.read_u8().unwrap();
        assert_eq!(cursor.remaining(), 3);
        cursor.read_u16_le().unwrap();
        assert_eq!(cursor.remaining(), 1);
    }
}
