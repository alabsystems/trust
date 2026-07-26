// trust-binary-parse: zero-copy byte reading utilities
//
// All reads are from &[u8] slices with bounds checking. No unsafe code.
// Supports both little-endian and big-endian via the `swap` flag.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::error::ParseError;

/// A cursor over a byte slice with bounds-checked reads.
///
/// Supports little-endian (native for AArch64/x86_64) and big-endian
/// via the `swap` flag. All reads advance the internal offset.
#[derive(Debug, Clone)]
pub struct Cursor<'a> {
    data: &'a [u8],
    offset: usize,
    swap: bool,
}

impl<'a> Cursor<'a> {
    /// Create a new cursor at the given offset.
    pub fn new(data: &'a [u8], offset: usize, swap: bool) -> Self {
        Self { data, offset, swap }
    }

    /// Current offset position.
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Set the cursor position.
    pub fn set_offset(&mut self, offset: usize) {
        self.offset = offset;
    }

    /// Read a slice of `n` bytes and advance.
    pub fn read_bytes(&mut self, n: usize) -> Result<&'a [u8], ParseError> {
        let end = self.offset.checked_add(n).ok_or(ParseError::BufferTooSmall {
            offset: self.offset,
            need: n,
            have: self.data.len(),
        })?;
        if end > self.data.len() {
            return Err(ParseError::BufferTooSmall {
                offset: self.offset,
                need: n,
                have: self.data.len(),
            });
        }
        let slice = &self.data[self.offset..end];
        self.offset = end;
        Ok(slice)
    }

    /// Read a u8.
    pub fn read_u8(&mut self) -> Result<u8, ParseError> {
        let bytes = self.read_bytes(1)?;
        Ok(bytes[0])
    }

    /// Read a u16 with endian handling.
    pub fn read_u16(&mut self) -> Result<u16, ParseError> {
        let bytes = self.read_bytes(2)?;
        let val = u16::from_le_bytes([bytes[0], bytes[1]]);
        Ok(if self.swap { val.swap_bytes() } else { val })
    }

    /// Read a u32 with endian handling.
    pub fn read_u32(&mut self) -> Result<u32, ParseError> {
        let bytes = self.read_bytes(4)?;
        let val = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        Ok(if self.swap { val.swap_bytes() } else { val })
    }

    /// Read an i32 with endian handling.
    pub fn read_i32(&mut self) -> Result<i32, ParseError> {
        Ok(self.read_u32()? as i32)
    }

    /// Read an i64 with endian handling.
    pub fn read_i64(&mut self) -> Result<i64, ParseError> {
        Ok(self.read_u64()? as i64)
    }

    /// Read a u64 with endian handling.
    pub fn read_u64(&mut self) -> Result<u64, ParseError> {
        let bytes = self.read_bytes(8)?;
        let val = u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]);
        Ok(if self.swap { val.swap_bytes() } else { val })
    }

    /// Skip `n` bytes.
    pub fn skip(&mut self, n: usize) -> Result<(), ParseError> {
        self.read_bytes(n)?;
        Ok(())
    }
}

/// Read a fixed-size name field (e.g., 16-byte segment/section name).
/// Returns the string up to the first nul byte (or the full length if no nul).
pub fn read_fixed_name(bytes: &[u8]) -> &str {
    let end = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
    // Mach-O names are ASCII; if not valid UTF-8, fall back to empty.
    std::str::from_utf8(&bytes[..end]).unwrap_or("")
}

/// Read a nul-terminated string from the string table at `index`.
pub fn read_strtab_entry(strtab: &[u8], index: u32) -> Result<&str, ParseError> {
    let idx = index as usize;
    if idx >= strtab.len() {
        return Err(ParseError::StringIndexOutOfBounds { index, size: strtab.len() as u32 });
    }
    let remaining = &strtab[idx..];
    let end = remaining.iter().position(|&b| b == 0).unwrap_or(remaining.len());
    std::str::from_utf8(&remaining[..end]).map_err(|_| ParseError::InvalidUtf8 { index })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cursor_read_u32_le() {
        let data = [0x01, 0x02, 0x03, 0x04];
        let mut c = Cursor::new(&data, 0, false);
        let val = c.read_u32().expect("should read u32");
        assert_eq!(val, 0x0403_0201);
        assert_eq!(c.offset(), 4);
    }

    #[test]
    fn test_cursor_read_u32_swap() {
        // Same bytes, but swap=true reads as big-endian.
        let data = [0x01, 0x02, 0x03, 0x04];
        let mut c = Cursor::new(&data, 0, true);
        let val = c.read_u32().expect("should read u32");
        assert_eq!(val, 0x0102_0304);
    }

    #[test]
    fn test_cursor_buffer_too_small() {
        let data = [0x01, 0x02];
        let mut c = Cursor::new(&data, 0, false);
        let err = c.read_u32().unwrap_err();
        assert!(matches!(err, ParseError::BufferTooSmall { .. }));
    }

    #[test]
    fn test_read_fixed_name_nul_terminated() {
        let bytes = b"__TEXT\0\0\0\0\0\0\0\0\0\0";
        assert_eq!(read_fixed_name(bytes), "__TEXT");
    }

    #[test]
    fn test_read_strtab_entry_valid() {
        let strtab = b"\0_main\0_printf\0";
        assert_eq!(read_strtab_entry(strtab, 1).unwrap(), "_main");
        assert_eq!(read_strtab_entry(strtab, 7).unwrap(), "_printf");
    }

    #[test]
    fn test_read_strtab_entry_out_of_bounds() {
        let strtab = b"\0_main\0";
        let err = read_strtab_entry(strtab, 100).unwrap_err();
        assert!(matches!(err, ParseError::StringIndexOutOfBounds { .. }));
    }

    #[test]
    fn test_cursor_skip_advances_position() {
        let data = [0x01, 0x02, 0x03, 0x04, 0x05];
        let mut c = Cursor::new(&data, 0, false);
        c.skip(3).unwrap();
        assert_eq!(c.offset(), 3);
        assert_eq!(c.read_u8().unwrap(), 0x04);
    }

    #[test]
    fn test_cursor_read_u8_at_eof_returns_error() {
        let data = [0x42];
        let mut c = Cursor::new(&data, 0, false);
        assert_eq!(c.read_u8().unwrap(), 0x42);
        assert!(c.read_u8().is_err());
    }

    #[test]
    fn test_cursor_read_u16_swap() {
        let data = [0x01, 0x02];
        let mut c = Cursor::new(&data, 0, true);
        assert_eq!(c.read_u16().unwrap(), 0x0102);
    }

    #[test]
    fn test_cursor_read_u16_le() {
        let data = [0x01, 0x02];
        let mut c = Cursor::new(&data, 0, false);
        assert_eq!(c.read_u16().unwrap(), 0x0201);
    }

    #[test]
    fn test_cursor_read_u64_le() {
        let data = 0x0102_0304_0506_0708u64.to_le_bytes();
        let mut c = Cursor::new(&data, 0, false);
        assert_eq!(c.read_u64().unwrap(), 0x0102_0304_0506_0708);
    }

    #[test]
    fn test_cursor_read_u64_swap() {
        let data = 0x0102_0304_0506_0708u64.to_le_bytes();
        let mut c = Cursor::new(&data, 0, true);
        // swap bytes: LE stored, then swap_bytes
        assert_eq!(c.read_u64().unwrap(), 0x0807_0605_0403_0201);
    }

    #[test]
    fn test_cursor_read_i32() {
        let data = (-42i32).to_le_bytes();
        let mut c = Cursor::new(&data, 0, false);
        assert_eq!(c.read_i32().unwrap(), -42);
    }

    #[test]
    fn test_cursor_read_i64() {
        let data = (-12345i64).to_le_bytes();
        let mut c = Cursor::new(&data, 0, false);
        assert_eq!(c.read_i64().unwrap(), -12345);
    }

    #[test]
    fn test_cursor_read_bytes_overflow_returns_error() {
        let data = [0x01, 0x02];
        let mut c = Cursor::new(&data, 0, false);
        assert!(c.read_bytes(usize::MAX).is_err());
    }

    #[test]
    fn test_read_fixed_name_all_nul_returns_empty() {
        let bytes = [0u8; 16];
        assert_eq!(read_fixed_name(&bytes), "");
    }

    #[test]
    fn test_read_fixed_name_no_nul_returns_full() {
        let bytes = b"0123456789abcdef";
        assert_eq!(read_fixed_name(bytes), "0123456789abcdef");
    }

    #[test]
    fn test_read_strtab_entry_invalid_utf8_returns_error() {
        let strtab = [0xFF, 0xFE, 0x00];
        let err = read_strtab_entry(&strtab, 0).unwrap_err();
        assert!(matches!(err, ParseError::InvalidUtf8 { .. }));
    }

    #[test]
    fn test_read_strtab_entry_empty_string_at_index_zero() {
        let strtab = b"\0rest";
        assert_eq!(read_strtab_entry(strtab, 0).unwrap(), "");
    }

    #[test]
    fn test_cursor_set_offset_and_read() {
        let data = [0x01, 0x02, 0x03, 0x04];
        let mut c = Cursor::new(&data, 0, false);
        c.set_offset(2);
        assert_eq!(c.offset(), 2);
        assert_eq!(c.read_u8().unwrap(), 0x03);
    }

    #[test]
    fn test_cursor_clone() {
        let data = [0x01, 0x02, 0x03, 0x04];
        let c = Cursor::new(&data, 2, false);
        let c2 = c.clone();
        assert_eq!(c.offset(), c2.offset());
    }

    #[test]
    fn test_cursor_skip_past_end_returns_error() {
        let data = [0x01, 0x02];
        let mut c = Cursor::new(&data, 0, false);
        assert!(c.skip(3).is_err());
    }
}
