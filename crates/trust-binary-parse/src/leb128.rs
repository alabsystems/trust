// trust-binary-parse: LEB128 decoding utilities
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::error::DwarfError;

/// Read an unsigned LEB128 value from `data` at `offset`.
pub fn read_uleb128(data: &[u8], offset: &mut usize) -> Result<u64, DwarfError> {
    let mut result = 0_u128;
    let mut shift = 0_u32;

    for _ in 0..10 {
        let byte = *data.get(*offset).ok_or(DwarfError::UnexpectedEof { offset: *offset })?;
        *offset += 1;

        result |= u128::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return u64::try_from(result).map_err(|_| DwarfError::InvalidLeb128);
        }

        shift += 7;
    }

    Err(DwarfError::InvalidLeb128)
}

/// Read a signed LEB128 value from `data` at `offset`.
pub fn read_sleb128(data: &[u8], offset: &mut usize) -> Result<i64, DwarfError> {
    let mut result = 0_i128;
    let mut shift = 0_u32;

    for _ in 0..10 {
        let byte = *data.get(*offset).ok_or(DwarfError::UnexpectedEof { offset: *offset })?;
        *offset += 1;

        result |= i128::from(byte & 0x7f) << shift;
        shift += 7;

        if byte & 0x80 == 0 {
            if byte & 0x40 != 0 {
                result |= (!0_i128) << shift;
            }
            return i64::try_from(result).map_err(|_| DwarfError::InvalidLeb128);
        }
    }

    Err(DwarfError::InvalidLeb128)
}

#[cfg(test)]
mod tests {
    use super::{read_sleb128, read_uleb128};

    fn encode_uleb128(mut value: u64) -> Vec<u8> {
        let mut bytes = Vec::new();
        loop {
            let mut byte = (value & 0x7f) as u8;
            value >>= 7;
            if value != 0 {
                byte |= 0x80;
            }
            bytes.push(byte);
            if value == 0 {
                break;
            }
        }
        bytes
    }

    fn encode_sleb128(mut value: i64) -> Vec<u8> {
        let mut bytes = Vec::new();
        loop {
            let byte = (value & 0x7f) as u8;
            let sign_bit_set = byte & 0x40 != 0;
            value >>= 7;

            let done = (value == 0 && !sign_bit_set) || (value == -1 && sign_bit_set);
            bytes.push(if done { byte } else { byte | 0x80 });

            if done {
                break;
            }
        }
        bytes
    }

    #[test]
    fn test_uleb128_known_values_decode_expected() {
        for expected in [0_u64, 1, 127, 128, 16_256, 624_485, u32::MAX as u64, u64::MAX] {
            let encoded = encode_uleb128(expected);
            let mut offset = 0;
            let decoded = read_uleb128(&encoded, &mut offset).unwrap();
            assert_eq!(decoded, expected);
            assert_eq!(offset, encoded.len());
        }
    }

    #[test]
    fn test_sleb128_known_values_decode_expected() {
        for expected in [0_i64, 1, -1, 63, -64, 64, -65, 624_485, -624_485, i64::MAX, i64::MIN] {
            let encoded = encode_sleb128(expected);
            let mut offset = 0;
            let decoded = read_sleb128(&encoded, &mut offset).unwrap();
            assert_eq!(decoded, expected);
            assert_eq!(offset, encoded.len());
        }
    }

    #[test]
    fn test_uleb128_truncated_sequence_returns_error() {
        let mut offset = 0;
        let error = read_uleb128(&[0x80], &mut offset).unwrap_err();
        assert_eq!(error.to_string(), "unexpected end of data at offset 1");
    }

    #[test]
    fn test_sleb128_overlong_sequence_returns_error() {
        let bytes = [0x80_u8; 11];
        let mut offset = 0;
        let error = read_sleb128(&bytes, &mut offset).unwrap_err();
        assert_eq!(error.to_string(), "invalid LEB128 encoding");
    }

    #[test]
    fn test_uleb128_empty_data_returns_error() {
        let mut offset = 0;
        assert!(read_uleb128(&[], &mut offset).is_err());
    }

    #[test]
    fn test_sleb128_empty_data_returns_error() {
        let mut offset = 0;
        assert!(read_sleb128(&[], &mut offset).is_err());
    }

    #[test]
    fn test_uleb128_overlong_returns_error() {
        let bytes = [0x80_u8; 11];
        let mut offset = 0;
        assert!(read_uleb128(&bytes, &mut offset).is_err());
    }

    #[test]
    fn test_uleb128_single_byte_values() {
        for val in [0u64, 1, 63, 127] {
            let encoded = encode_uleb128(val);
            assert_eq!(encoded.len(), 1);
            let mut offset = 0;
            assert_eq!(read_uleb128(&encoded, &mut offset).unwrap(), val);
        }
    }

    #[test]
    fn test_sleb128_single_byte_values() {
        for val in [0i64, 1, -1, 63, -64] {
            let encoded = encode_sleb128(val);
            assert_eq!(encoded.len(), 1);
            let mut offset = 0;
            assert_eq!(read_sleb128(&encoded, &mut offset).unwrap(), val);
        }
    }

    #[test]
    fn test_uleb128_offset_advances_correctly() {
        let mut data = encode_uleb128(128);
        data.extend(encode_uleb128(256));
        let mut offset = 0;
        assert_eq!(read_uleb128(&data, &mut offset).unwrap(), 128);
        let mid = offset;
        assert_eq!(read_uleb128(&data, &mut offset).unwrap(), 256);
        assert!(offset > mid);
        assert_eq!(offset, data.len());
    }

    #[test]
    fn test_sleb128_offset_advances_correctly() {
        let mut data = encode_sleb128(-128);
        data.extend(encode_sleb128(256));
        let mut offset = 0;
        assert_eq!(read_sleb128(&data, &mut offset).unwrap(), -128);
        assert_eq!(read_sleb128(&data, &mut offset).unwrap(), 256);
        assert_eq!(offset, data.len());
    }

    #[test]
    fn test_uleb128_truncated_multibyte_returns_error() {
        // 128 encodes as [0x80, 0x01]; truncate to just [0x80]
        let mut offset = 0;
        assert!(read_uleb128(&[0x80], &mut offset).is_err());
    }
}
