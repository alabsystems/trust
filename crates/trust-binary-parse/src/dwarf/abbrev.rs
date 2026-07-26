// trust-binary-parse: DWARF abbreviation tables
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use crate::cursor::Cursor;
use crate::dwarf::constants::{DW_CHILDREN_NO, DW_CHILDREN_YES, DW_FORM_IMPLICIT_CONST};
use crate::error::DwarfError;

/// A single abbreviation table contribution from `.debug_abbrev`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbbrevTable {
    entries: FxHashMap<u64, AbbrevEntry>,
}

/// A single abbreviation entry keyed by abbreviation code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbbrevEntry {
    pub(crate) tag: u64,
    pub(crate) has_children: bool,
    pub(crate) attributes: Vec<AbbrevAttribute>,
}

/// An attribute specification within an abbreviation entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbbrevAttribute {
    pub(crate) name: u64,
    pub(crate) form: u64,
    pub(crate) implicit_const: Option<i64>,
}

impl AbbrevTable {
    /// Parse an abbreviation table starting at `offset`.
    pub fn parse(data: &[u8], offset: usize) -> Result<Self, DwarfError> {
        let mut cursor = Cursor::new(data);
        cursor.set_position(offset)?;
        let mut entries = FxHashMap::default();

        loop {
            let code = cursor.read_uleb128()?;
            if code == 0 {
                break;
            }

            let tag = cursor.read_uleb128()?;
            let has_children = match cursor.read_u8()? {
                DW_CHILDREN_NO => false,
                DW_CHILDREN_YES => true,
                _ => return Err(DwarfError::InvalidAbbreviation),
            };

            let mut attributes = Vec::new();
            loop {
                let name = cursor.read_uleb128()?;
                let form = cursor.read_uleb128()?;
                if name == 0 && form == 0 {
                    break;
                }
                if name == 0 || form == 0 {
                    return Err(DwarfError::InvalidAbbreviation);
                }

                let implicit_const = if form == DW_FORM_IMPLICIT_CONST {
                    Some(cursor.read_sleb128()?)
                } else {
                    None
                };
                attributes.push(AbbrevAttribute { name, form, implicit_const });
            }

            entries.insert(code, AbbrevEntry { tag, has_children, attributes });
        }

        Ok(Self { entries })
    }

    #[must_use]
    pub fn get(&self, code: u64) -> Option<&AbbrevEntry> {
        self.entries.get(&code)
    }
}

#[cfg(test)]
mod tests {
    use super::{AbbrevAttribute, AbbrevEntry, AbbrevTable};
    use crate::dwarf::constants::{
        DW_AT_BYTE_SIZE, DW_AT_ENCODING, DW_AT_NAME, DW_FORM_DATA1, DW_FORM_IMPLICIT_CONST,
        DW_FORM_STRING, DW_TAG_BASE_TYPE,
    };

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
    fn test_abbrev_table_handcrafted_sequence_parses_expected() {
        let mut bytes = Vec::new();
        bytes.extend(encode_uleb128(1));
        bytes.extend(encode_uleb128(DW_TAG_BASE_TYPE));
        bytes.push(0);
        bytes.extend(encode_uleb128(DW_AT_NAME));
        bytes.extend(encode_uleb128(DW_FORM_STRING));
        bytes.extend(encode_uleb128(DW_AT_BYTE_SIZE));
        bytes.extend(encode_uleb128(DW_FORM_DATA1));
        bytes.extend(encode_uleb128(DW_AT_ENCODING));
        bytes.extend(encode_uleb128(DW_FORM_IMPLICIT_CONST));
        bytes.extend(encode_sleb128(5));
        bytes.push(0);
        bytes.push(0);
        bytes.push(0);

        let table = AbbrevTable::parse(&bytes, 0).unwrap();
        let expected = AbbrevEntry {
            tag: DW_TAG_BASE_TYPE,
            has_children: false,
            attributes: vec![
                AbbrevAttribute { name: DW_AT_NAME, form: DW_FORM_STRING, implicit_const: None },
                AbbrevAttribute {
                    name: DW_AT_BYTE_SIZE,
                    form: DW_FORM_DATA1,
                    implicit_const: None,
                },
                AbbrevAttribute {
                    name: DW_AT_ENCODING,
                    form: DW_FORM_IMPLICIT_CONST,
                    implicit_const: Some(5),
                },
            ],
        };

        assert_eq!(table.get(1), Some(&expected));
        assert!(table.get(2).is_none());
    }

    // --- Edge case tests for improved coverage ---

    #[test]
    fn test_abbrev_table_empty_returns_empty() {
        // Just a terminator
        let bytes = [0u8];
        let table = AbbrevTable::parse(&bytes, 0).unwrap();
        assert!(table.get(1).is_none());
    }

    #[test]
    fn test_abbrev_table_multiple_entries() {
        let mut bytes = Vec::new();
        // Entry 1: DW_TAG_BASE_TYPE, no children, one attribute
        bytes.extend(encode_uleb128(1));
        bytes.extend(encode_uleb128(DW_TAG_BASE_TYPE));
        bytes.push(0); // no children
        bytes.extend(encode_uleb128(DW_AT_NAME));
        bytes.extend(encode_uleb128(DW_FORM_STRING));
        bytes.push(0);
        bytes.push(0);

        // Entry 2: tag 17 (compile unit), has children, two attributes
        bytes.extend(encode_uleb128(2));
        bytes.extend(encode_uleb128(17)); // DW_TAG_COMPILE_UNIT
        bytes.push(1); // has children
        bytes.extend(encode_uleb128(DW_AT_NAME));
        bytes.extend(encode_uleb128(DW_FORM_STRING));
        bytes.extend(encode_uleb128(DW_AT_BYTE_SIZE));
        bytes.extend(encode_uleb128(DW_FORM_DATA1));
        bytes.push(0);
        bytes.push(0);

        bytes.push(0); // terminator

        let table = AbbrevTable::parse(&bytes, 0).unwrap();
        let entry1 = table.get(1).expect("should have entry 1");
        assert_eq!(entry1.tag, DW_TAG_BASE_TYPE);
        assert!(!entry1.has_children);
        assert_eq!(entry1.attributes.len(), 1);

        let entry2 = table.get(2).expect("should have entry 2");
        assert_eq!(entry2.tag, 17);
        assert!(entry2.has_children);
        assert_eq!(entry2.attributes.len(), 2);
    }

    #[test]
    fn test_abbrev_table_invalid_children_byte() {
        let mut bytes = Vec::new();
        bytes.extend(encode_uleb128(1));
        bytes.extend(encode_uleb128(DW_TAG_BASE_TYPE));
        bytes.push(2); // invalid: not DW_CHILDREN_YES or DW_CHILDREN_NO
        let err = AbbrevTable::parse(&bytes, 0).unwrap_err();
        assert!(err.to_string().contains("invalid abbreviation"));
    }

    #[test]
    fn test_abbrev_table_offset_nonzero() {
        // Put some junk before the abbrev table
        let mut bytes = vec![0xFF, 0xFF, 0xFF]; // 3 bytes of junk
        // Then a valid table at offset 3
        bytes.extend(encode_uleb128(1));
        bytes.extend(encode_uleb128(DW_TAG_BASE_TYPE));
        bytes.push(0); // no children
        bytes.extend(encode_uleb128(DW_AT_NAME));
        bytes.extend(encode_uleb128(DW_FORM_STRING));
        bytes.push(0);
        bytes.push(0);
        bytes.push(0); // terminator

        let table = AbbrevTable::parse(&bytes, 3).unwrap();
        assert!(table.get(1).is_some());
    }

    #[test]
    fn test_abbrev_table_implicit_const_negative() {
        let mut bytes = Vec::new();
        bytes.extend(encode_uleb128(1));
        bytes.extend(encode_uleb128(DW_TAG_BASE_TYPE));
        bytes.push(0);
        bytes.extend(encode_uleb128(DW_AT_ENCODING));
        bytes.extend(encode_uleb128(DW_FORM_IMPLICIT_CONST));
        bytes.extend(encode_sleb128(-42));
        bytes.push(0);
        bytes.push(0);
        bytes.push(0);

        let table = AbbrevTable::parse(&bytes, 0).unwrap();
        let entry = table.get(1).unwrap();
        assert_eq!(entry.attributes[0].implicit_const, Some(-42));
    }
}
