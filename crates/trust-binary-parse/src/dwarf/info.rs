// trust-binary-parse: DWARF compilation units and DIE trees
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use crate::cursor::Cursor;
use crate::dwarf::abbrev::{AbbrevEntry, AbbrevTable};
use crate::dwarf::constants::{
    DW_FORM_ADDR, DW_FORM_ADDRX, DW_FORM_BLOCK, DW_FORM_BLOCK1, DW_FORM_BLOCK2, DW_FORM_BLOCK4,
    DW_FORM_DATA1, DW_FORM_DATA2, DW_FORM_DATA4, DW_FORM_DATA8, DW_FORM_EXPRLOC, DW_FORM_FLAG,
    DW_FORM_FLAG_PRESENT, DW_FORM_IMPLICIT_CONST, DW_FORM_INDIRECT, DW_FORM_LINE_STRP,
    DW_FORM_REF_ADDR, DW_FORM_REF_UDATA, DW_FORM_REF1, DW_FORM_REF2, DW_FORM_REF4, DW_FORM_REF8,
    DW_FORM_SDATA, DW_FORM_SEC_OFFSET, DW_FORM_STRING, DW_FORM_STRP, DW_FORM_STRX1, DW_FORM_STRX2,
    DW_FORM_UDATA, DW_UT_COMPILE, DW_UT_PARTIAL, DW_UT_SKELETON, DW_UT_SPLIT_COMPILE,
    DW_UT_SPLIT_TYPE, DW_UT_TYPE,
};
use crate::dwarf::str::StringTable;
use crate::error::DwarfError;

/// A DWARF compilation unit and its DIE tree.
#[derive(Debug, Clone, PartialEq)]
pub struct CompilationUnit<'a> {
    pub(crate) unit_length: u64,
    pub(crate) version: u16,
    pub(crate) abbrev_offset: u64,
    pub(crate) address_size: u8,
    pub(crate) header_size: usize,
    pub(crate) dies: Vec<Die<'a>>,
}

/// A debug information entry (DIE).
#[derive(Debug, Clone, PartialEq)]
pub struct Die<'a> {
    pub(crate) offset: usize,
    pub(crate) tag: u64,
    pub(crate) has_children: bool,
    pub(crate) attributes: Vec<Attribute<'a>>,
    pub(crate) children: Vec<Die<'a>>,
}

/// A decoded DIE attribute.
#[derive(Debug, Clone, PartialEq)]
pub struct Attribute<'a> {
    pub(crate) name: u64,
    pub(crate) value: AttributeValue<'a>,
}

/// A decoded DWARF attribute value.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum AttributeValue<'a> {
    Address(u64),
    Data1(u8),
    Data2(u16),
    Data4(u32),
    Data8(u64),
    String(&'a str),
    StringOffset(u64),
    Flag(bool),
    SecOffset(u64),
    Sdata(i64),
    Udata(u64),
    Block(&'a [u8]),
    Reference(u64),
    ExprLoc(&'a [u8]),
}

struct UnitParseContext<'a, 'b> {
    strings: StringTable<'a>,
    abbrev_table: &'b AbbrevTable,
    unit_offset: usize,
    unit_end: usize,
    version: u16,
    address_size: u8,
    offset_size: usize,
}

/// Parse all compilation units from `.debug_info`.
pub fn parse_compilation_units<'a>(
    debug_info: &'a [u8],
    debug_abbrev: &'a [u8],
    debug_str: &'a [u8],
) -> Result<Vec<CompilationUnit<'a>>, DwarfError> {
    let mut cursor = Cursor::new(debug_info);
    let strings = StringTable::new(debug_str);
    let mut abbrev_cache = FxHashMap::default();
    let mut units = Vec::new();

    while cursor.position() < cursor.len() {
        let unit_offset = cursor.position();
        let (unit_length, offset_size, unit_end) = read_initial_length(&mut cursor)?;
        let version = cursor.read_u16_le()?;
        if !(2..=5).contains(&version) {
            return Err(DwarfError::UnsupportedDwarfVersion(version));
        }

        let (abbrev_offset, address_size) = if version == 5 {
            let unit_type = cursor.read_u8()?;
            let address_size = cursor.read_u8()?;
            let abbrev_offset = read_offset(&mut cursor, offset_size)?;

            match unit_type {
                DW_UT_COMPILE | DW_UT_PARTIAL | DW_UT_SKELETON | DW_UT_SPLIT_COMPILE => {}
                DW_UT_TYPE | DW_UT_SPLIT_TYPE => {
                    let _type_signature = cursor.read_u64_le()?;
                    let _type_offset = read_offset(&mut cursor, offset_size)?;
                }
                _ => return Err(DwarfError::InvalidUnit),
            }

            (abbrev_offset, address_size)
        } else {
            let abbrev_offset = read_offset(&mut cursor, offset_size)?;
            let address_size = cursor.read_u8()?;
            (abbrev_offset, address_size)
        };

        if usize::from(address_size) > 8 || address_size == 0 {
            return Err(DwarfError::InvalidUnit);
        }

        if let std::collections::hash_map::Entry::Vacant(e) = abbrev_cache.entry(abbrev_offset) {
            let table = AbbrevTable::parse(
                debug_abbrev,
                usize::try_from(abbrev_offset).map_err(|_| DwarfError::InvalidAbbreviation)?,
            )?;
            e.insert(table);
        }
        let abbrev_table =
            abbrev_cache.get(&abbrev_offset).ok_or(DwarfError::InvalidAbbreviation)?;

        let header_size = cursor.position() - unit_offset;
        let context = UnitParseContext {
            strings,
            abbrev_table,
            unit_offset,
            unit_end,
            version,
            address_size,
            offset_size,
        };
        let dies = parse_die_list(&mut cursor, &context)?;

        if cursor.position() < unit_end {
            if !debug_info[cursor.position()..unit_end].iter().all(|byte| *byte == 0) {
                return Err(DwarfError::InvalidUnit);
            }
            cursor.set_position(unit_end)?;
        }

        units.push(CompilationUnit {
            unit_length,
            version,
            abbrev_offset,
            address_size,
            header_size,
            dies,
        });
    }

    Ok(units)
}

fn parse_die_list<'a>(
    cursor: &mut Cursor<'a>,
    context: &UnitParseContext<'a, '_>,
) -> Result<Vec<Die<'a>>, DwarfError> {
    let mut dies = Vec::new();

    while cursor.position() < context.unit_end {
        let die_offset = cursor.position();
        let code = cursor.read_uleb128()?;
        if code == 0 {
            break;
        }

        let entry = context.abbrev_table.get(code).ok_or(DwarfError::InvalidAbbreviation)?;
        let attributes = parse_attributes(cursor, context, entry)?;
        let children =
            if entry.has_children { parse_die_list(cursor, context)? } else { Vec::new() };

        dies.push(Die {
            offset: die_offset,
            tag: entry.tag,
            has_children: entry.has_children,
            attributes,
            children,
        });
    }

    Ok(dies)
}

fn parse_attributes<'a>(
    cursor: &mut Cursor<'a>,
    context: &UnitParseContext<'a, '_>,
    entry: &AbbrevEntry,
) -> Result<Vec<Attribute<'a>>, DwarfError> {
    entry
        .attributes
        .iter()
        .map(|attribute| {
            let value =
                parse_form_value(cursor, context, attribute.form, attribute.implicit_const)?;
            Ok(Attribute { name: attribute.name, value })
        })
        .collect()
}

fn parse_form_value<'a>(
    cursor: &mut Cursor<'a>,
    context: &UnitParseContext<'a, '_>,
    form: u64,
    implicit_const: Option<i64>,
) -> Result<AttributeValue<'a>, DwarfError> {
    let value = match form {
        DW_FORM_ADDR => {
            AttributeValue::Address(cursor.read_uint(usize::from(context.address_size))?)
        }
        DW_FORM_DATA1 => AttributeValue::Data1(cursor.read_u8()?),
        DW_FORM_DATA2 => AttributeValue::Data2(cursor.read_u16_le()?),
        DW_FORM_DATA4 => AttributeValue::Data4(cursor.read_u32_le()?),
        DW_FORM_DATA8 => AttributeValue::Data8(cursor.read_u64_le()?),
        DW_FORM_STRING => AttributeValue::String(cursor.read_null_terminated_string()?),
        DW_FORM_STRP => {
            let offset = usize::try_from(read_offset(cursor, context.offset_size)?)
                .map_err(|_| DwarfError::InvalidForm)?;
            AttributeValue::String(context.strings.get_string(offset)?)
        }
        DW_FORM_LINE_STRP => {
            AttributeValue::StringOffset(read_offset(cursor, context.offset_size)?)
        }
        DW_FORM_REF1 => {
            AttributeValue::Reference(context.unit_offset as u64 + u64::from(cursor.read_u8()?))
        }
        DW_FORM_REF2 => {
            AttributeValue::Reference(context.unit_offset as u64 + u64::from(cursor.read_u16_le()?))
        }
        DW_FORM_REF4 => {
            AttributeValue::Reference(context.unit_offset as u64 + u64::from(cursor.read_u32_le()?))
        }
        DW_FORM_REF8 => {
            AttributeValue::Reference(context.unit_offset as u64 + cursor.read_u64_le()?)
        }
        DW_FORM_REF_ADDR => {
            let width = if context.version == 2 {
                usize::from(context.address_size)
            } else {
                context.offset_size
            };
            AttributeValue::Reference(read_offset(cursor, width)?)
        }
        DW_FORM_FLAG => AttributeValue::Flag(cursor.read_u8()? != 0),
        DW_FORM_FLAG_PRESENT => AttributeValue::Flag(true),
        DW_FORM_EXPRLOC => {
            let len =
                usize::try_from(cursor.read_uleb128()?).map_err(|_| DwarfError::InvalidForm)?;
            AttributeValue::ExprLoc(cursor.read_bytes(len)?)
        }
        DW_FORM_SEC_OFFSET => AttributeValue::SecOffset(read_offset(cursor, context.offset_size)?),
        DW_FORM_SDATA => AttributeValue::Sdata(cursor.read_sleb128()?),
        DW_FORM_UDATA => AttributeValue::Udata(cursor.read_uleb128()?),
        DW_FORM_BLOCK1 => {
            let len = usize::from(cursor.read_u8()?);
            AttributeValue::Block(cursor.read_bytes(len)?)
        }
        DW_FORM_BLOCK2 => {
            let len = usize::from(cursor.read_u16_le()?);
            AttributeValue::Block(cursor.read_bytes(len)?)
        }
        DW_FORM_BLOCK4 => {
            let len =
                usize::try_from(cursor.read_u32_le()?).map_err(|_| DwarfError::InvalidForm)?;
            AttributeValue::Block(cursor.read_bytes(len)?)
        }
        DW_FORM_BLOCK => {
            let len =
                usize::try_from(cursor.read_uleb128()?).map_err(|_| DwarfError::InvalidForm)?;
            AttributeValue::Block(cursor.read_bytes(len)?)
        }
        DW_FORM_REF_UDATA => {
            AttributeValue::Reference(context.unit_offset as u64 + cursor.read_uleb128()?)
        }
        DW_FORM_INDIRECT => {
            let actual_form = cursor.read_uleb128()?;
            return parse_form_value(cursor, context, actual_form, implicit_const);
        }
        DW_FORM_STRX1 => AttributeValue::StringOffset(u64::from(cursor.read_u8()?)),
        DW_FORM_STRX2 => AttributeValue::StringOffset(u64::from(cursor.read_u16_le()?)),
        DW_FORM_ADDRX => AttributeValue::Udata(cursor.read_uleb128()?),
        DW_FORM_IMPLICIT_CONST => {
            AttributeValue::Sdata(implicit_const.ok_or(DwarfError::InvalidAbbreviation)?)
        }
        _ => return Err(DwarfError::InvalidForm),
    };

    Ok(value)
}

fn read_initial_length(cursor: &mut Cursor<'_>) -> Result<(u64, usize, usize), DwarfError> {
    let initial_length = cursor.read_u32_le()?;
    let (unit_length, offset_size) = if initial_length == u32::MAX {
        (cursor.read_u64_le()?, 8)
    } else {
        (u64::from(initial_length), 4)
    };

    let unit_length = usize::try_from(unit_length).map_err(|_| DwarfError::InvalidUnit)?;
    let unit_end = cursor.position().checked_add(unit_length).ok_or(DwarfError::InvalidUnit)?;
    if unit_end > cursor.len() {
        return Err(DwarfError::UnexpectedEof { offset: cursor.position() });
    }

    Ok((unit_length as u64, offset_size, unit_end))
}

fn read_offset(cursor: &mut Cursor<'_>, width: usize) -> Result<u64, DwarfError> {
    cursor.read_uint(width)
}

impl<'a> Die<'a> {
    pub fn attribute(&self, name: u64) -> Option<&Attribute<'a>> {
        self.attributes.iter().find(|attribute| attribute.name == name)
    }
}

impl<'a> AttributeValue<'a> {
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Self::Address(value)
            | Self::SecOffset(value)
            | Self::StringOffset(value)
            | Self::Udata(value)
            | Self::Reference(value)
            | Self::Data8(value) => Some(*value),
            Self::Data1(value) => Some(u64::from(*value)),
            Self::Data2(value) => Some(u64::from(*value)),
            Self::Data4(value) => Some(u64::from(*value)),
            Self::Sdata(value) if *value >= 0 => u64::try_from(*value).ok(),
            _ => None,
        }
    }

    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Self::Sdata(value) => Some(*value),
            Self::Data1(value) => Some(i64::from(*value)),
            Self::Data2(value) => Some(i64::from(*value)),
            Self::Data4(value) => Some(i64::from(*value)),
            Self::Data8(value) => i64::try_from(*value).ok(),
            Self::Udata(value)
            | Self::Address(value)
            | Self::SecOffset(value)
            | Self::StringOffset(value)
            | Self::Reference(value) => i64::try_from(*value).ok(),
            _ => None,
        }
    }

    pub fn as_str(&self) -> Option<&'a str> {
        match self {
            Self::String(value) => Some(value),
            _ => None,
        }
    }

    pub fn as_reference(&self) -> Option<u64> {
        match self {
            Self::Reference(value) => Some(*value),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{AttributeValue, parse_compilation_units};
    use crate::dwarf::constants::{
        DW_AT_BYTE_SIZE, DW_AT_ENCODING, DW_AT_NAME, DW_AT_STMT_LIST, DW_AT_TYPE, DW_ATE_SIGNED,
        DW_FORM_DATA1, DW_FORM_REF4, DW_FORM_SEC_OFFSET, DW_FORM_STRING, DW_TAG_BASE_TYPE,
        DW_TAG_COMPILE_UNIT, DW_TAG_VARIABLE,
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

    fn patch_u32_le(bytes: &mut [u8], offset: usize, value: u32) {
        bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
    }

    #[test]
    fn test_info_minimal_unit_parses_die_tree_expected() {
        let mut debug_abbrev = Vec::new();
        debug_abbrev.extend(encode_uleb128(1));
        debug_abbrev.extend(encode_uleb128(DW_TAG_COMPILE_UNIT));
        debug_abbrev.push(1);
        debug_abbrev.extend(encode_uleb128(DW_AT_NAME));
        debug_abbrev.extend(encode_uleb128(DW_FORM_STRING));
        debug_abbrev.extend(encode_uleb128(DW_AT_STMT_LIST));
        debug_abbrev.extend(encode_uleb128(DW_FORM_SEC_OFFSET));
        debug_abbrev.push(0);
        debug_abbrev.push(0);

        debug_abbrev.extend(encode_uleb128(2));
        debug_abbrev.extend(encode_uleb128(DW_TAG_BASE_TYPE));
        debug_abbrev.push(0);
        debug_abbrev.extend(encode_uleb128(DW_AT_NAME));
        debug_abbrev.extend(encode_uleb128(DW_FORM_STRING));
        debug_abbrev.extend(encode_uleb128(DW_AT_BYTE_SIZE));
        debug_abbrev.extend(encode_uleb128(DW_FORM_DATA1));
        debug_abbrev.extend(encode_uleb128(DW_AT_ENCODING));
        debug_abbrev.extend(encode_uleb128(DW_FORM_DATA1));
        debug_abbrev.push(0);
        debug_abbrev.push(0);

        debug_abbrev.extend(encode_uleb128(3));
        debug_abbrev.extend(encode_uleb128(DW_TAG_VARIABLE));
        debug_abbrev.push(0);
        debug_abbrev.extend(encode_uleb128(DW_AT_NAME));
        debug_abbrev.extend(encode_uleb128(DW_FORM_STRING));
        debug_abbrev.extend(encode_uleb128(DW_AT_TYPE));
        debug_abbrev.extend(encode_uleb128(DW_FORM_REF4));
        debug_abbrev.push(0);
        debug_abbrev.push(0);
        debug_abbrev.push(0);

        let mut debug_info = vec![0; 4];
        debug_info.extend(4_u16.to_le_bytes());
        debug_info.extend(0_u32.to_le_bytes());
        debug_info.push(8);

        debug_info.extend(encode_uleb128(1));
        debug_info.extend(b"unit\0");
        debug_info.extend(0_u32.to_le_bytes());

        let base_type_offset = debug_info.len();
        debug_info.extend(encode_uleb128(2));
        debug_info.extend(b"int\0");
        debug_info.push(4);
        debug_info.push(DW_ATE_SIGNED as u8);

        debug_info.extend(encode_uleb128(3));
        debug_info.extend(b"value\0");
        debug_info.extend(u32::try_from(base_type_offset).unwrap().to_le_bytes());
        debug_info.push(0);

        let unit_length = (debug_info.len() - 4) as u32;
        patch_u32_le(&mut debug_info, 0, unit_length);

        let units = parse_compilation_units(&debug_info, &debug_abbrev, &[]).unwrap();
        assert_eq!(units.len(), 1);

        let unit = &units[0];
        assert_eq!(unit.version, 4);
        assert_eq!(unit.header_size, 11);
        assert_eq!(unit.dies.len(), 1);

        let root = &unit.dies[0];
        assert_eq!(root.tag, DW_TAG_COMPILE_UNIT);
        assert_eq!(root.children.len(), 2);
        assert_eq!(root.attributes[0].value, AttributeValue::String("unit"));

        let base_type = &root.children[0];
        assert_eq!(base_type.offset, base_type_offset);
        assert_eq!(base_type.attributes[0].value, AttributeValue::String("int"));

        let variable = &root.children[1];
        assert_eq!(variable.tag, DW_TAG_VARIABLE);
        assert_eq!(
            variable.attributes[1].value,
            AttributeValue::Reference(base_type_offset as u64)
        );
    }

    // --- Edge case tests for improved coverage ---

    #[test]
    fn test_attribute_value_as_u64_variants() {
        assert_eq!(AttributeValue::Address(42).as_u64(), Some(42));
        assert_eq!(AttributeValue::Data1(10).as_u64(), Some(10));
        assert_eq!(AttributeValue::Data2(300).as_u64(), Some(300));
        assert_eq!(AttributeValue::Data4(70000).as_u64(), Some(70000));
        assert_eq!(AttributeValue::Data8(u64::MAX).as_u64(), Some(u64::MAX));
        assert_eq!(AttributeValue::SecOffset(100).as_u64(), Some(100));
        assert_eq!(AttributeValue::Udata(999).as_u64(), Some(999));
        assert_eq!(AttributeValue::Reference(50).as_u64(), Some(50));
        assert_eq!(AttributeValue::StringOffset(7).as_u64(), Some(7));
        assert_eq!(AttributeValue::Sdata(5).as_u64(), Some(5));
        assert_eq!(AttributeValue::Sdata(-1).as_u64(), None);
        assert_eq!(AttributeValue::Flag(true).as_u64(), None);
        assert_eq!(AttributeValue::String("hello").as_u64(), None);
    }

    #[test]
    fn test_attribute_value_as_i64_variants() {
        assert_eq!(AttributeValue::Sdata(-42).as_i64(), Some(-42));
        assert_eq!(AttributeValue::Data1(255).as_i64(), Some(255));
        assert_eq!(AttributeValue::Data2(u16::MAX).as_i64(), Some(i64::from(u16::MAX)));
        assert_eq!(AttributeValue::Data4(u32::MAX).as_i64(), Some(i64::from(u32::MAX)));
        assert_eq!(AttributeValue::Address(100).as_i64(), Some(100));
        assert_eq!(AttributeValue::Flag(true).as_i64(), None);
        assert_eq!(AttributeValue::String("x").as_i64(), None);
    }

    #[test]
    fn test_attribute_value_as_str() {
        assert_eq!(AttributeValue::String("hello").as_str(), Some("hello"));
        assert_eq!(AttributeValue::String("").as_str(), Some(""));
        assert_eq!(AttributeValue::Data1(0).as_str(), None);
    }

    #[test]
    fn test_attribute_value_as_reference() {
        assert_eq!(AttributeValue::Reference(42).as_reference(), Some(42));
        assert_eq!(AttributeValue::Address(42).as_reference(), None);
        assert_eq!(AttributeValue::Data8(42).as_reference(), None);
    }

    #[test]
    fn test_die_attribute_lookup() {
        use super::Die;
        let die = Die {
            offset: 0,
            tag: DW_TAG_BASE_TYPE,
            has_children: false,
            attributes: vec![
                super::Attribute { name: DW_AT_NAME, value: AttributeValue::String("int") },
                super::Attribute { name: DW_AT_BYTE_SIZE, value: AttributeValue::Data1(4) },
            ],
            children: Vec::new(),
        };

        assert!(die.attribute(DW_AT_NAME).is_some());
        assert_eq!(die.attribute(DW_AT_NAME).unwrap().value.as_str(), Some("int"));
        assert!(die.attribute(DW_AT_BYTE_SIZE).is_some());
        assert_eq!(die.attribute(DW_AT_BYTE_SIZE).unwrap().value.as_u64(), Some(4));
        assert!(die.attribute(DW_AT_ENCODING).is_none());
    }

    #[test]
    fn test_info_unsupported_dwarf_version_rejected() {
        let mut debug_info = vec![0; 4];
        debug_info.extend(6_u16.to_le_bytes()); // version 6 (unsupported)
        debug_info.extend(0_u32.to_le_bytes());
        debug_info.push(8);
        let unit_length = (debug_info.len() - 4) as u32;
        patch_u32_le(&mut debug_info, 0, unit_length);

        let err = parse_compilation_units(&debug_info, &[], &[]).unwrap_err();
        assert!(err.to_string().contains("unsupported DWARF version"));
    }
}
