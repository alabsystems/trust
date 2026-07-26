// trust-binary-parse: DWARF type extraction and resolution
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use crate::dwarf::constants::{
    DW_AT_BYTE_SIZE, DW_AT_CONST_VALUE, DW_AT_COUNT, DW_AT_DATA_MEMBER_LOCATION, DW_AT_ENCODING,
    DW_AT_LOWER_BOUND, DW_AT_NAME, DW_AT_TYPE, DW_AT_UPPER_BOUND, DW_TAG_ARRAY_TYPE,
    DW_TAG_BASE_TYPE, DW_TAG_CONST_TYPE, DW_TAG_ENUMERATION_TYPE, DW_TAG_ENUMERATOR,
    DW_TAG_FORMAL_PARAMETER, DW_TAG_MEMBER, DW_TAG_POINTER_TYPE, DW_TAG_STRUCTURE_TYPE,
    DW_TAG_SUBRANGE_TYPE, DW_TAG_SUBROUTINE_TYPE, DW_TAG_TYPEDEF, DW_TAG_UNION_TYPE,
    DW_TAG_UNSPECIFIED_PARAMETERS, DW_TAG_UNSPECIFIED_TYPE, DW_TAG_VOLATILE_TYPE,
};
use crate::dwarf::info::{CompilationUnit, Die};
use crate::error::DwarfError;

type DieIndex<'unit, 'data> = FxHashMap<usize, &'unit Die<'data>>;

/// A recovered high-level DWARF type.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DwarfType {
    Base { name: Option<String>, byte_size: u64, encoding: u64 },
    Pointer { pointee: Option<Box<DwarfType>> },
    Struct { name: Option<String>, byte_size: Option<u64>, members: Vec<StructMember> },
    Array { element_type: Option<Box<DwarfType>>, bounds: Option<ArrayBounds> },
    Subroutine { return_type: Option<Box<DwarfType>>, parameters: Vec<DwarfType> },
    Typedef { name: String, underlying: Option<Box<DwarfType>> },
    Const { underlying: Option<Box<DwarfType>> },
    Volatile { underlying: Option<Box<DwarfType>> },
    Enum { name: Option<String>, byte_size: Option<u64>, enumerators: Vec<Enumerator> },
    Union { name: Option<String>, byte_size: Option<u64>, members: Vec<StructMember> },
    Void,
}

/// A recovered struct or union member.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructMember {
    pub(crate) name: Option<String>,
    pub(crate) type_: Option<DwarfType>,
    pub(crate) offset: Option<u64>,
}

/// Bounds information for an array type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArrayBounds {
    pub(crate) lower: i64,
    pub(crate) upper: Option<i64>,
    pub(crate) count: Option<u64>,
}

/// A recovered enum constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Enumerator {
    pub(crate) name: String,
    pub(crate) value: i64,
}

/// Extract all resolvable types from the parsed compilation units.
pub fn extract_types(units: &[CompilationUnit<'_>]) -> Vec<(usize, DwarfType)> {
    let index = build_die_index(units);
    let mut offsets = Vec::new();
    for unit in units {
        collect_type_offsets(&unit.dies, &mut offsets);
    }

    offsets
        .into_iter()
        .filter_map(|offset| {
            let mut visiting = FxHashSet::default();
            resolve_type_with_index(&index, offset, &mut visiting).ok().map(|type_| (offset, type_))
        })
        .collect()
}

/// Resolve a single type DIE by its absolute `.debug_info` offset.
pub fn resolve_type(
    units: &[CompilationUnit<'_>],
    die_offset: usize,
) -> Result<DwarfType, DwarfError> {
    let index = build_die_index(units);
    let mut visiting = FxHashSet::default();
    resolve_type_with_index(&index, die_offset, &mut visiting)
}

fn build_die_index<'unit, 'data>(units: &'unit [CompilationUnit<'data>]) -> DieIndex<'unit, 'data> {
    let mut index = FxHashMap::default();
    for unit in units {
        index_dies(&unit.dies, &mut index);
    }
    index
}

fn index_dies<'unit, 'data>(dies: &'unit [Die<'data>], index: &mut DieIndex<'unit, 'data>) {
    for die in dies {
        index.insert(die.offset, die);
        index_dies(&die.children, index);
    }
}

fn collect_type_offsets(dies: &[Die<'_>], offsets: &mut Vec<usize>) {
    for die in dies {
        if is_type_tag(die.tag) {
            offsets.push(die.offset);
        }
        collect_type_offsets(&die.children, offsets);
    }
}

fn is_type_tag(tag: u64) -> bool {
    matches!(
        tag,
        DW_TAG_BASE_TYPE
            | DW_TAG_POINTER_TYPE
            | DW_TAG_STRUCTURE_TYPE
            | DW_TAG_ARRAY_TYPE
            | DW_TAG_SUBROUTINE_TYPE
            | DW_TAG_TYPEDEF
            | DW_TAG_CONST_TYPE
            | DW_TAG_VOLATILE_TYPE
            | DW_TAG_ENUMERATION_TYPE
            | DW_TAG_UNION_TYPE
            | DW_TAG_UNSPECIFIED_TYPE
    )
}

fn resolve_type_with_index(
    index: &DieIndex<'_, '_>,
    die_offset: usize,
    visiting: &mut FxHashSet<usize>,
) -> Result<DwarfType, DwarfError> {
    if !visiting.insert(die_offset) {
        return Ok(DwarfType::Void);
    }

    let die =
        index.get(&die_offset).copied().ok_or(DwarfError::TypeResolutionFailed(die_offset))?;
    let resolved = match die.tag {
        DW_TAG_BASE_TYPE => DwarfType::Base {
            name: attr_name(die),
            byte_size: attr_u64(die, DW_AT_BYTE_SIZE).unwrap_or(0),
            encoding: attr_u64(die, DW_AT_ENCODING).unwrap_or(0),
        },
        DW_TAG_POINTER_TYPE => {
            DwarfType::Pointer { pointee: resolve_boxed_type(die, index, visiting) }
        }
        DW_TAG_STRUCTURE_TYPE => DwarfType::Struct {
            name: attr_name(die),
            byte_size: attr_u64(die, DW_AT_BYTE_SIZE),
            members: resolve_members(&die.children, index, visiting),
        },
        DW_TAG_ARRAY_TYPE => DwarfType::Array {
            element_type: resolve_boxed_type(die, index, visiting),
            bounds: resolve_array_bounds(&die.children),
        },
        DW_TAG_SUBROUTINE_TYPE => DwarfType::Subroutine {
            return_type: resolve_boxed_type(die, index, visiting),
            parameters: resolve_subroutine_parameters(&die.children, index, visiting),
        },
        DW_TAG_TYPEDEF => DwarfType::Typedef {
            name: attr_name(die).unwrap_or_default(),
            underlying: resolve_boxed_type(die, index, visiting),
        },
        DW_TAG_CONST_TYPE => {
            DwarfType::Const { underlying: resolve_boxed_type(die, index, visiting) }
        }
        DW_TAG_VOLATILE_TYPE => {
            DwarfType::Volatile { underlying: resolve_boxed_type(die, index, visiting) }
        }
        DW_TAG_ENUMERATION_TYPE => DwarfType::Enum {
            name: attr_name(die),
            byte_size: attr_u64(die, DW_AT_BYTE_SIZE),
            enumerators: resolve_enumerators(&die.children),
        },
        DW_TAG_UNION_TYPE => DwarfType::Union {
            name: attr_name(die),
            byte_size: attr_u64(die, DW_AT_BYTE_SIZE),
            members: resolve_members(&die.children, index, visiting),
        },
        DW_TAG_UNSPECIFIED_TYPE => DwarfType::Void,
        _ => return Err(DwarfError::UnknownTag(die.tag)),
    };

    visiting.remove(&die_offset);
    Ok(resolved)
}

fn resolve_boxed_type(
    die: &Die<'_>,
    index: &DieIndex<'_, '_>,
    visiting: &mut FxHashSet<usize>,
) -> Option<Box<DwarfType>> {
    let target = die.attribute(DW_AT_TYPE)?.value.as_reference()?;
    let offset = usize::try_from(target).ok()?;
    resolve_type_with_index(index, offset, visiting).ok().map(Box::new)
}

fn resolve_members(
    children: &[Die<'_>],
    index: &DieIndex<'_, '_>,
    visiting: &mut FxHashSet<usize>,
) -> Vec<StructMember> {
    children
        .iter()
        .filter(|child| child.tag == DW_TAG_MEMBER)
        .map(|child| StructMember {
            name: attr_name(child),
            type_: resolve_boxed_type(child, index, visiting).map(|type_| *type_),
            offset: attr_u64(child, DW_AT_DATA_MEMBER_LOCATION),
        })
        .collect()
}

fn resolve_array_bounds(children: &[Die<'_>]) -> Option<ArrayBounds> {
    let subrange = children.iter().find(|child| child.tag == DW_TAG_SUBRANGE_TYPE)?;
    Some(ArrayBounds {
        lower: attr_i64(subrange, DW_AT_LOWER_BOUND).unwrap_or(0),
        upper: attr_i64(subrange, DW_AT_UPPER_BOUND),
        count: attr_u64(subrange, DW_AT_COUNT),
    })
}

fn resolve_subroutine_parameters(
    children: &[Die<'_>],
    index: &DieIndex<'_, '_>,
    visiting: &mut FxHashSet<usize>,
) -> Vec<DwarfType> {
    children
        .iter()
        .filter_map(|child| match child.tag {
            DW_TAG_FORMAL_PARAMETER => {
                resolve_boxed_type(child, index, visiting).map(|type_| *type_)
            }
            DW_TAG_UNSPECIFIED_PARAMETERS => Some(DwarfType::Void),
            _ => None,
        })
        .collect()
}

fn resolve_enumerators(children: &[Die<'_>]) -> Vec<Enumerator> {
    children
        .iter()
        .filter(|child| child.tag == DW_TAG_ENUMERATOR)
        .map(|child| Enumerator {
            name: attr_name(child).unwrap_or_default(),
            value: attr_i64(child, DW_AT_CONST_VALUE).unwrap_or(0),
        })
        .collect()
}

fn attr_name(die: &Die<'_>) -> Option<String> {
    die.attribute(DW_AT_NAME).and_then(|attribute| attribute.value.as_str()).map(ToOwned::to_owned)
}

fn attr_u64(die: &Die<'_>, attribute_name: u64) -> Option<u64> {
    die.attribute(attribute_name).and_then(|attribute| attribute.value.as_u64())
}

fn attr_i64(die: &Die<'_>, attribute_name: u64) -> Option<i64> {
    die.attribute(attribute_name).and_then(|attribute| attribute.value.as_i64())
}

#[cfg(test)]
mod tests {
    use super::{ArrayBounds, DwarfType, StructMember, extract_types, is_type_tag, resolve_type};
    use crate::dwarf::constants::{
        DW_AT_BYTE_SIZE, DW_AT_COUNT, DW_AT_DATA_MEMBER_LOCATION, DW_AT_ENCODING, DW_AT_NAME,
        DW_AT_TYPE, DW_ATE_SIGNED, DW_TAG_ARRAY_TYPE, DW_TAG_BASE_TYPE, DW_TAG_MEMBER,
        DW_TAG_POINTER_TYPE, DW_TAG_STRUCTURE_TYPE, DW_TAG_SUBRANGE_TYPE,
    };
    use crate::dwarf::info::{Attribute, AttributeValue, CompilationUnit, Die};

    #[test]
    fn test_types_extract_and_resolve_handcrafted_dies_expected() {
        let base = Die {
            offset: 10,
            tag: DW_TAG_BASE_TYPE,
            has_children: false,
            attributes: vec![
                Attribute { name: DW_AT_NAME, value: AttributeValue::String("int") },
                Attribute { name: DW_AT_BYTE_SIZE, value: AttributeValue::Data1(4) },
                Attribute {
                    name: DW_AT_ENCODING,
                    value: AttributeValue::Data1(DW_ATE_SIGNED as u8),
                },
            ],
            children: Vec::new(),
        };

        let pointer = Die {
            offset: 20,
            tag: DW_TAG_POINTER_TYPE,
            has_children: false,
            attributes: vec![Attribute { name: DW_AT_TYPE, value: AttributeValue::Reference(10) }],
            children: Vec::new(),
        };

        let struct_type = Die {
            offset: 30,
            tag: DW_TAG_STRUCTURE_TYPE,
            has_children: true,
            attributes: vec![
                Attribute { name: DW_AT_NAME, value: AttributeValue::String("Point") },
                Attribute { name: DW_AT_BYTE_SIZE, value: AttributeValue::Data1(8) },
            ],
            children: vec![
                Die {
                    offset: 31,
                    tag: DW_TAG_MEMBER,
                    has_children: false,
                    attributes: vec![
                        Attribute { name: DW_AT_NAME, value: AttributeValue::String("x") },
                        Attribute { name: DW_AT_TYPE, value: AttributeValue::Reference(10) },
                        Attribute {
                            name: DW_AT_DATA_MEMBER_LOCATION,
                            value: AttributeValue::Udata(0),
                        },
                    ],
                    children: Vec::new(),
                },
                Die {
                    offset: 32,
                    tag: DW_TAG_MEMBER,
                    has_children: false,
                    attributes: vec![
                        Attribute { name: DW_AT_NAME, value: AttributeValue::String("y") },
                        Attribute { name: DW_AT_TYPE, value: AttributeValue::Reference(10) },
                        Attribute {
                            name: DW_AT_DATA_MEMBER_LOCATION,
                            value: AttributeValue::Udata(4),
                        },
                    ],
                    children: Vec::new(),
                },
            ],
        };

        let array = Die {
            offset: 40,
            tag: DW_TAG_ARRAY_TYPE,
            has_children: true,
            attributes: vec![Attribute { name: DW_AT_TYPE, value: AttributeValue::Reference(10) }],
            children: vec![Die {
                offset: 41,
                tag: DW_TAG_SUBRANGE_TYPE,
                has_children: false,
                attributes: vec![Attribute { name: DW_AT_COUNT, value: AttributeValue::Udata(10) }],
                children: Vec::new(),
            }],
        };

        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![base.clone(), pointer, struct_type, array],
        };

        let extracted = extract_types(std::slice::from_ref(&unit));
        assert_eq!(extracted.len(), 4);

        let pointer_type = resolve_type(std::slice::from_ref(&unit), 20).unwrap();
        assert_eq!(
            pointer_type,
            DwarfType::Pointer {
                pointee: Some(Box::new(DwarfType::Base {
                    name: Some("int".to_string()),
                    byte_size: 4,
                    encoding: DW_ATE_SIGNED,
                }))
            }
        );

        let struct_type = resolve_type(std::slice::from_ref(&unit), 30).unwrap();
        assert_eq!(
            struct_type,
            DwarfType::Struct {
                name: Some("Point".to_string()),
                byte_size: Some(8),
                members: vec![
                    StructMember {
                        name: Some("x".to_string()),
                        type_: Some(DwarfType::Base {
                            name: Some("int".to_string()),
                            byte_size: 4,
                            encoding: DW_ATE_SIGNED,
                        }),
                        offset: Some(0),
                    },
                    StructMember {
                        name: Some("y".to_string()),
                        type_: Some(DwarfType::Base {
                            name: Some("int".to_string()),
                            byte_size: 4,
                            encoding: DW_ATE_SIGNED,
                        }),
                        offset: Some(4),
                    },
                ],
            }
        );

        let array_type = resolve_type(&[unit], 40).unwrap();
        assert_eq!(
            array_type,
            DwarfType::Array {
                element_type: Some(Box::new(DwarfType::Base {
                    name: Some("int".to_string()),
                    byte_size: 4,
                    encoding: DW_ATE_SIGNED,
                })),
                bounds: Some(ArrayBounds { lower: 0, upper: None, count: Some(10) }),
            }
        );
    }

    #[test]
    fn test_types_resolve_nonexistent_offset_returns_error() {
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: Vec::new(),
        };
        let err = resolve_type(&[unit], 0x999);
        assert!(err.is_err());
    }

    #[test]
    fn test_types_extract_empty_units_returns_empty() {
        let result = extract_types(&[]);
        assert!(result.is_empty());
    }

    #[test]
    fn test_types_resolve_pointer_to_void_no_type_attribute() {
        use crate::dwarf::constants::DW_TAG_POINTER_TYPE;
        let pointer = Die {
            offset: 10,
            tag: DW_TAG_POINTER_TYPE,
            has_children: false,
            attributes: vec![], // No DW_AT_TYPE => void pointer
            children: Vec::new(),
        };
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![pointer],
        };
        let result = resolve_type(&[unit], 10).unwrap();
        assert_eq!(result, DwarfType::Pointer { pointee: None });
    }

    #[test]
    fn test_types_resolve_typedef() {
        use crate::dwarf::constants::{DW_AT_NAME, DW_AT_TYPE, DW_TAG_TYPEDEF};
        let base = Die {
            offset: 10,
            tag: DW_TAG_BASE_TYPE,
            has_children: false,
            attributes: vec![
                Attribute { name: DW_AT_NAME, value: AttributeValue::String("int") },
                Attribute { name: DW_AT_BYTE_SIZE, value: AttributeValue::Data1(4) },
                Attribute {
                    name: DW_AT_ENCODING,
                    value: AttributeValue::Data1(DW_ATE_SIGNED as u8),
                },
            ],
            children: Vec::new(),
        };
        let typedef = Die {
            offset: 20,
            tag: DW_TAG_TYPEDEF,
            has_children: false,
            attributes: vec![
                Attribute { name: DW_AT_NAME, value: AttributeValue::String("myint") },
                Attribute { name: DW_AT_TYPE, value: AttributeValue::Reference(10) },
            ],
            children: Vec::new(),
        };
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![base, typedef],
        };
        let result = resolve_type(&[unit], 20).unwrap();
        assert_eq!(
            result,
            DwarfType::Typedef {
                name: "myint".to_string(),
                underlying: Some(Box::new(DwarfType::Base {
                    name: Some("int".to_string()),
                    byte_size: 4,
                    encoding: DW_ATE_SIGNED,
                })),
            }
        );
    }

    #[test]
    fn test_types_resolve_const_type() {
        use crate::dwarf::constants::{DW_AT_TYPE, DW_TAG_CONST_TYPE};
        let base = Die {
            offset: 10,
            tag: DW_TAG_BASE_TYPE,
            has_children: false,
            attributes: vec![
                Attribute { name: DW_AT_NAME, value: AttributeValue::String("char") },
                Attribute { name: DW_AT_BYTE_SIZE, value: AttributeValue::Data1(1) },
                Attribute { name: DW_AT_ENCODING, value: AttributeValue::Data1(0x08) }, // DW_ATE_UNSIGNED_CHAR
            ],
            children: Vec::new(),
        };
        let const_type = Die {
            offset: 20,
            tag: DW_TAG_CONST_TYPE,
            has_children: false,
            attributes: vec![Attribute { name: DW_AT_TYPE, value: AttributeValue::Reference(10) }],
            children: Vec::new(),
        };
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![base, const_type],
        };
        let result = resolve_type(&[unit], 20).unwrap();
        match result {
            DwarfType::Const { underlying } => assert!(underlying.is_some()),
            other => panic!("expected Const, got: {other:?}"),
        }
    }

    #[test]
    fn test_types_resolve_volatile_type() {
        use crate::dwarf::constants::{DW_AT_TYPE, DW_TAG_VOLATILE_TYPE};
        let base = Die {
            offset: 10,
            tag: DW_TAG_BASE_TYPE,
            has_children: false,
            attributes: vec![
                Attribute { name: DW_AT_BYTE_SIZE, value: AttributeValue::Data1(4) },
                Attribute {
                    name: DW_AT_ENCODING,
                    value: AttributeValue::Data1(DW_ATE_SIGNED as u8),
                },
            ],
            children: Vec::new(),
        };
        let volatile = Die {
            offset: 20,
            tag: DW_TAG_VOLATILE_TYPE,
            has_children: false,
            attributes: vec![Attribute { name: DW_AT_TYPE, value: AttributeValue::Reference(10) }],
            children: Vec::new(),
        };
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![base, volatile],
        };
        let result = resolve_type(&[unit], 20).unwrap();
        match result {
            DwarfType::Volatile { underlying } => assert!(underlying.is_some()),
            other => panic!("expected Volatile, got: {other:?}"),
        }
    }

    #[test]
    fn test_types_resolve_enum_type() {
        use crate::dwarf::constants::{
            DW_AT_BYTE_SIZE, DW_AT_CONST_VALUE, DW_AT_NAME, DW_TAG_ENUMERATION_TYPE,
            DW_TAG_ENUMERATOR,
        };
        let enum_type = Die {
            offset: 10,
            tag: DW_TAG_ENUMERATION_TYPE,
            has_children: true,
            attributes: vec![
                Attribute { name: DW_AT_NAME, value: AttributeValue::String("Color") },
                Attribute { name: DW_AT_BYTE_SIZE, value: AttributeValue::Data1(4) },
            ],
            children: vec![
                Die {
                    offset: 20,
                    tag: DW_TAG_ENUMERATOR,
                    has_children: false,
                    attributes: vec![
                        Attribute { name: DW_AT_NAME, value: AttributeValue::String("Red") },
                        Attribute { name: DW_AT_CONST_VALUE, value: AttributeValue::Sdata(0) },
                    ],
                    children: Vec::new(),
                },
                Die {
                    offset: 30,
                    tag: DW_TAG_ENUMERATOR,
                    has_children: false,
                    attributes: vec![
                        Attribute { name: DW_AT_NAME, value: AttributeValue::String("Blue") },
                        Attribute { name: DW_AT_CONST_VALUE, value: AttributeValue::Sdata(1) },
                    ],
                    children: Vec::new(),
                },
            ],
        };
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![enum_type],
        };
        let result = resolve_type(&[unit], 10).unwrap();
        match result {
            DwarfType::Enum { name, byte_size, enumerators } => {
                assert_eq!(name, Some("Color".to_string()));
                assert_eq!(byte_size, Some(4));
                assert_eq!(enumerators.len(), 2);
                assert_eq!(enumerators[0].name, "Red");
                assert_eq!(enumerators[0].value, 0);
                assert_eq!(enumerators[1].name, "Blue");
                assert_eq!(enumerators[1].value, 1);
            }
            other => panic!("expected Enum, got: {other:?}"),
        }
    }

    #[test]
    fn test_types_resolve_union_type() {
        use crate::dwarf::constants::{DW_AT_BYTE_SIZE, DW_AT_NAME, DW_TAG_UNION_TYPE};
        let union_type = Die {
            offset: 10,
            tag: DW_TAG_UNION_TYPE,
            has_children: true,
            attributes: vec![
                Attribute { name: DW_AT_NAME, value: AttributeValue::String("Value") },
                Attribute { name: DW_AT_BYTE_SIZE, value: AttributeValue::Data1(8) },
            ],
            children: vec![],
        };
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![union_type],
        };
        let result = resolve_type(&[unit], 10).unwrap();
        match result {
            DwarfType::Union { name, byte_size, members } => {
                assert_eq!(name, Some("Value".to_string()));
                assert_eq!(byte_size, Some(8));
                assert!(members.is_empty());
            }
            other => panic!("expected Union, got: {other:?}"),
        }
    }

    #[test]
    fn test_types_resolve_unspecified_type() {
        use crate::dwarf::constants::DW_TAG_UNSPECIFIED_TYPE;
        let die = Die {
            offset: 10,
            tag: DW_TAG_UNSPECIFIED_TYPE,
            has_children: false,
            attributes: vec![],
            children: Vec::new(),
        };
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![die],
        };
        let result = resolve_type(&[unit], 10).unwrap();
        assert_eq!(result, DwarfType::Void);
    }

    #[test]
    fn test_types_resolve_unknown_tag_returns_error() {
        let die = Die {
            offset: 10,
            tag: 0xFF00, // not a type tag
            has_children: false,
            attributes: vec![],
            children: Vec::new(),
        };
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![die],
        };
        let err = resolve_type(&[unit], 10);
        assert!(err.is_err());
    }

    #[test]
    fn test_types_self_referencing_type_returns_void() {
        // A pointer that refers to itself should break the cycle
        use crate::dwarf::constants::{DW_AT_TYPE, DW_TAG_POINTER_TYPE};
        let self_ref = Die {
            offset: 10,
            tag: DW_TAG_POINTER_TYPE,
            has_children: false,
            attributes: vec![Attribute { name: DW_AT_TYPE, value: AttributeValue::Reference(10) }],
            children: Vec::new(),
        };
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![self_ref],
        };
        // Should not infinite loop; cycle detection returns Void
        let result = resolve_type(&[unit], 10).unwrap();
        assert_eq!(result, DwarfType::Pointer { pointee: Some(Box::new(DwarfType::Void)) });
    }

    #[test]
    fn test_types_subroutine_type() {
        use crate::dwarf::constants::{
            DW_AT_TYPE, DW_TAG_FORMAL_PARAMETER, DW_TAG_SUBROUTINE_TYPE,
        };
        let base = Die {
            offset: 10,
            tag: DW_TAG_BASE_TYPE,
            has_children: false,
            attributes: vec![
                Attribute { name: DW_AT_NAME, value: AttributeValue::String("int") },
                Attribute { name: DW_AT_BYTE_SIZE, value: AttributeValue::Data1(4) },
                Attribute {
                    name: DW_AT_ENCODING,
                    value: AttributeValue::Data1(DW_ATE_SIGNED as u8),
                },
            ],
            children: Vec::new(),
        };
        let subroutine = Die {
            offset: 20,
            tag: DW_TAG_SUBROUTINE_TYPE,
            has_children: true,
            attributes: vec![
                Attribute { name: DW_AT_TYPE, value: AttributeValue::Reference(10) }, // return type
            ],
            children: vec![Die {
                offset: 30,
                tag: DW_TAG_FORMAL_PARAMETER,
                has_children: false,
                attributes: vec![Attribute {
                    name: DW_AT_TYPE,
                    value: AttributeValue::Reference(10),
                }],
                children: Vec::new(),
            }],
        };
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![base, subroutine],
        };
        let result = resolve_type(&[unit], 20).unwrap();
        match result {
            DwarfType::Subroutine { return_type, parameters } => {
                assert!(return_type.is_some());
                assert_eq!(parameters.len(), 1);
            }
            other => panic!("expected Subroutine, got: {other:?}"),
        }
    }

    #[test]
    fn test_types_base_type_without_name() {
        let base = Die {
            offset: 10,
            tag: DW_TAG_BASE_TYPE,
            has_children: false,
            attributes: vec![
                Attribute { name: DW_AT_BYTE_SIZE, value: AttributeValue::Data1(1) },
                Attribute { name: DW_AT_ENCODING, value: AttributeValue::Data1(0x02) }, // DW_ATE_BOOLEAN
            ],
            children: Vec::new(),
        };
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![base],
        };
        let result = resolve_type(&[unit], 10).unwrap();
        assert_eq!(result, DwarfType::Base { name: None, byte_size: 1, encoding: 0x02 });
    }

    #[test]
    fn test_is_type_tag_returns_true_for_all_type_tags() {
        use crate::dwarf::constants::*;
        let type_tags = [
            DW_TAG_BASE_TYPE,
            DW_TAG_POINTER_TYPE,
            DW_TAG_STRUCTURE_TYPE,
            DW_TAG_ARRAY_TYPE,
            DW_TAG_SUBROUTINE_TYPE,
            DW_TAG_TYPEDEF,
            DW_TAG_CONST_TYPE,
            DW_TAG_VOLATILE_TYPE,
            DW_TAG_ENUMERATION_TYPE,
            DW_TAG_UNION_TYPE,
            DW_TAG_UNSPECIFIED_TYPE,
        ];
        for tag in type_tags {
            assert!(is_type_tag(tag), "expected true for tag 0x{tag:02x}");
        }
    }

    #[test]
    fn test_is_type_tag_returns_false_for_non_type_tags() {
        use crate::dwarf::constants::*;
        let non_type_tags = [
            DW_TAG_COMPILE_UNIT,
            DW_TAG_SUBPROGRAM,
            DW_TAG_VARIABLE,
            DW_TAG_FORMAL_PARAMETER,
            DW_TAG_LEXICAL_BLOCK,
            DW_TAG_NAMESPACE,
        ];
        for tag in non_type_tags {
            assert!(!is_type_tag(tag), "expected false for tag 0x{tag:02x}");
        }
    }
}
