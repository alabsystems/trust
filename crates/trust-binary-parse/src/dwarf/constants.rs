// trust-binary-parse: DWARF constants
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub const DW_TAG_ARRAY_TYPE: u64 = 0x01;
pub const DW_TAG_FORMAL_PARAMETER: u64 = 0x05;
#[cfg(test)]
pub const DW_TAG_LEXICAL_BLOCK: u64 = 0x0b;
pub const DW_TAG_MEMBER: u64 = 0x0d;
pub const DW_TAG_POINTER_TYPE: u64 = 0x0f;
#[cfg(test)]
pub const DW_TAG_COMPILE_UNIT: u64 = 0x11;
pub const DW_TAG_STRUCTURE_TYPE: u64 = 0x13;
pub const DW_TAG_SUBROUTINE_TYPE: u64 = 0x15;
pub const DW_TAG_TYPEDEF: u64 = 0x16;
pub const DW_TAG_UNION_TYPE: u64 = 0x17;
pub const DW_TAG_UNSPECIFIED_PARAMETERS: u64 = 0x18;
pub const DW_TAG_SUBRANGE_TYPE: u64 = 0x21;
pub const DW_TAG_BASE_TYPE: u64 = 0x24;
pub const DW_TAG_CONST_TYPE: u64 = 0x26;
pub const DW_TAG_ENUMERATOR: u64 = 0x28;
#[cfg(test)]
pub const DW_TAG_SUBPROGRAM: u64 = 0x2e;
#[cfg(test)]
pub const DW_TAG_VARIABLE: u64 = 0x34;
pub const DW_TAG_VOLATILE_TYPE: u64 = 0x35;
#[cfg(test)]
pub const DW_TAG_NAMESPACE: u64 = 0x39;
pub const DW_TAG_ENUMERATION_TYPE: u64 = 0x04;
pub const DW_TAG_UNSPECIFIED_TYPE: u64 = 0x3b;

pub const DW_FORM_ADDR: u64 = 0x01;
pub const DW_FORM_BLOCK2: u64 = 0x03;
pub const DW_FORM_BLOCK4: u64 = 0x04;
pub const DW_FORM_DATA2: u64 = 0x05;
pub const DW_FORM_DATA4: u64 = 0x06;
pub const DW_FORM_DATA8: u64 = 0x07;
pub const DW_FORM_STRING: u64 = 0x08;
pub const DW_FORM_BLOCK: u64 = 0x09;
pub const DW_FORM_BLOCK1: u64 = 0x0a;
pub const DW_FORM_DATA1: u64 = 0x0b;
pub const DW_FORM_FLAG: u64 = 0x0c;
pub const DW_FORM_SDATA: u64 = 0x0d;
pub const DW_FORM_STRP: u64 = 0x0e;
pub const DW_FORM_UDATA: u64 = 0x0f;
pub const DW_FORM_REF_ADDR: u64 = 0x10;
pub const DW_FORM_REF1: u64 = 0x11;
pub const DW_FORM_REF2: u64 = 0x12;
pub const DW_FORM_REF4: u64 = 0x13;
pub const DW_FORM_REF8: u64 = 0x14;
pub const DW_FORM_REF_UDATA: u64 = 0x15;
pub const DW_FORM_INDIRECT: u64 = 0x16;
pub const DW_FORM_SEC_OFFSET: u64 = 0x17;
pub const DW_FORM_EXPRLOC: u64 = 0x18;
pub const DW_FORM_FLAG_PRESENT: u64 = 0x19;
pub const DW_FORM_ADDRX: u64 = 0x1b;
pub const DW_FORM_LINE_STRP: u64 = 0x1f;
pub const DW_FORM_IMPLICIT_CONST: u64 = 0x21;
pub const DW_FORM_STRX1: u64 = 0x25;
pub const DW_FORM_STRX2: u64 = 0x26;

pub const DW_AT_NAME: u64 = 0x03;
pub const DW_AT_BYTE_SIZE: u64 = 0x0b;
pub const DW_AT_STMT_LIST: u64 = 0x10;
#[cfg(test)]
pub const DW_AT_LOW_PC: u64 = 0x11;
#[cfg(test)]
pub const DW_AT_HIGH_PC: u64 = 0x12;
pub const DW_AT_CONST_VALUE: u64 = 0x1c;
pub const DW_AT_LOWER_BOUND: u64 = 0x22;
pub const DW_AT_UPPER_BOUND: u64 = 0x2f;
pub const DW_AT_COUNT: u64 = 0x37;
pub const DW_AT_DATA_MEMBER_LOCATION: u64 = 0x38;
pub const DW_AT_ENCODING: u64 = 0x3e;
pub const DW_AT_TYPE: u64 = 0x49;

#[cfg(test)]
pub const DW_ATE_ADDRESS: u64 = 0x01;
#[cfg(test)]
pub const DW_ATE_BOOLEAN: u64 = 0x02;
#[cfg(test)]
pub const DW_ATE_FLOAT: u64 = 0x04;
#[cfg(test)]
pub const DW_ATE_SIGNED: u64 = 0x05;
#[cfg(test)]
pub const DW_ATE_SIGNED_CHAR: u64 = 0x06;
#[cfg(test)]
pub const DW_ATE_UNSIGNED: u64 = 0x07;
#[cfg(test)]
pub const DW_ATE_UNSIGNED_CHAR: u64 = 0x08;
#[cfg(test)]
pub const DW_ATE_UTF: u64 = 0x10;

pub const DW_CHILDREN_NO: u8 = 0x00;
pub const DW_CHILDREN_YES: u8 = 0x01;

pub const DW_UT_COMPILE: u8 = 0x01;
pub const DW_UT_TYPE: u8 = 0x02;
pub const DW_UT_PARTIAL: u8 = 0x03;
pub const DW_UT_SKELETON: u8 = 0x04;
pub const DW_UT_SPLIT_COMPILE: u8 = 0x05;
pub const DW_UT_SPLIT_TYPE: u8 = 0x06;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dwarf_tag_values_are_distinct() {
        let tags = [
            DW_TAG_ARRAY_TYPE,
            DW_TAG_FORMAL_PARAMETER,
            DW_TAG_LEXICAL_BLOCK,
            DW_TAG_MEMBER,
            DW_TAG_POINTER_TYPE,
            DW_TAG_COMPILE_UNIT,
            DW_TAG_STRUCTURE_TYPE,
            DW_TAG_SUBROUTINE_TYPE,
            DW_TAG_TYPEDEF,
            DW_TAG_UNION_TYPE,
            DW_TAG_UNSPECIFIED_PARAMETERS,
            DW_TAG_SUBRANGE_TYPE,
            DW_TAG_BASE_TYPE,
            DW_TAG_CONST_TYPE,
            DW_TAG_ENUMERATOR,
            DW_TAG_SUBPROGRAM,
            DW_TAG_VARIABLE,
            DW_TAG_VOLATILE_TYPE,
            DW_TAG_NAMESPACE,
            DW_TAG_ENUMERATION_TYPE,
            DW_TAG_UNSPECIFIED_TYPE,
        ];
        for (i, a) in tags.iter().enumerate() {
            for (j, b) in tags.iter().enumerate() {
                if i != j {
                    assert_ne!(a, b, "DW_TAG values at indices {i} and {j} must differ");
                }
            }
        }
    }

    #[test]
    fn test_dwarf_form_values_are_distinct() {
        let forms = [
            DW_FORM_ADDR,
            DW_FORM_BLOCK2,
            DW_FORM_BLOCK4,
            DW_FORM_DATA2,
            DW_FORM_DATA4,
            DW_FORM_DATA8,
            DW_FORM_STRING,
            DW_FORM_BLOCK,
            DW_FORM_BLOCK1,
            DW_FORM_DATA1,
            DW_FORM_FLAG,
            DW_FORM_SDATA,
            DW_FORM_STRP,
            DW_FORM_UDATA,
            DW_FORM_REF_ADDR,
            DW_FORM_REF1,
            DW_FORM_REF2,
            DW_FORM_REF4,
            DW_FORM_REF8,
            DW_FORM_REF_UDATA,
            DW_FORM_INDIRECT,
            DW_FORM_SEC_OFFSET,
            DW_FORM_EXPRLOC,
            DW_FORM_FLAG_PRESENT,
            DW_FORM_ADDRX,
            DW_FORM_LINE_STRP,
            DW_FORM_IMPLICIT_CONST,
            DW_FORM_STRX1,
            DW_FORM_STRX2,
        ];
        for (i, a) in forms.iter().enumerate() {
            for (j, b) in forms.iter().enumerate() {
                if i != j {
                    assert_ne!(a, b, "DW_FORM values at indices {i} and {j} must differ");
                }
            }
        }
    }

    #[test]
    fn test_dw_children_values() {
        assert_eq!(DW_CHILDREN_NO, 0);
        assert_eq!(DW_CHILDREN_YES, 1);
        assert_ne!(DW_CHILDREN_NO, DW_CHILDREN_YES);
    }

    #[test]
    fn test_dw_ut_values_are_sequential() {
        assert_eq!(DW_UT_COMPILE, 1);
        assert_eq!(DW_UT_TYPE, 2);
        assert_eq!(DW_UT_PARTIAL, 3);
        assert_eq!(DW_UT_SKELETON, 4);
        assert_eq!(DW_UT_SPLIT_COMPILE, 5);
        assert_eq!(DW_UT_SPLIT_TYPE, 6);
    }

    #[test]
    fn test_dw_ate_values_are_distinct() {
        let ates = [
            DW_ATE_ADDRESS,
            DW_ATE_BOOLEAN,
            DW_ATE_FLOAT,
            DW_ATE_SIGNED,
            DW_ATE_SIGNED_CHAR,
            DW_ATE_UNSIGNED,
            DW_ATE_UNSIGNED_CHAR,
            DW_ATE_UTF,
        ];
        for (i, a) in ates.iter().enumerate() {
            for (j, b) in ates.iter().enumerate() {
                if i != j {
                    assert_ne!(a, b, "DW_ATE values at indices {i} and {j} must differ");
                }
            }
        }
    }

    #[test]
    fn test_well_known_tag_values() {
        // These values come from the DWARF standard
        assert_eq!(DW_TAG_COMPILE_UNIT, 0x11);
        assert_eq!(DW_TAG_SUBPROGRAM, 0x2e);
        assert_eq!(DW_TAG_BASE_TYPE, 0x24);
        assert_eq!(DW_TAG_VARIABLE, 0x34);
        assert_eq!(DW_TAG_POINTER_TYPE, 0x0f);
    }

    #[test]
    fn test_well_known_attribute_values() {
        // Standard DWARF attribute numbers
        assert_eq!(DW_AT_NAME, 0x03);
        assert_eq!(DW_AT_LOW_PC, 0x11);
        assert_eq!(DW_AT_HIGH_PC, 0x12);
        assert_eq!(DW_AT_TYPE, 0x49);
        assert_eq!(DW_AT_BYTE_SIZE, 0x0b);
        assert_eq!(DW_AT_ENCODING, 0x3e);
    }

    #[test]
    fn test_well_known_form_values() {
        assert_eq!(DW_FORM_ADDR, 0x01);
        assert_eq!(DW_FORM_DATA1, 0x0b);
        assert_eq!(DW_FORM_DATA2, 0x05);
        assert_eq!(DW_FORM_DATA4, 0x06);
        assert_eq!(DW_FORM_DATA8, 0x07);
        assert_eq!(DW_FORM_STRING, 0x08);
        assert_eq!(DW_FORM_FLAG_PRESENT, 0x19);
    }
}
