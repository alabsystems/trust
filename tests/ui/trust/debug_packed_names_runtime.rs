//@ run-pass
//@ needs-unwind
//@ edition: 2021
#![feature(fmt_helpers_for_derive)]
#![allow(dead_code)]

// Runtime ground truth for the extractor's packed-name call guards. Both bad
// helpers reach core's name iterator unwrap although all field Debug impls are total.
use std::fmt;

struct BadFixed;
impl fmt::Debug for BadFixed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct_field2_finish("Bad first", &1u64, &2u64)
    }
}

struct BadNary;
impl fmt::Debug for BadNary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct_fields_finish("Bad first", &[&1u64, &2u64])
    }
}

struct PanickingField;
impl fmt::Debug for PanickingField {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result { panic!("field") }
}

struct BadArray;
impl fmt::Debug for BadArray {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut values: [&dyn fmt::Debug; 2] = [&1u64, &2u64];
        values[0] = &PanickingField;
        f.debug_struct_fields_finish("Bad first second", &values)
    }
}

struct BadSlot;
impl fmt::Debug for BadSlot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut value: &dyn fmt::Debug = &1u64;
        let address = &raw mut value;
        unsafe { *address = &PanickingField; }
        f.debug_struct_field2_finish("Bad first second", value, &2u64)
    }
}

#[derive(Debug)]
struct Pair { first: u64, second: bool }
#[derive(Debug)]
struct Tuple(u64, bool);
#[derive(Debug)]
struct Many { a: u64, b: u64, c: u64, d: u64, e: u64, f: bool }
#[derive(Debug)]
struct TupleMany(u64, u64, u64, u64, u64, bool);

fn main() {
    assert!(std::panic::catch_unwind(|| format!("{:?}", BadFixed)).is_err());
    assert!(std::panic::catch_unwind(|| format!("{:?}", BadNary)).is_err());
    assert!(std::panic::catch_unwind(|| format!("{:?}", BadArray)).is_err());
    assert!(std::panic::catch_unwind(|| format!("{:?}", BadSlot)).is_err());
    assert_eq!(format!("{:?}", Pair { first: 1, second: true }), "Pair { first: 1, second: true }");
    assert_eq!(format!("{:?}", Tuple(1, true)), "Tuple(1, true)");
    assert_eq!(
        format!("{:?}", Many { a: 1, b: 2, c: 3, d: 4, e: 5, f: true }),
        "Many { a: 1, b: 2, c: 3, d: 4, e: 5, f: true }",
    );
    assert_eq!(format!("{:?}", TupleMany(1, 2, 3, 4, 5, true)), "TupleMany(1, 2, 3, 4, 5, true)");
}
