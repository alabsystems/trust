//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! An ENUM-element array matched by position reads its element with the ELEMENT op.
//!
//! `lower_tuple_match` reads a C-like enum element's tag as `ExtractField(element, 0)`. For an
//! array scrutinee it used to take the element itself with `ExtractField` on the ARRAY too — a
//! validator reject ("aggregate operand must be a struct/record/tuple/enum/closure",
//! `FieldAccessInvalid`), and so a hard compile error under the default `-Ztrust-verify=on` on
//! valid code. Measured on the pre-change compiler (7bc480faf), one function per file: `cls`,
//! `pair` and `consts` below each failed final module validation with `FieldAccessInvalid`. The
//! element is now read with `ExtractElement` at its position, then its tag with `ExtractField`.
//!
//! Under `strict`, so a refusal is a compile error too: each body must LOWER, not merely
//! compile. And under the DEFAULT policy, not `advisory`: advisory demotes a finalization
//! failure to a warning, which is exactly the regression this file exists to catch.

#![allow(dead_code)]

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum E {
    A,
    B,
}

// A literal-variant test at the head and one at the tail through `..`.
pub fn cls(v: [E; 4]) -> u8 {
    match v {
        [E::A, .., E::B] => 1,
        _ => 0,
    }
}

// Every position tested, in a two-element array.
pub fn pair(v: [E; 2]) -> u8 {
    match v {
        [E::A, E::A] => 0,
        [E::A, E::B] => 1,
        [E::B, _] => 2,
    }
}

// A constant `[E; N]` scrutinee.
const D: [E; 2] = [E::A, E::B];

pub fn consts() -> bool {
    matches!(D, [E::A, E::B])
}
