// Regression test for rust-lang#118328.
// Incorrect optimization of enum with niche: LLVM's range metadata or
// niche-filling optimization could miscompile enums where the niche
// overlaps with a valid discriminant range, causing match arms to
// execute incorrectly.
//
// The bug pattern: an enum with a variant containing a type that has
// a niche (like NonZero, bool, or reference) gets its discriminant
// stored in that niche. Under certain optimization levels, LLVM
// could incorrectly assume the niche value is unreachable and
// eliminate the None/other branch.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ build-pass
//@ compile-flags: -C opt-level=3

#![allow(dead_code)]

use std::num::NonZeroU64;

// Enum using NonZeroU64 niche: None is represented as 0 in the u64.
#[inline(never)]
fn check_option_nonzero(val: Option<NonZeroU64>) -> u64 {
    match val {
        Some(n) => n.get(),
        None => 0,
    }
}

// Nested niche: Option<Option<NonZeroU64>> uses two niche values.
#[inline(never)]
fn check_nested_option(val: Option<Option<NonZeroU64>>) -> u64 {
    match val {
        Some(Some(n)) => n.get(),
        Some(None) => 1,
        None => 0,
    }
}

// Enum with multiple variants, one using a niche type.
enum MultiVariant {
    Empty,
    WithRef(NonZeroU64),
    WithBool(bool),
    Pair(NonZeroU64, bool),
}

#[inline(never)]
fn check_multi_variant(v: &MultiVariant) -> u64 {
    match v {
        MultiVariant::Empty => 0,
        MultiVariant::WithRef(n) => n.get(),
        MultiVariant::WithBool(b) => {
            if *b {
                1
            } else {
                2
            }
        }
        MultiVariant::Pair(n, b) => {
            if *b {
                n.get() + 100
            } else {
                n.get()
            }
        }
    }
}

// Enum where bool niche is used for discriminant.
enum BoolNiche {
    A(bool),
    B,
}

#[inline(never)]
fn check_bool_niche(v: BoolNiche) -> u32 {
    match v {
        BoolNiche::A(true) => 1,
        BoolNiche::A(false) => 2,
        BoolNiche::B => 3,
    }
}

fn main() {
    // Option<NonZeroU64> tests.
    let some_val = NonZeroU64::new(42).map(Some).unwrap();
    assert_eq!(check_option_nonzero(some_val), 42);
    assert_eq!(check_option_nonzero(None), 0);

    // Nested option tests.
    let nested_some = Some(NonZeroU64::new(99));
    assert_eq!(check_nested_option(nested_some), 99);
    assert_eq!(check_nested_option(Some(None)), 1);
    assert_eq!(check_nested_option(None), 0);

    // MultiVariant tests.
    let nz = NonZeroU64::new(7).unwrap();
    assert_eq!(check_multi_variant(&MultiVariant::Empty), 0);
    assert_eq!(check_multi_variant(&MultiVariant::WithRef(nz)), 7);
    assert_eq!(check_multi_variant(&MultiVariant::WithBool(true)), 1);
    assert_eq!(check_multi_variant(&MultiVariant::WithBool(false)), 2);
    assert_eq!(check_multi_variant(&MultiVariant::Pair(nz, true)), 107);
    assert_eq!(check_multi_variant(&MultiVariant::Pair(nz, false)), 7);

    // Bool niche tests.
    assert_eq!(check_bool_niche(BoolNiche::A(true)), 1);
    assert_eq!(check_bool_niche(BoolNiche::A(false)), 2);
    assert_eq!(check_bool_niche(BoolNiche::B), 3);
}
