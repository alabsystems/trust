//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-ANL): a NAMED or associated-const array length.
//!
//! `try_to_target_usize` goes through `try_to_scalar_int` and never EVALUATES,
//! so `[u8; INLINE_SIZE]` returned `None` and the whole array type was refused
//! — while the ORACLE does precisely the refused thing: `trust-mir-extract`'s
//! `ty_convert` falls back to a normalize before reading the length, and its
//! own comment warns that leaving these unsupported "wrongly fails
//! panic-freedom on ordinary fixed arrays". So the producer was the SOLE
//! refuser and the differential could never have compared the pair.
//!
//! The normalize goes through the SHIPPED `cycle_safe_normalize`, not a
//! hand-rolled call: that helper carries the opaque/TAIT screens a raw
//! `try_normalize_erasing_regions` loses, which is the documented E0391 hazard
//! of normalizing inside `mir_built`. And the result is RE-READ rather than
//! assumed — a normalized type that is not an array with a readable length
//! keeps the tag.

pub const INLINE_SIZE: usize = 4;

pub trait HasLen {
    const N: usize;
}

pub struct Four;
impl HasLen for Four {
    const N: usize = 3;
}

pub fn named_len() -> u8 {
    let a: [u8; INLINE_SIZE] = [1, 2, 3, 4];
    a[0] + a[3]
}

pub fn named_len_sum(v: [u8; INLINE_SIZE]) -> u8 {
    v[1] + v[2]
}

fn main() {
    assert_eq!(named_len(), 5);
    assert_eq!(named_len_sum([9, 2, 3, 9]), 5);
    assert_eq!(<Four as HasLen>::N, 3);
}
