//@ needs-trust-verify
//@ edition: 2021
//@ revisions: option_payload_written iter_mut_payload_written
//@ revisions: option_payload_read_only iter_mut_payload_written_after_use
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[option_payload_written] check-fail
//@[iter_mut_payload_written] check-fail
//@[option_payload_read_only] check-pass
//@[iter_mut_payload_written_after_use] check-pass
//! **A pointer moved out of an `Option` or an iterator item names its pointee
//! through the enum, and a write through it re-versions that name (Trust,
//! 2026-09-29).**
//!
//! `place_to_var_name` spells the pointee of `b` in `if let Some(b) = o` as
//! `o@1.0*`: `@1` is the `Some` downcast, and `@` is one of the characters a
//! projection segment starts with (`PROJECTION_SEGMENT_LEAD`). The version fabric
//! had four copies of that set that listed only `.`, `[` and `*`, so `o@1.0*` was not
//! a projection of `o`. A call re-versions a pointer-carrying local by its base name
//! and relies on prefix overlap to reach the pointees, so a call writing through `b`
//! never reached `o@1.0*`, and a guard on `*b` survived it:
//! `if *b > 96 { b.make_ascii_uppercase(); *b - 90 }` was proved and panics for
//! `b'a'`. The fabric now asks `is_projection_segment_lead`, the namer's own set.
//!
//! * `option_payload_written`, `iter_mut_payload_written`: NEGATIVE.
//! * `option_payload_read_only`, `iter_mut_payload_written_after_use`: POSITIVE —
//!   nothing writes the pointee between the guard and the use.

#[cfg(option_payload_written)]
pub fn uppercase_then_offset(o: Option<&mut u8>) -> u8 {
    //[option_payload_written]~^ ERROR Trust
    if let Some(b) = o {
        if *b > 96 {
            b.make_ascii_uppercase();
            return *b - 90;
        }
    }
    0
}

#[cfg(iter_mut_payload_written)]
pub fn letter_mask(word: &mut [u8]) -> u32 {
    //[iter_mut_payload_written]~^ ERROR Trust
    let mut mask = 0u32;
    for b in word.iter_mut() {
        if *b > 96 {
            b.make_ascii_uppercase();
            let idx = *b - 90;
            mask |= 1u32 << (idx % 32);
        }
    }
    mask
}

#[cfg(option_payload_read_only)]
pub fn offset(o: Option<&mut u8>) -> u8 {
    if let Some(b) = o {
        if *b > 96 {
            return *b - 90;
        }
    }
    0
}

#[cfg(iter_mut_payload_written_after_use)]
pub fn offsets_then_uppercase(word: &mut [u8]) -> u32 {
    let mut s = 0u32;
    for b in word.iter_mut() {
        if *b > 96 {
            s = s.wrapping_add((*b - 90) as u32);
            b.make_ascii_uppercase();
        }
    }
    s
}
