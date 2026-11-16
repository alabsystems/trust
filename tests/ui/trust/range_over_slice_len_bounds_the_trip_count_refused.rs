//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `range_over_slice_len_bounds_the_trip_count.rs`: `isize::MAX` items of
//! `+= 3` exceed `usize::MAX`, so the bound must not prove this counter.
pub fn triple(v: &[u8]) -> usize { //~ ERROR verification
    let mut c = 0usize;
    for _ in 0..v.len() {
        c += 3;
    }
    c
}

/// A RAW slice pointer's length is unconstrained metadata
/// (`ptr::slice_from_raw_parts(p, usize::MAX)` is safe), so this counter, which
/// proves over a `&[u32]` (`from_one` in the twin), overflows on the last of
/// `usize::MAX` trips and must not inherit the bound.
pub fn from_one_raw(p: *const [u8]) -> usize { //~ ERROR verification
    let mut c = 1usize;
    for _ in 0..p.len() {
        c += 1;
    }
    c
}

/// A slice of a zero-sized element can be `usize::MAX` long, so the same counter
/// overflows over `&[()]` and must not inherit the bound either.
pub fn from_one_zst(v: &[()]) -> usize { //~ ERROR verification
    let mut c = 1usize;
    for _ in 0..v.len() {
        c += 1;
    }
    c
}
