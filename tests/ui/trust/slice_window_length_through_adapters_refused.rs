//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twins of `slice_window_length_through_adapters.rs`: each reads
//! one past the item's length, or reads the wrong side of a `zip`, and panics on
//! any input with a full item. The length fact the adapters carry is EXACT (or
//! `[1, n]` for `chunks`), so none of these may prove.

pub fn enumerate_past_the_end(v: &[u32]) -> u32 { //~ ERROR failed for `slice_window_length_through_adapters_refused::enumerate_past_the_end`
    let mut s = 0u32;
    for (_, w) in v.windows(2).enumerate() {
        s ^= w[2];
    }
    s
}

pub fn rev_past_the_end(v: &[u32]) -> u32 { //~ ERROR failed for `slice_window_length_through_adapters_refused::rev_past_the_end`
    let mut s = 0u32;
    for w in v.windows(2).rev() {
        s ^= w[2];
    }
    s
}

// `zip`'s RIGHT item is the `chunks_exact(2)` one here: `d[2]` is out of bounds.
pub fn zip_wrong_side(a: &[u8], b: &[u8]) -> u8 { //~ ERROR failed for `slice_window_length_through_adapters_refused::zip_wrong_side`
    let mut x = 0u8;
    for (c, d) in a.chunks_exact(3).zip(b.chunks_exact(2)) {
        x ^= c[2] ^ d[2];
    }
    x
}

// `chunks(3).rev()` yields the SHORT remainder first: length in [1, 3].
pub fn chunks_remainder(v: &[u8]) -> u8 { //~ ERROR failed for `slice_window_length_through_adapters_refused::chunks_remainder`
    let mut x = 0u8;
    for c in v.chunks(3).rev() {
        x ^= c[2];
    }
    x
}
