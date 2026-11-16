//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twin of `position_index_bounds_a_range_slice.rs`: `i + 2` can pass
//! the end — `past_the_zero(&[0])` panics — so the bound on the payload must not
//! prove it.

pub fn past_the_zero(v: &[u8]) -> &[u8] { //~ ERROR failed for `position_index_bounds_a_range_slice_refused::past_the_zero`
    match v.iter().position(|&b| b == 0) {
        Some(i) => &v[..i + 2],
        None => v,
    }
}
