//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twins of `search_unwrap_or_length_is_bounded.rs`. Each panics on the
//! input named beside it.

// v = [1]: not found, and the default is past the end.
pub fn default_past_the_end(v: &[u8]) -> &[u8] { //~ ERROR failed for `search_unwrap_or_length_is_bounded_refused::default_past_the_end`
    let i = v.iter().position(|&x| x == 0).unwrap_or(v.len() + 1);
    &v[i..]
}

// s = "é": not found, and byte 1 is inside the char.
pub fn default_inside_a_char(s: &str) -> &str { //~ ERROR failed for `search_unwrap_or_length_is_bounded_refused::default_inside_a_char`
    &s[..s.find(',').unwrap_or(1)]
}

// v = [0], w = []: the search ran over another slice.
pub fn other_slice<'a>(v: &[u8], w: &'a [u8]) -> &'a [u8] { //~ ERROR failed for `search_unwrap_or_length_is_bounded_refused::other_slice`
    let i = v.iter().position(|&x| x == 0).unwrap_or(0);
    &w[i + 1..]
}
