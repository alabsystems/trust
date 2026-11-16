//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twins of `str_len_is_the_slice_length.rs`. Each panics on the input
//! named beside it.

// s = "", i = 0: the index may equal the length.
pub fn byte_at_the_length(s: &str, i: usize) -> u8 { //~ ERROR failed for `str_len_is_the_slice_length_refused::byte_at_the_length`
    if i <= s.len() { s.as_bytes()[i] } else { 0 }
}

// s = "", t = "a", i = 0: the length of another string.
pub fn another_length(s: &str, t: &str, i: usize) -> u8 { //~ ERROR failed for `str_len_is_the_slice_length_refused::another_length`
    if i < t.len() { s.as_bytes()[i] } else { 0 }
}

// s = "": no emptiness guard, so `s.len() - 1` underflows.
pub fn last_unguarded(s: &str) -> u8 { //~ ERROR failed for `str_len_is_the_slice_length_refused::last_unguarded`
    s.as_bytes()[s.len() - 1]
}

pub trait Len {
    fn len(&self) -> usize;
}

impl Len for str {
    fn len(&self) -> usize {
        usize::MAX
    }
}

// s = "", i = 0: a user trait's `len` on `str` is not the byte length.
pub fn user_trait_len(s: &str, i: usize) -> u8 { //~ ERROR failed for `str_len_is_the_slice_length_refused::user_trait_len`
    if i < Len::len(s) { s.as_bytes()[i] } else { 0 }
}
