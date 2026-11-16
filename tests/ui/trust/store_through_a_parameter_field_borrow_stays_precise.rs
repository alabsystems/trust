//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! A store through a borrow of a PARAMETER's field is a precise write of that field:
//! nothing else in the body names that memory, so the sibling field keeps its facts.
//! The twin of `store_through_an_unresolved_pointer_refused.rs`.

pub struct P {
    pub x: u8,
    pub y: u8,
}

pub fn sibling_kept(s: &mut P) -> u8 {
    if s.y < 5 {
        let x = &mut s.x;
        *x = 250;
        s.y + 250
    } else {
        0
    }
}
