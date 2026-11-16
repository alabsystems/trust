//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! A user callee that writes ELEMENTS of a `&mut [u8]` cannot change its length, so
//! a bound established before the call still holds after it. The twin of
//! `callee_reseat_kills_the_length_refused.rs`, whose callees reseat the pointer.

fn bump(s: &mut [u8]) {
    if !s.is_empty() {
        s[0] = s[0].wrapping_add(1);
    }
}

pub fn after_bump(s: &mut [u8], i: usize) -> u8 {
    if i < s.len() {
        bump(s);
        s[i]
    } else {
        0
    }
}
