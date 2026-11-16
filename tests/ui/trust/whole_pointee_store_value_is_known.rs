//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! After a whole-pointee store `*p = v` through a `&mut` parameter, `*p` is `v`. The
//! positive twin of `whole_pointee_store_is_a_new_value_refused.rs`. (Past a call
//! that cannot reach `p` — `*p = 3; u.as_bytes(); a[*p]` — the native lane still
//! refutes the read-back, on this build and on the 2026-09-17 pack alike.)

pub fn read_back(p: &mut usize, a: &[u8; 4]) -> u8 {
    *p = 2;
    a[*p]
}

pub fn new_string_length<'a>(s: &mut &'a str, t: &'a str, i: usize) -> u8 {
    *s = t;
    if i < s.len() { s.as_bytes()[i] } else { 0 }
}
