//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! A whole-pointee store `*p = v` through a `&mut` parameter makes `*p` a NEW value:
//! a read of `*p` before the store keeps the OLD one. Each panics on the input named
//! beside it.
//!
//! MEASURED FALSE PROOFS, 2026-09-29 (an adversarial audit; the first four were
//! already proved by the 2026-09-17 pack): the store's definition had no establish
//! point (the search looked for a write of the base `p`, which a parameter never
//! gets), so it shipped with the bare subject `p*`, which is also how the ENTRY
//! value of `*p` is spelled, and the old read and the new value became one symbol.
//! `whole_pointee_store_value_is_known.rs` is the positive twin.

// *p = 7: `old` is 7, and `a` has 4 elements.
pub fn stale_scalar(p: &mut usize, a: &[u8; 4], u: &str) -> u8 { //~ ERROR failed for `whole_pointee_store_is_a_new_value_refused::stale_scalar`
    let old = *p;
    let _x = u.as_bytes();
    *p = 0;
    let _y = u.as_bytes();
    a[old]
}

// *p = 7, a = [0; 4]: the guard is on the NEW value.
pub fn guard_on_the_new_value(p: &mut usize, a: &[u8], u: &str) -> u8 { //~ ERROR failed for `whole_pointee_store_is_a_new_value_refused::guard_on_the_new_value`
    let old = *p;
    let _n = u.as_bytes();
    *p = 2;
    if *p < a.len() { a[old] } else { 0 }
}

// s = "", t = "a": the old length is 0.
pub fn stale_length_underflow<'a>(s: &mut &'a str, t: &'a str, u: &str) -> usize { //~ ERROR failed for `whole_pointee_store_is_a_new_value_refused::stale_length_underflow`
    let old = s.len();
    let _x = u.as_bytes();
    *s = t;
    let _y = u.as_bytes();
    if t.len() > 0 { old - 1 } else { 0 }
}

// s = "abcdefgh", t = "", a = [0]: the old length indexes a shorter slice.
pub fn stale_length_index<'a>(s: &mut &'a str, t: &'a str, u: &str, a: &[u8]) -> u8 { //~ ERROR failed for `whole_pointee_store_is_a_new_value_refused::stale_length_index`
    let n = s.len();
    let _x = u.as_bytes();
    *s = t;
    let _y = u.as_bytes();
    if t.len() < a.len() { a[n] } else { 0 }
}

// s = "", t = "abc", i = 1: `b` views the OLD, empty string.
pub fn old_view_new_length<'a>(s: &mut &'a str, t: &'a str, i: usize) -> u8 { //~ ERROR failed for `whole_pointee_store_is_a_new_value_refused::old_view_new_length`
    let b = s.as_bytes();
    *s = t;
    if i < s.len() { b[i] } else { 0 }
}

// s = [], t = [1, 2], i = 0: the slice twin.
pub fn old_slice_new_length<'a>(s: &mut &'a [u8], t: &'a [u8], u: &str, i: usize) -> u8 { //~ ERROR failed for `whole_pointee_store_is_a_new_value_refused::old_slice_new_length`
    let b: &[u8] = *s;
    let _n = u.as_bytes();
    *s = t;
    if i < s.len() { b[i] } else { 0 }
}
