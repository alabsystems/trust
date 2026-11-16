//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! A value read before a same-block write keeps what its own guard says, and the
//! written place holds the new value: the twin of
//! `read_before_a_same_block_write_keeps_the_old_value_refused.rs`.

pub fn old_value_guarded(mut x: usize, a: &[u8; 4]) -> u8 {
    let old = x;
    x = 0;
    if old < 4 { a[old] | a[x] } else { 0 }
}

pub fn old_pointee_guarded(p: &mut usize, a: &[u8; 4]) -> u8 {
    let old = *p;
    *p = 1;
    if old < 4 { a[old] | a[*p] } else { 0 }
}
