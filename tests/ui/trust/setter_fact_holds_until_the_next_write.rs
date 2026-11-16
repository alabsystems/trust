//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! After a trivial setter call, the target holds the set value, and so does a copy
//! of it taken after the call, until the next write. The twin of
//! `setter_fact_is_live_only_until_the_next_write_refused.rs`.

#[inline(never)]
pub fn set(p: &mut u32, v: u32) {
    *p = v;
}

pub fn value_after_the_call(mut x: u32) {
    set(&mut x, 5);
    assert!(x == 5);
}

pub fn copy_after_the_call(mut x: u32) {
    set(&mut x, 5);
    let b = x;
    assert!(b == 5);
}
