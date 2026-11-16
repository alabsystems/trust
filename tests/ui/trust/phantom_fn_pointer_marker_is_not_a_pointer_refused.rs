//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `phantom_fn_pointer_marker_is_not_a_pointer.rs`: here the `fn` pointer is
//! a real value inside `Map`, pointing at a user function that panics on 0, so the
//! std `max` reaches user code and must not be tolerated.
fn inv(x: &u32) -> u32 {
    100 / *x
}

pub fn max_inv(v: &[u32]) -> Option<u32> { //~ ERROR verification
    let f: fn(&u32) -> u32 = inv;
    v.iter().map(f).max()
}
