//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `slice_split_constructor_is_bundled.rs`: this predicate divides by the
//! element, so `v.split(..)` over a slice holding 0 panics inside `Split::next`.
pub fn segments(v: &[u32]) -> usize { //~ ERROR verification
    let mut n = 0usize;
    for part in v.split(|x| 10 / *x == 1) {
        n += part.len().min(1);
    }
    n
}
