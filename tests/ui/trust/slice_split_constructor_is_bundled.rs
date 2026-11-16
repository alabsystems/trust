//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! `<[T]>::split(pred)` only moves the slice and the predicate into `Split`. Its
//! `core::slice` family decline left it a generic absent callee (a closure type
//! argument) and the caller fail-closed (sweep `c68`); it is now bundled and
//! lowers. Default policy only: `Split::next`'s own aggregate stays runtime-checked
//! under certify. The twin `_refused.rs` keeps a panicking predicate refused.
pub fn segments(v: &[u32]) -> usize {
    let mut n = 0usize;
    for part in v.split(|x| *x == 0) {
        if !part.is_empty() {
            n += 1;
        }
    }
    n
}
