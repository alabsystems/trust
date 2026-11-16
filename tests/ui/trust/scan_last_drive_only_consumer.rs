//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@[default] compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! `Iterator::last` drives `next` to the end and keeps the final item, and
//! `Scan::next` runs only its base's `next` and the scanner on `&mut state`. With a
//! verified panic-free scanner over a total std iterator the call is total; it was
//! a runtime-checked absent callee (sweep `q43`). The twin `_refused.rs` keeps a
//! scanner that can overflow refused.
pub fn running_xor(v: &[u32]) -> Option<u32> {
    v.iter().scan(0u32, |st, &x| {
        *st ^= x;
        Some(*st)
    })
    .last()
}

pub fn last_even(v: &[u32]) -> Option<&u32> {
    v.iter().filter(|x| **x % 2 == 0).last()
}
