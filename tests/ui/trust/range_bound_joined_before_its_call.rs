//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@[default] compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//! A range bound set on two paths (`let k = if .. { n } else { b.len() }`) has no
//! single value, so it resolved to nothing and `&b[..k]` became the always-violated
//! fail-close: a FAILED refutation of a correct slice (ordsweep2 strings/c15). The
//! range is built in the indexing call's own block and nothing writes `k` after it,
//! so the call reads the value the range holds. The twin `_refused.rs` keeps a
//! bound that can exceed the length refused.
pub fn prefix(b: &[u8], n: usize) -> &[u8] {
    let k = if n < b.len() { n } else { b.len() };
    &b[..k]
}

pub fn middle(b: &[u8], lo: usize, hi: usize) -> &[u8] {
    let e = if hi <= b.len() { hi } else { b.len() };
    let s = if lo <= e { lo } else { e };
    &b[s..e]
}
