//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@[default] compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//! A native `ensures` may name a slice parameter's length (`xs.len()`), as a
//! `requires` already could. The snippet lane refuses every method call, so the
//! clause is offered to the exact-native lane with the output sort as `_0`, and
//! extraction rebinds the `xs__len` leaf to the body's canonical `xs__slice_len`
//! under the `requires` admission (a unique, length-stable slice parameter). The
//! twin `_refused.rs` keeps false and resliced cases refused.
pub fn just_len(xs: &[u32]) -> usize
    ensures result == xs.len()
{
    xs.len()
}

pub fn at_most_len(xs: &[u32]) -> usize
    ensures result <= xs.len()
{
    0
}

pub fn half(xs: &mut [u32]) -> usize
    ensures result <= xs.len()
{
    xs.len() / 2
}

pub fn nonnegative(xs: &[u8]) -> bool
    ensures xs.len() >= 0
{
    true
}
