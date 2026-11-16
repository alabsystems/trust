//@ revisions: off_by_one resliced plus_one shadowed
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `ensures_over_slice_len.rs`. `off_by_one` and `plus_one` are false.
//! `resliced`: a `mut` slice parameter rebound in the body has no stable length,
//! so its leaf is not rebound and the clause stays unproved. `shadowed`: a body
//! `xs` shadows the parameter, so the name is not unique and nothing is rebound.
#[cfg(off_by_one)]
pub fn f(xs: &[u32]) -> usize //[off_by_one]~ ERROR verification
    ensures result == xs.len()
{
    if xs.len() > 0 { xs.len() - 1 } else { 0 }
}

#[cfg(resliced)]
pub fn f(mut xs: &[u32]) -> usize //[resliced]~ ERROR verification
    ensures result == xs.len()
{
    if xs.len() > 0 {
        xs = &xs[1..];
    }
    xs.len()
}

#[cfg(plus_one)]
pub fn f(xs: &[u32]) -> usize //[plus_one]~ ERROR verification
    ensures result == xs.len() + 1
{
    xs.len()
}

#[cfg(shadowed)]
pub fn f(xs: &[u32]) -> usize //[shadowed]~ ERROR verification
    ensures result == xs.len()
{
    let xs = if xs.len() > 0 { &xs[1..] } else { xs };
    xs.len()
}
