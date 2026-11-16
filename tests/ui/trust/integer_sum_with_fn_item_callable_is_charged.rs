//@ revisions: map_sum filter_sum map_product range_filter plus_zero char_gt char_lt
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A `sum`/`product` whose adapter callable is a local FN ITEM renders as
//! `<Map<Copied<Iter<'_, u8>>, fn(u8) -> u32 {big}> as Iterator>::sum::<u32>`.
//! vcgen's callee parsers read the `>` of that `->` as a closing bracket, so the
//! fold row charging the overflow was never minted, while the compiler (deciding on
//! `DefId`s) granted the call as charged. Review round 29 (2026-10-01) measured
//! every revision building rc=0 under certify (`plus_zero`: "1 proved", the `+ 0`)
//! while each panicked at `core::iter::traits::accum` with an overflow. The parsers
//! now mask `->` before counting brackets.
//!
//! `char_gt` / `char_lt` (review round 30): a `'>'`/`'<'` char const generic in the
//! callable's rendering broke the same parse, as did a source path with `<`/`>`
//! inside a closure's `{closure@...}` type. Masking cannot be complete for
//! rendered text, so the compiler now grants a sum/product only when vcgen's own
//! fold recognizer accepts the call's exact rendered spelling
//! (`trust_vcgen::callee_is_charged_integer_fold`); a miss leaves the call
//! ungranted, bundled and refused.
fn keep(_x: &u32) -> bool {
    true
}
fn dbl(x: u32) -> u32 {
    x
}
fn big(_x: u8) -> u32 {
    u32::MAX
}

#[cfg(map_sum)]
pub fn f(a: &[u8; 4]) -> u32 { //[map_sum]~ ERROR verification
    a.iter().copied().map(big).sum()
}
#[cfg(filter_sum)]
pub fn f(a: &[u32; 4]) -> u32 { //[filter_sum]~ ERROR verification
    a.iter().copied().filter(keep).sum()
}
#[cfg(map_product)]
pub fn f(a: &[u32; 4]) -> u32 { //[map_product]~ ERROR verification
    a.iter().copied().map(dbl).product()
}
#[cfg(range_filter)]
pub fn f(n: u32) -> u32 { //[range_filter]~ ERROR verification
    (0..n).filter(keep).sum()
}
#[cfg(plus_zero)]
pub fn f(a: &[u8; 4]) -> u32 { //[plus_zero]~ ERROR verification
    a.iter().copied().map(big).sum::<u32>() + 0
}

pub struct K<const C: char>;
#[cfg(char_gt)]
impl K<'>'> {
    fn big(_x: u8) -> u32 {
        u32::MAX
    }
}
#[cfg(char_gt)]
pub fn f(a: &[u8; 4]) -> u32 { //[char_gt]~ ERROR verification
    a.iter().copied().map(K::<'>'>::big).sum()
}
#[cfg(char_lt)]
impl K<'<'> {
    fn big(_x: u8) -> u32 {
        u32::MAX
    }
}
#[cfg(char_lt)]
pub fn f(a: &[u8; 4]) -> u32 { //[char_lt]~ ERROR verification
    a.iter().copied().map(K::<'<'>::big).sum()
}
