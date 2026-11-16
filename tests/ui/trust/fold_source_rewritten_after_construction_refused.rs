//@ revisions: field_store via_callee via_alias product
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The integer fold row bounds `r.sum()` by the iterator's defining `Range`
//! aggregate. Review round 31 (2026-10-01) measured each revision CERTIFIED (1
//! proved, kernel-certified) while it panics in core's `Sum`/`Product`: the
//! definition lookup counted neither a partial store (`r.end = ...`) nor a write
//! through an `&mut` handed out, so the first aggregate (3 items) bounded a sum of
//! 100000. A source local must now be a single static assignment as well.
#[cfg(field_store)]
pub fn f() -> u32 { //[field_store]~ ERROR verification
    let mut r = 0u32..3;
    r.end = 100_000;
    r.sum::<u32>()
}

#[cfg(via_callee)]
#[inline(never)]
fn bump(r: &mut core::ops::Range<u32>) {
    r.end = 100_000;
}
#[cfg(via_callee)]
pub fn f() -> u32 { //[via_callee]~ ERROR verification
    let mut r = 0u32..3;
    bump(&mut r);
    r.sum::<u32>()
}

#[cfg(via_alias)]
pub fn f() -> u32 { //[via_alias]~ ERROR verification
    let mut r = 0u32..3;
    let p = &mut r;
    p.end = 100_000;
    r.sum::<u32>()
}

#[cfg(product)]
pub fn f() -> u32 { //[product]~ ERROR verification
    let mut r = 1u32..2;
    r.end = 20;
    r.product::<u32>()
}
