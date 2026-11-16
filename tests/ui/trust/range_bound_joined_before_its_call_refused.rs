//@ revisions: too_far rewritten reused looped
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `range_bound_joined_before_its_call.rs`. `too_far`: the else arm uses
//! `b.len() + 1`. `rewritten`: the bound is written through a `&mut` after the join,
//! so the version at the call is not the one either arm set. `reused` / `looped`
//! (review round 34): a `Copy` range indexed at a SECOND call after the bound was
//! reassigned was checked against the new bound (the gate matched the first call's
//! block for both rows); both certified and panicked. A range read by more than one
//! call now keeps the fail-close.
#[cfg(too_far)]
pub fn prefix(b: &[u8], n: usize) -> &[u8] { //[too_far]~ ERROR verification
    let k = if n < b.len() { n } else { b.len() + 1 };
    &b[..k]
}

#[cfg(rewritten)]
fn bump(k: &mut usize) {
    *k += 1;
}
#[cfg(rewritten)]
pub fn prefix(b: &[u8], n: usize) -> &[u8] { //[rewritten]~ ERROR verification
    let mut k = if n < b.len() { n } else { b.len() };
    bump(&mut k);
    &b[..k]
}

#[cfg(any(reused, looped))]
#[inline(never)]
fn tick() {}

#[cfg(reused)]
pub fn twice(b: &[u8], c: &[u8], n: usize) -> usize { //[reused]~ ERROR verification
    let mut k = if n < b.len() { n } else { b.len() };
    let r = ..k;
    let x = &b[r];
    k = 0;
    tick();
    let y = &c[r];
    x.len().wrapping_add(y.len()).wrapping_add(k)
}

#[cfg(looped)]
pub fn to_loop(b: &[u8], c: &[u8], n: usize) -> usize { //[looped]~ ERROR verification
    let mut k = if n < b.len() { n } else { b.len() };
    let r = ..k;
    let mut t = b[r].len();
    let mut i = 0;
    while i < 3 {
        k = 0;
        tick();
        t = t.wrapping_add(c[r].len());
        i += 1;
    }
    t.wrapping_add(k)
}
