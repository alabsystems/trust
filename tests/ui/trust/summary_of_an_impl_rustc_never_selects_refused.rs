//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
#![feature(specialization)]
#![allow(incomplete_features)]
//! A trait impl's method summary applies only at the instantiation rustc ROUTES to
//! that method, which coherence alone does not decide. Every caller below panics.
//!
//! MEASURED FALSE PROOFS, 2026-09-30 (round 8 of the callee-summary review): the
//! impl for `Holder<u8>` has a where-clause that can never hold, so under
//! `specialization` it is never selected and `Holder(0u8).m(x)` runs the TRAIT
//! DEFAULT through the blanket impl. The call carries exactly the identity of a call
//! to `Tr::m` at the dead impl's own header, `[Holder<u8>]`, and renders as the dead
//! impl's def path, so its summaries (`x.min(3)`, `g.max(1)`, `{1, 2}`, `*p = v`)
//! were applied: `go`, `go_low` and `go_kst` were PROVED and kernel-certified,
//! `go_set` proved. The registration now asks `Instance::try_resolve`.

pub trait Never {}

pub trait Tr {
    #[inline(never)]
    fn m(&self, x: usize) -> usize {
        x
    }
    #[inline(never)]
    fn den(&self, g: u32) -> u32 {
        g
    }
    #[inline(never)]
    fn k(&self, _c: bool) -> u32 {
        0
    }
    #[inline(never)]
    fn set(&self, p: &mut u32, _v: u32) {
        *p = 0;
    }
}

pub struct Holder<X>(pub X);

impl<X: Copy> Tr for Holder<X> {}

impl<'a> Tr for Holder<u8>
where
    &'a (): Never,
{
    #[inline(never)]
    fn m(&self, x: usize) -> usize {
        x.min(3)
    }
    #[inline(never)]
    fn den(&self, g: u32) -> u32 {
        g.max(1)
    }
    #[inline(never)]
    fn k(&self, c: bool) -> u32 {
        if c { 1 } else { 2 }
    }
    #[inline(never)]
    fn set(&self, p: &mut u32, v: u32) {
        *p = v;
    }
}

// x = 10.
#[inline(never)]
pub fn go(x: usize, a: &[u8; 4]) -> u8 { //~ ERROR strict verification failed for `summary_of_an_impl_rustc_never_selects_refused::go`
    a[Holder(0u8).m(x)]
}

// g = 0.
#[inline(never)]
pub fn go_low(h: u32, g: u32) -> u32 { //~ ERROR strict verification failed for `summary_of_an_impl_rustc_never_selects_refused::go_low`
    h % Holder(0u8).den(g)
}

#[inline(never)]
pub fn go_kst(h: u32, c: bool) -> u32 { //~ ERROR strict verification failed for `summary_of_an_impl_rustc_never_selects_refused::go_kst`
    h / Holder(0u8).k(c)
}

// v = 5.
#[inline(never)]
pub fn go_set(v: u32) -> u32 { //~ WARN safety verification incomplete for `summary_of_an_impl_rustc_never_selects_refused::go_set`
    let mut a = 7u32;
    Holder(0u8).set(&mut a, v);
    assert!(a == v);
    a
}
