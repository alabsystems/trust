//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
#![allow(non_snake_case)]
//! A summary derived from one body describes calls that REACH that body, not a
//! concrete call to ANOTHER body whose rendering matches its def path. Every caller
//! below panics.
//!
//! MEASURED FALSE PROOFS, 2026-09-30 (round 7 of the callee-summary review): a type
//! nested inside a path is not namespace-tagged (residual 7c of
//! `apply_cross_namespace_tag`), so the fn-scoped `struct Inner` inside `fn Up`
//! renders `krate::Up::Inner`, like `mod Up`'s. `Holder(Inner).d(x)` then runs the
//! trait DEFAULT `d` (or the generic inherent `d`) while rendering as the def path of
//! the override (or concrete inherent method) for `Holder<Up::Inner>`, whose return
//! bound, lower bound, constant set or setter effect was applied. The call carries a
//! full identity, the default's or the generic method's, so the identity-presence
//! gate of `summary_needs_a_resolved_call_refused.rs` passed it; the identity now has
//! to be the summarized body's. All four were PROVED and kernel-certified.

pub trait Marker {}

pub struct Holder<X>(pub X);

// ── The upper bound, through a trait default method. x = 10.
pub trait TrUp {
    fn d(&self, x: usize) -> usize {
        x
    }
}

impl<X: Marker> TrUp for Holder<X> {}

pub mod Up {
    pub struct Inner;
}

impl TrUp for Holder<Up::Inner> {
    #[inline(never)]
    fn d(&self, x: usize) -> usize {
        x.min(3)
    }
}

#[inline(never)]
pub fn Up(x: usize, a: &[u8; 4]) -> u8 { //~ ERROR strict verification failed for `summary_needs_the_summarized_body_refused::Up#ns0v`
    struct Inner;
    impl crate::Marker for Inner {}
    a[Holder(Inner).d(x)]
}

// ── The upper bound, through two inherent impls (no trait). x = 10.
pub struct Cell<X>(pub X);

impl<X: Marker> Cell<X> {
    #[inline(never)]
    pub fn d(&self, x: usize) -> usize {
        x
    }
}

pub mod Inh {
    pub struct Inner;
}

impl Cell<Inh::Inner> {
    #[inline(never)]
    pub fn d(&self, x: usize) -> usize {
        x.min(3)
    }
}

#[inline(never)]
pub fn Inh(x: usize, a: &[u8; 4]) -> u8 { //~ ERROR strict verification failed for `summary_needs_the_summarized_body_refused::Inh#ns0v`
    struct Inner;
    impl crate::Marker for Inner {}
    a[Cell(Inner).d(x)]
}

// ── The lower bound and the constant set, through trait defaults: `den` returns
// `g` (g = 0) and `k` returns 0, where the overrides return `g.max(1)` and `{1, 2}`.
pub trait TrLow {
    fn den(&self, g: u32) -> u32 {
        g
    }
    fn k(&self, _c: bool) -> u32 {
        0
    }
}

impl<X: Marker> TrLow for Holder<X> {}

pub mod Low {
    pub struct Inner;
}

impl TrLow for Holder<Low::Inner> {
    #[inline(never)]
    fn den(&self, g: u32) -> u32 {
        g.max(1)
    }
    #[inline(never)]
    fn k(&self, c: bool) -> u32 {
        if c { 1 } else { 2 }
    }
}

#[inline(never)]
pub fn Low(h: u32, g: u32) -> u32 { //~ ERROR strict verification failed for `summary_needs_the_summarized_body_refused::Low#ns0v`
    struct Inner;
    impl crate::Marker for Inner {}
    h % Holder(Inner).den(g)
}

pub mod Kst {
    pub struct Inner;
}

impl TrLow for Holder<Kst::Inner> {
    #[inline(never)]
    fn den(&self, g: u32) -> u32 {
        g
    }
    #[inline(never)]
    fn k(&self, c: bool) -> u32 {
        if c { 1 } else { 2 }
    }
}

#[inline(never)]
pub fn Kst(h: u32, c: bool) -> u32 { //~ ERROR strict verification failed for `summary_needs_the_summarized_body_refused::Kst#ns0v`
    struct Inner;
    impl crate::Marker for Inner {}
    h / Holder(Inner).k(c)
}

// ── The trivial setter, through a trait default: the default stores 0, the override
// stores `v`. v = 5. The assertion stays a runtime check (a warning), as it must.
pub trait TrSet {
    fn set(&self, p: &mut u32, _v: u32) {
        *p = 0;
    }
}

impl<X: Marker> TrSet for Holder<X> {}

pub mod Set {
    pub struct Inner;
}

impl TrSet for Holder<Set::Inner> {
    #[inline(never)]
    fn set(&self, p: &mut u32, v: u32) {
        *p = v;
    }
}

#[inline(never)]
pub fn Set(v: u32) -> u32 { //~ WARN safety verification incomplete for `summary_needs_the_summarized_body_refused::Set#ns0v`
    struct Inner;
    impl crate::Marker for Inner {}
    let mut a = 7u32;
    Holder(Inner).set(&mut a, v);
    assert!(a == v);
    a
}
