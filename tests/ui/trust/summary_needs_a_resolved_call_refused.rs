//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! A summary derived from a blanket impl's body describes calls that REACH that
//! body, not a generic dispatch whose rendering happens to match its def path. Each
//! caller panics for `T = Foo`.
//!
//! MEASURED FALSE PROOFS, 2026-09-30 (a review of the callee summaries): the return
//! bound, lower bound and constant set of `impl<T: Marker> Tr for T` are keyed by
//! `<T as krate::Tr>::m`, and the unresolvable `t.m(x)` inside `fn f<T: Tr>` renders
//! the same string. With `Tr::m` `#[trust::panic_free]` (so the call's own row is
//! discharged), `a[t.m(x)]`, `h % t.d(g)` and `h / t.k(c)` were PROVED and
//! kernel-certified. `summary_applies_to_a_resolved_call.rs` is the twin.

pub trait Marker {}

trait Tr {
    #[trust::panic_free]
    fn m(&self, x: usize) -> usize;
}

impl<T: Marker> Tr for T {
    #[inline(never)]
    fn m(&self, x: usize) -> usize {
        x.min(3)
    }
}

trait Den {
    #[trust::panic_free]
    fn d(&self, g: u32) -> u32;
}

impl<T: Marker> Den for T {
    #[inline(never)]
    fn d(&self, g: u32) -> u32 {
        g.max(1)
    }
}

trait Konst {
    #[trust::panic_free]
    fn k(&self, c: bool) -> u32;
}

impl<T: Marker> Konst for T {
    #[inline(never)]
    fn k(&self, c: bool) -> u32 {
        if c { 1 } else { 2 }
    }
}

pub struct Foo;

impl Tr for Foo {
    #[inline(never)]
    fn m(&self, x: usize) -> usize {
        x
    }
}

impl Den for Foo {
    #[inline(never)]
    fn d(&self, g: u32) -> u32 {
        g
    }
}

impl Konst for Foo {
    #[inline(never)]
    fn k(&self, _c: bool) -> u32 {
        0
    }
}

// T = Foo, x = 10.
#[inline(never)]
fn upper_bound<T: Tr>(t: &T, x: usize, a: &[u8; 4]) -> u8 { //~ ERROR failed for `summary_needs_a_resolved_call_refused::upper_bound`
    a[t.m(x)]
}

// T = Foo, g = 0.
#[inline(never)]
fn lower_bound<T: Den>(t: &T, h: u32, g: u32) -> u32 { //~ ERROR failed for `summary_needs_a_resolved_call_refused::lower_bound`
    h % t.d(g)
}

// T = Foo.
#[inline(never)]
fn constant_set<T: Konst>(t: &T, h: u32, c: bool) -> u32 { //~ ERROR failed for `summary_needs_a_resolved_call_refused::constant_set`
    h / t.k(c)
}

pub fn run(x: usize, g: u32, c: bool) -> u32 {
    let a = [0u8; 4];
    upper_bound(&Foo, x, &a) as u32 + lower_bound(&Foo, 7, g) + constant_set(&Foo, 7, c)
}
