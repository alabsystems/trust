//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! A `#[derive(Ord)]` enum's `cmp` does not reach its `_ => unreachable` arm
//! (TRUST-09).
//!
//! `Utf8Sequence` is regex-syntax 0.8.10's (`src/utf8.rs`), its `Utf8Range`
//! reduced to the two fields the derive compares. Its derived `cmp` was reported
//!
//!     [unreach] FAILED (ay-in-process); counterexample: _10 = 1, _12 = 0, _3 = 0, _4 = 0, …
//!
//! The derive compares the two discriminants with `<isize as Ord>::cmp` and, on
//! `Equal`, re-reads them through `(self, other)` — after that call. The re-reads
//! were tied to the first reads only before any call, so the counterexample read
//! `disc(*self)` as 0 before the call and as 1 after it. `self` and `other` are
//! the function's own `&Utf8Sequence` parameters, protected for the whole call,
//! and the enum holds no `UnsafeCell`: no execution changes the discriminant.
//!
//! THE STRICT BUILD IS THE ASSERTION: a refuted row fails this file, while a row
//! that keeps rustc's runtime check is reported and tolerated, which is why
//! warnings are allowed. The fail-closed half — an `UnsafeCell` in the pointee,
//! a `&mut` or reassigned parameter, a local shared borrow, an unsafe, foreign,
//! atomic or opaque barrier — is pinned in trust-vcgen (`src/tests.rs`,
//! `unfrozen_or_unprotected_discriminants_are_not_tied_after_a_call`, and
//! `tests/derived_ord_cmp_realmir.rs`).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Utf8Range {
    pub start: u8,
    pub end: u8,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Utf8Sequence {
    One(Utf8Range),
    Two([Utf8Range; 2]),
    Three([Utf8Range; 3]),
    Four([Utf8Range; 4]),
}
