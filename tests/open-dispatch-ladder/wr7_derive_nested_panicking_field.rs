//@ trust-ladder: refuses
//@ trust-ladder-row: strict verification failed for `<wr7_derive_nested_panicking_field::Outer as core::fmt::Debug>::fmt`
//! D1 increment 2 (2026-09-25) RAIL. The derived `Outer`'s nested formatter
//! reaches `Inner::fmt`, which panics on one value: it passes neither the
//! absolute nor the writer-relative bar, so the nested site is refused and
//! `Outer` with it. Runtime truth (verification off): `format!("{:?}",
//! Outer(Inner(7)))` exits 101. Measured BEFORE on the stage-1 snapshot
//! `43b8fe6ab`: refuses, needle present.
use core::fmt;
pub struct Inner(pub u32);
impl fmt::Debug for Inner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 == 7 { panic!("seven") }
        f.write_str("i")
    }
}
#[derive(Debug)]
pub struct Outer(pub Inner);
