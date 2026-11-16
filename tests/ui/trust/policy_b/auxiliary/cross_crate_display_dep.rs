//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit. `D`'s `Display::fmt` PANICS for `D(1)`. Its `fmt` is never
//! verified (verify-off → no obligation) and is reached only INDIRECTLY through
//! the print machinery inside `_print`, so there is no direct Call in the caller
//! and no bundled obligation. It exists so the caller fixture can prove that a
//! value formatted through a cross-crate user `Display`/`Debug` cannot ride the
//! std print-backend completeness gap.
// `std::fmt`, not `core::fmt`: this aux is compiled at the ui suite's default
// edition, where a bare `use core::…` needs an `extern crate core;` and fails
// E0432 "unresolved import `core`" without one. `std::fmt` IS `core::fmt`
// re-exported, so the `Display` impl below — and the panic the caller fixtures
// are built to catch — are byte-for-byte the same.
use std::fmt;
pub struct D(pub i32);
impl fmt::Display for D {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 == 1 {
            panic!("cross-crate boom");
        }
        write!(f, "{}", self.0)
    }
}
