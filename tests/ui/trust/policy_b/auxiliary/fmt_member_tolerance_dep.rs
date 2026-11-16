//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit: nothing here carries a Trust verdict. Each impl panics on one
//! value, so a caller that reaches it through core's formatting machinery can be
//! shown to panic at run time (exit 101) while the caller's build succeeds.
//!
//! `std::fmt`, not `core::fmt`: at the ui suite's default edition a bare
//! `use core::…` needs an `extern crate core;`. `std::fmt` IS `core::fmt`.
use std::fmt;

/// `Debug` panics on `Inner(7)`. Reached from a caller only as a `&dyn Debug`
/// that core's builders (`DebugTuple::field`,
/// `Formatter::debug_tuple_field1_finish`) call through.
pub struct Inner(pub u32);
impl fmt::Debug for Inner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 == 7 {
            panic!("DEP DEBUG PANIC (unverified crate)")
        }
        f.write_str("i")
    }
}

/// A `fmt::Write` sink that panics on a 7-byte write. Reached from a caller only
/// as the `&mut dyn fmt::Write` that `core::fmt::write` writes through.
pub struct Sink;
impl fmt::Write for Sink {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if s.len() == 7 {
            panic!("DEP SINK PANIC (unverified crate)")
        }
        Ok(())
    }
}
