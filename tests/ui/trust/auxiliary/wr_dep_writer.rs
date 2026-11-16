//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! D1 increment 1 rails: a dependency compiled with verification OFF, the way
//! Targo compiles every dependency unit. Nothing here is checked by Trust.
//!
//! `F` is a `fmt::Write` whose `write_str` panics: a writer a formatting impl can
//! be handed OUTSIDE any std sink (`Formatter::new(&mut dep::F, ..)`), which is
//! exactly what the writer-relative premise does not cover. `boom` is a plain
//! verify-off function that panics on one input, the masked-source shape.
use std::fmt;

pub struct F;

impl fmt::Write for F {
    fn write_str(&mut self, _s: &str) -> fmt::Result {
        panic!("DEPENDENCY WRITER PANIC (unverified crate)")
    }
}

pub fn boom(x: u8) -> u8 {
    if x == 3 {
        panic!("DEP BOOM (unverified crate)")
    }
    x
}
