//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_rawok.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! An `unsafe impl` of a trait of ANOTHER crate for a type that holds a sealed
//! value (`Trust.Protocol.Seal`), with the trait named in `trusts`: the seal
//! HOLDS, on the author's word that what the trait promises lets no code build
//! or change a sealed value, as the conditions say ("whatever the impl is
//! for"). Review 4 of the review-14 build found it refused with no entry to
//! answer it (the rule for an `unsafe impl` of a trait of this crate ran too).
//! The twin (`_foreign_impl.rs`) names no entry.

#![allow(unused)]

extern crate seal_dep_rawok;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell, k: u8 }
unsafe impl seal_dep_rawok::RawOk for App {}
impl App { fn new() -> Self { App { cell: Cell::new(), k: 0 } } }
fn main() { let mut a = App::new(); a.cell.bump(); }

clean {
    import Trust.Binding
    namespace ForeignImpl
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] ["seal_dep_rawok::RawOk"]
    end ForeignImpl
}
