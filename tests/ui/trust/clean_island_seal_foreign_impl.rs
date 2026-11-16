//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_rawok.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The twin of `clean_island_seal_foreign_impl_holds.rs`
//! (`Trust.Protocol.Seal`): the same `unsafe impl` of a dependency's trait for a
//! holder, and no `trusts` entry: the seal must FAIL at the impl, and the note
//! asks for the trait. A refusal of every seal of the crate: a file of its
//! own.

#![allow(unused)]

extern crate seal_dep_rawok;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell, k: u8 }
unsafe impl seal_dep_rawok::RawOk for App {} //~ NOTE this is an `unsafe impl` of `seal_dep_rawok::RawOk`, a trait of another crate, for `App`: it promises that
impl App { fn new() -> Self { App { cell: Cell::new(), k: 0 } } }
fn main() { let mut a = App::new(); a.cell.bump(); }

clean {
    import Trust.Binding
    namespace ForeignImpl
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end ForeignImpl
}
//~^^^^ ERROR seal `ForeignImpl.cell` on `Cell` does not hold
