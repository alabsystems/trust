//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_pod_one.rs
//@ aux-build: seal_dep_pod_two.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! What the crate's shape asks a `trusts` entry for, an entry that works
//! (`Trust.Protocol.Seal`): the seal must FAIL, and each note must ask for an
//! entry that names its trait alone. Review 2 of the review-14 build: the
//! notes for two `unsafe impl`s of two crates' `marker::Pod` were written
//! before either trait was noted as relied on, and each asked for
//! `marker::Pod`, an entry that names both.
//!
//! With the entries the notes ask for: `_shape_entries_holds.rs`.

#![allow(unused)]

extern crate seal_dep_pod_one;
extern crate seal_dep_pod_two;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }
#[derive(Clone, Copy)]
struct Vertex { x: f32 }
#[derive(Clone, Copy)]
struct Index { i: u32 }
unsafe impl seal_dep_pod_one::marker::Pod for Vertex {} //~ NOTE name the trait in the seal's `trusts`: `seal_dep_pod_one::marker::Pod`
unsafe impl seal_dep_pod_two::marker::Pod for Index {} //~ NOTE name the trait in the seal's `trusts`: `seal_dep_pod_two::marker::Pod`

fn main() {
    let mut a = App::new();
    a.cell.bump();
}

clean {
    import Trust.Binding
    namespace ShapeEntries
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end ShapeEntries
}
//~^^^ ERROR seal `ShapeEntries.cell` on `Cell` does not hold
