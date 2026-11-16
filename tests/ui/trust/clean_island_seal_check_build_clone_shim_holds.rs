//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_bodies_built.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_check_build_clone_shim.rs`: the same
//! program against the same dependency built in full, whose bodies the
//! collector lists and the check reads, HOLDS (`Trust.Protocol.Seal`):
//! nothing writes a `Cell` but `Cell::bump`. The refusal of its twin is that
//! one unread body, not every check build.

#![allow(unused)]

extern crate seal_dep_bodies_built;

use std::marker::PhantomData;

use seal_dep_bodies_built::Tag;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }

/// A type of this crate that owns no `Cell`, as aterm's `Wake` owns none.
pub struct Wake { id: u32 }

fn main() {
    let mut a = App::new();
    a.cell.bump();
    let pair = (Tag::<Wake> { n: 1, of: PhantomData }, 2u8);
    let copy = pair.clone();
    let _ = copy.0.n;
}

clean {
    import Trust.Binding
    namespace CheckBuildCloneShimHolds
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end CheckBuildCloneShimHolds
}
//~^^^ NOTE seal `CheckBuildCloneShimHolds.cell` holds
