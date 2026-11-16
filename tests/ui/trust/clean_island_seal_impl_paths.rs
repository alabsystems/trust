//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_paths.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! `Trust.Protocol.Seal`: a `trusts` entry names one item. A method of a trait impl
//! whose own type is not a struct, enum or union (a blanket `impl<T> Reset for T`,
//! an `impl<T> Shuffle for [T]`) is named with its trait, `coll::Reset::reset`, not
//! by its module alone, where a free fn of the same name is (review 5 of the
//! review-14 build: the entry `coll::reset`, for a free fn that only measures, also
//! trusted the blanket `reset` that overwrites a holder). The entry for the free fn
//! covers it alone (`blanket_beside_free_fn`), and `coll::Touch::touch` does not
//! cover `Shuffle::touch` (`slice_beside_blanket`). Each refused at the other.

#![allow(unused)]

extern crate seal_dep_paths;

pub mod blanket_beside_free_fn {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    impl Default for App { fn default() -> Self { App::new() } }
    pub fn wipe(a: &mut App) -> usize { use seal_dep_paths::coll::Reset; let n = seal_dep_paths::coll::reset(a); a.reset(); n } //~ NOTE this runs `seal_dep_paths::coll::Reset::reset`, a fn of another crate, at the type
}

pub mod slice_beside_blanket {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub fn shuffle(v: &mut [App]) -> usize { use seal_dep_paths::coll::{Shuffle, Touch}; let n = Touch::touch(&mut v[0]); n + Shuffle::touch(v) } //~ NOTE this runs `seal_dep_paths::coll::Shuffle::touch`, a fn of another crate, at the type
}

clean {
    import Trust.Binding
    namespace ImplPaths
    open Trust.Protocol
    def blanket_beside_free_fn : Trust.Protocol.Seal := seals "blanket_beside_free_fn::Cell" ["blanket_beside_free_fn::Cell::bump"] ["blanket_beside_free_fn::Cell::new"] ["blanket_beside_free_fn::App::new"] ["coll::reset"]
    def slice_beside_blanket : Trust.Protocol.Seal := seals "slice_beside_blanket::Cell" ["slice_beside_blanket::Cell::bump"] ["slice_beside_blanket::Cell::new"] ["slice_beside_blanket::App::new"] ["coll::Touch::touch"]
    end ImplPaths
}
//~^^^^ ERROR seal `ImplPaths.blanket_beside_free_fn` on `Cell` does not hold
//~^^^^ ERROR seal `ImplPaths.slice_beside_blanket` on `Cell` does not hold
