//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_paths.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_impl_paths.rs` (`Trust.Protocol.Seal`): each item
//! named by its own entry HOLDS: the free fn `coll::reset` (`free_fn_trusted`) and
//! the blanket `coll::Touch::touch` (`blanket_trusted`).

#![allow(unused)]

extern crate seal_dep_paths;

pub mod free_fn_trusted {
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
    pub fn measure(a: &mut App) -> usize { seal_dep_paths::coll::reset(a) }
}

pub mod blanket_trusted {
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
    pub fn measure(a: &mut App) -> usize { use seal_dep_paths::coll::Touch; a.touch() }
}

clean {
    import Trust.Binding
    namespace ImplPathsHolds
    open Trust.Protocol
    def free_fn_trusted : Trust.Protocol.Seal := seals "free_fn_trusted::Cell" ["free_fn_trusted::Cell::bump"] ["free_fn_trusted::Cell::new"] ["free_fn_trusted::App::new"] ["coll::reset"]
    def blanket_trusted : Trust.Protocol.Seal := seals "blanket_trusted::Cell" ["blanket_trusted::Cell::bump"] ["blanket_trusted::Cell::new"] ["blanket_trusted::App::new"] ["coll::Touch::touch"]
    end ImplPathsHolds
}
