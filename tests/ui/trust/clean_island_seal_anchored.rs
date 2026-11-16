//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_a.rs
//@ aux-build: seal_dep_b.rs
//@ aux-crate: hashbrown=seal_anchor/hashbrown.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The twin of `clean_island_seal_anchored_holds.rs` (`Trust.Protocol.Seal`):
//! the same programs with the entries UNANCHORED. Each entry names two items
//! and each seal must FAIL, and the error must suggest an entry that names
//! each item alone, where one exists (review 2 of the review-14 build: it
//! suggested the ambiguous entry again, for both).

#![allow(unused)]

extern crate seal_dep_a;
extern crate seal_dep_b;

mod suffix {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> u32 {
        let mut v: Vec<App> = Vec::with_capacity(4);
        seal_dep_b::keep(&mut v, App::new());
        seal_dep_a::seal_dep_b::keep(&mut v, App::new());
        v[0].cell.bump();
        v[0].cell.get()
    }
}

mod hashed {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> usize {
        let mut a: std::collections::HashMap<u32, App> = std::collections::HashMap::new();
        a.insert(1, App::new());
        let mut b: hashbrown::HashMap<u32, App> = hashbrown::HashMap::new();
        b.insert(1, App::new());
        a.len() + b.len()
    }
}

fn main() {
    suffix::run();
    hashed::run();
}

clean {
    import Trust.Binding
    namespace Anchored
    open Trust.Protocol
    def suffix : Trust.Protocol.Seal := seals "suffix::Cell" ["suffix::Cell::bump"] ["suffix::Cell::new"] ["suffix::App::new"] ["seal_dep_b::keep", "seal_dep_a::seal_dep_b::keep", "Vec::with_capacity", "Vec::index_mut", "Vec::index", "Vec::drop", "RawVec::drop"]
    def hashed : Trust.Protocol.Seal := seals "hashed::Cell" ["hashed::Cell::bump"] ["hashed::Cell::new"] ["hashed::App::new"] ["RawTable::drop", "RawVec::drop", "Vec::drop", "hash::map::HashMap::insert", "hash::map::HashMap::len", "hashbrown::map::HashMap::insert", "hashbrown::map::HashMap::len"]
    end Anchored
}
//~^^^^ ERROR seal `Anchored.suffix` on `Cell` does not hold
//~| NOTE tells them apart (`seal_dep_a::seal_dep_b::keep` and `::seal_dep_b::keep`)
//~^^^^^ ERROR seal `Anchored.hashed` on `Cell` does not hold
//~| NOTE its `trusts` entry `hashbrown::map::HashMap::insert` names 2 items
