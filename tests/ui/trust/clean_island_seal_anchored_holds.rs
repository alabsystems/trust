//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_a.rs
//@ aux-build: seal_dep_b.rs
//@ aux-crate: hashbrown=seal_anchor/hashbrown.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! A `trusts` entry anchored at its crate (`::seal_dep_b::keep`: `::`, the
//! crate's name in this crate, and the item's whole path there, as Rust's
//! own `::krate::path` names one) names that crate's item alone
//! (`Trust.Protocol.Seal`): each seal HOLDS. Review 2 of the review-14 build
//! found no entry that could name either item of a pair alone, and the seal
//! of a true program could never hold:
//!
//! - `suffix`: crate `seal_dep_b`'s `keep`, whose whole path ends the path
//!   of crate `seal_dep_a`'s `seal_dep_b::keep`.
//! - `hashed`: a std `HashMap` of holders beside a dependency named
//!   `hashbrown`, as crates.io's is: std's own map runs the standard
//!   library's own `hashbrown` crate's `insert` beneath its `insert`, at the
//!   same path as the dependency's. (`::hashbrown` names the crate this one
//!   calls `hashbrown`; the standard library's own is no crate it names.)
//!
//! With the entries unanchored: `_anchored.rs`.

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
    namespace AnchoredHold
    open Trust.Protocol
    def suffix : Trust.Protocol.Seal := seals "suffix::Cell" ["suffix::Cell::bump"] ["suffix::Cell::new"] ["suffix::App::new"] ["::seal_dep_b::keep", "seal_dep_a::seal_dep_b::keep", "Vec::with_capacity", "Vec::index_mut", "Vec::index", "Vec::drop", "RawVec::drop"]
    def hashed : Trust.Protocol.Seal := seals "hashed::Cell" ["hashed::Cell::bump"] ["hashed::Cell::new"] ["hashed::App::new"] ["RawTable::drop", "RawVec::drop", "Vec::drop", "hash::map::HashMap::insert", "hash::map::HashMap::len", "::hashbrown::map::HashMap::insert", "::hashbrown::map::HashMap::len"]
    end AnchoredHold
}
