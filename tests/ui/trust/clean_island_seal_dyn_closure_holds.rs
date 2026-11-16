//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_tag.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_dyn_closure.rs` (`Trust.Protocol.Seal`):
//! a dependency's closure that its trusted fn calls directly (`each_closure`,
//! `.map(|t| tag(t))`) is covered by the trust of that fn; a fn item it hands
//! to std's `map` by name (`.map(tag)`, `.map(Some)`) is a fn value, covered
//! by an entry that names it (`seal_dep_tag::tag`, `Some::Some`). Every seal
//! HOLDS.

#![allow(unused)]

extern crate seal_dep_tag;

mod plain_closure {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    fn apps() -> Vec<App> { let mut v = Vec::new(); v.push(App::new()); v }
    pub fn run() -> u32 {
        let mut a = App::new();
        a.cell.bump();
        let mut v = apps(); seal_dep_tag::each_closure(&mut v) as u32
    }
}

mod map_closures {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    fn apps() -> Vec<App> { let mut v = Vec::new(); v.push(App::new()); v }
    pub fn run() -> u32 {
        let mut a = App::new();
        a.cell.bump();
        seal_dep_tag::tag_all_closure(apps()).len() as u32 + seal_dep_tag::wrap_all_closure(apps()).len() as u32
    }
}

mod map_items {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    fn apps() -> Vec<App> { let mut v = Vec::new(); v.push(App::new()); v }
    pub fn run() -> u32 {
        let mut a = App::new();
        a.cell.bump();
        seal_dep_tag::tag_all_item(apps()).len() as u32 + seal_dep_tag::wrap_all_item(apps()).len() as u32
    }
}

fn main() {
    println!("{}", plain_closure::run());
    println!("{}", map_closures::run());
    println!("{}", map_items::run());
}

clean {
    import Trust.Binding
    namespace DynClosureHolds
    open Trust.Protocol
    def plain_closure : Trust.Protocol.Seal := seals "plain_closure::Cell" ["plain_closure::Cell::bump"] ["plain_closure::Cell::new"] ["plain_closure::App::new"] ["seal_dep_tag::each_closure", "vec::Vec::push", "vec::Vec::len", "vec::Vec::drop", "RawVec::drop", "vec::Vec::new", "slice::iter_mut", "IterMut::next", "collect::into_iter", "vec::Vec::deref_mut"]
    def map_closures : Trust.Protocol.Seal := seals "map_closures::Cell" ["map_closures::Cell::bump"] ["map_closures::Cell::new"] ["map_closures::App::new"] ["seal_dep_tag::tag_all_closure", "seal_dep_tag::wrap_all_closure", "vec::Vec::push", "vec::Vec::len", "vec::Vec::drop", "RawVec::drop", "vec::Vec::new", "slice::iter_mut", "IterMut::next", "collect::into_iter", "vec::Vec::deref_mut"]
    def map_items : Trust.Protocol.Seal := seals "map_items::Cell" ["map_items::Cell::bump"] ["map_items::Cell::new"] ["map_items::App::new"] ["seal_dep_tag::tag_all_item", "seal_dep_tag::wrap_all_item", "seal_dep_tag::tag", "Some::Some", "vec::Vec::push", "vec::Vec::len", "vec::Vec::drop", "RawVec::drop", "vec::Vec::new", "slice::iter_mut", "IterMut::next", "collect::into_iter", "vec::Vec::deref_mut"]
    end DynClosureHolds
}
