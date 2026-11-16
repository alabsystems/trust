//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_tag.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A dependency's closure made a `dyn` in its own crate's code, and handed
//! a pointer to a holder (`Trust.Protocol.Seal`): the trusted
//! `seal_dep_tag::each_dyn` makes a `&dyn Fn(&mut T)` of its own closure and
//! calls it itself. A closure behind a `dyn` runs wherever the `dyn` is
//! called, on what its caller hands it, which the check does not follow, and
//! no `trusts` entry names a closure: the seal must FAIL (a listed cost), and
//! the note says that no entry covers it. Review 3 of the review-14 build:
//! the note promised that a trust of a fn of its own crate that runs it
//! covers it, and that fn was trusted. (The same closure called directly:
//! `_dyn_closure_holds.rs`.)

#![allow(unused)]

extern crate seal_dep_tag;

mod dyn_closure {
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
        let mut v = apps(); seal_dep_tag::each_dyn(&mut v) as u32 //~ NOTE no `trusts` entry covers it: an entry names no closure
    }
}

fn main() {
    println!("{}", dyn_closure::run());
}

clean {
    import Trust.Binding
    namespace DynClosure
    open Trust.Protocol
    def dyn_closure : Trust.Protocol.Seal := seals "dyn_closure::Cell" ["dyn_closure::Cell::bump"] ["dyn_closure::Cell::new"] ["dyn_closure::App::new"] ["seal_dep_tag::each_dyn", "seal_dep_tag::touch", "vec::Vec::push", "vec::Vec::len", "vec::Vec::drop", "RawVec::drop", "vec::Vec::new", "slice::iter_mut", "IterMut::next", "collect::into_iter", "vec::Vec::deref_mut"]
    end DynClosure
}
//~^^^ ERROR seal `DynClosure.dyn_closure` on `Cell` does not hold
