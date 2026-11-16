//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_inlined.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! A fn of an optimized dependency with no `unsafe` of its own, run where
//! it handles `&mut` pointers to holders, HOLDS with no trust
//! (`Trust.Protocol.Seal`): the code std's safe `slice::iter` left in it,
//! inlined, is std's, read by its shape as when the dependency calls it
//! (built without optimization). Review 1 of the review-14 build: the
//! pointer cast of std's code was laid to the dependency's fn, as if that
//! fn did what only `unsafe` code can, and the seal was refused in the
//! optimized build only. (`_inlined_std.rs`: an `unsafe fn` of std inlined
//! there is the dependency's own `unsafe`, and is refused.)

#![allow(unused)]

extern crate seal_dep_inlined;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
    fn get(&self) -> u32 { self.n }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }

fn main() {
    let mut a = App::new();
    let mut b = App::new();
    let mut refs: Vec<&mut App> = Vec::new();
    refs.push(&mut a);
    refs.push(&mut b);
    for r in refs.iter_mut() {
        r.cell.bump();
    }
    println!("{}", seal_dep_inlined::count(&refs));
    println!("{}", a.cell.get() + b.cell.get());
}

clean {
    import Trust.Binding
    namespace InlinedStdHolds
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end InlinedStdHolds
}
