//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_inlined.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The twin of `clean_island_seal_inlined_std_holds.rs`: a fn of an
//! optimized dependency that calls std's `unsafe fn Vec::set_len` where it
//! handles `&mut` pointers to holders must FAIL with no trust
//! (`Trust.Protocol.Seal`): the call was the dependency's own `unsafe`, and
//! is counted as such though the optimizer inlined it away to a plain write
//! of the length (built without optimization, it is a call of an `unsafe
//! fn`, and is refused the same way).

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
    seal_dep_inlined::forget_all(&mut refs); //~ NOTE this runs `seal_dep_inlined::forget_all`, a fn of a crate outside the standard library, which calls an `unsafe fn`
    println!("{}", a.cell.get() + b.cell.get());
}

clean {
    import Trust.Binding
    namespace InlinedStd
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end InlinedStd
}
//~^^^ ERROR seal `InlinedStd.cell` on `Cell` does not hold
