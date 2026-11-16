//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The twin of `clean_island_seal_impossible.rs`: the same fns where the
//! bound CAN hold (`&mut u8: Tr` is implemented) are read, and the seal must
//! FAIL at the swap (`Trust.Protocol.Seal`). Only a bound that holds for no
//! lifetime keeps a body from being read.

#![allow(unused)]

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
    fn get(&self) -> u32 { self.n }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }

trait Tr {
    type Out;
    fn m(&self) -> u32;
}
impl Tr for &mut u8 {
    type Out = u8;
    fn m(&self) -> u32 { 0 }
}
struct W<T: Tr>(T);
impl<T: Tr> Drop for W<T> {
    fn drop(&mut self) {
        let _ = self.0.m();
    }
}

fn dropped<'a>(x: &'a mut u8) where &'a mut u8: Tr {
    let w = W(x);
    let _ = &w;
}

fn swapped<'a, T>(a: &'a mut App, b: &'a mut App, _t: T) where &'a mut u8: Tr {
    std::mem::swap(a, b); //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `App`
}

fn main() {
    let mut app = App::new();
    app.cell.bump();
    println!("{}", app.cell.get());
}

clean {
    import Trust.Binding
    namespace ImpossibleBroken
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end ImpossibleBroken
}
//~^^^ ERROR seal `ImpossibleBroken.cell` on `Cell` does not hold
