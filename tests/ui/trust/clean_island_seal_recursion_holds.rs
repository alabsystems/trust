//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_doubling.rs`: recursion in a fn nothing
//! calls that does NOT grow its type at each step HOLDS
//! (`Trust.Protocol.Seal`): a fn that calls itself at the same type, and a
//! generic one that calls itself at its own parameter.

#![allow(unused)]

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
    fn get(&self) -> u32 { self.n }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }

fn same(x: (u8, u8), n: u32) -> u32 {
    if n == 0 { x.0 as u32 } else { same((x.1, x.0), n - 1) }
}
fn kept<T: Default + Clone>(x: T, n: u32) -> u32 {
    if n == 0 { 0 } else { kept(x.clone(), n - 1) }
}
fn unused() -> u32 {
    same((0, 1), 3) + kept((0u8, 0u8), 3)
}

fn main() {
    let mut app = App::new();
    app.cell.bump();
    println!("{}", app.cell.get());
}

clean {
    import Trust.Binding
    namespace RecursionHolds
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end RecursionHolds
}
