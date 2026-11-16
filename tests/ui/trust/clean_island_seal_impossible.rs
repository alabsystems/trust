//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Fns whose where-clauses hold for no lifetime, so that nothing can call
//! them, beside a seal that HOLDS (`Trust.Protocol.Seal`). The compiler
//! makes nothing such a fn names; the check reads it for (C) only where its
//! bounds can hold. Review 1 of the review-14 build: read where they stand,
//! `dropped` led the compiler to a panic (the drop glue of `W<&mut u8>`,
//! whose `Drop` impl needs `&mut u8: Tr`), `projected` refused every seal of
//! the crate at an alias nothing settles, and `swapped` would have been
//! refused for a swap that can never run.
//!
//! The same fns where the bound CAN hold are read: `_impossible_broken.rs`.

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

fn dropped_by_std<'a>(x: &'a mut u8) where &'a mut u8: Tr {
    std::mem::drop(W(x));
}

fn projected<'a>(x: <&'a mut u8 as Tr>::Out) where &'a mut u8: Tr {
    let _y = x;
}

fn swapped<'a, T>(a: &'a mut App, b: &'a mut App, _t: T) where &'a mut u8: Tr {
    std::mem::swap(a, b);
}

fn main() {
    let mut app = App::new();
    app.cell.bump();
    println!("{}", app.cell.get());
}

clean {
    import Trust.Binding
    namespace Impossible
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end Impossible
}
