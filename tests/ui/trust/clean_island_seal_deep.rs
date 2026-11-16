//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! Polymorphic recursion that grows its type by one level a step, in a fn
//! nothing calls, in a crate that raises its recursion limit
//! (`Trust.Protocol.Seal`). The compiler never makes these instances and
//! builds the program; the check reads every body, and stops, refusing every
//! seal of the crate, at a type nested more than 512 deep. Review 2 of the
//! review-14 build: at `#![recursion_limit = "2048"]` the check read `grow`
//! down to the limit, and the compiler's own walks of a type some 1,600
//! levels deep ran out of stack (a crash, SIGBUS). (It refuses every seal:
//! this file has one. With no recursion the same limit holds:
//! `_deep_holds.rs`.)

#![allow(unused)]
#![recursion_limit = "2048"]

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
    fn get(&self) -> u32 { self.n }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }

fn grow<T: Clone + std::fmt::Debug>(x: T, n: u32) { //~ NOTE at a type nested more than 512 deep
    if n > 0 { grow(Some(x.clone()), n - 1) } else { println!("{:?}", x) }
}
fn unused() { grow(1u8, 3) }

fn main() {
    let mut a = App::new();
    a.cell.bump();
}

clean {
    import Trust.Binding
    namespace Deep
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end Deep
}
//~^^^ ERROR seal `Deep.cell` on `Cell` does not hold
