//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! Polymorphic recursion whose type DOUBLES at each step (`(T, T)`), in a
//! fn nothing calls (`Trust.Protocol.Seal`). The compiler never makes these
//! instances, and builds the program at once; the check reads every body,
//! and stops, refusing every seal of the crate, at a type of more than
//! 4,194,304 parts as the compiler walks it, within about a second. Review
//! 1 of the review-14 build: it ran for minutes, in the compiler's own walk
//! of what such a type's drop runs (part by part, where the type shares its
//! parts), and never came back. (It refuses every seal: this file has one.
//! The same recursion over `Option<T>`, which grows by one part a step,
//! stops at the recursion limit: `clean_island_seal_limits.rs`.)

#![allow(unused)]

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
    fn get(&self) -> u32 { self.n }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }

fn grow<T: Default>(x: T, n: u32) -> u32 { //~ NOTE the crate names `grow`, at a type of more than 4194304 parts
    if n == 0 { 0 } else { grow((x, T::default()), n - 1) }
}
fn unused() -> u32 {
    grow(0u8, 3)
}

fn main() {
    let mut app = App::new();
    app.cell.bump();
    println!("{}", app.cell.get());
}

clean {
    import Trust.Binding
    namespace Doubling
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end Doubling
}
//~^^^ ERROR seal `Doubling.cell` on `Cell` does not hold
