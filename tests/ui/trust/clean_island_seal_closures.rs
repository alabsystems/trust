//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The twin of `clean_island_seal_closures_holds.rs` (`Trust.Protocol.Seal`):
//! the same chain of 20 adaptors, whose last closure swaps two holders. The
//! seal must FAIL at the swap: a closure counted by what it captures is still
//! read, at every depth of the chain.

#![allow(unused)]

mod chained {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> u32 {
        let mut app = App::new();
        let mut other = App::new();
        app.cell.bump();
        let start = app.cell.get() * 100;
        (0..start).filter(|x| x % 2 != 0).map(|x| x + 2).filter(|x| x % 4 != 0).map(|x| x + 4).filter(|x| x % 6 != 0).map(|x| x + 6).filter(|x| x % 8 != 0).map(|x| x + 8).filter(|x| x % 10 != 0).map(|x| x + 10).filter(|x| x % 12 != 0).map(|x| x + 12).filter(|x| x % 14 != 0).map(|x| x + 14).filter(|x| x % 16 != 0).map(|x| x + 16).filter(|x| x % 18 != 0).map(|x| x + 18).filter(|x| x % 20 != 0).map(|x| { std::mem::swap(&mut app, &mut other); x + 20 }).sum() //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `App`
    }
}

fn main() {
    chained::run();
}

clean {
    import Trust.Binding
    namespace Closures
    open Trust.Protocol
    def chained : Trust.Protocol.Seal := seals "chained::Cell" ["chained::Cell::bump"] ["chained::Cell::new"] ["chained::App::new"] []
    end Closures
}
//~^^^ ERROR seal `Closures.chained` on `Cell` does not hold
