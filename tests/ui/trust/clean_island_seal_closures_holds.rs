//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Long chains of closures in live code that never recurses HOLD
//! (`Trust.Protocol.Seal`). Review 2 of the review-14 build: each of these
//! refused every seal of the crate, "at a type of more than 4194304 parts":
//! the count of a closure's parts took its signature and the generic
//! arguments of the fn it is in as well as what it captures, std's `fold`
//! wraps each adaptor's closure in a closure that names and captures it, and
//! the count doubled at each adaptor. A closure is counted by what it
//! captures, as the compiler's own walks read one.
//!
//! - `chained`: one chain of 20 `filter`/`map` adaptors, summed.
//! - `wrapped`: 24 nested generic closure wrappers.
//! - `staged`: four nested calls of a generic fn of four adaptors.
//!
//! With a closure in the chain that swaps two holders: `_closures.rs`.

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
        app.cell.bump();
        (0..app.cell.get() * 100).filter(|x| x % 2 != 0).map(|x| x + 2).filter(|x| x % 4 != 0).map(|x| x + 4).filter(|x| x % 6 != 0).map(|x| x + 6).filter(|x| x % 8 != 0).map(|x| x + 8).filter(|x| x % 10 != 0).map(|x| x + 10).filter(|x| x % 12 != 0).map(|x| x + 12).filter(|x| x % 14 != 0).map(|x| x + 14).filter(|x| x % 16 != 0).map(|x| x + 16).filter(|x| x % 18 != 0).map(|x| x + 18).filter(|x| x % 20 != 0).map(|x| x + 20).sum()
    }
}

mod wrapped {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    fn wrap<F: Fn() -> u32>(f: F) -> impl Fn() -> u32 { move || f() + 1 }
    pub fn run() -> u32 {
        let mut app = App::new();
        app.cell.bump();
        let w = || app.cell.get();
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        let w = wrap(w);
        w()
    }
}

mod staged {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    fn stage<I: Iterator<Item = u32>>(it: I) -> impl Iterator<Item = u32> {
        it.map(|x| x + 1).filter(|x| x % 3 != 0).map(|x| x * 2).take_while(|x| *x < 1_000_000)
    }
    pub fn run() -> u32 {
        let mut app = App::new();
        app.cell.bump();
        stage(stage(stage(stage(0..app.cell.get() * 10)))).sum()
    }
}

fn main() {
    chained::run();
    wrapped::run();
    staged::run();
}

clean {
    import Trust.Binding
    namespace ClosuresHold
    open Trust.Protocol
    def chained : Trust.Protocol.Seal := seals "chained::Cell" ["chained::Cell::bump"] ["chained::Cell::new"] ["chained::App::new"] []
    def wrapped : Trust.Protocol.Seal := seals "wrapped::Cell" ["wrapped::Cell::bump"] ["wrapped::Cell::new"] ["wrapped::App::new"] []
    def staged : Trust.Protocol.Seal := seals "staged::Cell" ["staged::Cell::bump"] ["staged::Cell::new"] ["staged::App::new"] []
    end ClosuresHold
}
