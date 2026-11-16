//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_stack.rs
//@ aux-build: seal_dep_measure.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_standing.rs` (`Trust.Protocol.Seal`): the
//! same library with entries that each name ONE item HOLDS; `churn` calls
//! the measuring crate's `util::keep`.

#![allow(unused)]

extern crate seal_dep_measure;
extern crate seal_dep_stack;

pub mod pushed {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub fn keep(v: &mut Vec<App>, a: App) { v.push(a) }
    pub fn put<T>(v: &mut seal_dep_stack::stack::Vec<(T, App)>, x: (T, App)) { v.push(x) }
}

pub mod kept {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub fn measure() -> usize {
        let (mut x, mut y) = (App::new(), App::new());
        seal_dep_measure::util::keep(&mut x, &mut y)
    }
    pub fn churn<T>(a: &mut (T, App), b: &mut (T, App)) -> usize { seal_dep_measure::util::keep(a, b) }
}

clean {
    import Trust.Binding
    namespace StandingHold
    open Trust.Protocol
    def pushed : Trust.Protocol.Seal := seals "pushed::Cell" ["pushed::Cell::bump"] ["pushed::Cell::new"] ["pushed::App::new"] ["vec::Vec::push", "stack::Vec::push"]
    def kept : Trust.Protocol.Seal := seals "kept::Cell" ["kept::Cell::bump"] ["kept::Cell::new"] ["kept::App::new"] ["seal_dep_measure::util::keep"]
    end StandingHold
}
