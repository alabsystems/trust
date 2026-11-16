//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_visit.rs
//@ aux-build: seal_dep_tidy.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_third.rs`: the same trusts HOLD where the
//! code the trusted fn runs unchosen is this crate's own, which is read as
//! its own wherever it is called (`Trust.Protocol.Seal`).
//!
//! - `provided`: this crate's impl overrides `Settle::settle` with a body
//!   that swaps nothing.
//! - `driven`: `seal_dep_tidy::run` drives a visitor of this crate, whose
//!   `visit` changes the cell only through its writer; B's `drive`, which
//!   A's `run` calls by name, is covered by the trust of `run`.

#![allow(unused)]

extern crate seal_dep_tidy;
extern crate seal_dep_visit;

mod provided {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    impl seal_dep_visit::Settle for App {
        fn settle(a: &mut Self, b: &mut Self) {
            println!("{} {}", a.cell.get(), b.cell.get());
        }
    }
    pub fn run() {
        let mut a = App::new();
        a.cell.bump();
        let mut b = App::new();
        seal_dep_tidy::tidy(&mut a, &mut b);
    }
}

mod driven {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub struct Visitor { app: App }
    impl seal_dep_visit::Visit for Visitor {
        fn visit(&mut self) {
            self.app.cell.bump();
        }
    }
    pub fn run() {
        let mut visitor = Visitor { app: App::new() };
        seal_dep_tidy::run(&mut visitor);
    }
}

fn main() {
    provided::run();
    driven::run();
}

clean {
    import Trust.Binding
    namespace ThirdHolds
    open Trust.Protocol
    def provided : Trust.Protocol.Seal := seals "provided::Cell" ["provided::Cell::bump"] ["provided::Cell::new"] ["provided::App::new"] ["seal_dep_tidy::tidy"]
    def driven : Trust.Protocol.Seal := seals "driven::Cell" ["driven::Cell::bump"] ["driven::Cell::new"] ["driven::App::new"] ["seal_dep_tidy::run"]
    end ThirdHolds
}
