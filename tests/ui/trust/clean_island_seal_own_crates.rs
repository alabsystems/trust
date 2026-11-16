//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_own_drive.rs
//@ aux-build: seal_dep_own_pair.rs
//@ aux-build: seal_dep_own_visit.rs
//@ aux-build: seal_dep_own_run.rs
//@ aux-build: seal_dep_own_run0.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The twin of `clean_island_seal_own_crates_holds.rs` (`Trust.Protocol.Seal`):
//! the same ways, with a trust left out. Each seal must FAIL, in both
//! profiles of A: `stint` trusts only B's `drive`, and A's `run` is run at a
//! holder's type; `inlined` and `unoptimized` trust only A's `run`, which
//! covers B's `drive` (a fn it chose) but not B's impl method that `drive`
//! runs: a trust of a fn of one crate covers no impl of another, whether
//! `drive` was inlined into `run` or called.

#![allow(unused)]

extern crate seal_dep_own_drive;
extern crate seal_dep_own_pair;
extern crate seal_dep_own_run;
extern crate seal_dep_own_run0;
extern crate seal_dep_own_visit;

mod stint {
    use seal_dep_own_pair::Pair;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> usize {
        let mut a = Pair(App::new());
        let mut b = Pair(App::new());
        a.0.cell.bump();
        seal_dep_own_pair::run(&mut a, &mut b) //~ NOTE this runs `seal_dep_own_pair::run`, a fn of another crate, at the type `stint::App`
    }
}

mod inlined {
    use seal_dep_own_visit::Pair;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> usize {
        let mut a = Pair(App::new());
        let mut b = Pair(App::new());
        a.0.cell.bump();
        seal_dep_own_run::run(&mut a, &mut b) //~ NOTE this runs `seal_dep_own_visit::Pair::visit`, a fn of another crate, at the type `inlined::App`
    }
}

mod unoptimized {
    use seal_dep_own_visit::Pair;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> usize {
        let mut a = Pair(App::new());
        let mut b = Pair(App::new());
        a.0.cell.bump();
        seal_dep_own_run0::run(&mut a, &mut b) //~ NOTE this runs `seal_dep_own_visit::Pair::visit`, a fn of another crate, at the type `unoptimized::App`
    }
}

fn main() {
    stint::run();
    inlined::run();
    unoptimized::run();
}

clean {
    import Trust.Binding
    namespace OwnCrates
    open Trust.Protocol
    def stint : Trust.Protocol.Seal := seals "stint::Cell" ["stint::Cell::bump"] ["stint::Cell::new"] ["stint::App::new"] ["seal_dep_own_drive::drive"]
    def inlined : Trust.Protocol.Seal := seals "inlined::Cell" ["inlined::Cell::bump"] ["inlined::Cell::new"] ["inlined::App::new"] ["seal_dep_own_run::run"]
    def unoptimized : Trust.Protocol.Seal := seals "unoptimized::Cell" ["unoptimized::Cell::bump"] ["unoptimized::Cell::new"] ["unoptimized::App::new"] ["seal_dep_own_run0::run"]
    end OwnCrates
}
//~^^^^^ ERROR seal `OwnCrates.stint` on `Cell` does not hold
//~^^^^^ ERROR seal `OwnCrates.inlined` on `Cell` does not hold
//~^^^^^ ERROR seal `OwnCrates.unoptimized` on `Cell` does not hold
