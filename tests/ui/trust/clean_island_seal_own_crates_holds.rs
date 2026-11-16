//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_own_drive.rs
//@ aux-build: seal_dep_own_pair.rs
//@ aux-build: seal_dep_own_visit.rs
//@ aux-build: seal_dep_own_run.rs
//@ aux-build: seal_dep_own_run0.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! A trait impl's method of a crate outside the standard library, which the
//! fn running it did not choose, is covered by the trusts that name a fn OF
//! ITS CRATE anywhere on the way to it (`Trust.Protocol.Seal`): each seal
//! HOLDS. Review 2 of the review-14 build found both refused:
//!
//! - `stint`: crate A's trusted `run` calls crate B's trusted `drive`, which
//!   runs A's own impl method (it only measures). Entering B forgot what
//!   named A's fns.
//! - `inlined`, `unoptimized`: crate A's trusted `run` calls crate B's
//!   trusted `drive`, which runs B's own impl method. With A built with
//!   optimization `drive` is inlined into `run`, and what its code names was
//!   read on A's way, without B's trust: the verdict turned on A's profile.
//!
//! With the trust of the impl's own crate left out: `_own_crates.rs`.

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
        seal_dep_own_pair::run(&mut a, &mut b)
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
        seal_dep_own_run::run(&mut a, &mut b)
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
        seal_dep_own_run0::run(&mut a, &mut b)
    }
}

fn main() {
    stint::run();
    inlined::run();
    unoptimized::run();
}

clean {
    import Trust.Binding
    namespace OwnCratesHold
    open Trust.Protocol
    def stint : Trust.Protocol.Seal := seals "stint::Cell" ["stint::Cell::bump"] ["stint::Cell::new"] ["stint::App::new"] ["seal_dep_own_pair::run", "seal_dep_own_drive::drive"]
    def inlined : Trust.Protocol.Seal := seals "inlined::Cell" ["inlined::Cell::bump"] ["inlined::Cell::new"] ["inlined::App::new"] ["seal_dep_own_run::run", "seal_dep_own_visit::drive"]
    def unoptimized : Trust.Protocol.Seal := seals "unoptimized::Cell" ["unoptimized::Cell::bump"] ["unoptimized::Cell::new"] ["unoptimized::App::new"] ["seal_dep_own_run0::run", "seal_dep_own_visit::drive"]
    end OwnCratesHold
}
