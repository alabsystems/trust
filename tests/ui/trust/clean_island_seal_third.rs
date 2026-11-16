//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_visit.rs
//@ aux-build: seal_dep_tidy.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A trust of crate A's fn does not cover code of crate B that A's code
//! runs without having chosen it (`Trust.Protocol.Seal`): each seal must
//! FAIL, at B's body. Review 1 of the review-14 build found both passing.
//!
//! - `provided`: the seal trusts `seal_dep_tidy::tidy` only. Beneath it,
//!   `seal_dep_visit`'s PROVIDED method `Settle::settle`, which this crate's
//!   impl does not override, swaps two holders: a trait's own method was
//!   not stripped of the trust, as an impl's method was.
//! - `driven`: the seal trusts `seal_dep_tidy::run` only, which calls
//!   `seal_dep_visit::drive`, which runs B's `impl Visit for Pair<T>` at
//!   `Pair<App>` (the impl the caller's type chose): it swaps two holders.
//!   The trusts that cover what B runs unchosen are the trusts naming a fn
//!   OF B; entering B kept A's too.
//!
//! With this crate's own impls in their place the same trusts hold:
//! `_third_holds.rs`.

#![allow(unused)]

extern crate seal_dep_tidy;
extern crate seal_dep_visit;

mod provided {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    impl seal_dep_visit::Settle for App {}
    pub fn run() {
        let mut a = App::new();
        a.cell.bump();
        let mut b = App::new();
        seal_dep_tidy::tidy(&mut a, &mut b); //~ NOTE this runs `seal_dep_visit::Settle::settle`, a fn of another crate, at the type `provided::App`
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
    pub fn run() {
        let mut a = App::new();
        a.cell.bump();
        let mut pair = seal_dep_visit::Pair { a, b: App::new() };
        seal_dep_tidy::run(&mut pair); //~ NOTE this runs `seal_dep_visit::Pair::visit`, a fn of another crate, at the type `driven::App`
    }
}

fn main() {
    provided::run();
    driven::run();
}

clean {
    import Trust.Binding
    namespace Third
    open Trust.Protocol
    def provided : Trust.Protocol.Seal := seals "provided::Cell" ["provided::Cell::bump"] ["provided::Cell::new"] ["provided::App::new"] ["seal_dep_tidy::tidy"]
    def driven : Trust.Protocol.Seal := seals "driven::Cell" ["driven::Cell::bump"] ["driven::Cell::new"] ["driven::App::new"] ["seal_dep_tidy::run"]
    end Third
}
//~^^^^ ERROR seal `Third.provided` on `Cell` does not hold
//~^^^^ ERROR seal `Third.driven` on `Cell` does not hold
