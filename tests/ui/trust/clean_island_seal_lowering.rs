//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_unsafe_peek.rs
//@ aux-build: seal_dep_async_run.rs
//@ aux-build: seal_dep_async_make.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The twin of `clean_island_seal_lowering_holds.rs` (`Trust.Protocol.Seal`):
//! each seal must FAIL.
//!
//! - `peeked`: a dependency fn whose SOURCE uses `unsafe`, at an instance
//!   where it handles a pointer to a holder: what its `unsafe` does is not
//!   read, whatever the compiler lowered.
//! - `latent`: crate B's `async` closure swaps two holders, and crate A runs
//!   it once (`AsyncFnOnce`: B's by-move body, a synthetic coroutine body).
//!   The seal trusts A's `run`: the body is code A did not choose, and A's
//!   trust does not cover it. (Review 2 of the review-14 build: such a body
//!   was read as chosen, under A's trust; only the coroutine's compiler-made
//!   transmute, read as B's `unsafe`, still failed the seal.)

#![allow(unused)]

extern crate seal_dep_async_make;
extern crate seal_dep_async_run;
extern crate seal_dep_unsafe_peek;

mod peeked {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> u8 {
        let mut app = App::new();
        app.cell.bump();
        let mut r: &mut App = &mut app;
        seal_dep_unsafe_peek::peek(&mut r) //~ NOTE this runs `seal_dep_unsafe_peek::peek`, a fn of a crate outside the standard library
    }
}

mod latent {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    struct Mark;
    impl seal_dep_async_make::Make for Mark { type Out = App; }
    pub fn run() {
        let mut x = App::new();
        let mut y = App::new();
        x.cell.bump();
        seal_dep_async_run::run(seal_dep_async_make::later::<Mark>(&mut x, &mut y)); //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `latent::App`
    }
}

fn main() {
    peeked::run();
    latent::run();
}

clean {
    import Trust.Binding
    namespace Lowering
    open Trust.Protocol
    def peeked : Trust.Protocol.Seal := seals "peeked::Cell" ["peeked::Cell::bump"] ["peeked::Cell::new"] ["peeked::App::new"] []
    def latent : Trust.Protocol.Seal := seals "latent::Cell" ["latent::Cell::bump"] ["latent::Cell::new"] ["latent::App::new"] ["seal_dep_async_run::run"]
    end Lowering
}
//~^^^^ ERROR seal `Lowering.peeked` on `Cell` does not hold
//~^^^^ ERROR seal `Lowering.latent` on `Cell` does not hold
