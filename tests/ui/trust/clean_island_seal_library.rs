//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! Seals in a LIBRARY (`Trust.Protocol.Seal`): a crate another crate can
//! depend on. The check reads this crate only, so the sealed type and its
//! makers must be out of every other crate's reach, and what a body of this
//! crate does is judged though only a crate that depends on it would run it.
//!
//! - `kept` HOLDS: a `pub` holder with the cell in a private field, and a
//!   `pub` fn that builds it through the private maker.
//! - `named`: the sealed type itself is `pub` at the crate's root.
//! - `minted`: the type is private, but its maker is a `pub` fn that hands
//!   back a holder: another crate can call it (review 12).
//! - `method`: a `pub` method of `impl<'a>` that no body of the crate calls
//!   puts one holder over another (review 12).
//! - `handed`: the same in a `pub` fn generic in its caller's closure, which
//!   only the caller's crate makes concrete (review 12).

#![crate_type = "lib"]
#![allow(unused)]

mod kept {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> App { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump(); }
    }
}
pub use kept::App;

pub struct Named { n: u32 }
impl Named {
    pub(crate) fn new() -> Self { Named { n: 0 } }
    pub fn bump(&mut self) { self.n += 1; }
}
pub(crate) fn named_user() { let mut named = Named::new(); named.bump(); }

mod minted {
    pub(crate) struct Stamped { generation: u64 }
    pub struct Holder { stamp: Stamped }
    pub fn mint(generation: u64) -> Holder { Holder { stamp: Stamped { generation } } }
    pub(crate) fn watcher() -> Holder { mint(1) }
}
pub use minted::{Holder, mint};

mod method {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub struct Runner<'a> { tag: &'a str }
    impl<'a> Runner<'a> {
        pub fn run(&self) -> u32 {
            let mut app = App { cell: Cell::new() };
            app.cell.bump();
            app = App { cell: Cell::new() };
            app.cell.n
        }
    }
}
pub use method::Runner;

mod handed {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub fn run(mut with: impl FnMut(u32)) {
        let mut app = App { cell: Cell::new() };
        app.cell.bump();
        with(app.cell.n);
        app = App { cell: Cell::new() };
        with(app.cell.n);
    }
}
pub use handed::run;

clean {
    import Trust.Binding
    namespace Library
    open Trust.Protocol
    def kept : Trust.Protocol.Seal := seals "kept::Cell" ["kept::Cell::bump"] ["kept::Cell::new"] ["kept::App::new"] []
    def named : Trust.Protocol.Seal := seals "Named" ["Named::bump"] ["Named::new"] ["named_user"] []
    def minted : Trust.Protocol.Seal := seals "minted::Stamped" [] ["minted::mint"] ["minted::watcher"] []
    def method : Trust.Protocol.Seal := seals "method::Cell" ["method::Cell::bump"] ["method::Cell::new"] ["method::Runner::run"] []
    def handed : Trust.Protocol.Seal := seals "handed::Cell" ["handed::Cell::bump"] ["handed::Cell::new"] ["handed::run"] []
    end Library
}
//~^^^^^^ ERROR seal `Library.named` is on `Named`, which another crate can name: this check rea
//~^^^^^^ ERROR seal `Library.minted` names `crate::minted::mint` as a maker, which another crat
//~^^^^^^ ERROR seal `Library.method` on `Cell` does not hold
//~^^^^^^ ERROR seal `Library.handed` on `Cell` does not hold
