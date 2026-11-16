//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A NESTED type behind a non-owning std pointer (`Trust.Protocol.Seal`):
//! `Nest<T>` with a field `Weak<Nest<Option<T>>>`, whose instances grow as they
//! are walked. What it owns is read off its definitions where the walk has no
//! end. Each seal must FAIL: the type holds an `App` in a field of its own, and
//! a value is put over another (at `u8`, and whatever `T` is). (Written for
//! this fixture: review 4 of the review-14 build found the type taken to hold
//! one when it held none, with no `trusts` entry to answer it; the twin is
//! `_nested_owns_holds.rs`.)

#![allow(unused)]

pub mod holder {
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
    use std::rc::Weak;
    pub struct Nest<T> { v: T, app: App, up: Option<Weak<Nest<Option<T>>>> }
    pub fn reset(n: &mut Nest<u8>) { *n = Nest { v: 2, app: App::new(), up: None }; } //~ NOTE this puts a value of type `holder::Nest<u8>`, which holds a `Cell`, where one may already be, in
}

pub mod open_holder {
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
    use std::rc::Weak;
    pub struct Nest<T> { v: T, app: App, up: Option<Weak<Nest<Option<T>>>> }
    pub fn put<T>(slot: &mut Nest<T>, v: Nest<T>) { *slot = v; } //~ NOTE this puts a value of type `open_holder::Nest<T>`, which holds a `Cell`, where one may already be, in
}

clean {
    import Trust.Binding
    namespace NestedOwns
    open Trust.Protocol
    def holder : Trust.Protocol.Seal := seals "holder::Cell" ["holder::Cell::bump"] ["holder::Cell::new"] ["holder::App::new"] ["Weak::drop"]
    def open_holder : Trust.Protocol.Seal := seals "open_holder::Cell" ["open_holder::Cell::bump"] ["open_holder::Cell::new"] ["open_holder::App::new"] ["Weak::drop"]
    end NestedOwns
}
//~^^^^ ERROR seal `NestedOwns.holder` on `Cell` does not hold
//~^^^^ ERROR seal `NestedOwns.open_holder` on `Cell` does not hold
