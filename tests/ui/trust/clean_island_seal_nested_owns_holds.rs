//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_nested_owns.rs` (`Trust.Protocol.Seal`): the
//! nested type holds no sealed value, and putting one over another, or dropping
//! one, HOLDS with no entry. Review 4 of the review-14 build found `owns`
//! answering "every seal" at its walk's bound (`*n = Nest { .. }` refused, and
//! `Weak::drop` asked for "at a type that holds a `Cell`").

#![allow(unused)]

pub mod plain {
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
    pub struct Nest<T> { v: T, up: Option<Weak<Nest<Option<T>>>> }
    pub fn reset(n: &mut Nest<u8>) { *n = Nest { v: 2, up: None }; }
    pub fn sink(n: Nest<u8>) {}
}

pub mod open_plain {
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
    pub struct Nest<T> { v: T, up: Option<Weak<Nest<Option<T>>>> }
    pub fn put<T>(slot: &mut Nest<T>, v: Nest<T>) { *slot = v; }
}

clean {
    import Trust.Binding
    namespace NestedOwnsHolds
    open Trust.Protocol
    def plain : Trust.Protocol.Seal := seals "plain::Cell" ["plain::Cell::bump"] ["plain::Cell::new"] ["plain::App::new"] []
    def open_plain : Trust.Protocol.Seal := seals "open_plain::Cell" ["open_plain::Cell::bump"] ["open_plain::Cell::new"] ["open_plain::App::new"] []
    end NestedOwnsHolds
}
