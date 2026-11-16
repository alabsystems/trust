//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_stack.rs
//@ aux-build: seal_dep_measure.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A `trusts` entry names ONE item, also where a generic fn of a LIBRARY is
//! judged where it stands (`Trust.Protocol.Seal`): each seal must FAIL, for
//! an entry that names two items. Review 2 of the review-14 build found both
//! passing: the reading of a body where it stands covered the dependency's
//! fn by the entry and never said it relied on it, so the entry named one
//! item, std's (or the measuring crate's), and a crate that depends on this
//! one could swap two holders through `put` or `churn`.
//!
//! - `pushed`: `Vec::push`, relied on for std's in `keep`, also covers
//!   `seal_dep_stack::stack::Vec::push` at `(T, App)` in `put`.
//! - `kept`: `util::keep`, relied on for `seal_dep_measure::util::keep` in
//!   `measure`, also covers `seal_dep_stack::util::keep` (which swaps) at
//!   `(T, App)` in `churn`.
//!
//! With entries that each name one item: `_standing_holds.rs`.

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
    pub fn churn<T>(a: &mut (T, App), b: &mut (T, App)) -> usize { seal_dep_stack::util::keep(a, b) }
}

clean {
    import Trust.Binding
    namespace Standing
    open Trust.Protocol
    def pushed : Trust.Protocol.Seal := seals "pushed::Cell" ["pushed::Cell::bump"] ["pushed::Cell::new"] ["pushed::App::new"] ["Vec::push"]
    def kept : Trust.Protocol.Seal := seals "kept::Cell" ["kept::Cell::bump"] ["kept::Cell::new"] ["kept::App::new"] ["util::keep"]
    end Standing
}
//~^^^^ ERROR seal `Standing.pushed` on `Cell` does not hold
//~| NOTE its `trusts` entry `Vec::push` names 2 items: `alloc::vec::Vec::push` and `seal_dep_stack::stack::Vec::push`
//~^^^^^ ERROR seal `Standing.kept` on `Cell` does not hold
//~| NOTE its `trusts` entry `util::keep` names 2 items: `seal_dep_measure::util::keep` and `seal_dep_stack::util::keep`
