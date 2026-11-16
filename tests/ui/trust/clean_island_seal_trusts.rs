//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_collide.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! `trusts` entries that say more than the author meant (`Trust.Protocol.
//! Seal`): each seal must FAIL, for that reason. Review 1 of the review-14
//! build found each one passing, and the program putting one holder over
//! another. An entry names ONE item, as a writer or a maker does.
//!
//! - `pushed`: `Vec::push`, meant for std's, also names the dependency's
//!   `stack::Vec::push`, which puts the newest holder over the last one.
//! - `boxedany`: `any::Any`, meant for std's, also names the dependency's
//!   own trait `any::Any`, a `dyn` of which its `exchange` swaps.
//! - `converted`: `Vec::from` (the word the doc once gave for
//!   `vec![holder]`) also names the dependency's `impl From<Ring<T>> for
//!   Vec<T>`, defined at `seal_dep_collide::Vec::from`, which puts the
//!   newest holder over the oldest.
//! - `leading`, `trailing`: `::swap` and `swap::` are matched as the bare
//!   name `swap`, which would trust every fn of that name in every crate.
//! - `gap`: `mem::::swap` has an empty part.
//!
//! The entries that tell the items apart hold: `_trusts_holds.rs`.

#![allow(unused)]

extern crate seal_dep_collide;

mod pushed {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() {
        let mut kept: Vec<App> = Vec::new();
        kept.push(App::new());
        let mut ring = seal_dep_collide::stack::Vec::with_capacity(1);
        let mut a = App::new();
        a.cell.bump();
        ring.push(a);
        ring.push(App::new());
    }
}

mod boxedany {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    impl seal_dep_collide::any::Any for App {}
    pub fn run() {
        let kept: Box<dyn std::any::Any> = Box::new(App::new());
        let mut a = App::new();
        a.cell.bump();
        let mut x: Box<dyn seal_dep_collide::any::Any> = Box::new(a);
        let mut y: Box<dyn seal_dep_collide::any::Any> = Box::new(App::new());
        seal_dep_collide::any::exchange(&mut x, &mut y);
    }
}

mod converted {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() {
        let first = Vec::from([App::new()]);
        let mut a = App::new();
        a.cell.bump();
        let mut ring = seal_dep_collide::Ring::new(1);
        ring.put(a);
        ring.put(App::new());
        let all: Vec<App> = Vec::from(ring);
    }
}

mod leading {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub fn run() {
        let mut a = Cell::new();
        let mut b = Cell::new();
        a.bump();
        std::mem::swap(&mut a, &mut b);
    }
}

mod trailing {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub fn run() {
        let mut a = Cell::new();
        a.bump();
    }
}

mod gap {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub fn run() {
        let mut a = Cell::new();
        a.bump();
    }
}

fn main() {
    pushed::run();
    boxedany::run();
    converted::run();
    leading::run();
    trailing::run();
    gap::run();
}

clean {
    import Trust.Binding
    namespace Trusts
    open Trust.Protocol
    def pushed : Trust.Protocol.Seal := seals "pushed::Cell" ["pushed::Cell::bump"] ["pushed::Cell::new"] ["pushed::App::new"] ["Vec::push"]
    def boxedany : Trust.Protocol.Seal := seals "boxedany::Cell" ["boxedany::Cell::bump"] ["boxedany::Cell::new"] ["boxedany::App::new"] ["any::Any"]
    def converted : Trust.Protocol.Seal := seals "converted::Cell" ["converted::Cell::bump"] ["converted::Cell::new"] ["converted::App::new"] ["Vec::from"]
    def leading : Trust.Protocol.Seal := seals "leading::Cell" ["leading::Cell::bump"] ["leading::Cell::new"] ["leading::run"] ["::swap"]
    def trailing : Trust.Protocol.Seal := seals "trailing::Cell" ["trailing::Cell::bump"] ["trailing::Cell::new"] ["trailing::run"] ["swap::"]
    def gap : Trust.Protocol.Seal := seals "gap::Cell" ["gap::Cell::bump"] ["gap::Cell::new"] ["gap::run"] ["mem::::swap"]
    end Trusts
}
//~^^^^^^^^ ERROR seal `Trusts.pushed` on `Cell` does not hold
//~| NOTE its `trusts` entry `Vec::push` names 2 items: `alloc::vec::Vec::push` and `seal_dep_collide::stack::Vec::push`
//~^^^^^^^^^ ERROR seal `Trusts.boxedany` on `Cell` does not hold
//~| NOTE its `trusts` entry `any::Any` names 2 items: `core::any::Any` and `seal_dep_collide::any::Any`
//~^^^^^^^^^^ ERROR seal `Trusts.converted` on `Cell` does not hold
//~| NOTE its `trusts` entry `Vec::from` names 2 items: `alloc::vec::Vec::from` and `seal_dep_collide::Vec::from`
//~^^^^^^^^^^^ ERROR seal `Trusts.leading` trusts `::swap`, a bare name
//~^^^^^^^^^^^ ERROR seal `Trusts.trailing` trusts `swap::`, a bare name
//~^^^^^^^^^^^ ERROR seal `Trusts.gap` trusts `mem::::swap`, a path with an empty part
