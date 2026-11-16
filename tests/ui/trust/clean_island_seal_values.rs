//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_values.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A fn reached as a VALUE runs where it is called, and what covered the way
//! to the item that handed it out covers none of that
//! (`Trust.Protocol.Seal`): each seal must FAIL. Review 2 of the review-14
//! build found the first four passing: a `trusts` entry named the item that
//! handed the fn out, and the swap (or the overwrite) this crate then made
//! through the pointer was taken as that item's.
//!
//! - `konst`: the entry names a CONSTANT of another crate, `Tab::SWAP =
//!   mem::swap::<T>`. A constant runs nothing; an entry names a fn or a
//!   trait, and this one names nothing.
//! - `statik`: the same constant, through a `static` of this crate.
//! - `provided`: a trait's default constant, `Ops::PUT = put::<Self>`.
//! - `returned`: a trusted fn that only RETURNS `mem::swap::<T>` as a fn
//!   pointer: the swap runs in `run`, not beneath it.
//! - `closure`: a trusted fn that returns a closure that swaps. A closure is
//!   no item a `trusts` entry names (it had the path of the fn it is in).
//! - `boxed`: a trusted fn that returns the closure as a boxed `dyn Fn`: the
//!   vtable's methods run wherever the `dyn` is called.
//!
//! With a fn pointer that only measures, and its fn trusted by name, the
//! seal holds: `_values_holds.rs`.

#![allow(unused)]

extern crate seal_dep_values;

mod konst {
    use seal_dep_values::Tab;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() {
        let mut a = App::new();
        let mut b = App::new();
        a.cell.bump();
        (Tab::<App>::SWAP)(&mut a, &mut b); //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `konst::App`
    }
}

mod statik {
    use seal_dep_values::Tab;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    static SW: fn(&mut App, &mut App) = Tab::<App>::SWAP; //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `statik::App`
    pub fn run() {
        let mut a = App::new();
        let mut b = App::new();
        a.cell.bump();
        SW(&mut a, &mut b);
    }
}

mod provided {
    use seal_dep_values::Ops;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    impl Ops for App {}
    pub fn run() {
        let mut a = App::new();
        a.cell.bump();
        (<App as Ops>::PUT)(&mut a, App::new()); //~ NOTE this runs `seal_dep_values::put`, a fn of another crate, at the type `provided::App`
    }
}

mod returned {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() {
        let mut a = App::new();
        let mut b = App::new();
        a.cell.bump();
        let f = seal_dep_values::swapper::<App>(); //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `returned::App`
        f(&mut a, &mut b);
    }
}

mod closure {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() {
        let mut a = App::new();
        let mut b = App::new();
        a.cell.bump();
        let f = seal_dep_values::closure_swapper::<App>();
        f(&mut a, &mut b); //~ NOTE this runs a closure (or an `async` block) in `seal_dep_values::closure_swapper`, of another crate, at the type `closure::App`
    }
}

mod boxed {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() {
        let mut a = App::new();
        let mut b = App::new();
        a.cell.bump();
        let f = seal_dep_values::boxed_swapper::<App>(); //~ NOTE this runs a closure (or an `async` block) in `seal_dep_values::boxed_swapper`, of another crate, at the type `boxed::App`
        f(&mut a, &mut b);
    }
}

fn main() {
    konst::run();
    statik::run();
    provided::run();
    returned::run();
    closure::run();
    boxed::run();
}

clean {
    import Trust.Binding
    namespace Values
    open Trust.Protocol
    def konst : Trust.Protocol.Seal := seals "konst::Cell" ["konst::Cell::bump"] ["konst::Cell::new"] ["konst::App::new"] ["Tab::SWAP"]
    def statik : Trust.Protocol.Seal := seals "statik::Cell" ["statik::Cell::bump"] ["statik::Cell::new"] ["statik::App::new"] ["Tab::SWAP"]
    def provided : Trust.Protocol.Seal := seals "provided::Cell" ["provided::Cell::bump"] ["provided::Cell::new"] ["provided::App::new"] ["Ops::PUT"]
    def returned : Trust.Protocol.Seal := seals "returned::Cell" ["returned::Cell::bump"] ["returned::Cell::new"] ["returned::App::new"] ["seal_dep_values::swapper"]
    def closure : Trust.Protocol.Seal := seals "closure::Cell" ["closure::Cell::bump"] ["closure::Cell::new"] ["closure::App::new"] ["seal_dep_values::closure_swapper"]
    def boxed : Trust.Protocol.Seal := seals "boxed::Cell" ["boxed::Cell::bump"] ["boxed::Cell::new"] ["boxed::App::new"] ["seal_dep_values::boxed_swapper"]
    end Values
}
//~^^^^^^^^ ERROR seal `Values.konst` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `Values.statik` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `Values.provided` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `Values.returned` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `Values.closure` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `Values.boxed` on `Cell` does not hold
