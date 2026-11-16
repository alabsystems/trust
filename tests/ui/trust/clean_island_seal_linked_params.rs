//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_linked.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! `Trust.Protocol.Seal`: a dependency's generic fn named at a bare type parameter
//! that the item's bounds tie to a sealed value (`M: Make<Out = App>`, `P:
//! DerefMut<Target = App>`, `K: Sw<Item = (T, App)>`) is followed, and what it
//! does at `M::Out` is done to an `App` (review 5 of the review-14 build: such a
//! call was never followed, and a crate that depends on the library swapped or
//! overwrote two holders through it): an `unsafe` swap (`unsafe_direct`), safe
//! swaps and stores (`safe_swap_out`, `safe_put`, `deref_target`, `where_bound`),
//! and a driver that runs the trait method its type argument picks (`driver`).
//! Each refused.

#![allow(unused)]

extern crate seal_dep_linked;

pub mod unsafe_direct {
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
    pub fn churn<M: seal_dep_linked::Make<Out = App>>(a: &mut App, b: &mut App) { seal_dep_linked::direct::<M>(a, b) } //~ NOTE this runs `seal_dep_linked::direct`, a fn of a crate outside the standard library, which calls an `unsafe
}

pub mod safe_swap_out {
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
    pub fn churn<M: seal_dep_linked::Make<Out = App>>(a: &mut App, b: &mut App) { seal_dep_linked::swap_out::<M>(a, b) } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `safe_swap_out::App`, which holds a `Cell`,
}

pub mod safe_put {
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
    pub fn churn<M: seal_dep_linked::Make<Out = App>>(a: &mut App, b: App) { seal_dep_linked::put::<M>(a, b) } //~ NOTE `put`, named here in `safe_put::churn`, runs code of another crate that puts a value of type `safe_put::App`,
}

pub mod deref_target {
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
    pub fn churn<P: core::ops::DerefMut<Target = App>>(a: &mut P, b: &mut P) { seal_dep_linked::swap_deref::<P>(a, b) } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `deref_target::App`, which holds a `Cell`, in
}

pub mod where_bound {
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
    pub fn churn<M>(a: &mut App, b: &mut App) where M: seal_dep_linked::Make<Out = App> { seal_dep_linked::swap_out::<M>(a, b) } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `where_bound::App`, which holds a `Cell`, in
}

pub mod driver {
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
    pub fn churn<K: seal_dep_linked::Sw<Item = (T, App)>, T>(a: &mut (T, App), b: &mut (T, App)) { seal_dep_linked::run::<K>(a, b) } //~ NOTE this runs `seal_dep_linked::Sw::sw`, a fn of another crate, at the type `&mut (T, driver::App)`, which holds
}

clean {
    import Trust.Binding
    namespace LinkedParams
    open Trust.Protocol
    def unsafe_direct : Trust.Protocol.Seal := seals "unsafe_direct::Cell" ["unsafe_direct::Cell::bump"] ["unsafe_direct::Cell::new"] ["unsafe_direct::App::new"] []
    def safe_swap_out : Trust.Protocol.Seal := seals "safe_swap_out::Cell" ["safe_swap_out::Cell::bump"] ["safe_swap_out::Cell::new"] ["safe_swap_out::App::new"] []
    def safe_put : Trust.Protocol.Seal := seals "safe_put::Cell" ["safe_put::Cell::bump"] ["safe_put::Cell::new"] ["safe_put::App::new"] []
    def deref_target : Trust.Protocol.Seal := seals "deref_target::Cell" ["deref_target::Cell::bump"] ["deref_target::Cell::new"] ["deref_target::App::new"] []
    def where_bound : Trust.Protocol.Seal := seals "where_bound::Cell" ["where_bound::Cell::bump"] ["where_bound::Cell::new"] ["where_bound::App::new"] []
    def driver : Trust.Protocol.Seal := seals "driver::Cell" ["driver::Cell::bump"] ["driver::Cell::new"] ["driver::App::new"] []
    end LinkedParams
}
//~^^^^^^^^ ERROR seal `LinkedParams.unsafe_direct` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `LinkedParams.safe_swap_out` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `LinkedParams.safe_put` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `LinkedParams.deref_target` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `LinkedParams.where_bound` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `LinkedParams.driver` on `Cell` does not hold
