//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_vtable.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A `dyn` whose own bounds name a parameter (`Trust.Protocol.Seal`): a
//! library's generic code makes a CONCRETE type a `dyn` of a trait generic at
//! its parameter (`&P as &dyn Put<X>`), or a `dyn` of a holder whose trait has a
//! method with a where-clause the `dyn` does not prove (`fn m(..) where X:
//! Tr2`). The vtable is read open, in the body's own environment. Each seal
//! must FAIL: the method put in the vtable swaps two holders, whatever the
//! parameter stands for. Review 4 of the review-14 build found a compiler panic
//! in every crate with either shape (`vtable_entries` asked of `P: Show<X>`;
//! `Instance::try_resolve` handed a `Vec<<T as Tr2>::Out>` it could not
//! normalize), at any seal: these modules were written for this fixture, to pin
//! that the vtable is read, not skipped.
//! 
//! The shapes of the panics, at methods that write nothing, hold:
//! `_vtable_params_holds.rs`.

#![allow(unused)]

extern crate seal_dep_vtable;

pub mod put_dyn {
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
    pub trait Put<X> { fn put(&self, a: &mut (X, App), b: &mut (X, App)); }
    pub struct P;
    impl<X> Put<X> for P { fn put(&self, a: &mut (X, App), b: &mut (X, App)) { core::mem::swap(a, b) } } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `(X, put_dyn::App)`, which holds a `Cell`, in
    pub fn obj<X>() -> &'static dyn Put<X> { &P }
}

pub mod where_method {
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
    pub trait Tr2 { type Out; }
    pub trait Tr<X> { fn m(&self, a: &mut X, b: &mut X) where X: Tr2 { core::mem::swap(a, b) } fn n(&self) {} } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `(T, where_method::App)`, which holds a
    impl<T, X> Tr<X> for (T, App) {}
    pub fn mk<T>(x: &(T, App)) -> &dyn Tr<(T, App)> { x }
}

pub mod via_dep {
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
    pub fn churn<T: 'static>(a: &mut (T, App), b: &mut (T, App)) { seal_dep_vtable::swapper::<(T, App)>().swp(a, b) } //~ NOTE this runs `seal_dep_vtable::Q::swp`, a fn of another crate, at the type `(T, via_dep::App)`, which holds a
}

clean {
    import Trust.Binding
    namespace VtableParams
    open Trust.Protocol
    def put_dyn : Trust.Protocol.Seal := seals "put_dyn::Cell" ["put_dyn::Cell::bump"] ["put_dyn::Cell::new"] ["put_dyn::App::new"] []
    def where_method : Trust.Protocol.Seal := seals "where_method::Cell" ["where_method::Cell::bump"] ["where_method::Cell::new"] ["where_method::App::new"] []
    def via_dep : Trust.Protocol.Seal := seals "via_dep::Cell" ["via_dep::Cell::bump"] ["via_dep::Cell::new"] ["via_dep::App::new"] ["seal_dep_vtable::swapper"]
    end VtableParams
}
//~^^^^^ ERROR seal `VtableParams.put_dyn` on `Cell` does not hold
//~^^^^^ ERROR seal `VtableParams.where_method` on `Cell` does not hold
//~^^^^^ ERROR seal `VtableParams.via_dep` on `Cell` does not hold
