//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_abstract.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! An ABSTRACT impl (`Trust.Protocol.Seal`): in a library's generic code read
//! open, an item where the compiler names no one body (an impl a where-clause or
//! a projection bound picks) is unknown code at every type it is handed: its
//! type arguments, and its declaration's inputs, normalized where a projection
//! bound says what an associated type is. Each seal must FAIL: whatever `T` is,
//! the code hands two `(T, App)` to an impl that swaps them. Review 4 of the
//! review-14 build found every one of these passing: an impl of a trait of this
//! crate whose impl a where-clause picks was skipped (`local_where_*`,
//! `local_param`: the impl, read where it stands, sees a bare parameter), and a
//! dependency's trait item was judged by its type arguments `[K]` alone
//! (`dep_assoc_*`: `K::Item = (T, App)` is said by the bound). (`local_assoc`
//! was written for this fixture: a trait of this crate whose associated type a
//! bound sets.)
//! 
//! With a type that holds none, the compiler's own pick, an input the trait's
//! declaration names, or the dependency's item trusted, the seals hold:
//! `_abstract_holds.rs`.

#![allow(unused)]

extern crate seal_dep_abstract;

pub mod local_where_const {
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
    pub trait Bound {}
    impl<Y> Bound for Y {}
    pub trait LocalSw: Sized { const SW: fn(&mut Self, &mut Self); }
    impl<X: Bound> LocalSw for X { const SW: fn(&mut X, &mut X) = core::mem::swap::<X>; }
    pub fn churn<T>(a: &mut (T, App), b: &mut (T, App)) where (T, App): LocalSw { (<(T, App) as LocalSw>::SW)(a, b) } //~ NOTE this names `local_where_const::LocalSw::SW` at the type `(T, local_where_const::App)`, which holds a `Cell`,
}

pub mod local_where_method {
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
    pub trait Bound {}
    impl<Y> Bound for Y {}
    pub trait LocalSw: Sized { fn sw(&mut self, o: &mut Self); }
    impl<X: Bound> LocalSw for X { fn sw(&mut self, o: &mut X) { core::mem::swap(self, o) } }
    pub fn churn<T>(a: &mut (T, App), b: &mut (T, App)) where (T, App): LocalSw { a.sw(b) } //~ NOTE this names `local_where_method::LocalSw::sw` at the type `(T, local_where_method::App)`, which holds a
}

pub mod local_param {
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
    pub trait LSw<P> { const SW: fn(&mut P, &mut P); }
    pub struct Any;
    impl<P> LSw<P> for Any { const SW: fn(&mut P, &mut P) = core::mem::swap::<P>; }
    pub fn churn<T, K: LSw<(T, App)>>(a: &mut (T, App), b: &mut (T, App)) { (<K as LSw<(T, App)>>::SW)(a, b) } //~ NOTE this names `local_param::LSw::SW` at the type `(T, local_param::App)`, which holds a `Cell`, in
}

pub mod local_assoc {
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
    pub trait LSw { type Item; fn sw(a: &mut Self::Item, b: &mut Self::Item); }
    pub struct LBy<P>(core::marker::PhantomData<P>);
    impl<P> LSw for LBy<P> { type Item = P; fn sw(a: &mut P, b: &mut P) { core::mem::swap(a, b) } }
    pub fn churn<K: LSw<Item = (T, App)>, T>(a: &mut (T, App), b: &mut (T, App)) { K::sw(a, b) } //~ NOTE this names `local_assoc::LSw::sw` at the type `&mut (T, local_assoc::App)`, which holds a `Cell`, in
}

pub mod dep_assoc_const {
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
    pub fn churn<K: seal_dep_abstract::Sw<Item = (T, App)>, T>(a: &mut (T, App), b: &mut (T, App)) { (K::SW)(a, b) } //~ NOTE this runs `seal_dep_abstract::Sw::SW`, of another crate, at the type `for<'a, 'b> fn(&'a mut (T,
}

pub mod dep_assoc_method {
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
    pub fn churn<K: seal_dep_abstract::Sw<Item = (T, App)>, T>(a: &mut (T, App), b: &mut (T, App)) { K::sw(a, b) } //~ NOTE this runs `seal_dep_abstract::Sw::sw`, a fn of another crate, at the type `&mut (T, dep_assoc_method::App)`,
}

pub mod dep_assoc_where {
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
    pub fn churn<K, T>(a: &mut (T, App), b: &mut (T, App)) where K: seal_dep_abstract::Sw<Item = (T, App)> { K::sw(a, b) } //~ NOTE this runs `seal_dep_abstract::Sw::sw`, a fn of another crate, at the type `&mut (T, dep_assoc_where::App)`,
}

clean {
    import Trust.Binding
    namespace Abstract
    open Trust.Protocol
    def local_where_const : Trust.Protocol.Seal := seals "local_where_const::Cell" ["local_where_const::Cell::bump"] ["local_where_const::Cell::new"] ["local_where_const::App::new"] []
    def local_where_method : Trust.Protocol.Seal := seals "local_where_method::Cell" ["local_where_method::Cell::bump"] ["local_where_method::Cell::new"] ["local_where_method::App::new"] []
    def local_param : Trust.Protocol.Seal := seals "local_param::Cell" ["local_param::Cell::bump"] ["local_param::Cell::new"] ["local_param::App::new"] []
    def local_assoc : Trust.Protocol.Seal := seals "local_assoc::Cell" ["local_assoc::Cell::bump"] ["local_assoc::Cell::new"] ["local_assoc::App::new"] []
    def dep_assoc_const : Trust.Protocol.Seal := seals "dep_assoc_const::Cell" ["dep_assoc_const::Cell::bump"] ["dep_assoc_const::Cell::new"] ["dep_assoc_const::App::new"] []
    def dep_assoc_method : Trust.Protocol.Seal := seals "dep_assoc_method::Cell" ["dep_assoc_method::Cell::bump"] ["dep_assoc_method::Cell::new"] ["dep_assoc_method::App::new"] []
    def dep_assoc_where : Trust.Protocol.Seal := seals "dep_assoc_where::Cell" ["dep_assoc_where::Cell::bump"] ["dep_assoc_where::Cell::new"] ["dep_assoc_where::App::new"] []
    end Abstract
}
//~^^^^^^^^^ ERROR seal `Abstract.local_where_const` on `Cell` does not hold
//~^^^^^^^^^ ERROR seal `Abstract.local_where_method` on `Cell` does not hold
//~^^^^^^^^^ ERROR seal `Abstract.local_param` on `Cell` does not hold
//~^^^^^^^^^ ERROR seal `Abstract.local_assoc` on `Cell` does not hold
//~^^^^^^^^^ ERROR seal `Abstract.dep_assoc_const` on `Cell` does not hold
//~^^^^^^^^^ ERROR seal `Abstract.dep_assoc_method` on `Cell` does not hold
//~^^^^^^^^^ ERROR seal `Abstract.dep_assoc_where` on `Cell` does not hold
