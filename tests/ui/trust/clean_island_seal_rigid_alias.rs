//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! `Trust.Protocol.Seal`: a projection that the item's bounds keep RIGID (a
//! where-clause the compiler does not need shadows the blanket impl that would make
//! it `(T, App)`, or its trait is of this crate) owns every sealed type, whatever the
//! parameters stand for (review 5 of the review-14 build: it owned nothing, and a
//! crate that depends on the library swapped, overwrote or pushed two holders
//! through it). Swapped (`shadow_swap`), stored (`shadow_store`), handed to a
//! constant whose value swaps (`shadow_const`), std's `IntoIterator for Option`
//! (`shadow_std`), pushed and swapped in a `Vec` (`shadow_vec`), and a trait of this
//! crate's projection (`local_trait_alias`). Each refused.

#![allow(unused)]

pub mod shadow_swap {
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
    pub trait Id { type Out; }
    impl<X> Id for X { type Out = X; }
    pub fn churn<T>(a: &mut <(T, App) as Id>::Out, b: &mut <(T, App) as Id>::Out) where (T, App): Id { core::mem::swap(a, b) } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `<(T, shadow_swap::App) as
}

pub mod shadow_store {
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
    pub trait Id { type Out; }
    impl<X> Id for X { type Out = X; }
    pub fn churn<T>(a: &mut <(T, App) as Id>::Out, b: <(T, App) as Id>::Out) where (T, App): Id { *a = b; } //~ NOTE this puts a value of type `<(T, shadow_store::App) as shadow_store::Id>::Out`, which holds a `Cell`, where
}

pub mod shadow_const {
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
    pub trait Id { type Out; }
    impl<X> Id for X { type Out = X; }
    pub struct Tab<T>(core::marker::PhantomData<T>);
    impl<T> Tab<T> { const SW: fn(&mut T, &mut T) = core::mem::swap::<T>; } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `<(T, shadow_const::App) as
    pub fn churn<T>(a: &mut <(T, App) as Id>::Out, b: &mut <(T, App) as Id>::Out) where (T, App): Id { (Tab::<<(T, App) as Id>::Out>::SW)(a, b) }
}

pub mod shadow_std {
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
    pub fn churn<T>(a: &mut <Option<(T, App)> as IntoIterator>::Item, b: <Option<(T, App)> as IntoIterator>::Item) where Option<(T, App)>: IntoIterator { *a = b; } //~ NOTE this puts a value of type `<Option<(T, shadow_std::App)> as IntoIterator>::Item`, which holds a `Cell`, where
}

pub mod shadow_vec {
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
    pub trait Id { type Out; }
    impl<X> Id for X { type Out = X; }
    pub fn churn<T>(v: &mut Vec<<(T, App) as Id>::Out>, x: <(T, App) as Id>::Out) where (T, App): Id { v.push(x); v.swap(0, 1); } //~ NOTE this runs `alloc::vec::Vec::push`, a fn of another crate, at the type `<(T, shadow_vec::App) as
}

pub mod local_trait_alias {
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
    pub trait Out { type O; }
    impl<X> Out for X { type O = App; }
    pub fn churn<I>(a: &mut <I as Out>::O, b: <I as Out>::O) where I: Out { *a = b; } //~ NOTE this puts a value of type `<I as Out>::O`, which holds a `Cell`, where one may already be, in
}

clean {
    import Trust.Binding
    namespace RigidAlias
    open Trust.Protocol
    def shadow_swap : Trust.Protocol.Seal := seals "shadow_swap::Cell" ["shadow_swap::Cell::bump"] ["shadow_swap::Cell::new"] ["shadow_swap::App::new"] []
    def shadow_store : Trust.Protocol.Seal := seals "shadow_store::Cell" ["shadow_store::Cell::bump"] ["shadow_store::Cell::new"] ["shadow_store::App::new"] []
    def shadow_const : Trust.Protocol.Seal := seals "shadow_const::Cell" ["shadow_const::Cell::bump"] ["shadow_const::Cell::new"] ["shadow_const::App::new"] []
    def shadow_std : Trust.Protocol.Seal := seals "shadow_std::Cell" ["shadow_std::Cell::bump"] ["shadow_std::Cell::new"] ["shadow_std::App::new"] []
    def shadow_vec : Trust.Protocol.Seal := seals "shadow_vec::Cell" ["shadow_vec::Cell::bump"] ["shadow_vec::Cell::new"] ["shadow_vec::App::new"] []
    def local_trait_alias : Trust.Protocol.Seal := seals "local_trait_alias::Cell" ["local_trait_alias::Cell::bump"] ["local_trait_alias::Cell::new"] ["local_trait_alias::App::new"] []
    end RigidAlias
}
//~^^^^^^^^ ERROR seal `RigidAlias.shadow_swap` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `RigidAlias.shadow_store` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `RigidAlias.shadow_const` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `RigidAlias.shadow_std` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `RigidAlias.shadow_vec` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `RigidAlias.local_trait_alias` on `Cell` does not hold
