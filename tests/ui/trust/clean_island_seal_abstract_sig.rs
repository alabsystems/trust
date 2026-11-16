//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_sig.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! `Trust.Protocol.Seal`: an ABSTRACT impl (an item whose impl a where-clause or a
//! type parameter picks, so the compiler names no one body) is judged by its whole
//! signature, with nothing taken off (review 5 of the review-14 build): what a
//! method HANDS BACK, which the body then calls on two holders (a fn pointer,
//! `local_fnptr_method`, `dep_fnptr_method`; an `impl Fn`, `local_impl_fn`; a boxed
//! `dyn Fn`, `dep_boxed_method`); a constant whose type is an `Fn`-bounded
//! associated type (`local_op_const`, `dep_op_const`) or a `&dyn Fn` of one
//! (`local_dyn_const`); the holder handed as `Self` beside a holder the trait
//! declares (`declared_ctx`, `declared_const`, `declared_phantom`); a trait of this
//! crate's method whose impl a parameter picks, handed the `&mut App` it declares
//! (`declared_input`: a listed cost, no entry answers it); another crate's trait
//! that this crate implements, its item's entry given (`foreign_trait_local_impl`,
//! `dep_trait_local_impl`, `local_drop_where`: this crate's impl may be what runs);
//! and an abstract impl beneath a trusted driver (`under_trusted_driver`: the
//! driver's trust does not cover what its type argument picks). Each refused.

#![allow(unused)]

extern crate seal_dep_sig;

pub mod local_op_const {
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
    use core::marker::PhantomData;
    pub trait LocalSw { type Item; type Op: Fn(&mut Self::Item, &mut Self::Item) + Copy; const SW: Self::Op; }
    pub struct By<P>(PhantomData<P>);
    impl<P> LocalSw for By<P> { type Item = P; type Op = fn(&mut P, &mut P); const SW: fn(&mut P, &mut P) = core::mem::swap::<P>; }
    pub fn churn<K: LocalSw<Item = (T, App)>, T>(a: &mut (T, App), b: &mut (T, App)) { (K::SW)(a, b) } //~ NOTE this names `local_op_const::LocalSw::SW` at the type `<K as local_op_const::LocalSw>::Op`, which holds a
}

pub mod local_dyn_const {
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
    use core::marker::PhantomData;
    pub trait LocalSw { type Item: 'static; const SW: &'static dyn Fn(&mut Self::Item, &mut Self::Item); }
    pub struct By<P>(PhantomData<P>);
    impl<P: 'static> LocalSw for By<P> { type Item = P; const SW: &'static dyn Fn(&mut P, &mut P) = &|a, b| core::mem::swap(a, b); }
    pub fn churn<K: LocalSw<Item = (T, App)>, T: 'static>(a: &mut (T, App), b: &mut (T, App)) { (K::SW)(a, b) } //~ NOTE this names `local_dyn_const::LocalSw::SW` at the type `&dyn for<'a, 'b> Fn(&'a mut (T, local_dyn_const::App),
}

pub mod local_fnptr_method {
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
    use core::marker::PhantomData;
    pub trait LocalSw { type Item; fn op() -> fn(&mut Self::Item, &mut Self::Item); }
    pub struct By<P>(PhantomData<P>);
    impl<P> LocalSw for By<P> { type Item = P; fn op() -> fn(&mut P, &mut P) { core::mem::swap::<P> } }
    pub fn churn<K: LocalSw<Item = (T, App)>, T>(a: &mut (T, App), b: &mut (T, App)) { (K::op())(a, b) } //~ NOTE this names `local_fnptr_method::LocalSw::op` at the type `for<'a, 'b> fn(&'a mut (T,
}

pub mod local_impl_fn {
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
    use core::marker::PhantomData;
    pub trait LocalSw { type Item; fn op() -> impl Fn(&mut Self::Item, &mut Self::Item); }
    pub struct By<P>(PhantomData<P>);
    impl<P> LocalSw for By<P> { type Item = P; fn op() -> impl Fn(&mut P, &mut P) { |a: &mut P, b: &mut P| core::mem::swap(a, b) } }
    pub fn churn<K: LocalSw<Item = (T, App)>, T>(a: &mut (T, App), b: &mut (T, App)) { (K::op())(a, b) } //~ NOTE this runs `core::ops::function::Fn::call`, a fn of another crate, at the type `impl for<'a, 'b> Fn(&'a mut <K
}

pub mod dep_fnptr_method {
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
    pub fn churn<K: seal_dep_sig::Hand<Item = (T, App)>, T: 'static>(a: &mut (T, App), b: &mut (T, App)) { (K::swapper())(a, b) } //~ NOTE this runs `seal_dep_sig::Hand::swapper`, a fn of another crate, at the type `for<'a, 'b> fn(&'a mut (T,
}

pub mod dep_boxed_method {
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
    pub fn churn<K: seal_dep_sig::Hand<Item = (T, App)>, T: 'static>(a: &mut (T, App), b: &mut (T, App)) { let f = K::boxed(); f(a, b) } //~ NOTE this runs `seal_dep_sig::Hand::boxed`, a fn of another crate, at the type `Box<dyn for<'a, 'b> Fn(&'a mut (T,
}

pub mod dep_op_const {
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
    pub fn churn<K: seal_dep_sig::Hand<Item = (T, App)>, T: 'static>(a: &mut (T, App), b: &mut (T, App)) { (K::OP)(a, b) } //~ NOTE this runs `core::ops::function::Fn::call`, a fn of another crate, at the type `<K as Hand>::Op`, which holds
}

pub mod declared_ctx {
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
    pub trait LocalSw: Sized { fn sw(&mut self, o: &mut Self, ctx: &mut App); }
    impl<X: Bound> LocalSw for X { fn sw(&mut self, o: &mut X, ctx: &mut App) { ctx.tick(); core::mem::swap(self, o) } }
    pub fn churn<T>(a: &mut (T, App), b: &mut (T, App), ctx: &mut App) where (T, App): LocalSw { a.sw(b, ctx) } //~ NOTE this names `declared_ctx::LocalSw::sw` at the type `(T, declared_ctx::App)`, which holds a `Cell`, in
}

pub mod declared_const {
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
    pub trait LocalSw: Sized { const SW: fn(&mut Self, &mut Self, &mut App); }
    fn sw3<X>(a: &mut X, b: &mut X, _: &mut App) { core::mem::swap(a, b) }
    impl<X: Bound> LocalSw for X { const SW: fn(&mut X, &mut X, &mut App) = sw3::<X>; }
    pub fn churn<T>(a: &mut (T, App), b: &mut (T, App), w: &mut App) where (T, App): LocalSw { (<(T, App) as LocalSw>::SW)(a, b, w) } //~ NOTE this names `declared_const::LocalSw::SW` at the type `(T, declared_const::App)`, which holds a `Cell`, in
}

pub mod declared_phantom {
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
    pub trait LocalSw: Sized { fn sw(&mut self, o: &mut Self, _: core::marker::PhantomData<App>); }
    impl<X: Bound> LocalSw for X { fn sw(&mut self, o: &mut X, _: core::marker::PhantomData<App>) { core::mem::swap(self, o) } }
    pub fn churn<T>(a: &mut (T, App), b: &mut (T, App)) where (T, App): LocalSw { a.sw(b, core::marker::PhantomData) } //~ NOTE this names `declared_phantom::LocalSw::sw` at the type `(T, declared_phantom::App)`, which holds a `Cell`, in
}

pub mod declared_input {
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
    pub trait Effect { fn apply(&self, app: &mut App); }
    pub struct Tick;
    impl Effect for Tick { fn apply(&self, app: &mut App) { app.tick() } }
    pub fn run<E: Effect>(e: &E, app: &mut App) { e.apply(app) } //~ NOTE this names `declared_input::Effect::apply` at the type `&mut declared_input::App`, which holds a `Cell`, in
}

pub mod foreign_trait_local_impl {
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
    pub struct Slot<X>(pub X);
    impl<X> core::ops::AddAssign for Slot<X> { fn add_assign(&mut self, rhs: Slot<X>) { *self = rhs } }
    pub fn churn<T>(a: &mut Slot<(T, App)>, b: Slot<(T, App)>) where Slot<(T, App)>: core::ops::AddAssign { *a += b } //~ NOTE this names `core::ops::arith::AddAssign::add_assign` at the type `Slot<(T, foreign_trait_local_impl::App)>`,
}

pub mod dep_trait_local_impl {
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
    pub struct Mine<P>(core::marker::PhantomData<P>);
    impl<P> seal_dep_sig::Sw for Mine<P> { type Item = P; fn sw(a: &mut P, b: &mut P) { core::mem::swap(a, b) } }
    pub fn churn<K: seal_dep_sig::Sw<Item = (T, App)>, T>(a: &mut (T, App), b: &mut (T, App)) { K::sw(a, b) } //~ NOTE this names `seal_dep_sig::Sw::sw` at the type `&mut (T, dep_trait_local_impl::App)`, which holds a `Cell`, in
}

pub mod local_drop_where {
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
    pub struct Put<'a, X> { val: X, out: &'a mut X }
    impl<'a, X> Drop for Put<'a, X> { fn drop(&mut self) { core::mem::swap(&mut self.val, self.out) } }
    pub fn churn<'a, T>(a: &'a mut (T, App), b: (T, App)) where Put<'a, (T, App)>: Drop { let _g = Put { val: b, out: a }; } //~ NOTE this names `core::ops::drop::Drop::drop` at the type `Put<'_, (T, local_drop_where::App)>`, which holds a
}

pub mod under_trusted_driver {
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
    pub fn churn<K: seal_dep_sig::Sw<Item = (T, App)>, T>(a: &mut (T, App), b: &mut (T, App)) { seal_dep_sig::run::<K>(a, b) } //~ NOTE this names `seal_dep_sig::Sw::sw` at the type `&mut (T, under_trusted_driver::App)`, which holds a `Cell`, in
}

clean {
    import Trust.Binding
    namespace AbstractSig
    open Trust.Protocol
    def local_op_const : Trust.Protocol.Seal := seals "local_op_const::Cell" ["local_op_const::Cell::bump"] ["local_op_const::Cell::new"] ["local_op_const::App::new"] []
    def local_dyn_const : Trust.Protocol.Seal := seals "local_dyn_const::Cell" ["local_dyn_const::Cell::bump"] ["local_dyn_const::Cell::new"] ["local_dyn_const::App::new"] []
    def local_fnptr_method : Trust.Protocol.Seal := seals "local_fnptr_method::Cell" ["local_fnptr_method::Cell::bump"] ["local_fnptr_method::Cell::new"] ["local_fnptr_method::App::new"] []
    def local_impl_fn : Trust.Protocol.Seal := seals "local_impl_fn::Cell" ["local_impl_fn::Cell::bump"] ["local_impl_fn::Cell::new"] ["local_impl_fn::App::new"] []
    def dep_fnptr_method : Trust.Protocol.Seal := seals "dep_fnptr_method::Cell" ["dep_fnptr_method::Cell::bump"] ["dep_fnptr_method::Cell::new"] ["dep_fnptr_method::App::new"] []
    def dep_boxed_method : Trust.Protocol.Seal := seals "dep_boxed_method::Cell" ["dep_boxed_method::Cell::bump"] ["dep_boxed_method::Cell::new"] ["dep_boxed_method::App::new"] []
    def dep_op_const : Trust.Protocol.Seal := seals "dep_op_const::Cell" ["dep_op_const::Cell::bump"] ["dep_op_const::Cell::new"] ["dep_op_const::App::new"] []
    def declared_ctx : Trust.Protocol.Seal := seals "declared_ctx::Cell" ["declared_ctx::Cell::bump"] ["declared_ctx::Cell::new"] ["declared_ctx::App::new"] []
    def declared_const : Trust.Protocol.Seal := seals "declared_const::Cell" ["declared_const::Cell::bump"] ["declared_const::Cell::new"] ["declared_const::App::new"] []
    def declared_phantom : Trust.Protocol.Seal := seals "declared_phantom::Cell" ["declared_phantom::Cell::bump"] ["declared_phantom::Cell::new"] ["declared_phantom::App::new"] []
    def declared_input : Trust.Protocol.Seal := seals "declared_input::Cell" ["declared_input::Cell::bump"] ["declared_input::Cell::new"] ["declared_input::App::new"] []
    def foreign_trait_local_impl : Trust.Protocol.Seal := seals "foreign_trait_local_impl::Cell" ["foreign_trait_local_impl::Cell::bump"] ["foreign_trait_local_impl::Cell::new"] ["foreign_trait_local_impl::App::new"] ["AddAssign::add_assign"]
    def dep_trait_local_impl : Trust.Protocol.Seal := seals "dep_trait_local_impl::Cell" ["dep_trait_local_impl::Cell::bump"] ["dep_trait_local_impl::Cell::new"] ["dep_trait_local_impl::App::new"] ["seal_dep_sig::Sw::sw"]
    def local_drop_where : Trust.Protocol.Seal := seals "local_drop_where::Cell" ["local_drop_where::Cell::bump"] ["local_drop_where::Cell::new"] ["local_drop_where::App::new"] ["Drop::drop"]
    def under_trusted_driver : Trust.Protocol.Seal := seals "under_trusted_driver::Cell" ["under_trusted_driver::Cell::bump"] ["under_trusted_driver::Cell::new"] ["under_trusted_driver::App::new"] ["seal_dep_sig::run"]
    end AbstractSig
}
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.local_op_const` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.local_dyn_const` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.local_fnptr_method` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.local_impl_fn` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.dep_fnptr_method` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.dep_boxed_method` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.dep_op_const` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.declared_ctx` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.declared_const` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.declared_phantom` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.declared_input` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.foreign_trait_local_impl` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.dep_trait_local_impl` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.local_drop_where` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^ ERROR seal `AbstractSig.under_trusted_driver` on `Cell` does not hold
