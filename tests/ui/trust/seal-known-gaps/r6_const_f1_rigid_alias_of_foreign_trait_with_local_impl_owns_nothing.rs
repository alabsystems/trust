//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_projdep.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6ConstF1.s` holds
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-CONST-F1, a false pass; lens: constants). Recorded, not
//! fixed (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! The seal below HOLDS, and a crate that depends on this library and only
//! calls its pub fns swaps two holders through every one of them (a holder
//! whose `Cell` was bumped twice and one at 0 come back 0 and 2). When a fix
//! makes this file fail, that is the win: move the program to a must-fail
//! fixture beside a must-hold twin, and delete this file.
//! The shape: in a library's open reading, a RIGID projection of ANOTHER
//! crate's trait is taken to own nothing, also where the impl that settles it
//! is THIS crate's own: (1) `T::Out` with this crate's `impl Proj for Mine {
//! type Out = (Mine, App); }`, handed to a constant whose value is `mem::swap`,
//! to `mem::swap`, and stored; (2) a where-clause the compiler does not need
//! keeps `<Mine as Proj2<T>>::Out` rigid, which by this crate's `impl<T>
//! Proj2<T> for Mine` IS `(T, App)` (R5-CONST-F5's shape, with a dependency's
//! trait); (3) this crate's `impl<T> Proj2<Key> for Vec<T>`, picked by a
//! downstream `K = Vec<u8>`; (4) std's `DerefMut`, by this crate's impl for a
//! handle (`P::Target`); (5) a CONSTANT of another crate's trait whose impl
//! `K` picks (`K::SW`), handed the projection of (1), which docs/USING_TRUST.md
//! says "cannot be named, and refuses". The same code with the traits
//! declared in this crate is refused at each, and `churn_2` without its
//! where-clause is refused at `(T, App)`.
//! Root, as its skeptic put it: sealed.rs `Checker::alias_mask` consults
//! this crate's impls of a projection's trait (`local_assoc_mask`, which reads
//! `all_local_trait_impls`, foreign traits' impls too) only when the trait is
//! local; `env_mask` gives 0 for these bounds and `names_local_in` treats a
//! foreign alias as not local. The abstract-item rule (`implemented_here`)
//! already counts this crate's impls of a foreign trait as its own code, so
//! the two rules disagree.

#![allow(unused)]
extern crate seal_gap_projdep as projdep;

pub mod m {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
        pub(crate) fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
        pub fn n(&self) -> u32 { self.cell.get() }
    }
    pub struct Tab<X>(core::marker::PhantomData<X>);
    impl<X> Tab<X> { pub const SW: fn(&mut X, &mut X) = core::mem::swap::<X>; }

    // (1) a parameter's projection: this crate's impl makes it a holder.
    pub struct Mine;
    impl projdep::Proj for Mine { type Out = (Mine, App); }
    pub fn churn_1<T: projdep::Proj>(a: &mut T::Out, b: &mut T::Out) { (Tab::<T::Out>::SW)(a, b) }
    pub fn swap_1<T: projdep::Proj>(a: &mut T::Out, b: &mut T::Out) { core::mem::swap(a, b) }
    pub fn store_1<T: projdep::Proj>(a: &mut T::Out, b: T::Out) { *a = b }

    // (2) whatever T is, the projection IS (T, App).
    impl<T> projdep::Proj2<T> for Mine { type Out = (T, App); }
    pub fn churn_2<T>(a: &mut <Mine as projdep::Proj2<T>>::Out, b: &mut <Mine as projdep::Proj2<T>>::Out)
        where Mine: projdep::Proj2<T> { (Tab::<<Mine as projdep::Proj2<T>>::Out>::SW)(a, b) }

    // (3) this crate's impl for std's Vec<T>: a downstream crate picks K = Vec<u8>.
    pub struct Key;
    impl<T> projdep::Proj2<Key> for Vec<T> { type Out = (Vec<T>, App); }
    pub fn churn_3<K: projdep::Proj2<Key>>(a: &mut K::Out, b: &mut K::Out) { (Tab::<K::Out>::SW)(a, b) }

    // (4) std's DerefMut, this crate's impl for a handle of its own.
    pub struct Handle(App);
    impl Handle { pub fn new() -> Self { Handle(App::new()) } pub fn app(&mut self) -> &mut App { &mut self.0 } }
    impl core::ops::Deref for Handle { type Target = App; fn deref(&self) -> &App { &self.0 } }
    impl core::ops::DerefMut for Handle { fn deref_mut(&mut self) -> &mut App { &mut self.0 } }
    pub fn churn_4<P: core::ops::DerefMut>(p: &mut P, q: &mut P) where P::Target: Sized {
        (Tab::<P::Target>::SW)(&mut **p, &mut **q)
    }

    // (5) a constant of another crate's trait whose impl a parameter picks.
    pub fn churn_5<T: projdep::Proj, K: projdep::Sw<Item = T::Out>>(a: &mut T::Out, b: &mut T::Out) { (K::SW)(a, b) }
}

// A crate that depends on this one (not compiled here) only calls its pub fns,
// and each call swaps the two holders (a=0 b=2 after, where `a` held a `Cell`
// bumped twice):
//     let mut a = (Mine, App::new()); a.1.tick(); a.1.tick();
//     let mut b = (Mine, App::new());
//     churn_1::<Mine>(&mut a, &mut b);
//     churn_2::<u8>(&mut c, &mut d);                // c, d: (u8, App)
//     churn_3::<Vec<u8>>(&mut e, &mut f);           // e, f: (Vec<u8>, App)
//     churn_4(&mut h, &mut k);                      // h, k: Handle
//     churn_5::<Mine, projdep::By<(Mine, App)>>(&mut a, &mut b);

clean {
    import Trust.Binding
    namespace R6ConstF1
    open Trust.Protocol
    def s : Trust.Protocol.Seal := seals "m::Cell" ["m::Cell::bump"] ["m::Cell::new"] ["m::App::new"] []
    end R6ConstF1
}
