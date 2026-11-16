//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_jsw.rs
//@ aux-build: seal_gap_jguard.rs
//@ aux-build: seal_gap_ksw.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6ConstF3.blanket` holds
//@ error-pattern: seal `R6ConstF3.guard` holds
//@ error-pattern: seal `R6ConstF3.picked` holds
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-CONST-F3, a false pass; lens: constants). Recorded, not
//! fixed (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! Each seal below HOLDS, and a crate that depends on this library swaps two
//! `(T, App)` holders through each `churn` (a=2 b=0 before, a=0 b=2 after).
//! When a fix makes this file fail, that is the win: move the program to a
//! must-fail fixture beside a must-hold twin, and delete this file.
//! The shape: an ABSTRACT impl (the compiler names no one body) of a trait
//! of ANOTHER crate that this crate does not implement is covered by the
//! `trusts` entry that names it, and nothing beneath it is read; but the impl
//! that runs calls THIS crate's own impl of a different trait, which swaps.
//! `blanket`: the dependency's blanket `impl<X: Base> HasSw for X` runs this
//! crate's `impl<X> Base for Wrap<X>`, and a where-clause keeps
//! `<Wrap<(T, App)> as HasSw>::sw` abstract; the entry for `HasSw::sw` is the
//! one the note asks for (spelled with its crate here, so that the two
//! dependencies' `HasSw::sw` are told apart). `guard`: the dependency's
//! `impl<X: Hook> Drop for Guard<X>` runs this crate's `Hook::on_drop`
//! (entries `Drop::drop`, `mem::drop`; the crate has no `Drop` impl of its
//! own). `picked`: no
//! where-clause, R5-ROB-F2's own shape `K: HasSw<Item = (T, App)>` with
//! `K::sw(a, b)`, where a downstream crate picks `K = Mine<(u8, App)>`, whose
//! `Base` impl is this crate's. The note of a seal that holds says the word
//! covers "what its own crate and the standard library run beneath it": this
//! crate's impl is neither. Without the where-clause the compiler picks the
//! dependency's impl, the walk follows it into this crate's and refuses at
//! the swap, with the same entry.
//! Root, as its skeptic put it: sealed.rs `Checker::unresolved` takes `ours =
//! def.is_local() || implemented_here(trait_of_assoc(def))`, which looks only
//! at the abstract item's own trait; otherwise the call is `Site::Foreign`,
//! covered by `trusting(def)`, which never considers this crate's impls of
//! OTHER traits that the foreign impl may dispatch to.

#![allow(unused)]
extern crate seal_gap_jsw as jsw;
extern crate seal_gap_jguard as jguard;
extern crate seal_gap_ksw as ksw;

pub mod blanket {
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
    pub struct Wrap<X>(pub X);
    impl<X> jsw::Base for Wrap<X> {
        fn base_sw(a: &mut Self, b: &mut Self) { core::mem::swap(a, b) }
        const BASE_SW: fn(&mut Self, &mut Self) = core::mem::swap::<Self>;
    }
    pub fn churn<T>(a: &mut Wrap<(T, App)>, b: &mut Wrap<(T, App)>) where Wrap<(T, App)>: jsw::HasSw {
        <Wrap<(T, App)> as jsw::HasSw>::sw(a, b)
    }
}

pub mod guard {
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
    pub struct Pair<'a, X>(pub &'a mut X, pub &'a mut X);
    impl<'a, X> jguard::Hook for Pair<'a, X> {
        fn on_drop(&mut self) { core::mem::swap(self.0, self.1) }
    }
    pub fn churn<'a, T>(a: &'a mut (T, App), b: &'a mut (T, App)) where jguard::Guard<Pair<'a, (T, App)>>: Drop {
        drop(jguard::Guard(Pair(a, b)))
    }
}

pub mod picked {
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
    impl<P> ksw::Base for Mine<P> { type Item = P; fn base_sw(a: &mut P, b: &mut P) { core::mem::swap(a, b) } }
    pub fn churn<T, K: ksw::HasSw<Item = (T, App)>>(a: &mut (T, App), b: &mut (T, App)) { K::sw(a, b) }
}

clean {
    import Trust.Binding
    namespace R6ConstF3
    open Trust.Protocol
    def blanket : Trust.Protocol.Seal := seals "blanket::Cell" ["blanket::Cell::bump"] ["blanket::Cell::new"] ["blanket::App::new"] ["seal_gap_jsw::HasSw::sw"]
    def guard : Trust.Protocol.Seal := seals "guard::Cell" ["guard::Cell::bump"] ["guard::Cell::new"] ["guard::App::new"] ["Drop::drop", "mem::drop"]
    def picked : Trust.Protocol.Seal := seals "picked::Cell" ["picked::Cell::bump"] ["picked::Cell::new"] ["picked::App::new"] ["seal_gap_ksw::HasSw::sw"]
    end R6ConstF3
}
