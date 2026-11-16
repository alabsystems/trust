//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6ConstF4.s` on `Cell` does not hold: 3 statement(s) break it
//@ error-pattern: this names `m::Show::show` at the type `dyn Show<(T, App)>`, which holds a `Cell`, in `m::show_dyn`, where the compiler names no one body for it
//@ error-pattern: this names `m::Show::show` at the type `dyn Show<(T, App)>`, which holds a `Cell`, in `m::show_box`, where the compiler names no one body for it
//@ error-pattern: this names `m::Sink::put` at the type `dyn m::Sink<Item = (T, App)>`, which holds a `Cell`, in `m::sink_dyn`, where the compiler names no one body for it
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-CONST-F4, a true program refused; lens: constants).
//! Recorded, not fixed (docs/DECISION_QUEUE.md, "sealed types land with
//! review 6's findings recorded, not fixed").
//! The seal below is REFUSED at three statements, and the library is true:
//! every impl only measures (`size_of`). The same calls at `u8` for `T` hold.
//! The file passes while the seal is refused for that reason; the day it
//! holds, the file fails: that is the win. Move the program to a must-hold
//! fixture and delete this file.
//! The shape: in a library's generic code, a call through a `dyn` of a trait
//! of THIS crate whose trait arguments name the fn's parameter beside a holder
//! (`o.show(a)` on `&dyn Show<(T, App)>` or `Box<dyn Show<(T, App)>>`,
//! `o.put(a)` on `&mut dyn Sink<Item = (T, App)>`) is refused as an abstract
//! impl "that a where-clause or a type parameter picks", with no entry to
//! answer it. Neither picks it: the call goes through the vtable, and a
//! `dyn`'s methods are read where the `dyn` is made. docs/USING_TRUST.md gives
//! "call it through a `dyn` of the trait" as the REMEDY for exactly this
//! refusal; it works for `&mut dyn LocalM` (`size_dyn`, whose trait names no
//! parameter) and not here.
//! Root, as its skeptic put it: rustc's own resolver returns `None` for a
//! vtable entry whose trait ref still names a parameter
//! (compiler/rustc_ty_utils/src/instance.rs, the Object branch: "We only
//! resolve totally substituted vtable entries"); sealed.rs `Checker::resolve`
//! takes that `Ok(None)` for an abstract impl (`Resolved::Open`), and
//! `Checker::unresolved` records `Site::Picked` for a trait of this crate.

#![allow(unused)]
pub mod m {
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
    // (a) the documented remedy for `where (T, App): LocalM`: a `dyn` of the trait. Holds.
    pub trait LocalM { fn m(&mut self) -> usize; }
    impl<X: Bound> LocalM for X { fn m(&mut self) -> usize { core::mem::size_of::<X>() } }
    pub fn size_dyn<T>(a: &mut (T, App)) -> usize { let d: &mut dyn LocalM = a; d.m() }
    // (b) a trait generic at the parameter: a `&dyn Show<(T, App)>` handed in.
    pub trait Show<X> { fn show(&self, a: &mut X) -> usize; }
    pub struct P;
    impl<X> Show<X> for P { fn show(&self, a: &mut X) -> usize { core::mem::size_of::<X>() } }
    pub fn show_dyn<T: 'static>(o: &dyn Show<(T, App)>, a: &mut (T, App)) -> usize { o.show(a) }
    // (c) the same, boxed and made here.
    pub fn show_box<T: 'static>(a: &mut (T, App)) -> usize { let o: Box<dyn Show<(T, App)>> = Box::new(P); o.show(a) }
    // (d) a `dyn` of a trait of this crate with an associated type bound to it.
    pub trait Sink { type Item; fn put(&mut self, x: &Self::Item) -> usize; }
    pub struct Measure<X>(core::marker::PhantomData<X>);
    impl<X> Sink for Measure<X> { type Item = X; fn put(&mut self, _x: &X) -> usize { core::mem::size_of::<X>() } }
    pub fn sink_dyn<T>(o: &mut dyn Sink<Item = (T, App)>, a: &(T, App)) -> usize { o.put(a) }
}
clean {
    import Trust.Binding
    namespace R6ConstF4
    open Trust.Protocol
    def s : Trust.Protocol.Seal := seals "m::Cell" ["m::Cell::bump"] ["m::Cell::new"] ["m::App::new"] ["Box::new", "Box::drop"]
    end R6ConstF4
}
