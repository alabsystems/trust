//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_comp.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6DynF3.store` holds
//@ error-pattern: seal `R6DynF3.swap` holds
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-DYN-F3, a false pass; lens: dyn-trusts). Recorded, not
//! fixed (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! Each seal below HOLDS, and this crate's own code replaces (`x = y`) or
//! swaps (`mem::swap`, not trusted) two `Box<dyn Any>` that each hold an
//! `App` (`x` comes back holding id=2 n=0, where it held id=1 n=1), with the
//! dependency at -O and at -Copt-level=0. When a fix makes this file fail,
//! that is the win: move the program to a must-fail fixture beside a
//! must-hold twin, and delete this file.
//! The shape: a sibling of R5-DYN-F2 (fixed for upcasts the walk sees). A
//! holder behind a TRUSTED `dyn Component` (another crate's trait, named in
//! `trusts`) is upcast to an UNtrusted `Box<dyn Any>` by `into_any`, a fn of
//! the dependency that is not generic and that the walk never reads, so
//! nothing records that a `dyn Any` holds one. The same upcast written in
//! this crate, or in a GENERIC fn of the dependency, is refused (it asks for
//! `any::Any`); so is `mem::swap` of the two `Box<dyn Component>`.
//! docs/USING_TRUST.md: such an upcast "is a holder handed to that `dyn`,
//! refused unless that trait is named too".
//! Root, as its skeptic put it: sealed.rs `handed` iterates only
//! `instance.args.types()`, and `reach` enqueues a foreign instance only when
//! its arguments name something local, so the non-generic `into_any` gets no
//! S4b question and its upcast never reaches `record_erasure`:
//! `erased_foreign_held[Any]` stays 0 and `dyn_owns(Any)` is 0, against the
//! invariant stated on `erased_foreign_held` ("upcast to a dyn of a supertrait").

#![allow(unused)]
extern crate seal_gap_comp as comp;
use std::any::Any;

mod store {
    pub struct Cell { n: u32 }
    impl Cell { pub fn new() -> Self { Cell { n: 0 } } pub fn bump(&mut self) { self.n += 1; } pub fn get(&self) -> u32 { self.n } }
    pub struct App { cell: Cell, pub id: u8 }
    impl App { pub fn new(id: u8) -> Self { App { cell: Cell::new(), id } } pub fn tick(&mut self) { self.cell.bump() } pub fn n(&self) -> u32 { self.cell.get() } }
    impl crate::comp::Component for App {}
    pub fn run() -> Box<dyn std::any::Any> {
        let mut first = App::new(1);
        first.tick();
        let cx: Box<dyn crate::comp::Component> = Box::new(first);
        let cy: Box<dyn crate::comp::Component> = Box::new(App::new(2));
        let mut x: Box<dyn std::any::Any> = crate::comp::into_any(cx);
        let y: Box<dyn std::any::Any> = crate::comp::into_any(cy);
        x = y;
        x
    }
}
mod swap {
    pub struct Cell { n: u32 }
    impl Cell { pub fn new() -> Self { Cell { n: 0 } } pub fn bump(&mut self) { self.n += 1; } pub fn get(&self) -> u32 { self.n } }
    pub struct App { cell: Cell, pub id: u8 }
    impl App { pub fn new(id: u8) -> Self { App { cell: Cell::new(), id } } pub fn tick(&mut self) { self.cell.bump() } pub fn n(&self) -> u32 { self.cell.get() } }
    impl crate::comp::Component for App {}
    pub fn run() -> Box<dyn std::any::Any> {
        let mut first = App::new(1);
        first.tick();
        let cx: Box<dyn crate::comp::Component> = Box::new(first);
        let cy: Box<dyn crate::comp::Component> = Box::new(App::new(2));
        let mut x: Box<dyn std::any::Any> = crate::comp::into_any(cx);
        let mut y: Box<dyn std::any::Any> = crate::comp::into_any(cy);
        std::mem::swap(&mut x, &mut y);
        x
    }
}
fn main() {
    let _ = store::run();
    let _ = swap::run();
}
clean {
    import Trust.Binding
    namespace R6DynF3
    open Trust.Protocol
    def store : Trust.Protocol.Seal := seals "store::Cell" ["store::Cell::bump"] ["store::Cell::new"] ["store::App::new"] ["seal_gap_comp::Component", "boxed::Box::new", "Component::label", "Any::type_id", "Box::drop"]
    def swap : Trust.Protocol.Seal := seals "swap::Cell" ["swap::Cell::bump"] ["swap::Cell::new"] ["swap::App::new"] ["seal_gap_comp::Component", "boxed::Box::new", "Component::label", "Any::type_id", "Box::drop"]
    end R6DynF3
}
