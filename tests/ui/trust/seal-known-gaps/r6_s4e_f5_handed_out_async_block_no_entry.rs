//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_peek_block.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6S4eF5.block` on `Cell` does not hold
//@ error-pattern: this runs a closure (or an `async` block) in `seal_gap_peek_block::peek_block`, of a crate outside the standard library
//@ error-pattern: (a `trusts` entry names no closure: a trust of a fn of its own crate that runs it covers it)
//@ error-pattern: seal `R6S4eF5.async_fn` holds
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-S4E-F5, a true program refused; lens: foreign-unsafe).
//! Recorded, not fixed (docs/DECISION_QUEUE.md, "sealed types land with
//! review 6's findings recorded, not fixed").
//! The seal `block` is REFUSED, with no entry that can make it hold, and the
//! program is true (the dependency's `unsafe` reads one byte and writes
//! nothing; no `Cell` changes). The file passes while it is refused for that
//! reason; the day it holds (or the refusal becomes a listed cost whose note
//! says no entry answers it), the file fails: that is the win. Move the
//! program to the fixture that fits, and delete this file.
//! The shape: a sound dependency fn that RETURNS an `async` block, `fn
//! peek_block(a) -> impl Future { async move { unsafe { .. } } }`, the
//! long-hand of `async fn` and the usual way to write a `'static` or `Send`
//! future, is refused at the block's body (S4e) whoever polls it: this crate's
//! own `pin!` and `Future::poll` here; a third crate's `block_on` in the
//! review, even with every fn on the way trusted. The note's remedy ("a
//! trust of a fn of its own crate that runs it covers it") does not exist: no
//! fn of that crate runs the future. The identical `async fn` holds on its
//! own entry (`async_fn`), as docs/USING_TRUST.md says ("an `async fn`'s body
//! is the fn's, wherever its future is polled"). The listed no-entry cost is
//! for a closure "made a fn pointer or a `dyn` in that crate's code"; a
//! returned `impl Future` is neither. (A closure returned as `impl FnMut` and
//! called here is refused the same way, the shape review 2 made must-fail.)
//! Root, as its skeptic put it: sealed.rs `trust_item` maps only
//! `CoroutineSource::Fn` to its fn ("None for a closure or an `async` block"),
//! and `chosen` strips the trusts from closure-like bodies; the user doc does
//! not list that choice for a handed-out `async` block.

#![allow(unused)]
extern crate seal_gap_peek_block as dep;

mod block {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub struct Mark;
    impl dep::Make for Mark { type Out = App; }
    pub fn run() -> u32 {
        let mut x = App::new();
        x.cell.bump();
        {
            let mut f = ::core::pin::pin!(dep::peek_block::<Mark>(&mut x));
            let mut cx = ::core::task::Context::from_waker(::core::task::Waker::noop());
            let _ = ::core::future::Future::poll(f.as_mut(), &mut cx);
        }
        x.cell.get()
    }
}
mod async_fn {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub struct Mark;
    impl dep::Make for Mark { type Out = App; }
    pub fn run() -> u32 {
        let mut x = App::new();
        x.cell.bump();
        {
            let mut f = ::core::pin::pin!(dep::peek_async::<Mark>(&mut x));
            let mut cx = ::core::task::Context::from_waker(::core::task::Waker::noop());
            let _ = ::core::future::Future::poll(f.as_mut(), &mut cx);
        }
        x.cell.get()
    }
}
fn main() {
    block::run();
    async_fn::run();
}
clean {
    import Trust.Binding
    namespace R6S4eF5
    open Trust.Protocol
    def block : Trust.Protocol.Seal := seals "block::Cell" ["block::Cell::bump"] ["block::Cell::new"] ["block::App::new"] ["seal_gap_peek_block::peek_block", "DerefMut::deref_mut"]
    def async_fn : Trust.Protocol.Seal := seals "async_fn::Cell" ["async_fn::Cell::bump"] ["async_fn::Cell::new"] ["async_fn::App::new"] ["seal_gap_peek_block::peek_async", "DerefMut::deref_mut"]
    end R6S4eF5
}
