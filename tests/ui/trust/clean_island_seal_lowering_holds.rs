//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_lowered.rs
//@ aux-build: seal_dep_lowered0.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! What the compiler lowers SAFE code of a dependency into is not that
//! dependency's `unsafe` (`Trust.Protocol.Seal`): the seal HOLDS, with the
//! dependency built with and without optimization. Review 2 of the review-14
//! build: each call below refused the seal, the dependency forbidding
//! `unsafe` all the while: `eprintln!` and an `assert!` message (a call of
//! the `unsafe fn` `fmt::Arguments::new`), an `async fn` (a transmute of its
//! resume argument), a move out of a `Box` (a transmute of its pointer, and
//! a debug build's alignment checks), std's `pin!` (a call of
//! `Pin::new_unchecked`). What counts as a crate's `unsafe` is what its
//! source says (the fact its own compiler recorded beside its MIR), and what
//! a macro of std wrote is std's.
//!
//! With `unsafe` in the dependency's source: `_lowering.rs`.

#![allow(unused)]

extern crate seal_dep_lowered;
extern crate seal_dep_lowered0;

mod lowered {
    use std::future::Future;
    use std::task::{Context, Poll, Waker};
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    fn block_on<F: Future>(f: F) -> F::Output {
        let mut f = std::pin::pin!(f);
        let mut cx = Context::from_waker(Waker::noop());
        loop {
            if let Poll::Ready(v) = f.as_mut().poll(&mut cx) {
                return v;
            }
        }
    }
    pub fn run() {
        let mut app = App::new();
        seal_dep_lowered::with_retry(|| { app.cell.bump(); app.cell.get() > 2 }, 5);
        seal_dep_lowered::checked(|| { app.cell.bump(); app.cell.get() });
        let mut r: &mut App = &mut app;
        block_on(seal_dep_lowered::measure(&mut r));
        let r: &mut App = seal_dep_lowered::unbox(Box::new(&mut app));
        r.cell.bump();
        let r = &mut app;
        seal_dep_lowered::poll_once(async move { r.cell.bump(); });
        seal_dep_lowered0::with_retry(|| { app.cell.bump(); app.cell.get() > 2 }, 5);
        seal_dep_lowered0::checked(|| { app.cell.bump(); app.cell.get() });
        let mut r: &mut App = &mut app;
        block_on(seal_dep_lowered0::measure(&mut r));
        let r: &mut App = seal_dep_lowered0::unbox(Box::new(&mut app));
        r.cell.bump();
        let r = &mut app;
        seal_dep_lowered0::poll_once(async move { r.cell.bump(); });
    }
}

fn main() {
    lowered::run();
}

clean {
    import Trust.Binding
    namespace LoweringHold
    open Trust.Protocol
    def lowered : Trust.Protocol.Seal := seals "lowered::Cell" ["lowered::Cell::bump"] ["lowered::Cell::new"] ["lowered::App::new"] []
    end LoweringHold
}
