//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_bodies_built.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_check_build_dep_coroutine.rs`: the same
//! program against the same dependency built in full, whose bodies the
//! collector lists and the check reads, HOLDS (`Trust.Protocol.Seal`):
//! nothing writes a `Cell` but `Cell::bump`. The refusal of its twin is that
//! one unread body, not every check build.

#![allow(unused)]

extern crate seal_dep_bodies_built;

use std::future::Future;
use std::task::{Context, Poll, Waker};

use seal_dep_bodies_built::measure;

pub struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    fn bump(&mut self) { self.n += 1; }
}
pub struct App { cell: Cell }
impl App { fn new() -> Self { App { cell: Cell::new() } } }

/// A type of this crate that owns no `Cell`, as aterm's `Wake` owns none.
pub struct Wake { id: u32 }

/// Polls `future` to its end on this thread.
fn block_on<F: Future>(future: F) -> F::Output {
    let mut future = std::pin::pin!(future);
    let mut cx = Context::from_waker(Waker::noop());
    loop {
        if let Poll::Ready(out) = future.as_mut().poll(&mut cx) {
            return out;
        }
    }
}

fn main() {
    let mut a = App::new();
    a.cell.bump();
    let _ = block_on(measure(Wake { id: 1 }));
}

clean {
    import Trust.Binding
    namespace CheckBuildDepCoroutineHolds
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end CheckBuildDepCoroutineHolds
}
//~^^^ NOTE seal `CheckBuildDepCoroutineHolds.cell` holds
