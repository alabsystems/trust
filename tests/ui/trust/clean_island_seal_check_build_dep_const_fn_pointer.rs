//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_bodies_checked.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A seal checked against a dependency built for `check` (`--emit=metadata`),
//! where the compiler's own collector, asked what a body uses, lists a body
//! of that dependency whose MIR its metadata does not carry: the dependency's
//! `async fn measure_through`, made at `Wake` and polled here: its coroutine
//! (whose MIR the metadata does carry) calls `tick` through the constant
//! `TICK`, a fn pointer the collector finds in the constant's value. The
//! `async fn` itself is the unread body. Before, the collector stopped the
//! build there ("missing optimized MIR", which names no seal). Now it lists
//! that body as it lists one whose MIR is there, and the seal must FAIL
//! saying which body could not be read (`Trust.Protocol.Seal`). (Every seal
//! is refused where this happens: this file has one.) Built in full, the same
//! dependency holds:
//! `clean_island_seal_check_build_dep_const_fn_pointer_holds.rs`. No rule was
//! relaxed for it.

#![allow(unused)]

extern crate seal_dep_bodies_checked;

use std::future::Future;
use std::task::{Context, Poll, Waker};

use seal_dep_bodies_checked::measure_through;

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
    let _ = block_on(measure_through(Wake { id: 1 })); //~ NOTE the body of `seal_dep_bodies_checked::measure_through`, which the metadata of its crate does not carry
}

clean {
    import Trust.Binding
    namespace CheckBuildDepConstFnPointer
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end CheckBuildDepConstFnPointer
}
//~^^^ ERROR seal `CheckBuildDepConstFnPointer.cell` on `Cell` does not hold
