//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_chain.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6RobF7.cell` holds
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-ROB-F7, a cost that grows with the program (the review's
//! "hang"); lens: robustness). Recorded, not fixed (docs/DECISION_QUEUE.md,
//! "sealed types land with review 6's findings recorded, not fixed").
//! A SMALL INSTANCE: the seal below holds, as it should, but the check walks
//! every instance of the crate once per link of the chain (N+2 walks: 5 here,
//! counted at `checker.walk()` in sealed.rs `check_seals`; 2 for the same
//! items in forward order, `g0` first), where docs/USING_TRUST.md says "The
//! cost is two walks at most, whatever the order". The review's measure,
//! with 150 filler types (171,000 instances a walk; 4.8 s without the seal):
//! 10.8 s at N=1, 19.6 s at N=10, 38.8 s at N=30 in this (reverse) order,
//! 10.3 s at N=30 in forward order.
//! THIS FILE DOES NOT FAIL WHEN THE GAP IS CLOSED: the seal holds either way,
//! and neither the number of walks nor the time is printed (the instance
//! count printed is one walk's). It keeps the shape, small, for whoever fixes
//! it: count the walks as above, then delete this file or give it an
//! observable.
//! The shape: it revives the confirmed R3-ROB-F5 through round 6's rule 3.
//! `check_seals` relies on "which instances are read turns on what their
//! arguments name, never on what a type owns", so `settle_erasures` can
//! finish a chain from the coercion log in two walks. Now `names_local_in`
//! consults `env_mask`, and `env_mask` reads what was erased into a `dyn`
//! named in the bounds (`F: FnMut(&mut dyn T0)`): whether `box_k::<S::Item>`
//! is followed at all, and so whether its coercion is logged, turns on an
//! erasure the previous walk found. `g0` boxes an `App` as `dyn T0`; each
//! `g_k`, bounded by `F: FnMut(&mut dyn T{k-1})`, boxes `S::Item` as `dyn Tk`;
//! each `g_k` is written before `g_{k-1}`.
//! Root, as its skeptic put it: sealed.rs `names_local_in` ends with `local ||
//! (parameter && open.is_some_and(|scope| self.env_mask(scope) != 0))`;
//! `env_mask`'s `ty::Dynamic` arm reads `erased`, `erased_reach`,
//! `erased_foreign` and `dyn_owns`; `settle_erasures` re-reads only the
//! coercions already logged, so each link costs one more pass of the outer
//! loop in `check_seals`.

#![allow(unused)]
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
extern crate seal_gap_chain;
use seal_gap_chain::*;
pub fn g3<S: Src, F: FnMut(&mut dyn T2)>(x: S::Item, f: F) -> Box<dyn T3> where S::Item: T3 + 'static { box_3::<S::Item>(x) }
pub fn g2<S: Src, F: FnMut(&mut dyn T1)>(x: S::Item, f: F) -> Box<dyn T2> where S::Item: T2 + 'static { box_2::<S::Item>(x) }
pub fn g1<S: Src, F: FnMut(&mut dyn T0)>(x: S::Item, f: F) -> Box<dyn T1> where S::Item: T1 + 'static { box_1::<S::Item>(x) }
impl T0 for App {}
pub fn g0(a: App) -> Box<dyn T0> { Box::new(a) }

clean {
    import Trust.Binding
    namespace R6RobF7
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] ["Box::new", "Drop::drop", "seal_gap_chain::T0", "seal_gap_chain::box_1", "seal_gap_chain::T1", "seal_gap_chain::box_2", "seal_gap_chain::T2", "seal_gap_chain::box_3", "seal_gap_chain::T3"]
    end R6RobF7
}
