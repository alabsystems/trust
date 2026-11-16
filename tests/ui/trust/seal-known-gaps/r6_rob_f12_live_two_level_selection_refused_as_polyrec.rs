//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6RobF12.cell` on `Cell` does not hold
//@ error-pattern: the crate names `Tr::m`, at types the compiler's trait solver cannot settle within the recursion limit (128) (as polymorphic recursion makes, `grow(W(x))`
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-ROB-F12, a true program refused; lens: robustness).
//! Recorded, not fixed (docs/DECISION_QUEUE.md, "sealed types land with
//! review 6's findings recorded, not fixed").
//! The seal below is REFUSED, and the program is true: rustc builds the file
//! and codegens `mx`, resolving `Tr::m` at `W<W<W64<u8>>>` (a type 67 deep,
//! below the depth cap of 128); with `#![recursion_limit = "256"]` the seal
//! holds. The note says this is polymorphic recursion in code nothing calls,
//! and none of that is so: the code is live, not generic, not recursive. The
//! file passes while it is refused for that reason; the day it holds (or the
//! refusal becomes a listed cost with a note that says what it is), the file
//! fails: that is the win. Move the program to the fixture that fits, and
//! delete this file.
//! The shape: impl selection that nests two obligation levels per level of
//! `W` (`impl<T> Tr for W<T> where V<T>: Tr`); the smaller `m1`..`m6` fill the
//! compiler's evaluation cache, so its own resolve at the deep type succeeds
//! (rustc's acceptance is fragile: delete `m1`..`m6`, or move `mx` above them,
//! and rustc itself stops with E0275). docs/USING_TRUST.md lists this refusal
//! under POLYMORPHIC RECURSION; for live code it lists only "a live type
//! nested more than 128 deep".
//! Root, as its skeptic put it: sealed.rs `solver_overflows` builds a fresh
//! inference context and re-selects every nested obligation from scratch in
//! canonical mode, with no cache across calls; `W^66` costs about 132 levels,
//! so the walk overflows at 128, where rustc's fulfilment answered the same
//! global predicates from the evaluation cache.

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
pub trait Tr { fn m(&self) -> u32; }
impl Tr for u8 { fn m(&self) -> u32 { 1 } }
pub struct V<T>(pub T);
pub struct W<T>(pub T);
impl<T: Tr> Tr for V<T> { fn m(&self) -> u32 { self.0.m() } }
impl<T> Tr for W<T> where V<T>: Tr { fn m(&self) -> u32 { 2 } }
pub type W1<T> = W<T>;
pub type W2<T> = W1<W1<T>>;
pub fn m1(x: &W2<u8>) -> u32 { x.m() }
pub type W4<T> = W2<W2<T>>;
pub fn m2(x: &W4<u8>) -> u32 { x.m() }
pub type W8<T> = W4<W4<T>>;
pub fn m3(x: &W8<u8>) -> u32 { x.m() }
pub type W16<T> = W8<W8<T>>;
pub fn m4(x: &W16<u8>) -> u32 { x.m() }
pub type W32<T> = W16<W16<T>>;
pub fn m5(x: &W32<u8>) -> u32 { x.m() }
pub type W64<T> = W32<W32<T>>;
pub fn m6(x: &W64<u8>) -> u32 { x.m() }

pub fn mx(x: &W<W<W64<u8>>>) -> u32 { x.m() }

clean {
    import Trust.Binding
    namespace R6RobF12
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end R6RobF12
}
