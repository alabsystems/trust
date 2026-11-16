//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_mutref.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6S4eF3.s` holds
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-S4E-F3, a false pass; lens: foreign-unsafe). Recorded, not
//! fixed (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! The seal below HOLDS with no entry, and a crate that depends on this
//! library swaps two holders through `l6` (a=1 b=0 before, a=0 b=1 after)
//! and overwrites one through `l6s` (a=0 b=0), at -O and at -Copt-level=0.
//! When a fix makes this file fail, that is the win: move the program to a
//! must-fail fixture beside a must-hold twin, and delete this file.
//! The shape: the root of R6-S4E-F1 and R6-S4E-F2 in the library's OWN code.
//! `T: Exactly<App>` is a sealed trait whose only impl is `impl<X> Exactly<X>
//! for X`, so `T` is `App` in every instance (a downstream impl for another
//! type, or a `u32` instance, fails with E0277), and `env_mask` is not zero
//! (the check follows `swap_bytes::<T>` under this bound); yet `T` owns
//! nothing in the open reading: `mem::swap(a, b)` at `T` and a store `*slot =
//! v` at `T` pass. `mem::swap::<App>` written out is refused.
//! Root, as its skeptic put it: sealed.rs `owns_mode` sends a parameter type
//! to `owns_whatever`/`owns_in`, whose `ty::Param` arm adds nothing under
//! `Abstract::Nothing` and never consults `env_mask`; so `handed` sees 0 for
//! `mem::swap::<T>`, and the store judgment sees 0 at `*slot`.

#![allow(unused)]
extern crate seal_gap_mutref as dep;

pub(crate) struct Cell { n: u32 }
impl Cell {
    fn new() -> Self { Cell { n: 0 } }
    pub(crate) fn bump(&mut self) { self.n += 1; }
    pub(crate) fn get(&self) -> u32 { self.n }
}
pub struct App { cell: Cell }
impl App {
    pub fn new() -> Self { App { cell: Cell::new() } }
    pub fn bump(&mut self) { self.cell.bump() }
    pub fn get(&self) -> u32 { self.cell.get() }
}
pub fn l6<T: dep::Exactly<App>>(a: &mut T, b: &mut T) { ::core::mem::swap(a, b) }
pub fn l6s<T: dep::Exactly<App>>(slot: &mut T, v: T) { *slot = v; }

// A crate that depends on this one (not compiled here):
//     let (mut a, mut b) = (App::new(), App::new()); a.bump();
//     l6::<App>(&mut a, &mut b);       // a.get() == 0, b.get() == 1
//     l6s::<App>(&mut b, App::new());  // b.get() == 0

clean {
    import Trust.Binding
    namespace R6S4eF3
    open Trust.Protocol
    def s : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end R6S4eF3
}
