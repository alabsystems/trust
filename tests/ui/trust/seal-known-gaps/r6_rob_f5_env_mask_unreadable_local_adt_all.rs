//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6RobF5.cell` on `Cell` does not hold
//@ error-pattern: this puts a value of type `Option<<I as Iterator>::Item>`, which holds a `Cell`, where one may already be, in `drive`
//@ error-pattern: this runs `core::iter::traits::iterator::Iterator::next`, a fn of another crate, at the type `Option<<I as Iterator>::Item>`, which holds a `Cell`, in `Peek::with`
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-ROB-F5, a true program refused; lens: robustness). Recorded,
//! not fixed (docs/DECISION_QUEUE.md, "sealed types land with review 6's
//! findings recorded, not fixed").
//! The seal below is REFUSED, and the program is true: the generic code never
//! names `App`, and `Peek<I>` holds no sealed value. The same statements with
//! the callback bound on `&mut I` hold, and so does the review-5 build. The
//! file passes while it is refused for that reason; the day it holds, the
//! file fails: that is the win. Move the program to a must-hold fixture and
//! delete this file.
//! The shape: a bound that names a LOCAL generic struct whose definition the
//! summary cannot read (a field `Option<I::Item>`, as in any iterator adapter
//! `struct Peek<I: Iterator> { it: I, cur: Option<I::Item> }`): `F:
//! FnMut(&mut Peek<I>)` (`drive`), or the common `fn with<R, F: FnOnce(&mut
//! Self) -> R>(&mut self, f: F)` inside `impl<I: Iterator> Peek<I>`, makes every
//! rigid projection in the fn hold every sealed type: a store of
//! `Option<I::Item>`, the drop of an `I::Item`, `Iterator::next` are refused,
//! the notes saying these types hold a `Cell`. docs/USING_TRUST.md's cost is
//! for bounds that tie a parameter to a HOLDER (`F: FnOnce(&mut App)`).
//! Root, as its skeptic put it: sealed.rs `Checker::env_mask` takes, for a
//! local ADT in a caller bound, `self.owns_summary(adt.did()).unwrap_or(all)`;
//! `owns_summary` walks each field through `owns_defined_in`, which returns
//! `None` for a `ty::Alias` (where it accepts a `ty::Param`), so the field
//! `Option<I::Item>` makes the answer "every seal". With the field
//! `Option<I>` the seal holds.

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
pub struct Peek<I: Iterator> { pub it: I, pub cur: Option<I::Item> }
pub fn drive<I: Iterator, F: FnMut(&mut Peek<I>)>(p: &mut Peek<I>, mut f: F) -> usize { f(p); let mut last = p.it.next(); last = p.it.next(); last.is_some() as usize }
impl<I: Iterator> Peek<I> {
    pub fn advance(&mut self) { self.cur = self.it.next(); }
    pub fn with<R, F: FnOnce(&mut Self) -> R>(&mut self, f: F) -> R { let mut seen = 0; for _x in self.it.by_ref().take(2) { seen += 1; } f(self) }
}

clean {
    import Trust.Binding
    namespace R6RobF5
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end R6RobF5
}
