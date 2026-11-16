//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6RobF1.cell` on `Cell` does not hold
//@ error-pattern: this names `Visitor::visit` at the type `<V as Visitor>::Out`, which holds a `Cell`, in `twice`, where the compiler names no one body for it
//@ error-pattern: this puts a value of type `<V as Visitor>::Out`, which holds a `Cell`, where one may already be, in `twice`
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-ROB-F1, a true program refused; lens: robustness). Recorded,
//! not fixed (docs/DECISION_QUEUE.md, "sealed types land with review 6's
//! findings recorded, not fixed").
//! The seal below is REFUSED, and the program is true: the generic code never
//! names `App` or `Cell`, and every impl of the trait forwards the associated
//! type. The same generic fn without the forwarding impl holds, and the
//! review-5 build held this file. The file passes while it is refused for
//! that reason; the day it holds, the file fails: that is the win. Move the
//! program to a must-hold fixture and delete this file.
//! The shape: an impl of this crate that FORWARDS a local trait's associated
//! type to itself (`impl<V: Visitor> Visitor for &mut V { type Out = V::Out;
//! }`; the review found the same with a `Stream` adapter `type Item =
//! S::Item`, a GAT `type Item<'a> = L::Item<'a>`, an RPITIT or `async fn` in a
//! trait wrapper, `type Arr = (T::Arr, T::Arr)`) makes every rigid
//! `<V as Visitor>::Out` in an open reading hold every sealed type: its store,
//! its drop and the abstract `Visitor::visit` are refused, some notes saying
//! no `trusts` entry answers it.
//! Root, as its skeptic put it: sealed.rs `local_assoc_mask` inserts the
//! provisional "every seal" into `assoc_links` first, then reads each impl's
//! value; `V::Out` reaches `alias_mask`, which asks `local_assoc_mask` of the
//! same item again and gets the provisional answer, and that is kept as the
//! final one: nothing iterates to a least fixpoint.

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
pub trait Visitor { type Out; fn visit(&mut self, n: u32) -> Self::Out; }
impl<V: Visitor + ?Sized> Visitor for &mut V { type Out = V::Out; fn visit(&mut self, n: u32) -> V::Out { (**self).visit(n) } }
pub fn twice<V: Visitor>(v: &mut V) -> V::Out { let mut r = v.visit(1); r = v.visit(2); r }

clean {
    import Trust.Binding
    namespace R6RobF1
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end R6RobF1
}
