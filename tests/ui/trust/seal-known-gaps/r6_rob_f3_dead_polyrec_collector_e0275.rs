//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_odep.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: overflow evaluating the requirement `W<W<W<W<W<W<W<
//@ error-pattern: consider increasing the recursion limit by adding a
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-ROB-F3, a crash; lens: robustness). Recorded, not fixed
//! (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! With the seal below, the build stops with E0275 (no word of the seal,
//! "consider increasing the recursion limit"). Without the seal rustc builds
//! the file, and without the dead caller `unused` (the open reading only) the
//! seal is refused at the seal, as documented. The file passes while the
//! E0275 is printed; when a fix turns it into the documented refusal, it
//! fails: that is the win. Move the program to a must-fail fixture whose
//! annotations name the polymorphic-recursion note, and delete this file.
//! The shape: a sibling of R5-ROB-F4 that its fix does not reach. Dead
//! polymorphic recursion, two obligation levels a step (`impl<T> Tr for W<T>
//! where V<T>: Tr`), that calls a dependency's generic fn at `W^k<u8>`
//! (`odep::go(&x)`, which runs `x.m()`; the review found the same with
//! `odep::boxit(x)`, a `Box<dyn Tr>`). docs/USING_TRUST.md lists this shape as
//! refused at the seal.
//! Root, as its skeptic put it: `solver_overflows` guards the check's own
//! `resolve()` (the facts loop), but for a concrete instance of a dependency's
//! generic fn sealed.rs `read_instance` then asks the collector what the body
//! uses (`tcx.items_of_instance`), with no overflow check of its own; the
//! collector's `expect_resolve` reaches `codegen_select_candidate` in standard
//! mode (or `vtable_entries`, then `expect_resolve_for_vtable`), and that
//! overflow is fatal.

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
extern crate seal_gap_odep as odep;
use odep::Tr;
pub struct V<T>(T);
pub struct W<T>(T);
impl<T: Tr> Tr for V<T> {}
impl<T> Tr for W<T> where V<T>: Tr {}
fn grow<T: Tr>(x: T, n: u32) -> u32 { if n == 0 { odep::go(&x) } else { grow(W(x), n - 1) } }
fn unused() -> u32 { grow(0u8, 3) }

clean {
    import Trust.Binding
    namespace R6RobF3
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end R6RobF3
}
