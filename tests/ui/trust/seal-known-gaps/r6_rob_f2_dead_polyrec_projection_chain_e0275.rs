//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: overflow evaluating the requirement `V<T>: Tr`
//@ error-pattern: consider increasing the recursion limit by adding a
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-ROB-F2, a crash; lens: robustness). Recorded, not fixed
//! (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! With the seal below, the build stops with E0275 (no span on the error, no
//! word of the seal, "consider increasing the recursion limit"; at a limit
//! of 256 or 512 the same, and only at 1024 the documented refusal, after
//! 30 s). Without the seal, rustc builds the file. The file passes while the E0275 is
//! printed; when a fix turns it into the documented refusal at the seal, it
//! fails: that is the win. Move the program to a must-fail fixture whose
//! annotations name the polymorphic-recursion note, and delete this file.
//! The shape: a sibling of R5-ROB-F4 that its fix does not reach. Dead
//! polymorphic recursion two obligation levels a step THROUGH A PROJECTION:
//! `impl<T> Tr for W<T> where V<T>: Tr { type Out = <V<T> as Tr>::Out; }` and
//! a generic `grow<T: Tr>` that names `T::Out` and recurses at `W(x)`; nothing
//! calls it. docs/USING_TRUST.md lists this shape (`impl<T> Tr for W<T> where
//! V<T>: Tr`) as refused at the seal, "the solver's own query mode is asked
//! first"; the one-level twin is.
//! Root, as its skeptic put it: the open reading normalizes `<W^k<T> as
//! Tr>::Out` in sealed.rs `Checker::sub` with `try_normalize_erasing_regions`,
//! whose canonical normalize query runs a fulfilment context in standard mode
//! (backtrace: `check_seals`, `read_instance`, `sub`,
//! `normalize_canonicalized_projection`); `solver_overflows` guards only
//! `try_resolve`, and walks only trait clauses, never projections.

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
pub trait Tr { type Out; }
impl Tr for u8 { type Out = u8; }
pub struct V<T>(T);
pub struct W<T>(T);
impl<T: Tr> Tr for V<T> { type Out = T::Out; }
impl<T> Tr for W<T> where V<T>: Tr { type Out = <V<T> as Tr>::Out; }
fn grow<T: Tr>(x: T, n: u32) -> u32 { let _o: Option<T::Out> = None; if n == 0 { 0 } else { grow(W(x), n - 1) } }

clean {
    import Trust.Binding
    namespace R6RobF2
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end R6RobF2
}
