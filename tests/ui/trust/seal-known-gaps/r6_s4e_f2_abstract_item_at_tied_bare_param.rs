//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_mutref.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6S4eF2.s` holds
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-S4E-F2, a false pass; lens: foreign-unsafe). Recorded, not
//! fixed (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! The seal below HOLDS with no entry, and a crate that depends on this
//! library and calls `l2` or `l3` at `&mut App` swaps two holders (a=1 b=0
//! before, a=0 b=1 after), at -O and at -Copt-level=0, in editions 2021 and
//! 2024. When a fix makes this file fail, that is the win: move the program
//! to a must-fail fixture beside a must-hold twin, and delete this file.
//! The shape: a hole in round 5's collapse of abstract impls, a sibling of
//! R5-S4E-F1 and R4-CONST-F2. A where-clause the compiler does not need
//! shadows a blanket impl, so the method is an ABSTRACT impl, judged by what
//! its signature is handed; and a bare type parameter is measured as holding
//! nothing even where the bounds tie it to a holder (`P: DerefMut<Target =
//! App>`). `l2`: the dependency's `SwapPtr`, whose only impl is its safe
//! blanket `impl<P: DerefMut> SwapPtr for P` (`mem::swap` of the targets);
//! docs/USING_TRUST.md says such an item "so handed a holder, is refused unless
//! trusts names that item itself". `l3`: the same with THIS crate's `LocalSw`
//! and its blanket impl, which should refuse with no entry. Without the extra
//! bound (`a.swap_ptr(b)` under `P: DerefMut<Target = App>` alone) both are
//! refused at `mem::swap::<App>`: adding a bound the compiler does not need
//! turns a refusal into a pass.
//! Root, as its skeptic put it: sealed.rs `Checker::unresolved` calls
//! `abstract_reach`, which measures each handed type with `owns_whatever`,
//! `reach_open` and `dyn_handed`; under `Abstract::Nothing` their `ty::Param`
//! arms add nothing, so for `Self = P` and inputs `(P, P)` no `Site::Foreign`
//! (l2) or `Site::Picked` (l3) is raised. `env_mask`, whose doc names
//! `P: DerefMut<Target = App>` as a tie, is never consulted there.

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
use ::core::ops::DerefMut;
pub trait LocalSw { fn sw(self, o: Self); }
impl<P: DerefMut> LocalSw for P where P::Target: Sized {
    fn sw(mut self, mut o: Self) { ::core::mem::swap(&mut *self, &mut *o) }
}
pub fn l2<P: DerefMut<Target = App> + dep::SwapPtr>(a: P, b: P) { a.swap_ptr(b) }
pub fn l3<P: DerefMut<Target = App> + LocalSw>(a: P, b: P) { a.sw(b) }

// A crate that depends on this one (not compiled here):
//     let (mut a, mut b) = (App::new(), App::new()); a.bump();
//     l2::<&mut App>(&mut a, &mut b);  // a.get() == 0, b.get() == 1

clean {
    import Trust.Binding
    namespace R6S4eF2
    open Trust.Protocol
    def s : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end R6S4eF2
}
