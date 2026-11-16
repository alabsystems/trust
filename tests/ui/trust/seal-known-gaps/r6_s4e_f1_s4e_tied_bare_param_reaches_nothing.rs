//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_mutref.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6S4eF1.s` holds
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-S4E-F1, a false pass; lens: foreign-unsafe). Recorded, not
//! fixed (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! The seal below HOLDS with no entry, and a crate that depends on this
//! library and calls each fn at `&mut App` swaps two holders (a=1 b=0 before,
//! a=0 b=1 after), at -O and at -Copt-level=0, in editions 2021 and 2024.
//! When a fix makes this file fail, that is the win: move the program to a
//! must-fail fixture beside a must-hold twin, and delete this file.
//! The shape: a hole in the R5-S4E-F1 fix. In a library's open reading the
//! check FOLLOWS a dependency's fn named at a bare type parameter the bounds
//! tie to a holder, then asks S4e of it by what its locals' types reach, and
//! a bare parameter reaches nothing: a sound dependency fn whose locals are
//! typed only by the parameter swaps two holders in `unsafe` and is never
//! asked for an entry. `l1` (`P: MutRef<Target = App>`, `swap_mut::<P>`),
//! `l1p` (over a pair), `l1w` (the tie in a where-clause), `l1m` (the
//! dependency's blanket method), `l1k` (its closure, run by its own fn), `l6u`
//! (`swap_bytes::<T>` under `T: Exactly<App>`, a sealed trait whose only impl
//! is `impl<X> Exactly<X> for X`), `l8` (`swap_mut::<K::P>`, tied only by the
//! LOCAL trait's own item bound `type P: MutRef<Target = App>`). The concrete
//! twin (`swap_mut::<&mut App>`) is refused, asking for `swap_mut`.
//! Root, as its skeptic put it: sealed.rs `names_local_in` follows the call
//! when `env_mask(scope) != 0`; `works_on_unmemoized` then measures each held
//! type with `reach_mode`/`reach_open`/`reach_in` under `Abstract::Nothing`,
//! whose `ty::Param` arm (as `owns_in`'s) adds nothing; `env_mask` is
//! consulted only through `alias_mask`, and reads `caller_bounds` only.

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
pub fn l1<P: dep::MutRef<Target = App>>(a: P, b: P) { dep::swap_mut::<P>(a, b) }
pub fn l1p<P: dep::MutRef<Target = App>>(a: P, b: P) { dep::swap_pair::<P>((a, b)) }
pub fn l1w<P: dep::MutRef>(a: P, b: P) where P: DerefMut<Target = App> { dep::swap_mut::<P>(a, b) }
pub fn l1m<P: dep::MutRef<Target = App>>(a: P, b: P) { dep::RawSwapTr::raw_swap(a, b) }
pub fn l1k<P: dep::MutRef<Target = App>>(a: P, b: P) { dep::swap_in_closure::<P>(a, b) }
pub fn l6u<T: dep::Exactly<App>>(a: &mut T, b: &mut T) { dep::swap_bytes::<T>(a, b) }
/// A local trait whose associated type's own bound ties it to a holder.
pub trait Pick<'a> { type P: dep::MutRef<Target = App>; }
pub fn l8<'a, K: Pick<'a>>(a: K::P, b: K::P) { dep::swap_mut::<K::P>(a, b) }

// A crate that depends on this one (not compiled here):
//     let (mut a, mut b) = (App::new(), App::new()); a.bump();
//     l1::<&mut App>(&mut a, &mut b);  // a.get() == 0, b.get() == 1

clean {
    import Trust.Binding
    namespace R6S4eF1
    open Trust.Protocol
    def s : Trust.Protocol.Seal := seals "Cell" ["Cell::bump"] ["Cell::new"] ["App::new"] []
    end R6S4eF1
}
