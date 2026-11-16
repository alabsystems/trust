//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_nsdep.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6DynF2.cell` holds
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-DYN-F2, a false pass; lens: dyn-trusts). Recorded, not
//! fixed (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! The seal below HOLDS, and `k::Keep(&mut first, &mut second)` swaps two
//! holders (`first` comes back id=2 n=0, where it held id=1 n=1). When a fix
//! makes this file fail, that is the win: move the program to a must-fail
//! fixture beside a must-hold twin, and delete this file.
//! The shape: a trait and a free fn that share one defining path (the
//! dependency's `k::Keep`, in the type and in the value namespace) are one
//! name to `trusts`. The entry `k::Keep`, written to trust the trait (so that
//! a boxed `dyn` of it may hold a holder), also trusts the fn, which swaps,
//! with no "names 2 items" error; the note of the seal lists one item. Each
//! alone with no entry is refused, and both notes ask for the same `k::Keep`,
//! so no spelling names either alone. A trait and a fn are different words (a
//! `dyn` that may hold one, a fn run at a type), and review 2 and review 5
//! counted an entry that named two items, unsaid, as a false pass.
//! Root, as its skeptic put it: sealed.rs `relied` keys `entry_items` by
//! (trust path, crate, apart), where `apart` is `Some` only for an item of an
//! impl whose own type is no struct, enum or union; the trait's DefId and the
//! fn's get one key, so `judge_trusts` never sees two (it does when the trait
//! and the fn sit at different paths that both end in `k::Keep`).

#![allow(unused)]
extern crate seal_gap_nsdep as nsdep;

mod m {
    pub struct Cell { n: u32 }
    impl Cell { pub fn new() -> Self { Cell { n: 0 } } pub fn bump(&mut self) { self.n += 1; } pub fn get(&self) -> u32 { self.n } }
    pub struct App { cell: Cell, pub id: u8 }
    impl App { pub fn new(id: u8) -> Self { App { cell: Cell::new(), id } } pub fn tick(&mut self) { self.cell.bump() } pub fn n(&self) -> u32 { self.cell.get() } }
    impl crate::nsdep::k::Keep for App {}
}
fn main() {
    let kept: Box<dyn nsdep::k::Keep> = Box::new(m::App::new(9));
    let mut first = m::App::new(1);
    first.tick();
    let mut second = m::App::new(2);
    nsdep::k::Keep(&mut first, &mut second);
    let _ = (kept.label(), first.id, first.n());
}
clean {
    import Trust.Binding
    namespace R6DynF2
    open Trust.Protocol
    def cell : Trust.Protocol.Seal := seals "m::Cell" ["m::Cell::bump"] ["m::Cell::new"] ["m::App::new"] ["k::Keep", "boxed::Box::new", "Keep::label", "Box::drop", "Any::type_id"]
    end R6DynF2
}
