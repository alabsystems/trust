//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: its `trusts` entry `Iterator::next` names 2 items: `core::iter::traits::iterator::Iterator::next` (of the standard library's own `core`) and `core::iter::traits::iterator::Iterator::next` (of the standard library's own `core`)
//@ error-pattern: write as much of the path as tells them apart (`Iterator::next` and `Iterator::next`)
//@ error-pattern: its `trusts` entry `Debug::fmt` names 2 items: `core::fmt::Debug::fmt` (of the standard library's own `core`) and `core::fmt::Debug::fmt` (of the standard library's own `core`)
//@ error-pattern: write as much of the path as tells them apart (`Debug::fmt` and `Debug::fmt`)
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-ROB-F6, a false note; lens: robustness). Recorded, not fixed
//! (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! Each seal below is refused, as documented (an entry relied on for two
//! items that are keyed apart), and the NOTE is false: it suggests the
//! refused entry again, twice, as the spelling that tells them apart, where
//! no entry names either alone (the anchored
//! `::core::iter::traits::iterator::Iterator::next` gets the same note), and
//! "trust a fn on the way" does not help: the items are called straight from
//! this crate's `total` and from the derived `App::fmt`. docs/USING_TRUST.md
//! promises "Every note that asks for an entry prints one that works (or says
//! that none names the item alone ...)". The programs are true. The file
//! passes while those sentences are printed; when a fix changes them, it
//! fails: that is the win. Give the programs a must-fail fixture whose notes
//! say that none names either alone (or a must-hold one, if an entry comes to
//! name each), and delete this file.
//! The shape: rule 4 of review 5 keys a method of a non-ADT impl apart from
//! the trait's own item and from other such impls at the same path, but they
//! keep one printed path. `iter`: `for a in it` with `it: &mut I`, `I:
//! Iterator<Item = App>`, relies on `<&mut I as Iterator>::next` and the
//! abstract `<I as Iterator>::next` it runs (the by-value twin `it: I` holds
//! on `Iterator::next`). `dbg`: `println!("{:?}", (1u8, app))` with
//! `#[derive(Debug)]` on `App` and `Cell` relies on `<&T as Debug>::fmt` (at
//! `Cell`, from the derived `App::fmt`) and the tuple impl's `fmt` (printing
//! `App` alone holds; the review-5 build held the tuple with its spellings).
//! Root, as its skeptic put it: sealed.rs `Checker::relied` keys
//! `entry_items` by (path, crate, impl DefIndex) for an impl whose self type
//! is no ADT; `Checker::trust_entry` steps past an end only when ANOTHER
//! (crate, path) in `asked_paths` matches it, so for two items of one crate
//! and one path it hands back the shortest end, the refused entry itself,
//! and never reaches the anchor fallback or `entry_shown`'s "none names ..
//! alone"; `judge_trusts` prints that as the list that tells them apart.

#![allow(unused)]
mod iter {
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
    pub fn total<I: Iterator<Item = App>>(it: &mut I) -> u32 { let mut n = 0; for mut a in it { a.tick(); n += 1; } n }
}
mod dbg {
    #[derive(Debug)]
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    #[derive(Debug)]
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub fn show() { let app = App::new(); let t = (1u8, app); println!("{:?}", t); }
}
fn main() { dbg::show(); }

clean {
    import Trust.Binding
    namespace R6RobF6
    open Trust.Protocol
    def iter : Trust.Protocol.Seal :=
      seals "iter::Cell" ["iter::Cell::bump"] ["iter::Cell::new"] ["iter::App::new"] ["Iterator::next"]
    def dbg : Trust.Protocol.Seal :=
      seals "dbg::Cell" ["dbg::Cell::bump"] ["dbg::Cell::new"] ["dbg::App::new"] ["Debug::fmt", "Argument::new_debug"]
    end R6RobF6
}
