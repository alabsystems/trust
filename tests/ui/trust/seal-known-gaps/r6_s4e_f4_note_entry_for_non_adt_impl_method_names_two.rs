//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_poke.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: in `std_deref::run`: it may put one value over another (in `trusts`: `Deref::deref`)
//@ error-pattern: its `trusts` entry `Deref::deref` names 2 items: `core::ops::deref::Deref::deref` (of the standard library's own `core`) and `core::ops::deref::Deref::deref` (of the standard library's own `core`)
//@ error-pattern: write as much of the path as tells them apart (`Deref::deref` and `Deref::deref`)
//@ error-pattern: in `dep_poke::run`: it may put one value over another (in `trusts`: `Poke::poke`)
//@ error-pattern: its `trusts` entry `Poke::poke` names 2 items: `seal_gap_poke::Poke::poke` (of the crate this one names `dep`) and `seal_gap_poke::Poke::poke` (of the crate this one names `dep`)
//@ error-pattern: write as much of the path as tells them apart (`Poke::poke` and `Poke::poke`)
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-S4E-F4, a false note; lens: foreign-unsafe). Recorded, not
//! fixed (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! Each seal below is refused, as documented: review 5 keys apart, as two
//! items, the methods of two impls of one trait in one module whose self types
//! are no struct, enum or union (std's `Deref` for `&T` and for `&mut T`), and
//! such a method beside the trait's own provided method (a dependency's
//! `Poke::poke` run as the default at `Wrap<App>`, and its `&mut T` override),
//! and no entry names either alone. The NOTES are false: with no entry they
//! ask for `Deref::deref` / `Poke::poke`; with that entry written in, the seal
//! is refused as naming 2 items printed with one path, and the note says to
//! "write as much of the path as tells them apart (`Deref::deref` and
//! `Deref::deref`)", the refused entry twice. docs/USING_TRUST.md promises
//! "Every note that asks for an entry prints one that works (or says that none
//! names the item alone ...; trust a fn on the way to it)". Every program is
//! true (the `unsafe` only reads a byte, `Deref` only reads). The file passes
//! while those sentences are printed; when a fix changes them, it fails: that
//! is the win. Give the program a must-fail fixture whose notes say that none
//! names either item alone, and delete this file.
//! Root, as its skeptic put it: sealed.rs `entry_path` gives a non-ADT impl's
//! method the trait's name, so both impls and the trait's provided method get
//! one path; `trust_entry` skips an asked path only for ANOTHER (crate, path)
//! (`*krate != def.krate || *asked != path`), so a same-crate, same-path item
//! counts as the item itself and the shortest suffix comes back instead of
//! `None`; `judge_trusts` builds the "tells them apart" list from
//! `entry_shown` for items `entry_items` keyed apart.

#![allow(unused)]
extern crate seal_gap_poke as dep;

mod std_deref {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> u32 {
        let mut x = App::new();
        let mut y = App::new();
        x.cell.bump();
        let r: &mut App = &mut x; let s: &App = &y; let _ = ::core::ops::Deref::deref(&r).cell.get(); let _ = ::core::ops::Deref::deref(&s).cell.get();
        x.cell.get() + y.cell.get()
    }
}
mod std_deref_entry {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> u32 {
        let mut x = App::new();
        let mut y = App::new();
        x.cell.bump();
        let r: &mut App = &mut x; let s: &App = &y; let _ = ::core::ops::Deref::deref(&r).cell.get(); let _ = ::core::ops::Deref::deref(&s).cell.get();
        x.cell.get() + y.cell.get()
    }
}
mod dep_poke {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> u32 {
        let mut x = App::new();
        let mut y = App::new();
        x.cell.bump();
        let mut w = dep::Wrap(App::new()); let _ = dep::Poke::poke(&mut w); let mut r = &mut x; let _ = dep::Poke::poke(&mut r);
        x.cell.get() + y.cell.get()
    }
}
mod dep_poke_entry {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> u32 {
        let mut x = App::new();
        let mut y = App::new();
        x.cell.bump();
        let mut w = dep::Wrap(App::new()); let _ = dep::Poke::poke(&mut w); let mut r = &mut x; let _ = dep::Poke::poke(&mut r);
        x.cell.get() + y.cell.get()
    }
}
fn main() {
    std_deref::run();
    std_deref_entry::run();
    dep_poke::run();
    dep_poke_entry::run();
}
clean {
    import Trust.Binding
    namespace R6S4eF4
    open Trust.Protocol
    def std_deref : Trust.Protocol.Seal := seals "std_deref::Cell" ["std_deref::Cell::bump"] ["std_deref::Cell::new"] ["std_deref::App::new"] []
    def std_deref_entry : Trust.Protocol.Seal := seals "std_deref_entry::Cell" ["std_deref_entry::Cell::bump"] ["std_deref_entry::Cell::new"] ["std_deref_entry::App::new"] ["Deref::deref"]
    def dep_poke : Trust.Protocol.Seal := seals "dep_poke::Cell" ["dep_poke::Cell::bump"] ["dep_poke::Cell::new"] ["dep_poke::App::new"] []
    def dep_poke_entry : Trust.Protocol.Seal := seals "dep_poke_entry::Cell" ["dep_poke_entry::Cell::bump"] ["dep_poke_entry::Cell::new"] ["dep_poke_entry::App::new"] ["Poke::poke"]
    end R6S4eF4
}
