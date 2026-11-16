//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_gap_samename.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: seal `R6DynF1.visit` holds
//@ error-pattern: seal `R6DynF1.pair` holds
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-DYN-F1, a false pass; lens: dyn-trusts). Recorded, not
//! fixed (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! Each seal below HOLDS, and the program swaps two holders through a method
//! the entry was not written for: `s.visit()` swaps `stack::Vec`'s two `App`s
//! (its first comes back id=2 n=0, where it held id=1 n=1), and `q.touch()`
//! swaps `b::Pair`'s two. When a fix makes this file fail, that is the win:
//! move the program to a must-fail fixture beside a must-hold twin, and
//! delete this file.
//! The shape: a sibling of R5-DYN-F1, whose fix covers impls whose self type
//! is no struct, enum or union. An entry cannot tell apart two impls of one
//! trait (std's `Vec` and a dependency's `stack::Vec`, both impls written in
//! one module) or two inherent methods (`a::Pair::touch`, `b::Pair::touch`,
//! written in one module `ops`) for two ADTs of the SAME simple name: both
//! get one trust path and one key, the "names 2 items" error never fires, and
//! one entry written for the harmless method (`Vec::visit`, `Pair::touch`)
//! also trusts the swapping one. Without the entry each call is refused, and
//! the note (one note for both, "and at 1 more place(s)") asks for that same
//! entry; `vec::Vec::visit`, `stack::Vec::visit` and `a::Pair::touch` match
//! nothing, and the note does not say that none names either alone.
//! Root, as its skeptic put it: sealed.rs `entry_path` replaces an impl with
//! `tcx.item_name(adt)` alone, dropping the ADT's module; `relied` sets
//! `apart = None` whenever the impl's self type is an ADT, so `entry_items`
//! keeps one key for both items and `judge_trusts` never sees two.

#![allow(unused)]
extern crate seal_gap_samename as dep;

mod visit {
    use dep::Visit;
    pub struct Cell { n: u32 }
    impl Cell { pub fn new() -> Self { Cell { n: 0 } } pub fn bump(&mut self) { self.n += 1; } pub fn get(&self) -> u32 { self.n } }
    pub struct App { cell: Cell, pub id: u8 }
    impl App { pub fn new(id: u8) -> Self { App { cell: Cell::new(), id } } pub fn tick(&mut self) { self.cell.bump() } pub fn n(&self) -> u32 { self.cell.get() } }
    pub fn run() -> usize {
        let mut v: Vec<App> = Vec::new();
        v.push(App::new(7));
        let len = v.visit();
        let mut first = App::new(1);
        first.tick();
        let mut s = dep::stack::Vec { items: Vec::new() };
        s.items.push(first);
        s.items.push(App::new(2));
        len + s.visit()
    }
}
mod pair {
    pub struct Cell { n: u32 }
    impl Cell { pub fn new() -> Self { Cell { n: 0 } } pub fn bump(&mut self) { self.n += 1; } pub fn get(&self) -> u32 { self.n } }
    pub struct App { cell: Cell, pub id: u8 }
    impl App { pub fn new(id: u8) -> Self { App { cell: Cell::new(), id } } pub fn tick(&mut self) { self.cell.bump() } pub fn n(&self) -> u32 { self.cell.get() } }
    pub fn run() -> usize {
        let mut p = dep::a::Pair { x: App::new(5), y: App::new(6) };
        let k = p.touch();
        let mut first = App::new(1);
        first.tick();
        let mut q = dep::b::Pair { x: first, y: App::new(2) };
        k + q.touch()
    }
}
fn main() {
    visit::run();
    pair::run();
}
clean {
    import Trust.Binding
    namespace R6DynF1
    open Trust.Protocol
    def visit : Trust.Protocol.Seal := seals "visit::Cell" ["visit::Cell::bump"] ["visit::Cell::new"] ["visit::App::new"] ["vec::Vec::push", "Vec::drop", "RawVec::drop", "stack::Vec::drop", "Vec::visit"]
    def pair : Trust.Protocol.Seal := seals "pair::Cell" ["pair::Cell::bump"] ["pair::Cell::new"] ["pair::App::new"] ["Pair::touch"]
    end R6DynF1
}
