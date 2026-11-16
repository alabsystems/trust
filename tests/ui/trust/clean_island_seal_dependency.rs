//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! Seals against a DEPENDENCY's generic code (`Trust.Protocol.Seal`), read
//! from the optimized MIR its build left: each must FAIL. Review 13 found
//! both; the dependency's marker type hides the holder behind an associated
//! type, so no type argument of its fns holds a sealed value.
//!
//! - `refilled`: `refill` empties a `Vec` of holders and moves others in.
//!   Optimization inlined `Vec::clear` and `Vec::append` into it down to a
//!   raw copy: no assignment and no call is left at the holder's type. An
//!   inlined fn is a callee like any other, read under its own name.
//! - `swapped`: `swap_all` swaps two slices of holders.
//! - `exchanged`: `exchange` swaps two holders by their bytes: its body gives
//!   the pointers the type `*mut u8`, and nothing after that names a holder.
//!
//! Review 14 (a second crate with sound `unsafe` code of its own, or code a
//! trusted fn runs without having chosen it):
//! - `transmuted`: `exchange_through` swaps two holders through pointers read
//!   back out of a transmuted `Option<&mut T>`: no pointer cast. What such a
//!   crate's `unsafe` code does is not read by its shape: a fn of it that
//!   does what only `unsafe` code can, where it handles a value through
//!   which a sealed value can be written, runs on the author's word or not
//!   at all.
//! - `contained`: `Inline<Mark>` keeps a holder in bytes of its own, and its
//!   type names only the marker: `a = b` in this crate puts one holder over
//!   another, and no type says so. The container's maker is refused.
//! - `guarded`: a guard of the dependency, whose `Drop` swaps, is handed to
//!   `mem::drop`. The seal trusts `mem::drop`: that word is about `mem::drop`
//!   and what the standard library runs beneath it, not about the `Drop`
//!   impl of a dependency's type it was handed.
//! - `promised`: an `unsafe impl` of the dependency's `Bytes` for a view that
//!   BORROWS the sealed value. Whatever the impl is for, it is this crate's
//!   word to another crate's `unsafe` code: the seal needs the trait's name
//!   in `trusts`.
//! - `thinned`: a dependency's `Handle`, which only POINTS to a holder,
//!   handed to a `dyn` of the dependency's trait `Thin`, which only `Handle`
//!   implements: its `swap_thin`, which is not generic and is never read,
//!   reads the pointer back out of the `dyn`. (Not one of review 14's: the
//!   rule that answers it was written with the others.)
//! - `erasedthere`: `exchange_erased` hands the two `&mut` to a `dyn Send`
//!   IT makes, and a fn of the dependency that is not generic reads them
//!   back: a `dyn` of a std trait, made in the dependency's own body.
//! (Every other seal here names `seal_dep::Bytes` in its `trusts`: an `unsafe
//! impl` in the crate is asked of each of the crate's seals.)

#![allow(unused)]

extern crate seal_dep;

mod refilled {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub struct Mark;
    impl seal_dep::Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    pub fn run() {
        let mut held: Vec<App> = Vec::new();
        let mut more: Vec<App> = Vec::new();
        held.push(<Mark as seal_dep::Make>::make());
        more.push(<Mark as seal_dep::Make>::make());
        held[0].cell.bump();
        seal_dep::refill::<Mark>(&mut held, &mut more);
    }
}

mod swapped {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub struct Mark;
    impl seal_dep::Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    pub fn run() {
        let mut a = [<Mark as seal_dep::Make>::make()];
        let mut b = [<Mark as seal_dep::Make>::make()];
        a[0].cell.bump();
        seal_dep::swap_all::<Mark>(&mut a, &mut b);
    }
}

mod exchanged {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub struct Mark;
    impl seal_dep::Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    pub fn run() {
        let mut a = <Mark as seal_dep::Make>::make();
        let mut b = <Mark as seal_dep::Make>::make();
        a.cell.bump();
        seal_dep::exchange::<Mark>(&mut a, &mut b);
    }
}

mod transmuted {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub struct Mark;
    impl seal_dep::Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    pub fn run() {
        let mut a = <Mark as seal_dep::Make>::make();
        let mut b = <Mark as seal_dep::Make>::make();
        a.cell.bump();
        seal_dep::exchange_through::<Mark>(&mut a, &mut b);
    }
}

mod contained {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub struct Mark;
    impl seal_dep::Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    pub fn run() {
        let mut a = seal_dep::Inline::<Mark>::make();
        let b = seal_dep::Inline::<Mark>::make();
        a.get_mut().cell.bump();
        a = b;
    }
}

mod guarded {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub struct Mark;
    impl seal_dep::Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    pub fn run() {
        let mut a = <Mark as seal_dep::Make>::make();
        let mut b = <Mark as seal_dep::Make>::make();
        a.cell.bump();
        drop(seal_dep::SwapOnDrop::<Mark>(&mut a, &mut b));
    }
}

mod promised {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct View<'a>(&'a mut Cell);
    unsafe impl seal_dep::Bytes for View<'_> {
        fn bytes(&mut self) -> (*mut u8, usize) {
            (self.0 as *mut Cell as *mut u8, std::mem::size_of::<Cell>())
        }
    }
    pub fn run() {
        let mut cell = Cell::new();
        cell.bump();
        seal_dep::blank(&mut View(&mut cell), 5);
    }
}

mod thinned {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub struct Mark;
    impl seal_dep::Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    pub fn run() {
        let mut a = <Mark as seal_dep::Make>::make();
        let mut b = <Mark as seal_dep::Make>::make();
        a.cell.bump();
        let (mut to_a, mut to_b) = (seal_dep::Handle::<Mark>(&mut a), seal_dep::Handle::<Mark>(&mut b));
        seal_dep::swap_thin(&mut to_a, &mut to_b);
    }
}

mod erasedthere {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub struct Mark;
    impl seal_dep::Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    pub fn run() {
        let mut a = <Mark as seal_dep::Make>::make();
        let mut b = <Mark as seal_dep::Make>::make();
        a.cell.bump();
        seal_dep::exchange_erased::<Mark>(&mut a, &mut b);
    }
}

fn main() {
    refilled::run();
    swapped::run();
    exchanged::run();
    transmuted::run();
    contained::run();
    guarded::run();
    promised::run();
    thinned::run();
    erasedthere::run();
}

clean {
    import Trust.Binding
    namespace Dependency
    open Trust.Protocol
    def refilled : Trust.Protocol.Seal := seals "refilled::Cell" ["refilled::Cell::bump"] ["refilled::Cell::new"] ["refilled::Mark::make"] ["Vec::push", "Vec::index_mut", "Vec::reserve", "Vec::drop", "RawVec::drop", "seal_dep::Bytes"]
    def swapped : Trust.Protocol.Seal := seals "swapped::Cell" ["swapped::Cell::bump"] ["swapped::Cell::new"] ["swapped::Mark::make"] ["seal_dep::Bytes"]
    def exchanged : Trust.Protocol.Seal := seals "exchanged::Cell" ["exchanged::Cell::bump"] ["exchanged::Cell::new"] ["exchanged::Mark::make"] ["seal_dep::Bytes"]
    def transmuted : Trust.Protocol.Seal := seals "transmuted::Cell" ["transmuted::Cell::bump"] ["transmuted::Cell::new"] ["transmuted::Mark::make"] ["seal_dep::Bytes"]
    def contained : Trust.Protocol.Seal := seals "contained::Cell" ["contained::Cell::bump"] ["contained::Cell::new"] ["contained::Mark::make"] ["seal_dep::Bytes"]
    def guarded : Trust.Protocol.Seal := seals "guarded::Cell" ["guarded::Cell::bump"] ["guarded::Cell::new"] ["guarded::Mark::make"] ["mem::drop", "seal_dep::Bytes"]
    def promised : Trust.Protocol.Seal := seals "promised::Cell" ["promised::Cell::bump"] ["promised::Cell::new"] ["promised::run"] []
    def thinned : Trust.Protocol.Seal := seals "thinned::Cell" ["thinned::Cell::bump"] ["thinned::Cell::new"] ["thinned::Mark::make"] ["seal_dep::Bytes"]
    def erasedthere : Trust.Protocol.Seal := seals "erasedthere::Cell" ["erasedthere::Cell::bump"] ["erasedthere::Cell::new"] ["erasedthere::Mark::make"] ["seal_dep::Bytes"]
    end Dependency
}
//~^^^^^^^^^^^ ERROR seal `Dependency.refilled` on `Cell` does not hold
//~^^^^^^^^^^^ ERROR seal `Dependency.swapped` on `Cell` does not hold
//~^^^^^^^^^^^ ERROR seal `Dependency.exchanged` on `Cell` does not hold
//~^^^^^^^^^^^ ERROR seal `Dependency.transmuted` on `Cell` does not hold
//~^^^^^^^^^^^ ERROR seal `Dependency.contained` on `Cell` does not hold
//~^^^^^^^^^^^ ERROR seal `Dependency.guarded` on `Cell` does not hold
//~^^^^^^^^^^^ ERROR seal `Dependency.promised` on `Cell` does not hold
//~^^^^^^^^^^^ ERROR seal `Dependency.thinned` on `Cell` does not hold
//~^^^^^^^^^^^ ERROR seal `Dependency.erasedthere` on `Cell` does not hold
