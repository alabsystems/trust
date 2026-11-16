//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep.rs
//@ compile-flags: -Ztrust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! A seal that HOLDS against a dependency's generic code read from its
//! optimized MIR (`Trust.Protocol.Seal`). `fill` pushes one new holder into
//! a `Vec`. Its build inlined `Vec::push`, so its body shows `push`'s private
//! helper where a build without optimization shows `push`: which fns of std
//! a dependency's body still names turns on how it was built. The seal
//! trusts the dependency's own fn, `seal_dep::fill`, and that covers what it
//! runs in either build.

#![allow(unused)]

extern crate seal_dep;

mod filled {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    pub struct Mark;
    impl seal_dep::Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    pub fn run() {
        let mut held: Vec<App> = Vec::new();
        seal_dep::fill::<Mark>(&mut held);
        held[0].cell.bump();
        println!("{}", held[0].cell.get());
    }
}

// Review 14. A dependency's SAFE generic code is read like this crate's own:
// `visit` runs a closure of this crate on the holder and nothing else, and
// needs no trust.
mod visited {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    pub struct Mark;
    impl seal_dep::Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    pub fn run() {
        let mut app = <Mark as seal_dep::Make>::make();
        seal_dep::visit::<Mark>(&mut app, |app| app.cell.bump());
        println!("{}", app.cell.get());
    }
}

// An `unsafe impl` of a dependency's trait, on the author's word: EVERY seal
// of the crate names the trait in `trusts` (the impl is this crate's word to
// that crate's `unsafe` code, whatever it is for), and each note says so.
mod vouched {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct Pixels([u8; 4]);
    unsafe impl seal_dep::Bytes for Pixels {
        fn bytes(&mut self) -> (*mut u8, usize) { (self.0.as_mut_ptr(), 4) }
    }
    pub fn run() {
        let mut cell = Cell::new();
        cell.bump();
        let mut pixels = Pixels([0; 4]);
        seal_dep::blank(&mut pixels, 255);
        println!("{} {}", cell.get(), pixels.0[0]);
    }
}

// `peek` hands back the `&` it is given through a raw pointer, and writes
// nothing. Against THIS build of the dependency (optimized) the seal holds:
// nothing only `unsafe` code can do is left in `peek`'s body. Against a
// build with debug assertions the dereference is still there, the check does
// not tell it from one that writes, and the seal is refused until
// `seal_dep::peek` is trusted: which fns of a dependency need the author's
// word turns on how the dependency was built.
mod peeked {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    pub struct Mark;
    impl seal_dep::Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    pub fn run() {
        let mut a = <Mark as seal_dep::Make>::make();
        a.cell.bump();
        println!("{}", seal_dep::peek::<Mark>(&mut a).cell.get());
    }
}

fn main() {
    filled::run();
    visited::run();
    vouched::run();
    peeked::run();
}

clean {
    import Trust.Binding
    namespace DependencyHolds
    open Trust.Protocol
    def filled : Trust.Protocol.Seal :=
      seals "filled::Cell" ["filled::Cell::bump"] ["filled::Cell::new"] ["filled::Mark::make"] ["seal_dep::fill", "Vec::index", "Vec::index_mut", "Vec::drop", "RawVec::drop", "seal_dep::Bytes"]
    def visited : Trust.Protocol.Seal :=
      seals "visited::Cell" ["visited::Cell::bump"] ["visited::Cell::new"] ["visited::Mark::make"] ["seal_dep::Bytes"]
    def vouched : Trust.Protocol.Seal :=
      seals "vouched::Cell" ["vouched::Cell::bump"] ["vouched::Cell::new"] ["vouched::run"] ["seal_dep::Bytes"]
    def peeked : Trust.Protocol.Seal :=
      seals "peeked::Cell" ["peeked::Cell::bump"] ["peeked::Cell::new"] ["peeked::Mark::make"] ["seal_dep::Bytes"]
    end DependencyHolds
}
