//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_collide.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_trusts.rs`: `trusts` entries that tell
//! std's item from a dependency's of the same name HOLD, each naming the
//! one item it means (`Trust.Protocol.Seal`).
//!
//! - `pushed`: `vec::Vec::push` (std's) and `bag::Vec::push` (the
//!   dependency's, which only adds), both at the holder's type.
//! - `boxedany`: `core::any::Any` (std's) and `seal_dep_collide::any::Any`.
//! - `converted`: `vec::Vec::from` (std's, for an array), beside the
//!   dependency's `Vec::from`, which runs at `u8` only: an entry is asked to
//!   name one item among those its word is relied on for.
//! - `internal`: `Mutex::lock` names std's, though the walk meets other
//!   fns of std at that path beneath it (its platform's): none names a
//!   type of this crate, and no entry's word is relied on for them.

#![allow(unused)]

extern crate seal_dep_collide;

mod pushed {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() {
        let mut kept: Vec<App> = Vec::new();
        kept.push(App::new());
        let mut bag = seal_dep_collide::bag::Vec::new();
        let mut a = App::new();
        a.cell.bump();
        bag.push(a);
        println!("{} {}", kept.len(), bag.len());
    }
}

mod boxedany {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    impl seal_dep_collide::any::Any for App {}
    pub fn run() {
        let kept: Box<dyn std::any::Any> = Box::new(App::new());
        let mut a = App::new();
        a.cell.bump();
        let x: Box<dyn seal_dep_collide::any::Any> = Box::new(a);
    }
}

mod converted {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() {
        let first = Vec::from([App::new()]);
        let mut ring = seal_dep_collide::Ring::new(1);
        ring.put(1u8);
        ring.put(2u8);
        let bytes: Vec<u8> = Vec::from(ring);
        println!("{} {}", first.len(), bytes.len());
    }
}

mod internal {
    use std::sync::Mutex;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() {
        let shared = Mutex::new(App::new());
        shared.lock().unwrap().cell.bump();
    }
}

fn main() {
    pushed::run();
    boxedany::run();
    converted::run();
    internal::run();
}

clean {
    import Trust.Binding
    namespace TrustsHold
    open Trust.Protocol
    def pushed : Trust.Protocol.Seal := seals "pushed::Cell" ["pushed::Cell::bump"] ["pushed::Cell::new"] ["pushed::App::new"] ["vec::Vec::new", "vec::Vec::push", "vec::Vec::len", "Vec::drop", "RawVec::drop", "bag::Vec::new", "bag::Vec::push", "bag::Vec::len"]
    def boxedany : Trust.Protocol.Seal := seals "boxedany::Cell" ["boxedany::Cell::bump"] ["boxedany::Cell::new"] ["boxedany::App::new"] ["Box::new", "core::any::Any", "Any::type_id", "seal_dep_collide::any::Any", "Any::label"]
    def converted : Trust.Protocol.Seal := seals "converted::Cell" ["converted::Cell::bump"] ["converted::Cell::new"] ["converted::App::new"] ["vec::Vec::from", "vec::Vec::len", "Vec::drop", "RawVec::drop"]
    def internal : Trust.Protocol.Seal := seals "internal::Cell" ["internal::Cell::bump"] ["internal::Cell::new"] ["internal::App::new"] ["Mutex::new", "Mutex::lock", "Result::unwrap", "MutexGuard::deref_mut", "MutexGuard::drop"]
    end TrustsHold
}
