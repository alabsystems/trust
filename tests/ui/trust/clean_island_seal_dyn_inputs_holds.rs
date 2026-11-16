//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_erase.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_dyn_inputs.rs` (`Trust.Protocol.Seal`):
//! the same trusted `any_handler` and `boxed_any`, where the grips handed to
//! the `dyn Any` point to a plain `Tag`: what the handed-out fn swaps holds
//! no sealed value, and every seal HOLDS.

#![allow(unused)]

extern crate seal_dep_erase;

mod pointer {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell, pub id: u8 }
    impl App {
        pub fn new(id: u8) -> Self { App { cell: Cell::new(), id } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub struct Tag(pub u8);
    pub struct Grip(pub &'static mut Tag);
    impl std::ops::Deref for Grip { type Target = Tag; fn deref(&self) -> &Tag { self.0 } }
    impl std::ops::DerefMut for Grip { fn deref_mut(&mut self) -> &mut Tag { self.0 } }
    pub fn run() {
        let mut app = App::new(0);
        app.tick();
        let both: &'static mut [Tag; 2] = Box::leak(Box::new([Tag(1), Tag(2)]));
        let [x, y] = both;
        let (mut ga, mut gb) = (Grip(x), Grip(y));
        let f = seal_dep_erase::any_handler::<Grip>();
        f(&mut ga, &mut gb);
    }
}

mod boxed {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell, pub id: u8 }
    impl App {
        pub fn new(id: u8) -> Self { App { cell: Cell::new(), id } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub struct Tag(pub u8);
    pub struct Grip(pub &'static mut Tag);
    impl std::ops::Deref for Grip { type Target = Tag; fn deref(&self) -> &Tag { self.0 } }
    impl std::ops::DerefMut for Grip { fn deref_mut(&mut self) -> &mut Tag { self.0 } }
    pub fn run() {
        let mut app = App::new(0);
        app.tick();
        let both: &'static mut [Tag; 2] = Box::leak(Box::new([Tag(1), Tag(2)]));
        let [x, y] = both;
        let (mut ga, mut gb) = (Grip(x), Grip(y));
        let f = seal_dep_erase::boxed_any::<Grip>();
        f(&mut ga, &mut gb);
    }
}

fn main() {
    pointer::run();
    boxed::run();
}

clean {
    import Trust.Binding
    namespace DynInputsHolds
    open Trust.Protocol
    def pointer : Trust.Protocol.Seal := seals "pointer::Cell" ["pointer::Cell::bump"] ["pointer::Cell::new"] ["pointer::App::new"] ["seal_dep_erase::any_handler", "Box::new", "Box::leak"]
    def boxed : Trust.Protocol.Seal := seals "boxed::Cell" ["boxed::Cell::bump"] ["boxed::Cell::new"] ["boxed::App::new"] ["seal_dep_erase::boxed_any", "Box::new", "Box::leak"]
    end DynInputsHolds
}
