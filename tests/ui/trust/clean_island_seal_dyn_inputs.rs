//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_erase.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A fn reached as a VALUE runs where it is called, on what its caller hands
//! it, and a `dyn` of another crate's trait among its inputs can be handed
//! what this crate put behind such a `dyn` (`Trust.Protocol.Seal`): each
//! seal must FAIL. Review 3 of the review-14 build found both passing: the
//! trusted `any_handler` only RETURNS `fn(&mut dyn Any, &mut dyn Any)`, and
//! the fn it hands out downcasts each `dyn Any` to this crate's `Grip` and
//! swaps the two `App`s the grips point to. A `&mut Grip` as a `&mut dyn
//! Any` is let pass (it only points to a holder, and `Any` is std's), and
//! the handed-out fn's inputs were taken to reach nothing: so the trust of
//! `any_handler` covered the swap.
//!
//! - `pointer`: the fn pointer `any_handler` returns.
//! - `boxed`: the same as a boxed `dyn Fn` (a vtable's method).
//!
//! When what is put behind the `dyn Any` reaches no holder, the seals hold:
//! `_dyn_inputs_holds.rs`.

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
    pub struct Grip(pub &'static mut App);
    impl std::ops::Deref for Grip { type Target = App; fn deref(&self) -> &App { self.0 } }
    impl std::ops::DerefMut for Grip { fn deref_mut(&mut self) -> &mut App { self.0 } }
    pub fn run() {
        let mut app = App::new(0);
        app.tick();
        let both: &'static mut [App; 2] = Box::leak(Box::new([App::new(1), App::new(2)]));
        let [x, y] = both;
        let (mut ga, mut gb) = (Grip(x), Grip(y));
        let f = seal_dep_erase::any_handler::<Grip>(); //~ NOTE this runs `core::intrinsics::typed_swap_nonoverlapping`, a fn of another crate, at the type `pointer::App`,
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
    pub struct Grip(pub &'static mut App);
    impl std::ops::Deref for Grip { type Target = App; fn deref(&self) -> &App { self.0 } }
    impl std::ops::DerefMut for Grip { fn deref_mut(&mut self) -> &mut App { self.0 } }
    pub fn run() {
        let mut app = App::new(0);
        app.tick();
        let both: &'static mut [App; 2] = Box::leak(Box::new([App::new(1), App::new(2)]));
        let [x, y] = both;
        let (mut ga, mut gb) = (Grip(x), Grip(y));
        let f = seal_dep_erase::boxed_any::<Grip>(); //~ NOTE this runs `core::intrinsics::typed_swap_nonoverlapping`, a fn of another crate, at the type `boxed::App`,
        f(&mut ga, &mut gb);
    }
}

fn main() {
    pointer::run();
    boxed::run();
}

clean {
    import Trust.Binding
    namespace DynInputs
    open Trust.Protocol
    def pointer : Trust.Protocol.Seal := seals "pointer::Cell" ["pointer::Cell::bump"] ["pointer::Cell::new"] ["pointer::App::new"] ["seal_dep_erase::any_handler", "Box::new", "Box::leak"]
    def boxed : Trust.Protocol.Seal := seals "boxed::Cell" ["boxed::Cell::bump"] ["boxed::Cell::new"] ["boxed::App::new"] ["seal_dep_erase::boxed_any", "Box::new", "Box::leak"]
    end DynInputs
}
//~^^^^ ERROR seal `DynInputs.pointer` on `Cell` does not hold
//~^^^^ ERROR seal `DynInputs.boxed` on `Cell` does not hold
