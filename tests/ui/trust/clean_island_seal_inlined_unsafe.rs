//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_inl_c.rs
//@ aux-build: seal_dep_inl_b.rs
//@ aux-build: seal_dep_inl_n.rs
//@ aux-build: seal_dep_inl_c0.rs
//@ aux-build: seal_dep_inl_b0.rs
//@ aux-build: seal_dep_inl_n0.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The twin of `clean_island_seal_inlined_unsafe_holds.rs`
//! (`Trust.Protocol.Seal`): crate C's `swap_small`, which swaps the bytes of
//! two holders with `unsafe`, run beneath crate B's `go_small` with no
//! `trusts` entry. Each seal must FAIL, in both profiles: with optimization
//! the swap is inlined into `go_small`, and is still asked about as
//! `swap_small`.

#![allow(unused)]

extern crate seal_dep_inl_c;
extern crate seal_dep_inl_b;
extern crate seal_dep_inl_n;
extern crate seal_dep_inl_c0;
extern crate seal_dep_inl_b0;
extern crate seal_dep_inl_n0;

mod small_untrusted_o {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub struct Mark;
    impl seal_dep_inl_c::Make for Mark { type Out = App; }
    pub fn run() {
        let mut x = App::new();
        let mut y = App::new();
        x.cell.bump();
        let _ = seal_dep_inl_b::go_small::<Mark>(&mut x, &mut y); //~ NOTE this runs `seal_dep_inl_c::swap_small`, a fn of a crate outside the standard library, which reads or writes a
        println!("small_untrusted_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod small_untrusted_z {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub struct Mark;
    impl seal_dep_inl_c0::Make for Mark { type Out = App; }
    pub fn run() {
        let mut x = App::new();
        let mut y = App::new();
        x.cell.bump();
        let _ = seal_dep_inl_b0::go_small::<Mark>(&mut x, &mut y); //~ NOTE this runs `seal_dep_inl_c0::swap_small`, a fn of a crate outside the standard library, which reads or writes
        println!("small_untrusted_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

fn main() {
    small_untrusted_o::run();
    small_untrusted_z::run();
}

clean {
    import Trust.Binding
    namespace InlinedUnsafe
    open Trust.Protocol
    def small_untrusted_o : Trust.Protocol.Seal := seals "small_untrusted_o::Cell" ["small_untrusted_o::Cell::bump"] ["small_untrusted_o::Cell::new"] ["small_untrusted_o::App::new"] []
    def small_untrusted_z : Trust.Protocol.Seal := seals "small_untrusted_z::Cell" ["small_untrusted_z::Cell::bump"] ["small_untrusted_z::Cell::new"] ["small_untrusted_z::App::new"] []
    end InlinedUnsafe
}
//~^^^^ ERROR seal `InlinedUnsafe.small_untrusted_o` on `Cell` does not hold
//~^^^^ ERROR seal `InlinedUnsafe.small_untrusted_z` on `Cell` does not hold
