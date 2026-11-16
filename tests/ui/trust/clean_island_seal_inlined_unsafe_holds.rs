//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_inl_c.rs
//@ aux-build: seal_dep_inl_b.rs
//@ aux-build: seal_dep_inl_n.rs
//@ aux-build: seal_dep_inl_c0.rs
//@ aux-build: seal_dep_inl_b0.rs
//@ aux-build: seal_dep_inl_n0.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! What a fn the optimizer inlined into a dependency's body does with
//! `unsafe` is that fn's (`Trust.Protocol.Seal`): it is asked about as that
//! fn, at its own instance, with what IT handles, and is never charged to
//! the body it was inlined into. Every seal HOLDS, with the crates built
//! with optimization (`_o`) and without (`_z`): crate C's `swap_small`
//! trusted by name, or crate B's `go_small` that calls it; C's `noise`,
//! which uses `unsafe` on its own `u8`, trusted or not; a nested fn with
//! `unsafe` on its own local, inlined into the fn it is declared in. Review
//! 3 of the review-14 build found the four with optimization refused: the
//! inlined `unsafe` was paired with the holders of B's unsafe-free body,
//! and the entry `swap_small` stopped covering it. (Untrusted, C's swap is
//! still refused: `_inlined_unsafe.rs`.)

#![allow(unused)]

extern crate seal_dep_inl_c;
extern crate seal_dep_inl_b;
extern crate seal_dep_inl_n;
extern crate seal_dep_inl_c0;
extern crate seal_dep_inl_b0;
extern crate seal_dep_inl_n0;

mod small_inner_trusted_o {
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
        let _ = seal_dep_inl_b::go_small::<Mark>(&mut x, &mut y);
        println!("small_inner_trusted_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod small_outer_trusted_o {
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
        let _ = seal_dep_inl_b::go_small::<Mark>(&mut x, &mut y);
        println!("small_outer_trusted_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod noise_o {
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
        let _ = seal_dep_inl_b::go_noise::<Mark>(&mut x, &mut y);
        println!("noise_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod noise_inner_trusted_o {
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
        let _ = seal_dep_inl_b::go_noise::<Mark>(&mut x, &mut y);
        println!("noise_inner_trusted_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod nested_unrelated_o {
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
        let _ = seal_dep_inl_n::nested_unrelated::<Mark>(&mut x, &mut y);
        println!("nested_unrelated_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod small_inner_trusted_z {
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
        let _ = seal_dep_inl_b0::go_small::<Mark>(&mut x, &mut y);
        println!("small_inner_trusted_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod small_outer_trusted_z {
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
        let _ = seal_dep_inl_b0::go_small::<Mark>(&mut x, &mut y);
        println!("small_outer_trusted_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod noise_z {
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
        let _ = seal_dep_inl_b0::go_noise::<Mark>(&mut x, &mut y);
        println!("noise_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod noise_inner_trusted_z {
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
        let _ = seal_dep_inl_b0::go_noise::<Mark>(&mut x, &mut y);
        println!("noise_inner_trusted_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod nested_unrelated_z {
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
        let _ = seal_dep_inl_n0::nested_unrelated::<Mark>(&mut x, &mut y);
        println!("nested_unrelated_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

fn main() {
    small_inner_trusted_o::run();
    small_outer_trusted_o::run();
    noise_o::run();
    noise_inner_trusted_o::run();
    nested_unrelated_o::run();
    small_inner_trusted_z::run();
    small_outer_trusted_z::run();
    noise_z::run();
    noise_inner_trusted_z::run();
    nested_unrelated_z::run();
}

clean {
    import Trust.Binding
    namespace InlinedUnsafeHolds
    open Trust.Protocol
    def small_inner_trusted_o : Trust.Protocol.Seal := seals "small_inner_trusted_o::Cell" ["small_inner_trusted_o::Cell::bump"] ["small_inner_trusted_o::Cell::new"] ["small_inner_trusted_o::App::new"] ["seal_dep_inl_c::swap_small"]
    def small_outer_trusted_o : Trust.Protocol.Seal := seals "small_outer_trusted_o::Cell" ["small_outer_trusted_o::Cell::bump"] ["small_outer_trusted_o::Cell::new"] ["small_outer_trusted_o::App::new"] ["seal_dep_inl_b::go_small"]
    def noise_o : Trust.Protocol.Seal := seals "noise_o::Cell" ["noise_o::Cell::bump"] ["noise_o::Cell::new"] ["noise_o::App::new"] []
    def noise_inner_trusted_o : Trust.Protocol.Seal := seals "noise_inner_trusted_o::Cell" ["noise_inner_trusted_o::Cell::bump"] ["noise_inner_trusted_o::Cell::new"] ["noise_inner_trusted_o::App::new"] ["seal_dep_inl_c::noise"]
    def nested_unrelated_o : Trust.Protocol.Seal := seals "nested_unrelated_o::Cell" ["nested_unrelated_o::Cell::bump"] ["nested_unrelated_o::Cell::new"] ["nested_unrelated_o::App::new"] []
    def small_inner_trusted_z : Trust.Protocol.Seal := seals "small_inner_trusted_z::Cell" ["small_inner_trusted_z::Cell::bump"] ["small_inner_trusted_z::Cell::new"] ["small_inner_trusted_z::App::new"] ["seal_dep_inl_c0::swap_small"]
    def small_outer_trusted_z : Trust.Protocol.Seal := seals "small_outer_trusted_z::Cell" ["small_outer_trusted_z::Cell::bump"] ["small_outer_trusted_z::Cell::new"] ["small_outer_trusted_z::App::new"] ["seal_dep_inl_b0::go_small"]
    def noise_z : Trust.Protocol.Seal := seals "noise_z::Cell" ["noise_z::Cell::bump"] ["noise_z::Cell::new"] ["noise_z::App::new"] []
    def noise_inner_trusted_z : Trust.Protocol.Seal := seals "noise_inner_trusted_z::Cell" ["noise_inner_trusted_z::Cell::bump"] ["noise_inner_trusted_z::Cell::new"] ["noise_inner_trusted_z::App::new"] ["seal_dep_inl_c0::noise"]
    def nested_unrelated_z : Trust.Protocol.Seal := seals "nested_unrelated_z::Cell" ["nested_unrelated_z::Cell::bump"] ["nested_unrelated_z::Cell::new"] ["nested_unrelated_z::App::new"] []
    end InlinedUnsafeHolds
}
