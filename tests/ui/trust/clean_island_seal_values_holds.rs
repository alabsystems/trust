//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_values.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_values.rs`: fns handed out as VALUES that
//! HOLD (`Trust.Protocol.Seal`).
//!
//! - `measured`: a trusted fn hands out `mem::size_of_val::<App>`, whose
//!   one input is a `&App` of plain data, through which nothing is written:
//!   whoever calls the pointer can make it write nothing, and the trust of
//!   the fn that handed it out is enough.
//! - `named`: a trusted fn hands out `peek_len::<App>`, handed a `&mut App`
//!   by whoever calls the pointer: the seal trusts `peek_len` by name too,
//!   and a trust that names a fn covers it wherever it runs.
//! - `plain`: the constant `Tab::SWAP` and the trusted `swapper` at a type
//!   that holds no cell (`u8`): nothing is put over a holder.

#![allow(unused)]

extern crate seal_dep_values;

mod measured {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> usize {
        let mut a = App::new();
        a.cell.bump();
        let f = seal_dep_values::measure::<App>();
        f(&a)
    }
}

mod named {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> usize {
        let mut a = App::new();
        a.cell.bump();
        let f = seal_dep_values::reader::<App>();
        f(&mut a)
    }
}

mod plain {
    use seal_dep_values::Tab;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> u8 {
        let mut a = App::new();
        a.cell.bump();
        let (mut x, mut y) = (1u8, 2u8);
        (Tab::<u8>::SWAP)(&mut x, &mut y);
        let f = seal_dep_values::swapper::<u8>();
        f(&mut x, &mut y);
        x
    }
}

fn main() {
    measured::run();
    named::run();
    plain::run();
}

clean {
    import Trust.Binding
    namespace ValuesHold
    open Trust.Protocol
    def measured : Trust.Protocol.Seal := seals "measured::Cell" ["measured::Cell::bump"] ["measured::Cell::new"] ["measured::App::new"] ["seal_dep_values::measure"]
    def named : Trust.Protocol.Seal := seals "named::Cell" ["named::Cell::bump"] ["named::Cell::new"] ["named::App::new"] ["seal_dep_values::reader", "seal_dep_values::peek_len"]
    def plain : Trust.Protocol.Seal := seals "plain::Cell" ["plain::Cell::bump"] ["plain::Cell::new"] ["plain::App::new"] []
    end ValuesHold
}
