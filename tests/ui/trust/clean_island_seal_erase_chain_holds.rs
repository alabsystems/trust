//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_erase_chain.rs` (`Trust.Protocol.Seal`):
//! the same reverse-ordered chain of six `dyn`s, each place given one value,
//! and the seal HOLDS.

#![allow(unused)]

mod chained {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub trait Tr0 { fn id(&self) -> u32; }
    impl Tr0 for App { fn id(&self) -> u32 { self.cell.get() } }
    pub trait Tr6 { fn id(&self) -> u32; }
    pub struct H6(Box<dyn Tr5>);
    impl Tr6 for H6 { fn id(&self) -> u32 { self.0.id() + 1 } }
    #[inline(never)] pub fn f6(x: Box<dyn Tr5>) -> Box<dyn Tr6> { Box::new(H6(x)) }
    pub trait Tr5 { fn id(&self) -> u32; }
    pub struct H5(Box<dyn Tr4>);
    impl Tr5 for H5 { fn id(&self) -> u32 { self.0.id() + 1 } }
    #[inline(never)] pub fn f5(x: Box<dyn Tr4>) -> Box<dyn Tr5> { Box::new(H5(x)) }
    pub trait Tr4 { fn id(&self) -> u32; }
    pub struct H4(Box<dyn Tr3>);
    impl Tr4 for H4 { fn id(&self) -> u32 { self.0.id() + 1 } }
    #[inline(never)] pub fn f4(x: Box<dyn Tr3>) -> Box<dyn Tr4> { Box::new(H4(x)) }
    pub trait Tr3 { fn id(&self) -> u32; }
    pub struct H3(Box<dyn Tr2>);
    impl Tr3 for H3 { fn id(&self) -> u32 { self.0.id() + 1 } }
    #[inline(never)] pub fn f3(x: Box<dyn Tr2>) -> Box<dyn Tr3> { Box::new(H3(x)) }
    pub trait Tr2 { fn id(&self) -> u32; }
    pub struct H2(Box<dyn Tr1>);
    impl Tr2 for H2 { fn id(&self) -> u32 { self.0.id() + 1 } }
    #[inline(never)] pub fn f2(x: Box<dyn Tr1>) -> Box<dyn Tr2> { Box::new(H2(x)) }
    pub trait Tr1 { fn id(&self) -> u32; }
    pub struct H1(Box<dyn Tr0>);
    impl Tr1 for H1 { fn id(&self) -> u32 { self.0.id() + 1 } }
    #[inline(never)] pub fn f1(x: Box<dyn Tr0>) -> Box<dyn Tr1> { Box::new(H1(x)) }
    #[inline(never)] pub fn f0(x: App) -> Box<dyn Tr0> { Box::new(x) }
    pub fn top() -> Box<dyn Tr6> {
        let mut app = App::new();
        app.cell.bump();
        let b0 = f0(app);
        let b1 = f1(b0);
        let b2 = f2(b1);
        let b3 = f3(b2);
        let b4 = f4(b3);
        let b5 = f5(b4);
        let b6 = f6(b5);
        b6
    }
    pub fn run() -> u32 {
        let held = top();
        held.id()
    }
}

fn main() {
    println!("{}", chained::run());
}

clean {
    import Trust.Binding
    namespace EraseChainHolds
    open Trust.Protocol
    def chained : Trust.Protocol.Seal := seals "chained::Cell" ["chained::Cell::bump"] ["chained::Cell::new"] ["chained::App::new"] ["Box::new", "boxed::Box::drop"]
    end EraseChainHolds
}
