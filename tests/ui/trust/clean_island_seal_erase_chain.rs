//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A chain of six `dyn`s of traits of this crate, each made of a holder of
//! the one before, written so that each fn comes before the one whose
//! coercion it depends on (`Trust.Protocol.Seal`): the outermost `Box<dyn
//! Tr6>` owns the sealed value, as each one inside does, wherever the walk
//! met the coercions. Each seal must FAIL: `stored` gives that place a
//! second value, `erased` hands it to a `Box<dyn Any>`. Review 3 of the
//! review-14 build: the check learned one link of such a chain per walk of
//! every instance, so the cost grew with the chain; it now settles what each
//! `dyn` was handed over the coercions it logged, and walks again once.
//! (Each place given one value: `_erase_chain_holds.rs`.)

#![allow(unused)]

mod stored {
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
        let mut held = top();
        held = top(); //~ NOTE this puts a value of type `Box<dyn stored::Tr6>`, which holds a `Cell`, where one may already be, in
        held.id()
    }
}

mod erased {
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
        let any: Box<dyn std::any::Any> = Box::new(held); //~ NOTE this hands a value of type `Box<dyn erased::Tr6>`, which holds a `Cell` or points to one, to a `dyn Any`, in
        any.is::<u8>() as u32
    }
}

fn main() {
    println!("{}", stored::run());
    println!("{}", erased::run());
}

clean {
    import Trust.Binding
    namespace EraseChain
    open Trust.Protocol
    def stored : Trust.Protocol.Seal := seals "stored::Cell" ["stored::Cell::bump"] ["stored::Cell::new"] ["stored::App::new"] ["Box::new", "boxed::Box::drop"]
    def erased : Trust.Protocol.Seal := seals "erased::Cell" ["erased::Cell::bump"] ["erased::Cell::new"] ["erased::App::new"] ["Box::new", "boxed::Box::drop"]
    end EraseChain
}
//~^^^^ ERROR seal `EraseChain.stored` on `Cell` does not hold
//~^^^^ ERROR seal `EraseChain.erased` on `Cell` does not hold
