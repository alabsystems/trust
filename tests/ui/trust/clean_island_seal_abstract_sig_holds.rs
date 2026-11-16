//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_sig.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_abstract_sig.rs` (`Trust.Protocol.Seal`): what
//! still HOLDS. A call through the `Fn` traits of a callee value whose type is a
//! type parameter (`fn_param`: the closure the instantiating crate handed in); a
//! dependency's item that hands back a swap, named in `trusts` (`dep_fnptr_trusted`)
//! or at a type that holds none (`dep_handed_plain`); a trait of this crate's
//! method handed nothing that holds one (`local_handed_nothing`); a loop over an
//! `impl IntoIterator<Item = u32>` (`into_iter_param`), an `async` closure called
//! at a parameter (`async_param`), and a store at `Option<I::Item>`
//! (`rigid_plain`): a rigid projection of another crate's trait, at parameters
//! nothing ties to a sealed value, is what the instantiating crate makes it.

#![allow(unused)]

extern crate seal_dep_sig;

pub mod fn_param {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub fn with<F: FnOnce(&mut App)>(app: &mut App, f: F) { f(app) }
    pub fn twice<F: FnMut(&mut App)>(app: &mut App, mut f: F) { f(app); f(app) }
}

pub mod dep_fnptr_trusted {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub fn churn<K: seal_dep_sig::Hand<Item = (T, App)>, T: 'static>(a: &mut (T, App), b: &mut (T, App)) { (K::swapper())(a, b) }
}

pub mod dep_handed_plain {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub fn churn<K: seal_dep_sig::Hand<Item = (T, u8)>, T: 'static>(a: &mut (T, u8), b: &mut (T, u8)) { (K::swapper())(a, b); let f = K::boxed(); f(a, b); (K::OP)(a, b) }
}

pub mod local_handed_nothing {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub trait Sz { fn sz(&self) -> usize; }
    pub fn size<K: Sz>(k: &K, a: &(K, App)) -> usize { k.sz() }
}

pub mod into_iter_param {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub fn total(xs: impl IntoIterator<Item = u32>, app: &mut App) -> u32 { let mut n = 0; for x in xs { n += x; } app.tick(); n }
}

pub mod async_param {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub fn go<F: AsyncFnOnce() -> u8>(f: F) { let fut = f(); drop(fut); }
}

pub mod rigid_plain {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    pub fn last<I: Iterator>(it: I) -> Option<I::Item> { let mut last = None; for x in it { last = Some(x); } last }
}

clean {
    import Trust.Binding
    namespace AbstractSigHolds
    open Trust.Protocol
    def fn_param : Trust.Protocol.Seal := seals "fn_param::Cell" ["fn_param::Cell::bump"] ["fn_param::Cell::new"] ["fn_param::App::new"] []
    def dep_fnptr_trusted : Trust.Protocol.Seal := seals "dep_fnptr_trusted::Cell" ["dep_fnptr_trusted::Cell::bump"] ["dep_fnptr_trusted::Cell::new"] ["dep_fnptr_trusted::App::new"] ["seal_dep_sig::Hand::swapper"]
    def dep_handed_plain : Trust.Protocol.Seal := seals "dep_handed_plain::Cell" ["dep_handed_plain::Cell::bump"] ["dep_handed_plain::Cell::new"] ["dep_handed_plain::App::new"] []
    def local_handed_nothing : Trust.Protocol.Seal := seals "local_handed_nothing::Cell" ["local_handed_nothing::Cell::bump"] ["local_handed_nothing::Cell::new"] ["local_handed_nothing::App::new"] []
    def into_iter_param : Trust.Protocol.Seal := seals "into_iter_param::Cell" ["into_iter_param::Cell::bump"] ["into_iter_param::Cell::new"] ["into_iter_param::App::new"] []
    def async_param : Trust.Protocol.Seal := seals "async_param::Cell" ["async_param::Cell::bump"] ["async_param::Cell::new"] ["async_param::App::new"] []
    def rigid_plain : Trust.Protocol.Seal := seals "rigid_plain::Cell" ["rigid_plain::Cell::bump"] ["rigid_plain::Cell::new"] ["rigid_plain::App::new"] []
    end AbstractSigHolds
}
