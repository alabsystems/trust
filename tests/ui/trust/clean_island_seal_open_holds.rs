//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_open.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_open.rs` (`Trust.Protocol.Seal`): a
//! LIBRARY's generic code read OPEN, where what it names at `(T, App)` puts
//! no value over another, and every seal HOLDS. A helper of this crate that
//! reads, or that runs the writer; a constant that only measures; a fn
//! handed out that measures, trusted by name; a blanket impl's method that
//! measures, trusted; a method whose impl the parameter picks (this crate's
//! trait, and std's `Debug`); a call of the closure a caller handed in, at a
//! `&mut App` (`with_fn`: what runs is that closure); a `dyn` of a trait of this crate made of a
//! holder; a `Vec<(T, App)>` dropped, its `Drop` impls trusted; a swap and a
//! clone at a type that holds none; a closure that calls the fn it was
//! handed, made an `Arc<dyn Fn>` (its vtable's `call_once` is the compiler's
//! shim around it: the first open build read the closure's body at the
//! shim's arguments, and the compiler's trait selection panicked).

#![allow(unused)]

extern crate seal_dep_open;

pub mod helper {
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
    fn local_first<T, U>(p: &(T, U)) -> &T { &p.0 }
    pub fn churn<T>(a: &(T, App)) -> &T { local_first(a) }
}

pub mod writer {
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
    fn tick_second<T>(p: &mut (T, App)) { p.1.tick() }
    pub fn churn<T>(a: &mut (T, App)) { tick_second(a) }
}

pub mod dep_size {
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
    use seal_dep_open::Tab;
    pub fn size<T>() -> usize { Tab::<(T, App)>::SIZE }
}

pub mod measurer {
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
    pub fn measure<T>(a: &(T, App)) -> usize { (seal_dep_open::measurer::<(T, App)>())(a) }
}

pub mod size_trait {
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
    use seal_dep_open::Size;
    pub fn size<T>(a: &(T, App)) -> usize { a.size() }
}

pub mod param_trait {
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
    pub trait Visit { fn visit(&mut self); }
    pub fn go<T: Visit>(x: &mut (T, App)) { x.0.visit() }
}

pub mod foreign_param {
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
    pub fn show<T: core::fmt::Debug>(x: &(T, App)) -> String { format!("{:?}", x.0) }
}

pub mod unsize_local {
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
    pub trait Show { fn show(&self) -> u32; }
    impl<X> Show for X { fn show(&self) -> u32 { 1 } }
    pub fn hide<T: 'static>(x: Box<(T, App)>) -> Box<dyn Show> { x }
}

pub mod dropped {
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
    pub fn sink<T>(v: Vec<(T, App)>) {}
}

pub mod plain_swap {
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
    pub fn swap_u<T>(a: &mut (T, u8), b: &mut (T, u8)) { core::mem::swap(a, b) }
}

pub mod cloned {
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
    pub fn dup<T: Clone>(x: &(T, u8)) -> (T, u8) { x.clone() }
}

pub mod with_fn {
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
}

pub mod hook {
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
    pub fn hook<F: Fn(u32) + Send + Sync + 'static>(send: F) -> std::sync::Arc<dyn Fn(&str, Option<u8>) + Send + Sync> {
        std::sync::Arc::new(move |s: &str, p: Option<u8>| send(s.len() as u32 + p.unwrap_or(0) as u32))
    }
}

clean {
    import Trust.Binding
    namespace OpenHolds
    open Trust.Protocol
    def helper : Trust.Protocol.Seal := seals "helper::Cell" ["helper::Cell::bump"] ["helper::Cell::new"] ["helper::App::new"] []
    def writer : Trust.Protocol.Seal := seals "writer::Cell" ["writer::Cell::bump"] ["writer::Cell::new"] ["writer::App::new"] []
    def dep_size : Trust.Protocol.Seal := seals "dep_size::Cell" ["dep_size::Cell::bump"] ["dep_size::Cell::new"] ["dep_size::App::new"] []
    def measurer : Trust.Protocol.Seal := seals "measurer::Cell" ["measurer::Cell::bump"] ["measurer::Cell::new"] ["measurer::App::new"] ["seal_dep_open::measure"]
    def size_trait : Trust.Protocol.Seal := seals "size_trait::Cell" ["size_trait::Cell::bump"] ["size_trait::Cell::new"] ["size_trait::App::new"] ["seal_dep_open::Size::size"]
    def param_trait : Trust.Protocol.Seal := seals "param_trait::Cell" ["param_trait::Cell::bump"] ["param_trait::Cell::new"] ["param_trait::App::new"] []
    def foreign_param : Trust.Protocol.Seal := seals "foreign_param::Cell" ["foreign_param::Cell::bump"] ["foreign_param::Cell::new"] ["foreign_param::App::new"] []
    def unsize_local : Trust.Protocol.Seal := seals "unsize_local::Cell" ["unsize_local::Cell::bump"] ["unsize_local::Cell::new"] ["unsize_local::App::new"] []
    def dropped : Trust.Protocol.Seal := seals "dropped::Cell" ["dropped::Cell::bump"] ["dropped::Cell::new"] ["dropped::App::new"] ["vec::Vec::drop", "RawVec::drop"]
    def plain_swap : Trust.Protocol.Seal := seals "plain_swap::Cell" ["plain_swap::Cell::bump"] ["plain_swap::Cell::new"] ["plain_swap::App::new"] []
    def cloned : Trust.Protocol.Seal := seals "cloned::Cell" ["cloned::Cell::bump"] ["cloned::Cell::new"] ["cloned::App::new"] []
    def with_fn : Trust.Protocol.Seal := seals "with_fn::Cell" ["with_fn::Cell::bump"] ["with_fn::Cell::new"] ["with_fn::App::new"] []
    def hook : Trust.Protocol.Seal := seals "hook::Cell" ["hook::Cell::bump"] ["hook::Cell::new"] ["hook::App::new"] []
    end OpenHolds
}
