//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_vtable.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_vtable_params.rs` (`Trust.Protocol.Seal`):
//! the shapes review 4 of the review-14 build found crashing the compiler, at
//! any seal, now read and HOLDING: a unit type made a `dyn` of a trait generic
//! at the fn's parameter (`shown`, `observers` under `T: Debug`, `router`,
//! `const_generic` at a const parameter, `state_machine`, and through a
//! dependency's generic fn, `via_dep`); and a holder made a `dyn` of a trait
//! whose provided method has a where-clause the `dyn` does not prove, and names
//! a projection only that clause settles (`where_default`, `codec`: what that
//! method names is an abstract impl, handed nothing that holds one).

#![allow(unused)]

extern crate seal_dep_vtable;

pub mod shown {
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
    pub trait Show<X> { fn show(&self, x: &X) -> usize; }
    pub struct P;
    impl<X> Show<X> for P { fn show(&self, _x: &X) -> usize { 1 } }
    pub fn obj<X>() -> &'static dyn Show<X> { &P }
}

pub mod observers {
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
    use std::fmt::Debug;
    pub trait Observer<T> { fn seen(&self, t: &T); }
    pub struct Logger;
    impl<T: Debug> Observer<T> for Logger { fn seen(&self, t: &T) { let _ = format!("{:?}", t); } }
    pub fn observers<T: Debug>() -> Vec<Box<dyn Observer<T>>> { vec![Box::new(Logger)] }
}

pub mod router {
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
    pub trait Handler<Req> { fn handle(&self, r: Req) -> u8; }
    pub struct Echo;
    impl<Req> Handler<Req> for Echo { fn handle(&self, _r: Req) -> u8 { 0 } }
    pub struct Router<Req> { hs: Vec<Box<dyn Handler<Req>>> }
    impl<Req: 'static> Router<Req> { pub fn new() -> Self { Router { hs: vec![Box::new(Echo)] } } }
}

pub mod const_generic {
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
    pub trait Tr<const N: usize> { fn n(&self) -> usize { N } }
    pub struct P;
    impl<const N: usize> Tr<N> for P {}
    pub fn obj<const N: usize>() -> &'static dyn Tr<N> { &P }
}

pub mod state_machine {
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
    pub trait State<C> { fn next(self: Box<Self>, c: &mut C) -> Box<dyn State<C>>; }
    pub struct Idle;
    impl<C> State<C> for Idle { fn next(self: Box<Self>, _c: &mut C) -> Box<dyn State<C>> { self } }
    pub fn start<C>() -> Box<dyn State<C>> { Box::new(Idle) }
}

pub mod where_default {
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
    pub trait Tr2 { type Out: Default; }
    pub trait Tr<X> {
        fn m(&self) where X: Tr2 { let v: Vec<<X as Tr2>::Out> = Default::default(); drop(v); }
        fn n(&self) {}
    }
    impl<T, X> Tr<X> for (T, App) {}
    pub fn mk<T>(x: &(T, App)) -> &dyn Tr<T> { x }
}

pub mod codec {
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
    pub trait Codec { type Msg; }
    pub trait Sink<C> {
        fn push(&mut self, raw: u8);
        fn decoded(&self) -> usize where C: Codec { let v: Vec<<C as Codec>::Msg> = std::iter::empty().collect(); v.len() }
    }
    pub struct Buf { app: App, raw: Vec<u8> }
    impl<C> Sink<C> for (C, Buf) { fn push(&mut self, raw: u8) { self.1.raw.push(raw) } }
    pub fn sink_of<C>(b: &mut (C, Buf)) -> &mut dyn Sink<C> { b }
}

pub mod via_dep {
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
    pub fn g<T: 'static>(t: &(T, App)) -> usize { seal_dep_vtable::obj::<(T, App)>().show(t) }
}

clean {
    import Trust.Binding
    namespace VtableParamsHolds
    open Trust.Protocol
    def shown : Trust.Protocol.Seal := seals "shown::Cell" ["shown::Cell::bump"] ["shown::Cell::new"] ["shown::App::new"] []
    def observers : Trust.Protocol.Seal := seals "observers::Cell" ["observers::Cell::bump"] ["observers::Cell::new"] ["observers::App::new"] []
    def router : Trust.Protocol.Seal := seals "router::Cell" ["router::Cell::bump"] ["router::Cell::new"] ["router::App::new"] []
    def const_generic : Trust.Protocol.Seal := seals "const_generic::Cell" ["const_generic::Cell::bump"] ["const_generic::Cell::new"] ["const_generic::App::new"] []
    def state_machine : Trust.Protocol.Seal := seals "state_machine::Cell" ["state_machine::Cell::bump"] ["state_machine::Cell::new"] ["state_machine::App::new"] []
    def where_default : Trust.Protocol.Seal := seals "where_default::Cell" ["where_default::Cell::bump"] ["where_default::Cell::new"] ["where_default::App::new"] []
    def codec : Trust.Protocol.Seal := seals "codec::Cell" ["codec::Cell::bump"] ["codec::Cell::new"] ["codec::App::new"] ["vec::Vec::push"]
    def via_dep : Trust.Protocol.Seal := seals "via_dep::Cell" ["via_dep::Cell::bump"] ["via_dep::Cell::new"] ["via_dep::App::new"] ["seal_dep_vtable::obj", "Show::show"]
    end VtableParamsHolds
}
