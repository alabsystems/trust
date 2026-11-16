//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_component.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! `Trust.Protocol.Seal`: a `dyn` of a trait of another crate, trusted to hold a
//! sealed value, owns it from then on: upcast to a `dyn Any` (`upcast`), or put in a
//! value made a `dyn Any` (`wrapped`), it is handed to a `dyn` no entry names, and
//! code that names no type of this crate can swap two of them (review 5 of the
//! review-14 build: the `dyn` was taken to own nothing). Each refused.

#![allow(unused)]

extern crate seal_dep_component;

pub mod upcast {
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
    impl seal_dep_component::Component for App {}
    pub fn mix(x: App, y: App) -> (Box<dyn core::any::Any>, Box<dyn core::any::Any>) {
        let cx: Box<dyn seal_dep_component::Component> = Box::new(x);
        let cy: Box<dyn seal_dep_component::Component> = Box::new(y);
        let mut ax: Box<dyn core::any::Any> = cx; //~ NOTE this hands a value of type `dyn seal_dep_component::Component`, which holds a `Cell` or points to one, to a
        let mut ay: Box<dyn core::any::Any> = cy;
        seal_dep_component::exchange(&mut ax, &mut ay);
        (ax, ay)
    }
}

pub mod wrapped {
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
    impl seal_dep_component::Component for App {}
    pub struct W(pub Box<dyn seal_dep_component::Component>);
    pub fn mix(x: App, y: App) -> (Box<dyn core::any::Any>, Box<dyn core::any::Any>) {
        let cx: Box<dyn seal_dep_component::Component> = Box::new(x);
        let cy: Box<dyn seal_dep_component::Component> = Box::new(y);
        let mut ax: Box<dyn core::any::Any> = Box::new(W(cx)); //~ NOTE this hands a value of type `W`, which holds a `Cell` or points to one, to a
        let mut ay: Box<dyn core::any::Any> = Box::new(W(cy));
        seal_dep_component::exchange(&mut ax, &mut ay);
        (ax, ay)
    }
}

clean {
    import Trust.Binding
    namespace DynUpcast
    open Trust.Protocol
    def upcast : Trust.Protocol.Seal := seals "upcast::Cell" ["upcast::Cell::bump"] ["upcast::Cell::new"] ["upcast::App::new"] ["seal_dep_component::Component", "boxed::Box::new", "Box::drop", "Component::label", "Any::type_id"]
    def wrapped : Trust.Protocol.Seal := seals "wrapped::Cell" ["wrapped::Cell::bump"] ["wrapped::Cell::new"] ["wrapped::App::new"] ["seal_dep_component::Component", "boxed::Box::new", "Box::drop", "Component::label", "Any::type_id"]
    end DynUpcast
}
//~^^^^ ERROR seal `DynUpcast.upcast` on `Cell` does not hold
//~^^^^ ERROR seal `DynUpcast.wrapped` on `Cell` does not hold
